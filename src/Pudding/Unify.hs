module Pudding.Unify where

import Pudding.Types
import Pudding.Eval
import qualified Data.Map as Map
import Data.Foldable (fold)
import Data.Functor ((<&>), void)
import GHC.StableName (StableName)
import qualified Data.List as List
import qualified Data.Vector as Vector
import Data.Maybe (fromMaybe)
import GHC.Stack (HasCallStack)
import Data.These (These(..))
import Data.Semialign.Indexed (SemialignWithIndex (ialignWith))
import qualified Pudding.Types.Stack as Stack
import Debug.Trace (traceWith)
import Pudding.Printer (formatCore, Style (Ansi))
import qualified Data.Text as T
import qualified Pudding.Printer as P
import Control.DeepSeq (NFData(rnf))

-- Validate the type of a term, as an evaluated type
validate :: EvalTypeCtx -> "term" @:: Term -> "type" @:: Eval
validate = validateOrNot seq
-- Validate and quote back to a term
validateQuote :: EvalTypeCtx -> "term" @:: Term -> "type" @:: Term
validateQuote ctx = quote (void ctx) . validate ctx
-- Validate in a context of neutrals
validateQuoteNeutrals :: Globals -> ["type" @:: Term] -> "term" @:: Term -> "type" @:: Term
validateQuoteNeutrals globals localTypes = validateQuote $
  mapCtx (\_ lvl ty -> (ty, neutralVar lvl)) $ evalCtx $
    ctxOfList globals $ (BFresh,) <$> localTypes
-- Do not validate, but just assemble the type
quickTermType :: EvalTypeCtx -> "term" @:: Term -> "type" @:: Eval
quickTermType = validateOrNot (const id)


-- Typecheck and share partial evaluation of globals
--
-- TODO: make sure definitions are acyclic!
bootGlobals, bootGlobalDefns, bootGlobalTypes :: Globals -> Globals
bootGlobals = bootGlobalDefns . bootGlobalTypes

bootGlobalDefns globals = newGlobals
  where
  newGlobals = globals <&> \case
    GlobalDefn _ _ (GlobalTerm defn _) ->
      let !ty = typeofGlobal defn in
      GlobalDefn (arityOfTerm defn) ty (globalTerm defn)
    global -> global
  ctx :: forall t. Ctx t
  ctx = ctxOfGlobals newGlobals
  globalTerm :: Term -> GlobalTerm
  globalTerm tm = GlobalTerm tm (evalGlobal tm)
  evalGlobal :: Term -> Eval
  evalGlobal = eval ctx
  typeofGlobal :: Term -> GlobalTerm
  typeofGlobal tm =
    let !ty = validate ctx tm in
    GlobalTerm (quote (void ctx) ty) ty

bootGlobalTypes globals =
  globals `disjointUnion` constructors globals
  where
  disjointUnion = Map.unionWithKey \k _ _ -> error $ "Duplicate global: " <> show k
  fakeGlobal tm = GlobalDefn (arityOfTerm tm) undefined (GlobalTerm tm undefined)
  constructors = fold . Map.mapWithKey \tyName -> \case
    GlobalType (GlobalTypeInfo { typeParams, typeConstrs }) ->
      flip Map.mapWithKey typeConstrs \conName (ConstructorInfo { ctorArguments }) -> fakeGlobal $
        abstract (Vector.toList typeParams <> Vector.toList ctorArguments) $
          TConstr mempty (tyName, conName) (toVars (Vector.length ctorArguments) typeParams) (toVars 0 ctorArguments)
    _ -> Map.empty
  -- Form repeated lambdas to turn the raw constructor into a curried function
  abstract ((p, b, paramType) : more) focus =
    TLambda mempty p b paramType $ Scoped $ abstract more focus
  abstract [] focus = focus

  toVars :: forall i. Int -> Vector.Vector i -> Vector.Vector Term
  toVars skipped template =
    -- ugh why no mapWithIndex
    Vector.zipWith mk (Level <$> Vector.fromList [0..]) template
    where
    mk lvl _ =
      let Index idx = index (Vector.length template) lvl in
      TVar mempty $ Index $ idx + skipped

--------------------------------------------------------------------------------
-- Conversion checking: the algorithm for definitional equality / unification --
--------------------------------------------------------------------------------


-- Conversion checking is the algorithm for definitional equality used during
-- typechecking: specifically it refers to the process of finding out if a term
-- can be converted from one type to another, but with dependent types, it needs
-- to be a general algorithm for definitional equality.
--
-- Note: we care that the happy path is fast, more than failing fast for
-- mismatches.
conversionCheck :: HasCallStack => Ctx () -> Eval -> Eval -> Bool
conversionCheck ctx evalL evalR = case (evalL, evalR) of
  -- We unravel `EDeferred` slowly, to check if any names match up, before
  -- continuing with the main cases.
  (EDeferred {}, _) -> deferred [] [] evalL evalR
  (_, EDeferred {}) -> deferred [] [] evalL evalR

  -- Conversion checking for the main constructors is straightforward:
  (EUniv _ univL, EUniv _ univR) -> univL == univR
  (ELambda _ _ bdrL tyL bodyL, ELambda _ _ bdrR tyR bodyR) ->
    ccScoped bdrL tyL bodyL bdrR tyR bodyR
  (EPi _ _ bdrL tyL bodyL, EPi _ _ bdrR tyR bodyR) ->
    ccScoped bdrL tyL bodyL bdrR tyR bodyR
  (ESigma _ _ bdrL tyL bodyL, ESigma _ _ bdrR tyR bodyR) ->
    ccScoped bdrL tyL bodyL bdrR tyR bodyR
  (EPair _ _ leftL rightL, EPair _ _ leftR rightR) ->
    cc leftL leftR && cc rightL rightR
  (ETyCtor _ nameL paramsL indicesL, ETyCtor _ nameR paramsR indicesR) ->
    nameL == nameR
      && List.length paramsL == List.length paramsR
      && all (uncurry cc) (Vector.zip paramsL paramsR)
      && List.length indicesL == List.length indicesR
      && all (uncurry cc) (Vector.zip indicesL indicesR)
  (EConstr _ nameL paramsL argsL, EConstr _ nameR paramsR argsR) ->
    nameL == nameR
      && List.length paramsL == List.length paramsR
      && all (uncurry cc) (Vector.zip paramsL paramsR)
      && List.length argsL == List.length argsR
      && all (uncurry cc) (Vector.zip argsL argsR)
  (ELift _ tyL, ELift _ tyR) -> cc tyL tyR
  (EQuote _ tmL, EQuote _ tmR) -> cc tmL tmR -- TODO: what about staging??

  -- Handle some eta conversions (but not unit-type eta, which needs to be
  -- type-directed)
  (EPair _ ty _ _, _) -> cc evalL (etaPair ty evalR)
  (_, EPair _ ty _ _) -> cc (etaPair ty evalL) evalR
  (ELambda _ _ bdr _ body, _) ->
    let
      (lvl, ctx') = push (bdr, ()) ctx
      !arg = neutralVar lvl
    in conversionCheck ctx' (instantiateClosure body arg) (doApp evalR arg)
  (_, ELambda _ _ bdr _ body) ->
    let
      (lvl, ctx') = push (bdr, ()) ctx
      !arg = neutralVar lvl
    in conversionCheck ctx' (doApp evalL arg) (instantiateClosure body arg)

  -- The default case of neutrals (variables) is easy to check: check projections
  -- pairwise. Dealing with lazily inlined globals requires checking via
  -- inlining if the normal approach failed to unify them. Finally, dealing with
  -- holes will require some particular thought.
  (ENeut (Neutral focusL prjsL), ENeut (Neutral focusR prjsR))
    | checkFocus focusL focusR
    -- We do care that this is fast, so check that everything matches up
    -- before recursing into arguments
    , checkPrjs (\_ _ -> True) (prjsL, prjsR)
    , checkPrjs cc (prjsL, prjsR)
      -> True
    -- otherwise fall through

  -- Finally we are left with alternate strategies

  -- TODO: holes
  -- If one or both sides are globals, they can still match by inlining
  _ | conversionCheckGlobal -> True
  -- TODO: Finally we handle eta for subsingleton types
  _ -> False
  where
  cc :: HasCallStack => Eval -> Eval -> Bool
  cc = conversionCheck ctx
  ccScoped bdrL tyL bodyL bdrR tyR bodyR =
    let
      (lvl, ctx') = push (BMulti bdrL bdrR, ()) ctx
      !var = neutralVar lvl
    in cc tyL tyR && conversionCheck ctx'
      (instantiateClosure bodyL var) (instantiateClosure bodyR var)

  -- Check what the neutral is blocked on: if it is a neutral variable,
  -- they *must* be the same variable (à la skolem variables)
  checkFocus focusL focusR = case (focusL, focusR) of
    (NVar _ lvlL, NVar _ lvlR) -> lvlL == lvlR
    (NHole _ holeL, NHole _ holeR) -> holeL == holeR
    -- We also check globals separately if it fails
    (NGlobal _ _ nameL, NGlobal _ _ nameR) -> nameL == nameR
    (_, _) -> False -- FIXME: handle holes via unification!!
  checkPrjs shouldCC = \case
    (moreL :> NApp _ argL, moreR :> NApp _ argR) ->
      shouldCC argL argR && checkPrjs shouldCC (moreL, moreR)
    (moreL :> NFst _, moreR :> NFst _) ->
      checkPrjs shouldCC (moreL, moreR)
    (moreL :> NSnd _, moreR :> NSnd _) ->
      checkPrjs shouldCC (moreL, moreR)
    (moreL :> NSplice _, moreR :> NSplice _) ->
      checkPrjs shouldCC (moreL, moreR)
    (Nil, Nil) -> True
    -- Differing lengths or differing projections
    (_, _) -> False

  -- TODO: use IntSet or something
  deferred :: [StableName Eval] -> [StableName Eval] -> Eval -> Eval -> Bool
  -- Short circuit on matching `EDeferred` stable names!
  deferred namesL namesR _ _ | not (List.null (List.intersect namesL namesR)) = True
  -- Force the terms pairwise if possible
  deferred namesL namesR (EDeferred _ _ mnameL _ tmL) (EDeferred _ _ mnameR _ tmR) =
    deferred (maybe id (:) mnameL namesL) (maybe id (:) mnameR namesR) tmL tmR
  deferred namesL namesR (EDeferred _ _ mnameL _ tmL) tmR | mnameR <- Nothing =
    deferred (maybe id (:) mnameL namesL) (maybe id (:) mnameR namesR) tmL tmR
  deferred namesL namesR tmL (EDeferred _ _ mnameR _ tmR) | mnameL <- Nothing =
    deferred (maybe id (:) mnameL namesL) (maybe id (:) mnameR namesR) tmL tmR
  -- No stable names matched, force the terms and do regular conversion checking
  deferred _ _ tmL tmR = cc tmL tmR

  conversionCheckGlobal = case (forceGlobal ctx evalL, forceGlobal ctx evalR) of
    -- If we do not make progress on either as a global, then conversion checking
    -- fails: they were different constructors in the AST and semantically
    (Nothing, Nothing) -> False
    -- Retry with one or both being inlined now
    (forcedL, forcedR) -> cc (fromMaybe evalL forcedL) (fromMaybe evalR forcedR)



--------------------------------------------------------------------------------
-- Type inference / checking / validation                                     --
--------------------------------------------------------------------------------


-- Infer the type of the term, either checking the whole tree as it goes if
-- `seqOrConst = seq`, or just doing the minimal work to return the inferred
-- type if `seqOrConst = const id`.
validateOrNot :: (forall a b. a -> b -> b) -> HasCallStack => EvalTypeCtx -> "term" @:: Term -> "type" @:: Eval
validateOrNot seqOrConst ctx = \case
  TVar _ idx ->
    checkFor "idx is nonnegative" (idx >= Index 0)
      `seqOrConst`
    checkFor "idx fits in the current context" (idx < Index (size ctx))
      `seqOrConst`
    fst (ctx @@: idx)
  TGlobal _ name -> case Map.lookup name (ctxGlobals ctx) of
    Nothing -> error $ "Undefined global " <> show name
    Just (GlobalDefn _ (GlobalTerm _ ty) _) -> ty
    -- FIXME a bit lazy
    Just (GlobalType info) -> validateOrNot seqOrConst ctx $ mkTypeConstructor name info
  THole _ _fresh -> error "typeof hole not implemented"
  TUniv meta univ -> EUniv meta $ case univ of
    UBase lvl -> UBase (lvl + 1)
    UMeta lvl -> UMeta (lvl + 1)
    -- This is why `UVar` has an `Int`: increment to get the typeof
    UVar fresh incr -> UVar fresh (incr + 1)
  TLambda meta p b ty body ->
    case validateScoped b ty body of
      (argTy, bodyTy) ->
        EPi meta p b argTy $ Closure b evalCtxHere $
          -- We have to quote it back into a `Term`, mostly for when the
          -- neutral variable we used for typechecking is actually instantiated
          -- at an application site
          Scoped $ quote (quoteCtxHere :> (b, ())) bodyTy
  TPi _ _ b ty body ->
    -- Π(x : ty : U), (body : U)
    case (vv ty, snd $ validateScoped b ty body) of
      (EUniv m1 u1, EUniv m2 u2) -> EUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad pi type"
  TSigma _ _ b ty body ->
    case (vv ty, snd $ validateScoped b ty body) of
      (EUniv m1 u1, EUniv m2 u2) -> EUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad sigma type"
  TPair _ ty left right ->
    validateType ty `seqOrConst` case evalHere ty of
      tyVal@(ESigma _ _ _ fstTy body) ->
        cc "fst type mismatch" fstTy (vv left) `seqOrConst`
        cc "snd type mismatch" (instantiateClosure body (evalHere left)) (vv right) `seqOrConst`
        tyVal
      _ -> error "bad pair type"
  TFst _ tm -> case vv tm of
    ESigma _ _ _ ty _ -> ty
    _ -> error "Bad fst"
  TSnd _ tm -> case vv tm of
    ESigma _ _ _ _ body ->
      instantiateClosure body (doPrj (evalHere tm) (NFst mempty))
    _ -> error "Bad snd"
  TApp _ fun arg -> case (vv fun, vv arg) of
    (EPi _ _ _ argTyExpected body, argTyActual) ->
      cc "argument type mismatch" argTyExpected argTyActual `seq` instantiateClosure body (evalHere arg)
    _ -> error "Bad app"
  TTyCtor _ tyName params indices -> case Map.lookup tyName (ctxGlobals ctx) of
    Just (GlobalType (GlobalTypeInfo { typeParams, typeIndices, typeConstrs = _ })) ->
      checkFor "Wrong number of parameters" (Vector.length params == Vector.length typeParams) `seqOrConst`
      checkFor "Wrong number of indices" (Vector.length indices == Vector.length typeIndices) `seqOrConst`
      validateTelescope "Invalid type constructor parameter" 0 ctx params (ctxOfGlobals $ ctxGlobals ctx) typeParams \ctxParams ->
      validateTelescope "Invalid type constructor index" 0 ctx indices ctxParams typeIndices \_ctxIndices ->
      -- FIXME: do a proper universe check
      EUniv mempty (UBase 0)
    _ -> error "Bad type constructor name"
  TConstr _ (tyName, conName) params args -> case Map.lookup tyName (ctxGlobals ctx) of
    Just (GlobalType (GlobalTypeInfo { typeParams, typeIndices = _, typeConstrs }))
      | Just (ConstructorInfo { ctorArguments, ctorIndices }) <- Map.lookup conName typeConstrs ->
      checkFor "Wrong number of parameters" (Vector.length params == Vector.length typeParams) `seqOrConst`
      validateTelescope "Invalid constructor parameter" 0 ctx params (ctxOfGlobals $ ctxGlobals ctx) typeParams \ctxParams ->
      validateTelescope "Invalid constructor argument" 0 ctx args ctxParams ctorArguments \ctxArgs ->
        let
          -- the parameters were already evaluated onto the first stack
          paramValues = Vector.fromList $ snd <$> ctxToList ctxParams
          -- then we need to evaluate the indices, now that the arguments are
          -- all bound as well
          indexValues = eval ctxArgs <$> ctorIndices
        in ETyCtor mempty tyName paramValues indexValues
    _ -> error "Bad constructor name"
  TCase _ motive cases inspect ->
    let motiveHere = evalHere motive in
    flip seqOrConst (doApp motiveHere (evalHere inspect))
    case vv inspect of
      inspectType@(ETyCtor _ tyName chosenParams _) ->
        case Map.lookup tyName (ctxGlobals ctx) of
          Just (GlobalType tyInfo@(GlobalTypeInfo { typeConstrs })) ->
            cc "case motive" (vv motive) (EPi mempty Explicit BUnused inspectType (Closure BUnused Nil $ Scoped $ TUniv mempty (UBase 0)))
              `seqOrConst`
            checkFor "Wrong case names" (Map.keys typeConstrs == Map.keys cases)
              `seqOrConst`
            checkFor "Wrong case types" do
              alignAll typeConstrs cases \conName -> \case
                That _ -> error "Extra case"
                This _ -> error "Missing case"
                These constr caseTerm ->
                  let
                    !caseFnType = traceEval "caseFnType" $ ee (makeCaseFnType tyName tyInfo conName constr)
                    !caseType = traceEval "caseType" $ doApps caseFnType (Stack.fromFoldable chosenParams :> motiveHere)
                  in cc ("Wrong case type for " <> show conName) caseType (vv caseTerm) `seqOrConst` True
          _ -> error "Undefined type constructor"
      _ -> error "Not a type constructor in case annotation"
  TLift _ ty -> case vv ty of
    EUniv m1 (UBase n) -> EUniv m1 (UMeta n)
    _ -> error "Must be a type in the base"
  TQuote meta tm -> ELift meta $ vv tm
  TSplice _ tm -> case vv tm of
    ELift _ ty -> ty
    _ -> error "Bad splice"
  where
  validateType ty = case vv ty of
    EUniv _ _ -> evalHere ty
    _ -> error "Expected a valid type"

  -- TODO: subsumption
  cc :: HasCallStack => String -> Eval -> Eval -> Eval
  cc err l r
    | conversionCheck (void ctx) l r = l
    | otherwise = error err

  vv = validateOrNot seqOrConst ctx

  checkFor _ True = ()
  checkFor err False = error err

  validateScoped :: Binder -> "arg type" @:: Term -> ScopedTerm -> ("arg type" @:: Eval, "body type" @:: Eval)
  validateScoped bdr ty (Scoped body) =
    let
      (lvl, ctx') = push (bdr, (tyVal, neutralVar lvl)) ctx
      tyVal = validateType ty
    in (tyVal, tyVal `seq` validateOrNot seqOrConst ctx' body)

  -- FIXME: rnf on the left here does not terminate...?
  ee tm = vv tm `seqOrConst` evalHere tm

  evalHere = eval evalCtxHere
  toEvalCtx = mapCtx (\_ _ (_, tm) -> tm)
  evalCtxHere = toEvalCtx ctx :: EvalCtx
  quoteCtxHere = mapCtx (\_ _ _ -> ()) ctx :: QuoteCtx

  traceEval desc = traceTermWith desc (quote quoteCtxHere)
  traceTerm desc = traceTermWith desc id
  traceTermWith :: forall x. String -> (x -> Term) -> x -> x
  traceTermWith desc fn = traceWith (termTrace desc . fn)
  termTrace desc tm = desc <> ": " <> do
    T.unpack $ P.format P.Ansi $ P.printCore tm (P.PS 0 (size ctx))

  -- Validating a dependent telescope is a little more tricky, but mostly it is
  -- just a lot of data to plumb around.
  validateTelescope ::
    "error" @:: String ->
    "current index" @:: Int ->
    "eval/result ctx" @:: EvalTypeCtx ->
    "values" @:: Vector.Vector Term ->
    "telescope value ctx" @:: EvalCtx ->
    "telescope" @:: Vector.Vector (Plicit, Binder, Term) ->
    ("new telescope value ctx" @:: EvalCtx -> r) -> r
  validateTelescope mismatchError i ctorCtx valueVector typeCtx typeVector continuation =
    case (valueVector Vector.!? i, typeVector Vector.!? i) of
      (Just value, Just (_, binder, tyTerm)) ->
        let
          -- Eval the telescope type first, in the context reserved for the
          -- inductive type, starting from the global context
          tyEval = eval typeCtx tyTerm
          -- Next we typecheck `value` against `tyEval`
          valueTy = cc (mismatchError <> " " <> show i) (validateOrNot seqOrConst ctorCtx value) tyEval
          -- Now we extend `typeCtx` with the new value (laziness is nice here)
          typeCtx' = valueTy `seqOrConst` typeCtx :> (binder, eval (toEvalCtx ctorCtx) value)
        in valueTy `seqOrConst`
          -- Proceed with the next index `i+1`
          validateTelescope mismatchError (i+1) ctorCtx valueVector typeCtx' typeVector continuation
      _ -> continuation typeCtx

alignAll :: SemialignWithIndex i f => Foldable f => f x -> f y -> (i -> These x y -> Bool) -> Bool
alignAll xs ys f = and $ ialignWith f xs ys

-- | The type of the motive for the given inductive type:
-- it takes the indices of the inductive type as arguments
-- and then returns a type (the motive at those indices).
--
-- We need to abstract over the *parameters* of the type, so to keep it as a
-- closed term, we take those as lambda arguments for the caller to apply.
makeMotiveType :: Name -> GlobalTypeInfo -> Term
makeMotiveType tyName (GlobalTypeInfo { typeParams, typeIndices }) =
  let
    -- Make a telescope of *lambdas* to accept the chosen parameter types
    prependParams inner = foldr prependParam inner typeParams
    prependParam (p, b, paramType) inner =
      TLambda mempty p b paramType $ Scoped inner
    -- Make a telescope of *Pis* to abstract over indices of the type constructor
    prependIndices inner = foldr prependIndex inner typeIndices
    prependIndex (p, b, indexType) inner =
      TPi mempty p b indexType $ Scoped inner
    -- Finally we apply the *chosen values* of each parameter and index to the type constructor
    -- Level <$> (#params + #indices - 1)..(#indices)
    -- Level <$> (#indices - 1)..0
    chosenParam i = TVar mempty $ Index $ (length typeParams - 1 - i) + length typeIndices
    chosenIndex i = TVar mempty $ Index $ (length typeIndices - 1 - i) + 0
    chosenType = TTyCtor mempty tyName
      (Vector.imap (const . chosenParam) typeParams)
      (Vector.imap (const . chosenIndex) typeIndices)
    -- And a motive takes that specific type and returns the goal type for it
    motive = TPi mempty Explicit BUnused chosenType $ Scoped (TUniv mempty (UBase 0))
  in prependParams $ prependIndices $ motive


-- TODO: share this evaluation
makeCaseFnType :: Name -> GlobalTypeInfo -> Name -> ConstructorInfo -> Term
makeCaseFnType tyName tyInfo@(GlobalTypeInfo { typeParams, typeIndices = _ }) conName (ConstructorInfo { ctorArguments, ctorIndices }) =
  let
    -- Make a telescope of *lambdas* to accept the chosen parameter types
    prependParams inner = foldr prependParam inner typeParams
    prependParam (p, b, paramType) inner =
      TLambda mempty p b paramType $ Scoped inner
    -- Now take a motive for those parameters
    abstractedMotiveType = makeMotiveType tyName tyInfo
    chosenParamForMotive i = TVar mempty $ Index $ (length typeParams - 1 - i)
    chosenMotiveType = Vector.ifoldl
      (\motiveTypeFn i _ -> TApp mempty motiveTypeFn $ chosenParamForMotive i)
      abstractedMotiveType typeParams
    prependMotive inner = TLambda mempty Explicit BFresh chosenMotiveType $ Scoped inner
    withMotive introed = shiftFrom introed 1
    -- Make a telescope of *Pis* to abstract over the *constructor* arguments
    prependArguments inner = Vector.ifoldr prependArgument inner ctorArguments
    prependArgument introed (p, b, argumentType) inner =
      TPi mempty p b (withMotive introed argumentType) $ Scoped inner
    -- Now we know the constructor arguments...
    chosenArgument i = TVar mempty $ Index $ (length ctorArguments - 1 - i) + 0
    -- (The parameters have shifted)
    chosenParam i = TVar mempty $ Index $ (length typeParams - 1 - i) + 1 {- motive -} + length ctorArguments
    -- ... So we can reconstruct the inspected value
    chosenValue = TConstr mempty (tyName, conName)
      (Vector.imap (const . chosenParam) typeParams)
      (Vector.imap (const . chosenArgument) ctorArguments)
    -- And we know the abstract motive, waiting for indices and the constructed value
    givenMotive = TVar mempty (Index (length ctorArguments))
    -- So we should be able to just plug in the indices to the motive:
    -- (They are relative to the arguments abstracted in the same way)
    -- FIXME: this is not true! the parameters are one off! ugh
    relevantMotive = Vector.ifoldl
      (\motiveFn i chosenIndex -> TApp mempty motiveFn (withMotive (i + Vector.length ctorArguments) chosenIndex))
      givenMotive ctorIndices
    appliedMotive = TApp mempty relevantMotive chosenValue
    -- And plug in the value from the arguments
  -- Now we fit it all together, then let the caller apply it
  in prependParams $ prependMotive $ prependArguments $ appliedMotive

