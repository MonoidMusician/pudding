module Pudding.Unify where

import Pudding.Types
import Pudding.Eval
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor ((<&>), void)
import Pudding.Printer (Style (Ansi), format, printCore)
import qualified Data.Text as T
import Data.Coerce (coerce)
import GHC.StableName (StableName)
import qualified Data.List as List
import qualified Data.Vector as Vector
import Data.Maybe (fromMaybe)

-- Validate the type of a term, as an evaluated type
validate :: EvalTypeCtx -> Desc "term" Term -> Desc "type" Eval
validate = validateOrNot seq
-- Validate and quote back to a term
validateQuote :: EvalTypeCtx -> Desc "term" Term -> Desc "type" Term
validateQuote ctx = quote (void ctx) . validate ctx
-- Validate in a context of neutrals
validateQuoteNeutrals :: Globals -> [Desc "type" Term] -> Desc "term" Term -> Desc "type" Term
validateQuoteNeutrals globals localTypes = validateQuote $
  mapCtx (\(_idx, lvl) ty -> (ty, neutralVar lvl)) $ evalCtx $
    ctxOfList globals $ (BFresh,) <$> localTypes
-- Do not validate, but just assemble the type
quickTermType :: EvalTypeCtx -> Desc "term" Term -> Desc "type" Eval
quickTermType = validateOrNot (const id)


-- Typecheck and share partial evaluation of globals
--
-- TODO: make sure definitions are acyclic!
bootGlobals :: Globals -> Globals
bootGlobals globals = globals <&> \case
  GlobalDefn _ _ tm@(GlobalTerm defn _) ->
    let !ty = typeofGlobal tm in
    GlobalDefn (arityOfTerm defn) ty (globalTerm tm)
  global -> global
  where
  ctx = ctxOfGlobals globals
  globalTerm (GlobalTerm tm _) = GlobalTerm tm (evalGlobal tm)
  evalGlobal = eval ctx
  typeofGlobal :: GlobalTerm -> GlobalTerm
  typeofGlobal (GlobalTerm tm _) =
    let !ty = validate ctx tm in
    GlobalTerm (quote (void ctx) ty) ty


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
conversionCheck :: Ctx () -> Eval -> Eval -> Bool
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

  -- Handle some eta conversions (but not unit-type eta, which needs to be
  -- type-directed)
  (EPair _ ty _ _, _) -> cc evalL (etaPair ty evalR)
  (_, EPair _ ty _ _) -> cc (etaPair ty evalL) evalR
  (ELambda _ _ bdr _ body, _) ->
    let !arg = nextNeutral ctx in
    conversionCheck (snoc ctx bdr ()) (instantiateClosure body arg) (doApp evalR arg)
  (_, ELambda _ _ bdr _ body) ->
    let !arg = nextNeutral ctx in
    conversionCheck (snoc ctx bdr ()) (doApp evalL arg) (instantiateClosure body arg)

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
  cc = conversionCheck ctx
  ccScoped bdrL tyL bodyL bdrR tyR bodyR =
    let
      !var = nextNeutral ctx
      ctx' = snoc ctx (BMulti bdrL bdrR) ()
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
    (NApp _ argL : moreL, NApp _ argR : moreR) ->
      shouldCC argL argR && checkPrjs shouldCC (moreL, moreR)
    (NFst _ : moreL, NFst _ : moreR) ->
      checkPrjs shouldCC (moreL, moreR)
    (NSnd _ : moreL, NSnd _ : moreR) ->
      checkPrjs shouldCC (moreL, moreR)
    ([], []) -> True
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
validateOrNot :: (forall a b. a -> b -> b) -> EvalTypeCtx -> Desc "term" Term -> Desc "type" Eval
validateOrNot seqOrConst ctx = \case
  TVar _ idx -> fst $ indexCtx idx ctx
  TGlobal _ name -> case Map.lookup name (ctxGlobals ctx) of
    Nothing -> error $ "Undefined global " <> show name
    Just (GlobalDefn _ (GlobalTerm _ ty) _) -> ty
    Just _ -> error "Not implemented"
  THole _ fresh -> error "typeof hole not implemented"
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
          Scoped $ quote (snoc quoteCtxHere b ()) bodyTy
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
  TTyCtor meta tyName params indices -> case Map.lookup tyName (ctxGlobals ctx) of
    Just (GlobalType (GlobalTypeInfo { typeParams, typeIndices })) ->
      checkFor "Wrong number of parameters" (Vector.length params == Vector.length typeParams) `seqOrConst`
      checkFor "Wrong number of indices" (Vector.length indices == Vector.length typeIndices) `seqOrConst`
      validateTelescope "Invalid type constructor parameter" ctx params typeParams \ctx' ->
      validateTelescope "Invalid type constructor index" ctx' indices typeIndices \ctx'' ->
      -- FIXME: do a proper universe check
      EUniv mempty (UBase 0)
    _ -> error "Bad type constructor name"
  TConstr meta (tyName, conName) params args -> case Map.lookup tyName (ctxGlobals ctx) of
    Just (GlobalType (GlobalTypeInfo { typeParams, typeIndices, typeConstrs }))
      | Just (ConstructorInfo { ctorArguments, ctorIndices }) <- Map.lookup conName typeConstrs ->
      checkFor "Wrong number of parameters" (Vector.length params == Vector.length typeParams) `seqOrConst`
      validateTelescope "Invalid constructor parameter" ctx params typeParams \ctx' ->
      validateTelescope "Invalid constructor argument" ctx' args ctorArguments \ctx'' ->
      eval (mapCtx (\_ (_, tm) -> tm) ctx) 
    _ -> error "Bad type constructor name"
  where
  validateType ty = case vv ty of
    EUniv _ _ -> evalHere ty
    _ -> error "Expected a valid type"

  -- TODO: subsumption
  cc err l r = case conversionCheck (void ctx) l r of
    True -> l
    False -> error err

  vv = validateOrNot seqOrConst ctx

  checkFor _ True = ()
  checkFor err False = error err

  validateScoped :: Binder -> Desc "arg type" Term -> ScopedTerm -> (Desc "arg type" Eval, Desc "body type" Eval)
  validateScoped bdr ty (Scoped body) =
    let
      tyVal = validateType ty
      ctx' = snoc ctx bdr (tyVal, nextNeutral ctx)
    in (tyVal, tyVal `seq` validateOrNot seqOrConst ctx' body)

  evalHere = eval evalCtxHere
  evalCtxHere = mapCtx (\_ (_, tm) -> tm) ctx :: EvalCtx
  quoteCtxHere = mapCtx (\_ _ -> ()) ctx :: QuoteCtx



-- This functions as a proof that terms are intrinsically typed
typeof :: TypeCtx -> Term -> Term
typeof ctx = \case
  TVar _ idx -> getShifted idx (snd <$> ctxStack ctx)
  TGlobal _ name -> case Map.lookup name (ctxGlobals ctx) of
    Nothing -> error $ "Undefined global " <> show name
    Just (GlobalDefn _ (GlobalTerm ty _) _) -> ty
    Just _ -> error "Not implemented"
  THole _ fresh -> error "typeof hole not implemented"
  TUniv meta univ -> TUniv meta case univ of
    UBase lvl -> UBase (lvl + 1)
    UMeta lvl -> UMeta (lvl + 1)
    -- This is why `UVar` has an `Int`: increment to get the typeof
    UVar fresh incr -> UVar fresh (incr + 1)
  TLambda meta p b ty (Scoped body) ->
    TPi meta p b ty (Scoped (typeof (into b ty) body))
  TPi _ _ b ty (Scoped body) ->
    -- Π(x : ty : U), (body : U)
    case (typeof ctx ty, typeof (into b ty) body) of
      (TUniv m1 u1, TUniv m2 u2) -> TUniv (m1 <> m2) (umax u1 u2)
      (_, r) -> error $ "Bad pi type: " <> T.unpack do
        format Ansi $ printCore r (0, coerce $ ctxSize ctx)
  TSigma _ _ b ty (Scoped body) ->
    case (typeof ctx ty, typeof (into b ty) body) of
      (TUniv m1 u1, TUniv m2 u2) -> TUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad sigma type"
  TPair _meta ty _left _right -> ty
  TFst _ tm -> case typeof ctx tm of
    TSigma _ _ _ ty _body -> ty
    _ -> error "Bad fst"
  TSnd _ tm -> case typeof ctx tm of
    -- typeof (snd (tm : Σ(x : ty), body)) = body@[x := fst tm] = (λ(x : ty), body)(fst tm)
    TSigma _ _ binder ty body ->
      TApp mempty (TLambda mempty Explicit binder ty body) (TFst mempty tm)
    _ -> error "Bad snd"
  TApp _ fun arg -> case typeof ctx fun of
    -- typeof ((f : Π(x : ty), body) (arg : ty)) = body@[x := arg] = (λ(x : ty), body)(arg)
    TPi meta p b ty body -> TApp mempty (TLambda meta p b ty body) arg
    _ -> error "Bad app"
  where
  into :: Binder -> Term -> TypeCtx
  into bdr ty = snoc ctx bdr ty
