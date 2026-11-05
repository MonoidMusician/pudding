-- | This is the core module for typechecking and unification. Core terms
-- | are already intrinsically typed, which can be validated with `validate`,
-- | or just quickly assembled with `quickTermType`.
-- |
-- | Currently it does not have any features for unification: that needs
-- | some monad design first.
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{- HLINT ignore "Redundant <$>" -}
module Pudding.Core.Unify where

import Control.Arrow (Arrow(first))
import Control.DeepSeq (NFData)
import Control.Lens (view)
import Control.Monad ((<=<), forM)
import Control.Monad.Fix
import Control.Monad.Reader.Class (ask, MonadReader (local))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT (ContT))
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Data.Align (Semialign(alignWith))
import Data.Distributive (Distributive(distribute))
import Data.Foldable (foldl', fold)
import Data.Function ((&))
import Data.Functor ((<&>), void)
import Data.Functor.Classes (Eq1(liftEq))
import Data.Maybe (fromMaybe)
import Data.Pair (Pair(..))
import Data.Semialign.Indexed (SemialignWithIndex (ialignWith))
import Data.These (These(..))
import GHC.Generics (Generic)
import GHC.StableName (StableName)
import GHC.Stack (HasCallStack)
import Pudding.Core.Eval
import Pudding.Core.Types
import Pudding.Semantics.Universes.Evidence (Relation(Equal, LessThanEqual))
import Pudding.Types.Monads (Proving, bindNeut, Constraining (constrainULevel))
import qualified Data.FastEq as FastEq
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Vector as Vector
import qualified Pudding.Types.Monads as M
import qualified Pudding.Types.Stack as Stack



-- validate :: "term" @:: Term -> "type" @:: Eval



-- Validate the type of a term, as an evaluated type
validate :: Proving m => HasCallStack => "term" @:: Term -> m ("type" @:: Eval)
validate = validateOrNot True
-- Validate and quote back to a term
validateQuote :: Proving m => HasCallStack => "term" @:: Term -> m ("type" @:: Term)
validateQuote = M.quote <=< validate
-- Validate in a context of neutrals
-- validateQuoteNeutrals :: HasCallStack => Globals -> ["type" @:: Term] -> "term" @:: Term -> "type" @:: Term
-- validateQuoteNeutrals globals localTypes = validateQuote $
--   mapCtx (\_ lvl ty -> (ty, neutralVar lvl)) $ evalCtx $
--     ctxOfList globals $ (BFresh,) <$> localTypes
-- Do not validate, but just assemble the type
quickTermType :: Proving m => HasCallStack => "term" @:: Term -> m ("type" @:: Eval)
quickTermType = validateOrNot False


-- Typecheck and share partial evaluation of globals

-- TODO: make sure definitions are acyclic!
bootGlobals, bootGlobalDefns, bootGlobalTypes :: (MonadFix m, Proving m)
  => HasCallStack => Globals -> m Globals
bootGlobals = bootGlobalDefns <=< bootGlobalTypes

bootGlobalDefns globals = mdo
  newDefns <- forM (globalDefns globals) \case
    GlobalDefn _ _ (GlobalTerm defn _) -> do
      ty <- typeofGlobal defn
      return $ GlobalDefn (arityOfTerm defn) ty (globalTerm defn)
  let newGlobals = globals { globalDefns = newDefns }
  let ctx = ctxOfGlobals newGlobals
  let globalTerm tm = GlobalTerm tm (evalGlobal tm)
  let evalGlobal = undeferred . eval ctx
  let typeofGlobal tm = do
        ty <- validate tm
        return $ GlobalTerm (quote (void ctx) ty) (undeferred ty)
  return newGlobals

bootGlobalTypes globals =
  pure $ globals { globalDefns = globalDefns globals `disjointUnion` constructors (globalTypes globals) }
  where
  disjointUnion = Map.union
  -- disjointUnion = Map.unionWithKey \k _ _ -> error $ "Duplicate global: " <> show k
  fakeGlobal tm = GlobalDefn (arityOfTerm tm) undefined (GlobalTerm tm undefined)
  constructors = fold . Map.mapWithKey \typeName -> \case
    GlobalTypeInfo { typeParams, typeIndices, typeConstrs } -> fold
      -- The type constructor: take all of the parameters and the indices,
      -- and then make the fully applied type constructor term.
      [ Map.singleton typeName $ fakeGlobal $
          abstract (Vector.toList typeParams <> Vector.toList typeIndices) $
            TTyCtor mempty typeName (toVars (Vector.length typeIndices) typeParams) (toVars 0 typeIndices)
      -- The term constructors: take all of the parameters and constructor
      -- arguments, then make the fully applied inductive constructor. (Note
      -- that the type indices are inferred from the parameters and arguments.)
      , flip Map.mapWithKey typeConstrs \ctorName (ConstructorInfo { ctorArguments }) -> fakeGlobal $
          abstract (Vector.toList typeParams <> Vector.toList ctorArguments) $
            TTmCtor mempty (typeName, ctorName) (toVars (Vector.length ctorArguments) typeParams) (toVars 0 ctorArguments)
      ]
  -- Form repeated lambdas to turn the raw constructor into a curried function
  abstract ((p, b, paramType) : more) focus =
    TLambda mempty p b paramType $ Scoped $ abstract more focus
  abstract [] focus = focus

  toVars :: forall i. Int -> Vector.Vector i -> Vector.Vector Term
  toVars skipped = mapWithLevel \(_, Index idx) _ ->
    TVar mempty $ Index $ idx + skipped

--------------------------------------------------------------------------------
-- Conversion checking: the algorithm for definitional equality / unification --
--------------------------------------------------------------------------------

-- | One-implementation-fits-all function for unification, subsumption,
-- | conversion checking, et cetera.
-- |
-- | Precondition: the types are already unified.
-- |
-- | Subsumption is, strictly speaking, only relevant to types and universes.
-- | During elaboration, a meaningful coercion between types may be inserted,
-- | and this coercion can be compositional through the types. Otherwise,
-- | the coercion must be the identity term in the sense of Core. It may still
-- | mediate between universe levels: that is not visible to the core, since
-- | everything is strongly parametric over universe level and hopefully
-- | polymorphic over levels too. However, subsumption could be considered
-- | for terms of other types serving in specific roles: for example,
-- | the `n` in `Fin n` could be considered for subsumption in the category
-- | `n <= m` in order to help generate coercions from monotonocity:
-- | `(n <= m) -> Fin n -> Fin m`.
subsume :: forall m r. Proving m => UnifyMode r -> Pair Eval -> m ("unified" @:: Pair Eval, "coercion" @:: Maybe r)
subsume _ (!evalL :# !evalR) | evalL FastEq.===? evalR = pure (evalL :# evalR, Nothing)
subsume mode (!evalL :# !evalR) = case evalL :# evalR of
  -- We unravel `EDeferred` slowly, to check if any names match up, before
  -- continuing with the main cases.
  EDeferred {} :# _ -> deferred [] [] (evalL :# evalR) (evalL :# evalR, Nothing) (subsume mode)
  _ :# EDeferred {} -> deferred [] [] (evalL :# evalR) (evalL :# evalR, Nothing) (subsume mode)

  -- Conversion checking for the main constructors is straightforward:
  EUniv _ univL :# EUniv _ univR -> do
    constrainULevel case unifyDir mode of
      Invariant  -> (uLevel univL, Equal, uLevel univR, ())
      RSubsumesL -> (uLevel univL, LessThanEqual, uLevel univR, ())
      -- opposite order!
      LSubsumesR -> (uLevel univR, LessThanEqual, uLevel univL, ())
    pure $ bified (EUniv mU univL :# EUniv mU univR)
  ELambda _ pL bdrL tyL bodyL :# ELambda _ pR bdrR tyR bodyR -> do
    (ty@tyL' :# tyR') <- cc (tyL :# tyR)
    let bdrU = unifyBdr bdrL bdrR
    (bodyL' :# bodyR') <- ccClo bdrU ty (bodyL :# bodyR)
    pure $ bified (ELambda mU pL bdrU tyL' bodyL' :# ELambda mU pR bdrU tyR' bodyR')
  EPi _ pL bdrL tyL bodyL :# EPi _ pR bdrR tyR bodyR -> do
    (ty@tyL' :# tyR') <- cc (tyL :# tyR)
    let bdrU = unifyBdr bdrL bdrR
    (bodyL' :# bodyR') <- ccClo bdrU ty (bodyL :# bodyR)
    pure (EPi mU pL bdrU tyL' bodyL' :# EPi mU pR bdrU tyR' bodyR', Nothing)

    -- |- h : I2 -> I1
    -- h |- f x : O1[h x] -> O2[x]
    -- g : Π (y : I1). O1[y]
    --   |- f x (g (h x)) : Π (x : I2). O2[x]

    -- -- Check with contravariance
    -- ((tyL', tyR'), mcoeI) <- subsume modeContra tyL tyR
    -- -- Take the smaller type
    -- ty <- case unifyDir modeContra of
    --   LSubsumesR -> pure tyR'
    --   _ -> pure tyL'
    -- let bdrU = unifyBdr bdrL bdrR
    -- bindNeut mempty bdrU ty do
    --   ((bodyL', bodyR'), mcoeO) <- subsume mode bodyL bodyR
    --   mcoe <- case (mcoeI, mcoeO) of
    --     (Nothing, Nothing) -> pure Nothing
    --     _ -> pure $ Just $ _
    --   pure ((EPi mU pL bdrU tyL' bodyL', EPi mU pR bdrU tyR' bodyR'), mcoe)

  ESigma _ pL bdrL tyL bodyL :# ESigma _ pR bdrR tyR bodyR -> do
    (ty@tyL' :# tyR') <- cc (tyL :# tyR)
    let bdrU = unifyBdr bdrL bdrR
    (bodyL' :# bodyR') <- ccClo bdrU ty (bodyL :# bodyR)
    pure (ESigma mU pL bdrU tyL' bodyL' :# ESigma mU pR bdrU tyR' bodyR', Nothing)

    -- |- f : I1 -> I2
    -- f |- h x : O1[x] -> O2[f x]
    -- (x, p) : Σ (x : I1). O1[x]
    --   |- (f x, h x p) : Σ (y : I2). O2[y]

  EPair _ tyL leftL rightL :# EPair _ tyR leftR rightR -> do
    (leftL' :# leftR') <- cc (leftL :# leftR)
    (rightL' :# rightR') <- cc (rightL :# rightR)
    pure (EPair mU tyL leftL' rightL' :# EPair mU tyR leftR' rightR', Nothing)

  ETyCtor _ nameL paramsL indicesL :# ETyCtor _ nameR paramsR indicesR -> do
    check $ nameL == nameR
    check $ List.length paramsL == List.length paramsR
    check $ List.length indicesL == List.length indicesR
    (paramsL' :# paramsR') <- distribute <$> alignCC (paramsL :# paramsR)
    (indicesL' :# indicesR') <- distribute <$> alignCC (indicesL :# indicesR)
    pure (ETyCtor mU nameL paramsL' indicesL' :# ETyCtor mU nameL paramsR' indicesR', Nothing)
  ETmCtor _ nameL paramsL argsL :# ETmCtor _ nameR paramsR argsR -> do
    check $ nameL == nameR
    check $ List.length paramsL == List.length paramsR
    check $ List.length argsL == List.length argsR
    (paramsL' :# paramsR') <- distribute <$> alignCC (paramsL :# paramsR)
    (argsL' :# argsR') <- distribute <$> alignCC (argsL :# argsR)
    pure (ETmCtor mU nameL paramsL' argsL' :# ETmCtor mU nameL paramsR' argsR', Nothing)
  ERecordTy _ fieldsL :# ERecordTy _ fieldsR -> do
    check $ Map.keys fieldsL == Map.keys fieldsR
    -- TODO: subsumption
    (fieldsL' :# fieldsR') <- distribute <$> alignCC (fieldsL :# fieldsR)
    pure (ERecordTy mU fieldsL' :# ERecordTy mU fieldsR', Nothing)
  ERecordTm _ fieldsL :# ERecordTm _ fieldsR -> do
    check $ Map.keys fieldsL == Map.keys fieldsR
    (fieldsL' :# fieldsR') <- distribute <$> alignCC (fieldsL :# fieldsR)
    pure (ERecordTy mU fieldsL' :# ERecordTy mU fieldsR', Nothing)
  ELift _ tyL :# ELift _ tyR ->
    -- Take the subsumption of the underlying types and splice–quote it
    subsumpAdapter (ELift mempty) (tyL :# tyR) \f -> adaptLam \inner ->
      EQuote mempty $ doApp f $ doPrj inner (NSplice mempty)
  EQuote _ tmL :# EQuote _ tmR -> subsume mode (tmL :# tmR) <&> first (fmap (EQuote mempty))

  -- Handle some eta conversions (but not unit-type eta, which needs to be
  -- type-directed)
  EPair _ ty _ _ :# _ -> subsume mode (evalL :# etaPair ty evalR)
  _ :# EPair _ ty _ _ -> subsume mode (etaPair ty evalL :# evalR)
  ERecordTm _ fieldsL :# _ -> subsume mode (evalL :# etaRecord fieldsL evalR)
  _ :# ERecordTm _ fieldsR -> subsume mode (etaRecord fieldsR evalL :# evalR)
  ELambda _ _ bdr ty body :# _ ->
    M.bindNeut mempty bdr ty \_ !arg ->
      subsume mode (instantiateClosure body arg :# doApp evalR arg)
  _ :# ELambda _ _ bdr ty body ->
    M.bindNeut mempty bdr ty \_ !arg ->
      subsume mode (doApp evalL arg :# instantiateClosure body arg)

  -- Splicing is a definitional isomorphism
  ENeut (Neutral focusL (prjsL :> NSplice _)) :# ENeut (Neutral focusR (prjsR :> NSplice _)) ->
    subsume mode (ENeut (Neutral focusL prjsL) :# ENeut (Neutral focusR prjsR))

  -- The default case of neutrals (variables) is easy to check: check projections
  -- pairwise. Dealing with lazily inlined globals requires checking via
  -- inlining if the normal approach failed to unify them. Finally, dealing with
  -- holes will require some particular thought.
  ENeut (Neutral focusL prjsL) :# ENeut (Neutral focusR prjsR)
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
  _ -> conversionCheckGlobal

  -- TODO: Finally we handle eta for subsingleton types
  _ -> error "Conversion check failed"

  where
  -- Concatenate metadata (this is what the monoid instance is designed for!)
  mU = view metadata evalL <> view metadata evalR

  -- The mode for recursing in conversion checking mode
  -- under an injective constructor
  modeCC = UnifyMode Invariant IdentitySubsumption (stillInjective mode)
  -- Contravariant mode, just flip the relation of left and right
--   modeContra = case unifyDir mode of
--     LSubsumesR -> UnifyMode RSubsumesL (shouldSubsume mode) (stillInjective mode)
--     RSubsumesL -> UnifyMode LSubsumesR (shouldSubsume mode) (stillInjective mode)
--     Invariant  -> UnifyMode Invariant  (shouldSubsume mode) (stillInjective mode)

  cc :: Pair Eval -> m (Pair Eval)
  cc pair = fst <$> subsume modeCC pair

  subsumpAdapter :: (Eval -> Eval) -> Pair Eval -> (Eval -> m Eval) -> m (Pair Eval, Maybe r)
  subsumpAdapter recons pair adapt = subsume mode pair >>= \case
    (tys, Just coe) | GenerateSubsumption <- shouldSubsume mode -> do
      coe' <- adapt coe
      pure (recons <$> tys, Just coe')
    r -> pure r

  adaptLam :: (Eval -> Eval) -> m Eval
  adaptLam f = do
    ctx <- M.askEvalCtx
    let
      bdr = BFresh
      inputTy = case unifyDir mode of
        LSubsumesR -> evalR
        _ -> evalL
    pure $ mkHOAS ctx bdr inputTy f

  ccClo :: Binder -> "type" @:: Eval -> Pair Closure -> m (Pair Closure)
  ccClo bdrU ty (bodyL :# bodyR) = do
    bodys' <- bindNeut mempty bdrU ty \_ var -> do
      bodys' <- cc $ instantiateClosure <$> (bodyL :# bodyR) <*> pure var
      traverse M.quote bodys'
    saved <- M.askEvalCtx
    pure $ bodys' <&> Closure saved bdrU . Scoped

  check :: Bool -> m ()
  check False = ccFailed
  check _ = pure ()

  ccFailed :: forall any. m any
  ccFailed = M.fatal "Conversion check failed"

  alignCC :: forall f. Eq1 f => Semialign f => Traversable f => Pair (f Eval) -> m (f (Pair Eval))
  alignCC (itemsL :# itemsR) | not (liftEq (\_ _ -> True) itemsL itemsR) = ccFailed
  alignCC (itemsL :# itemsR) = sequence (alignWith aligned itemsL itemsR)
    where
    aligned = \case
      This _ -> ccFailed
      That _ -> ccFailed
      These x y -> cc (x :# y)

  -- Helpers for results

  bified es = (es, Nothing)
  unifyBdr bdrL _bdrR = bdrL

  deferred :: forall ret. [StableName Eval] -> [StableName Eval] -> Pair Eval -> ret -> (Pair Eval -> m ret) -> m ret
  -- Short circuit on matching `EDeferred` stable names!
  deferred namesL namesR _ match _ | not (List.null (List.intersect namesL namesR)) = pure match
  -- Force the terms pairwise if possible
  deferred namesL namesR (EDeferred (Deferred _ _ _ mnameL tmL) :# EDeferred (Deferred _ _ _ mnameR tmR)) match nomatch =
    deferred (maybe id (:) mnameL namesL) (maybe id (:) mnameR namesR) (tmL :# tmR) match nomatch
  -- Check for holes at each step

  -- _
  deferred namesL namesR (EDeferred (Deferred _ _ _ mnameL tmL) :# tmR) match nomatch | mnameR <- Nothing =
    deferred (maybe id (:) mnameL namesL) (maybe id (:) mnameR namesR) (tmL :# tmR) match nomatch
  deferred namesL namesR (tmL :# EDeferred (Deferred _ _ _ mnameR tmR)) match nomatch | mnameL <- Nothing =
    deferred (maybe id (:) mnameL namesL) (maybe id (:) mnameR namesR) (tmL :# tmR) match nomatch
  -- No stable names matched, force the terms and do regular conversion checking
  deferred _ _ (tmL :# tmR) _ nomatch = nomatch (tmL :# tmR)


  -- Check what the neutral is blocked on: if it is a neutral variable,
  -- they *must* be the same variable (à la skolem variables)
  checkFocus focusL focusR = case (focusL, focusR) of
    (NVar _ lvlL, NVar _ lvlR) -> lvlL == lvlR
    (NHole _ holeL ctxL, NHole _ holeR ctxR) -> holeL == holeR
    -- We also check globals separately if it fails
    (NGlobal _ _ nameL, NGlobal _ _ nameR) -> nameL == nameR
    (_, _) -> False -- FIXME: handle holes via unification!!
  checkPrjs shouldCC = \case
    (moreL :> NApp _ _ argL, moreR :> NApp _ _ argR) ->
      shouldCC argL argR && checkPrjs shouldCC (moreL, moreR)
    (moreL :> NFst _, moreR :> NFst _) ->
      checkPrjs shouldCC (moreL, moreR)
    (moreL :> NSnd _, moreR :> NSnd _) ->
      checkPrjs shouldCC (moreL, moreR)
    (moreL :> NSplice _, moreR :> NSplice _) ->
      checkPrjs shouldCC (moreL, moreR)
    (moreL :> NField _ fieldL, moreR :> NField _ fieldR) ->
      fieldL == fieldR && checkPrjs shouldCC (moreL, moreR)
    (Nil, Nil) -> True
    -- Differing lengths or differing projections
    (_, _) -> False

  conversionCheckGlobal = do
    forcedL <- M.forceGlobal evalL
    forcedR <- M.forceGlobal evalR
    case (forcedL, forcedR) of
      -- If we do not make progress on either as a global, then conversion checking
      -- fails: they were different constructors in the AST and semantically
      (Nothing, Nothing) -> error "Conversion checking failed"
      -- Retry with one or both being inlined now
      _ -> subsume mode (fromMaybe evalL forcedL :# fromMaybe evalR forcedR)


-- Conversion checking is the algorithm for definitional equality used during
-- typechecking: specifically it refers to the process of finding out if a term
-- can be converted from one type to another, but with dependent types, it needs
-- to be a general algorithm for definitional equality.
--
-- Note: we care that the happy path is fast, more than failing fast for
-- mismatches.

-- conversionCheck :: HasCallStack => Ctx () -> Eval -> Eval -> Bool



--------------------------------------------------------------------------------
-- Type inference / checking / validation                                     --
--------------------------------------------------------------------------------

-- External telescope
type ExTeleScoping m r = ContT r (ReaderT EvalCtx m)

-- Infer the type of the term, either checking the whole tree as it goes if
-- `should = True`, or just doing the minimal work to return the inferred
-- type if `should = False`.
validateOrNot :: forall m. Proving m => Bool -> HasCallStack => "term" @:: Term -> m ("type" @:: Eval)
validateOrNot should = \case
  TVar _ idx -> do
    ctx <- M.askCtx
    checkFor "idx is nonnegative" (idx >= Index 0)
    checkFor "idx fits in the current context" (idx < Index (size ctx))
    pure $ fst (ctx @@: idx)
  TGlobal _ name -> do
    M.lookupDefn name >>= \case
      Nothing -> do
        Globals { globalDefns = defns } <- M.askGlobals
        M.fatal $ "Undefined global " <> show name <>
          if Map.size defns == 0 then " (global context is empty)" else ""
      Just (GlobalDefn _ (GlobalTerm _ ty) _) -> pure ty
  THole _ _fresh _ -> M.fatal "typeof hole not implemented"
  TUniv meta univ -> pure $ EUniv meta univ -- FIXME universe
  TAscribe _ tm ty -> do
    tyAct <- vv tm
    tyExp <- ee ty
    tyExp <$ cc "Bad ascription" tyAct tyExp
  TLet _ b ty tm (Scoped body) -> do
    tyAct <- vv tm
    tyExp <- ee ty
    val <- M.eval tm
    might $ cc "Bad let ascription" tyExp tyAct
    M.bindVar b (tyExp, val) do
      validateOrNot should body
  TLambda meta p b ty body ->
    validateScoped b ty body >>= \case
      (argTy, bodyTy) -> do
        ctx <- M.askEvalCtx
        pure $ EPi meta p b argTy $ Closure ctx b $
          -- We have to quote it back into a `Term`, mostly for when the
          -- neutral variable we used for typechecking is actually instantiated
          -- at an application site
          Scoped $ quote (void ctx :> (b, ())) bodyTy
  TPi _ _ b ty body -> do
    -- Π(x : ty : U). (body : U)
    univL <- vvv ty
    univR <- force . snd =<< validateScoped b ty body
    case (univL, univR) of
      (EUniv m1 u1, EUniv m2 _u2) -> pure $ EUniv (m1 <> m2) u1 -- FIXME universe
      _ -> M.fatal "Bad pi type"
  TSigma _ _ b ty body -> do
    univL <- vvv ty
    univR <- force . snd =<< validateScoped b ty body
    case (univL, univR) of
      (EUniv m1 u1, EUniv m2 _u2) -> pure $ EUniv (m1 <> m2) u1 -- FIXME universe
      _ -> M.fatal "Bad sigma type"
  TPair _ ty left right -> do
    might $ void $ validateType ty
    M.eval ty >>= \case
      tyVal@(ESigma _ _ _ fstTy body) -> do
        tyVal <$ might do
          cc "fst type mismatch" fstTy =<< vv left
          outTy <- instantiateClosure body <$> M.eval left
          cc "snd type mismatch" outTy =<< vv right
      _ -> M.fatal "bad pair type"
  TFst _ tm -> vvv tm >>= \case
    ESigma _ _ _ ty _ -> pure ty
    _ -> M.fatal "Bad fst"
  TSnd _ tm -> vvv tm >>= \case
    ESigma _ _ _ _ body -> do
      val <- M.eval tm
      pure $ instantiateClosure body (doPrj val (NFst mempty))
    _ -> M.fatal "Bad snd"
  TApp _ _ fun arg -> do
    funTy <- vvv fun
    argTy <- vv arg
    case (funTy, argTy) of
      (EPi _ _ _ argTyExpected body, argTyActual) -> do
        might $ cc "argument type mismatch" argTyExpected argTyActual
        val <- M.eval arg
        pure $ instantiateClosure body val
      _ -> M.fatal "Bad app"
  TTyCtor _ typeName params indices -> do
    M.lookupType typeName >>= \case
      Just (GlobalTypeInfo { typeParams, typeIndices, typeConstrs = _ }) -> do
        might $ checkFor "Wrong number of parameters" (Vector.length params == Vector.length typeParams)
        might $ checkFor "Wrong number of indices" (Vector.length indices == Vector.length typeIndices)
        startTelescoping do
          validateTelescope "Invalid type constructor parameter" 0 params typeParams
          validateTelescope "Invalid type constructor index" 0 indices typeIndices
          -- FIXME universe
          pure $ EUniv mempty (ULevel (Fresh 0) (Fresh 0))
      _ -> M.fatal "Bad type constructor name"
  TTmCtor _ (typeName, ctorName) params args -> do
    M.lookupType typeName >>= \case
      Just (GlobalTypeInfo { typeParams, typeIndices = _, typeConstrs })
        | Just (ConstructorInfo { ctorArguments, ctorIndices }) <- Map.lookup ctorName typeConstrs -> do
        might $ checkFor "Wrong number of parameters" (Vector.length params == Vector.length typeParams)
        startTelescoping do
          validateTelescope "Invalid constructor parameter" 0 params typeParams
          ctxParams <- ask
          validateTelescope "Invalid constructor argument" 0 args ctorArguments
          ctxArgs <- ask
          let
            -- the parameters were already evaluated onto the first stack
            paramValues = Vector.fromList $ snd <$> ctxToList ctxParams
            -- then we need to evaluate the indices, now that the arguments are
            -- all bound as well
            indexValues = eval ctxArgs <$> ctorIndices
          pure $ ETyCtor mempty typeName paramValues indexValues
      _ -> M.fatal "Bad constructor name"
  TCase _ motive cases scrutinee -> do
    might do
      ctx <- M.askCtx
      vvv scrutinee >>= \case
        ETyCtor _ typeName chosenParams _ | applyParams <- Stack.fromFoldable chosenParams ->
          case Map.lookup typeName (globalTypes $ ctxGlobals ctx) of
            Just tyInfo -> do
              motiveTy <- vv motive
              typeConstructor <- ee (makeMotiveType typeName tyInfo)
              cc "case motive" motiveTy (doApps typeConstructor applyParams)
              motiveVal <- M.eval motive
              !caseRecordType <- {- traceEval "caseRecordType" <$> -} ee (makeCaseRecordType typeName tyInfo)
              !caseType <- {- traceEval "caseType" <$> -} M.progressGlobal $ doApps caseRecordType (applyParams :> motiveVal)
              cc "Wrong case types" caseType =<< vv cases
              pure ()
            _ -> M.fatal "Undefined type constructor"
        _ty -> M.fatal "Not a type constructor in case annotation" -- $ termTrace "Not a type constructor in case annotation" $ quote quoteCtxHere _ty
    liftA2 doApp (ee motive) (M.eval scrutinee)
  TRecordTy _ fields -> uncurry EUniv <$>
    -- FIXME universe
    foldl' (\(m1, u1) (EUniv m2 _u2) -> (m1 <> m2, u1)) (mempty, ULevel (Fresh 0) (Fresh 0)) <$> traverse vv fields
  TRecordTm meta fields -> ERecordTy meta <$> traverse vv fields
  TField _ focus field -> vvv focus >>= \case
    ERecordTy _ fields | Just ty <- Map.lookup field fields -> pure ty
    _ -> M.fatal "Bad record field"
  TLift _ ty -> vvv ty -- FIXME universe
  TQuote meta tm -> ELift meta <$> vv tm
  TSplice _ tm -> vvv tm >>= \case
    ELift _ ty -> pure ty
    _ -> M.fatal "Bad splice"
  where

  might act | should = act
  might _ = pure ()

  -- TODO: might?
  validateType ty = vvv ty >>= \case
    EUniv _ _ -> M.eval ty
    _ -> M.fatal "Expected a valid type"

  -- TODO: subsumption
  cc :: HasCallStack => String -> Eval -> Eval -> m ()
  cc _err l r | should =
    void $ subsume (UnifyMode Invariant IdentitySubsumption StillInjective) (l :# r)
  cc _ _ _ = pure ()

  vv = validateOrNot should
  vvv = (=<<) force . vv

  -- FIXME: make sure globals are never deferred
  force val = do
    ctx <- M.askEvalCtx
    pure $ withForced ctx id $ undeferred val

  checkFor _ True = pure ()
  checkFor err False = M.fatal err

  validateScoped :: Binder -> "arg type" @:: Term -> ScopedTerm -> m ("arg type" @:: Eval, "body type" @:: Eval)
  validateScoped bdr ty (Scoped body) = do
    tyVal <- validateType ty
    bodyTy <- M.bindNeut mempty bdr tyVal \_ _ ->
      validateOrNot should body
    pure (tyVal, bodyTy)

  -- Validate then evaluate
  ee :: Term -> m Eval
  -- FIXME: rnf on the left here does not terminate...?
  ee tm = do
    might $ void $ vv tm
    M.eval tm

  -- _noWarn = (traceEval, traceTerm)
  -- traceEval desc = traceTermWith desc (quote quoteCtxHere)
  -- traceTerm desc = traceTermWith desc id
  -- traceTermWith :: forall x. String -> (x -> Term) -> x -> x
  -- traceTermWith desc fn = traceWith (termTrace desc . fn)
  -- termTrace desc tm = desc <> ": " <> do
  --   T.unpack $ P.format P.Ansi $ P.printCore tm (P.PS 0 (size ctx))

  -- Validating a dependent telescope is a little more tricky, but mostly it is
  -- just a lot of data to plumb around.
  validateTelescope ::
    "error" @:: String ->
    "current index" @:: Int ->
    "values" @:: Vector.Vector Term ->
    "telescope" @:: Vector.Vector (Plicit, Binder, Term) ->
    ExTeleScoping m r ()
  validateTelescope mismatchError i valueVector typeVector =
    case (valueVector Vector.!? i, typeVector Vector.!? i) of
      (Just value, Just (_, binder, tyTerm)) -> do
        ctorCtx <- lift $ lift M.askCtx
        typeCtx <- ask
        let
          -- Eval the telescope type first, in the context reserved for the
          -- inductive type, starting from the global context
          tyEval = eval typeCtx tyTerm
        -- Next we typecheck `value` against `tyEval`
        lift $ lift $ might do
          valueTy <- validateOrNot should value
          cc (mismatchError <> " " <> show i) valueTy tyEval
        -- Now we extend `typeCtx` with the new value (laziness is nice here)
        ContT $ local (:> (binder, eval (toEvalCtx ctorCtx) value)) . ($ ())
        -- Proceed with the next index `i+1`
        validateTelescope mismatchError (i+1) valueVector typeVector
      _ -> pure ()

  startTelescoping :: forall r. ExTeleScoping m r r -> m r
  startTelescoping (ContT act) = do
    ctx <- M.askCtx
    let start = ctxOfGlobals $ ctxGlobals ctx
    runReaderT (act pure) start

  toEvalCtx = mapCtx (\_ _ (_, tm) -> tm)

alignAll :: SemialignWithIndex i f => Foldable f => f x -> f y -> (i -> These x y -> Bool) -> Bool
alignAll xs ys f = and $ ialignWith f xs ys

-- | The type of the motive for the given inductive type:
-- it takes the indices of the inductive type as arguments
-- and then returns a type (the motive at those indices).
--
-- We need to abstract over the *parameters* of the type, so to keep it as a
-- closed term, we take those as lambda arguments for the caller to apply.
makeMotiveType :: Name -> GlobalTypeInfo -> Term
makeMotiveType typeName (GlobalTypeInfo { typeParams, typeIndices }) =
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
    chosenType = TTyCtor mempty typeName
      (Vector.imap (const . chosenParam) typeParams)
      (Vector.imap (const . chosenIndex) typeIndices)
    -- And a motive takes that specific type and returns the goal type for it
    motive = TPi mempty Explicit BUnused chosenType $ Scoped (TUniv mempty (ULevel (Fresh 0) (Fresh 0))) -- FIXME universe
  in prependParams $ prependIndices motive

makeCaseRecordType :: Name -> GlobalTypeInfo -> Term
makeCaseRecordType typeName tyInfo@(GlobalTypeInfo { typeParams, typeConstrs }) =
  let
    -- Make a telescope of *lambdas* to accept the chosen parameter types
    prependParams inner = foldr prependParam inner typeParams
    prependParam (p, b, paramType) inner =
      TLambda mempty p b paramType $ Scoped inner
    -- Now take a motive for those parameters
    abstractedMotiveType = makeMotiveType typeName tyInfo
    chosenParamForMotive i = TVar mempty $ Index $ length typeParams - 1 - i
    chosenMotiveType = Vector.ifoldl
      (\motiveTypeFn i (p, _, _) -> TApp mempty p motiveTypeFn $ chosenParamForMotive i)
      abstractedMotiveType typeParams
    prependMotive inner = TLambda mempty Explicit BFresh chosenMotiveType $ Scoped inner
    applyParams abstracted = Vector.ifoldl
      (\fun i (p, _, _) -> TApp mempty p fun $ chosenParamForMotive (i - 1))
      abstracted typeParams
    applyParamsAndMotive abstracted =
      TApp mempty Explicit (applyParams abstracted) $ TVar mempty $ Index 0
    caseTypes = typeConstrs & Map.mapWithKey \ctorName ctorInfo ->
      applyParamsAndMotive $ makeCaseFnType typeName tyInfo ctorName ctorInfo
  in prependParams $ prependMotive $ TRecordTy mempty caseTypes

-- TODO: share this evaluation
makeCaseFnType :: Name -> GlobalTypeInfo -> Name -> ConstructorInfo -> Term
makeCaseFnType typeName tyInfo@(GlobalTypeInfo { typeParams, typeIndices = _ }) ctorName (ConstructorInfo { ctorArguments, ctorIndices }) =
  let
    -- Make a telescope of *lambdas* to accept the chosen parameter types
    prependParams inner = foldr prependParam inner typeParams
    prependParam (p, b, paramType) inner =
      TLambda mempty p b paramType $ Scoped inner
    -- Now take a motive for those parameters
    abstractedMotiveType = makeMotiveType typeName tyInfo
    chosenParamForMotive i = TVar mempty $ Index $ length typeParams - 1 - i
    chosenMotiveType = Vector.ifoldl
      (\motiveTypeFn i (p, _, _) -> TApp mempty p motiveTypeFn $ chosenParamForMotive i)
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
    chosenValue = TTmCtor mempty (typeName, ctorName)
      (Vector.imap (const . chosenParam) typeParams)
      (Vector.imap (const . chosenArgument) ctorArguments)
    -- And we know the abstract motive, waiting for indices and the constructed value
    givenMotive = TVar mempty (Index (length ctorArguments))
    -- So we should be able to just plug in the indices to the motive:
    -- (They are relative to the arguments abstracted in the same way)
    -- FIXME: this is not true! the parameters are one off! ugh
    relevantMotive = Vector.ifoldl
      -- FIXME: Plicit
      (\motiveFn i chosenIndex -> TApp mempty Explicit motiveFn (withMotive (i + Vector.length ctorArguments) chosenIndex))
      givenMotive ctorIndices
    appliedMotive = TApp mempty Explicit relevantMotive chosenValue
    -- And plug in the value from the arguments
  -- Now we fit it all together, then let the caller apply it
  in prependParams $ prependMotive $ prependArguments appliedMotive

data StrictPositivityM t
  = NotPositive
  | NotStrictlyPositive
  | PositivityIrrelevant t
  | StrictlyPositive t
  deriving stock (Eq, Ord, Functor, Foldable, Traversable, Generic)
  deriving anyclass (NFData)

instance Applicative StrictPositivityM where
  NotPositive <*> _ = NotPositive
  _ <*> NotPositive = NotPositive
  NotStrictlyPositive <*> _ = NotStrictlyPositive
  _ <*> NotStrictlyPositive = NotStrictlyPositive

  PositivityIrrelevant f <*> PositivityIrrelevant a = PositivityIrrelevant (f a)
  PositivityIrrelevant f <*> StrictlyPositive a = StrictlyPositive (f a)
  StrictlyPositive f <*> PositivityIrrelevant a = StrictlyPositive (f a)
  StrictlyPositive f <*> StrictlyPositive a = StrictlyPositive (f a)

  pure = PositivityIrrelevant

-- checkForType :: Name -> Either Eval Term -> Any
-- checkForType name = summarize $ Summarize
--   { onTerm = _
--   , onEval = _
--   , onNeutFocus = _
--   , onNeutPrj = _
--   }

-- strictlyPositiveCtorArg :: Name -> QuoteCtx -> Eval -> StrictPositivityM Term
-- strictlyPositiveCtorArg selfName ctx = go
--   where
--   go = test . undeferred
--   test (EPi _meta p b ty body) = do
--     irrelevant ty
--   test (ETyCtor _meta tyName params indices) = do
--     _
--   test ty = case irrelevant ty of
--     _ -> _
