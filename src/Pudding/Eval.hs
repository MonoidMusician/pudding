module Pudding.Eval where

import Pudding.Types
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor ((<&>))
import Pudding.Printer (Style (Ansi), format, printCore)
import qualified Data.Text as T
import Data.Coerce (coerce)
import GHC.StableName (StableName)
import qualified Data.List as List

captureClosure :: Binder -> ScopedTerm -> EvalCtx -> Closure
captureClosure = flip . Closure

instantiateClosure :: Closure -> Eval -> Eval
instantiateClosure (Closure binder savedCtx (Scoped savedBody)) providedArg =
  evaling savedBody $ snoc savedCtx binder providedArg

neutralVar :: Level -> Eval
neutralVar lvl = ENeut (Neutral (NVar mempty lvl) [])

eval :: EvalCtx -> Term -> Eval
eval = flip evaling
quote :: QuoteCtx -> Eval -> Term
quote = flip quoting

-- Share partial evaluation of globals
bootGlobals :: Map Name GlobalInfo -> Map Name GlobalInfo
bootGlobals globals = globals <&> \case
  GlobalDefn _ tm -> GlobalDefn (typeofGlobal tm) (globalTerm tm)
  global -> global
  where
  ctx = ctxOfGlobals globals
  globalTerm (GlobalTerm tm _) = GlobalTerm tm (evalGlobal tm)
  evalGlobal = eval ctx
  typeofGlobal :: GlobalTerm -> GlobalTerm
  typeofGlobal (GlobalTerm tm _) =
    let ty = typeof ctx tm
    in GlobalTerm ty (evalGlobal ty)

-- If you want to fully partially evaluate (ahem, normalize) a top-level `Term`.
normalize :: Map Name GlobalInfo -> Term -> Term
normalize globals original =
  let
    -- First we use `eval` to partially evaluate `Term` into `Eval`
    evaluated = eval (ctxOfGlobals globals) original
    -- Now we are left with something that is evaluated to depth 1
    -- (so it might have applied some functions and ended up with a `EPair` or
    -- something), but now we need to recursively normalize under binders:
    -- which is what `quote` does.
    quoted = quote (ctxOfGlobals globals) evaluated
    -- And now it is a `Term` again: core syntax that we can manipulate as a
    -- self-contained thing. (Whereas the `Closure`s in `Eval` contain
    -- frozen contexts that we can't deal with in any sensible way.)
    --
    -- `quoteSize` is just used to convert `Level` back to `Index`
  in quoted

normalizeCtx :: EvalCtx -> Term -> Term
normalizeCtx ctx = quote (mapCtx (\_ _ -> ()) ctx) . eval ctx

normalizeNeutrals :: Map Name GlobalInfo -> [Desc "type" Term] -> Term -> Term
normalizeNeutrals globals localTypes = normalizeCtx $
  mapCtx (\(_idx, lvl) _ty -> neutralVar lvl) $
    ctxOfList globals $ (\ty -> (BFresh, ty)) <$> localTypes

-- Normalization by Evaluation
-- - Much more efficient: avoids retraversing terms when possible
-- - Still can do full partial evaluation, but this work is split between
--   `eval` and `quote` now.
-- - `Closure` sometimes uses closures from the host language, which makes it
--   look weird/cool (and I don't think it buys you much), so that would be
--   `(Eval -> Eval)` via `\evalingArg -> evaling savedBody $ cons evalingArg savedCtx`
-- - But here we represent `Closure` explicitly as an ordinary ADT.
-- - Eval does as much work as it can in a single pass. Quoting makes it recur
--   under binders (into closures), to make it into a *partial* evaluator
--   (since `eval` handles neutrals nicely).
evaling :: Term -> EvalCtx -> Eval
evaling = \case
  -- If we have a variable
  TVar moreMeta idx -> \ctx ->
    -- Look it up by index: it must be in the context.
    -- Note that we do not generate neutrals here: they are put in the context
    -- only during *quoting* and *conversion checking*, where we must handle
    -- open terms (digging down below binders (λ, Π, Σ)) by seeding neutrals
    case indexCtx idx ctx of
      -- If it is a neutral, we should add metadata...
      ENeut (Neutral (NVar metaNeut lvl) []) ->
        ENeut (Neutral (NVar (metaNeut <> moreMeta) lvl) [])
      -- Otherwise we just pass the value from context along:
      -- the variable has done its job
      e -> e
  -- If we are looking at evaluating a global
  TGlobal _ name -> \ctx ->
    -- The global info is already looked up
    case Map.lookup name (ctxGlobals ctx) of
      -- We already have a shared lazy evaluation for a global definition
      Just (GlobalDefn _ (GlobalTerm _ evaled)) -> evaled
      -- Constructors are a bit tricky
      Just _ -> error "Not implemented yet"
      Nothing -> error $ "Could not find global " <> show name
  -- For a lambda
  TLambda meta plicit binder ty body ->
    -- We eval the type, but capture the body as a closure in *this* environment
    -- to restart evaluation later, when the argument's value is known (or neutral)
    ELambda meta plicit binder <$> evaling ty <*> captureClosure binder body
  -- Similar story
  TPi meta plicit binder ty body ->
    EPi meta plicit binder <$> evaling ty <*> captureClosure binder body
  -- Similar story
  TSigma meta plicit binder ty body ->
    ESigma meta plicit binder <$> evaling ty <*> captureClosure binder body
  -- Application is interesting
  TApp metaApp fun arg -> \ctx ->
    -- `($) :: (a -> b) -> a -> b` is strict in its first argument: we always
    -- want to evaluate that and see what it does: thus evaluating `fun` as
    -- `evaling fun ctx` and casing on it immediately, *not* examining the raw
    -- `fun :: Term` because that would just be inefficient at that point.
    case (evaling fun ctx, evaling arg ctx) of
      -- Beta redex: we can resume the body closure now that we know the value
      -- it was waiting for: `evalingArg`
      --
      -- (here we have a lazy interpreter in `evaling arg ctx` just because
      -- Haskell is lazy: `evalingArg` could be ignored by the `Closure`)
      (ELambda _ _ _ _ clo, evalingArg) ->
        instantiateClosure clo evalingArg
      -- If it was stuck as a neutral, we need to preserve the argument on the
      -- stack of projections to apply to the neutral variable
      (ENeut (Neutral focus prjs), evalingArg) ->
        ENeut (Neutral focus (NApp metaApp evalingArg : prjs))
      _ -> error "Type error: cannot apply to non-function"
  TPair meta ty left right ->
    EPair meta <$> evaling ty <*> evaling left <*> evaling right
  TFst meta term -> \ctx ->
    -- Again, we look to beta reduce, or add a projection to a neutral
    case evaling term ctx of
      -- If it reduces to a literal, it must be a pair by type correctness
      EPair _ _ left _ -> left
      -- Otherwise it must be a neutral: it does not have an actual value yet
      -- (it is waiting for a variable / hole), so we *record* that we want to
      -- apply `fst` to it when it does reduce -> this means that in quoting we
      -- can actually reconstruct the syntax around the neutral
      ENeut (Neutral focus prjs) ->
        ENeut (Neutral focus (NFst meta : prjs))
      _ -> error "Type error: cannot apply to non-function"
  TSnd meta term -> \ctx ->
    -- Again, we look to beta reduce, or add a projection to a neutral
    case evaling term ctx of
      EPair _ _ _ right -> right
      ENeut (Neutral focus prjs) ->
        ENeut (Neutral focus (NSnd meta : prjs))
      _ -> error "Type error: cannot apply to non-function"
  TUniv meta univ -> pure $ EUniv meta univ
  THole meta hole -> pure $ ENeut (Neutral (NHole meta hole) [])

-- Quoting takes a term that was evaluated to depth 1 (`Eval`) and turns it back
-- into a `Term`, calling `eval` on all closures to evaluate it fully.
quoting :: Eval -> QuoteCtx -> Term
quoting = eval2termWith quotingClosure

-- We implement it via a generic function, to avoid duplication. (Duplication
-- itself is not too painful, but having to add 500 new cases every time you
-- add an AST node is painful.)
eval2termWith ::
  (Closure -> Desc "type" Eval -> QuoteCtx -> ScopedTerm) ->
  Eval -> QuoteCtx -> Term
eval2termWith handleClosure = \case
  ENeut (Neutral focus prjs) -> \ctx ->
    let
      base = case focus of
        NVar meta lvl -> TVar meta (lvl2idx (ctxSize ctx) lvl)
        NHole meta hole -> THole meta hole
      go (prj : more) soFar = go more case prj of
        NApp meta arg -> TApp meta soFar (e2t arg ctx)
        NFst meta -> TFst meta soFar
        NSnd meta -> TSnd meta soFar
      go [] result = result
    in go prjs base
  EUniv meta univ -> pure $ TUniv meta univ
  ELambda meta plicit binder ty body ->
    TLambda meta plicit binder <$> e2t ty <*> handleClosure body ty
  EPi meta plicit binder ty body ->
    TPi meta plicit binder <$> e2t ty <*> handleClosure body ty
  ESigma meta plicit binder ty body ->
    TSigma meta plicit binder <$> e2t ty <*> handleClosure body ty
  EPair meta ty left right ->
    TPair meta <$> e2t ty <*> e2t left <*> e2t right
  EDeferred _ _ _ _ tm -> e2t tm
  where
  e2t = eval2termWith handleClosure

-- Quote a closure back into a syntactic term: this generates a neutral to be
-- a placeholder for the bound variable during evaluation, and then it restarts
-- evaluation on the frozen `Term` inside the `Closure`. This finishes
-- normalizing it.
--
-- Note: this calls directly into `quoting`.
quotingClosure :: Closure -> Eval -> QuoteCtx -> ScopedTerm
quotingClosure (Closure bdr savedCtx (Scoped savedBody)) argTy ctx =
  let
    -- This is the (only-ish) place that we create neutrals: when quoting.
    evalingArg = ENeut (Neutral (NVar mempty (Level (ctxSize ctx))) [])
  in Scoped $ quoting ((evaling savedBody $ snoc savedCtx bdr evalingArg) :: Eval) (snoc ctx bdr ())

-- If we don't want to fully normalize, we can turn `Eval` back into a `Term`
-- in the simplest way: copying the `Term` out of the `Closure` without any
-- further evaluation.
--
-- This actually needs more thought... the saved `Term` is an open term from a
-- different context, so `EvalCtx` would need to be converted and inlined at
-- least, with quoting at the correct level.
-- eval2term :: Eval -> QuoteCtx -> Term
-- eval2term = eval2termWith \(Closure savedCtx savedBody) _ _ -> term


conversionCheck :: EvalTypeCtx -> Eval -> Eval -> Bool
conversionCheck ctx evalL evalR = case (evalL, evalR) of
  (EDeferred {}, _) -> deferred [] [] evalL evalR
  (_, EDeferred {}) -> deferred [] [] evalL evalR
  (ENeut (Neutral focusL prjsL), ENeut (Neutral focusR prjsR)) ->
    let
      base = case (focusL, focusR) of
        (NVar _ lvlL, NVar _ lvlR) -> lvlL == lvlR
        (NHole _ holeL, NHole _ holeR) -> holeL == holeR
        (_, _) -> False -- FIXME
      go = \case
        (NApp _ argL : moreL, NApp _ argR : moreR) ->
          cc argL argR && go (moreL, moreR)
        (NFst _ : moreL, NFst _ : moreR) ->
          go (moreL, moreR)
        (NSnd _ : moreL, NSnd _ : moreR) ->
          go (moreL, moreR)
        ([], []) -> True
        (_, _) -> False
    in base && List.length prjsL == List.length prjsR && go (prjsL, prjsR)
  (EUniv _ univL, EUniv _ univR) -> univL == univR
  (ELambda _ _ bdrL tyL bodyL, ELambda _ _ bdrR tyR bodyR) ->
    ccScoped bdrL tyL bodyL bdrR tyR bodyR
  (EPi _ _ bdrL tyL bodyL, EPi _ _ bdrR tyR bodyR) ->
    ccScoped bdrL tyL bodyL bdrR tyR bodyR
  (ESigma _ _ bdrL tyL bodyL, ESigma _ _ bdrR tyR bodyR) ->
    ccScoped bdrL tyL bodyL bdrR tyR bodyR
  (EPair _ _ leftL rightL, EPair _ _ leftR rightR) ->
    cc leftL leftR && cc rightL rightR
  (_, _) -> False
  where
  cc = conversionCheck ctx
  ccScoped bdrL tyL bodyL bdrR tyR bodyR =
    let
      var = neutralVar $ Level $ ctxSize ctx
      ctx' = snoc ctx (BMulti bdrL bdrR) (tyL, var)
    in cc tyL tyR && conversionCheck ctx'
      (instantiateClosure bodyL var) (instantiateClosure bodyR var)
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

-- Infer the type of the term, checking the whole tree as it goes.
validate :: EvalTypeCtx -> Desc "term" Term -> Desc "type" Eval
validate ctx = \case
  TVar _ idx -> fst $ indexCtx idx ctx
  TGlobal _ name -> case Map.lookup name (ctxGlobals ctx) of
    Nothing -> error $ "Undefined global " <> show name
    Just (GlobalDefn (GlobalTerm _ ty) _) -> ty
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
        EPi meta p b argTy $ Closure b evalCtx $
          -- We have to quote it back into a `Term`, mostly for when the
          -- neutral variable we used for typechecking is actually instantiated
          -- at an application site
          Scoped $ quote (snoc quoteCtx b ()) bodyTy
  TPi _ _ b ty body ->
    -- Π(x : ty : U), (body : U)
    case (validate ctx ty, snd $ validateScoped b ty body) of
      (EUniv m1 u1, EUniv m2 u2) -> EUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad pi type"
  TSigma _ _ b ty body ->
    case (validate ctx ty, snd $ validateScoped b ty body) of
      (EUniv m1 u1, EUniv m2 u2) -> EUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad sigma type"
  TPair _ ty left right ->
    validateType ty `seq` case evalHere ty of
      tyVal@(ESigma _ _ _ fstTy body) ->
        cc "fst type mismatch" fstTy (validate ctx left) `seq`
        cc "snd type mismatch" (instantiateClosure body (evalHere left)) (validate ctx right) `seq`
        tyVal
      _ -> error "bad pair type"
  TFst _ tm -> case validate ctx tm of
    ESigma _ _ _ ty _ -> ty
    _ -> error "Bad fst"
  TSnd _ tm -> case validate ctx tm of
    ESigma _ _ _ _ body ->
      instantiateClosure body (doPrj (evalHere tm) (NFst mempty))
    _ -> error "Bad snd"
  TApp _ fun arg -> case (validate ctx fun, validate ctx arg) of
    (EPi _ _ _ argTyExpected body, argTyActual) ->
      cc "argument type mismatch" argTyExpected argTyActual `seq` instantiateClosure body (evalHere arg)
    _ -> error "Bad app"
  where
  validateType ty = case validate ctx ty of
    EUniv _ _ -> evalHere ty
    _ -> error "Expected a valid type"

  -- TODO: subsumption
  cc err l r = case conversionCheck ctx l r of
    True -> l
    False -> error err

  validateScoped :: Binder -> Desc "arg type" Term -> ScopedTerm -> (Desc "arg type" Eval, Desc "body type" Eval)
  validateScoped bdr ty (Scoped body) =
    let
      tyVal = validateType ty
      ctx' = snoc ctx bdr (tyVal, neutralVar $ Level $ ctxSize ctx)
    in (tyVal, tyVal `seq` validate ctx' body)

  evalHere = eval evalCtx
  evalCtx = mapCtx (\_ (_, tm) -> tm) ctx :: EvalCtx
  quoteCtx = mapCtx (\_ _ -> ()) ctx :: QuoteCtx


type TypeCtx = Ctx Term
type EvalTypeCtx = Ctx (Desc "type" Eval, Desc "value" Eval)

umax :: ULevel -> ULevel -> ULevel
umax (UBase l1) (UBase l2) = UBase (max l1 l2)
umax (UMeta l1) (UMeta l2) = UMeta (max l1 l2)
umax _ _ = error "Bad umax / unimplemented"

-- This functions as a proof that terms are intrinsically typed
typeof :: TypeCtx -> Term -> Term
typeof ctx = \case
  TVar _ idx -> getShifted idx (snd <$> ctxStack ctx)
  TGlobal _ name -> case Map.lookup name (ctxGlobals ctx) of
    Nothing -> error $ "Undefined global " <> show name
    Just (GlobalDefn (GlobalTerm ty _) _) -> ty
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

doPrj :: Eval -> NeutPrj -> Eval
doPrj (ENeut (Neutral blocker prjs)) prj = ENeut (Neutral blocker (prj : prjs))
doPrj (EPair _ _ left _) (NFst _) = left
doPrj (EPair _ _ _ right) (NSnd _) = right
doPrj (ELambda _ _ _ _ body) (NApp _ arg) = instantiateClosure body arg
doPrj _ _ = error "Type error in doPrj"

-- We are lazy with shifting terms: they enter the context completely unshifted,
-- and then when we want to pull one out, we shift by the appropriate amount
-- based on how much the context has grown.
getShifted :: Index -> [Term] -> Term
getShifted (Index idx) terms =
  -- We always shift at least one: index 0 is the most recent variable, but its
  -- type belongs to the context _before_ it was introduced
  shift (idx+1) (terms !! idx)

shift :: Int -> Term -> Term
shift = shiftFrom 0

-- Only indices >= base are affected, which is incremented under binders
shiftFrom :: Int -> Int -> Term -> Term
shiftFrom base delta = \case
  TVar meta (Index idx) -> TVar meta (Index (if idx >= base then idx + delta else idx))
  TGlobal meta name -> TGlobal meta name
  THole meta fresh -> THole meta fresh
  TUniv meta univ -> TUniv meta univ
  TLambda meta p b ty (Scoped body) ->
    TLambda meta p b (go ty) (Scoped (into body))
  TPi meta p b ty (Scoped body) ->
    TPi meta p b (go ty) (Scoped (into body))
  TSigma meta p b ty (Scoped body) ->
    TSigma meta p b (go ty) (Scoped (into body))
  TPair meta ty left right ->
    TPair meta (go ty) (go left) (go right)
  TFst meta tm -> TFst meta $ go tm
  TSnd meta tm -> TSnd meta $ go tm
  TApp meta fun arg -> TApp meta (go fun) (go arg)
  where
  go = shiftFrom base delta
  into = shiftFrom (base+1) delta
