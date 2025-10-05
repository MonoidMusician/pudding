module Pudding.Eval where

import Pudding.Types
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor (void)
import qualified Data.List as List
import Data.Maybe (fromMaybe)

eval :: EvalCtx -> Term -> Eval
eval = flip evaling
quote :: QuoteCtx -> Eval -> Term
quote = flip quoting

-- Turn a `Term` context into an `Eval` context, evaluating from the root
-- (global scope) to the top of the stack.
evalCtx :: Ctx Term -> Ctx Eval
evalCtx ctx@(Ctx { ctxStack = [] }) = ctx { ctxSize = 0, ctxStack = [] }
evalCtx ctx0@(Ctx { ctxStack = (bdr, one) : more }) =
  let ctx = evalCtx ctx0 { ctxStack = more }
  -- Patch sizes on the way out
  in ctx { ctxSize = ctxSize ctx + 1, ctxStack = (bdr, eval ctx one) : ctxStack ctx }


-- If you want to fully partially evaluate (ahem, normalize) a top-level `Term`.
-- Note that this does not handle eta expansion or eta reduction: those are
-- handled during conversion checking.
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
normalizeCtx ctx = quote (void ctx) . eval ctx

normalizeNeutrals :: Map Name GlobalInfo -> [Desc "type" Term] -> Term -> Term
normalizeNeutrals globals localTypes = normalizeCtx $
  mapCtx (\(_idx, lvl) _ty -> neutralVar lvl) $
    ctxOfList globals $ (BFresh,) <$> localTypes

------------------------------
-- Various helper functions --
------------------------------

-- Do a projection on `Eval`
doPrj :: Eval -> NeutPrj -> Eval
doPrj (ENeut (Neutral blocker prjs)) prj = ENeut (Neutral blocker (prj : prjs))
doPrj (EPair _ _ left _) (NFst _) = left
doPrj (EPair _ _ _ right) (NSnd _) = right
doPrj (ELambda _ _ _ _ body) (NApp _ arg) = instantiateClosure body arg
doPrj _ _ = error "Type error in doPrj"

doApp :: Desc "fun" Eval -> Desc "arg" Eval -> Eval
doApp fun arg = doPrj fun (NApp mempty arg)

doFst :: Eval -> Eval
doFst tgt = doPrj tgt (NFst mempty)

doSnd :: Eval -> Eval
doSnd tgt = doPrj tgt (NSnd mempty)

-- Do a stack of projections on `Eval`
doPrjs :: Eval -> [NeutPrj] -> Eval
doPrjs focus (prj : prjs) = doPrj (doPrjs focus prjs) prj
doPrjs focus [] = focus

-- Eta expand the pair constructor, for sigma types
etaPair :: Desc "type" Eval -> Desc "pair" Eval -> Eval
etaPair ty e = EPair mempty ty (doPrj e (NFst mempty)) (doPrj e (NSnd mempty))

-- Inline the global if it has reached its arity and its arguments are not all
-- neutrals themselves, otherwise keep it “neutral”.
checkGlobal :: forall t. Ctx t -> Eval -> Eval
checkGlobal ctx e@(ENeut (Neutral (NGlobal arity _ _name) prjs))
  | arity <= List.length prjs && not (idlePrjs prjs)
    = fromMaybe e (forceGlobal ctx e)
  where
  -- Neutral argument: see what happens with the rest
  idlePrjs (NApp _ (ENeut _) : prjs') = idlePrjs prjs'
  -- Have a concrete argument: reduce now, hopefully it simplifies
  idlePrjs (NApp _ _ : _) = False
  -- Have a different kind of projection: reduce now
  idlePrjs (_ : _) = False
  -- All arguments were neutral
  idlePrjs [] = True
checkGlobal _ e = e

-- Just evaluate a neutral global
forceGlobal :: forall t. Ctx t -> Eval -> Maybe Eval
forceGlobal ctx (ENeut (Neutral (NGlobal _ _ name) prjs)) =
  case Map.lookup name (ctxGlobals ctx) of
    Just (GlobalDefn _ _ (GlobalTerm _ evaled)) -> Just (doPrjs evaled prjs)
    _ -> Nothing
forceGlobal _ _ = Nothing

-- Capture a closure during evaluation
captureClosure :: Binder -> ScopedTerm -> EvalCtx -> Closure
captureClosure = flip . Closure

-- Instantiate a closure
instantiateClosure :: Closure -> Eval -> Eval
instantiateClosure (Closure binder savedCtx (Scoped savedBody)) providedArg =
  evaling savedBody $ snoc savedCtx binder providedArg

--------------------------------------------------------------------------------
-- Implementations                                                            --
--------------------------------------------------------------------------------

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
  TGlobal meta name -> \ctx ->
    -- The global info is already looked up
    case Map.lookup name (ctxGlobals ctx) of
      -- We already have a shared lazy evaluation for a global definition
      Just (GlobalDefn arity _ (GlobalTerm _ evaled)) ->
        if arity == 0 then evaled else
          -- If it has a positive number of immediate arguments, then we let
          -- it block evaluation until they are filled with at least one non-
          -- neutral argument
          ENeut (Neutral (NGlobal arity meta name) [])
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
    case (undeferred $ evaling fun ctx, evaling arg ctx) of
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
        checkGlobal ctx $ ENeut (Neutral focus (NApp metaApp evalingArg : prjs))
      _ -> error "Type error: cannot apply to non-function"
  TPair meta ty left right ->
    EPair meta <$> evaling ty <*> evaling left <*> evaling right
  TFst meta term -> \ctx ->
    -- Again, we look to beta reduce, or add a projection to a neutral
    case undeferred $ evaling term ctx of
      -- If it reduces to a literal, it must be a pair by type correctness
      EPair _ _ left _ -> left
      -- Otherwise it must be a neutral: it does not have an actual value yet
      -- (it is waiting for a variable / hole), so we *record* that we want to
      -- apply `fst` to it when it does reduce -> this means that in quoting we
      -- can actually reconstruct the syntax around the neutral
      ENeut (Neutral focus prjs) ->
        checkGlobal ctx $ ENeut (Neutral focus (NFst meta : prjs))
      _ -> error "Type error: cannot project from non-sigma"
  TSnd meta term -> \ctx ->
    -- Again, we look to beta reduce, or add a projection to a neutral
    case undeferred $ evaling term ctx of
      EPair _ _ _ right -> right
      ENeut (Neutral focus prjs) ->
        checkGlobal ctx $ ENeut (Neutral focus (NSnd meta : prjs))
      _ -> error "Type error: cannot project from non-sigma"
  TUniv meta univ -> pure $ EUniv meta univ
  -- A hole is a neutral: we do not know its value yet. Thus we have to block
  -- on it and record its arguments or projections. This is contrary to the
  -- neutrals for abstract variables, which are introduced *outside* of eval.
  THole meta hole -> pure $ ENeut (Neutral (NHole meta hole) [])
  where
  undeferred (EDeferred _ _ _ _ tm) = undeferred tm
  undeferred tm = tm

-- Quoting takes a term that was evaluated to depth 1 (`Eval`) and turns it back
-- into a `Term`, calling `eval` on all closures to evaluate it fully.
quoting :: Eval -> QuoteCtx -> Term
quoting = eval2termWith False quotingClosure

-- We implement it via a generic function, to avoid duplication. (Duplication
-- itself is not too painful, but having to add 500 new cases every time you
-- add an AST node is painful.)
eval2termWith ::
  Desc "force globals" Bool ->
  (Closure -> Desc "type" Eval -> QuoteCtx -> ScopedTerm) ->
  Eval -> QuoteCtx -> Term
eval2termWith forceGlobals handleClosure = \case
  ENeut (Neutral focus prjs) -> \ctx ->
    let
      base = case focus of
        NVar meta lvl -> TVar meta (lvl2idx (ctxSize ctx) lvl)
        NHole meta hole -> THole meta hole
        NGlobal _ _ name
          | forceGlobals
          , Just (GlobalDefn _ _ (GlobalTerm term _)) <-
              Map.lookup name (ctxGlobals ctx) -> term
        NGlobal _arity meta name -> TGlobal meta name
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
  e2t = eval2termWith forceGlobals handleClosure

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

type TypeCtx = Ctx Term
type EvalTypeCtx = Ctx (Desc "type" Eval, Desc "value" Eval)

umax :: ULevel -> ULevel -> ULevel
umax (UBase l1) (UBase l2) = UBase (max l1 l2)
umax (UMeta l1) (UMeta l2) = UMeta (max l1 l2)
umax _ _ = error "Bad umax / unimplemented"

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
