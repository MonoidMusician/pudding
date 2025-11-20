module Pudding.Eval where

import Pudding.Types
import qualified Data.Map as Map
import Data.Functor (void)
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Pudding.Printer (Style (Ansi), formatCoreWithSpan)
import qualified Data.Text as T
import GHC.Stack (HasCallStack)
import qualified Pudding.Types.Stack as Stack

eval :: EvalCtx -> Term -> Eval
eval = flip evaling
quote :: QuoteCtx -> Eval -> Term
quote = flip quoting

-- Turn a `Term` context into an `Eval` context, evaluating from the root
-- (global scope) to the top of the stack.
evalCtx :: Ctx Term -> Ctx Eval
evalCtx = foldCtx ctxOfGlobals \_ (bdr, one) acc ->
  acc :> (bdr, eval acc one)

-- If you want to fully partially evaluate (ahem, normalize) a top-level `Term`.
-- Note that this does not handle eta expansion or eta reduction: those are
-- handled during conversion checking.
normalize :: Globals -> Term -> Term
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

normalizeNeutrals :: Globals -> ["type" @:: Term] -> Term -> Term
normalizeNeutrals globals localTypes = normalizeCtx $
  mapCtx (\_ lvl _ty -> neutralVar lvl) $
    ctxOfList globals $ (BFresh,) <$> localTypes

------------------------------
-- Various helper functions --
------------------------------

-- Do a projection on `Eval`
doPrj :: HasCallStack => Eval -> NeutPrj -> Eval
doPrj (ENeut (Neutral blocker prjs)) prj = ENeut (Neutral blocker (prjs :> prj))
doPrj (EPair _ _ left _) (NFst _) = left
doPrj (EPair _ _ _ right) (NSnd _) = right
doPrj (ELambda _ _ _ _ body) (NApp _ arg) = instantiateClosure body arg
doPrj (ERecordTm _ fields) (NField _ name) = fields Map.! name
doPrj (EConstr _meta (_tyName, conName) _params args) (NCase _ _ cases) =
  doApps (doField cases conName) (Stack.fromFoldable args)
doPrj (EDeferred _ _ _ _ term) prj = doPrj term prj
doPrj e prj = error $ mconcat
  [ "Type error in doPrj "
  , case prj of
      NApp _ _ -> "App"
      NFst _ -> "Fst"
      NSnd _ -> "Snd"
      NSplice _ -> "Splice"
      NCase {} -> "Case"
      NField _ _ -> "Field"
  , ":"
  -- FIXME: no scope available, indices will be wrong
  , "\n", T.unpack $ formatCoreWithSpan Ansi $ quote (ctxOfSize freshGlobals 100) e
  ]

doApp :: HasCallStack => "fun" @:: Eval -> "arg" @:: Eval -> Eval
doApp fun arg = doPrj fun (NApp mempty arg)

doFst :: HasCallStack => Eval -> Eval
doFst tgt = doPrj tgt (NFst mempty)

doSnd :: HasCallStack => Eval -> Eval
doSnd tgt = doPrj tgt (NSnd mempty)

doField :: HasCallStack => Eval -> Name -> Eval
doField tgt field = doPrj tgt (NField mempty field)

-- Do a stack of projections on `Eval`
doPrjs :: HasCallStack => Eval -> Stack NeutPrj -> Eval
doPrjs focus (prjs :> prj) = doPrj (doPrjs focus prjs) prj
doPrjs focus Nil = focus

doApps :: HasCallStack => Eval -> Stack Eval -> Eval
doApps focus = doPrjs focus . fmap (NApp mempty)

-- Eta expand the pair constructor, for sigma types
etaPair :: HasCallStack => "type" @:: Eval -> "pair" @:: Eval -> Eval
etaPair ty e = EPair mempty ty (doFst e) (doSnd e)

-- Eta expand a record constructor
etaRecord :: HasCallStack => "fields" @:: Map.Map Name ignored -> "record" @:: Eval -> Eval
etaRecord fields e = ERecordTm mempty $ Map.mapWithKey (const . doField e) fields

-- Inline the global if it has reached its arity and its arguments are not all
-- neutrals themselves, otherwise keep it “neutral”.
checkGlobal :: forall t. Ctx t -> Eval -> Eval
checkGlobal ctx e@(ENeut (Neutral (NGlobal arity _ _name) prjs))
  | arity <= List.length prjs && not (idlePrjs prjs)
    = fromMaybe e (forceGlobal ctx e)
  where
    idlePrjs :: Stack NeutPrj -> Bool
    -- Neutral argument: see what happens with the rest
    idlePrjs (prjs' :> NApp _ (ENeut _)) = idlePrjs prjs'
    -- Have a concrete argument: reduce now, hopefully it simplifies
    idlePrjs (_ :> NApp _ _) = False
    -- Have a different kind of projection: reduce now
    idlePrjs (_ :> _) = False
    -- All arguments were neutral
    idlePrjs Nil = True
checkGlobal _ e = e

-- Just evaluate a neutral global
forceGlobal :: forall t. HasCallStack => Ctx t -> Eval -> Maybe Eval
forceGlobal ctx (ENeut (Neutral (NGlobal _ _ name) prjs)) =
  case Map.lookup name (globalDefns $ ctxGlobals ctx) of
    Just (GlobalDefn _ _ (GlobalTerm _ evaled)) ->
      Just (checkGlobal ctx (doPrjs evaled prjs))
    _ -> Nothing
forceGlobal _ _ = Nothing

-- Capture a closure during evaluation
captureClosure :: Binder -> ScopedTerm -> EvalCtx -> Closure
captureClosure = flip . Closure

-- Instantiate a closure
instantiateClosure :: Closure -> Eval -> Eval
instantiateClosure (Closure binder savedCtx (Scoped savedBody)) providedArg =
  evaling savedBody $ savedCtx :> (binder, providedArg)


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
evaling :: HasCallStack => Term -> EvalCtx -> Eval
evaling = \case
  -- If we have a variable
  TVar moreMeta idx -> \ctx ->
    -- Look it up by index: it must be in the context.
    -- Note that we do not generate neutrals here: they are put in the context
    -- only during *quoting* and *conversion checking*, where we must handle
    -- open terms (digging down below binders (λ, Π, Σ)) by seeding neutrals
    case ctx @@: idx of
      -- If it is a neutral, we should add metadata...
      ENeut (Neutral (NVar metaNeut lvl) Nil) ->
        ENeut (Neutral (NVar (metaNeut <> moreMeta) lvl) Nil)
      -- Otherwise we just pass the value from context along:
      -- the variable has done its job
      e -> e
  -- If we are looking at evaluating a global
  TGlobal meta name -> \ctx ->
    -- The global info is already looked up
    case Map.lookup name (globalDefns $ ctxGlobals ctx) of
      -- We already have a shared lazy evaluation for a global definition
      Just (GlobalDefn arity _ (GlobalTerm _ evaled)) ->
        if arity == 0 then evaled else
          -- If it has a positive number of immediate arguments, then we let
          -- it block evaluation until they are filled with at least one non-
          -- neutral argument
          ENeut (Neutral (NGlobal arity meta name) Nil)
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
        checkGlobal ctx $ ENeut $ Neutral
          { neutralBlocking = focus
          , neutralSpine = prjs :> NApp metaApp evalingArg
          }
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
        checkGlobal ctx $ ENeut (Neutral focus (prjs :> NFst meta))
      _ -> error "Type error: cannot project from non-sigma"
  TSnd meta term -> \ctx ->
    -- Again, we look to beta reduce, or add a projection to a neutral
    case undeferred $ evaling term ctx of
      EPair _ _ _ right -> right
      ENeut (Neutral focus prjs) ->
        checkGlobal ctx $ ENeut (Neutral focus (prjs :> NSnd meta))
      _ -> error "Type error: cannot project from non-sigma"
  TUniv meta univ -> pure $ EUniv meta univ
  -- A hole is a neutral: we do not know its value yet. Thus we have to block
  -- on it and record its arguments or projections. This is contrary to the
  -- neutrals for abstract variables, which are introduced *outside* of eval.
  THole meta hole -> pure $ ENeut (Neutral (NHole meta hole) Nil)
  TTyCtor meta name params indices -> ETyCtor meta name <$> traverse evaling params <*> traverse evaling indices
  TConstr meta name params args -> EConstr meta name <$> traverse evaling params <*> traverse evaling args
  TCase meta motive cases inspect -> \ctx ->
    case undeferred $ evaling inspect ctx of
      EConstr _meta (_tyName, conName) _params args ->
        checkGlobal ctx $ doApps (doField (evaling cases ctx) conName) (Stack.fromFoldable args)
      ENeut (Neutral focus prjs) ->
        checkGlobal ctx $ ENeut (Neutral focus (prjs :> NCase meta (evaling motive ctx) (evaling cases ctx)))
      _ -> error "Type error: cannot case on non-inductive"
  TRecordTy meta fields -> ERecordTy meta <$> traverse evaling fields
  TRecordTm meta fields -> ERecordTm meta <$> traverse evaling fields
  TField meta focus field -> doPrj <$> evaling focus <*> pure (NField meta field)
  TLift meta ty -> ELift meta <$> evaling ty
  TQuote meta tm -> doQuote meta <$> evaling tm
  TSplice meta tm -> doSplice meta <$> evaling tm

undeferred :: ("deferred term" @:: Eval) -> Eval
undeferred (EDeferred _ _ _ _ tm) = undeferred tm
undeferred tm = tm

doQuote :: Metadata -> Eval -> Eval
doQuote _ (ENeut (Neutral blocking (rest :> NSplice _))) = ENeut (Neutral blocking rest)
doQuote meta tm = EQuote meta tm

doSplice :: Metadata -> Eval -> Eval
doSplice _ (EQuote _ tm) = tm
doSplice meta (ENeut (Neutral blocking rest)) = ENeut (Neutral blocking (rest :> NSplice meta))
doSplice _ _ = error "Type error: cannot splice a non-quote"

-- Quoting takes a term that was evaluated to depth 1 (`Eval`) and turns it back
-- into a `Term`, calling `eval` on all closures to evaluate it fully.
quoting :: Eval -> QuoteCtx -> Term
quoting = eval2termWith False quotingClosure

-- We implement it via a generic function, to avoid duplication. (Duplication
-- itself is not too painful, but having to add 500 new cases every time you
-- add an AST node is painful.)
eval2termWith ::
  "force globals" @:: Bool ->
  (Closure -> "type" @:: Eval -> QuoteCtx -> ScopedTerm) ->
  Eval -> QuoteCtx -> Term
eval2termWith forceGlobals handleClosure = \case
  ENeut (Neutral focus prjs) -> \ctx ->
    let
      base = case focus of
        NVar meta lvl -> TVar meta (index ctx lvl)
        NHole meta hole -> THole meta hole
        NGlobal _ _ name
          | forceGlobals
          , Just (GlobalDefn _ _ (GlobalTerm term _)) <-
              Map.lookup name (globalDefns $ ctxGlobals ctx) -> term
        NGlobal _arity meta name -> TGlobal meta name
      go (more :> prj) soFar = go more case prj of
        NApp meta arg -> TApp meta soFar (e2t arg ctx)
        NFst meta -> TFst meta soFar
        NSnd meta -> TSnd meta soFar
        NSplice meta -> TSplice meta soFar
        NCase meta motive cases -> TCase meta (e2t motive ctx) (e2t cases ctx) soFar
        NField meta field -> TField meta soFar field
      go Nil result = result
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
  ETyCtor meta name params indices ->
    TTyCtor meta name <$> traverse e2t params <*> traverse e2t indices
  EConstr meta name params args ->
    TConstr meta name <$> traverse e2t params <*> traverse e2t args
  ERecordTy meta fields -> TRecordTy meta <$> traverse e2t fields
  ERecordTm meta fields -> TRecordTm meta <$> traverse e2t fields
  EDeferred _ _ _ _ tm -> e2t tm
  ELift meta ty -> TLift meta <$> e2t ty
  EQuote meta tm -> TQuote meta <$> e2t tm
  where
  e2t = eval2termWith forceGlobals handleClosure

-- Quote a closure back into a syntactic term: this generates a neutral to be
-- a placeholder for the bound variable during evaluation, and then it restarts
-- evaluation on the frozen `Term` inside the `Closure`. This finishes
-- normalizing it.
--
-- Note: this calls directly into `quoting`.
quotingClosure :: Closure -> Eval -> QuoteCtx -> ScopedTerm
quotingClosure (Closure bdr savedCtx (Scoped savedBody)) _argTy ctx =
  let
    (lvl, ctx') = push (bdr, ()) ctx
    -- This is the (only-ish) place that we create neutrals: when quoting.
    evalingArg = ENeut (Neutral (NVar mempty lvl) Nil)
  in Scoped $ quoting ((evaling savedBody $ savedCtx :> (bdr, evalingArg)) :: Eval) ctx'

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
type EvalTypeCtx = Ctx ("type" @:: Eval, "value" @:: Eval)

umax :: ULevel -> ULevel -> ULevel
umax (UBase l1) (UBase l2) = UBase (max l1 l2)
umax (UMeta l1) (UMeta l2) = UMeta (max l1 l2)
umax _ _ = error "Bad umax / unimplemented"


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
  TTyCtor meta name params indices -> TTyCtor meta name (go <$> params) (go <$> indices)
  TConstr meta name params args -> TConstr meta name (go <$> params) (go <$> args)
  TCase meta motive cases inspect -> TCase meta (go motive) (go cases) (go inspect)
  TRecordTy meta fields -> TRecordTy meta (go <$> fields)
  TRecordTm meta fields -> TRecordTm meta (go <$> fields)
  TField meta focus field -> TField meta (go focus) field
  TLift meta ty -> TLift meta $ go ty
  TQuote meta tm -> TQuote meta $ go tm
  TSplice meta tm -> TSplice meta $ go tm
  where
  go = shiftFrom base delta
  into = shiftFrom (base+1) delta
