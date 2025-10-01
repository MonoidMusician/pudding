{-# LANGUAGE DataKinds #-}
module Pudding.Eval where

import Pudding.Types

captureClosure :: Term -> EvalCtx -> Closure
captureClosure = flip Closure

cons :: Eval -> EvalCtx -> EvalCtx
cons value (EvalCtx sz stack) = EvalCtx (sz+1) (value:stack)

evalIndex :: Index -> EvalCtx -> Eval
evalIndex (Index idx) ctx = evalValues ctx !! idx

evalLevel :: Level -> EvalCtx -> Eval
evalLevel lvl ctx = evalIndex (lvl2idx (evalSize ctx) lvl) ctx

eval :: EvalCtx -> Term -> Eval
eval = flip evaling
quote :: QuoteCtx -> Eval -> Term
quote = flip quoting

-- If you want to fully partially evaluate (ahem, normalize) a top-level `Term`.
normalize :: Term -> Term
normalize original =
  let
    evaluated = eval (EvalCtx 0 []) original
    -- Now we are left with something that is evaluated to depth 1
    -- (so it might have applied some functions and ended up with a `EPair` or
    -- something), but now we need to recursively normalize under binders:
    -- which is what `quote` does.
    quoted = quote (QuoteCtx { quoteSize = 0 }) evaluated
    -- And now it is a `Term` again: core syntax that we can manipulate as a
    -- self-contained thing. (Whereas the `Closure`s in `Eval` contain
    -- frozen contexts that we can't deal with in any sensible way.)
    --
    -- `quoteSize` is just used to convert `Level` back to `Index`
  in quoted

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
    case evalIndex idx ctx of
      -- If it is a neutral, we should add metadata...
      ENeut (Neutral (NVar metaNeut lvl) []) ->
        ENeut (Neutral (NVar (metaNeut <> moreMeta) lvl) [])
      -- Otherwise we just pass the value from context along:
      -- the variable has done its job
      e -> e
  -- If we are looking at evaluating a global
  TGlobal _ _ (Meta (Exact global)) ->
    -- The global info is already looked up
    case global of
      -- We already have a shared lazy evaluation for a global definition
      GlobalDefn _ (GlobalTerm _ eval) -> pure eval
      -- Constructors are a bit tricky
      _ -> error "Not implemented yet"
  -- For a lambda
  TLambda meta plicit binder ty body ->
    -- We eval the type, but capture the body as a closure in *this* environment
    -- to restart evaluation later, when the argument's value is known (or neutral)
    ELambda meta plicit binder <$> evaling ty <*> captureClosure body
  -- Similar story
  TPi meta plicit binder ty body ->
    EPi meta plicit binder <$> evaling ty <*> captureClosure body
  -- Similar story
  TSigma meta plicit binder ty body ->
    ESigma meta plicit binder <$> evaling ty <*> captureClosure body
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
      (ELambda _ _ _ _ (Closure savedCtx savedBody), evalingArg) ->
        evaling savedBody $ cons evalingArg savedCtx
      -- If it was stuck as a neutral, we need to preserve the argument on the
      -- stack of projections to apply to the neutral variable
      (ENeut (Neutral focus prjs), evalingArg) ->
        ENeut (Neutral focus (NApp metaApp evalingArg : prjs))
      _ -> error "Type error: cannot apply to non-function"
  TPair meta plicit left ltr right ->
    EPair meta plicit <$> evaling left <*> evaling ltr <*> evaling right
  TFst meta term -> \ctx ->
    -- Again, we look to beta reduce, or add a projection to a neutral
    case evaling term ctx of
      -- If it reduces to a literal, it must be a pair by type correctness
      EPair _ _ left _ _ -> left
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
      EPair _ _ _ _ right -> right
      ENeut (Neutral focus prjs) ->
        ENeut (Neutral focus (NSnd meta : prjs))
      _ -> error "Type error: cannot apply to non-function"
  TUniv meta univ -> pure $ EUniv meta univ
  THole meta hole -> pure $ ENeut (Neutral (NHole meta hole) [])

quoting :: Eval -> QuoteCtx -> Term
quoting = \case
  ENeut (Neutral focus prjs) -> \ctx ->
    let
      base = case focus of
        NVar meta lvl -> TVar meta (lvl2idx (quoteSize ctx) lvl)
        NHole meta hole -> THole meta hole
      go (prj : more) soFar = go more case prj of
        NApp meta arg -> TApp meta soFar (quoting arg ctx)
        NFst meta -> TFst meta soFar
        NSnd meta -> TSnd meta soFar
      go [] result = result
    in go prjs base
  EUniv meta univ -> pure $ TUniv meta univ
  ELambda meta plicit binder ty body ->
    TLambda meta plicit binder <$> quoting ty <*> quotingClosure body ty
  EPi meta plicit binder ty body ->
    TPi meta plicit binder <$> quoting ty <*> quotingClosure body ty
  ESigma meta plicit binder ty body ->
    TSigma meta plicit binder <$> quoting ty <*> quotingClosure body ty
  EPair meta plicit left ltr right ->
    TPair meta plicit <$> quoting left <*> quoting ltr <*> quoting right

-- Quote a closure back into a syntactic term: this generates a neutral to be
-- a placeholder for the bound variable during evaluation, and then it restarts
-- evaluation on the frozen `Term` inside the `Closure`.
quotingClosure :: Closure -> Eval -> QuoteCtx -> Term
quotingClosure (Closure savedCtx savedBody) argTy ctx =
  let
    -- This is the (only-ish) place that we create neutrals: when quoting.
    evalingArg = ENeut (Neutral (NVar mempty (Level (quoteSize ctx))) [])
  in quoting (evaling savedBody $ cons evalingArg savedCtx) ctx
