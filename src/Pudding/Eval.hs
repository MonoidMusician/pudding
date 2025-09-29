module Pudding.Eval where

import Pudding.Types

captureClosure :: Term -> EvalCtx -> Closure
captureClosure = flip Closure

cons :: Eval -> EvalCtx -> EvalCtx
cons value (EvalCtx sz stack) = EvalCtx (sz+1) (value:stack)

-- Normalization by Evaluation
evaling :: Term -> EvalCtx -> Eval
evaling = \case
  -- If we have a variable
  TVar moreMeta (Index idx) -> \ctx ->
    -- Look it up by index: it must be in the context.
    -- Note that we do not generate neutrals here: they are put in the context
    -- only during *quoting* and *conversion checking*, where we must handle
    -- open terms (digging down below binders (λ, Π, Σ)) by seeding neutrals
    case evalValues ctx !! idx of
      -- If it is a neutral, we should add metadata...
      ENeut (Neutral (NVar metaNeut ty lvl) []) ->
        ENeut (Neutral (NVar (metaNeut <> moreMeta) ty lvl) [])
      -- Otherwise we just pass the value from context along:
      -- the variable has done its job
      e -> e
  -- If we are looking at evaluating a global
  TGlobal _ _ (Meta (Exact global)) ->
    -- The global info is already looked up
    case global of
      -- We already have a lazy evaluation for a global definition
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
  -- Application is interesting
  TApp metaApp fun arg -> \ctx ->
    case (evaling fun ctx, evaling arg ctx) of
      -- Beta redex: we can resume the body closure now that we know the value
      -- it was waiting for: `evalingArg`
      (ELambda _ _ _ _ (Closure savedCtx savedBody), evalingArg) ->
        evaling savedBody $ cons evalingArg savedCtx
      -- If it was stuck as a neutral, we need to preserve the argument on the
      -- stack of projections to apply to the neutral variable
      (ENeut (Neutral focus prjs), evalingArg) ->
        ENeut (Neutral focus (NApp metaApp evalingArg : prjs))
      _ -> error "Type error: cannot apply to non-function"
