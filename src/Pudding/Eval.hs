{-# LANGUAGE DataKinds #-}
module Pudding.Eval where

import Pudding.Types
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Functor ((<&>))

captureClosure :: Term -> EvalCtx -> Closure
captureClosure = flip Closure

cons :: Eval -> EvalCtx -> EvalCtx
cons value ctx@(EvalCtx { evalSize = sz, evalValues = stack }) =
  ctx { evalSize = sz+1, evalValues = value:stack }

evalIndex :: Index -> EvalCtx -> Eval
evalIndex (Index idx) ctx = evalValues ctx !! idx

evalLevel :: Level -> EvalCtx -> Eval
evalLevel lvl ctx = evalIndex (lvl2idx (evalSize ctx) lvl) ctx

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
  globalTerm (GlobalTerm tm _) = GlobalTerm tm (evalGlobal tm)
  evalGlobal = eval (EvalCtx 0 [] globals)
  typeofGlobal :: GlobalTerm -> GlobalTerm
  typeofGlobal (GlobalTerm tm _) =
    let ty = typeof (simpleCtx globals []) tm
    in GlobalTerm ty (evalGlobal ty)

-- If you want to fully partially evaluate (ahem, normalize) a top-level `Term`.
normalize :: Map Name GlobalInfo -> Term -> Term
normalize globals original =
  let
    evaluated = eval (EvalCtx 0 [] globals) original
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
  TGlobal _ name -> \ctx ->
    -- The global info is already looked up
    case Map.lookup name (evalGlobals ctx) of
      -- We already have a shared lazy evaluation for a global definition
      Just (GlobalDefn _ (GlobalTerm _ evaled)) -> evaled
      -- Constructors are a bit tricky
      Just _ -> error "Not implemented yet"
      Nothing -> error $ "Could not find global " <> show name
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
      (ELambda _ _ _ _ (Closure _ty savedCtx savedBody), evalingArg) ->
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
  EDeferred _ _ _ _ tm -> quoting tm

-- Quote a closure back into a syntactic term: this generates a neutral to be
-- a placeholder for the bound variable during evaluation, and then it restarts
-- evaluation on the frozen `Term` inside the `Closure`.
quotingClosure :: Closure -> Eval -> QuoteCtx -> Term
quotingClosure (Closure _ty savedCtx savedBody) argTy ctx =
  let
    -- This is the (only-ish) place that we create neutrals: when quoting.
    evalingArg = ENeut (Neutral (NVar mempty (Level (quoteSize ctx))) [])
  in quoting (evaling savedBody $ cons evalingArg savedCtx) ctx



data SimpleCtx item = SimpleCtx
  { scSize :: !Int
  , scStack :: [item]
  , scGlobals :: Map Name GlobalInfo
  }
type TypeCtx = SimpleCtx Term
type EvalTypeCtx = SimpleCtx Eval

simpleCtx :: forall item. Map Name GlobalInfo -> [item] -> SimpleCtx item
simpleCtx globals stack = SimpleCtx (length stack) stack globals

snocSimple :: forall item. SimpleCtx item -> item -> SimpleCtx item
snocSimple ctx item = ctx
  { scSize = scSize ctx + 1, scStack = item : scStack ctx }

umax :: ULevel -> ULevel -> ULevel
umax = undefined

typeof :: TypeCtx -> Term -> Term
typeof ctx = \case
  TVar _ (Index idx) -> scStack ctx !! idx
  TGlobal _ name -> case Map.lookup name (scGlobals ctx) of
    Nothing -> error $ "Undefined global " <> show name
    Just (GlobalDefn (GlobalTerm ty _) _) -> ty
    Just _ -> error "Not implemented"
  THole _ fresh -> error "typeof hole not implemented"
  TUniv meta univ -> TUniv meta case univ of
    UBase lvl -> UBase (lvl + 1)
    UMeta lvl -> UMeta (lvl + 1)
    -- This is why `UVar` has an `Int`: increment to get the typeof
    UVar fresh incr -> UVar fresh (incr + 1)
  TLambda meta p b ty body ->
    TPi meta p b ty (typeof (into ty) body)
  TPi _ _ _ ty body ->
    -- Π(x : ty : U), (body : U)
    case (typeof ctx ty, typeof (into ty) body) of
      (TUniv m1 u1, TUniv m2 u2) -> TUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad pi type"
  TSigma _ _ _ ty body ->
    case (typeof ctx ty, typeof (into ty) body) of
      (TUniv m1 u1, TUniv m2 u2) -> TUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad sigma type"
  TPair meta p left dep _right ->
    -- A bit tricky: `dep` is the dependency of the type of `right` on `left`:
    -- because we can infer `left` (and we could infer `right`), but we can't
    -- infer their exact dependency as `left` varies: so `dep` itself should have
    -- type `(typeof left) -> Type`
    --
    -- so we make it back into syntax by applying the variable we just bound
    -- (... potentially not great because it is unevaluated, but yeah)
    case dep of
      -- Shortcut: if it is a lambda, then we can transmogrify it into a TSigma
      TLambda _ _ b ty body ->
        TSigma
          -- take metadata and plicity from the pair/sigma
          meta p
          -- take the binder from the lambda, trust the type, and insert the body
          b ty body
      -- Otherwise we just use `TApp` to apply the variable we just bound
      _ ->
        TSigma meta p (BVar noName) (typeof ctx left) (TApp mempty dep (TVar mempty (Index 0)))
  TFst _ tm -> case typeof ctx tm of
    TSigma _ _ _ ty _body -> ty
    _ -> error "Bad fst"
  TSnd _ tm -> case typeof ctx tm of
    -- snd (tm : Σ(x : ty), body) = body@[x := fst tm]
    TSigma _ _ binder ty body ->
      TApp mempty (TLambda mempty Explicit binder ty body) (TFst mempty tm)
    _ -> error "Bad snd"
  TApp _ fun arg -> case typeof ctx fun of
    TPi meta p b ty body -> TApp mempty (TLambda meta p b ty body) arg
    _ -> error "Bad app"
  where
  into :: Term -> TypeCtx
  into ty = ctx { scStack = ty : scStack ctx }

  noName :: Meta CanonicalName
  noName = Meta $ CanonicalName { chosenName = undefined, allNames = mempty }

typeofEval :: EvalTypeCtx -> Eval -> Eval
typeofEval ctx = \case
  EUniv meta univ -> EUniv meta case univ of
    UBase lvl -> UBase (lvl + 1)
    UMeta lvl -> UMeta (lvl + 1)
    -- This is why `UVar` has an `Int`: increment to get the typeof
    UVar fresh incr -> UVar fresh (incr + 1)
  ELambda meta p b ty body ->
    EPi meta p b ty (typeofClosure ty body)
  EPi _ _ _ ty body ->
    -- Π(x : ty : U), (body : U)
    case (typeofEval ctx ty, typeofClosure ty body) of
      (EUniv m1 u1, EUniv m2 u2) -> EUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad pi type"
  ESigma _ _ _ ty body ->
    case (typeofEval ctx ty, typeofClosure ty body) of
      (EUniv m1 u1, EUniv m2 u2) -> EUniv (m1 <> m2) (umax u1 u2)
      _ -> error "Bad sigma type"
  EPair meta p left dep _right ->
    case dep of
      ELambda _ _ b ty body ->
        ESigma
          -- take metadata and plicity from the pair/sigma
          meta p
          -- take the binder from the lambda, trust the type, and insert the body
          b ty body
      -- Otherwise we just use `TApp` to apply the variable we just bound
      _ ->
        ESigma meta p (BVar noName) (typeofEval ctx left) (ENeut (Neutral (NVar mempty ()) (NApp mempty dep)))
  ENeut (Neutral focus prjs) -> typeofPrjs (typeofFocus focus) prjs
  EDeferred _ ty _ _ _ -> ty
  where
  into :: Eval -> EvalTypeCtx
  into ty = ctx { scStack = ty : scStack ctx }

  noName :: Meta CanonicalName
  noName = Meta $ CanonicalName { chosenName = undefined, allNames = mempty }

  typeofFocus = \case
    NVar _ (Level idx) -> scStack ctx !! idx
    NHole _ fresh -> error "typeof hole not implemented"
  typeofPrjs ty [] = ty
  typeofPrjs ty (prj : prjs) = typeofPrjs (typeofPrj ty prj) prjs
  typeofPrj ty = \case
    NFst _ -> case ty of
      TSigma _ _ _ ty _body -> ty
      _ -> error "Bad fst"
    NSnd _ -> case ty of
      -- snd (tm : Σ(x : ty), body) = body@[x := fst tm]
      ESigma _ _ binder ty body ->
        TApp mempty (ELambda mempty Explicit binder ty body) (EFst mempty tm)
      _ -> error "Bad snd"
    NApp _ arg -> case ty of
      EPi meta p b ty body -> EApp mempty (ELambda meta p b ty body) arg
      _ -> error "Bad app"
