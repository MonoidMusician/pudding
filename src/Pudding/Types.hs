module Pudding.Types
  ( module Pudding.Types -- Export the default exports of this module
  , module Pudding.Types.Base
  , module Pudding.Types.Metadata
  , module Pudding.Types.Stack
  , module Pudding.Name -- Export more
  ) where

import Control.DeepSeq (NFData)
import Control.Lens (from, view)
import Data.Functor.Apply ((<.>), (<.*>))
import Data.Map (Map)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)
import GHC.StableName (StableName)
import Prettyprinter (Pretty)
import Pudding.Name (CanonicalName(..), Name(..), newTable, initTable, internalize)
import Pudding.Types.Base
import Pudding.Types.Metadata
import Pudding.Types.Stack

--------------------------------------------------------------------------------
-- Main semantic types!                                                       --
--------------------------------------------------------------------------------

data Binder
  = BVar !(Meta CanonicalName)
  | BMulti !Binder !Binder -- Bind two to the same value
  | BPair !Binder !Binder -- Bind to fst and snd projections
  | BFresh -- Assign a name to it during pretty printing
  | BUnused
  deriving (Generic, NFData)

data GlobalTerm = GlobalTerm !Term Eval
  deriving (Generic, NFData)

data GlobalInfo
  -- A function or global constant or whatever.
  -- These also get generated for the names introduced by inductive types:
  -- the type name becomes a definition and so does each constructor.
  = GlobalDefn !("arity" @:: Int) ("type" @:: GlobalTerm) ("term" @:: GlobalTerm)
  -- An inductive type declaration.
  | GlobalType GlobalTypeInfo
  deriving (Generic, NFData)

type Globals = Map Name GlobalInfo

data GlobalTypeInfo = GlobalTypeInfo
  { typeParams :: !(Vector (Plicit, Binder, Term))
  , typeIndices :: !(Vector (Plicit, Binder, Term))
  , typeConstrs :: !(Map Name ConstructorInfo)
  }
  deriving (Generic, NFData)

data ConstructorInfo = ConstructorInfo
  { ctorArguments :: !(Vector (Plicit, Binder, Term))
  , ctorIndices :: !(Vector Term)
  }
  deriving (Generic, NFData)

----------------------------------------
-- An overview of important functions --
----------------------------------------

-- Surface syntax
-- print, parse :: Surface <-> Text
-- elaborate :: Surface -> Elab (Term, Term)

-- Core syntax
-- printCore, parseCore :: Term <-> Text
-- typeof :: Term -> Term   -- Core syntax is intrinsically typed

-- Normalization by Evaluation
-- eval :: EvalCtx -> Term -> Eval
-- printEval :: Eval -> Text
-- conversionCheck / unification :: EvalCtx -> Eval -> Eval -> Maybe Eval
-- quote :: QuoteCtx -> Eval -> Term
-- normalize = quote . eval :: Term -> Term

-------------------------------
-- The core types themselves --
-------------------------------

-- (It usually ends up being convenient in Haskell to reduce type variables
-- and not shove metadata into a separate structure, unfortunately)

-- A dependently typed term in the *core* calculus (not meant to be pleasant to write).
-- It is intrinsically typed in the sense that it supports `typeof :: Term -> Term`
-- (where `typeof . typeof` resolves to some `TUniv`)
data Term
  -- (Local) variables
  = TVar Metadata !Index
  -- Typed holes
  | THole Metadata !Fresh
  -- Type universes
  | TUniv Metadata ULevel
  -- Global variables
  | TGlobal Metadata !Name
  -- | TLet Metadata Binder ("value" @:: Term) ("body" @:: Term)
  | TLambda
      -- Metadata: not relevant to equality/unification
      -- Every argument is explicit in the core and every core binder only binds
      -- one variable, but we keep this information around for pretty printing
      Metadata !Plicit Binder
      -- Actual core data (influences equality, etc.)
      ("domain type" @:: Term) ("body" @:: ScopedTerm)
  | TPi
      Metadata !Plicit Binder
      ("domain type" @:: Term) ("codomain" @:: ScopedTerm)
  | TApp Metadata
      ("function" @:: Term) ("argument" @:: Term)
  | TSigma
      Metadata !Plicit Binder
      ("fst type" @:: Term) ("snd type under fst type" @:: ScopedTerm)
  -- A pair of a sigma type
  | TPair Metadata
      ("sigma type" @:: Term)
      ("fst value" @:: Term)
      ("snd value" @:: Term)
  | TFst Metadata Term
  | TSnd Metadata Term
  -- A type constructor: the name of an inductive type applied to parameters
  -- and indices
  | TTyCtor Metadata !("type name" @:: Name)
      ("params" @:: Vector Term)
      ("indices" @:: Vector Term)
  -- A term constructor: the actual constructor of the inductive type applied
  -- to its arguments (from which the indices are also derived)
  | TConstr Metadata !("type name" @:: Name, "constr name" @:: Name)
      ("params" @:: Vector Term)
      -- args are the actual data stored in the constructor, from which the
      -- indices are inferred based on the constructor declaration
      ("args" @:: Vector Term)
  deriving (Generic, NFData)
newtype ScopedTerm = Scoped Term
  deriving newtype (NFData)

spine :: Term -> (Term, [Term])
spine = go []
  where
  go acc (TApp _ fun arg) = go (arg : acc) fun
  go acc fun = (fun, acc)

-- Result of the `eval` half of Normalization by Evaluation (NbE), called
-- "the semantic domain".
--
-- Concretely, it is `Term` evaluated to a depth of 1, not recursing under any
-- binders. Thus it sits between Weak-Head Normal Form (WHNF) and fully
-- normalized.
--
-- If `ENeut` is ommitted, this would be no longer be suitable for partial
-- evaluation: it could only evaluate top-level terms. That is suitable for many
-- programming languages, but insufficient for a dependent type checker.
-- Dependent types necessitate normalizing terms in arbitrary contexts (“open”
-- terms).
data Eval
  = ENeut Neutral -- do we want it tagged with its ultimate type?
  | EUniv Metadata ULevel
  | ELambda
      Metadata !Plicit Binder
      ("domain type" @:: Eval) ("body" @:: Closure)
  | EPi
      Metadata !Plicit Binder
      ("domain type" @:: Eval) ("codomain" @:: Closure)
  | ESigma
      Metadata !Plicit Binder
      ("fst type" @:: Eval) ("snd type under fst type" @:: Closure)
  | EPair Metadata ("sigma type" @:: Eval) ("fst value" @:: Eval) ("snd value" @:: Eval)
  | ETyCtor Metadata !("type name" @:: Name)
      ("params" @:: Vector Eval)
      ("indices" @:: Vector Eval)
  | EConstr Metadata !("type name" @:: Name, "constr name" @:: Name)
      ("params" @:: Vector Eval)
      ("args" @:: Vector Eval)
  | EDeferred ("reason" @:: Meta Text) ("type" @:: Eval) !("sharing" @:: Maybe (StableName Eval)) Metadata ("deferred term" @:: Eval)
  deriving (Generic, NFData)

-- A Neutral is stuck on a variable (or hole), with some projections and eliminators applied to it.
-- (This is the Normalization part of NbE: inserting variables to evaluate open terms.)
data Neutral = Neutral
  { neutralBlocking :: NeutFocus
  , neutralSpine :: [NeutPrj]
    -- ^ Spine of projections/function applications/eliminators to apply,
    -- either to reconstruct the syntax around the variable, or to finish
    -- evaluating it once it is known.
    --
    -- This should **really** be a Snoc list (in terms of order of
    -- evaluation), but I've been lazy thus far.
  }
  deriving (Generic, NFData)
data NeutFocus
  = NVar Metadata !Level
  | NHole Metadata !Fresh -- needs some scoping information(?)
  -- this is a kind of weak neutral: it will be evaluated when it reaches the
  -- arity of function arguments and they are not all neutrals, and it can
  -- also be evaluated during conversion checking
  | NGlobal !("arity" @:: Int) Metadata Name
  deriving (Generic, NFData)
data NeutPrj
  = NApp Metadata ("arg" @:: Eval)
  | NFst Metadata
  | NSnd Metadata
  deriving (Generic, NFData)
-- Alternatively: we could just implement it as a recursive type
-- Neutral = NVar Level | NFst Neutral | NApp ("fun" @:: Neutral) ("arg" @:: Eval)


-- Closure: an unevaluated term frozen in an environment of evaluated (or neutral)
-- variable values.
--
-- A closure is created during evaluation from a binder (like lambda/Pi/Sigma),
-- where `EvalCtx` is the external context *not* including what was just bound
-- (whatever the context happened to be when we ran into the lambda), and `Term`
-- is literally just the body of the lambda, waiting for the bound variable to
-- have some `Eval` to instantiate it (during evaluation: with a value, or during
-- quoting: with a neutral term, to capture the dependence of the body on
-- the argument it is expecting).
--
-- `(\x -> x + 1) 2` will evaluate the `Closure` immediately, but
-- `(\x -> x) (\y -> y)` leaves `(\y -> y)` for quoting
data Closure = Closure
  Binder
  ("saved external context" @:: EvalCtx)
  ("body" @:: ScopedTerm)
  deriving (Generic, NFData)

data Telescope = Telescope Eval Closure

----------------------------------
-- Functions for the core types --
----------------------------------

neutralVar :: Level -> Eval
neutralVar lvl = ENeut (Neutral (NVar mempty lvl) [])

arityOfTerm :: Term -> Int
arityOfTerm = go 0
  where
  go !acc (TLambda _ _ _ _ (Scoped body)) = go (1 + acc) body
  go !acc _ = acc

--------------------------
-- The type of contexts --
--------------------------

data Ctx t = Ctx
  { ctxGlobals :: Globals
  , ctxStack :: !(Stack (Binder, t))
  }
  deriving (Functor, Generic, NFData)

instance StackLike (Ctx t) where
  type Elem (Ctx t) = (Binder, t)

  Ctx _ s @@ i = s @@ i

  size (Ctx _ s) = size s

  Ctx globals s >: b = Ctx globals (s >: b)

  pop :: Ctx t -> Maybe (Ctx t, (Binder, t))
  pop (Ctx g s) = do
    (s', b) <- pop s
    return (Ctx g s', b)

infixr 8 @@:
(@@:) :: ToIndex i => Ctx t -> i -> t
c @@: i = snd (c @@ i)

-- Context used for `eval`
type EvalCtx = Ctx Eval

-- Context used for `quote`: `ctxSize` is just used to convert `Level` back to `Index`
type QuoteCtx = Ctx ()

ctxOfStack :: forall t. Globals -> "inner bindings first" @:: [(Binder, t)] -> Ctx t
ctxOfStack globals s = Ctx globals (view rstack s)

ctxOfList :: forall t. Globals -> "inner bindings last" @:: [(Binder, t)] -> Ctx t
ctxOfList globals s = Ctx globals (view stack s)

ctxToList :: forall t. Ctx t -> "inner bindings last" @:: [(Binder, t)]
ctxToList (Ctx _ s) = view (from stack) s

ctxOfGlobals :: forall t. Globals -> Ctx t
ctxOfGlobals globals = Ctx globals (view stack [])

ctxOfSize :: Globals -> "size" @:: Int -> Ctx ()
ctxOfSize globals sz = Ctx globals (view stack (replicate sz (BFresh, ())))

foldCtx :: (Globals -> a) -> (Ctx t -> (Binder, t) -> a -> a) -> Ctx t -> a
foldCtx z s ctx@(Ctx g _) = case pop ctx of
  Nothing -> z g
  Just (ctx', b) -> s ctx' b (foldCtx z s ctx')

mapCtx :: (Ctx t -> t -> a) -> Ctx t -> Ctx a
mapCtx f = foldCtx ctxOfGlobals \ctx (b, t) acc ->
  acc >: (b, f ctx t)

--------------------------------------------------------------------------------
-- Helper types!                                                              --
--------------------------------------------------------------------------------

-- decl: Π(T : Type), T -> T
-- surface syntax usage: f Nat 42
-- decl: Π{T : Type}, T -> T
-- surface syntax usage: f 42
data Plicit = Explicit | Implicit
  deriving (Eq, Ord, Generic, NFData)

-- E.g. for numbering typed holes
newtype Fresh = Fresh Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData)

data ULevel
  = UBase !Int
  | UMeta !Int
  | UVar !Fresh !Int -- unsolved level, plus offset
    -- sigh, scoping...
  deriving (Eq, Ord, Generic, Show, NFData)

--------------------------------------------------------------------------------
-- Metadata types                                                             --
--------------------------------------------------------------------------------

-- `Exact` values only unify with themself: otherwise it throws an error.
newtype Exact t = Exact t
  deriving newtype (Eq, Ord, NFData)

instance Eq t => Semigroup (Exact t) where
  Exact l <> Exact r =
    if l == r then Exact l else error "Inexact"

--------------------
-- Metadata class --
--------------------

instance HasMetadata Term where
  traverseMetadata1 f = \case
    TVar old idx -> (\new -> TVar new idx) <$> f old
    THole old hole -> (\new -> THole new hole) <$> f old
    TUniv old univ -> (\new -> TUniv new univ) <$> f old
    TGlobal old name -> (\new -> TGlobal new name) <$> f old
    TLambda old p b ty body -> (\new -> TLambda new p b)
      <$> f old
      <.> traverseMetadata1 f ty
      <.> traverseMetadata1 f body
    TPi old p b ty body -> (\new -> TPi new p b)
      <$> f old
      <.> traverseMetadata1 f ty
      <.> traverseMetadata1 f body
    TApp old fun arg -> TApp
      <$> f old
      <.> traverseMetadata1 f fun
      <.> traverseMetadata1 f arg
    TSigma old p b ty body -> (\new -> TSigma new p b)
      <$> f old
      <.> traverseMetadata1 f ty
      <.> traverseMetadata1 f body
    TPair old t l r -> TPair
      <$> f old
      <.> traverseMetadata1 f t
      <.> traverseMetadata1 f l
      <.> traverseMetadata1 f r
    TFst old t -> TFst <$> f old <.> traverseMetadata1 f t
    TSnd old t -> TSnd <$> f old <.> traverseMetadata1 f t
    TTyCtor old name params indices -> (\new -> TTyCtor new name)
      <$> f old
      <.*> traverse (traverseMetadata1 (apply f)) params
      <.*> traverse (traverseMetadata1 (apply f)) indices
    TConstr old name params args -> (\new -> TConstr new name)
      <$> f old
      <.*> traverse (traverseMetadata1 (apply f)) params
      <.*> traverse (traverseMetadata1 (apply f)) args

instance HasMetadata ScopedTerm where
  traverseMetadata1 f (Scoped term) = Scoped <$> traverseMetadata1 f term

instance HasMetadata Eval where
  traverseMetadata1 f = \case
    ENeut neutral -> ENeut <$> traverseMetadata1 f neutral
    EUniv old univ -> (\new -> EUniv new univ) <$> f old
    ELambda old p b ty body -> (\new -> ELambda new p b)
      <$> f old
      <.> traverseMetadata1 f ty
      <.> traverseMetadata1 f body
    EPi old p b ty body -> (\new -> EPi new p b)
      <$> f old
      <.> traverseMetadata1 f ty
      <.> traverseMetadata1 f body
    ESigma old p b ty body -> (\new -> ESigma new p b)
      <$> f old
      <.> traverseMetadata1 f ty
      <.> traverseMetadata1 f body
    EPair old t l r -> EPair
      <$> f old
      <.> traverseMetadata1 f t
      <.> traverseMetadata1 f l
      <.> traverseMetadata1 f r
    ETyCtor old name params indices -> (\new -> ETyCtor new name)
      <$> f old
      <.*> traverse (traverseMetadata1 (apply f)) params
      <.*> traverse (traverseMetadata1 (apply f)) indices
    EConstr old name params args -> (\new -> EConstr new name)
      <$> f old
      <.*> traverse (traverseMetadata1 (apply f)) params
      <.*> traverse (traverseMetadata1 (apply f)) args
    EDeferred reason ty ref _ term ->
      (\term' ty' -> EDeferred reason ty' ref (getMetadata term') term')
      <$> traverseMetadata1 f term
      <.> traverseMetadata1 f ty

instance HasMetadata Neutral where
  traverseMetadata1 f (Neutral focus prjs) =
    Neutral
      <$> traverseMetadata1 f focus
      <.*> traverse (traverseMetadata1 (apply f)) (reverse prjs)

instance HasMetadata NeutFocus where
  traverseMetadata1 f (NVar old lvl) = (\new -> NVar new lvl) <$> f old
  traverseMetadata1 f (NHole old hole) = (\new -> NHole new hole) <$> f old
  traverseMetadata1 f (NGlobal arity old name) = (\new -> NGlobal arity new name) <$> f old

instance HasMetadata NeutPrj where
  traverseMetadata1 f = \case
    NApp old arg -> NApp
      <$> f old
      <.> traverseMetadata1 f arg
    NFst old -> NFst <$> f old
    NSnd old -> NSnd <$> f old

instance HasMetadata Closure where
  traverseMetadata1 f (Closure bdr ctx term) = Closure bdr ctx
    <$> traverseMetadata1 f term
