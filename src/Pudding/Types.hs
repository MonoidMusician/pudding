module Pudding.Types
  ( module Pudding.Types -- Export the default exports of this module
  , module Pudding.Types.Base
  , module Pudding.Types.Metadata
  , module Pudding.Name -- Export more
  ) where

import Control.DeepSeq (NFData)
import Data.Functor ((<&>))
import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)
import GHC.StableName (StableName)
import Prettyprinter (Pretty)
import Pudding.Name (Name(..), newTable, initTable, internalize)
import Pudding.Types.Base
import Pudding.Types.Metadata

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

nextNeutral :: forall t. Ctx t -> Eval
nextNeutral = neutralVar . Level . ctxSize

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
  , ctxSize :: !Int
  , ctxStack :: ![(Binder, t)]
  }
  deriving (Functor, Generic, NFData)

-- Context used for `eval`
type EvalCtx = Ctx Eval

-- Context used for `quote`: `ctxSize` is just used to convert `Level` back to `Index`
type QuoteCtx = Ctx ()

ctxOfStack :: forall t. Globals -> "stack" @:: [(Binder, t)] -> Ctx t
ctxOfStack globals stack =
  Ctx globals (length stack) stack

ctxOfList :: forall t. Globals -> "list in order" @:: [(Binder, t)] -> Ctx t
ctxOfList globals = ctxOfStack globals . reverse

ctxOfGlobals :: forall t. Globals -> Ctx t
ctxOfGlobals globals = ctxOfStack globals []

ctxOfSize :: Globals -> "size" @:: Int -> Ctx ()
ctxOfSize globals 0 = ctxOfGlobals globals
ctxOfSize globals sz = ctxOfStack globals $ (BFresh, ()) <$ [0..(sz - 1)]

snoc :: forall t. Ctx t -> Binder -> t -> Ctx t
snoc (Ctx globals sz stack) binder item =
  Ctx globals (sz + 1) ((binder, item) : stack)

indexCtx :: forall t. Index -> Ctx t -> t
indexCtx (Index idx) (Ctx { ctxStack }) = snd (ctxStack !! idx)

levelCtx :: forall t. Level -> Ctx t -> t
levelCtx lvl ctx@Ctx { ctxSize } = indexCtx (lvl2idx ctxSize lvl) ctx

mapCtx :: forall t t'. ((Index, Level) -> t -> t') -> Ctx t -> Ctx t'
mapCtx f ctx = Ctx (ctxGlobals ctx) (ctxSize ctx) $
  zip indices (ctxStack ctx) <&> \(idx, (bdr, t)) -> (bdr, f idx t)
  where
  indices = [0..] <&> \i -> (Index i, idx2lvl (ctxSize ctx) (Index i))

--------------------------------------------------------------------------------
-- Helper types!                                                              --
--------------------------------------------------------------------------------

-- decl: Π(T : Type), T -> T
-- surface syntax usage: f Nat 42
-- decl: Π{T : Type}, T -> T
-- surface syntax usage: f 42
data Plicit = Explicit | Implicit
  deriving (Eq, Ord, Generic, NFData)

-- DeBruijn index: 0 is the most recently bound variable (inner scope). Useful
-- for syntax manipulation: closed terms have well-defined semantics with `Index`.
newtype Index = Index Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData)

-- DeBruijn level: 0 is the first bound variable (outer scope). Used for
-- evaluation because they behave like variable names (they do not change once
-- introduced, unlike indices which would require shifting).
newtype Level = Level Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData)

idx2lvl :: Int -> Index -> Level
idx2lvl size (Index idx) = Level ((size - 1) - idx)
lvl2idx :: Int -> Level -> Index
lvl2idx size (Level lvl) = Index ((size - 1) - lvl)

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

-- A canonical name, that is merged during unification
data CanonicalName = CanonicalName
  { chosenName :: Name
  , allNames :: Set Name -- concatenated during unification
  }
  deriving (Generic, NFData)

instance Semigroup CanonicalName where
  l <> r = CanonicalName
    { chosenName = chosenName l
    , allNames = allNames l <> allNames r
    }

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
  onMetadata f = \case
    TVar old idx | new <- f old -> (old, TVar new idx, new)
    THole old hole | new <- f old -> (old, THole new hole, new)
    TUniv old univ | new <- f old -> (old, TUniv new univ, new)
    TGlobal old name | new <- f old -> (old, TGlobal new name, new)
    TLambda old p b ty body | new <- f old -> (old, TLambda new p b ty body, new)
    TPi old p b ty body | new <- f old -> (old, TPi new p b ty body, new)
    TApp old fun arg | new <- f old -> (old, TApp new fun arg, new)
    TSigma old p b ty body | new <- f old -> (old, TSigma new p b ty body, new)
    TPair old t l r | new <- f old -> (old, TPair new t l r, new)
    TFst old t | new <- f old -> (old, TFst new t, new)
    TSnd old t | new <- f old -> (old, TSnd new t, new)
    TTyCtor old name params indices | new <- f old -> (old, TTyCtor new name params indices, new)
    TConstr old name params args | new <- f old -> (old, TConstr new name params args, new)
  traverseMetadata f = \case
    TVar old idx -> (\new -> TVar new idx) <$> f old
    THole old hole -> (\new -> THole new hole) <$> f old
    TUniv old univ -> (\new -> TUniv new univ) <$> f old
    TGlobal old name -> (\new -> TGlobal new name) <$> f old
    TLambda old p b ty body -> (\new -> TLambda new p b)
      <$> f old
      <*> traverseMetadata f ty
      <*> traverseMetadata f body
    TPi old p b ty body -> (\new -> TPi new p b)
      <$> f old
      <*> traverseMetadata f ty
      <*> traverseMetadata f body
    TApp old fun arg -> TApp
      <$> f old
      <*> traverseMetadata f fun
      <*> traverseMetadata f arg
    TSigma old p b ty body -> (\new -> TSigma new p b)
      <$> f old
      <*> traverseMetadata f ty
      <*> traverseMetadata f body
    TPair old t l r -> TPair
      <$> f old
      <*> traverseMetadata f t
      <*> traverseMetadata f l
      <*> traverseMetadata f r
    TFst old t -> TFst <$> f old <*> traverseMetadata f t
    TSnd old t -> TSnd <$> f old <*> traverseMetadata f t
    TTyCtor old name params indices -> (\new -> TTyCtor new name)
      <$> f old
      <*> traverse (traverseMetadata f) params
      <*> traverse (traverseMetadata f) indices
    TConstr old name params args -> (\new -> TConstr new name)
      <$> f old
      <*> traverse (traverseMetadata f) params
      <*> traverse (traverseMetadata f) args
instance HasMetadata ScopedTerm where
  onMetadata f (Scoped term) | (old, term', new) <- onMetadata f term = (old, Scoped term', new)
  traverseMetadata f (Scoped term) = Scoped <$> traverseMetadata f term

instance HasMetadata Eval where
  onMetadata f = \case
    ENeut neutral | (old, neutral', new) <- onMetadata f neutral -> (old, ENeut neutral', new)
    EUniv old univ | new <- f old -> (old, EUniv new univ, new)
    ELambda old p b ty body | new <- f old -> (old, ELambda new p b ty body, new)
    EPi old p b ty body | new <- f old -> (old, EPi new p b ty body, new)
    ESigma old p b ty body | new <- f old -> (old, ESigma new p b ty body, new)
    EPair old t l r | new <- f old -> (old, EPair new t l r, new)
    ETyCtor old name params indices | new <- f old -> (old, ETyCtor new name params indices, new)
    EConstr old name params args | new <- f old -> (old, EConstr new name params args, new)
    EDeferred reason ty ref old term | new <- f old -> (old, EDeferred reason ty ref new (setMetadata term new), new)
  traverseMetadata f = \case
    ENeut neutral -> ENeut <$> traverseMetadata f neutral
    EUniv old univ -> (\new -> EUniv new univ) <$> f old
    ELambda old p b ty body -> (\new -> ELambda new p b)
      <$> f old
      <*> traverseMetadata f ty
      <*> traverseMetadata f body
    EPi old p b ty body -> (\new -> EPi new p b)
      <$> f old
      <*> traverseMetadata f ty
      <*> traverseMetadata f body
    ESigma old p b ty body -> (\new -> ESigma new p b)
      <$> f old
      <*> traverseMetadata f ty
      <*> traverseMetadata f body
    EPair old t l r -> EPair
      <$> f old
      <*> traverseMetadata f t
      <*> traverseMetadata f l
      <*> traverseMetadata f r
    ETyCtor old name params indices -> (\new -> ETyCtor new name)
      <$> f old
      <*> traverse (traverseMetadata f) params
      <*> traverse (traverseMetadata f) indices
    EConstr old name params args -> (\new -> EConstr new name)
      <$> f old
      <*> traverse (traverseMetadata f) params
      <*> traverse (traverseMetadata f) args
    EDeferred reason ty ref _ term ->
      (\term' ty' -> EDeferred reason ty' ref (getMetadata term') term')
      <$> traverseMetadata f term
      <*> traverseMetadata f ty

instance HasMetadata Neutral where
  onMetadata f (Neutral focus [])
    | (old, focus', new) <- onMetadata f focus
    = (old, Neutral focus' [], new)
  onMetadata f (Neutral focus (prj : prjs))
    | (old, prj', new) <- onMetadata f prj
    = (old, Neutral focus (prj' : prjs), new)
  traverseMetadata f (Neutral focus prjs) =
    Neutral <$> traverseMetadata f focus <*> bwd prjs
    where
    bwd [] = pure []
    bwd (one : more) = flip (:) <$> bwd more <*> traverseMetadata f one

instance HasMetadata NeutFocus where
  onMetadata f (NVar old lvl) | new <- f old = (old, NVar new lvl, new)
  onMetadata f (NHole old hole) | new <- f old = (old, NHole new hole, new)
  onMetadata f (NGlobal arity old name) | new <- f old = (old, NGlobal arity new name, new)
  traverseMetadata f (NVar old lvl) = (\new -> NVar new lvl) <$> f old
  traverseMetadata f (NHole old hole) = (\new -> NHole new hole) <$> f old
  traverseMetadata f (NGlobal arity old name) = (\new -> NGlobal arity new name) <$> f old

instance HasMetadata NeutPrj where
  onMetadata f = \case
    NApp old arg | new <- f old -> (old, NApp new arg, new)
    NFst old | new <- f old -> (old, NFst new, new)
    NSnd old | new <- f old -> (old, NSnd new, new)
  traverseMetadata f = \case
    NApp old arg -> NApp
      <$> f old
      <*> traverseMetadata f arg
    NFst old -> NFst <$> f old
    NSnd old -> NSnd <$> f old

instance HasMetadata Closure where
  onMetadata f (Closure bdr ctx term) | (old, term', new) <- onMetadata f term = (old, Closure bdr ctx term', new)
  -- This is somewhat a judgment call on whether to recurse into `ctx`:
  -- fully remapping `Metadata` would require it, but `ctx` is not part of the
  -- tree, really, it is just information captured from earlier.
  traverseMetadata f (Closure bdr ctx term) = Closure bdr ctx <$> traverseMetadata f term
