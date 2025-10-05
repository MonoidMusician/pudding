{-# LANGUAGE DataKinds #-}
module Pudding.Types
  ( module Pudding.Types -- Export the default exports of this module
  , module Pudding.Name -- Export more
  ) where

import Data.Functor.Const (Const(..))
import Data.Set (Set)
import Data.Map (Map)
import Data.Vector (Vector)
import GHC.Base (Symbol)
import Text.Parsec.Pos (SourcePos)
import Control.DeepSeq (NFData(rnf))
import GHC.Generics (Generic)
import Pudding.Name (Name(..), newTable, initTable, internalize)
import Control.Applicative.Backwards (Backwards (forwards, Backwards))
import Prettyprinter (Pretty)
import GHC.StableName (StableName)
import Data.Text (Text)

-- Just give a little description of the type
type Desc (s :: Symbol) t = t

--------------------------------------------------------------------------------
-- Main semantic types!                                                       --
--------------------------------------------------------------------------------

data Binder
  = BVar !(Meta CanonicalName)
  | BMulti !Binder !Binder -- Bind two to the same value
  | BPair !Binder !Binder -- Bind to fst and snd projections
  deriving (Generic, NFData)

data GlobalTerm = GlobalTerm !Term Eval
  deriving (Generic, NFData)

data GlobalInfo
  -- A function or global constant or whatever
  = GlobalDefn (Desc "type" GlobalTerm) (Desc "term" GlobalTerm)
  -- An inductive type declaration
  | GlobalType GlobalTypeInfo
  deriving (Generic, NFData)

type Globals = Map Name GlobalInfo

data GlobalTypeInfo = GlobalTypeInfo
  { typeArgs :: !(Vector (Plicit, Binder, Term))
  , typeCons :: !(Map Name ConstructorInfo)
  }
  deriving (Generic, NFData)

data ConstructorInfo = ConstructorInfo
  { arguments :: !(Vector (Plicit, Binder, Term))
  , indices :: !(Vector Term)
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
  -- | TLet Metadata Binder (Desc "value" Term) (Desc "body" Term)
  | TLambda
      -- Metadata: not relevant to equality/unification
      -- Every argument is explicit in the core and every core binder only binds
      -- one variable, but we keep this information around for pretty printing
      Metadata !Plicit Binder
      -- Actual core data (influences equality, etc.)
      (Desc "domain type" Term) (Desc "body" Term)
  | TPi
      Metadata !Plicit Binder
      (Desc "domain type" Term) (Desc "codomain" Term)
  | TApp Metadata
      (Desc "function" Term) (Desc "argument" Term)
  | TSigma
      Metadata !Plicit Binder
      (Desc "fst type" Term) (Desc "snd type under fst type" Term)
  -- A pair of a sigma type
  | TPair Metadata
      (Desc "sigma type" Term)
      (Desc "fst value" Term)
      (Desc "snd value" Term)
  | TFst Metadata Term
  | TSnd Metadata Term
  deriving (Generic, NFData)

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
      (Desc "domain type" Eval) (Desc "body" Closure)
  | EPi
      Metadata !Plicit Binder
      (Desc "domain type" Eval) (Desc "codomain" Closure)
  | ESigma
      Metadata !Plicit Binder
      (Desc "fst type" Eval) (Desc "snd type under fst type" Closure)
  | EPair Metadata (Desc "sigma type" Eval) (Desc "fst value" Eval) (Desc "snd value" Eval)
  | EDeferred (Desc "reason" (Meta Text)) (Desc "type" Eval) !(Desc "sharing" (Maybe (StableName Eval))) Metadata (Desc "deferred term" Eval)
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
  deriving (Generic, NFData)
data NeutPrj
  = NApp Metadata (Desc "arg" Eval)
  | NFst Metadata
  | NSnd Metadata
  deriving (Generic, NFData)
-- Alternatively: we could just implement it as a recursive type
-- Neutral = NVar Level | NFst Neutral | NApp (Desc "fun" Neutral) (Desc "arg" Eval)


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
data Closure = Closure (Desc "saved external context" EvalCtx) (Desc "body" Term)
  deriving (Generic, NFData)

data EvalCtx = EvalCtx
  { evalSize :: !Int
  , evalValues :: ![Eval]
  , evalGlobals :: Map Name GlobalInfo
  }
  deriving (Generic, NFData)

data QuoteCtx = QuoteCtx
  { quoteSize :: !Int
  -- ^ `quoteSize` is just used to convert `Level` back to `Index`
  }
  deriving (Generic, NFData)

--------------------------------------------------------------------------------
-- Helper types!                                                              --
--------------------------------------------------------------------------------

-- decl: Π(T : Type), T -> T
-- surface syntax usage: f Nat 42
-- decl: Π{T : Type}, T -> T
-- surface syntax usage: f 42
data Plicit = Explicit | Implicit
  deriving (Eq, Ord, Generic, NFData)

-- DeBruijn index: 0 is the most recently bound variable (inner scope). Used for
-- syntax manipulation.
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

-- Tag for metadata: not relevant to normalization/unification, just display or
-- implementation efficiency or so on.
-- Should implement `Semigroup`, so it can be unified!
newtype Meta t = Meta t
  deriving newtype (Eq, Ord, Semigroup, NFData)


data SourceSpan = SourceSpan
  { spanBegin :: SourcePos
  , spanEnd :: SourcePos
  }
  deriving (Eq, Ord, Generic)

instance Semigroup SourceSpan where
  SourceSpan b1 e1 <> SourceSpan b2 e2 =
    SourceSpan (min b1 b2) (max e1 e2)

-- Per-node metadata (a monoid, unlike the other `Meta`s), since synthesized nodes
-- do not have source metadata and such.
data Metadata = Metadata
  { sourcePos :: Set SourceSpan -- concatenated during unification
  }
  deriving (Eq, Ord, Generic)
instance Semigroup Metadata where
  m1 <> m2 = Metadata
    { sourcePos = sourcePos m1 <> sourcePos m2
    }
-- For nodes we synthesize, use `mempty :: Metadata`
instance Monoid Metadata where
  mempty = Metadata mempty
instance NFData Metadata where
  rnf (Metadata pos) = seq pos () -- good enough

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

-- | Class for handling metadata in types
class HasMetadata t where
  -- | Non-recursive: modify the top metadata
  onMetadata :: (Metadata -> Metadata) -> t -> (Metadata, t, Metadata)
  -- | Recursive! Modify/aggregate all of the metadata in the tree
  traverseMetadata :: forall f. Applicative f => (Metadata -> f Metadata) -> t -> f t

-- | Get the metadata at the top
getMetadata :: forall t. HasMetadata t => t -> Metadata
getMetadata t = let (old, _, _) = onMetadata id t in old

-- | Set the metadata at the top
setMetadata :: forall t. HasMetadata t => t -> Metadata -> t
setMetadata t new = let (_, t', _) = onMetadata (const new) t in t'

-- | List the metadata (including the node itself)
listMetadata :: forall t. HasMetadata t => t -> [Metadata]
listMetadata t = let Const r = traverseMetadata (Const . pure) t in r

-- | Aggregate the metadata (including the node itself)
-- TODO: should be `Semigroup`
foldMetadata :: forall t m. Monoid m => HasMetadata t => (Metadata -> m) -> t -> m
foldMetadata f t = let Const r = traverseMetadata (Const . f) t in r

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

instance HasMetadata Eval where
  onMetadata f = \case
    ENeut neutral | (old, neutral', new) <- onMetadata f neutral -> (old, ENeut neutral', new)
    EUniv old univ | new <- f old -> (old, EUniv new univ, new)
    ELambda old p b ty body | new <- f old -> (old, ELambda new p b ty body, new)
    EPi old p b ty body | new <- f old -> (old, EPi new p b ty body, new)
    ESigma old p b ty body | new <- f old -> (old, ESigma new p b ty body, new)
    EPair old t l r | new <- f old -> (old, EPair new t l r, new)
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
  traverseMetadata f (Neutral focus prjs) = forwards $
    Neutral <$> Backwards (traverseMetadata f focus) <*> bwd prjs
    where
    bwd [] = pure []
    bwd (one : more) = flip (:) <$> bwd more <*> Backwards (traverseMetadata f one)

instance HasMetadata NeutFocus where
  onMetadata f (NVar old lvl) | new <- f old = (old, NVar new lvl, new)
  onMetadata f (NHole old hole) | new <- f old = (old, NHole new hole, new)
  traverseMetadata f (NVar old lvl) = (\new -> NVar new lvl) <$> f old
  traverseMetadata f (NHole old hole) = (\new -> NHole new hole) <$> f old

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
  onMetadata f (Closure ctx term) | (old, term', new) <- onMetadata f term = (old, Closure ctx term', new)
  traverseMetadata f (Closure ctx term) = Closure ctx <$> traverseMetadata f term
