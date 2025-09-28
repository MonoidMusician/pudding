module Pudding.Types where

import Data.Text (Text)
import Data.Set (Set)
import Data.Map (Map)

--------------------------------------------------------------------------------
-- Main semantic types!                                                       --
--------------------------------------------------------------------------------

data Binder
  = BVar (Meta CanonicalName)
  | BMulti Binder Binder -- Bind two to the same value
  | BPair Binder Binder -- Bind to fst and snd projections

data GlobalInfo
  -- A function or global constant or whatever
  = GlobalTerm Term
  -- An inductive type declaration
  | GlobalType GlobalTypeInfo

data GlobalTypeInfo = GlobalTypeInfo
  { typeArgs :: [(Plicit, Binder, Term)]
  , typeCons :: Map Name ConstructorInfo
  }

data ConstructorInfo = ConstructorInfo
  { arguments :: [(Plicit, Binder, Term)]
  , indices :: [Term]
  }

-- A dependently typed term in the core calculus
data Term
  = TVar Index
  | TGlobal Name {-cached info:-} (Meta (Exact GlobalInfo))
  | THole Fresh
  | TLet Binder {-value:-} Term {-body:-} Term
  | TLambda Plicit Binder {-domain type:-} Term {-body:-} Term
  | TPi Plicit Binder {-domain type:-} Term {-codomain:-} Term
  | TApp {-function:-} Term {-argument:-} Term
  | TSigma Plicit Binder {-fst type:-} Term {-snd type under fst type:-} Term
  | TPair {-fst value:-} Term {-snd type functor:-} Term {-snd value:-} Term
  | TFst Term
  | TSnd Term

-- Result of Normalization by Evaluation (NbE), the semantic domain.
data Eval
  = ENeut Neutral -- do we want it tagged with its ultimate type?
  | ELambda Plicit Binder {-domain type:-} Eval {-body:-} Closure
  | EPi Plicit Binder {-domain type:-} Eval {-codomain:-} Closure
  | ESigma Plicit Binder {-fst type:-} Eval {-snd type under fst type:-} Closure
  | EPair {-fst value:-} Eval {-snd type functor:-} Eval {-snd value:-} Eval

-- A Neutral is stuck on a variable (or hole), with some projections and eliminators applied to it.
-- (This is the Normalization part of NbE: inserting variables to evaluate open terms.)
data Neutral = Neutral NeutHead [NeutPrj]
data NeutHead
  = NVar {-type:-} Term Level
  | NHole {-type:-} Fresh
data NeutPrj
  = NFst
  | NSnd

-- Closure: an unevaluated term ossified in an environment of evaluated variables
data Closure = Closure [Eval] Term

--------------------------------------------------------------------------------
-- Helper types!                                                              --
--------------------------------------------------------------------------------

data Plicit = Explicit | Implicit

-- DeBruijn index: 0 is the most recently bound variable (inner scope). Used for typechecking.
newtype Index = Index Int
  deriving (Eq, Ord)

-- DeBruijn level: 0 is the first bound variable (outer scope). Used for evaluation.
newtype Level = Level Int
  deriving (Eq, Ord)

-- Name (TODO: string interning)
newtype Name = Name Text
  deriving (Eq, Ord)

-- E.g. for numbering typed holes
newtype Fresh = Fresh Int

--------------------------------------------------------------------------------
-- Metadata types                                                             --
--------------------------------------------------------------------------------

-- Tag for metadata: not relevant to normalization/unification, just display or
-- implementation efficiency or so on.
-- Should implement `Semigroup`, so it can be unified!
newtype Meta t = Meta t

data CanonicalName = CanonicalName
  { chosenName :: Name
  , allNames :: Set Name
  }

-- `Exact` values only unify with themself: otherwise it throws an error.
newtype Exact t = Exact t
  deriving (Eq, Ord)

instance Eq t => Semigroup (Exact t) where
  Exact l <> Exact r =
    if l == r then Exact l else error "Inexact"
