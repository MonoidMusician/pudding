{-# LANGUAGE DataKinds #-}
module Pudding.Types
  ( module Pudding.Types -- Export the default exports of this module
  , module Pudding.Name -- Export more
  ) where

import Data.Functor ((<&>))
import Data.Functor.Const (Const(..))
import Data.Set (Set)
import Data.Map (Map)
import Data.Vector (Vector)
import GHC.Base (Symbol)
import Text.Parsec.Pos (SourcePos)
import Control.DeepSeq (NFData(rnf))
import GHC.Generics (Generic)
import Pudding.Name (Name(..), newTable, initTable, internalize)
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

-- print, parse :: Surface <-> Text
-- elaborate :: Surface -> Elab (Term, Term)
-- typeof :: Term -> Term
-- printCore, parseCore :: Term <-> Text
-- eval :: EvalCtx -> Term -> Eval
-- printEval :: Eval -> Text
-- conversionCheck :: EvalCtx -> Eval -> Eval -> Maybe Eval
-- quote :: QuoteCtx -> Eval -> Term

-------------------------------
-- The core types themselves --
-------------------------------

-- (It usually ends up being convenient in Haskell to reduce type variables
-- and not shove metadata into a separate structure, unfortunately)

-- A dependently typed term in the *core* calculus (not meant to be pleasant to write).
-- It is intrinsically typed in the sense that it supports `typeof :: Term -> Term`
-- (where `typeof . typeof` resolves to some `TUniv`)
data Term
  = TVar Metadata !Index
  -- | TUniv Metadata ULevel
  | TGlobal Metadata !Name (Desc "cached info" (Meta (Exact GlobalInfo)))
  -- | THole Metadata !Fresh
  -- | TLet Metadata Binder (Desc "value" Term) (Desc "body" Term)
  | TLambda Metadata !Plicit Binder (Desc "domain type" Term) (Desc "body" Term)
  | TPi Metadata !Plicit Binder (Desc "domain type" Term) (Desc "codomain" Term)
  | TApp Metadata (Desc "function" Term) (Desc "argument" Term)
  -- | TSigma Metadata !Plicit Binder (Desc "fst type" Term) (Desc "snd type under fst type" Term)
  -- | TPair Metadata (Desc "fst value" Term) (Desc "snd type functor" Term) (Desc "snd value" Term)
  -- | TFst Metadata Term
  -- | TSnd Metadata Term
  deriving (Generic, NFData)

spine :: Term -> (Term, [Term])
spine = go []
  where
  go acc (TApp _ fun arg) = go (arg : acc) fun
  go acc fun = (fun, acc)

-- Result of Normalization by Evaluation (NbE), the semantic domain.
data Eval
  = ENeut Metadata Neutral -- do we want it tagged with its ultimate type?
  | EUniv Metadata ULevel
  | ELambda Metadata !Plicit Binder (Desc "domain type" Eval) (Desc "body" Closure)
  | EPi Metadata !Plicit Binder (Desc "domain type" Eval) (Desc "codomain" Closure)
  | ESigma Metadata !Plicit Binder (Desc "fst type" Eval) (Desc "snd type under fst type" Closure)
  | EPair Metadata (Desc "fst value" Eval) (Desc "snd type functor" Eval) (Desc "snd value" Eval)
  deriving (Generic, NFData)

-- A Neutral is stuck on a variable (or hole), with some projections and eliminators applied to it.
-- (This is the Normalization part of NbE: inserting variables to evaluate open terms.)
data Neutral = Neutral NeutHead [NeutPrj]
  deriving (Generic, NFData)
data NeutHead
  = NVar Metadata (Desc "type" Term) !Level
  | NHole Metadata (Desc "type" Term) !Fresh
  deriving (Generic, NFData)
data NeutPrj
  = NFst Metadata
  | NSnd Metadata
  deriving (Generic, NFData)

-- Closure: an unevaluated term frozen in an environment of evaluated variables.
data Closure = Closure EvalCtx Term
  deriving (Generic, NFData)

data EvalCtx = EvalCtx
  { evalSize :: !Int
  , evalValues :: ![Eval]
  }
  deriving (Generic, NFData)

data QuoteCtx = QuoteCtx
  { quoteSize :: !Int
  }
  deriving (Generic, NFData)

--------------------------------------------------------------------------------
-- Helper types!                                                              --
--------------------------------------------------------------------------------

data Plicit = Explicit | Implicit
  deriving (Eq, Ord, Generic, NFData)

-- DeBruijn index: 0 is the most recently bound variable (inner scope). Used for typechecking.
newtype Index = Index Int
  deriving newtype (Eq, Ord, Show, NFData)

-- DeBruijn level: 0 is the first bound variable (outer scope). Used for evaluation.
newtype Level = Level Int
  deriving newtype (Eq, Ord, Show, NFData)

-- E.g. for numbering typed holes
newtype Fresh = Fresh Int
  deriving newtype (Eq, Ord, Show, NFData)

data ULevel
  = UBase !Int
  | UMeta !Int
  | UVar !Fresh -- unsolved level
  deriving (Eq, Ord, Generic, NFData)

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
    TGlobal old name info | new <- f old -> (old, TGlobal new name info, new)
    TLambda old p b ty body | new <- f old -> (old, TLambda new p b ty body, new)
    TPi old p b ty body | new <- f old -> (old, TPi new p b ty body, new)
    TApp old fun arg | new <- f old -> (old, TApp new fun arg, new)
  traverseMetadata f = \case
    TVar old idx -> f old <&> \new -> TVar new idx
    TGlobal old name info -> f old <&> \new -> TGlobal new name info
    TLambda old p b ty body -> f old <&> \new -> TLambda new p b ty body
    TPi old p b ty body -> f old <&> \new -> TPi new p b ty body
    TApp old fun arg -> f old <&> \new -> TApp new fun arg
