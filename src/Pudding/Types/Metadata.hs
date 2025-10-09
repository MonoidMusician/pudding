module Pudding.Types.Metadata where

import Control.DeepSeq (NFData)
import Control.Lens (Lens', Traversal', Traversal1', cloneTraversal, foldMapOf, singular, toListOf, toNonEmptyOf)
import Data.Functor.Apply (Apply, MaybeApply(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Set (Set)
import GHC.Generics (Generic)
import Pudding.Parser.Base (SourceSpan)

-- Tag for metadata: not relevant to normalization/unification, just display or
-- implementation efficiency or so on.
-- Should implement `Semigroup`, so it can be unified!
newtype Meta t = Meta t
  deriving newtype (Eq, Ord, Semigroup, NFData)

-- Per-node metadata. Synthesized nodes do not have source metadata, and so use
-- `mempty :: Metadata`.
data Metadata = Metadata
  { sourcePos :: Set SourceSpan -- concatenated during unification
  }
  deriving (Eq, Ord, Generic, NFData)

instance Semigroup Metadata where
  m1 <> m2 = Metadata
    { sourcePos = sourcePos m1 <> sourcePos m2
    }

instance Monoid Metadata where
  mempty = Metadata mempty

class HasMetadata t where
  -- | Access the top metadata
  metadata :: Lens' t Metadata
  metadata = singular traverseMetadata1
  -- | Recursively access metadata from children
  traverseMetadata :: Traversal' t Metadata
  traverseMetadata = cloneTraversal traverseMetadata1
  -- | Recursively access non-empty metadata from children
  traverseMetadata1 :: Traversal1' t Metadata

-- | List the metadata (including the node itself)
listMetadata1 :: forall t. HasMetadata t => t -> NonEmpty Metadata
listMetadata1 = toNonEmptyOf traverseMetadata1

listMetadata :: forall t. HasMetadata t => t -> [Metadata]
listMetadata = toListOf traverseMetadata

-- | Aggregate the metadata (including the node itself)
foldMetadata1 :: forall t m. Semigroup m => HasMetadata t => (Metadata -> m) -> t -> m
foldMetadata1 = foldMapOf traverseMetadata1

foldMetadata :: forall t m. Monoid m => HasMetadata t => (Metadata -> m) -> t -> m
foldMetadata = foldMapOf traverseMetadata

-- | Strengthen an `Apply` profunctor in to an `Applicative` profunctor
apply :: Apply f => (a -> f b) -> a -> MaybeApply f b
apply f = MaybeApply . Left . f
