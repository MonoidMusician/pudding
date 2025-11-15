module Pudding.Types.Metadata where

import Control.DeepSeq (NFData)
import Control.Lens (Lens', Traversal', Traversal1', cloneTraversal, foldMapOf, singular, toListOf, toNonEmptyOf, dropping, ignored, over)
import Data.Functor.Apply (Apply, MaybeApply(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Pudding.Parser.Base (SourceSpan)
import Data.IntMap.Monoidal.Strict (MonoidalIntMap)
import Data.Semigroup (Min)

-- Tag for metadata: not relevant to normalization/unification, just display or
-- implementation efficiency or so on.
-- Should implement `Semigroup`, so it can be unified!
newtype Meta t = Meta t
  deriving newtype (Eq, Ord, Semigroup, NFData)


-- `Exact` values only unify with themself: otherwise it throws an error.
newtype Exact t = Exact t
  deriving newtype (Eq, Ord, NFData)

instance Eq t => Semigroup (Exact t) where
  Exact l <> Exact r =
    if l == r then Exact l else error "Inexact"


-- Per-node metadata. Synthesized nodes do not have source metadata, and so use
-- `mempty :: Metadata`.
data Metadata = Metadata
  { sourcePos :: Set SourceSpan
    -- ^ concatenated during unification
  , metaVars :: MonoidalIntMap (Min Int)
    -- ^ current generation of each meta var, for substitution
  }
  deriving (Eq, Ord, Generic, NFData)

parseMetadata :: SourceSpan -> Metadata
parseMetadata pos = Metadata
  { sourcePos = Set.singleton pos
  , metaVars = mempty
  }

-- | Recalculate aspects of the top-level metadata of the node from children.
-- |
-- | Note: this does not handle base cases.
remeta :: HasMetadata t => t -> t
remeta focus = over metadata (recalcMetadata (toListOf childrenMetadata focus)) focus

-- | The procedure for recalculating metadata.
recalcMetadata :: [Metadata] -> Metadata -> Metadata
recalcMetadata fromChildren fromSelf = fromSelf
  { metaVars = foldMap metaVars fromChildren
  }


instance Semigroup Metadata where
  m1 <> m2 = Metadata
    { sourcePos = sourcePos m1 <> sourcePos m2
    , metaVars = metaVars m1 <> metaVars m2
    }

instance Monoid Metadata where
  mempty = Metadata mempty mempty

class HasMetadata t where
  -- | Traverse metadata from self, and children with specified depth.
  -- | Implement this one! (And use @traverseMetadataDepth@ for recursing.)
  traverseMetadata1Depth :: Maybe Word -> Traversal1' t Metadata

  -- | Skip traversing if depth 0, otherwise traverse own metadata, and then
  -- | children at decreased depth
  traverseMetadataDepth :: Maybe Word -> Traversal' t Metadata
  traverseMetadataDepth Nothing = cloneTraversal $ traverseMetadataDepth Nothing
  traverseMetadataDepth (Just 0) = ignored
  traverseMetadataDepth (Just n) = cloneTraversal $ traverseMetadata1Depth $ Just (n - 1)

  -- | Access the top metadata
  metadata :: Lens' t Metadata
  metadata = singular traverseMetadata1
  -- | Recursively access metadata from self and children
  traverseMetadata :: Traversal' t Metadata
  traverseMetadata = cloneTraversal traverseMetadata1
  -- | Recursively access non-empty metadata from self and children
  traverseMetadata1 :: Traversal1' t Metadata
  traverseMetadata1 = traverseMetadata1Depth Nothing
  -- | Recursively access metadata from children
  descendantMetadata :: Traversal' t Metadata
  descendantMetadata = dropping 1 traverseMetadata
  -- | Access metadata from direct children
  childrenMetadata :: Traversal' t Metadata
  childrenMetadata = dropping 1 $ cloneTraversal $ traverseMetadata1Depth $ Just 1

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
