module Pudding.Types.Metadata where

import Control.DeepSeq (NFData)
import Data.Functor.Const (Const(..))
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
