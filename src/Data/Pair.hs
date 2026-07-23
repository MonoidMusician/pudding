module Data.Pair where

import Prelude
import Data.Functor.Classes (Eq1 (liftEq), Ord1 (liftCompare))
import GHC.Generics (Generic, Generic1, Generically1(..))
import Control.DeepSeq (NFData, NFData1)
import qualified Data.Aeson as AE
import Data.Functor ((<&>))
import Data.Foldable1 (Foldable1(foldMap1))
import Data.Distributive (Distributive(distribute))

data Pair t = t :# t
  deriving (Eq, Ord, Show, Read, Generic, NFData, AE.ToJSON, AE.FromJSON)
  deriving (Functor, Foldable, Traversable, Generic1, NFData1)
  deriving Applicative via Generically1 Pair

{-# COMPLETE Pair #-}
pattern Pair :: t -> t -> Pair t
pattern Pair x y = x :# y

instance Eq1 Pair where
  liftEq f (l1 :# r1) (l2 :# r2) = f l1 l2 && f r1 r2
instance Ord1 Pair where
  liftCompare f (l1 :# r1) (l2 :# r2) = f l1 l2 <> f r1 r2

instance Foldable1 Pair where
  foldMap1 f (l :# r) = f l <> f r

instance Distributive Pair where
  distribute items = Pair (items <&> \(Pair t _) -> t) (items <&> \(Pair _ t) -> t)
