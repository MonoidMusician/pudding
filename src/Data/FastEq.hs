{-# LANGUAGE UndecidableInstances #-}
module Data.FastEq where

import Prelude
import GHC.Generics (Generic (from, Rep))
import GHC.Base (reallyUnsafePtrEquality, isTrue#)
import Control.DeepSeq (NFData)
import qualified Data.Aeson as AE
import Prettyprinter (Pretty)

newtype FastEq t = FastEq t
  deriving newtype (NFData, AE.ToJSON, AE.FromJSON, Show, Read, Pretty)

instance (Generic t, Eq (Rep t ())) => Eq (FastEq t) where
  FastEq !t1 == FastEq !t2 | isTrue# (reallyUnsafePtrEquality t1 t2) = True
  FastEq !t1 == FastEq !t2 = from t1 == (from t2 :: Rep t ())

instance (Generic t, Ord (Rep t ())) => Ord (FastEq t) where
  FastEq !t1 `compare` FastEq !t2 | isTrue# (reallyUnsafePtrEquality t1 t2) = EQ
  FastEq !t1 `compare` FastEq !t2 = from t1 `compare` (from t2 :: Rep t ())

(===) :: forall t. Eq t => t -> t -> Bool
!t1 === !t2 | isTrue# (reallyUnsafePtrEquality t1 t2) = True
!t1 === !t2 = t1 == t2

(/==) :: forall t. Eq t => t -> t -> Bool
!t1 /== !t2 = not (t1 === t2)

