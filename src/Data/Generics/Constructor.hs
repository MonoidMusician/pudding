-- https://stackoverflow.com/questions/48179380/getting-the-data-constructor-name-as-a-string-using-ghc-generics
module Data.Generics.Constructor where

import GHC.Generics
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))

ctorName :: (HasConstructor (Rep t), Generic t) => t -> String
ctorName = gctorName . from

class HasConstructor (f :: Type -> Type) where
  gctorName :: f x -> String
  gctorNames :: proxy f -> [String]

instance HasConstructor f => HasConstructor (D1 c f) where
  gctorName (M1 x) = gctorName x
  gctorNames _ = gctorNames (Proxy :: Proxy f)

instance (HasConstructor x, HasConstructor y) => HasConstructor (x :+: y) where
  gctorName (L1 l) = gctorName l
  gctorName (R1 r) = gctorName r

  gctorNames _ = gctorNames (Proxy :: Proxy x) <> gctorNames (Proxy :: Proxy y)

instance Constructor c => HasConstructor (C1 c f) where
  gctorName = conName
  gctorNames _ = [conName (undefined :: t c f a)]
