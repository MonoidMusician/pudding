module Data.Conserve where

import Prelude

import Data.Functor ((<&>))
import Control.Comonad (Comonad(extract, extend))

-- | Use to conserve referential identity when possible.
-- |
-- | Isomorphic to `(,) All`
data Conserve t = Conserved t | Altered !t
  deriving (Functor, Foldable, Traversable)

instance Applicative Conserve where
  {-# INLINE pure #-}
  pure = Conserved

  {-# INLINEABLE (<*>) #-}
  (<*>) (Conserved f) (Conserved t) = Conserved (f t)
  (<*>) fs ts = Altered (extract fs (extract ts))

instance Monad Conserve where
  {-# INLINEABLE (>>=) #-}
  (>>=) (Conserved t) f = f t
  (>>=) (Altered t) f = case f t of
    Conserved r -> Altered r
    r@(Altered _) -> r

instance Comonad Conserve where
  {-# INLINE extract #-}
  extract (Conserved t) = t
  extract (Altered t) = t

  {-# INLINE extend #-}
  extend f ts@(Conserved _) = Conserved (f ts)
  extend f ts@(Altered _) = Altered (f ts)

{-# INLINE conserve #-}
conserve :: forall t. t -> (t -> Maybe t) -> Conserve t
conserve t f = case f t of
  Just t' -> Altered t'
  Nothing -> Conserved t

{-# INLINE conserve' #-}
conserve' :: forall t. t -> (t -> Conserve t) -> Conserve t
conserve' t f = case f t of
  Altered t' -> Altered t'
  Conserved _ -> Conserved t

{-# INLINE reconserve #-}
reconserve :: forall t. (t -> Conserve t) -> (t -> Conserve t)
reconserve = flip conserve'

{-# INLINE conserve_ #-}
conserve_ :: forall t. Eq t => t -> (t -> t) -> Conserve t
conserve_ t f = case f t of
  t' | t' /= t -> Altered t'
  _ -> Conserved t

{-# INLINE conserveM #-}
conserveM :: forall t m. Functor m => t -> (t -> m (Maybe t)) -> m (Conserve t)
conserveM t f = f t <&> \case
  Just t' -> Altered t'
  Nothing -> Conserved t

{-# INLINE conserveM' #-}
conserveM' :: forall t m. Functor m => t -> (t -> m (Conserve t)) -> m (Conserve t)
conserveM' t f = f t <&> \case
  Altered t' -> Altered t'
  Conserved _ -> Conserved t

{-# INLINE conserveM_ #-}
conserveM_ :: forall t m. Eq t => Functor m => t -> (t -> m t) -> m (Conserve t)
conserveM_ t f = f t <&> \case
  t' | t' /= t -> Altered t'
  _ -> Conserved t
