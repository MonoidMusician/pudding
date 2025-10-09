module Pudding.Types.Stack where

import Control.DeepSeq (NFData)
import Control.Exception (assert)
import Control.Lens (Iso, folded, foldMapOf, from, iso, traverseOf, withIso)
import qualified Data.RAList as RAL
import Data.RAList (RAList)
import GHC.Generics (Generic)
import Prettyprinter (Pretty)

-- | Finite mapping of indices `i` to elements `Elem`
class StackLike c where
  type Elem c

  infixr 8 @@
  (@@) :: ToIndex i => c -> i -> Elem c

  size :: c -> Int

  empty :: c
  push' :: c -> Elem c -> c
  pop :: c -> Maybe (c, Elem c)

push :: StackLike c => Elem c -> c -> (Level, c)
push e c = (Level (size c), push' c e)

infixl 5 :>
pattern (:>) :: StackLike c => c -> Elem c -> c
pattern (:>) xs x <- (pop -> Just (xs, x)) where
  (:>) xs x = push' xs x

pattern Nil :: StackLike c => c
pattern Nil <- (pop -> Nothing) where
  Nil = empty

{-# COMPLETE (:>), Nil #-}

-- Slightly silly instance for when we only care about the term depth
instance StackLike Int where
  type Elem Int = ()
  _ @@ _ = ()
  size = id
  empty = 0
  push' i _ = i + 1
  pop 0 = Nothing
  pop n = Just (n - 1, ())

-- DeBruijn index: 0 is the most recently bound variable (inner scope). Useful
-- for syntax manipulation: closed terms have well-defined semantics with
-- `Index`.
newtype Index = Index Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData)

class ToIndex i where
  index :: StackLike c => c -> i -> Index

instance ToIndex Index where
  index c ix@(Index i) = assert (i < size c) ix

instance ToIndex Int where
  index c i = assert (i < size c) (Index i)

instance ToIndex Level where
  index c (Level lvl) = index c ((size c - 1) - lvl)

-- DeBruijn level: 0 is the first bound variable (outer scope). Used for
-- evaluation because they behave like variable names (they do not change once
-- introduced, unlike indices which would require shifting).
newtype Level = Level Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData)

class ToLevel l where
  level :: StackLike c => c -> l -> Level

instance ToLevel Level where
  level c lv@(Level l) = assert (l < size c) lv

instance ToLevel Int where
  level c l = assert (l < size c) (Level l)

instance ToLevel Index where
  level c (Index idx) = level c ((size c - 1) - idx)

-- | A stack-shaped context. New elements, corresponding to inner binders, are
-- | added on the right. DeBruijn indicies index from the right; levels index
-- | from the left. The internal representation is stored right-to-left to allow
-- | snoc semantics.
data Stack a = Stack !Int !(RAList a)
  deriving (Functor, Generic, NFData)

instance Foldable Stack where
  foldMap :: Monoid m => (a -> m) -> Stack a -> m
  foldMap = foldMapOf (from stack . folded)

instance Traversable Stack where
  traverse :: Applicative f => (a -> f b) -> Stack a -> f (Stack b)
  traverse = traverseOf (from stack . traverse)

instance StackLike (Stack a) where
  type Elem (Stack a) = a

  s@(Stack sz elems) @@ ix = case index s ix of
    Index i -> assert (i < sz) (elems RAL.! i)

  size (Stack sz _) = sz

  empty = Stack 0 RAL.empty

  push' (Stack sz elems) x = Stack (1 + sz) (RAL.cons x elems)

  pop (Stack sz elems) = do
    (x, xs) <- RAL.uncons elems
    return (Stack (sz - 1) xs, x)

-- | Construct a stack, `head` being the outermost binder
stack :: Iso [a] [b] (Stack a) (Stack b)
stack = withIso rstack \fl tl -> iso (fl . reverse) (reverse . tl)
  -- `reversed . rstack` is morally correct but the monomorphization of the
  -- underlying `reverse` breaks heterogeneous optics.

-- | Construct a stack, `head` being the innermost binder
rstack :: Iso [a] [b] (Stack a) (Stack b)
rstack = iso
  (\xs -> let elems = RAL.fromList xs in Stack (RAL.length elems) elems)
  (\(Stack _ elems) -> RAL.toList elems)
