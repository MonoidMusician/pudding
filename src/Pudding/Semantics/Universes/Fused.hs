module Pudding.Semantics.Universes.Fused where

import Prelude

import Pudding.Semantics.Universes
import Pudding.Semantics.LevelAlgebra
import Pudding.Types (Fresh)
import qualified Pudding.Semantics.LevelAlgebra as Lvl
import qualified Pudding.Semantics.Universes as Uni
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Monoidal.Strict (MonoidalIntMap)
import Data.IntSet (IntSet)

type QuickStored = (Int, [(Fresh, Relation, Fresh)])

data Fused meta = Fused
  { quickSolver :: !(Maybe Solver)
  , quickRels :: !QuickStored -- ^ relations to add to the next quick solver
  , slowSolver :: !(ConstraintMap meta) -- this is strict because it is a simple monoid instance
  , polyConstraints :: !(MonoidalIntMap IntSet)
  }

-- | Deciding Left or Right is O(1), but obtaining evidence takes longer.
check :: forall meta. Fused meta -> Either (InconsistentRelationship meta) (IntMap.IntMap Int)
check (Fused Nothing _ constraints _) = Left $
  case searchForInconsistency $ Uni.saturate constraints of
    Nothing -> error "Could not find evidence of inconsistency after all"
    Just example -> example
check (Fused (Just solver) _ _ _) = Right $ Lvl.demonstrate solver

addAll :: QuickStored -> [(Fresh, Relation, Fresh)] -> Solver -> Maybe (QuickStored, Solver)
addAll acc [] !solver = Just (acc, solver)
addAll (!sz, acc) (rel@(v1, _, v2) : rels) !solver = do
  (added, !solver') <- Lvl.checkAndRelate rel solver
  let
    acc' = case added of
      Nothing -> (sz, acc)
      Just rel' -> (sz+1, (v1, rel', v2) : acc)
  addAll acc' rels solver'

instance Monoid (Fused meta) where
  mempty = Fused (Just Lvl.base) (0, []) mempty mempty
instance Semigroup (Fused meta) where
  (Fused (Just s1) (sz1, r1) slow1 poly1) <> (Fused (Just s2) (sz2, r2) slow2 poly2) =
    case sz1 `compare` sz2 of
      LT -> case addAll (sz2, r2) r1 s2 of
        Nothing -> Fused Nothing (0, []) (slow1 <> slow2) (poly1 <> poly2)
        Just (r, !s) -> Fused (Just s) r (slow1 <> slow2) (poly1 <> poly2)
      _ -> case addAll (sz1, r1) r2 s1 of
        Nothing -> Fused Nothing (0, []) (slow1 <> slow2) (poly1 <> poly2)
        Just (r, !s) -> Fused (Just s) r (slow1 <> slow2) (poly1 <> poly2)
  -- Inconsistent: just need the slow solver
  Fused _ _ slow1 poly1 <> Fused _ _ slow2 poly2 = Fused Nothing (0, []) (slow1 <> slow2) (poly1 <> poly2)
