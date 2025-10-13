{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const", "Redundant lambda", "Redundant bracket", "Eta reduce" #-}
module Pudding.Semantics.LevelAlgebra where

import Prelude hiding (lookup)

import Data.Foldable (fold)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Ratio (Ratio, numerator, denominator, (%))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Pudding.Types (Fresh (Fresh))
import Pudding.Types.Base (type (@::))
import Pudding.Semantics.Universes (Relation (..))
import qualified Data.IntMap.Merge.Strict as IntMapMerge
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntSet as IntSet
import Safe.Foldable (maximumMay, minimumMay)
import Data.Maybe (fromMaybe, mapMaybe)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

-- v: number of variables
-- d: number of (active) dimensions (<= ctr, <= v)
-- w: maximum active dimensions of a single lattice point (<= d)
-- c: maximum number of points along a dimension (= maximum chain depth, <= v)
-- A: apartnesses (<= v^2)
-- log: generic log, i.e. log v, but usually better

type Chain = Ratio Int

minChain, maxChain :: Chain
(minChain, maxChain) = (-32, 32) -- (-1048576, 1048576) -- 2^20

intermediate :: Chain -> Chain -> Chain
intermediate r1 r2
  | n1 <- numerator r1, d1 <- denominator r1
  , n2 <- numerator r2, d2 <- denominator r2
  , d1 == d2
  , avg <- (n1 + n2) `div` 2
  , rounder <- avg + (avg `mod` 2)
  , n1 < rounder, rounder < n2
  = rounder % d1
intermediate x y = (x + y) / 2 -- TODO

isBetween :: (Chain, Chain) -> (Chain -> Bool)
isBetween (x, z) = \y ->
  case (compare x y, compare y z) of
    (LT, GT) -> False
    (GT, LT) -> False
    _ -> True

-- O(log)
belowChain :: Chain -> Set.Set Chain -> Maybe Chain
belowChain point chain =
  if Set.findMin chain == point then
    Just (intermediate point minChain)
  else Nothing

-- O(log)
aboveChain :: Chain -> Set.Set Chain -> Maybe Chain
aboveChain point chain =
  if Set.findMax chain == point then
    Just (intermediate point maxChain)
  else Nothing

-- O(log)
betweenChain :: (Chain, Chain) -> Set.Set Chain -> Maybe Chain
betweenChain (lower, upper) chain =
  if Set.findIndex lower chain + 1 == Set.findIndex upper chain then
    Just (intermediate lower upper)
  else Nothing

type Var = Int
type VarMap = IntMap
type Dim = Int
type DimMap = IntMap

type Lattice = DimMap Chain

data Solver = Solver
  { ctr :: !Int -- ^ next free dimension to use
  , vars :: !(VarMap Lattice) -- ^ current position of each point
  , points :: !(DimMap (Set.Set Chain)) -- ^ active points along each dimension
  , aparts :: !(VarMap IntSet.IntSet) -- ^ smaller var index to larger var index
  }
  deriving (Show, Generic, NFData)

base :: Solver
base = Solver 0 IntMap.empty IntMap.empty IntMap.empty

(@!) :: Int -> Chain -> Lattice
dimension @! position = IntMap.singleton dimension position

_apart :: Int -> Int -> Solver -> Solver
_apart v1 v2 solver = solver
  { aparts = IntMap.insertWith (<>) (min v1 v2) (IntSet.singleton (max v1 v2)) (aparts solver) }

_apartIf :: Bool -> Int -> Int -> Solver -> Solver
_apartIf True = _apart
_apartIf False = \_ _ -> id

_apartIfRel :: Relation -> Int -> Int -> Solver -> Solver
_apartIfRel = _apartIf . (LessThan ==)

setVar :: Var -> (Solver, Lattice) -> Solver
setVar v (solver, !pos) =
  solver { vars = IntMap.insert v pos (vars solver) }

newVar :: "var" @:: Int -> Solver -> Solver
newVar = flip newVarBelow IntMap.empty

newVarBelow :: "var" @:: Int -> "pos" @:: Lattice -> Solver -> Solver
newVarBelow v pos solver = setVar v (below pos solver)

newDim :: Solver -> (Solver, Lattice)
newDim = newDimBelow IntMap.empty

newDimBelow :: "pos" @:: Lattice -> Solver -> (Solver, Lattice)
newDimBelow pos solver@(Solver { ctr, points }) =
  let (dim, pt) = (ctr, 0) in
  (solver { ctr = ctr + 1, points = IntMap.insert dim (Set.singleton pt) points }, IntMap.insert dim pt pos)

data PartialComparison
  = PosetUN -- uncomparable
  | PosetEQ -- equal
  | PosetLE -- less-than-or-equal (but not known to be equal (yet))
  | PosetGE -- greather-than-or-equal
  deriving (Eq, Ord, Show, Generic, NFData)
instance Monoid PartialComparison where
  mempty = PosetEQ
instance Semigroup PartialComparison where
  (<>) :: PartialComparison -> PartialComparison -> PartialComparison
  PosetEQ <> r = r
  r <> PosetEQ = r
  PosetLE <> PosetLE = PosetLE
  PosetGE <> PosetGE = PosetGE
  _ <> _ = PosetUN

partialOfTotal :: Ordering -> PartialComparison
partialOfTotal = \case
  EQ -> PosetEQ
  LT -> PosetLE
  GT -> PosetGE

mergeValues :: IntMap a -> IntMap b -> (a -> c) -> (b -> c) -> (a -> b -> c) -> IntMap c
mergeValues m1 m2 l r b =
  mergeWithKeys m1 m2 (const l) (const r) (const b)

mergeBoth :: IntMap a -> IntMap b -> c -> (a -> b -> c) -> IntMap c
mergeBoth m1 m2 df both = mergeValues m1 m2 (const df) (const df) both

mergeWithKeys :: IntMap a -> IntMap b -> (Int -> a -> c) -> (Int -> b -> c) -> (Int -> a -> b -> c) -> IntMap c
mergeWithKeys m1 m2 l r b = IntMapMerge.merge
  (IntMapMerge.mapMissing l)
  (IntMapMerge.mapMissing r)
  (IntMapMerge.zipWithMatched b)
  m1 m2

mergeZip :: IntMap a -> IntMap b -> IntMap (a, b)
mergeZip = IntMapMerge.merge
  IntMapMerge.dropMissing
  IntMapMerge.dropMissing
  (IntMapMerge.zipWithMatched (const (,)))

-- O(w)
lattice :: Lattice -> Lattice -> PartialComparison
lattice l1 l2 = fold $ mergeValues l1 l2
  (const PosetLE)
  (const PosetGE)
  \x y -> partialOfTotal (compare x y)

-- O(w)
(<=?) :: Lattice -> Lattice -> Bool
l1 <=? l2 = case lattice l1 l2 of
  PosetEQ -> True
  PosetLE -> True
  _ -> False


solverState :: Solver -> [(Var, [Int])]
solverState (Solver { points, vars }) =
  let
    spread :: Set.Set Chain -> Map.Map Chain Int
    spread = Map.fromDescList . flip zip [1..] . Set.toDescList
    pointsSpread :: DimMap (Map.Map Chain Int)
    pointsSpread = spread <$> points
    dimensions :: [Dim]
    dimensions = IntMap.keys points

    latticePoint latticeValues =
      dimensions <&> \dim -> fromMaybe 0 do
        dimSpread <- IntMap.lookup dim pointsSpread
        dimValue <- IntMap.lookup dim latticeValues
        pointValue <- Map.lookup dimValue dimSpread
        pure pointValue
  in IntMap.toAscList vars <&> \(v, pt) -> (v, latticePoint pt)


demonstrate :: Solver -> IntMap Int
demonstrate (Solver { points, vars }) =
  let
    spread :: Set.Set Chain -> Map.Map Chain Int
    spread = Map.fromAscList . flip zip [0..] . Set.toAscList
    pointsSpread :: IntMap (Map.Map Chain Int)
    pointsSpread = spread <$> points
    topGrade = fromMaybe 0 $ maximumMay $ fromMaybe 0 . maximumMay <$> pointsSpread
    mapPoint dimension alongChain = (pointsSpread IntMap.! dimension) Map.! alongChain
    gradeLattice :: Lattice -> Int
    gradeLattice latticeValues = sum $ -- fromMaybe topGrade $ maximumMay $
      IntMap.mapWithKey mapPoint latticeValues
  in gradeLattice <$> vars

-- O(w*v + w*A) worst case, but hopefully most operations are <=O(w*log)
relate :: (Fresh, Relation, Fresh) -> Solver -> Maybe Solver
relate (Fresh v1, rel, Fresh v2) solver | v1 == v2 =
  if rel == LessThan then Nothing else Just solver
relate (Fresh v1, rel, Fresh v2) solver@(Solver { ctr, vars }) =
  case (IntMap.lookup v1 vars, IntMap.lookup v2 vars) of
    (Nothing, Nothing) -> Just $ case rel of
      Equal ->
        -- Might as well insert them with the same dimension `ctr`
        solver { ctr = ctr + 1, vars = IntMap.insert v1 (ctr @! 0) $ IntMap.insert v2 (ctr @! 0) vars }
      _ -> _apartIfRel rel v1 v2 $ newVarBelow v1 (ctr @! 0) $ newVar v2 solver
    (Nothing, Just upper) -> case rel of
      Equal -> Just $ solver { vars = IntMap.insert v1 upper vars }
      -- This is potentially much cheaper than the symmetric `insertAbove`
      _ -> Just $ _apartIfRel rel v1 v2 $ newVarBelow v1 upper solver
    (Just lower, Nothing) -> case rel of
      Equal -> Just $ solver { vars = IntMap.insert v1 lower vars }
      -- This is potentially expensive, if there is no degree of freedom
      -- where it can be inserted without altering other relationships
      _ -> Just $ _apartIfRel rel v1 v2 $ insertAbove lower v2 solver
    (Just lower, Just upper) -> case (lattice lower upper, rel) of
      (PosetEQ, LessThan) -> Nothing
      (PosetEQ, _) -> Just solver
      (PosetLE, LessThan) -> Just $ _apart v1 v2 solver
      (PosetLE, LessThanEqual) -> Just solver
      (PosetGE, LessThan) -> Nothing
      -- squish several points on the lattice together: O(w*v + w*A)
      (PosetGE, _) -> squish (upper {- erm, lower -}) (lower {- currently upper -}) $ lower `tuckUnder` upper $ solver
      -- ?
      (PosetUN, Equal) -> squish lower upper $ upper `tuckUnder` lower $ lower `tuckUnder` upper $ solver
      (_, Equal) -> squish lower upper solver
      -- edit the lower one to be below the upper one: O(w*v)
      (PosetUN, _) -> Just $ _apartIfRel rel v1 v2 $ lower `tuckUnder` upper $ solver

lookup :: Fresh -> Solver -> Maybe Lattice
lookup (Fresh v) = IntMap.lookup v . vars

compareIn :: (Fresh, Fresh) -> Solver -> Maybe (Lattice, PartialComparison, Lattice)
compareIn (v1, v2) solver = do
  x <- lookup v1 solver
  y <- lookup v2 solver
  pure (x, lattice x y, y)

insert :: (Fresh, Relation, Fresh, Relation, Fresh) -> Solver -> Maybe Solver
insert (Fresh v1, r12, Fresh v2, r23, Fresh v3) solver@(Solver { vars }) =
  case (IntMap.lookup v1 vars, IntMap.lookup v2 vars, IntMap.lookup v3 vars) of
    (Just lower, Nothing, Just upper)
      | r12 /= Equal, r23 /= Equal, lower <=? upper ->
        -- The rare opportunity to try to insert it along an existing chain
        Just $ _apartIfRel r12 v1 v2 $ _apartIfRel r23 v2 v3 $
          insertBetween lower v2 upper solver
    _ -> do
      -- Do the upper relation first, so we do not have to shift the lower relation
      solver' <- relate (Fresh v2, r23, Fresh v3) solver
      solver'' <- relate (Fresh v1, r12, Fresh v2) solver'
      pure solver''

type SquishCmd = (Chain, Maybe Chain)

squishCmds :: Lattice -> Lattice -> DimMap SquishCmd
squishCmds = IntMapMerge.merge
  (IntMapMerge.mapMissing (const (,Nothing)))
  (IntMapMerge.mapMissing (const (,Nothing)))
  $ IntMapMerge.zipWithMaybeMatched \_ x y ->
    case compare x y of
      EQ -> Nothing -- Already squished!
      LT -> Just (x, Just y)
      GT -> Just (y, Just x)

squishCmd :: SquishCmd -> (Chain -> Maybe Chain)
squishCmd (bound, Nothing) point
  | point >= bound = Nothing -- to infinity! (but not beyond)
  | otherwise = Just point
squishCmd (lower, Just upper) point
  | lower <= point && point <= upper = Just upper
  | otherwise = Just point

squishLattice :: DimMap SquishCmd -> Lattice -> Lattice
squishLattice = IntMapMerge.merge
  (IntMapMerge.dropMissing :: IntMapMerge.SimpleWhenMissing SquishCmd Chain)
  (IntMapMerge.mapMissing (const id))
  $ IntMapMerge.zipWithMaybeMatched (const squishCmd)

squishPoints :: DimMap SquishCmd -> DimMap (Set.Set Chain) -> DimMap (Set.Set Chain)
squishPoints = IntMapMerge.merge
  (IntMapMerge.dropMissing :: IntMapMerge.SimpleWhenMissing SquishCmd (Set.Set Chain))
  (IntMapMerge.mapMissing (const id))
  $ IntMapMerge.zipWithMaybeMatched $ const \cmd points ->
    let updated = Set.fromList $ mapMaybe (squishCmd cmd) $ Set.toList points
    in if Set.null updated then Nothing else Just updated

-- O(w*v)
-- squish :: Lattice -> Lattice -> Solver -> Maybe Solver
-- squish loc1 loc2 solver =
--   checkAparts $ solver
--     { points = IntMap.foldr' (\pt -> IntMap.unionWith (<>) $ Set.singleton <$> pt) IntMap.empty vars' -- squishPoints dimensions (points solver)
--     , vars = vars'
--     }
--   where
--   vars' = (\pt -> if pt <=? loc2 || pt <=? loc1 then squishLattice dimensions pt else pt) <$> vars solver
--   dimensions = squishCmds loc1 loc2

squish :: Lattice -> Lattice -> Solver -> Maybe Solver
squish loc1 loc2 solver = checkAparts $ solver
  { points = IntMap.foldr' (\pt -> IntMap.unionWith (<>) $ Set.singleton <$> pt) IntMap.empty vars'
  , vars = vars'
  }
  where
  -- O(w)
  vars' = (\pt -> if loc1 <=? pt && pt <=? loc2 || loc2 <=? pt && pt <=? loc1 then loc1 else pt) <$> vars solver

-- O(w*A)
checkAparts :: Solver -> Maybe Solver
checkAparts solver = if stillApart solver then Just solver else Nothing

stillApart :: Solver -> Bool
stillApart solver =
  mergeZip (aparts solver) (vars solver)
  & all \(apartFromHere, here) ->
    mergeZip (set2Map apartFromHere) (vars solver)
    & all \((), there) ->
      case lattice here there of
        PosetEQ -> False
        _ -> True
  where
  set2Map apartFromHere =
    IntMap.fromDistinctAscList ((,()) <$> IntSet.toAscList apartFromHere)

-- This takes care of transitivity, at the expense of having to move all the
-- points below `lower`, thus it is fully O(w*v) since we do not maintain
-- a cache of those points by dimension or grade or anything...
tuckUnder :: Lattice -> Lattice -> Solver -> Solver
tuckUnder lower upper solver = solver' { vars = tucking <$> vars solver' }
  where
  -- O(w)
  tucking position = if position <=? lower then
    IntMap.unionWith min position limit else position
  (solver', limit) = below upper solver

-- O(w*log)
below :: Lattice -> Solver -> (Solver, Lattice)
below !upper solver =
  chainInsertion belowChain {- O(log) -} (newDimBelow upper solver) upper solver


chainInsertion ::
  (Chain -> Set.Set Chain -> Maybe Chain) ->
  (Solver, Lattice) -> Lattice -> Solver -> (Solver, Lattice)
chainInsertion method fallback reference solver =
  -- Add a new dimension if we cannot find a chain with free space below it
  IntMap.foldrWithKey (&) fallback $
    -- Try to find a way to insert into an existing dimension,
    -- if the dimension's chain (set of points) has space below it
    mergeBoth reference (points solver) (const id) findInsertion
  where
  findInsertion :: Chain -> Set.Set Chain -> Dim -> (Solver, Lattice) -> (Solver, Lattice)
  findInsertion point chain dim keepTrying =
    case method point chain of
      Nothing -> keepTrying
      Just newPoint ->
        ( solver { points = IntMap.adjust (Set.insert newPoint) dim (points solver) }
        , IntMap.insert dim newPoint reference
        )

-- O(w*log) fast path, O(w*v) slow path
insertAbove :: Lattice -> Var -> Solver -> Solver
insertAbove !lower !v solver =
  setVar v $ fallback -- chainInsertion aboveChain fallback lower solver
  where
  fallback =
    let (solver', upper) = newDim solver in
    (lower `tuckUnder` upper $ solver', upper)

insertBetween :: Lattice -> Var -> Lattice -> Solver -> Solver
insertBetween !lower v !upper solver =
  case chainInsertion' betweenChain (mergeZip lower upper) solver of
    Just (solver', (dim, newPoint, _)) ->
      setVar v (solver', IntMap.insert dim newPoint upper)
    Nothing -> setVar v $ newDimBelow upper solver

chainInsertion' :: forall a.
  (a -> Set.Set Chain -> Maybe Chain) ->
  IntMap a ->
  Solver ->
  Maybe (Solver, (IntSet.Key, Chain, IntMap a))
chainInsertion' method reference solver =
  -- Add a new dimension if we cannot find a chain with free space below it
  IntMap.foldrWithKey (&) Nothing $
    -- Try to find a way to insert into an existing dimension,
    -- if the dimension's chain (set of points) has space below it
    mergeBoth reference (points solver) (const id) findInsertion
  where
  findInsertion :: a -> Set.Set Chain -> Dim -> Maybe (Solver, (IntSet.Key, Chain, IntMap a)) -> Maybe (Solver, (IntSet.Key, Chain, IntMap a))
  findInsertion point chain dim keepTrying =
    case method point chain of
      Nothing -> keepTrying
      Just newPoint -> Just
        ( solver { points = IntMap.adjust (Set.insert newPoint) dim (points solver) }
        , (dim, newPoint, reference)
        )




data Health = HealthReport
  { missingChainPoints :: IntMap (Set.Set Chain)
  , excessChainPoints :: IntMap (Set.Set Chain)
  , dimensions :: Int
  , width :: Int
  , chainLength :: Int
  }

checkHealth :: Solver -> Health
checkHealth (Solver { points, vars }) = HealthReport
  { missingChainPoints =
      IntMap.differenceWith
        (\x y -> let z = Set.difference x y in if Set.null z then Nothing else Just z)
        allPoints points
  , excessChainPoints =
      IntMap.differenceWith
        (\x y -> let z = Set.difference x y in if Set.null z then Nothing else Just z)
        points allPoints
  , dimensions = IntMap.size allPoints
  , width = fromMaybe 0 $ maximumMay $ IntMap.size <$> vars
  , chainLength = fromMaybe 0 $ maximumMay $ Set.size <$> allPoints
  }
  where
  allPoints :: DimMap (Set.Set Chain)
  allPoints = IntMap.foldr' (\pt -> IntMap.unionWith (<>) $ Set.singleton <$> pt) IntMap.empty vars

