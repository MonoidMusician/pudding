-- A solver for universe levels via semigroups, based on the technique I wrote
-- about on my blog: https://blog.veritates.love/version_solver.html
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Eta reduce" #-}
module Pudding.Semantics.Universes where

import Data.Function ((&))
import Data.Functor ((<&>))
import Data.IntMap.Monoidal.Strict (MonoidalIntMap)
import Data.List.NonEmpty (NonEmpty)
import Pudding.Types (Fresh (Fresh))
import qualified Data.IntMap.Monoidal.Strict as Map
import qualified Data.List.NonEmpty as NEL
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import qualified Data.IntMap.Strict as IntMap
import Data.Coerce (coerce)
import Data.Maybe (fromMaybe)

-- The goal is to maintain a state monoid of the current universe level
-- constraints. These constraints are proof-relevant in the sense that we keep
-- evidence for how the constraints came about: source locations if they occur
-- from specific places in the source, cumulated transitively in a chain `evData`.
--
-- You can think of it as a database of facts. It maintains maps from each
-- universe level variable to all *larger* universe level variables, with
-- a record of the shortest *evidence* provided for their relationship:
-- whatever metadata carried by `meta` exists along the shortest path
-- between variables. This is useful for displaying errors to the user.
--
-- Semantically it trying to model a finite poset, until it fails to be a poset,
-- at which point it keeps adding constraints anyways, tracking inconsistencies.
--
-- We always keep it saturated, using transitivity and other properties to
-- derive additional fact. This ensures that if there is an inconsistency, it
-- is in the map, avoiding having to retraverse chains to check for consistency.
--
-- This is a total monoid: we remember inconsistencies instead of blowing up.
-- In fact, it is the only monoid: everything below is just a semigroup. Having
-- it as a monoid makes plumbing it everywhere in the typechecker much much
-- easier, but it still needs to be checked for consistency before evaluation.
-- It is not quite commutative: the left side is meant to be the “older”
-- constraints that we will lightly prefer in case there is no other deciding
-- factor (length of the chain of evidence is the most important).
data Constraints meta = Constraints
  (Maybe (InconsistentRelationship meta))
  -- ^ lazy(?), a best-effort tracking of an inconsistency that occurred
  !(MonoidalIntMap (MonoidalIntMap (Related meta)))
  -- ^ the map of constraints: lower => upper => relationship
  deriving (Functor, Foldable, Traversable, Generic, NFData)
type ConstraintMap meta = MonoidalIntMap (MonoidalIntMap (Related meta))

-- A poset with `LessThanEqual < LessThan` and `LessThanEqual < Equal`
-- (in order to model the relationships in our poset model :3)
data Relation = LessThanEqual | LessThan | Equal
  deriving (Eq, Ord, Generic, Show, NFData)

-- The chain of evidence gathered during transitive relationships: it always
-- prefers the shorter path, and takes the left one if they are equal.
data Evidence meta = Evidence
  { evLength :: !Int
  , evData :: NonEmpty meta -- lazy
    -- ^ the head is the largest relation so far, the tail is the inequality from
    -- the base key
  , evHeat :: !Int
    -- ^ a measure of how many times it has been touched: if you are looking for
    -- an accidentally introduced constraint, it is probably one with low heat.
    -- this compensates for discarding `evData` when possible, but it is not
    -- exactly a semantic measure
  } deriving (Functor, Foldable, Traversable, Generic, Show, NFData)
-- Ignore `evHeat` for comparisons
instance Eq meta => Eq (Evidence meta) where
  ev1 == ev2 = evLength ev1 == evLength ev2 && evData ev1 == evData ev2
instance Ord meta => Ord (Evidence meta) where
  ev1 `compare` ev2 = evLength ev1 `compare` evLength ev2 <> evData ev1 `compare` evData ev2
instance Semigroup (Evidence meta) where
  ev1 <> ev2 =
    -- If the second is shorter, take it. Otherwise try to preserve older
    -- evidence.
    (if evLength ev2 < evLength ev1 then ev2 else ev1)
      { evHeat = evHeat ev1 + evHeat ev2 }

-- The matter of the relationship between the variables: ideally it is
-- less than or equal to the next variable, but if there is an inconsistency,
-- we will track that.
data Related meta
  = Related !Relation !(Evidence meta)
  | Inconsistent !(Inconsistency meta)
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic, Show, NFData)
-- There are two types of inconsistencies:
-- - If there is a cycle, add at least one of those is a strict inequality,
--   then we record that as `InconsistentLTGT`
-- - If `Equal` constraints are allowed to be added, then `InconsistentLTEQ`
--   can also result.
data Inconsistency meta
  -- `InconsistentLTGT`
  = InconsistentLTGT !(Evidence meta {- LT -}) !(Evidence meta {- GT -})
  -- `InconsistentLTEQ` from summing `Related Equal` and `Related LessThan`
  | InconsistentLTEQ !(Evidence meta {- LT -}) !(Evidence meta {- EQ -})
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic, Show, NFData)

-- This is the `Semigroup` for two relations *between the same nodes*.
-- There is a different `Semigroup` for the transitivity of relations!! But that
-- one is less important: it only occurs in `generate`
instance Semigroup (Related meta) where
  -- On the diagonal (= when the relations are equal), we take the one with
  -- shorter length, and add heat measures
  Related LessThanEqual ev1 <> Related LessThanEqual ev2 =
    Related LessThanEqual (ev1 <> ev2)
  Related LessThan ev1 <> Related LessThan ev2 =
    Related LessThan (ev1 <> ev2)
  Related Equal ev1 <> Related Equal ev2 =
    Related Equal (ev1 <> ev2)
  -- `LessThanEqual` is the weakest relation, so we take the evidence from the
  -- stronger relation
  Related LessThanEqual ev1 <> Related rel ev2 =
    Related rel ev2 { evHeat = evHeat ev1 + evHeat ev2 }
  Related rel ev1 <> Related LessThanEqual ev2 =
    Related rel ev2 { evHeat = evHeat ev1 + evHeat ev2 }
  -- Otherwise we have an inconsistency: inconsistencies here are of the form
  -- `InconsistentLTEQ`: strictly less than and also equal to, with evidence
  -- in that order
  Related LessThan evLT <> Related Equal evEQ = Inconsistent $ InconsistentLTEQ evLT evEQ
  Related Equal evEQ <> Related LessThan evLT = Inconsistent $ InconsistentLTEQ evLT evEQ
  -- Inconsistencies have their own semigroup
  Inconsistent i1 <> Inconsistent i2 = Inconsistent (i1 <> i2)
  -- Otherwise ignore new evidence that comes in
  r@(Inconsistent _) <> Related _ _ = r
  Related _ _ <> r@(Inconsistent _) = r
instance Semigroup (Inconsistency meta) where
  InconsistentLTGT evLT1 evGT1 <> InconsistentLTGT evLT2 evGT2 =
    InconsistentLTGT (evLT1 <> evLT2) (evGT1 <> evGT2)
  -- prefer `InconsistentLTGT` over `InconsistentLTEQ`?
  r@(InconsistentLTGT _ _) <> InconsistentLTEQ _ _ = r
  InconsistentLTEQ _ _ <> r@(InconsistentLTGT _ _) = r
  InconsistentLTEQ evLT1 evEQ1 <> InconsistentLTEQ evLT2 evEQ2 =
    InconsistentLTEQ (evLT1 <> evLT2) (evEQ1 <> evEQ2)

-- TODO: quickcheck that `Related rel _ <- Related r1 _ <> Related r2` obeys
-- monotonicity of `Relation`


-- Two variables are put in a relationship, with some associated metadata
type Relationship meta = (Fresh, Relation, Fresh, meta)

-- We can turn this relationship into a singleton constraint mapping
constraint :: Relationship meta -> Constraints meta
constraint (Fresh lower, rel, Fresh upper, meta) =
  case rel of
    _ | lower /= upper -> Constraints Nothing $ (<>)
      do Map.singleton upper Map.empty
      do Map.singleton lower $ Map.singleton upper $ Related rel evidence
    LessThan ->
      let inco = InconsistentLTEQ evidence evidence in
      Constraints (Just (IncoRel (Fresh lower) inco (Fresh upper))) $
        Map.singleton lower $ Map.singleton upper $ Inconsistent inco
    _ -> mempty
  where
  evidence = Evidence
    { evLength = 1 -- there is one relationship in the chain
    , evData = NEL.singleton meta -- with this metadata
    , evHeat = 1 -- it has appeared once now
    }
touch :: Fresh -> meta -> Constraints meta
touch var meta = constraint (var, Equal, var, meta)

data InconsistentRelationship meta = IncoRel !Fresh !(Inconsistency meta) !Fresh
  deriving (Functor, Foldable, Traversable, Eq, Ord, Generic, Show, NFData)
instance Semigroup (InconsistentRelationship meta) where
  -- Attempt to obtain a canonical inconsistency: smallest length, smallest
  -- variables (in lexicographic order), or prefer the leftmost one
  i1@(IncoRel lower1 inco1 upper1) <> i2@(IncoRel lower2 inco2 upper2)
    -- Same endpoints: merge their inconsistency to get the shortest one
    | (lower1, upper1) == (lower2, upper2) = IncoRel lower1 (inco1 <> inco2) upper1
    | otherwise = case (inco1, inco2) of
      -- Prefer `InconsistentLTGT` somewhat arbitrarily
      (InconsistentLTGT _ _, InconsistentLTEQ _ _) -> i1
      (InconsistentLTEQ _ _, InconsistentLTGT _ _) -> i2
      -- Remember, these are different endpoints now, but they both have cycles
      -- (they may be part of the same cycle, even)
      (InconsistentLTGT evLT1 evGT1, InconsistentLTGT evLT2 evGT2) ->
        let
          -- Compare the length of the cycle first
          c1 = (evLength evLT1 + evLength evGT1) `compare` (evLength evLT2 + evLength evGT2)
          -- Then do lexicographic order, arbitrarily
          c2 = (lower1, upper1) `compare` (lower2, upper2)
        in case c1 <> c2 of
          LT -> i1
          GT -> i2
          EQ -> i1 -- left biased
      (InconsistentLTEQ evLT1 evEQ1, InconsistentLTEQ evLT2 evEQ2) ->
        let
          c1 = evLength evEQ1 `compare` evLength evEQ2
          c2 = evLength evLT1 `compare` evLength evLT2
          c3 = (lower1, upper1) `compare` (lower2, upper2)
        in case c1 <> c2 <> c3 of
          LT -> i1
          GT -> i2
          EQ -> i1 -- left biased


-- We can look for inconsistencies in the end
searchForInconsistency :: ConstraintMap meta -> Maybe (InconsistentRelationship meta)
searchForInconsistency relationships =
  relationships & Map.foldMapWithKey \lower -> Map.foldMapWithKey \upper relatedBy ->
    case relatedBy of
      Inconsistent inco -> Just $ IncoRel (Fresh lower) inco (Fresh upper)
      _ -> Nothing

-- `saturate` builds on `oppositivize` and `transitivize1` to add all of the
-- implied constraints. We keep `ConstraintMap` in this maximal form to make it
-- easy to check for inconsistencies, otherwise that work would essentially
-- need to be duplicated each time.
saturate :: ConstraintMap meta -> ConstraintMap meta
saturate relationships =
  let
    -- This amends the map directly, filling in information from backwards
    -- relationships: e.g. if `a <= b` and `b <= a` then `a = b`
    amended = oppositivize relationships
    -- This returns a map of only the necessary amendments, things learned from
    -- transitivity (`a <= b` and `b < c` then `a < c`) that were not present
    learned = transitivize1 amended
    -- Merge the maps directly, since we do not need to recalculate the monoid
    -- appends on `Related meta` that we already calculated in `transitivize1`
    rightBias :: Related meta -> Related meta -> Related meta
    rightBias _ fromLearned = fromLearned
    merged = Map.unionWith (Map.unionWith rightBias) amended learned
  in if Map.null learned
    then amended {- le fin -}
    else saturate merged {- recurse -}

restrict :: MonoidalIntMap x -> (meta -> meta') -> Constraints meta -> Constraints meta'
restrict to mapping (Constraints inco relationships) = Constraints (fmap mapping <$> inco) $
  Map.intersectionWith (const $ Map.intersectionWith (const (fmap mapping)) to) to relationships

instantiate :: (Fresh -> Fresh) -> (meta -> meta') -> Constraints meta -> Constraints meta'
instantiate var mapping (Constraints inco relationships) = Constraints
  do inco <&> \(IncoRel x r y) -> IncoRel (var x) (mapping <$> r) (var y)
  do Map.mapKeys (coerce var) $ Map.mapKeys (coerce var) . fmap (fmap mapping) <$> relationships

-- Instantiate with fresh variables
freshen :: Fresh -> (meta -> meta') -> Constraints meta -> (Fresh, Constraints meta')
freshen (Fresh start) mapping (Constraints inco relationships) = (Fresh maxFresh,) $ Constraints
  do inco <&> \(IncoRel x r y) -> IncoRel (coerce var x) (mapping <$> r) (coerce var y)
  do Map.mapKeysMonotonic var $ Map.mapKeysMonotonic var . fmap (fmap mapping) <$> relationships
  where
  (maxFresh, freshened) = Map.mapAccum (\(!here) _ -> (here + 1, here)) start relationships
  var i = fromMaybe i $ Map.lookup i freshened

demonstrate :: Constraints meta -> (Fresh -> Int)
demonstrate (Constraints _ relationshipsLTEI) =
  \(Fresh var) -> fromMaybe 99 $ Map.lookup var assigned
  where
  -- Flip it around, so it is a map of greater to lesser
  relationshipsGT = relationshipsLTEI & Map.foldMapWithKey \lower ->
    Map.mapMaybe \case
      -- This only makes sense on a saturated map where we don't lose LTE constraints
      Related LessThan _ -> Just $ Map.singleton lower ()
      _ -> Nothing
  assigned = loop Map.empty 0 $
    relationshipsGT <> (Map.empty <$ relationshipsLTEI)
  loop !acc !depth !left =
    let (layer, remaining) = Map.partition Map.null left in
    let trimmed = flip Map.difference layer <$> remaining in
    let acc' = Map.unionWith const acc (depth <$ layer) in
    if Map.null layer then acc' else loop acc' (depth + 1) trimmed

uvars :: Constraints meta -> [Fresh]
uvars (Constraints _ rels)  = coerce $ Map.keys rels

--------------------------------------------------------------------------------
-- Transitivity: Fill out the constraints with transitive relationships       --
--------------------------------------------------------------------------------

check :: Monoid m => Bool -> m -> m
check True m = m
check False _ = mempty

-- Return generated constraints that are implied from direct transitivity on
-- the set of existing ones. This operates by `foldMap`ping over the *entire*
-- structure, almost twice: if `(lower, mid)` is in the map then we lookup
-- `mid` to find uppers for `(lower, upper)`. This does not care if the
-- evidence it finds is in the map already: we handle that separately.
--
-- Note: we `foldMap` on `ConstraintMap`: we do not want to be recursively
-- transitivizing these as `Constraints`!
--
-- O(n^3)-ish
transitivize1 :: ConstraintMap meta -> ConstraintMap meta
transitivize1 existing =
  -- Get a pair (lower, relationLowerMid, mid)
  existing & Map.foldMapWithKey \lower aboveLower ->
    aboveLower & Map.foldMapWithKey \mid relationLowerMid ->
      -- Look it up to find pairs (mid, relationMidUpper, upper)
      Map.lookup mid existing & foldMap \aboveMid ->
        aboveMid & Map.foldMapWithKey \upper relationMidUpper ->
          -- Calculate the transitive relation
          transitive relationLowerMid relationMidUpper & foldMap \relationLowerUpper ->
            -- Do a lookup to check that it would contribute something
            learns relationLowerUpper (Map.lookup upper aboveLower) & foldMap \learned ->
              -- Introduce this relation to the constraint map
              Map.singleton lower $ Map.singleton upper learned

transitive :: Related meta -> Related meta -> Maybe (Related meta)
-- We only care about equal constraints when they are both equal:
-- transitivity of equality, we might find a shorter path
transitive (Related Equal ev1) (Related Equal ev2) = Just $ Related Equal (ev1 <> ev2)
-- Otherwise equality serves as an identity: just drop them
transitive (Related Equal _) r = Just r
transitive r (Related Equal _) = Just r
-- The relation stays as LessThanEqual only if both are
transitive (Related LessThanEqual ev1) (Related LessThanEqual ev2) =
  Just $ Related LessThanEqual (transitiveEvidence ev1 ev2)
-- Otherwise it strictifies to LessThan
transitive (Related _ ev1) (Related _ ev2) =
  Just $ Related LessThan  (transitiveEvidence ev1 ev2)
-- If one relation is already inconsistent, we just do not care?
transitive (Inconsistent _) _ = Nothing
transitive _ (Inconsistent _) = Nothing

-- Concatenate the evidence, adding lengths, instead of preferring the shorter.
transitiveEvidence :: Evidence meta -> Evidence meta -> Evidence meta
transitiveEvidence evLower evUpper = Evidence
  { evLength = evLength evLower + evLength evUpper
  , evData = evData evUpper <> evData evLower -- upper is the head, lower is the tail
  , evHeat = evLength evLower `max` evLength evUpper -- seems reasonable? idk
  }

-- `learns newInfo existing`: kind of like `Just newInfo <> existing /= existing`
learns :: Related meta -> Maybe (Related meta) -> Maybe (Related meta)
learns newInfo Nothing = Just newInfo
learns newInfo@(Related _ _) (Just existed@(Related r2 ev2)) = case newInfo <> existed of
  learned@(Related r3 ev3)
    | r3 /= r2 -> Just learned
    | evLength ev3 /= evLength ev2 -> Just learned
    | otherwise -> Nothing
  learned@(Inconsistent _) -> Just learned
-- no sense optimizing inconsistencies
learns l@(Inconsistent _) (Just r@(Related _ _)) = Just (l <> r)
-- just a bit of care, to check that we have not reached a fixedpoint
learns l (Just (Inconsistent r)) =
  let learned = l <> Inconsistent r in
  let haveLearned b = if b then Just learned else Nothing in
  haveLearned
    case (learned, r) of
      (Related _ _, _) -> error "nope"
      (Inconsistent (InconsistentLTGT _ _), InconsistentLTEQ _ _) -> True
      (Inconsistent (InconsistentLTEQ _ _), InconsistentLTGT _ _) -> True
      (Inconsistent (InconsistentLTGT m n), InconsistentLTGT o p) ->
        evLength m /= evLength o || evLength n /= evLength p
      (Inconsistent (InconsistentLTEQ m n), InconsistentLTEQ o p) ->
        evLength m /= evLength o || evLength n /= evLength p

--------------------------------------------------------------------------------
-- Opposites: Reverse EQ relations, check for LTGT inconsistencies            --
--------------------------------------------------------------------------------

-- O(n^2)-ish
oppositivize :: ConstraintMap meta -> ConstraintMap meta
oppositivize existing =
  Map.foldlWithKey outer existing existing
  where
  outer !acc lower aboveLower = Map.foldlWithKey (inner lower) acc aboveLower
  inner lower !acc upper relation =
    let addOpposite aboveUpper = Map.alter (oppositive relation) lower aboveUpper
    in Map.adjust addOpposite upper acc

-- `x R y` and `y R x` to `y R x`
oppositive :: Related meta -> Maybe (Related meta) -> Maybe (Related meta)
-- If `a = b` and `b = a`, then, well, `b = a`
oppositive (Related Equal ev1) existing@(Just (Related Equal ev2)) =
  -- But we only prefer it if it has shorter evidence, otherwise it is old news
  if evLength ev1 < evLength ev2 then
    Just $ Related Equal $ opEv ev1
  else existing
-- If `a = b` and `b <= a`, then we strengthen it to `b = a`
oppositive (Related Equal ev1) (Just (Related LessThanEqual _)) =
  Just $ Related Equal $ opEv ev1
-- If `a = b`, then we learn that `b = a`
oppositive (Related Equal ev1) Nothing = Just $ Related Equal $ opEv ev1
-- If `a = b` but `b < a`, then we have a LTEQ inconsistency
oppositive (Related Equal evEQ) (Just (Related LessThan evLT)) =
  Just $ Inconsistent $ InconsistentLTEQ evLT $ opEv evEQ
-- Vice-versa: if `a < b` but `b = a`
oppositive (Related LessThan evGT) (Just (Related Equal evEQ)) =
  Just $ Inconsistent $ InconsistentLTEQ (opEv evGT) evEQ
-- If `a <= b` and `b < a` then we have a LTGT inconsistency
oppositive (Related _ evGTE) (Just (Related LessThan evLT)) =
  Just $ Inconsistent $ InconsistentLTGT evLT $ opEv evGTE
-- If `a <= b` and `b <= a`, then `a = b`
oppositive (Related LessThanEqual evGTE) (Just (Related LessThanEqual evLTE)) =
  Just $ Related Equal $ evLTE <> opEv evGTE
-- Otherwise we learn nothing from `a <= b`
oppositive (Related _ _) existing = existing
-- We reflect LTGT inconsistencies
oppositive (Inconsistent (InconsistentLTGT evLT evGT)) existing =
  let
    learning = Inconsistent (InconsistentLTGT (opEv evGT) (opEv evLT))
  in Just case existing of
    Nothing -> learning
    Just existed -> learning <> existed
-- And do nothing with LTEQ inconsistencies
oppositive (Inconsistent (InconsistentLTEQ _ _)) existing = existing

-- Opposite evidence: reverse the data chain
opEv :: Evidence meta -> Evidence meta
opEv ev = ev { evData = NEL.reverse (evData ev) }

instance Monoid (Constraints meta) where
  mempty = Constraints mempty mempty

instance Semigroup (Constraints meta) where
  Constraints i1 m1 <> Constraints i2 m2
    | IntMap.disjoint (Map.getMonoidalIntMap m1) (Map.getMonoidalIntMap m2) =
      -- Quick append for disjoint universes
      Constraints (i1 <> i2) (m1 <> m2)
  Constraints _ m1 <> Constraints _ m2 =
    let m3 = saturate (m1 <> m2) in
    -- Since this is lazy, and we are not optimizing for having inconsistencies,
    -- it is best to search for an inconsistency as late as possible
    Constraints (searchForInconsistency m3) m3
