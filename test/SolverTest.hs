{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Evaluate" #-}
module SolverTest (solverTest) where

import Control.Monad.IO.Class (liftIO)

import Testing
import Data.Foldable (for_)
import Control.DeepSeq (force, NFData)
import Pudding.Types (Fresh(..))
import Pudding.Semantics.Universes
import GHC.IO (evaluate)
import Data.Maybe (isNothing)
import GHC.Generics (Generic)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NEL
import qualified GHC.Base as GHC
import qualified Hedgehog as HG
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog (Gen, (===))

data Ev = Ev Fresh Relation Fresh
  deriving (Eq, Ord, Generic, NFData)

relate :: Relation -> String
relate = \case
  LessThan -> "<"
  LessThanEqual -> "<="
  Equal -> "="

class (Show ev) => ShowEvidence ev where
  showEvidence :: NonEmpty ev -> String
instance ShowEvidence Ev where
  showEvidence (least :| []) = show least
  showEvidence (_greater@(Ev (Fresh l) r (Fresh u)) :| lesser@(Ev (Fresh next) _ _) : more) | u == next =
    step <> showEvidence (lesser :| more)
    where
    step = mconcat [ "v", show l, " ", relate r, " " ]
  showEvidence (step :| x : xs) =
    show step <> "  χ  " <> showEvidence (x :| xs)


instance Show Ev where
  show (Ev (Fresh x) rel (Fresh y)) = mconcat
    [ "v", show x, " "
    , relate rel
    , " v", show y
    ]

lt :: Fresh -> Fresh -> Relationship Ev
lt x y = (x, LessThan, y, Ev x LessThan y)
le :: Fresh -> Fresh -> Relationship Ev
le x y = (x, LessThanEqual, y, Ev x LessThanEqual y)

endpoints :: Evidence Ev -> (Fresh, Fresh)
endpoints ev =
  case (NEL.head (evData ev), NEL.last (evData ev)) of
    (Ev x _ _, Ev _ _ y) -> (x, y)

solverTest :: TestSuite
solverTest = TestSuite "SolverTest" do
  let
    v = Fresh
    v0 = v 0
    v1 = v 1
    v2 = v 2
  testCase "Consistent" do
    testCase "Samples" do
      let
        setups =
          [ [v0 `lt` v1]
          , [v0 `lt` v1, v1 `le` v2]
          , [v0 `le` v1, v1 `le` v2]
          ]
      for_ setups \setup -> do
        consistent =<< solve setup
  testCase "Inconsistent" do
    testCase "Samples" do
      let
        setups =
          [ [v0 `lt` v1, v1 `le` v0]
          , [v0 `lt` v1, v1 `le` v2, v2 `lt` v0]
          , [v0 `lt` v1, v1 `le` v2, v2 `le` v 3, v 3 `le` v 4, v 4 `lt` v0]
          ]
      for_ setups \setup -> do
        inconsistent =<< solve setup
  testCase "Properties" do
    let
      constraints (Constraints _ m) = m
      constraintsEq x y = constraints x === constraints y
      hedgeTest num name f = testCase name do
        HG.check $ HG.withTests num $ HG.property f
      onRandomConstraints num name fixed f =
        hedgeTest (maybe num (const 1) fixed) name $
          f =<< randomConstraints fixed
      checkEvidence (_ :| []) = pure ()
      checkEvidence ((Ev _ _ x) :| z@(Ev y _ _) : more) = do
        x === y
        checkEvidence (z :| more)
      problem = const Nothing $ Just $ reverse
        [ v0 `le` v1
        , v2 `le` v0
        , v1 `le` v2
        ]
    -- Trace through the problem
    for_ problem \posed -> do
      liftIO $ print posed
      for_ (traceConstraints posed) \(generation, state) -> do
        liftIO $ putStrLn $ show generation <> ":"
        forConstraint state \lower rel upper ev -> do
          liftIO $ putStrLn $ mconcat
            [ "  v", show lower, " ", relate rel, " v", show upper
            , " (heat ", show (evHeat ev), "):"
            , if endpoints ev /= (lower, upper) then "  χ" else "", "\n"
            , "    ", showEvidence (evData ev)
            ]
    onRandomConstraints 2000 "SolvableHasSolution" problem \case
      c@(Constraints Nothing m) -> do
        searchForInconsistency m === Nothing
        let solution = demonstrate c
        forConstraint m \lower rel upper ev -> do
          let
            cmp = case rel of
              Equal -> (===)
              LessThan -> \x y -> (x < y) === True
              LessThanEqual -> \x y -> (x <= y) === True
          HG.annotateShow (lower, rel, upper)
          solution lower `cmp` solution upper
          evLength ev === NEL.length (evData ev)
          HG.annotateShow $ evData ev
          checkEvidence $ evData ev
      Constraints _ _ -> pure ()
    onRandomConstraints 400 "Idempotent" Nothing \c -> do
      rel <- constraint <$> HG.forAll do
        genRelWith do Gen.choice $ genFresh : (pure <$> uvars c)
      (rel <> rel) `constraintsEq` rel
      -- ((c <> rel) <> rel) `constraintsEq` (c <> rel)
      -- Once removed: good enough for now. Guess some of the evidence does not
      -- quite saturate...
      (((c <> rel) <> rel) <> rel) `constraintsEq` ((c <> rel) <> rel)
      ((((c <> rel) <> rel) <> rel) <> rel) `constraintsEq` ((c <> rel) <> rel)

      -- Maybe these will hold? not quite sure
      -- ((rel <> c) <> rel) `constraintsEq` (rel <> c)
      -- (rel <> (c <> rel)) `constraintsEq` (rel <> c)
    -- hedgeTest 400 "Assoc" do
    --   c1 <- randomConstraints Nothing
    --   c2 <- randomConstraints Nothing
    --   c3 <- randomConstraints Nothing
    --   ((c1 <> c2) <> c3) `constraintsEq` (c1 <> (c2 <> c3))


solve :: NFData meta => [Relationship meta] -> Test (Constraints meta)
solve rels = do
  liftIO . evaluate . force $ foldMap constraint rels

consistent :: ShowEvidence meta => Constraints meta -> Test (Constraints meta)
consistent c@(Constraints Nothing rels) = do
  assert (isNothing (searchForInconsistency rels)) "Uncaught inconsistency"
  liftIO $ print (demonstrate c <$> uvars c)
  pure c
consistent (Constraints (Just inco) _) = testFail $
  inconsistency inco

inconsistent :: ShowEvidence meta => Constraints meta -> Test (Constraints meta)
inconsistent c@(Constraints Nothing _) = do
  testFail $ "consistent?? " <> show (demonstrate c <$> uvars c)
inconsistent c@(Constraints (Just inco) _) = do
  liftIO $ putStrLn $ inconsistency inco
  pure c

inconsistency :: ShowEvidence meta => InconsistentRelationship meta -> String
inconsistency (IncoRel (Fresh lower) inco (Fresh upper)) = mconcat
  case inco of
    InconsistentLTGT evLT evGT ->
      [ show lower, " < ", show upper, " (heat ", show (evHeat evLT), ") because:\n"
      , "  ", evidence evLT, "\n"
      , show lower, " > ", show upper, " (heat ", show (evHeat evGT), ") because:\n"
      , "  ", evidence evGT, "\n"
      ]
    InconsistentLTEQ evLT evEQ ->
      [ show lower, " = ", show upper, " (heat ", show (evHeat evEQ), ") because:\n"
      , "  ", evidence evEQ, "\n"
      , show lower, " < ", show upper, " (heat ", show (evHeat evLT), ") because:\n"
      , "  ", evidence evLT, "\n"
      ]

evidence :: ShowEvidence meta => Evidence meta -> String
evidence (Evidence { evData }) = showEvidence evData

genFresh :: Gen Fresh
genFresh = Fresh <$> do
  Gen.int =<< Gen.choice [ pure $ Range.linear 0 10, pure $ Range.linear 0 50 ]

genRelWith :: Gen Fresh -> Gen (Relationship Ev)
genRelWith freshener = Gen.choice [ pure le, pure lt ] <*> freshener <*> freshener

genRel :: Gen (Relationship Ev)
genRel = genRelWith genFresh

genRels :: Gen [Relationship Ev]
genRels = Gen.list (Range.linear 0 100) genRel

randomConstraints :: Maybe [Relationship Ev] -> HG.PropertyT IO (Constraints Ev)
randomConstraints fixed =
  liftIO . evaluate . force . foldMap constraint =<<
    maybe (HG.forAll genRels) pure fixed

traceConstraints :: Eq ev => [Relationship ev] -> NonEmpty (Int, ConstraintMap ev)
traceConstraints = NEL.reverse . go where
  go [] = NEL.singleton (0, mempty)
  go (newRel : more) =
    let
      -- First we recurse (to match the associativity of `foldMap constraint`)
      (!gen, current) :| recorded0 = go more
      -- The new constraint to add
      Constraints _ step = constraint newRel
      -- Wait for it to stabilize with this new constraint
      stabilized :| stabilization = (gen+1,) <$>
        stabilizeConstraints (step <> current :| [])
    in stabilized :| stabilization ++ [(gen, current)] ++ recorded0 -- append recordings

stabilizeConstraints :: Eq ev => NonEmpty (ConstraintMap ev) -> NonEmpty (ConstraintMap ev)
stabilizeConstraints = tick
  where
  tick (current :| recording) =
    let new = oppositivize current in
    tock if new == current then new :| recording else new :| current : recording
  tock (current :| recording) =
    let new = transitivize1 current <> current in
    if new == current then new :| recording else tick (new :| current : recording)
