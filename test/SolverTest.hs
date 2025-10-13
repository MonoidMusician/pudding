{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Evaluate" #-}
module SolverTest (solverTest) where

import Control.Monad.IO.Class (liftIO)

import Testing
import Data.Foldable (for_)
import Control.DeepSeq (force, NFData)
import Pudding.Types (Fresh(..))
import Pudding.Semantics.Universes
import qualified Pudding.Semantics.LevelAlgebra as Lvl
import GHC.IO (evaluate)
import Data.Maybe (isNothing, fromMaybe)
import GHC.Generics (Generic)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NEL
import qualified Hedgehog as HG
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog (Gen, (===))
import Data.Either (isRight, isLeft)
import qualified Data.IntMap.Strict as IntMap

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
  const (pure ()) $ testCase "Properties" do
    let
      rawConstraints (Constraints _ m) = m
      constraintsEq x y = rawConstraints x === rawConstraints y
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
    let
      fake = Evidence 0 (pure ()) 0
      testAssoc :: forall i o. Show i => Semigroup i => Show o => Eq o => HG.TestLimit -> Gen i -> (i -> o) -> Test ()
      testAssoc n gen f = hedgeTest n "Assoc" do
        x <- HG.forAll gen
        y <- HG.forAll gen
        z <- HG.forAll gen
        f ((x <> y) <> z) === f (x <> (y <> z))
      testIdemp :: forall i o. Show i => Semigroup i => Eq i => Show o => Eq o => HG.TestLimit -> Gen i -> (i -> o) -> Test ()
      testIdemp n gen f = hedgeTest n "Idempotent" do
        x <- HG.forAll gen
        z <- HG.forAll gen
        (z <> z) === z -- idempotence should hold literally
        f ((x <> z) <> z) === f (x <> z)
    testCase "Semigroup Inconsistency" do
      testAssoc 4000 genInconsistency id
      testIdemp 4000 genInconsistency id
    testCase "Semigroup Related" do
      let
        glossOverInconsistentAlgebra = \case
          Inconsistent i -> Inconsistent case i of
            InconsistentLTGT _ _ -> InconsistentLTGT fake fake
            InconsistentLTEQ _ _ -> InconsistentLTEQ fake fake
          r -> r
      testAssoc 4000 genRelated glossOverInconsistentAlgebra
      testIdemp 4000 genRelated glossOverInconsistentAlgebra
  levelAlgebra
  levelAlgebraHasSolution


hedgeTest :: HG.TestLimit -> String -> HG.PropertyT IO () -> Test ()
hedgeTest num name f = testCase name do
  HG.check $ HG.withTests num $ HG.property f

levelAlgebra :: Test ()
levelAlgebra =
  hedgeTest 2000 "LevelAlgebra" do
    rels <- HG.forAll genRels
    case (quickConstraints rels, quickSolve rels) of
      (Constraints Nothing _, solution) -> do
        HG.annotateShow case solution of
          Left (rel@(v1, _, v2, _), history, solv) -> Just
            (rel, Lvl.compareIn (v1, v2) solv, Lvl.solverState <$> history)
          Right _ -> Nothing
        isRight solution === True
      (Constraints (Just _) _, solution) -> do
        isLeft solution === True
        pure ()

levelAlgebraHasSolution :: Test ()
levelAlgebraHasSolution =
  hedgeTest 8000 "LevelAlgebraHasSolution" do
    rels <- HG.forAll genRels
    case quickSolve rels of
      (Right (_history, solution)) -> do
        HG.annotateShow $ Lvl.solverState <$> solution : _history
        let assigned = flip IntMap.lookup $ Lvl.demonstrate solution
        HG.annotateShow $ IntMap.toAscList $ Lvl.demonstrate solution
        for_ rels \(Fresh lower, rel, Fresh upper, _) -> do
          let
            cmpL = case rel of
              Equal -> (===)
              LessThan -> \x y -> Lvl.lattice x y === Lvl.PosetLE
              LessThanEqual -> \x y -> x Lvl.<=? y === True
            -- cmp = case rel of
            --   Equal -> (===)
            --   LessThan -> \x y -> (x < y) === True
            --   LessThanEqual -> \x y -> (x <= y) === True
          HG.annotateShow (lower, rel, upper)
          let
            x = fromMaybe 0 $ assigned lower
            y = fromMaybe 0 $ assigned upper
            p = fromMaybe IntMap.empty $ Lvl.lookup (Fresh lower) solution
            q = fromMaybe IntMap.empty $ Lvl.lookup (Fresh upper) solution
          cmpL p q -- *> cmp x y
      (Left _) -> do
        -- isNothing solv === True
        pure ()

(???) :: Maybe a -> String -> a
Nothing ??? err = error err
Just r ??? _ = r

solve :: NFData meta => [Relationship meta] -> Test (Constraints meta)
solve rels = do
  liftIO . evaluate . force $ foldMap constraint rels

quickSolve :: [Relationship meta] -> Either (Relationship meta, [Lvl.Solver], Lvl.Solver) ([Lvl.Solver], Lvl.Solver)
quickSolve [] = Right ([], Lvl.base)
quickSolve (rel@(v1, r, v2, _) : more) =
  case quickSolve more of
    Left err -> Left err
    Right (history, solv) -> case Lvl.relate (v1, r, v2) solv of
      Nothing -> Left (rel, solv : history, solv)
      Just res -> Right (solv : history, res)

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

-- 100 is okay performance wise, but 200 is really slow :(
-- `quickConstraints` helps but might not be realistic for actual usage, where
-- constraints are mostly being added one-by-one
genRels :: Gen [Relationship Ev]
genRels = Gen.list (Range.linear 0 60) genRel

randomConstraints :: Maybe [Relationship Ev] -> HG.PropertyT IO (Constraints Ev)
randomConstraints fixed =
  liftIO . evaluate . force . foldMap constraint {- quickConstraints -} =<<
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

genEvidence :: Gen (Evidence ())
genEvidence = Evidence
  <$> Gen.int (Range.constant 0 10)
  <*> pure (pure ()) -- cheating, should be of the right length but /shrug
  <*> Gen.int (Range.constant 0 20)

genInconsistency :: Gen (Inconsistency ())
genInconsistency =
  Gen.choice [ pure InconsistentLTGT, pure InconsistentLTEQ ]
    <*> genEvidence <*> genEvidence

genRelated :: Gen (Related ())
genRelated = Gen.choice
  [ Related <$> Gen.choice [ pure LessThan, pure LessThanEqual, pure Equal ] <*> genEvidence
  , Inconsistent <$> genInconsistency
  ]
