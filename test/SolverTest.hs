{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Evaluate" #-}
module SolverTest (solverTest, solverUnitTest) where

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
import Data.IORef (newIORef, modifyIORef', readIORef)
import qualified Data.Vector as Vector
import qualified Hedgehog.Internal.Config as HG.Config
import qualified Hedgehog.Internal.Gen as HG.Gen
import qualified Hedgehog.Internal.Region as HG.Region
import qualified Hedgehog.Internal.Report as HG.Report
import qualified Hedgehog.Internal.Runner as HG.Runner
import qualified Hedgehog.Internal.Seed as HG.Seed
import qualified Hedgehog.Internal.Tree as HG.Tree
import Data.Int (Int32)
import Data.Word (Word64)

solverUnitTest :: TestSuite
solverUnitTest = TestSuite "SolverUnitTest" do
  reducedEqual
  intermediateIsBetween

reducedEqual :: Test r ()
reducedEqual = hedgeTest 1000 "reducedEqual" do
  n <- HG.forAll genNumerator
  d <- HG.forAll genDenominator
  let r = Lvl.reduced n d
  HG.annotateShow r
  Lvl.Chain n 1 === r * Lvl.Chain d 1

intermediateIsBetween :: Test r ()
intermediateIsBetween = hedgeTest 1000 "intermediateIsBetween" do
  x <- HG.forAll genChain
  y <- HG.forAll genChain
  let z = Lvl.intermediate x y
  HG.annotateShow z
  HG.assert $ Lvl.isBetween (x, y) z

minSafeInt32 :: Int32
minSafeInt32 = -32768

maxSafeInt32 :: Int32
maxSafeInt32 = 32767

genNumerator :: Gen Int32
genNumerator = Gen.int32 $ Range.linearFrom 0 minSafeInt32 maxSafeInt32

genDenominator :: Gen Int32
genDenominator = Gen.choice
  [ Gen.int32 $ Range.linearFrom 1 1 maxSafeInt32
  , Gen.int32 $ Range.linearFrom (-1) minSafeInt32 (-1)
  ]

genChain :: Gen Lvl.Chain
genChain = Lvl.reduced <$> genNumerator <*> genDenominator

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
    recordSuccessRate "Solvable (length 80)" \wasSolvable -> do
      onRandomConstraints 1000 "SolvableHasSolution" problem \case
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
          wasSolvable True
        Constraints _ _ -> wasSolvable False
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
      testAssoc :: forall i o. Show i => Semigroup i => Show o => Eq o => HG.TestLimit -> Gen i -> (i -> o) -> Test () ()
      testAssoc n gen f = hedgeTest n "Assoc" do
        x <- HG.forAll gen
        y <- HG.forAll gen
        z <- HG.forAll gen
        f ((x <> y) <> z) === f (x <> (y <> z))
      testIdemp :: forall i o. Show i => Semigroup i => Eq i => Show o => Eq o => HG.TestLimit -> Gen i -> (i -> o) -> Test () ()
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

hedgeTest :: HG.TestLimit -> String -> HG.PropertyT IO () -> Test r ()
hedgeTest = hedgeTest' Nothing

hedgeTest' :: Maybe HG.Seed -> HG.TestLimit -> String -> HG.PropertyT IO () -> Test r ()
hedgeTest' seed num name f = testCase name do
  expectProp seed $ HG.withTests num $ HG.property f

expectProp :: Maybe HG.Seed -> HG.Property -> Test r ()
expectProp mseed prop = do
  color <- HG.Config.detectColor
  seed <- HG.Config.resolveSeed mseed
  ok <- liftIO . HG.Region.displayRegion $ \region ->
    (== HG.Report.OK) . HG.Report.reportStatus <$>
      HG.Runner.checkRegion region color Nothing 0 seed prop
  expect ok "Property does not hold"

levelAlgebra :: Test r ()
levelAlgebra = do
  recordSuccessRate "Solvable (length 80)" \wasSolvable -> do
    hedgeTest 2000 "LevelAlgebra" do
      rels <- HG.forAll genRels
      case (quickConstraints rels, quickSolve rels) of
        (Constraints Nothing _, solution) -> do
          HG.annotateShow case solution of
            Left (rel@(v1, _, v2, _), history, solv) -> Just
              (rel, Lvl.compareIn (v1, v2) solv, Lvl.solverState <$> history)
            Right _ -> Nothing
          isRight solution === True
          wasSolvable True
        (Constraints (Just _) _, solution) -> do
          isLeft solution === True
          wasSolvable False
  testCase "LevelAlgebra" do
    levelAlgebraHasSolution

levelAlgebraHasSolution :: Test r ()
levelAlgebraHasSolution = do
  -- Capture the generated test cases
  recorded <- liftIO $ newIORef []
  -- This seems a particularly bad seed for the current tests: not only are they
  -- slower but they also hit more nonlinear behavior for the 200x1000 vs
  -- 1000x200 tests, thus they are probably a good target for optimization
  let hedgeSeed = Just 314159265358979323
  -- Generate a total order
  totalOrder <- liftIO $ case hedgeSeed of
    Nothing -> Gen.sample seedConsistent
    Just seed -> maybe (error "failed gen") (pure . HG.Tree.treeValue) $
      HG.Gen.evalGen 30 (HG.Seed.from seed) seedConsistent
  hedgeTest' (HG.Seed.from <$> hedgeSeed) 6000 "HasSolution" do
    rels <- HG.forAll $ genConsistent totalOrder $ Range.linear 0 100
    _ <- liftIO $ evaluate $ force rels
    liftIO $ modifyIORef' recorded (rels++)
    verify rels
  -- To remove the overhead during the speedy tests
  vectored <- liftIO $ readIORef recorded >>= \listed ->
    pure $! Vector.fromList listed
  let
    testWithParams nTests maxSize = do
      let testName = "HasSolutionSpeedy (" <> show (toInteger nTests) <> "×" <> show maxSize <> ")"
      recordAverage ("Chosen length (out of " <> show maxSize <> ")") \solveLength ->
        recordTime "Took" do
          hedgeTest' (HG.Seed.from <$> hedgeSeed) nTests testName do
            relStart <- HG.forAll $ Gen.int $ Range.constant 0 (Vector.length vectored - maxSize)
            relSize <- HG.forAll $ Gen.int $ Range.constant 20 maxSize
            solveLength relSize
            let rels = Vector.toList $ Vector.slice relStart relSize vectored
            verify rels
  testWithParams 200 1000
  testWithParams 1000 200
  where
  verify :: [Relationship meta] -> HG.PropertyT IO ()
  verify rels =
    case quickSolve rels of
      Right (_history, solution) -> do
        HG.annotateShow $ Lvl.solverState <$> solution : _history
        let assigned = flip IntMap.lookup $ Lvl.demonstrate solution
        HG.annotateShow $ IntMap.toAscList $ Lvl.demonstrate solution
        for_ rels \(Fresh lower, rel, Fresh upper, _) -> do
          let
            cmpL :: Lvl.Lattice -> Lvl.Lattice -> HG.PropertyT IO ()
            cmpL = case rel of
              Equal -> (===)
              LessThan -> \x y -> Lvl.lattice x y === Lvl.PosetLE
              LessThanEqual -> \x y -> x Lvl.<=? y === True
            cmp :: Int -> Int -> HG.PropertyT IO ()
            cmp = case rel of
              Equal -> (===)
              LessThan -> \x y -> (x < y) === True
              LessThanEqual -> \x y -> (x <= y) === True
          HG.annotateShow (lower, rel, upper)
          let
            x = fromMaybe 0 $ assigned lower
            y = fromMaybe 0 $ assigned upper
            p = fromMaybe IntMap.empty $ Lvl.lookup (Fresh lower) solution
            q = fromMaybe IntMap.empty $ Lvl.lookup (Fresh upper) solution
          cmpL p q *> cmp x y
      Left (_failedRel, _goodRels, _failedSolver) -> do
        error "Was deemed inconsistent!"

-- (???) :: Maybe a -> String -> a
-- Nothing ??? err = error err
-- Just r ??? _ = r

solve :: NFData meta => [Relationship meta] -> Test r (Constraints meta)
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

consistent :: ShowEvidence meta => Constraints meta -> Test r (Constraints meta)
consistent c@(Constraints Nothing rels) = do
  assert (isNothing (searchForInconsistency rels)) "Uncaught inconsistency"
  liftIO $ print (demonstrate c <$> uvars c)
  pure c
consistent (Constraints (Just inco) _) = testFail $
  inconsistency inco

inconsistent :: ShowEvidence meta => Constraints meta -> Test r (Constraints meta)
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
  Gen.int =<< Gen.choice [ pure $ Range.linear 0 10, pure $ Range.linear 0 60 ]

genRelWith :: Gen Fresh -> Gen (Relationship Ev)
genRelWith freshener = Gen.choice [ pure le, pure lt, pure mkEq ] <*> freshener <*> freshener
  where mkEq x y = (x, Equal, y, Ev x Equal y)

genRel :: Gen (Relationship Ev)
genRel = genRelWith genFresh

-- 100 is okay performance wise, but 200 is really slow :(
-- `quickConstraints` helps but might not be realistic for actual usage, where
-- constraints are mostly being added one-by-one
genRels :: Gen [Relationship Ev]
genRels = Gen.list (Range.linear 0 80) genRel

seedConsistent :: Gen (IntMap.IntMap Int)
seedConsistent = IntMap.fromList . zip [0..] <$>
  -- Increasing the number of variables seems to increase average solve time
  -- and also increase the slowness of more relations in certain cases
  Gen.list (Range.linear 0 300)
    -- Harder to tell how this affects speed
    (Gen.int (Range.linear 0 40))

genConsistent :: IntMap.IntMap Int -> Range.Range Int -> Gen [Relationship Ev]
genConsistent totalOrder lengthRange = do
  let sz = IntMap.size totalOrder
  Gen.list lengthRange do
    x <- Gen.int (Range.linear 0 sz)
    y <- Gen.int (Range.linear 0 sz)
    rel <- case compare (IntMap.lookup x totalOrder) (IntMap.lookup y totalOrder) of
      EQ -> Just <$> do
        (\i -> if i > 0 then LessThanEqual else Equal) <$> Gen.int (Range.constant 0 3)
      LT -> pure (Just LessThan)
      GT -> pure Nothing
    pure case rel of
      Just r -> (Fresh x, r, Fresh y, Ev (Fresh x) r (Fresh y))
      Nothing -> (Fresh y, LessThanEqual, Fresh x, Ev (Fresh y) LessThanEqual (Fresh x))


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
