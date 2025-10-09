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
import qualified GHC.Base as GHC

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
  showEvidence (_greater@(Ev (Fresh l) r (Fresh u)) :| lesser@(Ev (Fresh next) _ _) : more) =
    GHC.assert (u == next) $ step <> showEvidence (lesser :| more)
    where
    step = mconcat [ "v", show l, " ", relate r, " " ]


instance Show Ev where
  show (Ev (Fresh x) rel (Fresh y)) = mconcat
    [ "v", show x, " "
    , relate rel
    , " v", show y
    ]

solverTest :: TestSuite
solverTest = TestSuite "SolverTest" do
  let
    v = Fresh
    v0 = v 0
    v1 = v 1
    v2 = v 2

    lt :: Fresh -> Fresh -> Relationship Ev
    lt x y = (x, LessThan, y, Ev x LessThan y)
    le :: Fresh -> Fresh -> Relationship Ev
    le x y = (x, LessThanEqual, y, Ev x LessThanEqual y)
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
