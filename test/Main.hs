-- Run with `cabal test --verbose=0` or `cabal test` (from the project root)
module Main (main) where

import Control.Monad (when)
import System.Exit (exitFailure)

import Testing (TestSummary(failed, passed), summarize, runSuites)

import UnitTest (unitTests)
import EvalTest (evalTest)
import ParserTest (parserTest)
import SolverTest (solverTest, solverUnitTest)
import FileTest (plumTest)

main :: IO ()
main = do
  r <- runSuites "Pudding"
    [unitTests] -- [unitTests, parserTest, evalTest, solverUnitTest, solverTest, plumTest]
  let summary = summarize r
  putStrLn $ show (passed summary) ++ " tests passed"
  putStrLn $ show (failed summary) ++ " tests failed"
  when (failed summary /= 0) exitFailure
