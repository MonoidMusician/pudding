-- Run with `cabal test --verbose=0` or `cabal test` (from the project root)
module Main (main) where

import Control.Monad (when)
import System.Exit (exitFailure)

import EvalTest (evalTest)
import ParserTest (parserTest)
import Testing (TestSummary(failed, passed), summarize, runSuites)
import SolverTest (solverTest)

main :: IO ()
main = do
  r <- runSuites "Pudding" [parserTest, evalTest, solverTest]
  let summary = summarize r
  putStrLn $ show (passed summary) ++ " tests passed"
  putStrLn $ show (failed summary) ++ " tests failed"
  when (failed summary /= 0) exitFailure
