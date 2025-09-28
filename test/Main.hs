-- Run with `cabal test --verbose=0` or `cabal test` (from the project root)
module Main (main) where

import Control.Applicative (many, (<|>))
import Control.Monad (forM, when)
import Data.Functor (void)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (exitFailure)
import qualified Text.Parsec as P
import Text.Parsec.Text (Parser)

import Pudding.Parser (runParser, term)

data TestResults = TestResults { passed :: Int, failed :: Int }

resultPass, resultFail :: TestResults
resultPass = TestResults 1 0
resultFail = TestResults 0 1

instance Semigroup TestResults where
  TestResults p1 f1 <> TestResults p2 f2 = TestResults (p1 + p2) (f1 + f2)

instance Monoid TestResults where
  mempty = TestResults 0 0

main :: IO ()
main = do
  let sourceName = "test/core.txt"
  raw <- TIO.readFile sourceName
  cases <- case P.runParser testFile () sourceName raw of
    Left err -> do
      putStrLn $ "Failed to parse test cases: " ++ show err
      exitFailure
    Right cases -> return cases
  results <- fmap mconcat $ forM cases $ \(TestCase expected text) ->
    runParser (P.spaces *> term <* P.eof) "test case" text >>= \case
      Left err -> case expected of
        Pass -> do
          putStrLn "Test failed (could not parse):"
          putStrLn $ "  " ++ T.unpack text
          putStrLn $ "  " ++ show err
          return resultFail
        Fail -> return resultPass
      Right _ -> case expected of
        Pass -> return resultPass
        Fail -> do
          putStrLn "Test failed (should not have parsed):"
          putStrLn $ "  " ++ T.unpack text
          -- putStrLn $ "  " ++ show t
          return resultFail
  putStrLn $ show (passed results) ++ " tests passed"
  putStrLn $ show (failed results) ++ " tests failed"
  when (failed results /= 0) exitFailure

data Expected = Pass | Fail
data TestCase = TestCase Expected Text

comment :: Parser ()
comment = void $ P.string "--" *> P.manyTill P.anyChar (P.char '\n')

space :: Parser ()
space = P.spaces *> P.skipMany (comment *> P.spaces)

testCase :: Parser TestCase
testCase = do
  e <- Pass <$ P.string' "pass" <|> Fail <$ P.string' "fail"
  space *> P.char '{' *> space
  cs <- P.manyTill P.anyChar (P.char '}') <* space
  return (TestCase e (T.pack cs))

testFile :: Parser [TestCase]
testFile = space *> many testCase <* P.eof
