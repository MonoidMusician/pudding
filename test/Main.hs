-- Run with `cabal test --verbose=0` or `cabal test` (from the project root)
module Main (main) where

import Control.Applicative (many, (<|>))
import Control.Monad (forM_, when)
import Control.Monad.IO.Class (liftIO)
import Data.Functor (void)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (exitFailure)
import qualified Text.Parsec as P
import Text.Parsec.Text (Parser)

import Pudding.Parser (runParser, term)
import Pudding.Printer (formatCore, Style (Ansi))
import Testing

main :: IO ()
main = do
  r <- runSuites [parserTest]
  let summary = summarize r
  putStrLn $ show (passed summary) ++ " tests passed"
  putStrLn $ show (failed summary) ++ " tests failed"
  when (testStatus r /= Pass) exitFailure

parserTest :: TestSuite
parserTest = TestSuite "ParserTest" do
  let sourceName = "test/core.txt"
  raw <- liftIO $ TIO.readFile sourceName
  cases <- case P.runParser testFile () sourceName raw of
    Left err -> testFail $ "Failed to parse test cases: " ++ show err
    Right cases -> return cases
  forM_ (zip [1..] cases) $ \(n :: Int, TestCase expected text) -> do
    let name = "ParserTest/" ++ show n
    testCase name do
      r <- liftIO $ runParser (P.spaces *> term <* P.eof) name text
      case r of
        Left err -> case expected of
          ExpectPass -> testFail $
            "Test failed (could not parse): " ++ show err
          ExpectFail -> return ()
        Right parsed -> case expected of
          ExpectPass -> liftIO $ putStrLn $ T.unpack $ formatCore Ansi parsed
          ExpectFail -> testFail $
            "Test failed (should not have parsed): " ++ T.unpack text

data Expected = ExpectPass | ExpectFail
data TestCase = TestCase Expected Text

comment :: Parser ()
comment = void $ P.string "--" *> P.manyTill P.anyChar (P.char '\n')

space :: Parser ()
space = P.spaces *> P.skipMany (comment *> P.spaces)

testFileCase :: Parser TestCase
testFileCase = do
  e <- ExpectPass <$ P.string' "pass"
    <|> ExpectFail <$ P.string' "fail"
  space *> P.char '{' *> space
  cs <- P.manyTill P.anyChar (P.char '}') <* space
  return (TestCase e (T.pack cs))

testFile :: Parser [TestCase]
testFile = space *> many testFileCase <* P.eof
