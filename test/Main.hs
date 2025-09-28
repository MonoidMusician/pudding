module Main (main) where

import Control.Applicative (many, (<|>))
import Control.Monad (forM)
import Data.Functor (void)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (exitFailure)
import qualified Text.Parsec as P
import Text.Parsec.Text (Parser)

import Pudding.Parser (runParser, term)

main :: IO ()
main = do
  let sourceName = "test/core.txt"
  raw <- TIO.readFile sourceName
  cases <- case P.runParser testFile () sourceName raw of
    Left err -> do
      putStrLn $ "Failed to parse test cases: " ++ show err
      exitFailure
    Right cases -> return cases
  failures <- fmap sum $ forM cases $ \(TestCase expected text) ->
    case runParser (P.spaces *> term <* P.eof) "test case" text of
      Left err -> case expected of
        Pass -> do
          putStrLn "Test failed (could not parse):"
          putStrLn $ "  " ++ T.unpack text
          putStrLn $ "  " ++ show err
          return 1
        Fail -> return 0
      Right _ -> case expected of
        Pass -> return 0
        Fail -> do
          putStrLn "Test failed (should not have parsed):"
          putStrLn $ "  " ++ T.unpack text
          -- putStrLn $ "  " ++ show t
          return 1
  if failures == (0 :: Int) then
    putStrLn "All tests passed"
  else do
    putStrLn $ show failures ++ " tests failed"
    exitFailure

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
