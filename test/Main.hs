-- Run with `cabal test --verbose=0` or `cabal test` (from the project root)
module Main (main) where

import Control.Applicative (many, (<|>))
import Control.Monad (forM_, when)
import Control.Monad.IO.Class (liftIO)
import Data.Functor (void)
import Data.Set (elems)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (exitFailure)
import qualified Text.Parsec as P
import Text.Parsec.Text (Parser)

import Pudding.Parser (runParser, term)
import Pudding.Printer (formatCore, Style (Ansi))
import Pudding.Types
import Testing

main :: IO ()
main = do
  r <- runSuites "Pudding" [parserTest, sourceSpanTest]
  let summary = summarize r
  putStrLn $ show (passed summary) ++ " tests passed"
  putStrLn $ show (failed summary) ++ " tests failed"
  when (failed summary /= 0) exitFailure

parserTest :: TestSuite
parserTest = TestSuite "ParserTest" do
  let sourceName = "test/ParserTest.txt"
  raw <- liftIO $ TIO.readFile sourceName
  cases <- assertRight $ P.runParser testFile () sourceName raw
  forM_ (zip [1..] cases) $ \(n :: Int, TestCase expected text) -> do
    testCase (show n) case expected of
      ExpectPass -> testParser text
      ExpectFail -> expectFail $ testParser text

testParser :: Text -> Test ()
testParser text = do
  name <- testCaseName
  r <- liftIO $ runParser (P.spaces *> term <* P.eof) (show name) text
  tm <- assertRight r
  liftIO $ putStrLn $ T.unpack $ formatCore Ansi tm

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

simplePos :: P.SourcePos -> (Int, Int)
simplePos p = (P.sourceLine p, P.sourceColumn p)

metaSpan :: Metadata -> Test ((Int, Int), (Int, Int))
metaSpan meta = case elems (sourcePos meta) of
  [SourceSpan begin end] -> return (simplePos begin, simplePos end)
  _ -> testFail "Malformed metadata"

expectSpan :: ((Int, Int), (Int, Int)) -> Metadata -> Test ()
expectSpan (eBegin, eEnd) meta = do
  (begin, end) <- metaSpan meta
  expectEq eBegin begin
  expectEq eEnd end

sourceSpanTest :: TestSuite
sourceSpanTest = TestSuite "SourceSpanTest" do
  let sourceName = "test/SourceSpanTest.txt"
  raw <- liftIO $ TIO.readFile sourceName
  res <- liftIO $ runParser (P.spaces *> many term <* P.eof) sourceName raw
  [t1, t2] <- assertRight res
  testCase "TVar" do
    -- The final "x" in the term (f x x x)
    TLambda _ _ _ _ (TApp _ _ (TVar meta _)) <- pure t1
    expectSpan ((2, 10), (2, 11)) meta
  testCase "TGlobal" do
    -- The type "A" in (lambda (x A) ...)
    TLambda _ _ _ (TGlobal meta _ _) _ <- pure t1
    expectSpan ((1, 12), (1, 13)) meta
  testCase "TLambda" do
    -- The entire second top-level term
    TLambda meta _ _ _ _ <- pure t2
    expectSpan ((4, 2), (5, 25)) meta
  testCase "TPi" do
    -- The entire second top-level term
    TLambda _ _ _ (TPi meta _ _ _ _) _ <- pure t2
    expectSpan ((4, 16), (4, 33)) meta
  testCase "TApp" do
    -- The term (eq (Loop z) (refl z))
    TLambda _ _ _ _ (TApp meta (TApp lmeta _ _) (TApp rmeta _ _)) <- pure t2
    expectSpan ((5, 4), (5, 24)) meta
    expectSpan ((5, 4), (5, 15)) lmeta
    expectSpan ((5, 17), (5, 23)) rmeta
