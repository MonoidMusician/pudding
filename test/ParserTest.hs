module ParserTest (parserTest, sourceSpanTest) where

import Control.Applicative (many)
import Control.Monad.IO.Class (liftIO)
import Data.Functor (void)
import Data.Set (elems)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Text.Parsec as P

import Pudding.Parser (SourceSpan(SourceSpan), runParser, term)
import Pudding.Printer (formatCore, Style (Ansi))
import Pudding.Types
import Testing

parserTest :: TestSuite
parserTest = TestSuite "ParserTest" do
  runSuite termTest
  runSuite sourceSpanTest

termTest :: TestSuite
termTest = TestSuite "TermTest" do
  testCase "Var" do
    testParser' "x"
  testCase "App" do
    testParser' "(f x)"
    testParser' "(f x y)"
    testParser' "(f x y z)"
    expectFail $ testParser' "f x"
  testCase "Lambda" do
    testParser' "(lambda (x A) x)"
    testParser' "(λ (x A) x)"
    testParser' "(λ (x A) (f x))"
    expectFail $ testParser' "(lambda (x A))"
    expectFail $ testParser' "(lambda (x A) f x)"
    expectFail $ testParser' "(lambda (x) x)"
    expectFail $ testParser' "(lambda x x)"
  testCase "Pi" do
    testParser' "(Pi (x A) B)"
    testParser' "(Π (x A) B)"
    testParser' "(Π (x A) (B x))"
    expectFail $ testParser' "(Pi (x A))"
    expectFail $ testParser' "(Pi (x A) B x)"
    expectFail $ testParser' "(Pi (x) B)"
    expectFail $ testParser' "(Pi x B)"
  testCase "BigTerm" do
    testParser' "(lambda (f (Pi (x A) (B x))) (f ((lambda (s T) (s s)) y) z))"
  testCase "Keyword" do
    testParser' "(lambda2)"
  testCase "TypeofIdentity" do
    TPi _ _ _ _ (Scoped (TPi _ _ _ (TVar _ i1) (Scoped (TVar _ i2)))) <-
      testParser "(Pi (t (Type0)) (Pi (x t) t))"
    expectEq (Index 0) i1
    expectEq (Index 1) i2
  testCase "2LTT" do
    testParser' "(Lift (Pi (x A) B))"
    testParser' "(Π (x (Lift A)) B)"
    testParser' "(quote (lambda (x A) x))"
    testParser' "(splice (quote x))"
    expectFail $ testParser' "(Lift)"
    expectFail $ testParser' "(quote)"
    expectFail $ testParser' "(splice)"
    expectFail $ testParser' "(splice x y)"

testParser :: Text -> Test r Term
testParser text = do
  name <- testCaseName
  r <- liftIO $ runParser (P.spaces *> term <* P.eof) (show name) text
  tm <- assertRight r
  liftIO $ putStrLn $ T.unpack $ formatCore Ansi tm
  return tm

testParser' :: Text -> Test r ()
testParser' = void . testParser

simplePos :: P.SourcePos -> (Int, Int)
simplePos p = (P.sourceLine p, P.sourceColumn p)

metaSpan :: Metadata -> Test r ((Int, Int), (Int, Int))
metaSpan meta = case elems (sourcePos meta) of
  [SourceSpan begin end] -> return (simplePos begin, simplePos end)
  _ -> testFail "Malformed metadata"

expectSpan :: ((Int, Int), (Int, Int)) -> Metadata -> Test r ()
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
    TLambda _ _ _ _ (Scoped (TApp _ _ (TVar meta _))) <- pure t1
    expectSpan ((2, 10), (2, 11)) meta
  testCase "TGlobal" do
    -- The type "A" in (lambda (x A) ...)
    TLambda _ _ _ (TGlobal meta _) _ <- pure t1
    expectSpan ((1, 12), (1, 13)) meta
  testCase "TLambda" do
    -- The entire second top-level term
    TLambda meta _ _ _ _ <- pure t2
    expectSpan ((4, 2), (5, 25)) meta
  testCase "TPi" do
    -- The term (Pi (x A) (Id x x))
    TLambda _ _ _ (TPi meta _ _ _ _) _ <- pure t2
    expectSpan ((4, 16), (4, 33)) meta
  testCase "TApp" do
    -- The term (eq (Loop z) (refl z))
    TLambda _ _ _ _ (Scoped (TApp meta (TApp lmeta _ _) (TApp rmeta _ _))) <- pure t2
    expectSpan ((5, 4), (5, 24)) meta
    expectSpan ((5, 4), (5, 15)) lmeta
    expectSpan ((5, 17), (5, 23)) rmeta
