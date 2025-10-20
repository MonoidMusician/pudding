module Testing where

import Control.Exception (SomeException, catch)
import Control.Monad (ap, forM_, unless)
import Control.Monad.IO.Class ( MonadIO(..) )
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.Maybe (isNothing)
import Control.Monad.Reader.Class (MonadReader (local, ask))

type TestFailure = String

data TestResult = TestResult
  { testName :: String
  , testCases :: [TestResult]
  , testFailures :: [TestFailure]
  }

newtype TestName = TestName [String]

child :: TestName -> String -> TestName
child (TestName p) c = TestName (c:p)

instance Show TestName where
  show (TestName parts) = intercalate "/" $ reverse parts

-- TODO: Snoc lists?
type TestState a = (Maybe a, [TestResult], [TestFailure])

data Test r a = Test ((TestName, r) -> IO (TestState a))
  deriving (Functor)

instance Applicative (Test r) where
  pure a = Test $ \_ -> return (Just a, [], [])
  (<*>) = ap

instance Monad (Test r) where
  return = pure
  Test m1 >>= f = Test $ \name -> do
    (x, r, fs) <- wrapExceptions (m1 name)
    case x of
      Nothing -> return (Nothing, r, fs)
      Just a -> do
        let Test m2 = f a
        (x', r', fs') <- wrapExceptions (m2 name)
        return (x', r <> r', fs <> fs')

instance MonadReader r (Test r) where
  local = changeContext
  ask = testContext

instance MonadFail (Test r) where
  fail = testFail

instance MonadIO (Test r) where
  liftIO m = Test $ \_ -> wrapExceptions
    (m <&> \a -> (Just a, [], []))

wrapExceptions :: IO (TestState a) -> IO (TestState a)
wrapExceptions m = catch m
  \(e :: SomeException) -> do
    let s = show e
    putStrLn s
    return (Nothing, [], [s])

runTest :: TestName -> String -> r -> Test r a -> IO TestResult
runTest parent name context (Test m) = do
  let fullName = child parent name
  (_, r, fs) <- wrapExceptions (m (fullName, context))
  let result = TestResult name r fs
  let summary = summarize result
  if failed summary == 0 then
    putStrLn $ "\ESC[32m[ PASS ]\ESC[0m  " ++ show fullName
  else
    putStrLn $ "\ESC[31m[ FAIL ]\ESC[0m  " ++ show fullName
  return result

testCase :: String -> Test r a -> Test r ()
testCase name t = Test $ \(parent, context) -> do
  r <- runTest parent name context t
  return (Just (), [r], [])

testCaseName :: Test r TestName
testCaseName = Test $ \(name, _context) ->
  return (Just name, [], [])

testContext :: Test r r
testContext = Test \(_name, context) ->
  return (Just context, [], [])

withContext :: r' -> Test r' a -> Test r a
withContext context (Test m) =
  Test \(name, _oldContext) ->
    m (name, context)

changeContext :: (r -> r') -> Test r' a -> Test r a
changeContext newOfOld (Test m) =
  Test \(name, oldContext) ->
    m (name, newOfOld oldContext)

testFail :: String -> Test r a
testFail e = Test $ \_ -> do
  putStrLn e
  return (Nothing, [], [e])

testFailSoft :: String -> Test r ()
testFailSoft e = Test $ \_ -> do
  putStrLn e
  return (Just (), [], [e])

data TestSuite = TestSuite String (Test () ())

runSuite :: TestSuite -> Test () ()
runSuite (TestSuite name t) = testCase name t

runSuites :: String -> [TestSuite] -> IO TestResult
runSuites topLevel suite = runTest (TestName []) topLevel () $
  forM_ suite $ \(TestSuite name t) -> testCase name t

data TestSummary = TestSummary { passed :: Int, failed :: Int }

instance Semigroup TestSummary where
  TestSummary p1 f1 <> TestSummary p2 f2 =
    TestSummary (p1 + p2) (f1 + f2)

instance Monoid TestSummary where
  mempty = TestSummary 0 0

summarize :: TestResult -> TestSummary
summarize (TestResult _ r fs) = foldMap summarize r <> case fs of
  [] -> TestSummary 1 0
  _ -> TestSummary 0 1

assert :: Bool -> String -> Test r ()
assert c e = unless c $ testFail $ "Assertion failed: " ++ e

assertRight :: Show e => Either e a -> Test r a
assertRight (Left e) = testFail $ show e
assertRight (Right a) = return a

expect :: Bool -> String -> Test r ()
expect c e = unless c $ testFailSoft $ "Assertion failed: " ++ e

expectEq :: (Eq a, Show a) => a -> a -> Test r ()
expectEq a b = expect (a == b) $ show a ++ " == " ++ show b

expectEquiv :: (Eq b, Show b) => (a -> b) -> a -> a -> Test r ()
expectEquiv e a b = let
  a' = e a
  b' = e b
  in assert (a' == b') $ show a' ++ " ~= " ++ show b'

expectFail :: Test r a -> Test r ()
expectFail (Test m) = do
  f <- Test $ \(name, context) -> do
    let fullName = child name "expectFail"
    (x, _, _) <- wrapExceptions (m (fullName, context))
    return (Just (isNothing x), [], [])
  expect f "expectFail ..."
