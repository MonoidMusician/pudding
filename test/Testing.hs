module Testing where

import Control.Monad (ap, forM_, unless)
import Control.Monad.Except ( MonadError(catchError) )
import Control.Monad.IO.Class ( MonadIO(..) )
import Data.List (intercalate)

data Status = Pass | Fail String
  deriving (Eq)

instance Semigroup Status where
  Pass <> Pass = Pass
  Pass <> Fail e = Fail e
  Fail e <> Pass = Fail e
  Fail _ <> Fail _ = Fail "(multiple failures)"

instance Monoid Status where
  mempty = Pass

status :: Either String () -> Status
status (Left e) = Fail e
status (Right _) = Pass

data TestResult = TestResult
  { testName :: String
  , testCases :: [TestResult]
  , testStatus :: Status
  }

newtype TestName = TestName [String]

child :: TestName -> String -> TestName
child (TestName p) c = TestName (c:p)

instance Show TestName where
  show (TestName parts) = intercalate "/" $ reverse parts

-- TODO: Give testFail access to test names
data Test a = Test (TestName -> IO (Either String a, [TestResult]))
  deriving (Functor)

instance Applicative Test where
  pure a = Test $ \_ -> return (Right a, [])
  (<*>) = ap

instance Monad Test where
  return = pure
  Test m1 >>= f = Test $ \name -> do
    (x, r) <- m1 name
    case x of
      Left e -> return (Left e, r)
      Right a -> do
        let Test m2 = f a
        (x', r') <- m2 name
        return (x', r <> r')

instance MonadIO Test where
  liftIO m = Test $ \_ -> catchError
    (m >>= \a -> return (Right a, []))
    (\e -> return (Left (show e), []))

runTest :: TestName -> String -> Test () -> IO TestResult
runTest parent name (Test m) = do
  (x, r) <- m $ child parent name
  let s = status x <> mconcat [testStatus t | t <- r]
  return $ TestResult name r s

testCase :: String -> Test () -> Test ()
testCase name t = Test $ \parent -> do
  r <- runTest parent name t
  return (Right (), [r])

testCaseName :: Test TestName
testCaseName = Test $ \name ->
  return (Right name, [])

testFail :: String -> Test a
testFail e = Test $ \name -> do
  -- TODO: Color
  putStrLn $ "[ FAIL ]  " ++ show name ++ "\n" ++ e
  return (Left e, [])

data TestSuite = TestSuite String (Test ())

runSuites :: String -> [TestSuite] -> IO TestResult
runSuites topLevel suite = runTest (TestName []) topLevel $
  forM_ suite $ \(TestSuite name t) -> testCase name t

data TestSummary = TestSummary { passed :: Int, failed :: Int }

instance Semigroup TestSummary where
  TestSummary p1 f1 <> TestSummary p2 f2 =
    TestSummary (p1 + p2) (f1 + f2)

instance Monoid TestSummary where
  mempty = TestSummary 0 0

summarize :: TestResult -> TestSummary
summarize (TestResult _ [] Pass) = TestSummary 1 0
summarize (TestResult _ [] (Fail _)) = TestSummary 0 1
summarize (TestResult _ r _) = foldMap summarize r

-- TODO: Expect?
assert :: Bool -> String -> Test ()
assert c e = unless c $ testFail $ "Assertion failed: " ++ e

assertEq :: (Eq a, Show a) => a -> a -> Test ()
assertEq a b = assert (a == b) $ show a ++ " == " ++ show b
