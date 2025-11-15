module FileTest (plumTest) where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable (sequenceA_)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Text.Parsec as P

import Pudding.Parser
import Pudding.Types
import Testing
import EvalTest
import qualified Data.Map.Lazy as Map
import Pudding.Unify (bootGlobals)
import Control.Monad.Trans.Class (MonadTrans(lift))
import Control.Monad.Trans.Cont (ContT (ContT))
import qualified Data.Text.IO.Utf8 as Text

plumTest :: TestSuite
plumTest = TestSuite "PlumTests" do
  runPlumFile "test/test.plum"

plumStatement :: Parser PlumTest
plumStatement = testAction P.<|> fmap intoEnv declaration

plumStatements :: Parser PlumTest
plumStatements = do
  statements <- spaces *> P.many (plumStatement <* spaces)
  pure $ sequenceA_ statements

testAction :: Parser PlumTest
testAction = P.try do lp *> testActions <* rp
  where
  testActions = P.choice
    [ do
        _ <- keyword ["normalizesTo"]
        tm1 <- term
        tm2 <- term
        pure $ inEnv do
          ty1 <- typecheck tm1
          ty2 <- typecheck tm2
          defEqTo ty1 ty2
          normalizesTo tm1 tm2
    , do
        _ <- keyword ["defEq"]
        tm1 <- term
        tm2 <- term
        pure $ inEnv do
          ty1 <- typecheck tm1
          ty2 <- typecheck tm2
          defEqTo ty1 ty2
          defEqTo tm1 tm2
    , do
        _ <- keyword ["hasType"]
        ty <- term
        tm <- term
        pure $ inEnv do
          _ <- typecheck ty
          ty' <- typecheck tm
          defEqTo ty ty'
    , do
        _ <- keyword ["namedTest"]
        name <- str
        ContT inner <- plumStatements
        pure $ ContT (=<< testCase (T.unpack name) (inner pure))
    -- , do
    --     _ <- keyword ["parameter"]
    --     name <- ident
    --     ty <- term
    --     ContT inner <- plumStatements
    --     pure $ ContT (=<< addVar (nameText name) ty (inner pure))
    ]

runPlumFile :: String -> Test () ()
runPlumFile filename = do
  source <- liftIO $ Text.readFile filename
  runPlumSource filename source

runPlumSource :: P.SourceName -> Text -> Test () ()
runPlumSource sourceName source = do
  parsed <- liftIO $ runParser plumContents sourceName source
  case parsed of
    Right testToRun -> testToRun
    Left err -> testFail $ show err

plumContents :: Parser (Test () ())
plumContents = uncont <$> plumStatements

-- Bare globals, lazily booted globals
type RunningEnv = (Map.Map Name GlobalInfo, Globals)
-- Turn reader into state, basically
type PlumTest = ContT () (Test RunningEnv) ()

uncont :: PlumTest -> Test () ()
uncont (ContT withFinish) =
  withContext (Map.empty, Map.empty) $
    withFinish \() -> pure ()

intoEnv :: (Name, GlobalInfo) -> PlumTest
intoEnv (name, entry) = ContT \cont ->
  changeContext envppend (cont ())
  where
  envppend (prev, _) =
    let globals = Map.insert name entry prev in
    (globals, bootGlobals globals)

inEnv :: EvalTest () -> PlumTest
inEnv wrapped = lift $
  changeContext (ctxOfGlobals . snd) wrapped
