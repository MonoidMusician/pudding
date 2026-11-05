module FileTest (plumTest) where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader.Class (MonadReader(local), asks)
import Control.Monad.Trans.Class (MonadTrans(lift))
import Control.Monad.Trans.Cont (ContT (ContT))
import Data.Foldable (sequenceA_)
import Data.Text (Text)
import EvalTest
import Pudding (unsafeRunProver)
import Pudding.Core.Parser
import Pudding.Core.Types
import Pudding.Core.Unify (bootGlobals)
import Pudding.Types.Name (canonicalName)
import Testing
import qualified Data.Text as T
import qualified Data.Text.IO.Utf8 as Text
import qualified Text.Parsec as P
import qualified Pudding.Core.Eval as Eval

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
    , do
        _ <- keyword ["parameter"]
        name <- ident
        ty <- term
        ContT inner <- local (bindIdent name) plumStatements
        pure $ ContT (=<< addParam name ty (inner pure))
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

-- Bare globals, and local parameters with lazily booted globals
type RunningEnv = (Globals, EvalTypeCtx)
-- Turn reader into state, basically
type PlumTest = ContT () (Test RunningEnv) ()

uncont :: PlumTest -> Test () ()
uncont (ContT withFinish) =
  withContext (freshGlobals, ctxOfGlobals freshGlobals) $
    withFinish \() -> pure ()

intoEnv :: (Name, GlobalInfo) -> PlumTest
intoEnv (name, entry) = ContT \cont ->
  changeContext envppend (cont ())
  where
  envppend (prev, Ctx _ params) =
    let globals = addGlobal prev name entry in
    (globals, Ctx (unsafeRunProver Nil $ bootGlobals globals) params)

inEnv :: EvalTest () -> PlumTest
inEnv wrapped = lift $
  changeContext snd wrapped

addParam :: Name -> Term -> Test RunningEnv a -> Test RunningEnv a
addParam name ty inner = do
  tyE <- Eval.eval <$> asks (fmap snd . snd) <*> pure ty
  local (fmap \ctx -> ctx :> (BVar (Meta (canonicalName name)), (tyE, neutralVar (Level (size ctx))))) do
    inner
