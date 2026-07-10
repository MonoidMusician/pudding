{- HLINT ignore "Use <=<" -}
module Pudding.Surface.Web where

import Prelude hiding (lex, error)

import Pudding.Surface.Lexer hiding (demo)
import qualified Pudding.Surface.Happy as Happy

import qualified Data.Text as T
import Pudding.Core.Types (initTable, GlobalDefn (GlobalDefn), GlobalTerm (GlobalTerm), Name (nameText), Term, GlobalInfo (DefnGlobal))
import qualified Text.Parsec as P
import qualified Data.Text.IO.Utf8 as TIO
import Control.Monad.Identity (Identity (runIdentity))
import Data.Show.Reshow (reshowAs)
import qualified Pudding.Surface.Elaborator as Elab
import Pudding.Core.Printer (Style (..), formatCore)
import GHC.IO (catch, evaluate, catchAny)
import GHC.Exception (SomeException)
import qualified Data.Map.Strict as Map
import Data.Foldable (Foldable (fold))
import Data.Text (Text)
import qualified Data.Aeson as AE
import GHC.Generics (Generic)
import qualified Text.Parsec as Parsec
import Data.Maybe (fromMaybe)
import Pudding.Surface.Parser (CST, Decl(..))
import Data.Function ((&))
import Data.Functor ((<&>))
import qualified Data.Show.Reshow as RS
import qualified System.Directory as Dir
import Control.Monad (join)
import Data.Traversable (for)
import System.FilePath ((</>))
import Data.Monoid (All (All))
import GHC.Base (error)
import qualified Data.Set as Set
import qualified Data.ByteString.Lazy as BS
import qualified Data.Aeson.Encode.Pretty as AEP

data Formats = Formats
  { text :: Text
  , html :: Text
  , ansi :: Text
  , json :: AE.Value
  } deriving (Show, Generic, AE.ToJSON, AE.FromJSON)

type Stages = [(Text, Stage)]
data Stage
  = StageFail
    { stageError :: Formats
    , stageDetails :: Maybe AE.Value
    }
  | StageDiff
    { stageDiff :: Maybe Formats -- a pretty diff itself
    , stageParts :: [Formats] -- the elements of the diff
    , stageDiffAux :: Maybe AE.Value
    }
  | StageSuccess
    { stageContent :: Formats
    , stageExtra :: Maybe AE.Value
    }
  deriving (Show, Generic, AE.ToJSON, AE.FromJSON)

xmlEscape :: Text -> Text
xmlEscape = T.pack . (esc =<<) . T.unpack
  where
  esc c =
    fromMaybe [c] $ Map.lookup c ents
  ents = Map.fromList
    [ ('"', "&quot;")
    , ('&', "&amp;")
    , ('<', "&lt;")
    , ('>', "&gt;")
    ]

plain :: Text -> Formats
plain t = Formats
  { text = t
  , html = xmlEscape t
  , ansi = t
  , json = AE.Null
  }

reshown :: forall s. Show s => s -> Formats
reshown s = (plain (reshowAs RS.Plain s))
  { ansi = reshowAs RS.Ansi s }

catching :: Text -> IO Stages -> IO Stages
catching stageName inner = do
  catch inner
    \(err :: SomeException) -> pure [(stageName, StageFail
      { stageError = plain (T.pack (show err))
      , stageDetails = Nothing
      })]


stage1Fail :: Parsec.ParseError -> (Text, Stage)
stage1Fail err = ("prelex", StageFail
  { stageError = plain (T.pack (show err))
  , stageDetails = Nothing
  })
stage1Success :: [LEXED] -> (Text, Stage)
stage1Success lexemes = ("prelex", StageSuccess
  { stageContent =
    (reshown lexemes)
    { json = AE.toJSON lexemes }
  , stageExtra = Nothing
  })

stage2Fail :: Parsec.ParseError -> (Text, Stage)
stage2Fail err = ("tokenize", StageFail
  { stageError = plain (T.pack (show err))
  , stageDetails = Nothing
  })
stage2Success :: [Token] -> (Text, Stage)
stage2Success tokens = ("tokenize", StageSuccess
  { stageContent =
    (reshown tokens)
    { json = AE.toJSON tokens }
  , stageExtra = Nothing
  })

stage3Fail :: String -> (Text, Stage)
stage3Fail err = ("parse", StageFail
  { stageError = plain (T.pack err)
  , stageDetails = Nothing
  })
stage3ESuccess :: CST -> (Text, Stage)
stage3ESuccess tree = ("parse", StageSuccess
  { stageContent =
    (reshown tree)
    { json = AE.toJSON tree }
  , stageExtra = Nothing
  })
stage3DSuccess :: [Decl] -> (Text, Stage)
stage3DSuccess tree = ("parse", StageSuccess
  { stageContent =
    (reshown tree)
    { json = AE.toJSON tree }
  , stageExtra = Nothing
  })

stage4Fail :: String -> (Text, Stage)
stage4Fail err = ("elab", StageFail
  { stageError = plain (T.pack err)
  , stageDetails = Nothing
  })
stage4ESuccess :: Term -> (Text, Stage)
stage4ESuccess term = ("elab", StageSuccess
  { stageContent = formatsTerm term
  , stageExtra = Nothing
  })
stage4DSuccess :: Map.Map Name GlobalInfo -> (Text, Stage)
stage4DSuccess modul = ("elab", StageSuccess
  { stageContent = formatsModule modul
  , stageExtra = Nothing
  })

formatsTerm :: Term -> Formats
formatsTerm term = Formats
  { text = text
  , html = xmlEscape text
  , ansi = formatCore Ansi term
  , json = AE.toJSON term
  }
  where
  text = formatCore Plain term

formatsModule :: Map.Map Name GlobalInfo -> Formats
formatsModule modul = Formats
  { text = text
  , html = xmlEscape text
  , ansi = fmt Ansi
  , json = AE.toJSON modul
  }
  where
  text = fmt Plain
  fmt f = Map.toList modul & foldMap \(name, info) ->
    case info of
      DefnGlobal (GlobalDefn _ (GlobalTerm ty _) (GlobalTerm tm _)) ->
        nameText name <> " : " <> formatCore f ty <> "\n" <>
        nameText name <> " := " <> formatCore f tm <> "\n"
      _ -> mempty




fullSurfaceProcess :: String -> Text -> IO Stages
fullSurfaceProcess = startSurfaceProcess finishDecls finishExpr

startSurfaceProcess ::
  ([Decl] -> IO Stages) ->
  (CST -> IO Stages) ->
  String -> T.Text -> IO Stages
startSurfaceProcess onDecls onExpr filename contents = do
  let prelexed = runIdentity (P.runPT (prelex <* P.eof) WHITESPACE filename contents)
  catching "prelex" case prelexed of
    Left err -> pure [stage1Fail err]
    Right r -> (stage1Success r :) <$> do
      let tokenized = runIdentity (P.runPT (tokenize <* P.eof) Nothing filename r)
      catching "tokenize" case tokenized of
        Left err -> pure [stage2Fail err]
        Right ts -> (stage2Success ts :) <$> do
          let parsed = (Happy.parseDecls ts, Happy.parseExprInParens ts)
          catching "parse" case parsed of
            (Left err, Left _) -> pure [stage3Fail err]
            (Right decls, _) -> onDecls decls
            (_, Right expr) -> onExpr expr

finishExpr :: CST -> IO Stages
finishExpr expr =
  (stage3ESuccess expr :) <$> do
    tbl <- initTable
    catching "elab" do
      term <- Elab.runElabScoped tbl (Elab.elab Nothing expr)
      pure [stage4ESuccess term]

finishDecls :: [Decl] -> IO Stages
finishDecls decls =
  (stage3DSuccess decls :) <$> do
    tbl <- initTable
    catching "elab" do
      (modul, ()) <- Elab.runElabFull tbl (Elab.elaborateModule decls)
      pure [stage4DSuccess modul]




findTests :: FilePath -> IO [FilePath]
findTests rootDir = do
  Dir.doesDirectoryExist rootDir >>= \case
    False -> pure []
    True -> do
      children <- Dir.listDirectory rootDir
      join <$> for children \case
        "input.pudding" -> pure [rootDir]
        '.' : _ -> pure []
        [] -> pure []
        child -> do
          findTests $ rootDir </> child

saveTestIn :: FilePath -> Text -> Set.Set FilePath -> IO Stages
saveTestIn iodir contents selection = do
  Dir.createDirectoryIfMissing True iodir
  TIO.writeFile (iodir </> "input.pudding") contents
  (_status, stages, commit) <- runTestText iodir contents
  join $ commit selection
  pure stages

runTestIn :: FilePath -> IO (All, Stages, Set.Set FilePath -> IO (IO ()))
runTestIn iodir = do
  let input = iodir </> "input.pudding"
  contents <- TIO.readFile input
  runTestText iodir contents

runTestText :: FilePath -> Text -> IO (All, Stages, Set.Set FilePath -> IO (IO ()))
runTestText iodir contents = do
  initialResults <- fullSurfaceProcess iodir contents
  comparedResults <- for initialResults \(name, stage) -> do
    outputText     <- catchAny (Just <$> TIO.readFile (iodir </> (T.unpack name <> ".txt"))) mempty
    outputJsonText <- catchAny (Just <$> TIO.readFile (iodir </> (T.unpack name <> ".json"))) mempty
    outputJson <- case AE.eitherDecodeStrictText <$> outputJsonText of
      Just (Left e) -> error e
      Just (Right r) -> pure (Just r)
      Nothing -> pure Nothing
    fmap (name,) <$> checkStage stage outputText outputJson
  let
    notDiff = \case
      StageDiff {} -> False
      _ -> True
    save selection = saveTestOutput iodir selection comparedResults
  pure (All $ all (notDiff . snd . snd) comparedResults, snd <$> comparedResults, save)

saveTestOutput :: FilePath -> Set.Set FilePath -> [(StageStatus, (Text, Stage))] -> IO (IO ())
saveTestOutput iodir selection = foldMap \(status, (name, stage)) -> do
  let
    format = case stage of
      StageSuccess f _ -> (plain "", f)
      StageFail f _ -> (plain "", f)
      StageDiff _ [f0, f1] _ -> (f0, f1)
      _ -> error "Bad StageDiff"
    fnText = T.unpack name <> ".txt"
    fnJson = T.unpack name <> ".json"

    checkFormat :: forall a. Eq a => FilePath -> (Formats -> a) -> (FilePath -> a -> IO ()) -> IO (IO ())
    checkFormat filename getter writer = do
      case status of
        _ | not $ Set.member filename selection -> do
          Dir.doesFileExist (iodir </> filename) <&> \case
            True -> Dir.removeFile (iodir </> filename)
            False -> pure ()
        StageUnchanged -> mempty
        StageChanged | getter (fst format) == getter (snd format) -> mempty
        _ -> mempty <$ writer (iodir </> filename) (getter (snd format))
  fold
    [ checkFormat fnText text TIO.writeFile
    , checkFormat fnJson json \at -> BS.writeFile at . AEP.encodePretty
    ]

data StageStatus = StageNew | StageUnchanged | StageChanged

checkStage :: Stage -> Maybe Text -> Maybe AE.Value -> IO (StageStatus, Stage)
checkStage stage Nothing Nothing = pure (StageNew, stage)
checkStage stage mt mj = evaluate
  case (all (== text format) mt, all (== json format) mj) of
    (True, True) -> (StageUnchanged, stage)
    (_, _) -> (StageChanged, StageDiff Nothing [aggregated, format] aux)
  where
  format = case stage of
    StageSuccess f _ -> f
    StageFail f _ -> f
    StageDiff {} -> error "Unexpected StageDiff"
  aux = case stage of
    StageSuccess _ a -> a
    StageFail _ a -> a
    StageDiff {} -> error "Unexpected StageDiff"
  t = fromMaybe (text format) mt
  j = fromMaybe (json format) mj
  aggregated = Formats
    { html = xmlEscape t
    , ansi = t
    , text = t
    , json = j
    }
