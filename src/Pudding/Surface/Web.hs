module Pudding.Surface.Web where

import Prelude hiding (lex, error)

import Pudding.Surface.Lexer hiding (demo)
import qualified Pudding.Surface.Happy as Happy

import qualified Data.Text as T
import Pudding.Core.Types (initTable, GlobalDefn (GlobalDefn), GlobalTerm (GlobalTerm), Globals (globalDefns), globalsFrom, Name (nameText), Term)
import Pudding.Types.Stack (pattern Nil)
import qualified Text.Parsec as P
import qualified Data.Text.IO.Utf8 as TIO
import Control.Monad.Identity (Identity (runIdentity))
import Data.Show.Reshow (reshow)
import qualified Pudding.Surface.Elaborator as Elab
import Pudding.Core.Printer (Style (..), formatCore)
import GHC.IO (catch, evaluate)
import GHC.Exception (SomeException)
import qualified Pudding.Core.Unify as U
import qualified Pudding.Core.Eval as E
import Control.DeepSeq (force)
import qualified Pudding.Surface.Delaborator as D
import System.Environment (getArgs)
import qualified Data.Map.Strict as Map
import Data.Foldable (for_)
import Data.Text (Text)
import qualified Data.Aeson as AE
import GHC.Generics (Generic)
import qualified Text.Parsec as Parsec
import Data.Maybe (fromMaybe)
import Pudding.Surface.Parser (CST)

data Formats = Formats
  { text :: Text
  , html :: Text
  , ansi :: Text
  , json :: AE.Value
  } deriving (Generic, AE.ToJSON, AE.FromJSON)

data Stage
  = StageFail
    { stageError :: Formats
    , stageDetails :: Maybe AE.Value
    }
  | StageDiff
    { stageDiff :: Maybe Formats
    , stageParts :: [Formats] -- the elements of the diff
    , stageDiffAux :: Maybe AE.Value
    }
  | StageSuccess
    { stageContent :: Formats
    , stageExtra :: Maybe AE.Value
    }
  deriving (Generic, AE.ToJSON, AE.FromJSON)

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

catching :: Text -> IO [(Text, Stage)] -> IO [(Text, Stage)]
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
    (plain (T.pack (show lexemes)))
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
    (plain (T.pack (show tokens)))
    { json = AE.toJSON tokens }
  , stageExtra = Nothing
  })

stage3Fail :: String -> (Text, Stage)
stage3Fail err = ("parse", StageFail
  { stageError = plain (T.pack err)
  , stageDetails = Nothing
  })
stage3Success :: CST -> (Text, Stage)
stage3Success tree = ("parse", StageSuccess
  { stageContent =
    (plain (T.pack (show tree)))
    { json = AE.toJSON tree }
  , stageExtra = Nothing
  })

stage4Fail :: String -> (Text, Stage)
stage4Fail err = ("elab", StageFail
  { stageError = plain (T.pack err)
  , stageDetails = Nothing
  })
stage4Success :: Term -> (Text, Stage)
stage4Success term = ("elab", StageSuccess
  { stageContent = formatsTerm term
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

fullSurfaceProcess :: String -> T.Text -> IO [(Text, Stage)]
fullSurfaceProcess filename contents = do
  let prelexed = runIdentity (P.runPT (prelex <* P.eof) WHITESPACE filename contents)
  catching "prelex" case prelexed of
    Left err -> pure [stage1Fail err]
    Right r -> (stage1Success r :) <$> do
      let tokenized = runIdentity (P.runPT (tokenize <* P.eof) Nothing filename r)
      catching "tokenize" case tokenized of
        Left err -> pure [stage2Fail err]
        Right ts -> (stage2Success ts :) <$> do
          let parsed = Happy.parseExprInParens ts
          catching "parse" case parsed of
            Left err -> do
              pure [stage3Fail err]
            Right expr -> (stage3Success expr :) <$> do
              tbl <- initTable
              catching "elab" do
                term <- Elab.runElabScoped tbl (Elab.elab Nothing expr)
                pure [stage4Success term]
