module Main where

import Prelude hiding (lex)

import System.Environment (getArgs)
import qualified Data.Text as T
import qualified Data.Text.IO.Utf8 as TIO
import Control.Monad.IO.Class (MonadIO(liftIO))

import qualified Network.Wai.Handler.Warp as Warp
import qualified Web.Scotty as Scotty
import qualified Network.HTTP.Types as HTTP
import qualified Data.Aeson as AE
import GHC.Generics (Generic)
import Pudding.Surface.Surface (surfaceToCore)
import Pudding.Surface.Web (fullSurfaceProcessExpr, fullSurfaceProcessDecl)

getOpts :: Int -> Scotty.Options
getOpts port = Scotty.defaultOptions
  { Scotty.settings =
      Warp.setHost "127.0.0.1"
      $ Warp.setPort port
      $ Warp.defaultSettings
  }

data Content = Content
  { content :: T.Text
  , filename :: Maybe T.Text
  , extra :: Maybe AE.Value
  } deriving (Generic, AE.FromJSON, AE.ToJSON)

data Error = Error
  { error :: T.Text
  , details :: Maybe AE.Value
  } deriving (Generic, AE.FromJSON, AE.ToJSON)

main :: IO ()
main = do
  let port = 9344
  Scotty.scottyOpts (getOpts port) do

    -- API requests
    Scotty.post "/api/parse/surface/expr" do
      Content { content, filename } :: Content <- Scotty.jsonData
      stages <- liftIO $ fullSurfaceProcessExpr (maybe "<input>" T.unpack filename) content
      Scotty.json stages
      pure ()
    Scotty.post "/api/parse/surface/decl" do
      Content { content, filename } :: Content <- Scotty.jsonData
      stages <- liftIO $ fullSurfaceProcessDecl (maybe "<input>" T.unpack filename) content
      Scotty.json stages
      pure ()

    -- Everything else: static files
    Scotty.get (Scotty.regex "^/(.*?(\\..*?))$") do
      path <- Scotty.pathParam "1"
      ext :: T.Text <- Scotty.pathParam "2"
      case ext of
        ".js" -> Scotty.setHeader "Content-Type" "text/javascript"
        ".json" -> Scotty.setHeader "Content-Type" "application/json"
        ".html" -> Scotty.setHeader "Content-Type" "text/html"
        ".css" -> Scotty.setHeader "Content-Type" "text/css"
        _ -> pure ()
      Scotty.file $ "./web/static/" <> path
