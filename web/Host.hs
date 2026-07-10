module Host where

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
import qualified Pudding.Surface.Web as SW
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Monoid (All(All))
import qualified Data.Set as Set
import Control.Monad (join)
import Data.Show.Reshow (reshowAs, Style (Ansi))
import Control.Exception (try)
import Control.Monad.Error.Class (tryError)
import qualified Data.List as List
import Witherable (Filterable(mapMaybe))

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

  asdf <- SW.findTests "./test/golden/"
  print asdf
  -- (All succeeded, results, commit) <- SW.runTest "./test/golden/surface/syntax"
  -- join $ commit (Set.fromList ["prelex.txt", "prelex.json"])
  -- TIO.putStrLn $ reshowAs Ansi results

  Scotty.scottyOpts (getOpts port) do
    -- API requests
    Scotty.get "/api/surface/list" do
      testPaths <- liftIO $ SW.findTests "./test/golden/"
      let tests = testPaths & mapMaybe (List.stripPrefix "./test/golden/")
      Scotty.json tests
    Scotty.post "/api/surface/load" do
      filename :: T.Text <- Scotty.jsonData
      result <- liftIO $
        tryError (TIO.readFile ("./test/golden/" <> T.unpack filename <> "/input.pudding"))
      case result of
        Left _ -> Scotty.status HTTP.notFound404
        Right contents -> Scotty.json contents
    Scotty.post "/api/surface/test" do
      Content { content, filename } :: Content <- Scotty.jsonData
      stages <- liftIO $ SW.fullSurfaceProcess (maybe "<input>" T.unpack filename) content
      Scotty.json stages
    Scotty.post "/api/surface/save" do
      liftIO $ TIO.putStrLn "save!"
      Content { content, filename, extra } :: Content <- Scotty.jsonData
      let
        selected = case AE.fromJSON <$> extra of
          Just (AE.Success items) -> items
          _ -> Set.empty
      case filename of
        Nothing -> Scotty.status HTTP.badRequest400
        Just name -> do
          result <- liftIO $ tryError do SW.saveTestIn ("./test/golden/" <> T.unpack name) content selected
          case result of
            Left err -> liftIO $ print err
            Right stages -> Scotty.json stages

    -- Everything else: static files
    Scotty.get "/" do
      Scotty.redirect "/index.html"
    Scotty.get (Scotty.regex "^/(.*?([.][^.]+))$") do
      path <- Scotty.pathParam "1" -- includes extension
      ext  <- Scotty.pathParam "2" -- just the extension
      case ext :: T.Text of
        ".js" -> Scotty.setHeader "Content-Type" "text/javascript"
        ".json" -> Scotty.setHeader "Content-Type" "application/json"
        ".html" -> Scotty.setHeader "Content-Type" "text/html"
        ".css" -> Scotty.setHeader "Content-Type" "text/css"
        _ -> pure ()
      Scotty.file $ "./web/static/" <> path
