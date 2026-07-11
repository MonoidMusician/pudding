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
import Control.Exception (try, evaluate)
import Control.Monad.Error.Class (tryError)
import qualified Data.List as List
import Witherable (Filterable(mapMaybe))
import System.FilePath ((</>))
import Data.Traversable (for)
import Control.DeepSeq (force)
import qualified System.FilePath.Posix as Path.Posix

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

under :: FilePath -> T.Text -> FilePath
under base relative = base </> Path.Posix.makeRelative "/" (T.unpack relative)

main :: IO ()
main = do
  let port = 9344

  -- ./test/golden/
  let goldenTests = "." </> "test" </> "golden"

  asdf <- SW.findTests goldenTests
  print asdf
  -- (All succeeded, results, commit) <- SW.runTest "./test/golden/surface/syntax"
  -- join $ commit (Set.fromList ["prelex.txt", "prelex.json"])
  -- TIO.putStrLn $ reshowAs Ansi results

  Scotty.scottyOpts (getOpts port) do
    -- API requests
    Scotty.get "/api/surface/list" do
      testPaths <- liftIO $ SW.findTests goldenTests
      let tests = testPaths & mapMaybe (List.stripPrefix (goldenTests <> "/"))
      Scotty.json tests
    Scotty.post "/api/surface/load" do
      filename :: T.Text <- Scotty.jsonData
      result <- liftIO $
        tryError (TIO.readFile (under goldenTests filename </> "input.pudding"))
      case result of
        Left _ -> Scotty.status HTTP.notFound404
        Right contents -> Scotty.json contents
    Scotty.post "/api/surface/test" do
      Content { content, filename } :: Content <- Scotty.jsonData
      stages <- liftIO $ SW.fullSurfaceProcess (maybe "<input>" T.unpack filename) content
      Scotty.json stages
    Scotty.post "/api/surface/save" do
      Content { content, filename, extra } :: Content <- Scotty.jsonData
      let
        selected = case AE.fromJSON <$> extra of
          Just (AE.Success items) -> items
          _ -> Set.empty
      case filename of
        Nothing -> Scotty.status HTTP.badRequest400
        Just name | content == "" -> do
          _ <- liftIO $ tryError $ SW.deleteTest (under goldenTests name)
          Scotty.json ()
        Just name -> do
          result <- liftIO $ tryError $ SW.saveTestIn (under goldenTests name) content selected
          case result of
            Left err -> liftIO $ print err
            Right stages -> Scotty.json stages
    -- TODO: websocket
    Scotty.get "/api/surface/report" do
      tests <- liftIO do SW.findTests goldenTests
      results <- for tests \test -> do
        for (List.stripPrefix (goldenTests <> "/") test) \name -> do
          (content, All success, result, _commit) <- liftIO do
            evaluate . force =<< SW.runTestIn test
          pure (name, (content, success, result))
      Scotty.json results

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
