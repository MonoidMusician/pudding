module Pudding.Surface.Surface where

import Prelude

import Pudding.Surface.Lexer hiding (demo)
import qualified Pudding.Surface.Happy as Happy

import qualified Data.Text as T
import Pudding.Types ()
import qualified Text.Parsec as P
import qualified Data.Text.IO.Utf8 as TIO
import Control.Monad.Identity (Identity (runIdentity))
import Data.Show.Reshow (reshow)

demo :: IO ()
demo = do
  TIO.putStrLn ""
  line <- TIO.getLine
  let prelexed = runIdentity (P.runPT (prelex <* P.eof) WHITESPACE "<input>" line)
  case prelexed of
    Left err -> TIO.putStrLn $ T.pack $ show err
    Right r -> do
      TIO.putStrLn $ reshow r
      let tokenized = runIdentity (P.runPT (tokenize <* P.eof) Nothing "<input>" r)
      case tokenized of
        Left err -> TIO.putStrLn $ T.pack $ show err
        Right ts -> do
          TIO.putStrLn $ reshow ts
          let parsed = Happy.parseExpr ts
          case parsed of
            Left err -> TIO.putStrLn $ T.pack $ "Error at " <> err
            Right cst -> do
              TIO.putStrLn $ reshow cst
  demo

