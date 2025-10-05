module Pudding (someFunc, parseAndBootGlobals) where

import Data.Text (Text)
import Pudding.Types (GlobalInfo, Name)
import Data.Map (Map)
import Pudding.Parser (declarations, runParser)
import Pudding.Unify (bootGlobals)
import GHC.IO (unsafePerformIO)

someFunc :: IO ()
someFunc = do
  putStrLn "someFunc"

parseAndBootGlobals :: Text -> Map Name GlobalInfo
parseAndBootGlobals source = unsafePerformIO do
  parsed <- runParser (bootGlobals <$> declarations) "<globals>" source
  case parsed of
    Left err -> error $ show err
    Right booted -> pure booted
