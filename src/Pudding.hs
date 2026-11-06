module Pudding (parseAndBootGlobals) where

import Data.Text (Text)
import GHC.IO (unsafePerformIO, evaluate)
import Pudding.Core.Parser (declarations, runParser)
import Pudding.Core.Types (Globals)
import Pudding.Core.Boot (bootGlobals)


parseAndBootGlobals :: Text -> Globals
parseAndBootGlobals source = unsafePerformIO do
  parsed <- runParser declarations "<globals>" source
  case parsed of
    Left err -> error $ show err
    Right booted -> evaluate $ bootGlobals booted
