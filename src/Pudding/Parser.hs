module Pudding.Parser where

import qualified Text.Parsec as P
import qualified Text.Parsec.Text as PT
import Data.Text (Text)
import Data.Functor (void)
import qualified Data.Text as T

type Parser = PT.Parser

pragma :: Text -> Parser ()
pragma name = void $ P.string' $ "%" <> T.unpack name
