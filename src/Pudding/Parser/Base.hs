module Pudding.Parser.Base where

import GHC.Generics (Generic)
import Text.Parsec.Pos (SourcePos)

data SourceSpan = SourceSpan
  { spanBegin :: SourcePos
  , spanEnd :: SourcePos
  }
  deriving (Eq, Ord, Generic)

instance Semigroup SourceSpan where
  SourceSpan b1 e1 <> SourceSpan b2 e2 =
    SourceSpan (min b1 b2) (max e1 e2)
