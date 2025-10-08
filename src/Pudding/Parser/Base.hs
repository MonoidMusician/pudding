module Pudding.Parser.Base where

import Control.DeepSeq (NFData(rnf))
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

instance NFData SourceSpan where
  rnf (SourceSpan b e) = b `seq` e `seq` ()
