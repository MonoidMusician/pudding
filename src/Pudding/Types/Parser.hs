module Pudding.Types.Parser where

import Control.DeepSeq (NFData(rnf))
import GHC.Generics (Generic)
import Text.Parsec.Pos (SourcePos, sourceName, sourceLine, sourceColumn, newPos)
import qualified Data.Aeson as AE

data SourceSpan = SourceSpan
  { spanBegin :: SourcePos
  , spanEnd :: SourcePos
  }
  deriving (Eq, Ord, Generic)

instance AE.ToJSON SourceSpan where
  toJSON s = AE.toJSON
    [ AE.toJSON
      [ sourceLine $ spanBegin s
      , sourceColumn $ spanBegin s
      , sourceLine $ spanEnd s
      , sourceColumn $ spanEnd s
      ]
    , AE.toJSON $ sourceName $ spanBegin s
    ]
instance AE.FromJSON SourceSpan where
  parseJSON s = do
    vs <- AE.parseJSON s
    case vs of
      ((l1,c1,l2,c2),n) -> pure do
        SourceSpan (newPos n l1 c1) (newPos n l2 c2)

instance Semigroup SourceSpan where
  SourceSpan b1 e1 <> SourceSpan b2 e2 =
    SourceSpan (min b1 b2) (max e1 e2)

instance NFData SourceSpan where
  rnf (SourceSpan b e) = b `seq` e `seq` ()
