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
  toJSON s = AE.object
    [ "spanBegin" AE..= enc (spanBegin s)
    , "spanEnd" AE..= enc (spanEnd s)
    ]
    where
    enc sp = AE.object
      [ "name" AE..= sourceName sp
      , "line" AE..= sourceLine sp
      , "col" AE..= sourceColumn sp
      ]
instance AE.FromJSON SourceSpan where
  parseJSON s = SourceSpan
    <$> dec "spanBegin"
    <*> dec "spanEnd"
    where
    dec field = do
      o <- AE.parseJSON s
      sp <- o AE..: field
      newPos
        <$> sp AE..: "name"
        <*> sp AE..: "line"
        <*> sp AE..: "col"

instance Semigroup SourceSpan where
  SourceSpan b1 e1 <> SourceSpan b2 e2 =
    SourceSpan (min b1 b2) (max e1 e2)

instance NFData SourceSpan where
  rnf (SourceSpan b e) = b `seq` e `seq` ()
