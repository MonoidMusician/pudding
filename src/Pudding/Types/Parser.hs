module Pudding.Types.Parser where

import Control.DeepSeq (NFData(rnf))
import GHC.Generics (Generic)
import Text.Parsec.Pos (SourcePos, sourceName, sourceLine, sourceColumn, newPos, SourceName)
import qualified Data.Aeson as AE
import Data.Int (Int32, Int8)
import Data.Bits ( Bits((.|.), shiftR, (.&.), shiftL) )
import Control.Arrow ((&&&))
import Data.FastEq (FastEq(..))

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

-- | Join tab (Int8) and column (Int24) into an Int32.
newtype TabCol = MkTabCol Int32
  deriving (Generic)
  deriving newtype (Eq, Ord, NFData)

{-# COMPLETE TabCol #-}
pattern TabCol :: Int8 -> Int32 {- Int24 -} -> TabCol
pattern TabCol tab col <- MkTabCol
  ((fromIntegral . (`shiftR` 24)) &&& (.&. 0xFFFFFF) -> (tab, col))
  where
  TabCol tab col = MkTabCol (fromIntegral (tab `shiftL` 24) .|. col)

-- | A source position, tracking line indent too
data SrcPos = SrcPos
  { posLine :: {-# UNPACK #-} !Int32
  , posCol :: {-# UNPACK #-} !TabCol
  , posIndent :: {-# UNPACK #-} !TabCol
  , posName :: FastEq SourceName
  }
  deriving (Generic, NFData)
  deriving Eq via FastEq SrcPos
  deriving Ord via FastEq SrcPos

pattern SrcIndent :: Int32 -> TabCol -> FastEq SourceName -> SrcPos
pattern SrcIndent l c n <- SrcPos l c ((== c) -> True) n
  where
  SrcIndent l c n = SrcPos l c c n

incrTab :: TabCol -> TabCol
incrTab (TabCol t c) = TabCol (t+1) c
incrCol :: TabCol -> TabCol
incrCol (TabCol t c) = TabCol t (c+1)

advance :: Char -> SrcPos -> SrcPos
advance '\n' (SrcPos l _ _ n)  = SrcIndent (l+1) (TabCol 0 0) n
advance '\t' (SrcIndent l c n) = SrcIndent l (incrTab c) n
advance '\t' (SrcPos l c i n)  = SrcPos l (incrTab c) i n
advance ' '  (SrcIndent l c n) = SrcIndent l (incrCol c) n
advance _    (SrcPos l c i n)  = SrcPos l (incrCol c) i n

-- | A source span, tracking starting line indent and minimum line indent.
data SrcSpan = SrcSpan
  { spanStartLine :: {-# UNPACK #-} !Int32
  , spanStartCol :: {-# UNPACK #-} !TabCol
  , spanFinLine :: {-# UNPACK #-} !Int32
  , spanFinCol :: {-# UNPACK #-} !TabCol

  , spanStartIndent :: {-# UNPACK #-} !TabCol
  , spanFinIndent :: {-# UNPACK #-} !TabCol
  , spanMinIndent :: {-# UNPACK #-} !TabCol

  , spanName :: FastEq SourceName
  }
  deriving (Generic, NFData)
  deriving Eq via FastEq SrcSpan
  deriving Ord via FastEq SrcSpan

spanStart :: SrcSpan -> (Int32, TabCol)
spanStart !s = (spanStartLine s, spanStartCol s)

spanFin :: SrcSpan -> (Int32, TabCol)
spanFin !s = (spanFinLine s, spanFinCol s)

instance Semigroup SrcSpan where
  s1 <> s2 | spanName s1 /= spanName s2 = s1
  s1 <> s2 = SrcSpan ssl ssc sfl sfc
    ssi sfi
    (min (spanMinIndent s1) (spanMinIndent s2))
    (spanName s1)
    where
    ((ssl, ssc), ssi) = minDecide (spanStart s1, spanStartIndent s1) (spanStart s2, spanStartIndent s2)
    ((sfl, sfc), sfi) = maxDecide (spanFin s1, spanFinIndent s1) (spanFin s2, spanFinIndent s2)

minDecide :: forall o t. Ord o => (o, t) -> (o, t) -> (o, t)
minDecide (o1, t) (o2, _) | o1 <= o2 = (o1, t)
minDecide _ (o2, t) = (o2, t)

maxDecide :: forall o t. Ord o => (o, t) -> (o, t) -> (o, t)
maxDecide (o1, _) (o2, t) | o2 >= o1 = (o2, t)
maxDecide (o1, t) _ = (o1, t)
