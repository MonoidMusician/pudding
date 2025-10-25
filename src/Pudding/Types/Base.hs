module Pudding.Types.Base where

import GHC.Base (Symbol)
import Prettyprinter (Pretty)
import Control.DeepSeq (NFData)

-- Annotate a data field with a name
infixr 9 @::
type (@::) (s :: Symbol) t = t

-- Fresh integers.
-- E.g. for numbering typed holes
newtype Fresh = Fresh Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData)
