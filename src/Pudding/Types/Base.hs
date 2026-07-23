module Pudding.Types.Base where

import GHC.Base (Symbol)
import Prettyprinter (Pretty)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import qualified Data.Aeson as AE

-- Annotate a data field with a name
infixr 9 @::
type (@::) (s :: Symbol) t = t

-- Fresh integers.
-- E.g. for numbering typed holes
newtype Fresh = Fresh Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData, AE.ToJSON, AE.FromJSON)

nextFresh :: Fresh -> Fresh
nextFresh (Fresh i) = Fresh (i + 1)

-- decl: Π (T : Type). T -> T
-- surface syntax usage: f Nat 42
-- decl: Π @{T : Type}. T -> T
-- surface syntax usage: f 42 = f @{T := Nat} 42
data Plicit = Explicit | Implicit
  deriving (Eq, Ord, Show, Generic, NFData, AE.ToJSON, AE.FromJSON)
