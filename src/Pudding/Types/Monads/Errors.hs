module Pudding.Types.Monads.Errors where

import Data.Text (Text)
import Data.Data (Data)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Control.Exception (Exception)



data ProverE = ProverE !Text
  deriving (Data, Show, Generic, NFData)

instance Exception ProverE
