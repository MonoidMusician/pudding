module Pudding.Types.Base where

import GHC.Base (Symbol)

-- Annotate a data field with a name
infixr 9 @::
type (@::) (s :: Symbol) t = t
