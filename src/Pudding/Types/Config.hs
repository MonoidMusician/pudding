module Pudding.Types.Config where

-- Import this module qualified!

data Config = Config
  { universes :: Universes
  , validation :: Validation
  }

class Field t where
  dflt :: t
  merge :: t -> t -> t

data Universes
  = TypeInType
  | Cumulative
  | Polymorphic

instance Field Universes where
  dflt = Polymorphic
  merge = const id

data Validation = Validation
  {
  }
