module Pudding.Name where

import Data.Text (Text)
import Control.DeepSeq (NFData(rnf))
import qualified Data.Map as Map
import GHC.StableName (StableName, hashStableName, makeStableName)
import Data.IORef (IORef, readIORef, modifyIORef', newIORef)
import Data.Coerce (coerce)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Prettyprinter (Pretty(pretty))
import qualified Data.Text as T

data Name = Name !(StableName Text) !Text

instance Eq Name where
  Name n1 _ == Name n2 _ = n1 == n2
instance Ord Name where
  compare (Name n1 _) (Name n2 _) | n1 == n2 = EQ
  compare (Name n1 t1) (Name n2 t2) =
    case compare (hashStableName n1) (hashStableName n2) of
      EQ -> compare t1 t2
      c -> c
instance NFData Name where
  rnf name = seq name ()

instance Show Name where
  show (Name _ name) = T.unpack name

instance Pretty Name where
  pretty (Name _ name) = pretty name

newtype NameTable = NameTable (Map.Map Text Name)

initTable :: IO (IORef NameTable)
initTable = newIORef newTable

newTable :: NameTable
newTable = NameTable Map.empty

internalize :: forall m. MonadIO m => IORef NameTable -> Text -> m Name
internalize ref search = liftIO do
  NameTable names <- readIORef ref
  case Map.lookup search names of
    Just found -> pure found
    Nothing -> do
      named <- makeStableName search
      let made = Name named search
      modifyIORef' ref $ coerce $ Map.insert search made
      pure made
