-- | Internalized names, so equality can be a simple pointer comparison.
module Pudding.Types.Name where

import Control.DeepSeq (NFData(rnf))
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Coerce (coerce)
import Data.IORef (IORef, readIORef, modifyIORef', newIORef)
import qualified Data.Map as Map
import Data.Set (Set, singleton)
import qualified Data.Text as T
import Data.Text (Text)
import GHC.Generics (Generic)
import GHC.StableName (StableName, hashStableName, makeStableName)
import Prettyprinter (Pretty(pretty))
import GHC.IO (evaluate, unsafePerformIO)
import qualified Data.Aeson as AE
import Data.Functor.Contravariant (Contravariant(contramap))
import qualified Data.Text.Internal as TI
import qualified Data.Text.Array as A
import GHC.Base (sizeofByteArray#, Int (I#))

data Name = Name { nameId :: !(StableName Text), nameText :: !Text }

instance AE.ToJSON Name where toJSON = AE.toJSON . nameText
instance AE.FromJSON Name where
  parseJSON = fmap internalizeG . AE.parseJSON
instance AE.ToJSONKey Name where
  toJSONKey = contramap nameText (AE.toJSONKey @Text)
instance AE.FromJSONKey Name where
  fromJSONKey = AE.FromJSONKeyText internalizeG

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

{-# NOINLINE globalTable #-}
globalTable :: IORef NameTable
globalTable = unsafePerformIO initTable

newTable :: NameTable
newTable = NameTable Map.empty

{-# NOINLINE mayCopy #-}
mayCopy :: Text -> Text
mayCopy t@(TI.Text (A.ByteArray b) 0 slice)
  | slice == I# (sizeofByteArray# b) = t
mayCopy t = T.copy t

internalize :: forall m. MonadIO m => IORef NameTable -> Text -> m Name
internalize ref search = liftIO do
  NameTable names <- readIORef ref
  case Map.lookup search names of
    Just found -> pure found
    Nothing -> do
      copied <- evaluate $ mayCopy search
      named <- makeStableName copied
      let made = Name named copied
      modifyIORef' ref $ coerce $ Map.insert copied made
      pure made

{-# NOINLINE internalizeG #-}
internalizeG :: Text -> Name
internalizeG search = unsafePerformIO (internalize globalTable search)

-- A canonical name, that is merged during unification
data CanonicalName = CanonicalName
  { chosenName :: Name
  , allNames :: Set Name -- concatenated during unification
  }
  deriving (Generic, NFData, AE.ToJSON, AE.FromJSON)

canonicalName :: Name -> CanonicalName
canonicalName = CanonicalName <*> singleton

instance Semigroup CanonicalName where
  l <> r = CanonicalName
    { chosenName = chosenName l
    , allNames = allNames l <> allNames r
    }
