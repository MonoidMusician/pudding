-- | This is a read-only monad meant for double-checking.
module Pudding.Types.Monads.Verifier where

import Data.Functor (void)
import Control.Monad.Error.Class (MonadError (throwError))
import Data.Functor.Identity (Identity)


class Monad m => MayCheck e m where
  mayCheck :: forall r. (MonadError e m => m r) -> m (Maybe r)

instance MayCheck e Identity where
  mayCheck _ = pure Nothing

instance MayCheck e (Either e) where
  mayCheck m = Just <$> m


thingy :: forall m. MayCheck String m => m ()
thingy = do
  void $ mayCheck do
    throwError ("test" :: String)
  thingy
  pure ()

