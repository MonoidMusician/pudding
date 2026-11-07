{-# LANGUAGE UndecidableInstances #-}
module Pudding.Types.Monads.Cont1T where

import Control.Monad (ap, join, (<=<))
import Control.Concurrent (newMVar, readMVar, newEmptyMVar, putMVar, swapMVar, takeMVar)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Reader.Class (MonadReader (ask, local))
import Control.Monad.Trans.Class (MonadTrans (lift))
import Control.Monad.Error.Class (MonadError (throwError, catchError))
import Control.Monad.Writer.Class (MonadWriter (tell, listen, pass))
import Control.Monad.State.Class (MonadState (get, put))
import Data.Functor ((<&>))
import Data.Bifunctor (Bifunctor(first))


-- Linear continuation monad

{-
ContT \(produce :: x -> m r) -> do
  value <- obtain
  tweak $ produce value

ContT f >>= g = ContT \final -> do
  f \intermediate ->
    case g intermediate of
      ContT next -> next final

Cont1T do
  value <- obtain
  pure (tweak, value)
-}

data Memoizer m = Memoizer { useMemoizer :: forall r. m r -> m (m r) }

noMemoizer :: forall m. Applicative m => Memoizer m
noMemoizer = Memoizer pure

memoizerIO :: forall m. MonadIO m => Memoizer m
memoizerIO = Memoizer memoizeIO

memoizeIO :: forall m1 m2 r. (MonadIO m1, MonadIO m2) => m1 r -> m2 (m1 r)
memoizeIO act = liftIO do
  getter <- newEmptyMVar @(m1 r)
  putMVar getter =<< do
    v <- newMVar @(Maybe r) Nothing
    pure do
      -- Temporarily take the MVar just to ensure that there is only one writer
      r <- liftIO (takeMVar v) >>= \case
        Just r  -> pure r
        -- Run the computation if needed; leave the MVar empty if this fails
        Nothing -> act
      liftIO $ r <$ do
        -- Put (back) the MVar
        putMVar v (Just r)
        -- And bypass the MVar entirely now
        swapMVar getter (pure r)
  pure $ join $ liftIO $ readMVar getter


-- | This is the space of linear functions `m r -> m r`, that linearly transform
-- | a monad `m` on a known result type `r`.
-- |
-- | Two things make this linear:
-- | - The `forall c.` skolem ensures that the transformation actually calls
-- |   the provided `m (c, r)` (or crashes; nothing you can do about that).
-- | - The provided `m (c, r)` should be memoized, so that side effects run
-- |   the first time, only, and the result is cached in case it is called again.
-- |
-- | Currently this is only provided for `IO` through `MVar`.
data Tweak r m = Tweak (Memoizer m -> forall i o. ((r -> m r) -> i -> o) -> m i -> m o) | NoTweak

tweaks :: forall r m i o. Applicative m => Memoizer m -> Tweak r m -> ((r -> m r) -> i -> o) -> m i -> m o
tweaks m (Tweak f) t = f m t
tweaks _ NoTweak t = fmap (t pure)

tweak :: forall r m. Monad m => Memoizer m -> Tweak r m -> m r -> m r
tweak m (Tweak f) act = join $ f m id act
tweak _ NoTweak act = act

posttweak :: Monad m => (r -> m r) -> Tweak r m -> Tweak r m
posttweak f NoTweak = Tweak \_ io act -> io f <$> act
posttweak f (Tweak orig) = Tweak \m io act ->
  orig m (\g -> io (f <=< g)) act

instance Monad m => Semigroup (Tweak r m) where
  NoTweak <> m = m
  m <> NoTweak = m
  -- Assume `act` is already memoized, but memoize `f` before performing `g`
  Tweak g <> Tweak f = Tweak \m io act -> do
    g m (\x (y, i) -> io (x <=< y) i) =<< useMemoizer m (f m (,) act)
instance Monad m => Monoid (Tweak r m) where
  mempty = NoTweak


-- | A linear continuation monad.
newtype Cont1T r m t = Cont1T (Memoizer m -> m (Tweak r m, t))
  deriving (Functor)


instance Monad m => Applicative (Cont1T r m) where
  pure = Cont1T . pure . pure . (mempty @(Tweak r m),)
  (<*>) = ap

instance Monad m => Monad (Cont1T r m) where
  Cont1T act1 >>= g = Cont1T \m -> do
    (acc1, x) <- act1 m
    act2 <- case g x of Cont1T act2 -> useMemoizer m (act2 m)
    first (acc1 <>) <$> tweaks m acc1 (const id) act2

runCont1TIO :: MonadIO m => Cont1T r m t -> (t -> m r) -> m r
runCont1TIO = runCont1T memoizerIO

runCont1T :: Monad m => Memoizer m -> Cont1T r m t -> (t -> m r) -> m r
runCont1T m act f = evalCont1T m (act >>= lift . f)

runCont1pT :: Monad m => Cont1T r m t -> (t -> m r) -> m r
runCont1pT = runCont1T noMemoizer


evalCont1T :: Monad m => Memoizer m -> Cont1T r m r -> m r
evalCont1T m (Cont1T act) = do
  (acc, v) <- act m
  tweak m acc (pure v)

evalCont1pT :: Monad m => Cont1T r m r -> m r
evalCont1pT = evalCont1T noMemoizer


-- Provide a function to adapt the linear continuation
adaptCont :: Applicative m => (forall c. m c -> m c) -> Cont1T r m ()
adaptCont f = Cont1T \_ -> pure (Tweak \_ io x -> io pure <$> f x, ())

localizeCont :: MonadReader r m => (r -> r) -> Cont1T c m ()
localizeCont f = adaptCont (local f)

onResult :: Monad m => (r -> m r) -> Cont1T r m ()
onResult rmr = Cont1T \_ -> pure (Tweak \_ io x -> io rmr <$> x, ())

adaptOnResult :: Applicative m => (forall c. m c -> m (c, r -> m r)) -> Cont1T r m ()
adaptOnResult f = Cont1T \_ -> pure (Tweak \_ io x -> uncurry (flip io) <$> f x, ())

mapCont1T :: forall r m i o. (m (Tweak r m, i) -> m (Tweak r m, o)) -> Cont1T r m i -> Cont1T r m o
mapCont1T f (Cont1T g) = Cont1T (f . g)


instance MonadTrans (Cont1T r) where
  lift act = Cont1T \_ -> (NoTweak,) <$> act

instance MonadReader r m => MonadReader r (Cont1T c m) where
  ask = lift ask
  local f (Cont1T act) = Cont1T \m -> do
    local f (act m)
instance MonadError e m => MonadError e (Cont1T r m) where
  throwError = lift . throwError
  catchError (Cont1T act) runoff = Cont1T \m -> do
    catchError (act m) \e ->
      case runoff e of
        Cont1T recover -> recover m
instance MonadWriter w m => MonadWriter w (Cont1T r m) where
  tell = lift . tell
  listen (Cont1T act) = Cont1T \m -> do
    listen (act m) <&> \((x, y), z) -> (x, (y, z))
  pass (Cont1T act) = Cont1T \m -> do
    pass do act m  <&> \(x, (y, z)) -> ((x, y), z)
instance MonadState s m => MonadState s (Cont1T r m) where
  get = lift get
  put = lift . put

instance MonadIO m => MonadIO (Cont1T r m) where liftIO = lift . liftIO

instance (Monoid t, Monad m) => Monoid (Cont1T r m t) where mempty = pure mempty
instance (Semigroup t, Monad m) => Semigroup (Cont1T r m t) where (<>) = liftA2 (<>)
