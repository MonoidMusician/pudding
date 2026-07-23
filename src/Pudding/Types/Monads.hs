{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}
module Pudding.Types.Monads where

import Pudding.Types.Config (Config)
import GHC.Base (Symbol)
import Data.Text (Text)
import Pudding.Types.Base (Fresh(..), type (@::))
import Pudding.Types.Stack (pattern Nil)
import Pudding.Core.Types (Eval (ENeut), Term, Name, Binder, Metadata, Level (Level), Neutral (Neutral), NeutFocus (NVar), UnifyDir, ULevel, UnifyMode, nextFresh, EvalCtx)
import Pudding.Core.Eval (EvalTypeCtx)
import Data.Pair (Pair)
import Control.Monad.State.Strict (StateT, MonadTrans (lift), MonadState (state, get, put), evalStateT, MonadIO)
import Control.Monad.Reader.Class (MonadReader)
import Control.Monad.Error.Class (MonadError)
import Control.Monad.Writer.Class (MonadWriter)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Writer.Strict (WriterT)

-----------------
-- Memoization --
-----------------


-- State/IO-like
class Internalize t m where -- no fundep!
  internalize :: t -> m t

class Memoizing k m where
  -- Function to memoize, allocates and returns a lookup function, and a release function
  memoizing :: (k -> v) -> m
    ( "lookup"  @:: k -> m v
    , "release" @:: m ()
    )

withMemo :: Monad m => Memoizing k m => (k -> v) -> ((k -> m v) -> m r) -> m r
withMemo fn action = do
  (memo, release) <- memoizing fn
  action memo <* release

class Memoized (what :: Symbol) v k m where
  -- Globally memoized in the monad
  memoized :: k -> m v

-- Technically we could do `m (Text -> Name)` for this...
mkName :: Memoized "Name" Name Text m => Text -> m Name
mkName = memoized @"Name"


----------
-- Misc --
----------


-- State/IO-like
class Monad m => Freshener m where
  freshen :: m Fresh


-- Reader-like
class Monad m => WithConfig m where
  getConfig :: m Config


-----------------------
-- Semantics for DTT --
-----------------------
-- Reader-like
class Monad m => Scoping m where
  -- this may incorporate updated globals each time
  askCtx :: m EvalTypeCtx
  ctxSize :: m Int
  bindVar :: forall r. Binder -> ("type" @:: Eval, "value" @:: Eval) -> m r -> m r

bindNeut :: forall m r. Scoping m => Metadata -> Binder -> ("type" @:: Eval) -> (Level -> Eval -> m r) -> m r
bindNeut meta bdr ty inner = do
  lvl <- Level <$> ctxSize
  let neut = ENeut (Neutral (NVar meta lvl) Nil)
  bindVar bdr (ty, neut) (inner lvl neut)

askEvalCtx :: Scoping m => m EvalCtx
askEvalCtx = fmap snd <$> askCtx

class Scoping m => Evaling m where
  eval  :: Term -> m Eval
  quote :: Eval -> m Term
  -- unification variables
  -- may be a no-op, may be constant (reader-like),
  -- or may be the full stateful apparatus
  currentSolution :: Fresh -> m (Maybe Eval)


-- Writer-like
class Constraining m where
  type Constraints m
  constrain :: Constraints m -> m ()
  constraintsFrom :: m a -> m (Constraints m, a)

  constrainULevel :: UnifyDir -> Pair ULevel -> m ()

-- State/IO-like
class Constraining m => Unifying m where
  -- unsafeSolve :: Fresh -> Eval -> m Eval
  -- currentSolution :: Fresh -> m Eval

class Checkpointing m where
  type Checkpoint m
  checkpointFor :: forall r. (Checkpoint m -> m r) -> m r
  rewind :: Checkpoint m -> m ()

-- logging...

class Evaling m => Typing m where
  validate :: Term -> m ("type" @:: Eval)
  validEval :: Term -> m ("type" @:: Eval, "value" @:: Eval)

class (Unifying m, Typing m) => Proving m where
  subsume :: UnifyMode r -> Pair Eval -> m ("unified" @:: Pair Eval, "coercion" @:: Maybe r)

-- MonadMask
-- class MonadError e m => Proving e m | m -> e where
--   typecheckEval ::
--     ("expected type" @:: Maybe Eval, "term" @:: Term) -> m
--     ("actual type" @:: Eval, "value" @:: Eval, "normalized" @:: Term)
--   tryUnify :: UnifyMode -> (Eval, Eval) -> m (Either e Eval)
--   unify :: UnifyMode -> (Eval, Eval) -> m Eval
--   conversionCheck :: UnifyMode -> (Eval, Eval) -> m Bool



-- class Proving e m => Elaborating e m where


---------------
-- Extras... --
---------------

class Serialize fmt m t where
  serialize :: t -> m fmt
class Deserialize fmt m t where
  deserialize :: fmt -> m t
-- Serializing can use memoization to maintain sharing/hashcons/backrefs or something
-- Deserializing can either be State-like (for backrefs) or Reader-like...


-- Monads


newtype FreshT m r = FreshT (StateT Fresh m r)
  deriving newtype (Functor, Applicative, Monad, MonadTrans, MonadIO)

instance Monad m => Freshener (FreshT m) where
  freshen = FreshT do state \s -> (s, nextFresh s)

evalFreshT :: Monad m => FreshT m r -> m r
evalFreshT (FreshT act) = evalStateT act (Fresh 0)

deriving newtype instance MonadReader r m => MonadReader r (FreshT m)
deriving newtype instance MonadError e m => MonadError e (FreshT m)
deriving newtype instance MonadWriter w m => MonadWriter w (FreshT m)
instance MonadState s m => MonadState s (FreshT m) where
  get = lift get
  put = lift . put


-- Instances

instance Freshener m => Freshener (StateT s m) where freshen = lift freshen
instance Freshener m => Freshener (ReaderT r m) where freshen = lift freshen
instance Freshener m => Freshener (ExceptT e m) where freshen = lift freshen
instance (Freshener m, Monoid w) => Freshener (WriterT w m) where freshen = lift freshen

instance WithConfig m => WithConfig (StateT s m) where getConfig = lift getConfig
instance WithConfig m => WithConfig (ReaderT r m) where getConfig = lift getConfig
instance WithConfig m => WithConfig (ExceptT e m) where getConfig = lift getConfig
instance (WithConfig m, Monoid w) => WithConfig (WriterT w m) where getConfig = lift getConfig


