{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}
module Pudding.Types.Monads where

import Pudding.Types.Config (Config)
import GHC.Base (Symbol)
import Data.Text (Text)
import Pudding.Core.Types
import Data.Pair (Pair)
import Control.Monad ((<=<))
import Control.Monad.State.Strict (StateT(..), MonadTrans (lift), MonadState (state, get, put), evalStateT, MonadIO, mapStateT)
import Control.Monad.Reader.Class (MonadReader)
import Control.Monad.Error.Class (MonadError)
import Control.Monad.Writer.Class (MonadWriter)
import Control.Monad.Trans.Reader (ReaderT(..), mapReaderT)
import Control.Monad.Trans.Except (ExceptT(..), mapExceptT)
import Control.Monad.Trans.Writer.Strict (WriterT(..), mapWriterT)
import Pudding.Semantics.Universes.Evidence (Relationship)
import GHC.Stack (HasCallStack)
import Data.Functor (void)
import qualified Data.Map as Map
import qualified Control.Monad.Trans.State.Strict as StateT
import Data.Tuple (swap)
import qualified Control.Monad.Trans.Except as ExceptT
import Data.Vector (Vector)
import Control.Monad.Trans.Cont (ContT, mapContT)
import Pudding.Types.Monads.Cont1T (Cont1T (Cont1T), mapCont1T, unsafeRunCont1T, adaptCont)

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
  withCtx :: forall r. EvalTypeCtx -> m r -> m r
  bindVar :: forall r. Binder -> ("type" @:: Eval, "value" @:: Eval) -> m r -> m r

bindNeut :: forall m r. Scoping m => Metadata -> Binder -> ("type" @:: Eval) -> (Level -> Eval -> m r) -> m r
bindNeut meta bdr ty inner = do
  unsafeRunCont1T (bindNeut1 meta bdr ty)
    (uncurry inner)

bindNeut1 :: forall m r. Scoping m => Metadata -> Binder -> ("type" @:: Eval) -> Cont1T r m (Level, Eval)
bindNeut1 meta bdr ty = do
  lvl <- Level <$> ctxSize
  let neut = ENeut (Neutral (NVar meta lvl) Nil)
  (lvl, neut) <$ adaptCont (bindVar bdr (ty, neut))

ctxSize :: Scoping m => m Int
ctxSize = size <$> askCtx

askEvalCtx :: Scoping m => m EvalCtx
askEvalCtx = fmap snd <$> askCtx

askQuoteCtx :: Scoping m => m QuoteCtx
askQuoteCtx = void <$> askCtx

askGlobals :: Scoping m => m Globals
askGlobals = ctxGlobals <$> askCtx

lookupType :: Scoping m => ("type name" @:: Name) -> m (Maybe GlobalTypeInfo)
lookupType name = Map.lookup name . globalTypes <$> askGlobals

lookupDefn :: Scoping m => ("defn name" @:: Name) -> m (Maybe GlobalDefn)
lookupDefn name = Map.lookup name . globalDefns <$> askGlobals

class Scoping m => Evaling m where
  eval  :: Term -> m Eval
  quote :: Eval -> m Term
  -- unification variables
  -- may be a no-op, may be constant (reader-like),
  -- or may be the full stateful apparatus
  currentSolutions :: m (Fresh -> Maybe (Eval, Vector Eval -> Eval))
  progressGlobal :: Eval -> m Eval
  forceGlobal :: Eval -> m (Maybe Eval)
  forceNeutral :: Eval -> m (Maybe Eval)

currentSolution :: Evaling m => Fresh -> m (Maybe (Eval, Vector Eval -> Eval))
currentSolution var = do
  sols <- currentSolutions
  pure $ sols var

-- Writer-like

type ULevelEvidence = ()
class Monad m => Constraining m where
  type Constraints m
  constrain :: Constraints m -> m ()
  constraintsFrom :: m a -> m (Constraints m, a)

  constrainULevel :: Relationship ULevelEvidence -> m ()

-- State/IO-like
class Constraining m => Unifying m where
  unsafeSolve :: Fresh -> Eval -> m ()
  equate :: Equation -> m ()

class Monad m => Checkpointing m where
  type Checkpoint m
  checkpointFor :: forall r. (Checkpoint m -> m r) -> m r
  rewind :: Checkpoint m -> m ()

instance Checkpointing m => Checkpointing (StateT s m) where
  type Checkpoint (StateT s m) = (s, Checkpoint m)
  checkpointFor f = StateT \s ->
    checkpointFor \chkpt ->
      runStateT (f (s, chkpt)) s
  rewind (s, chkpt) = lift (rewind chkpt) *> put s
instance Checkpointing m => Checkpointing (ReaderT r m) where
  type Checkpoint (ReaderT r m) = Checkpoint m
  checkpointFor f = ReaderT \r ->
    checkpointFor \chkpt -> runReaderT (f chkpt) r
  rewind = lift . rewind
instance Checkpointing m => Checkpointing (ExceptT e m) where
  type Checkpoint (ExceptT e m) = Checkpoint m
  checkpointFor f = ExceptT $ checkpointFor \chkpt ->
    case f chkpt of ExceptT act -> act
  rewind = lift . rewind
instance (Checkpointing m, Monoid w) => Checkpointing (WriterT w m) where
  type Checkpoint (WriterT w m) = Checkpoint m
  checkpointFor f = WriterT $ checkpointFor (runWriterT . f)
  rewind = lift . rewind
instance Checkpointing m => Checkpointing (FreshT m) where
  type Checkpoint (FreshT m) = (Fresh, Checkpoint m)
  checkpointFor f = FreshT $ checkpointFor \chkpt ->
    case f chkpt of FreshT act -> act
  rewind (s, chkpt) = lift (rewind chkpt) *> FreshT (put s)

-- logging...

class Evaling m => Typing m where
  fatal :: HasCallStack => String -> m any
  context :: HasCallStack => String -> m r -> m r
  validate :: Term -> m ("type" @:: Eval)
  validEval :: Term -> m ("type" @:: Eval, "value" @:: Eval)

validateQuote :: Typing m => Term -> m ("type" @:: Term)
validateQuote = quote <=< validate

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

mapFreshT :: (m (r, Fresh) -> n (r, Fresh)) -> FreshT m r -> FreshT n r
mapFreshT f (FreshT act) = FreshT (mapStateT f act)

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
instance Freshener m => Freshener (ContT c m) where freshen = lift freshen
instance Freshener m => Freshener (Cont1T c m) where freshen = lift freshen

instance WithConfig m => WithConfig (StateT s m) where getConfig = lift getConfig
instance WithConfig m => WithConfig (ReaderT r m) where getConfig = lift getConfig
instance WithConfig m => WithConfig (ExceptT e m) where getConfig = lift getConfig
instance (WithConfig m, Monoid w) => WithConfig (WriterT w m) where getConfig = lift getConfig
instance WithConfig m => WithConfig (ContT c m) where getConfig = lift getConfig
instance WithConfig m => WithConfig (Cont1T c m) where getConfig = lift getConfig


instance Scoping m => Scoping (StateT s m) where
  askCtx = lift askCtx
  withCtx = mapStateT . withCtx
  bindVar bdr tyval = mapStateT (bindVar bdr tyval)
instance Scoping m => Scoping (ReaderT r m) where
  askCtx = lift askCtx
  withCtx = mapReaderT . withCtx
  bindVar bdr tyval = mapReaderT (bindVar bdr tyval)
instance Scoping m => Scoping (ExceptT e m) where
  askCtx = lift askCtx
  withCtx = mapExceptT . withCtx
  bindVar bdr tyval = mapExceptT (bindVar bdr tyval)
instance (Scoping m, Monoid w) => Scoping (WriterT w m) where
  askCtx = lift askCtx
  withCtx = mapWriterT . withCtx
  bindVar bdr tyval = mapWriterT (bindVar bdr tyval)
instance Scoping m => Scoping (FreshT m) where
  askCtx = lift askCtx
  withCtx = mapFreshT . withCtx
  bindVar bdr tyval = mapFreshT (bindVar bdr tyval)
instance Scoping m => Scoping (ContT c m) where
  askCtx = lift askCtx
  withCtx = mapContT . withCtx
  bindVar bdr tyval = mapContT (bindVar bdr tyval)
instance Scoping m => Scoping (Cont1T c m) where
  askCtx = lift askCtx
  withCtx = mapCont1T . withCtx
  bindVar bdr tyval = mapCont1T (bindVar bdr tyval)


instance Evaling m => Evaling (StateT s m) where
  eval = lift . eval
  quote = lift . quote
  currentSolutions = lift currentSolutions
  progressGlobal = lift . progressGlobal
  forceGlobal = lift . forceGlobal
  forceNeutral = lift . forceNeutral
instance Evaling m => Evaling (ReaderT r m) where
  eval = lift . eval
  quote = lift . quote
  currentSolutions = lift currentSolutions
  progressGlobal = lift . progressGlobal
  forceGlobal = lift . forceGlobal
  forceNeutral = lift . forceNeutral
instance Evaling m => Evaling (ExceptT e m) where
  eval = lift . eval
  quote = lift . quote
  currentSolutions = lift currentSolutions
  progressGlobal = lift . progressGlobal
  forceGlobal = lift . forceGlobal
  forceNeutral = lift . forceNeutral
instance (Evaling m, Monoid w) => Evaling (WriterT w m) where
  eval = lift . eval
  quote = lift . quote
  currentSolutions = lift currentSolutions
  progressGlobal = lift . progressGlobal
  forceGlobal = lift . forceGlobal
  forceNeutral = lift . forceNeutral
instance Evaling m => Evaling (FreshT m) where
  eval = lift . eval
  quote = lift . quote
  currentSolutions = lift currentSolutions
  progressGlobal = lift . progressGlobal
  forceGlobal = lift . forceGlobal
  forceNeutral = lift . forceNeutral
instance Evaling m => Evaling (ContT c m) where
  eval = lift . eval
  quote = lift . quote
  currentSolutions = lift currentSolutions
  progressGlobal = lift . progressGlobal
  forceGlobal = lift . forceGlobal
  forceNeutral = lift . forceNeutral
instance Evaling m => Evaling (Cont1T c m) where
  eval = lift . eval
  quote = lift . quote
  currentSolutions = lift currentSolutions
  progressGlobal = lift . progressGlobal
  forceGlobal = lift . forceGlobal
  forceNeutral = lift . forceNeutral


instance (Monad m, Constraining m) => Constraining (StateT s m) where
  type Constraints (StateT s m) = Constraints m
  constrain = lift . constrain
  constraintsFrom = fmap swap . StateT.liftListen (fmap swap . constraintsFrom)
  constrainULevel = lift . constrainULevel
instance (Monad m, Constraining m) => Constraining (ReaderT r m) where
  type Constraints (ReaderT r m) = Constraints m
  constrain = lift . constrain
  constraintsFrom (ReaderT f) = ReaderT $ constraintsFrom . f
  constrainULevel = lift . constrainULevel
instance (Monad m, Constraining m) => Constraining (ExceptT e m) where
  type Constraints (ExceptT e m) = Constraints m
  constrain = lift . constrain
  constraintsFrom = fmap swap . ExceptT.liftListen (fmap swap . constraintsFrom)
  constrainULevel = lift . constrainULevel
instance (Monad m, Constraining m, Monoid w) => Constraining (WriterT w m) where
  type Constraints (WriterT w m) = Constraints m
  constrain = lift . constrain
  constraintsFrom (WriterT act) = WriterT $ (\(x, (y, z)) -> ((x, y), z)) <$> constraintsFrom act
  constrainULevel = lift . constrainULevel
instance (Monad m, Constraining m) => Constraining (FreshT m) where
  type Constraints (FreshT m) = Constraints m
  constrain = lift . constrain
  constraintsFrom (FreshT act) = FreshT (constraintsFrom act)
  constrainULevel = lift . constrainULevel
instance (Monad m, Constraining m) => Constraining (Cont1T c m) where
  type Constraints (Cont1T c m) = Constraints m
  constrain = lift . constrain
  constraintsFrom (Cont1T act) = Cont1T \m -> (\(x, (y, z)) -> (y, (x, z))) <$> constraintsFrom (act m)
  constrainULevel = lift . constrainULevel

instance Typing m => Typing (StateT s m) where
  fatal = lift . fatal
  context msg = mapStateT (context msg)
  validate = lift . validate
  validEval = lift . validEval
instance Typing m => Typing (ReaderT r m) where
  fatal = lift . fatal
  context msg = mapReaderT (context msg)
  validate = lift . validate
  validEval = lift . validEval
instance Typing m => Typing (ExceptT e m) where
  fatal = lift . fatal
  context msg = mapExceptT (context msg)
  validate = lift . validate
  validEval = lift . validEval
instance (Typing m, Monoid w) => Typing (WriterT w m) where
  fatal = lift . fatal
  context msg = mapWriterT (context msg)
  validate = lift . validate
  validEval = lift . validEval
instance Typing m => Typing (FreshT m) where
  fatal = lift . fatal
  context msg = mapFreshT (context msg)
  validate = lift . validate
  validEval = lift . validEval
instance Typing m => Typing (Cont1T c m) where
  fatal = lift . fatal
  context msg = mapCont1T (context msg)
  validate = lift . validate
  validEval = lift . validEval

instance (Monad m, Unifying m) => Unifying (StateT s m) where
  unsafeSolve = fmap lift . unsafeSolve
  equate = lift . equate
instance (Monad m, Unifying m) => Unifying (ReaderT r m) where
  unsafeSolve = fmap lift . unsafeSolve
  equate = lift . equate
instance (Monad m, Unifying m) => Unifying (ExceptT e m) where
  unsafeSolve = fmap lift . unsafeSolve
  equate = lift . equate
instance (Monad m, Unifying m, Monoid w) => Unifying (WriterT w m) where
  unsafeSolve = fmap lift . unsafeSolve
  equate = lift . equate
instance (Monad m, Unifying m) => Unifying (FreshT m) where
  unsafeSolve = fmap lift . unsafeSolve
  equate = lift . equate
instance (Monad m, Unifying m) => Unifying (Cont1T c m) where
  unsafeSolve = fmap lift . unsafeSolve
  equate = lift . equate

instance Proving m => Proving (StateT s m) where
  subsume = fmap lift . subsume
instance Proving m => Proving (ReaderT r m) where
  subsume = fmap lift . subsume
instance Proving m => Proving (ExceptT e m) where
  subsume = fmap lift . subsume
instance (Proving m, Monoid w) => Proving (WriterT w m) where
  subsume = fmap lift . subsume
instance Proving m => Proving (FreshT m) where
  subsume = fmap lift . subsume
instance Proving m => Proving (Cont1T c m) where
  subsume = fmap lift . subsume
