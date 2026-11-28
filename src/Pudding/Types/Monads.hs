{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances, DefaultSignatures, ImpredicativeTypes #-}
{-# HLINT ignore "Eta reduce" #-}
module Pudding.Types.Monads where

import Pudding.Types.Config (Config)
import GHC.Base (Symbol)
import Data.Text (Text)
import Pudding.Core.Types
import Data.Pair (Pair)
import Control.Monad ((<=<))
import Control.Monad.State.Strict (StateT(..), MonadTrans (lift), MonadState (state, get, put), evalStateT, MonadIO, mapStateT)
import Control.Monad.Reader.Class (MonadReader)
import Control.Monad.Error.Class (MonadError (catchError))
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
import Control.Monad.Trans.Cont (ContT, mapContT)
import Pudding.Types.Monads.Cont1T (Cont1T (Cont1T), mapCont1T, runCont1pT, adaptCont1)
import Pudding.Types.Monads.Errors (ProverE)
import qualified Pudding.Core.Printer as Printer
import Pudding.Types.Monads.Types (AfterSolve, UVReeval)

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
  default freshen :: (m ~ t n, MonadTrans t, Freshener n) => m Fresh
  freshen = lift freshen


-- Reader-like
class Monad m => WithConfig m where
  getConfig :: m Config
  default getConfig :: (m ~ t n, MonadTrans t, WithConfig n) => m Config
  getConfig = lift getConfig


-----------------------
-- Semantics for DTT --
-----------------------
-- Reader-like
class Monad m => Scoping m where
  -- this may incorporate updated globals each time
  askCtx :: m EvalTypeCtx
  withCtx :: forall r. EvalTypeCtx -> m r -> m r
  bindVar :: forall r. Binder -> ("type" @:: Eval, "value" @:: Eval) -> m r -> m r

  default askCtx :: (m ~ t n, MonadTrans t, Scoping n) => m EvalTypeCtx
  askCtx = lift askCtx
  default withCtx :: (m ~ t n, MonadInvmap t, Scoping n) => forall r. EvalTypeCtx -> m r -> m r
  withCtx ctx = invmapMonad (withCtx ctx)
  default bindVar :: (m ~ t n, MonadInvmap t, Scoping n) => forall r. Binder -> ("type" @:: Eval, "value" @:: Eval) -> m r -> m r
  bindVar bdr tyval = invmapMonad (bindVar bdr tyval)


bindNeut :: forall m r. Scoping m => Metadata -> Binder -> ("type" @:: Eval) -> (Level -> Eval -> m r) -> m r
bindNeut meta bdr ty inner = do
  runCont1pT (bindNeut1 meta bdr ty)
    (uncurry inner)

bindNeut1 :: forall m r. Scoping m => Metadata -> Binder -> ("type" @:: Eval) -> Cont1T r m (Level, Eval)
bindNeut1 meta bdr ty = do
  lvl <- Level <$> ctxDepth
  let neut = ENeutralVar meta lvl Nil
  (lvl, neut) <$ adaptCont1 (bindVar bdr (ty, neut))

ctxDepth :: Scoping m => m Int
ctxDepth = size <$> askCtx

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

bindClosure :: Scoping m => Binder -> ScopedTerm -> m Closure
bindClosure bdr body = do
  ctx <- askEvalCtx
  pure $ Closure ctx bdr body

printCore :: Scoping m => Term -> m Text
printCore term = do
  depth <- ctxDepth
  pure $ Printer.formatCoreFrom Printer.Plain depth term

class Scoping m => Evaling m where
  eval  :: HasCallStack => Term -> m Eval
  quote :: HasCallStack => Eval -> m Term
  -- unification variables
  -- may be a no-op, may be constant (reader-like),
  -- or may be the full stateful apparatus
  currentSolutions :: HasCallStack => m (Fresh -> Maybe UVReeval)
  univarsType      :: HasCallStack => m (Fresh -> UVReeval)
  univarsLocals    :: HasCallStack => m (Fresh -> EvalTypeCtx)
  progressGlobal :: Eval -> m Eval
  forceGlobal :: Eval -> m (Maybe Eval)
  forceNeutral :: Eval -> m (Maybe Eval)

  default eval :: (m ~ t n, MonadTrans t, Evaling n) => HasCallStack => Term -> m Eval
  eval = lift . eval
  default quote :: (m ~ t n, MonadTrans t, Evaling n) => HasCallStack => Eval -> m Term
  quote = lift . quote
  default currentSolutions :: (m ~ t n, MonadTrans t, Evaling n) => HasCallStack => m (Fresh -> Maybe UVReeval)
  currentSolutions = lift currentSolutions
  default univarsType      :: (m ~ t n, MonadTrans t, Evaling n) => HasCallStack => m (Fresh -> UVReeval)
  univarsType = lift univarsType
  default univarsLocals    :: (m ~ t n, MonadTrans t, Evaling n) => HasCallStack => m (Fresh -> EvalTypeCtx)
  univarsLocals = lift univarsLocals
  default progressGlobal :: (m ~ t n, MonadTrans t, Evaling n) => Eval -> m Eval
  progressGlobal = lift . progressGlobal
  default forceGlobal :: (m ~ t n, MonadTrans t, Evaling n) => Eval -> m (Maybe Eval)
  forceGlobal = lift . forceGlobal
  default forceNeutral :: (m ~ t n, MonadTrans t, Evaling n) => Eval -> m (Maybe Eval)
  forceNeutral = lift . forceNeutral

currentSolution :: Evaling m => HasCallStack => Fresh -> m (Maybe UVReeval)
currentSolution which = do
  sols <- currentSolutions
  pure $ sols which

univarType :: Evaling m => HasCallStack => Fresh -> m UVReeval
univarType which = do
  tyFor <- univarsType
  pure $ tyFor which

univarLocals :: Evaling m => HasCallStack => Fresh -> m EvalTypeCtx
univarLocals which = do
  localsFor <- univarsLocals
  pure $ localsFor which

globalEval :: Evaling m => HasCallStack => Term -> m GlobalTerm
globalEval t = GlobalTerm <$> pure t <*> eval t

globalQuote :: Evaling m => HasCallStack => Eval -> m GlobalTerm
globalQuote e = GlobalTerm <$> quote e <*> pure e

class MonadTrans t => MonadInvmap t where
  invmapMonad :: forall m. (forall r. m r -> m r) -> (forall r. t m r -> t m r)
  default invmapMonad :: MonadCovmap t => forall m. (forall r. m r -> m r) -> (forall r. t m r -> t m r)
  invmapMonad = covmapMonad
class MonadInvmap t => MonadCovmap t where
  covmapMonad :: forall m n. (forall r. m r -> n r) -> (forall r. t m r -> t n r)

instance MonadCovmap (StateT s) where covmapMonad f = mapStateT f
instance MonadCovmap (ReaderT r) where covmapMonad f = mapReaderT f
instance MonadCovmap (ExceptT e) where covmapMonad f = mapExceptT f
instance Monoid w => MonadCovmap (WriterT w) where covmapMonad f = mapWriterT f
instance MonadCovmap FreshT where covmapMonad f = mapFreshT f

instance MonadInvmap (StateT s)
instance MonadInvmap (ReaderT r)
instance MonadInvmap (ExceptT e)
instance Monoid w => MonadInvmap (WriterT w)
instance MonadInvmap FreshT
instance MonadInvmap (ContT c) where invmapMonad f = mapContT f
instance MonadInvmap (Cont1T c) where invmapMonad f = mapCont1T f




-- Writer-like

type ULevelEvidence = ()
class Monad m => Constraining m where
  type Constraints m
  constrain :: Constraints m -> m ()
  constraintsFrom :: m a -> m (Constraints m, a)

  constrainULevel :: Relationship ULevelEvidence -> m ()

-- State/IO-like
class (Constraining m, Typing m) => Unifier m where
  -- | Provide a solution for a univar (in its original context!) and provide
  -- | equations to check that involved it.
  unsafeSolve :: Fresh -> Eval -> m AfterSolve
  -- | Add a constraining equation that will be imposed when univars in it
  -- | make progress.
  -- TODO: variance? RSubsumesL?
  equate :: Equation -> m ()
  -- Create unification variables
  initUVType :: m (Fresh, Term, Eval)
  initUVTerm :: Eval -> m (Fresh, Term, Eval)

  default unsafeSolve :: (m ~ t n, MonadTrans t, Unifier n) => Fresh -> Eval -> m AfterSolve
  unsafeSolve which = lift . unsafeSolve which
  default equate :: (m ~ t n, MonadTrans t, Unifier n) => Equation -> m ()
  equate = lift . equate
  default initUVType :: (m ~ t n, MonadTrans t, Unifier n) => m (Fresh, Term, Eval)
  initUVType = lift initUVType
  default initUVTerm :: (m ~ t n, MonadTrans t, Unifier n) => Eval -> m (Fresh, Term, Eval)
  initUVTerm = lift . initUVTerm

-- Gather all monad state into a checkpoint, which may be scoped to a callback
-- (e.g. if the monad needs to track writes to arbitrary mutable variables,
-- it could do so only for the duration of the callback.)
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
  checkpointFor f = ExceptT $ checkpointFor $ ExceptT.runExceptT <$> f
  rewind = lift . rewind
instance (Checkpointing m, Monoid w) => Checkpointing (WriterT w m) where
  type Checkpoint (WriterT w m) = Checkpoint m
  checkpointFor f = WriterT $ checkpointFor $ runWriterT <$> f
  rewind = lift . rewind
instance Checkpointing m => Checkpointing (FreshT m) where
  type Checkpoint (FreshT m) = (Fresh, Checkpoint m)
  checkpointFor f = FreshT $ checkpointFor \chkpt ->
    case f chkpt of FreshT act -> act
  rewind (s, chkpt) = lift (rewind chkpt) *> FreshT (put s)

-- TODO: logging...

class (Freshener m, Evaling m) => Typing m where
  fatal :: HasCallStack => String -> m any
  context :: HasCallStack => String -> m r -> m r
  validate :: HasCallStack => Term -> m ("type" @:: Eval)
  validEval :: HasCallStack => Term -> m ("type" @:: Eval, "value" @:: Eval)
  reinfer :: HasCallStack => Term -> m ("type" @:: Eval)
  freshUniv :: m (ULevel, Term, Eval)
  -- freshUniv = do
  --   uLevel <- freshen
  --   uStage <- freshen
  --   let u = ULevel { uStage = uStage, uLevel = uLevel }
  --   pure (u, TUniv mempty u, EUniv mempty u)

  default fatal :: (m ~ t n, MonadInvmap t, Typing n) => HasCallStack => String -> m any
  fatal = lift . fatal
  default context :: (m ~ t n, MonadInvmap t, Typing n) => HasCallStack => String -> m r -> m r
  context c = invmapMonad (context c)
  default validate :: (m ~ t n, MonadInvmap t, Typing n) => HasCallStack => Term -> m ("type" @:: Eval)
  validate = lift . validate
  default validEval :: (m ~ t n, MonadInvmap t, Typing n) => HasCallStack => Term -> m ("type" @:: Eval, "value" @:: Eval)
  validEval = lift . validEval
  default reinfer :: (m ~ t n, MonadInvmap t, Typing n) => HasCallStack => Term -> m ("type" @:: Eval)
  reinfer = lift . reinfer
  default freshUniv :: (m ~ t n, MonadInvmap t, Typing n) => m (ULevel, Term, Eval)
  freshUniv = lift freshUniv

validateQuote :: Typing m => HasCallStack => Term -> m ("type" @:: Term)
validateQuote = quote <=< validate

-- | This is the full class needed for elaboration, including unification
-- | and subsumption.
class (Unifier m, Typing m, MonadError ProverE m) => Proving m where
  subsume :: UnifyMode r -> HasCallStack => Pair Eval -> m ("unified" @:: Pair Eval, "coercion" @:: Maybe r)

  default subsume :: (m ~ t n, MonadTrans t, Proving n) => UnifyMode r -> HasCallStack => Pair Eval -> m ("unified" @:: Pair Eval, "coercion" @:: Maybe r)
  subsume m = lift . subsume m


tryUnify :: Proving m => UnifyDir -> Pair Eval -> m (Either ProverE (Pair Eval))
tryUnify dir eLR = catchError (Right <$> unify dir eLR) (pure . Left)

-- | Unify two terms.
unify :: Proving m => UnifyDir -> Pair Eval -> m (Pair Eval)
unify dir eLR = fst <$> subsume (UnifyMode dir IdentitySubsumption Unifying) eLR

-- | Check whether two terms are convertible (definitionally equal up to
-- | universe levels), without doing any unification. This turns off learning
-- | any equations from the equalities.
conversionCheck :: Proving m => UnifyDir -> Pair Eval -> m Bool
conversionCheck dir eLR =
  catchError (True <$ subsume (UnifyMode dir IdentitySubsumption Checking) eLR)
    (const (pure False))



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


instance Scoping m => Scoping (StateT s m)
instance Scoping m => Scoping (ReaderT r m)
instance Scoping m => Scoping (ExceptT e m)
instance (Scoping m, Monoid w) => Scoping (WriterT w m)
instance Scoping m => Scoping (FreshT m)
instance Scoping m => Scoping (ContT c m)
instance Scoping m => Scoping (Cont1T c m)


instance Evaling m => Evaling (StateT s m)
instance Evaling m => Evaling (ReaderT r m)
instance Evaling m => Evaling (ExceptT e m)
instance (Evaling m, Monoid w) => Evaling (WriterT w m)
instance Evaling m => Evaling (FreshT m)
instance Evaling m => Evaling (ContT c m)
instance Evaling m => Evaling (Cont1T c m)


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

instance Typing m => Typing (StateT s m)
instance Typing m => Typing (ReaderT r m)
instance Typing m => Typing (ExceptT e m)
instance (Typing m, Monoid w) => Typing (WriterT w m)
instance Typing m => Typing (FreshT m)
instance Typing m => Typing (Cont1T c m)

instance (Monad m, Unifier m) => Unifier (StateT s m)
instance (Monad m, Unifier m) => Unifier (ReaderT r m)
instance (Monad m, Unifier m) => Unifier (ExceptT e m)
instance (Monad m, Unifier m, Monoid w) => Unifier (WriterT w m)
instance (Monad m, Unifier m) => Unifier (FreshT m)
instance (Monad m, Unifier m) => Unifier (Cont1T c m)

instance Proving m => Proving (StateT s m)
instance Proving m => Proving (ReaderT r m)
-- instance Proving m => Proving (ExceptT e m)
instance (Proving m, Monoid w) => Proving (WriterT w m)
instance Proving m => Proving (FreshT m)
instance Proving m => Proving (Cont1T c m)
