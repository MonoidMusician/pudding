module Pudding.Types.Monads.Prover where

import Pudding.Types.Monads
import Pudding.Types.Monads.Types
import qualified Pudding.Types.Monads as M
import Pudding.Core.Types
import Pudding.Core.Unify as U
import Pudding.Core.Eval as E
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.RWS.Strict (RWST (runRWST, RWST))
import Control.Monad.Reader.Class (asks, MonadReader (local))
import Control.Monad.Writer.Class (tell, listen)
import Control.Monad.State.Class (get, gets, state, put, modify')
import GHC.Generics (Generic, Generically(..))
import Data.Function ((&))
import Data.Functor ((<&>))
import Pudding.Types.Config (Config, Field (dflt))
import qualified Pudding.Semantics.Universes.Fused as Universes
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Monoidal.Strict (MonoidalIntMap)
import qualified Data.IntMap.Monoidal.Strict as MonoidalIntMap
import Data.Pair (Pair(..))
import Control.Lens (review)
import qualified Pudding.Semantics.Universes.Fused as Fused
import Control.Monad.IO.Class (MonadIO (liftIO))
import qualified Data.Vector as Vector
import GHC.IO.Unsafe (unsafePerformIO)
import Control.Monad.Error.Class (MonadError (throwError, catchError))
import Control.Exception (throw)
import Pudding.Types.Monads.Errors (ProverE)
import GHC.IO (catchException)

newtype Prover t = Prover (RWST ProverR ProverW ProverS IO t)
  deriving newtype (Functor, Applicative, Monad, MonadFix)

data ProverS = ProverS
  { freshest :: {-# UNPACK #-} !Fresh
  , nextUV :: {-# UNPACK #-} !Fresh
  -- | Override the globals in the context
  , proofGlobals :: !(Maybe Globals)
  -- | The state of each unification variable
  , uvState :: !(IntMap UnivarState)
  -- | indexed by univar ID?
  , uvDeferred :: !(IntMap (Prover ()))
  -- | sparse array / arbitrary IDs
  , uvConstraints :: !(IntMap ("uvs involved" @:: IntSet, "equation ctx" @:: EvalTypeCtx, Equation))
  , uvConstraintsRev :: !("uv ID to" @:: MonoidalIntMap ("uvConstraints" @:: IntSet))
  }

-- Solve a variable fully and return constraints it is involved in,
-- so they can be checked/solved in turn.
--
-- Assumes that it has the correct type and that it refines the previous solution.
solveFully :: Fresh -> Eval -> Prover AfterSolve
solveFully (Fresh !i) !val = do
  st <- Prover get
  headEqns <- case IntMap.lookup i $ uvState st of
    Nothing -> error "Unknown univar"
    Just current -> do
      let
        updated = current
          { uvIrrelevant =
              -- If all variables are irrelevant already, no need to check
              if IntSet.size (uvIrrelevant current) == size (uvCtx current)
              then uvIrrelevant current
              else freeVarsOf $ Left val
          , uvTerm = val
          , uvStatus = UVProgressed
          }
      Prover $ put $! st
        { uvState = IntMap.insert i updated $ uvState st }
      pure $ uvHeadEqns current
  let
    -- Global equations that constrain this variable.
    -- Will be returned in an arbitrary order *after*
    -- the head equations, which are stored with the variable.
    globalEqns :: IntMap (IntSet, EvalTypeCtx, Equation)
    globalEqns =
      case MonoidalIntMap.lookup i (uvConstraintsRev st) of
        Nothing -> IntMap.empty
        Just relevant ->
          IntMap.intersection (uvConstraints st) $ IntMap.fromSet id $
            relevant <> headEqns
  Prover $ modify' \st' -> st' { uvState = IntMap.difference (uvState st') globalEqns }
  pure globalEqns

initUV :: Eval -> Prover (Fresh, Term, Eval)
initUV ty = do
  ctx <- askCtx
  which@(Fresh i) <- Prover do
    state \st -> (nextUV st, st { nextUV = nextFresh $ nextUV st })
  let val = ENeutralHole mempty which (Vector.fromList $ fmap (snd . snd) $ review stack $ ctxStack ctx) Nil
  tm <- M.quote val
  let
    entry = UVState
      { uvCtx = ctx
      , uvIrrelevant =
          if size ctx == 0
          then mempty
          else freeVarsOf $ Left val
      , uvTerm = val
      , uvType = ty
      , uvHeadEqns = IntSet.empty
      , uvNotify = mempty
      , uvStatus = UVUnsolved
      }
  Prover $ modify' \st -> st
    { uvState = IntMap.insert i entry $ uvState st }
  pure (which, tm, val)


-- Create a new constraint to check when the relevant variables are solved
equateGlobal :: Equation -> Prover Fresh
equateGlobal (l :# r) = do
  Fresh n <- freshen
  ctx <- M.askCtx
  -- FIXME: include uvs of the uvs' types?
  let mentioned = uvsOf (Left l) <> uvsOf (Left r)
  Prover $ modify' \s -> s
    { uvConstraints = IntMap.insert n (mentioned, ctx, l :# r) $ uvConstraints s
    , uvConstraintsRev = uvConstraintsRev s <>
        MonoidalIntMap.fromSet (const (IntSet.singleton n)) mentioned
    }
  pure (Fresh n)

equateHead :: "univar" @:: Fresh -> "constraint" @:: Fresh -> Prover ()
equateHead (Fresh i) (Fresh n) = do
  st <- Prover get
  updated <- case IntMap.lookup i $ uvState st of
    Nothing -> error "equateHead missing"
    Just current -> pure $
      current { uvHeadEqns = IntSet.insert n $ uvHeadEqns current }
  Prover $ put $! st
    { uvState = IntMap.insert i updated $ uvState st }

data ProverR = ProverR
  { proofCtx :: !EvalTypeCtx
  , proofCfg :: !Config
  -- TODO: cache for stuff
  }

data ProverW = ProverW
  { levels :: Universes.Fused ULevelEvidence
  -- , stages
  }
  deriving (Generic)
  deriving Monoid via Generically ProverW
  deriving Semigroup via Generically ProverW

runProverMonad :: forall m t. MonadIO m => Config -> Prover t -> m t
runProverMonad cfg (Prover act) = do
  let
    r = ProverR
      { proofCtx = Nil
      , proofCfg = cfg
      }
    s = ProverS
      { freshest = Fresh 0
      , nextUV = Fresh 0
      , proofGlobals = Nothing
      , uvState = IntMap.empty
      , uvDeferred = IntMap.empty
      , uvConstraints = IntMap.empty
      , uvConstraintsRev = MonoidalIntMap.empty
      }
  liftIO $ runRWST act r s <&> \(t, _, _) -> t

unsafeRunProver :: EvalTypeCtx -> Prover t -> t
unsafeRunProver ctx = unsafePerformIO . runProverMonad dflt . withCtx ctx

instance Constraining Prover where
  type Constraints Prover = ProverW
  constrain = Prover . tell
  constraintsFrom (Prover act) = (\(a, w) -> (w, a)) <$> Prover (listen act)
  constrainULevel rel = constrain $ mempty { levels = Fused.constraint rel }


modifyUnivar :: Fresh -> (Maybe UnivarState -> Prover (UnivarState, b)) -> Prover b
modifyUnivar (Fresh which) act = do
  (upd, ret) <- act =<< Prover do gets (IntMap.lookup which . uvState)
  Prover do
    ret <$ modify' \s -> s { uvState = IntMap.insert which upd (uvState s) }

instance Checkpointing Prover where
  type Checkpoint Prover = ProverS
  checkpointFor k = Prover get >>= k
  rewind = Prover . put

instance Freshener Prover where
  freshen = Prover do state \s -> (freshest s, s { freshest = nextFresh (freshest s) })

instance WithConfig Prover where
  getConfig = Prover do asks proofCfg



instance Scoping Prover where
  askCtx = Prover do
    ctx <- asks proofCtx
    globals <- gets proofGlobals
    case globals of
      Nothing -> pure ctx
      Just override -> pure ctx { ctxGlobals = override }
  withCtx newCtx (Prover inner) = Prover do
    inner & local \ctx -> ctx { proofCtx = newCtx }
  bindVar b tyval (Prover inner) = Prover do
    inner & local \ctx -> ctx { proofCtx = proofCtx ctx :> (b, tyval) }


instance Evaling Prover where
  eval tm = do
    ctx <- M.askEvalCtx
    pure $ E.eval ctx tm
  quote val = do
    ctx <- M.askQuoteCtx
    pure $ E.quote ctx val
  currentSolutions = Prover do
    -- TODO: return Nothing if the var is not solved?
    gets ((\vars (Fresh which) -> uvSolution =<< IntMap.lookup which vars) . uvState)
  univarsType = Prover do
    gets ((\vars (Fresh which) -> maybe (error "univarsType") uvTypeEval $ IntMap.lookup which vars) . uvState)
  univarsLocals = Prover do
    gets ((\vars (Fresh which) -> maybe (error "univarsLocals") uvCtx $ IntMap.lookup which vars) . uvState)
  progressGlobal val = do
    ctx <- M.askCtx
    pure $ E.progressGlobal ctx val
  forceGlobal val = do
    ctx <- M.askCtx
    pure $ E.forceGlobal ctx val
  forceNeutral val = do
    ctx <- M.askCtx
    sols <- currentSolutions
    pure $ E.forceNeutral ctx sols val


instance Typing Prover where
  fatal = error
  context _msg act = act

  validate = U.validate
  validEval tm = do
    ty <- U.validate tm
    val <- M.eval tm
    pure (ty, val)
  reinfer = U.reinfer

instance Unifying Prover where
  unsafeSolve = solveFully

  equate eqn = do
    n <- equateGlobal eqn
    case eqn of
      ENeutralHole _ whichL _ _ :# ENeutralHole _ whichR _ _ ->
        equateHead whichL n *> equateHead whichR n
      ENeutralHole _ whichL _ _ :# _ -> equateHead whichL n
      _ :# ENeutralHole _ whichR _ _ -> equateHead whichR n
      _ -> pure ()

  initUVTerm = initUV

instance Proving Prover where
  subsume = U.subsume

instance MonadIO Prover where
  liftIO = Prover . liftIO

instance Monoid t => Monoid (Prover t) where mempty = pure mempty
instance Semigroup t => Semigroup (Prover t) where (<>) = liftA2 (<>)

instance MonadError ProverE Prover where
  throwError = Prover . liftIO . throw
  catchError (Prover act) handler = Prover $ RWST \r s ->
    catchException @ProverE (runRWST act r s)
      \e -> runRWST (case handler e of Prover act2 -> act2) r s
