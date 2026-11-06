module Pudding.Types.Monads.Prover where

import Pudding.Types.Monads
import qualified Pudding.Types.Monads as M
import Pudding.Core.Types
import Pudding.Core.Unify as U
import Pudding.Core.Eval as E
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.RWS.Strict (RWST (runRWST))
import Control.Monad.Reader.Class (asks, MonadReader (local))
import Control.Monad.Writer.Class (tell, listen)
import Control.Monad.State.Class (get, gets, state, put, modify')
import GHC.Generics (Generic, Generically(..))
import Data.Function ((&))
import Data.Functor ((<&>), void)
import Pudding.Types.Config (Config)
import qualified Pudding.Semantics.Universes.Fused as Universes
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Monoidal.Strict (MonoidalIntMap)
import qualified Data.IntMap.Monoidal.Strict as MonoidalIntMap
import Data.Vector (Vector)
import Data.Pair (Pair(..), pattern Pair)
import Control.Lens (review)
import qualified Pudding.Semantics.Universes.Fused as Fused
import Data.Maybe (fromMaybe)
import Control.Monad.IO.Class (MonadIO (liftIO))
import qualified Data.Vector as Vector

newtype Prover t = Prover (RWST ProverR ProverW ProverS IO t)
  deriving newtype (Functor, Applicative, Monad, MonadFix)

data ProverS = ProverS
  { freshest :: {-# UNPACK #-} !Fresh
  , uvState :: !(IntMap UnivarState)
  -- | indexed by univar ID?
  , uvDeferred :: !(IntMap (Prover ()))
  -- | sparse array / arbitrary IDs
  , uvConstraints :: !(IntMap ("uvs involved" @:: IntSet, Equation))
  , uvConstraintsRev :: !("uv ID to" @:: MonoidalIntMap ("uvConstraints" @:: IntSet))
  }

-- TODO: cache by referential identity
uvsOf :: Either Eval Term -> IntSet
uvsOf = summarize $ trivialSummarize
  { onNeutFocus = \case
      NHole _ (Fresh n) _ -> Append $ IntSet.singleton n
      _ -> Append mempty
  }

freeVarsOf :: Either Eval Term -> IntSet
freeVarsOf = summarize $ trivialSummarize
  { onNeutFocus = \case
      NVar _ (Level lvl) -> Append $ IntSet.singleton lvl
      _ -> Append mempty
  }

data UnivarState = UVState
  -- the original context of the hole. TODO: globals? TODO: let?
  { uvCtx :: !EvalTypeCtx
  -- which variables (Levels) are known to be irrelevant
  , uvIrrelevant :: !IntSet
  -- the value for the term itself and its type
  , uvTerm :: !("tm" @:: Eval)
  , uvType :: "ty" @:: Eval -- ^ lazy
  -- Partial equations (constraints with this unification variable as its head)
  , uvEqns :: Stack ("ctx" @:: Vector ("value given" @:: Eval), "projections" @:: Stack NeutPrj, "value achieved" @:: Eval)
  -- Callbacks? for filling in holes for deferred elaboration?
  , uvNotify :: IntSet -- into ProverS.uvDeferred
  }

data AfterSolve = AfterSolve
  { aftHeadEqns :: Stack Equation
  , aftGlobalEqns :: IntMap (IntSet, Equation)
  }

-- | Gather the equations as a list of pairs
aftEqns :: AfterSolve -> [Equation]
aftEqns d =
  review rstack (aftHeadEqns d)
    <>
  (snd <$> IntMap.toAscList (snd <$> aftGlobalEqns d))

-- Solve a variable fully and return constraints it is involved in,
-- so they can be checked/solved in turn.
--
-- Assumes that it has the correct type and that it refines the previous solution.
solveFully :: Fresh -> Eval -> Prover AfterSolve
solveFully (Fresh !i) !val = do
  st <- Prover get
  let
    -- Global equations that constrain this variable.
    -- Will be returned in an arbitrary order *after*
    -- the head equations, which are stored with the variable.
    globalEqns :: IntMap (IntSet, Equation)
    globalEqns =
      case MonoidalIntMap.lookup i (uvConstraintsRev st) of
        Nothing -> IntMap.empty
        Just relevant ->
          IntMap.intersection (uvConstraints st) $ IntMap.fromSet id relevant
  case IntMap.lookup i $ uvState st of
    Nothing -> do
      ctx <- Prover $ asks proofCtx
      tm <- M.quote val
      ty <- U.quickTermType tm
      let
        entry = UVState
          { uvCtx = ctx
          , uvIrrelevant =
              if size ctx == 0
              then mempty
              else freeVarsOf $ Left val
          , uvTerm = val
          , uvType = ty
          , uvEqns = Nil
          , uvNotify = mempty
          }
      Prover $ put $ st
        { uvState = IntMap.insert i entry $ uvState st }
      pure $ AfterSolve { aftHeadEqns = Nil, aftGlobalEqns = globalEqns }
    Just current -> do
      let
        updated = current
          { uvIrrelevant =
              -- If all variables are irrelevant already, no need to check
              if IntSet.size (uvIrrelevant current) == size (uvCtx current)
              then uvIrrelevant current
              else freeVarsOf $ Left val
          , uvTerm = val
          }
        hydrate locals prjs = ENeut $ Neutral
          (NHole mempty (Fresh i) locals)
          prjs
        headEqns = uvEqns current
          <&> \(locals, prjs, result) -> Pair (hydrate locals prjs) result
      Prover $ put $! st
        { uvState = IntMap.insert i updated $ uvState st }
      pure $ AfterSolve { aftHeadEqns = headEqns, aftGlobalEqns = globalEqns }

-- Create a new constraint to check when the relevant variables are solved
equateGlobal :: Equation -> Prover ()
equateGlobal (l :# r) = do
  Fresh i <- freshen
  let mentioned = uvsOf (Left l) <> uvsOf (Left r)
  Prover $ modify' \s -> s
    { uvConstraints = IntMap.insert i (mentioned, l :# r) $ uvConstraints s
    , uvConstraintsRev = uvConstraintsRev s <> MonoidalIntMap.fromSet (const (IntSet.singleton i)) mentioned
    }

equateHead :: Equation -> Prover ()
equateHead (focus :# result) = case focus of
  ENeut (Neutral (NHole _meta (Fresh i) locals) prjs) -> do
    st <- Prover get
    updated <- case IntMap.lookup i $ uvState st of
      Nothing -> error "equateHead"
      Just current -> pure $
        current { uvEqns = uvEqns current :> (locals, prjs, result) }
    Prover $ put $! st
      { uvState = IntMap.insert i updated $ uvState st }
  _ -> error "equateHead"

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
      , uvState = IntMap.empty
      , uvDeferred = IntMap.empty
      , uvConstraints = IntMap.empty
      , uvConstraintsRev = MonoidalIntMap.empty
      }
  liftIO $ runRWST act r s <&> \(t, _, _) -> t

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
  askCtx = Prover do asks proofCtx
  withCtx newCtx (Prover inner) = Prover do
    inner & local \ctx -> ctx { proofCtx = newCtx }
  bindVar b tyval (Prover inner) = Prover do
    inner & local \ctx -> ctx { proofCtx = proofCtx ctx :> (b, tyval) }


uvSolution :: UnivarState -> (Eval, Vector Eval -> Eval)
uvSolution current
  -- If every variable is irrelevant, the term does not depend on its local context
  | IntSet.size (uvIrrelevant current) == size (uvCtx current) =
      (uvTerm current, const (uvTerm current))
  | otherwise =
      (uvTerm current, \newLocals ->
        -- TODO: check if newLocals is all neutral or referentially equal?
        let
          -- Replace the locals in the stored context
          ctx = uvCtx current & mapCtx \_ (Level i) _old ->
            newLocals Vector.! i
        -- TODO: traverse Eval directly
        in E.eval ctx $ E.quote (void ctx) $ uvTerm current
      )

instance Evaling Prover where
  eval tm = do
    ctx <- M.askEvalCtx
    pure $ E.eval ctx tm
  quote val = do
    ctx <- M.askQuoteCtx
    pure $ E.quote ctx val
  currentSolutions = Prover do
    -- TODO: return Nothing if the var is not solved?
    gets ((\vars (Fresh which) -> uvSolution <$> IntMap.lookup which vars) . uvState)
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

instance Unifying Prover where
  unsafeSolve var val = do
    _ <- solveFully var val
    pure ()

instance Proving Prover where
  subsume = U.subsume

instance MonadIO Prover where
  liftIO = Prover . liftIO
