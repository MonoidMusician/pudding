module Pudding.Types.Monads.Prover where

import Pudding.Types.Monads
import Pudding.Types.Base (Fresh(..), type (@::), nextFresh)
import Pudding.Types.Stack (Stack, pattern (:>), pattern Nil)
import Pudding.Core.Types (Eval, Term, Name, Ctx, NeutPrj)
import Pudding.Core.Unify as U
import Pudding.Core.Eval as E
import Control.Monad.Trans.RWS.Strict (RWST)
import Control.Monad.Writer.Class (tell, censor, listen)
import Control.Monad.State.Class (get, gets, state, put, modify')
import Control.Monad.Reader.Class (ask, asks, local)
import GHC.Generics (Generic, Generically(..))
import Data.Functor (void)
import Pudding.Types.Config (Universes, Config)
import qualified Pudding.Semantics.Universes.Fused as Universes
import Pudding.Core.Eval (EvalTypeCtx)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)

newtype Prover t = Prover (RWST ProverR ProverW ProverS IO t)
  deriving newtype (Functor, Applicative, Monad)

data ProverS = ProverS
  { freshest :: {-# UNPACK #-} !Fresh
  , uvState :: !(IntMap UnivarState)
  , uvDeferred :: !(IntMap (Prover ()))
  , uvConstraints :: !(IntMap (IntSet, Eval, Eval))
  }

data UnivarState = UVState
  -- the original context of the hole. TODO: globals? TODO: let?
  { uvCtx :: !(Ctx ("ty" @:: Eval))
  -- which variables are possibly relevant, versus known to be irrelevant (False)
  , uvRelevant :: !(Ctx Bool)
  -- the value for the term itself and its type
  , uvTerm :: !("tm" @:: Eval)
  , uvType ::  ("ty" @:: Eval) -- ^ lazy
  -- Partial equations (constraints with this unification variable as its head)
  , uvEqns :: [ ("ctx" @:: Stack ("value given" @:: Eval), "projections" @:: Stack NeutPrj, "value achieved" @:: Eval) ]
  -- Callbacks? for filling in holes for deferred elaboration?
  , uvNotify :: IntSet -- into ProverS.uvDeferred
  , uvGlobal :: IntSet -- into ProverS.uvConstraints
  }

data ProverR = ProverR
  { proofCtx :: !EvalTypeCtx
  , proofCfg :: !Config
  }

data ProverW = ProverW
  { universe :: Universes.Fused ()
  }
  deriving (Generic)
  deriving Monoid via Generically ProverW
  deriving Semigroup via Generically ProverW

instance Constraining Prover where
  type Constraints Prover = ProverW
  constrain = Prover . tell
  constraintsFrom (Prover act) = (\(a, w) -> (w, a)) <$> Prover (listen act)


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
