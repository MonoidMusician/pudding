module Pudding.Types.Monads.Prover where

import Pudding.Types.Monads
import Pudding.Types.Base (Fresh(..), UnifyMode, type (@::), nextFresh)
import Pudding.Types.Stack (Stack, pattern (:>), pattern Nil)
import Pudding.Core.Types (Eval, Term, Name, Ctx)
import Pudding.Core.Unify as U
import Pudding.Core.Eval as E
import Control.Monad.Trans.RWS.Strict (RWST)
import Control.Monad.Writer.Class (tell, censor, listen)
import Control.Monad.State.Class (get, gets, state, put, modify')
import Control.Monad.Reader.Class (ask, asks, local)
import Data.Monoid.Generic (GenericMonoid(..), GenericSemigroup(..))
import GHC.Generics (Generic)
import Data.Functor (void)
import Pudding.Types.Config (Universes, Config)
import qualified Pudding.Semantics.Universes.Fused as Universes
import Pudding.Core.Eval (EvalTypeCtx)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

newtype Prover t = Prover (RWST ProverR ProverW ProverS IO t)
  deriving newtype (Functor, Applicative, Monad)

data ProverS = ProverS
  { fresh :: Fresh
  , solns :: IntMap Eval
  }

data SolveState = SolveState
  -- the original context of the hole. TODO: globals? TODO: let?
  { solCtx :: !(Ctx ("ty" @:: Eval))
  , solTm :: !("tm" @:: Eval)
  , solTy ::  ("ty" @:: Eval) -- ^ lazy
  -- Instantiations / constraints
  , solInst :: [ ("ctx" @:: Stack ("value given" @:: Eval), "value achieved" @:: Eval) ]
  -- Callbacks? for filling in holes for deferred elaboration?
  }


data ProverR = ProverR
  { ctx :: EvalTypeCtx
  , cfg :: Config
  }

data ProverW = ProverW
  { universe :: Universes.Fused ()
  }
  deriving (Generic)
  deriving Monoid via GenericMonoid ProverW
  deriving Semigroup via GenericSemigroup ProverW

instance Constraining Prover where
  type Constraints Prover = ProverW
  constrain = Prover . tell
  constraintsFrom (Prover act) = (\(a, w) -> (w, a)) <$> Prover (listen act)

instance Unification Prover where
  fullSolve (Fresh var) value = Prover do
    gets (IntMap.lookup var . solns) >>= \case
      Nothing -> state \s -> (value, s { solns = IntMap.insert var value $ solns s })
      Just past -> do
        c <- asks (void . ctx)
        -- TODO/FIXME: unification!
        case U.conversionCheck c past value of
          False -> error "Unification inconsistency"
          True -> state \s -> (value, s { solns = IntMap.insert var value $ solns s })
  currentSolution (Fresh var) = Prover do
    gets (IntMap.lookup var . solns) >>= \case
      Nothing -> error $ "Missing unification variable: " <> show var
      Just currently -> pure currently

instance Checkpointing Prover where
  type Checkpoint Prover = ProverS
  checkpoint = Prover get
  rewind = Prover . put

instance Freshener Prover where
  freshen = Prover $ state \s -> (fresh s, s { fresh = nextFresh (fresh s) })

instance WithConfig Prover where
  getConfig = Prover $ asks cfg
