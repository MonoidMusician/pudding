-- | This is a read-only monad meant for double-checking.
module Pudding.Types.Monads.Verifier where

import Pudding.Types.Monads
import Pudding.Types.Base (Fresh(..), UnifyMode, type (@::), nextFresh)
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


