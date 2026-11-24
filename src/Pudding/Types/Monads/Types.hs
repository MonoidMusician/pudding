module Pudding.Types.Monads.Types where

import Pudding.Core.Types
import Pudding.Core.Eval as E
import GHC.Generics (Generic)
import Data.Function ((&))
import Data.IntMap.Strict (IntMap)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Control.DeepSeq (NFData)



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
  , uvStatus :: UnivarStatus
  }

data UnivarStatus
  = UVUnsolved
  | UVProgressed
  | UVClosed
  deriving (Eq, Ord, Generic, NFData)

data AfterSolve = AfterSolve
  { aftHeadEqns :: Stack Equation
  , aftGlobalEqns :: IntMap (IntSet, Equation)
  }

uvSolution :: UnivarState -> Maybe (Eval, Vector Eval -> Eval)
uvSolution current
  | uvStatus current == UVUnsolved = Nothing
  -- If every variable is irrelevant, the term does not depend on its local context
  | IntSet.size (uvIrrelevant current) == size (uvCtx current) =
      Just (uvTerm current, const (uvTerm current))
  | otherwise = Just
      (uvTerm current, \newLocals ->
        -- TODO: check if newLocals is all neutral or referentially equal?
        let
          -- Replace the locals in the stored context
          ctx = uvCtx current & mapCtx \_ (Level i) _old ->
            newLocals Vector.! i
        in E.reeval ctx $ uvTerm current
      )

uvTypeEval :: UnivarState -> (Eval, Vector Eval -> Eval)
uvTypeEval current =
  (uvTerm current, \newLocals ->
    -- TODO: check if newLocals is all neutral or referentially equal?
    let
      -- Replace the locals in the stored context
      ctx = uvCtx current & mapCtx \_ (Level i) _old ->
        newLocals Vector.! i
    in E.reeval ctx $ uvType current
  )
