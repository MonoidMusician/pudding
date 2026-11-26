module Pudding.Types.Monads.Types where

import Pudding.Core.Types
import Pudding.Core.Eval as E
import GHC.Generics (Generic)
import Data.Function ((&))
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Control.DeepSeq (NFData)
import qualified Data.IntMap.Strict as IntMap



data UnivarState = UVState
  -- the original context of the hole. TODO: globals? TODO: let?
  { uvCtx :: !EvalTypeCtx
  -- which variables (Levels) are known to be irrelevant
  , uvIrrelevant :: !IntSet
  -- the value for the term itself and its type
  , uvTerm :: !("tm" @:: Eval)
  , uvType :: "ty" @:: Eval -- ^ lazy
  -- Partial equations (constraints with this unification variable as its head)
  , uvHeadEqns :: !IntSet -- into ProverS.uvConstraints
  -- Callbacks? for filling in holes for deferred elaboration?
  , uvNotify :: !IntSet -- into ProverS.uvDeferred
  , uvStatus :: !UnivarStatus
  }

type AfterSolve = IntMap.IntMap ("uvs involved" @:: IntSet, "equation ctx" @:: EvalTypeCtx, Equation)

data UnivarStatus
  = UVUnsolved
  | UVProgressed
  | UVClosed
  deriving (Eq, Ord, Generic, NFData)

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
