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
import qualified Data.FastEq as FastEq



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

type UVReeval = (Eval, Vector Eval -> Eval)
type UVsReeval = Fresh -> Maybe UVReeval

originalCtx :: "original" @:: EvalTypeCtx -> "new" @:: Vector Eval -> Bool
originalCtx original new = all snd $ ctxStack $ mapCtx
  (\_ (Level i) (_, v) -> shallowCompare v (new Vector.! i)) original

shallowCompare :: Eval -> Eval -> Bool
shallowCompare eL eR | eL FastEq.===? eR = True
shallowCompare (ENeutralVar _ lvlL Nil) (ENeutralVar _ lvlR Nil) = lvlL == lvlR
shallowCompare (EDeferred (Deferred _ _ _ (Just snL) _)) (EDeferred (Deferred _ _ _ (Just snR) _)) = snL == snR
shallowCompare _ _ = False

uvSolution :: UnivarState -> Maybe UVReeval
uvSolution current
  | uvStatus current == UVUnsolved = Nothing
  -- If every variable is irrelevant, the term does not depend on its local context
  | IntSet.size (uvIrrelevant current) == size (uvCtx current) =
      Just (uvTerm current, const (uvTerm current))
  | otherwise = Just
      (uvTerm current, \newLocals ->
        -- Do a quick comparison to optimize for the original context
        -- (obvious neutral variables, and let-bound variables should be
        -- referentially identical or at least with equal stable names)
        if originalCtx (uvCtx current) newLocals then uvTerm current else
        let
          -- Replace the locals in the stored context
          ctx = uvCtx current & mapCtx \_ (Level i) _old ->
            newLocals Vector.! i
        in E.reeval ctx $ uvTerm current
      )

uvTypeEval :: UnivarState -> UVReeval
uvTypeEval current
  -- If every variable is irrelevant, the term does not depend on its local context
  | IntSet.size (uvIrrelevant current) == size (uvCtx current) =
      (uvType current, const (uvType current))
  | otherwise =
      (uvTerm current, \newLocals ->
        -- Do a quick comparison to optimize for the original context
        -- (obvious neutral variables, and let-bound variables should be
        -- referentially identical or at least with equal stable names)
        let
          -- Replace the locals in the stored context
          ctx = uvCtx current & mapCtx \_ (Level i) _old ->
            newLocals Vector.! i
        in E.reeval ctx $ uvType current
      )
