{-# LANGUAGE AllowAmbiguousTypes #-}
module Pudding.Types.Monads where

import Pudding.Types.Base (Fresh, UnifyMode, type (@::))
import Pudding.Types (Eval, Term, Name)
import Control.Monad.Error.Class (MonadError)
import Criterion.Types (Config)
import GHC.Base (Symbol)
import Data.Text (Text)

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
class Freshener m where
  freshen :: m Fresh

-- Reader-like
class WithConfig m where
  getConfig :: m Config


-----------------------
-- Semantics for DTT --
-----------------------


-- Writer-like
class Constraints c m | m -> c where
  constrain :: c -> m ()
  constraintsFrom :: m a -> m (c, a)

-- State/IO-like
class Constraints c m => Unification c m | m -> c where
  solve :: Fresh -> Eval -> m Eval
  currentSolution :: Fresh -> m Eval

-- saveCheckpoint :: m (m ()) -- or something more scoped?
-- logging...

class MonadError e m => Proving e m where
  typecheckEval ::
    ("expected type" @:: Maybe Eval, "term" @:: Term) -> m
    ("actual type" @:: Eval, "value" @:: Eval, "normalized" @:: Term)
  tryUnify :: UnifyMode -> (Eval, Eval) -> m (Either e Eval)
  unify :: UnifyMode -> (Eval, Eval) -> m Eval
  conversionCheck :: UnifyMode -> (Eval, Eval) -> m Bool


---------------
-- Extras... --
---------------

class Serialize fmt m t where
  serialize :: t -> m fmt
class Deserialize fmt m t where
  deserialize :: fmt -> m t
-- Serializing can use memoization to maintain sharing/hashcons/backrefs or something
-- Deserializing can either be State-like (for backrefs) or Reader-like...
