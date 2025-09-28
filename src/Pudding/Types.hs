module Pudding.Types where

import Data.Text (Text)
import Data.Set (Set)

-- DeBruijn index: 0 is the most recently bound variable (inner scope). Used for typechecking.
newtype Index = Index Int

-- DeBruijn level: 0 is the first bound variable (outer scope). Used for evaluation.
newtype Level = Level Int

-- Tag for metadata: not relevant to normalization/unification, just display.
-- Should implement `Semigroup`, so it can be unified!
newtype Meta t = Meta t

-- Name (TODO: string interning)
newtype Name = Name Text

data Binder
  = BVar (Meta (Set Name))

-- A dependently typed term in the core calculus
data Term
  = TVar Index
  | TLambda Binder {-domain type:-} Term {-body:-} Term
  | TPi Binder {-domain type:-} Term {-codomain:-} Term

-- Result of Normalization by Evaluation (NbE), the semantic domain.
data Eval
  = EVar Level
  | EClosure Binder {-domain type:-} Eval {-body:-} Closure
  | EPi Binder {-domain type:-} Eval {-codomain:-} Closure

-- Closure: an unevaluated term ossified in an environment of evaluated variables
data Closure = Closure [Eval] Term
