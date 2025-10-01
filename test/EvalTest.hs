module EvalTest (evalTest) where

import Control.Monad.IO.Class (liftIO)
import qualified Data.Text as T

import Pudding.Eval
import Pudding.Parser
import Pudding.Types
import Testing

evalTest :: TestSuite
evalTest = TestSuite "EvalTest" do
  testCase "BetaReduction" do
    t1 <- parseTerm "(lambda (x A) (x x))"
    t2 <- parseTerm "y"
    t3 <- parseTerm "(y y)"
    let t12' = normalize (TApp (Metadata mempty) t1 t2)
    let t3' = normalize t3
    expectEquiv Term' t12' t3'

parseTerm :: String -> Test Term
parseTerm s = do
  name <- testCaseName
  r <- liftIO $ runParser term (show name) (T.pack s)
  assertRight r

termEquiv :: Term -> Term -> Bool
termEquiv (TVar _ i1) (TVar _ i2) = i1 == i2
termEquiv (THole _ f1) (THole _ f2) = f1 == f2
termEquiv (TUniv _ l1) (TUniv _ l2) = l1 == l2
termEquiv (TGlobal _ n1 _) (TGlobal _ n2 _) = n1 == n2
termEquiv (TLambda _ p1 _ t1 b1) (TLambda _ p2 _ t2 b2) =
  p1 == p2 && t1 `termEquiv` t2 && b1 `termEquiv` b2
termEquiv (TPi _ p1 _ t1 b1) (TPi _ p2 _ t2 b2) =
  p1 == p2 && t1 `termEquiv` t2 && b1 `termEquiv` b2
termEquiv (TApp _ a1 b1) (TApp _ a2 b2) =
  a1 `termEquiv` a2 && b1 `termEquiv` b2
termEquiv _ _ = False

newtype Term' = Term' Term

instance Show Term' where
  show (Term' t) = show' t
    where
      show' (TVar {}) = "TVar {}"
      show' (THole {}) = "THole {}"
      show' (TUniv {}) = "TUniv {}"
      show' (TGlobal {}) = "TGlobal {}"
      show' (TLambda {}) = "TLambda {}"
      show' (TPi {}) = "TPi {}"
      show' (TApp {}) = "TApp {}"

instance Eq Term' where
  Term' t1 == Term' t2 = t1 `termEquiv` t2
