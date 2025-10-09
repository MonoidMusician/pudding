module EvalTest (evalTest) where

import Control.Monad.IO.Class (liftIO)
import qualified Data.Text as T

import Pudding.Eval
import Pudding.Unify
import Pudding.Parser
import Pudding.Types
import Testing
import Pudding (parseAndBootGlobals)
import Data.Text (Text)
import Data.Foldable (for_)
import Pudding.Printer (PrinterState(..), formatCore, Style (Ansi), format, printCore)
import Control.DeepSeq (force)

evalTest :: TestSuite
evalTest = TestSuite "EvalTest" do
  let
    top = ctxOfGlobals globals
    globals = parseAndBootGlobals $ T.unlines
      -- Id := \(x : Type0) -> x
      [ "(define Id (lambda (x (Type0)) x))"
      , "(define Id1 (lambda (x (Type0 1)) x))"
      -- Polymorphic identity function
      , "(define identity (lambda (t (Type0)) (lambda (x t) x)))"
      , "(define identity1 (lambda (t (Type0 1)) (lambda (x t) x)))"
      -- Non-dependent function type
      , "(define Fun (lambda (i (Type0)) (lambda (o (Type0)) (Pi (x i) o))))"
      -- Basic ADTs
      , "(inductive Void () ())"
      , "(inductive Unit () () (unit))"
      , "(inductive Bool () () (true) (false))"
      , "(inductive Maybe ((t (Type0))) () (nothing) (just ((v t)) ()))"
      , "(inductive IsJust ((t (Type0))) ((mv (Maybe t))) (proveJust ((v t)) ((just t v))))"
      , "(inductive Either ((l (Type0)) (r (Type0))) ()"
      , "  (left ((v l))) (right ((v r))))"
      ]
    normUnder = normalizeNeutrals globals
    type0 = TUniv mempty $ UBase 0
    neutralCtx localTypes =
      mapCtx (\ctx _ty -> neutralVar (level ctx (Index 0))) $
        ctxOfList globals $ (BFresh,) <$> localTypes
    typecheckUnder localTypes = force . validateQuoteNeutrals globals localTypes
  testCase "Globals" do
    for_ globals \case
      -- GlobalDefn _ (GlobalTerm ty _) _ -> do
      --   liftIO $ putStrLn $ T.unpack $ formatCore Ansi ty
      --   liftIO $ putStrLn $ T.unpack $ formatCore Ansi $ typecheckUnder [] ty
      _ -> pure ()
    testCase "Id" do
      expectType top "Id1" "(Pi (t (Type0 1)) (Type0 1))"
    testCase "identity" do
      expectType top "identity1" "(Pi (t (Type0 1)) (Pi (x t) t))"
  testCase "AlphaEquivalence" do
    t1 <- parseTerm "(lambda (A (Type0)) A)"
    t2 <- parseTerm "(lambda (B (Type0)) B)"
    expectEquiv Term' t1 t2
  testCase "BetaReduction" do
    t1 <- parseTerm "(lambda (x (Type0)) x)"
    t2 <- parseTerm "(Type0)"
    t3 <- parseTerm "(identity1 (Type0) (Type0))"
    let t12' = normUnder [] (TApp (Metadata mempty) t1 t2)
    let t3' = normUnder [] t3
    expectEquiv Term' t12' t3'
  testCase "BetaReduction2" do
    t1 <- parseTerm "(Pi (t Unit) Void)"
    t2 <- parseTerm "(Fun Unit Void)"
    let e1 = evaling t1 $ neutralCtx []
    let e2 = evaling t2 $ neutralCtx []
    -- liftIO $ print $ SubTerm' 2 $ quote (ctxOfSize globals 2) e1
    -- liftIO $ print $ SubTerm' 2 $ quote (ctxOfSize globals 2) e2
    expect (conversionCheck (ctxOfSize globals 0) e1 e2) "Terms are equal under the conversion check"
  testCase "EtaEquivalence" do
    testCase "Lambdas" do
      t1 <- parseTermWith ["A", "B"] $ T.unlines
        [ "(lambda (f (Pi (x A) B))"
        , "  f)"
        ]
      t2 <- parseTermWith ["A", "B"] $ T.unlines
        [ "(lambda (f (Pi (x A) B))"
        , "  (lambda (x A)"
        , "    (f x)))"
        ]
      let e1 = evaling t1 $ neutralCtx [type0, type0]
      let e2 = evaling t2 $ neutralCtx [type0, type0]
      -- liftIO $ print $ SubTerm' 2 $ quote (ctxOfSize globals 2) e1
      -- liftIO $ print $ SubTerm' 2 $ quote (ctxOfSize globals 2) e2
      expect (conversionCheck (ctxOfSize globals 2) e1 e2) "Terms are equal under the conversion check"
    testCase "Pairs" do
      t1 <- parseTermWith ["A", "B"] $ T.unlines
        [ "(lambda (p (Sigma (x A) B))"
        , "  p)"
        ]
      t2 <- parseTermWith ["A", "B"] $ T.unlines
        [ "(lambda (p (Sigma (x A) B))"
        , "  (pair (Sigma (x A) B) (fst p) (snd p)))"
        ]
      let e1 = evaling t1 $ neutralCtx [type0, type0]
      let e2 = evaling t2 $ neutralCtx [type0, type0]
      -- liftIO $ print $ SubTerm' 2 $ quote (ctxOfSize globals 2) e1
      -- liftIO $ print $ SubTerm' 2 $ quote (ctxOfSize globals 2) e2
      expect (conversionCheck (ctxOfSize globals 2) e1 e2) "Terms are equal under the conversion check"
  testCase "AlreadyNormalized" do
    let
      alreadyNormalized s = do
        t <- parseTerm s
        let t1 = normUnder [] t
        let t2 = normUnder [] t1
        expectEquiv Term' t t1
        expectEquiv Term' t t2
    alreadyNormalized "(lambda (x (Type0)) x)"
    alreadyNormalized "(Pi (t (Type0)) (Type0))"
    alreadyNormalized "(lambda (t (Type0)) (lambda (x t) x))"
    alreadyNormalized "(Pi (t (Type0)) (Pi (x t) t))"
  testCase "DoubleNormalize" do
    let
      doublyNormalized s = do
        t <- normUnder [] <$> parseTerm s
        let t1 = normUnder [] t
        expectEquiv Term' t t1
    doublyNormalized "(Id1 (Id1 (Type0)))"
    doublyNormalized "identity1 (Type0) (Type0)"
    doublyNormalized $ T.unlines
      [ "(lambda (A (Type0))"
      , "  (lambda (B (Type0))"
      , "    (lambda (f (Pi (x A) B))"
      , "      f)))"
      ]
    doublyNormalized $ T.unlines
      [ "(lambda (A (Type0))"
      , "  (lambda (B (Type0))"
      , "    (lambda (f (Pi (x A) B))"
      , "      (lambda (x A)"
      , "        (f x)))))"
      ]
  testCase "Constructor" do
    tm <- parseTermWith ["t"] "(nothing t)"
    let ty = typecheckUnder [type0] tm
    liftIO $ print $ SubTerm' 1 ty

    tmL <- parseTermWith ["l", "r"] "(identity (Fun l (Either l r)) (left l r))"
    let tyL = typecheckUnder [type0, type0] tmL
    liftIO $ print $ SubTerm' 2 tmL
    liftIO $ print $ SubTerm' 2 tyL

    tmR <- parseTermWith [] "(right Void Unit unit)"
    let tyR = typecheckUnder [] tmR
    liftIO $ print $ SubTerm' 0 tmR
    liftIO $ print $ SubTerm' 0 tyR

    tmT <- parseTermWith [] "(lambda (Err (Type0)) (identity (Either Err Unit) (right Err Unit unit)))"
    let tyT = typecheckUnder [] tmT
    liftIO $ print $ SubTerm' 0 tmT
    liftIO $ print $ SubTerm' 0 tyT

    tmP <- parseTermWith []
      -- "(IsJust Unit (just Unit unit))"
      -- "(proveJust Unit unit)"
      "(identity (IsJust Unit (just Unit unit)) (proveJust Unit unit))"
    let tyP = typecheckUnder [] tmP
    liftIO $ print $ SubTerm' 0 tmP
    liftIO $ print $ SubTerm' 0 tyP

parseTerm :: Text -> Test Term
parseTerm s = do
  name <- testCaseName
  r <- liftIO $ runParser term (show name) s
  assertRight r

parseTermWith :: [Text] -> Text -> Test Term
parseTermWith names s = do
  name <- testCaseName
  r <- liftIO $ runParserScope term names (show name) s
  assertRight r

expectType :: TypeCtx -> Text -> Text -> Test ()
expectType ctx tm ty = do
  tm' <- parseTerm tm
  ty' <- parseTerm ty
  expectEquiv Term' ty' (typeof ctx tm')

termEquiv :: Term -> Term -> Bool
termEquiv (TVar _ i1) (TVar _ i2) = i1 == i2
termEquiv (THole _ f1) (THole _ f2) = f1 == f2
termEquiv (TUniv _ l1) (TUniv _ l2) = l1 == l2
termEquiv (TGlobal _ n1) (TGlobal _ n2) = n1 == n2
termEquiv (TLambda _ p1 _ t1 (Scoped b1)) (TLambda _ p2 _ t2 (Scoped b2)) =
  p1 == p2 && t1 `termEquiv` t2 && b1 `termEquiv` b2
termEquiv (TPi _ p1 _ t1 (Scoped b1)) (TPi _ p2 _ t2 (Scoped b2)) =
  p1 == p2 && t1 `termEquiv` t2 && b1 `termEquiv` b2
termEquiv (TApp _ a1 b1) (TApp _ a2 b2) =
  a1 `termEquiv` a2 && b1 `termEquiv` b2
termEquiv _ _ = False

newtype Term' = Term' Term

instance Show Term' where
  show (Term' t) = "\n" <> T.unpack (formatCore Ansi t)

instance Eq Term' where
  Term' t1 == Term' t2 = t1 `termEquiv` t2

data SubTerm' = SubTerm' Int Term

instance Show SubTerm' where
  show (SubTerm' depth t) = "\n" <> T.unpack (format Ansi $ printCore t (PS 0 depth))

instance Eq SubTerm' where
  SubTerm' _ t1 == SubTerm' _ t2 = t1 `termEquiv` t2
