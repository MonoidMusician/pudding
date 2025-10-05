module EvalTest (evalTest) where

import Control.Monad.IO.Class (liftIO)
import qualified Data.Text as T

import Pudding.Eval
import Pudding.Parser
import Pudding.Types
import Testing
import Pudding (parseAndBootGlobals)
import Data.Text (Text)
import Data.Foldable (for_)
import Pudding.Printer (formatCore, Style (Ansi), format, printCore)

evalTest :: TestSuite
evalTest = TestSuite "EvalTest" do
  let
    empty = simpleCtx globals []
    globals = parseAndBootGlobals $ T.unlines
      -- Id := \(x : U0) -> x
      [ "(define Id (lambda (x (U0)) x))"
      -- Polymorphic identity function
      , "(define identity (lambda (t (U0)) (lambda (x t) x)))"
      ]
    normUnder = normalizeNeutrals globals
    u0 = TUniv mempty $ UBase 0
  testCase "Globals" do
    for_ globals \case
    --   GlobalDefn (GlobalTerm ty _) _ -> do
    --     liftIO $ putStrLn $ T.unpack $ formatCore Ansi ty
    --     liftIO $ putStrLn $ T.unpack $ formatCore Ansi $ typeof empty ty
      _ -> pure ()
    testCase "Id" do
      expectType empty "Id" "(Pi (t (U0)) (U0))"
    testCase "identity" do
      expectType empty "identity" "(Pi (t (U0)) (Pi (x t) t))"
  testCase "AlphaEquivalence" do
    t1 <- parseTerm "(lambda (A (U0)) A)"
    t2 <- parseTerm "(lambda (B (U0)) B)"
    expectEquiv Term' t1 t2
  testCase "BetaReduction" do
    t1 <- parseTerm "(lambda (x (U0)) x)"
    t2 <- parseTerm "(U0)"
    t3 <- parseTerm "(identity (U0) (U0))"
    let t12' = normUnder [] (TApp (Metadata mempty) t1 t2)
    let t3' = normUnder [] t3
    expectEquiv Term' t12' t3'
  testCase "EtaEquivalence" do
    t1 <- parseTermWith ["A", "B"] $ T.unlines
      [ "(lambda (f (Pi (x A) B))"
      , "  f)"
      ]
    t2 <- parseTermWith ["A", "B"] $ T.unlines
      [ "(lambda (f (Pi (x A) B))"
      , "  (lambda (x A)"
      , "    (f x)))"
      ]
    -- liftIO $ putStrLn $ show $ Term' t1
    let t1' = normUnder [u0, u0] t1
    let t2' = normUnder [u0, u0] t2
    expectEquiv (SubTerm' 2) t1' t2'
  testCase "AlreadyNormalized" do
    let
      alreadyNormalized s = do
        t <- parseTerm s
        let t1 = normUnder [] t
        let t2 = normUnder [] t1
        expectEquiv Term' t t1
        expectEquiv Term' t t2
    alreadyNormalized "(lambda (x (U0)) x)"
    alreadyNormalized "(Pi (t (U0)) (U0))"
    alreadyNormalized "(lambda (t (U0)) (lambda (x t) x))"
    alreadyNormalized "(Pi (t (U0)) (Pi (x t) t))"
  testCase "DoubleNormalize" do
    let
      doublyNormalized s = do
        t <- normUnder [] <$> parseTerm s
        let t1 = normUnder [] t
        expectEquiv Term' t t1
    doublyNormalized "(Id (Id (U0)))"
    doublyNormalized "identity (U0) (U0)"
    doublyNormalized $ T.unlines
      [ "(lambda (A (U0))"
      , "  (lambda (B (U0))"
      , "    (lambda (f (Pi (x A) B))"
      , "      f)))"
      ]
    doublyNormalized $ T.unlines
      [ "(lambda (A (U0))"
      , "  (lambda (B (U0))"
      , "    (lambda (f (Pi (x A) B))"
      , "      (lambda (x A)"
      , "        (f x)))))"
      ]

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
  show (SubTerm' depth t) = "\n" <> T.unpack (format Ansi $ printCore t (0, QuoteCtx depth))

instance Eq SubTerm' where
  SubTerm' _ t1 == SubTerm' _ t2 = t1 `termEquiv` t2
