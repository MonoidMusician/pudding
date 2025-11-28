{-# OPTIONS_GHC -Wno-type-defaults #-}
module EvalTest where

import Control.Monad.IO.Class (liftIO, MonadIO)
import qualified Data.Text as T

import Pudding.Unify ( validateQuoteNeutrals, conversionCheck )
import Pudding.Parser ( runParserScope, globalTable )
import Pudding.Types
import Pudding.Name (canonicalName)
import Testing
import Pudding (parseAndBootGlobals)
import Data.Text (Text)
import Data.Foldable (fold)
import Pudding.Printer (PrinterState(..), formatCore, Style (Ansi), format, printCore)
import Control.Monad.Reader.Class (MonadReader (reader, ask), asks, local)
import Control.Lens (review)
import qualified Pudding.Eval as Eval
import Data.Functor (void)
import qualified Pudding.Parser as Parse
import qualified Data.Map as Map

-- NamedDefaults requires GHC 9.12.1
default (Text)

type EvalTestCtx = Ctx (Name, "type" @:: Term)
type EvalTest = Test EvalTestCtx

addVar ::
  (MonadIO m, MonadReader (Ctx (Name, Term)) m) =>
  Text -> Term -> m a -> m a
addVar nameText ty inner = do
  name <- liftIO $ internalize globalTable nameText
  local (\ctx -> ctx :> (BVar (Meta (canonicalName name)), (name, ty))) do
    inner

addVars :: [("name" @:: Text, "type" @:: Term)] -> EvalTest a -> EvalTest a
addVars = flip $ foldr (uncurry addVar)

globalSource :: Text
globalSource = T.unlines
  -- Id := \(x : Type0) -> x
  [ "(define Id (lambda (x (Type0)) x))"
  , "(define Id1 (lambda (x (Type0 1)) x))"
  -- Polymorphic identity function
  , "(define identity (lambda (t (Type0)) (lambda (x t) x)))"
  , "(define identity1 (lambda (t (Type0 1)) (lambda (x t) x)))"
  -- Non-dependent function type
  , "(define Fun (lambda (I (Type0)) (lambda (O (Type0)) (Pi (x I) O))))"
  -- Basic ADTs
  , "(inductive Void () ())"
  , "(inductive Unit () () (unit))"
  , "(inductive Bool () () (true) (false))"
  , "(inductive Maybe ((T (Type0))) () (nothing) (just ((v T)) ()))"
  , "(inductive IsJust ((T (Type0))) ((mv (Maybe T))) (proveJust ((v T)) ((just T v))))"
  , "(inductive Either ((L (Type0)) (R (Type0))) ()"
  , "  (left ((v L))) (right ((v R))))"
  ]

withTestContext :: EvalTest r -> Test () r
withTestContext = withContext $ ctxOfGlobals $ parseAndBootGlobals globalSource

toNeutralCtx :: Ctx t -> Ctx Eval
toNeutralCtx = mapCtx (\_ lvl _ty -> neutralVar lvl)

(.::) :: "name" @:: Text -> "type" @:: Term -> ("name" @:: Text, "type" @:: Term)
(.::) = (,)

class Convert i o where
  convert :: i -> EvalTest o
instance Convert Term Term where
  convert = pure
instance Convert Eval Eval where
  convert = pure
instance Convert Text Term where
  convert = parseTerm
instance Convert Term Eval where
  convert = fmap fst . evalNorm
instance Convert Text Eval where
  convert s = do
    (e :: Term) <- convert s
    convert e


evalTest :: TestSuite
evalTest = TestSuite "EvalTest" $ withTestContext do
  let
    type0 = TUniv mempty $ UBase 0
  testCase "Globals" do
    globals <- asks ctxGlobals
    _ <- flip Map.traverseWithKey (globalDefns globals) \name -> \case
      -- GlobalDefn _ (GlobalTerm ty _) (GlobalTerm tm _) -> do
      --   liftIO $ putStrLn $ T.unpack $ nameText name <> " : " <> formatCore Ansi ty
      --   liftIO $ putStrLn $ T.unpack $ nameText name <> " := " <> formatCore Ansi tm
      --   liftIO $ putStrLn $ T.unpack $ formatCore Ansi $ typecheckUnder [] ty
      _ -> pure ()
    testCase "Id" do
      expectType "Id1" "(Pi (t (Type0 1)) (Type0 1))"
    testCase "identity" do
      expectType "identity1" "(Pi (t (Type0 1)) (Pi (x t) t))"
  testCase "AlphaEquivalence" do
    t1 <- parseTerm "(lambda (A (Type0)) A)"
    t2 <- parseTerm "(lambda (B (Type0)) B)"
    expectEquiv Term' t1 t2
  testCase "BetaReduction" do
    t1 <- parseTerm "(lambda (x (Type0 1)) x)"
    t2 <- parseTerm "(Type0)"
    t3 <- parseTerm "(identity1 (Type0 1) (Type0))"
    TApp mempty t1 t2 `defEqTo` t3
    testCase "SimpleDefinition" do
      "(Fun Unit Void)" `defEqTo` "(Pi (t Unit) Void)"
  testCase "EtaEquivalence" do
    testCase "Lambdas" $
      addVars ["A" .:: type0, "B" .:: type0] do
        t1 <- parseTerm $ T.unlines
          [ "(lambda (f (Pi (x A) B))"
          , "  f)"
          ]
        t2 <- parseTerm $ T.unlines
          [ "(lambda (f (Pi (x A) B))"
          , "  (lambda (x A)"
          , "    (f x)))"
          ]
        defEqTo t1 t2
    testCase "Pairs" do
      addVars ["A" .:: type0, "B" .:: type0] do
        t1 <- parseTerm $ T.unlines
          [ "(lambda (p (Sigma (x A) B))"
          , "  p)"
          ]
        t2 <- parseTerm $ T.unlines
          [ "(lambda (p (Sigma (x A) B))"
          , "  (pair (Sigma (x A) B) (fst p) (snd p)))"
          ]
        defEqTo t1 t2
  testCase "AlreadyNormalized" do
    let
      alreadyNormalized s = normalizesTo s s
    alreadyNormalized "(lambda (x (Type0)) x)"
    alreadyNormalized "(Pi (t (Type0)) (Type0))"
    alreadyNormalized "(lambda (t (Type0)) (lambda (x t) x))"
    alreadyNormalized "(Pi (t (Type0)) (Pi (x t) t))"
  testCase "DoubleNormalize" do
    let
      doublyNormalize s = do
        (_, t) <- evalNorm =<< convert s
        normalizesTo t t
    doublyNormalize "(Id1 (Id1 (Type0)))"
    doublyNormalize "identity1 (Type0) (Type0)"
    doublyNormalize $ T.unlines
      [ "(lambda (A (Type0))"
      , "  (lambda (B (Type0))"
      , "    (lambda (f (Pi (x A) B))"
      , "      f)))"
      ]
    doublyNormalize $ T.unlines
      [ "(lambda (A (Type0))"
      , "  (lambda (B (Type0))"
      , "    (lambda (f (Pi (x A) B))"
      , "      (lambda (x A)"
      , "        (f x)))))"
      ]
  testCase "Constructor" do
    addVars ["t" .:: type0] do
      tm <- parseTerm "(nothing t)"
      ty <- typecheck tm
      liftIO $ print $ SubTerm' 1 ty

    addVars ["l" .:: type0, "r" .:: type0] do
      tmL <- parseTerm "(identity (Fun l (Either l r)) (left l r))"
      tyL <- typecheck tmL
      liftIO $ print $ SubTerm' 2 tmL
      liftIO $ print $ SubTerm' 2 tyL

    do
      tmR <- parseTerm "(right Void Unit unit)"
      tyR <- typecheck tmR
      liftIO $ print $ SubTerm' 0 tmR
      liftIO $ print $ SubTerm' 0 tyR

    do
      tmT <- parseTerm "(lambda (Err (Type0)) (identity (Either Err Unit) (right Err Unit unit)))"
      tyT <- typecheck tmT
      liftIO $ print $ SubTerm' 0 tmT
      liftIO $ print $ SubTerm' 0 tyT

    do
      tmP <- parseTerm
        -- "(IsJust Unit (just Unit unit))"
        -- "(proveJust Unit unit)"
        "(identity (IsJust Unit (just Unit unit)) (proveJust Unit unit))"
      tyP <- typecheck tmP
      liftIO $ print $ SubTerm' 0 tmP
      liftIO $ print $ SubTerm' 0 tyP
  testCase "2LTT" do
    liftBoolType <- parseTerm "(Lift Bool)"
    "(splice (quote (lambda (x (Type0)) x)))"
      `normalizesTo` "(lambda (x (Type0)) x)"
    addVar "v" liftBoolType do
      "(quote (splice v))" `normalizesTo` "v"

parseTerm :: Text -> EvalTest Term
parseTerm s = do
  names <- asks \ctx -> review stack (nameText . fst . snd <$> ctxStack ctx)
  name <- testCaseName
  r <- liftIO $ runParserScope Parse.term names (show name) s
  assertRight r

evalNorm :: Term -> EvalTest (Eval, Term)
evalNorm term = do
  evaled <- reader \ctx -> Eval.eval (toNeutralCtx ctx) term
  normed <- reader \ctx -> Eval.quote (void ctx) evaled
  pure (evaled, normed)

typecheck :: Term -> EvalTest Term
typecheck term = do
  ctx <- ask
  let globals = ctxGlobals ctx
  let localTypes = review stack (snd . snd <$> ctxStack ctx)
  testNF $ validateQuoteNeutrals globals localTypes term

defEqTo :: forall i1 i2. Convert i1 Eval => Convert i2 Eval => "term1" @:: i1 -> "term2" @:: i2 -> EvalTest ()
defEqTo i1 i2 = do
  (e1 :: Eval) <- convert i1
  (e2 :: Eval) <- convert i2
  ctx <- ask
  expect (conversionCheck (void ctx) e1 e2) $ fold
    [ "Terms are equal under the conversion check:"
    , "\n", T.unpack $ formatCore Ansi $ Eval.quote (void ctx) e1
    , "\n", T.unpack $ formatCore Ansi $ Eval.quote (void ctx) e2
    ]

normalizesTo :: forall i1 i2. Convert i1 Term => Convert i2 Term => "term1" @:: i1 -> "term2" @:: i2 -> EvalTest ()
normalizesTo i1 i2 = do
  (t0 :: Term) <- convert i1
  (t2 :: Term) <- convert i2
  (e1, t1) <- evalNorm t0
  ctx <- ask
  let wrapper = SubTerm' (size ctx)
  expectEquiv wrapper t1 t2
  (e2, t3) <- evalNorm t2
  expectEquiv wrapper t2 t3 -- Already normalized?
  expectEquiv wrapper t1 t3 -- Still equal to normalized version...
  expect (conversionCheck (void ctx) e1 e2) "Conversion check should succeed for equivalent terms"

expectType :: "term" @:: Text -> "type" @:: Text -> EvalTest ()
expectType tm ty = do
  tm' <- parseTerm tm
  ty' <- parseTerm ty
  defEqTo ty' =<< typecheck tm'

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
