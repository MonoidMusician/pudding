module Pudding.Surface.Elaborator where

import Prelude

import Data.Functor ((<&>), void)
import Data.Function ((&))
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)
import Pudding.Name (Name (..), internalize, NameTable, canonicalName)
import Pudding.Types.Base (Plicit (Explicit), type (@::))
import Pudding.Types.Metadata
import Pudding.Types.Stack (Stack, ToLevel(level), ToIndex(index), Level(Level), StackLike(size), pattern Nil, pattern (:>))
import Control.Monad.State.Strict (StateT (runStateT), gets, modify', MonadIO, MonadTrans (lift))
import Pudding.Types (GlobalInfo (..), Term (..), GlobalDefn (GlobalDefn), GlobalTerm (GlobalTerm), Binder (BVar, BUnused), ScopedTerm (Scoped), Eval (ENeut, EUniv), Neutral (Neutral), NeutFocus (NVar), ULevel (UBase))
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Data.IORef (IORef)
import Pudding.Surface.Parser (Decl (..), CST (..), CBinder)
import Data.Foldable (traverse_, Foldable (fold))
import Data.Functor.Compose (Compose (Compose))
import Control.Monad.Reader.Class (MonadReader (local, ask), asks)
import Data.List.NonEmpty (NonEmpty(..))
import Pudding.Eval (EvalTypeCtx)
import qualified Pudding.Unify as U
import qualified Pudding.Eval as E
import Pudding.Surface.Lexer (VariableDB(..), NameForm (..))
import Data.Maybe (fromMaybe)
import qualified Pudding.Printer as P
import qualified Data.Text as T
import Control.Arrow (Arrow(first))
import qualified Data.List.NonEmpty as NE
import Control.Monad.Trans.Cont (ContT(ContT, runContT))

class Applicative m => TwoPhase m where
  twoPhases :: m (m r) -> m r

-- | Gather global names. Merely an applicative, not a monad.
data GGather m r = GGather (Map Name (m GlobalInfo))
  (Map Name (m GlobalInfo) -> m r)
  deriving (Functor)

instance Applicative m => Applicative (GGather m) where
  pure = GGather M.empty . const . pure
  liftA2 f (GGather ml cl) (GGather mr cr) = GGather
    (M.unionWith (\_ r -> r) ml mr)
    (liftA2 (liftA2 f) cl cr)

instance Monad m => TwoPhase (GGather m) where
  twoPhases (GGather m1 c1) = GGather m1 \m2 ->
    c1 m2 >>= \case
      GGather m3 c2 -> c2 (M.unionWith (\_ r -> r) m2 m3)

type GInit = StateT (Map Name (Initializing GlobalInfo))

data Initializing t
  = Uninitialized
  | Initializing (Maybe t)
  | InitFailed
  | Initialized t
  deriving (Eq, Ord, Functor, Foldable, Traversable)

willInit :: forall m. Monad m => Name -> GInit m GlobalInfo -> GGather (GInit m) (GInit m GlobalInfo)
willInit !n creator = GGather (M.singleton n cachedCreator)
  \_items -> pure cachedCreator
  where
  cachedCreator :: GInit m GlobalInfo
  cachedCreator = do
    gets (M.lookup n) >>= \case
      Nothing -> error $ "Missing name: " <> show n
      Just InitFailed -> error $ "Init failed: " <> show n
      Just (Initialized r) -> pure r
      Just (Initializing (Just r)) -> pure r
      Just (Initializing Nothing) -> error $ "Circular dependency: " <> show n
      Just Uninitialized -> do
        modify' $ M.insert n (Initializing Nothing)
        r <- creator
        modify' $ M.insert n (Initialized r)
        pure r

inited :: forall m. Monad m => Name -> GGather (GInit m) GlobalInfo
inited !n = GGather M.empty \items ->
  case M.lookup n items of
    Nothing -> error $ "Missing name: " <> show n
    Just r -> r

data GLScope = GLScope
  { names :: IORef NameTable
  , globals :: Map Name (Scoped GlobalInfo)
  , locals :: Map Name (Stack Eval)
  , ctx :: EvalTypeCtx
  }

mintName :: forall r m. MonadIO m => MonadReader r m => (r -> IORef NameTable) -> Text -> m Name
mintName getTable t = do
  tbl <- asks getTable
  internalize tbl t

type Scoped = GInit (ReaderT GLScope IO)

-- Global Local Monad
-- Stage 1: Text -> Name
-- Stage 2: gather global definitions
-- Stage 3: initialize global definitions
-- Stage 4: evaluate expressions with globals, locals, and names
type GLM = Compose (ReaderT (IORef NameTable) IO) (GGather Scoped)

willInitGLM :: Text -> (Name -> Scoped GlobalInfo) -> GLM ()
willInitGLM name creator = Compose $ mintName id name <&>
  \name' -> void $ willInit name' (creator name')

initedGLM :: Name -> Scoped GlobalInfo
initedGLM n = do
  asks (M.lookup n . globals) >>= \case
    Nothing -> error $ "Missing name: " <> show n
    Just i -> i


runElabFull :: IORef NameTable -> GLM r -> IO (Map Name GlobalInfo, r)
runElabFull tbl (Compose stage0) = do
  GGather items stage1 <- runReaderT stage0 tbl
  let
    stage2 = do
      r <- stage1 items
      env <- sequence items
      pure (env, r)
  (r, _) <- runReaderT (runStateT stage2 (Uninitialized <$ items))
    (GLScope tbl items M.empty Nil)
  pure r

runElabScoped :: IORef NameTable -> Scoped r -> IO r
runElabScoped tbl stage2 = do
  fmap fst $ runReaderT (runStateT stage2 M.empty) $
    GLScope tbl M.empty M.empty Nil




elaborateModule :: [Decl] -> GLM ()
elaborateModule = traverse_ elaborateDecl

elaborateDecl :: Decl -> GLM ()
elaborateDecl = \case
  DDefine text mty tm -> willInitGLM text \name -> DefnGlobal <$> do
    GlobalDefn 0 <$> maybe undefined elaborateDefn mty <*> elaborateDefn tm
  _ -> error "Not supported"


elaborateDefn :: CST -> Scoped GlobalTerm
elaborateDefn = fmap (\t -> GlobalTerm t undefined) . elab Nothing


elab :: Maybe ("expected type" @:: Eval) -> CST -> Scoped Term
elab mexp = \case
  CApp fun arg -> TApp mempty Explicit <$> elab Nothing fun <*> elab Nothing arg
  CUniv -> pure $ TUniv mempty (UBase 0)

  CLambda binders body -> elabBinders (TLambda mempty) binders body
  CPi     binders body -> elabBinders (TPi     mempty) binders body
  CSigma  binders body -> elabBinders (TSigma  mempty) binders body
  -- | CLet    ![(CBinder, "ty" @:: Maybe CST, "tm" @:: CST)]    !CST

  -- | CSentence !(NonEmpty (Either L.OpForm CST))

  CVar (Just (PlainName [] text)) PlainVar -> do
    name <- mintName names text
    asks (M.lookup name . locals) >>= \case
      Just (_ :> e) -> do
        qc <- asks (void . ctx)
        pure $ E.quote qc e
      _ -> error $ "Missing variable: " <> show name
  CVar Nothing idxOrLvl -> case idxOrLvl of
    PlainVar -> error "impossible: CVar Nothing PlainVar"
    DBIndex i -> do
      c <- asks ctx
      pure $ TVar mempty $ index c i
    DBLevel l -> do
      c <- asks ctx
      pure $ TVar mempty $ index c $ level c l

  -- | CMod  ![Text]

  -- | CNum !Text
  -- | CStr ![Either Text CST]
  -- | CHole !(Maybe Text)

  CLift t -> TLift mempty <$> elab (Just (EUniv mempty (UBase 0))) t
  CQuote e -> TQuote mempty <$> elab Nothing e
  CSplice e -> TSplice mempty <$> elab Nothing e

  -- | CMatch ![CST] !("cases" @:: [("pats" @:: [CST], "body" @:: CST)])
  -- | CField  !CST !Text
  CAscribe tm ty -> do
    here <- ask
    tyT <- elab Nothing ty
    let tyE = E.eval (snd <$> ctx here) tyT
    tmT <- elab (Just tyE) tm
    let tmtyE = U.validate (ctx here) tmT
    if U.conversionCheck (void (ctx here)) tyE tmtyE
      then pure tmT
      else error $ fold
        [ "Type error: "
        , "\n" <> T.unpack do P.format P.Ansi $ P.printCore (E.quote (void (ctx here)) tyE) (P.PS 0 $ size $ ctx here)
        , "\n" <> T.unpack do P.format P.Ansi $ P.printCore (E.quote (void (ctx here)) tmtyE) (P.PS 0 $ size $ ctx here)
        , "\n" <> T.unpack do P.format P.Ansi $ P.printCore tmT (P.PS 0 $ size $ ctx here)
        ]

  -- | CAssign !CST !CST -- for patterns and do notation

  cst -> error $ "Cannot elaborate yet: " <> show cst

elabBinders ::
  (Plicit -> Binder -> Term -> ScopedTerm -> Term) ->
  NonEmpty (Plicit, NonEmpty CBinder, "ty" @:: Maybe CST) -> CST -> Scoped Term
elabBinders cons binders body = foldr addBinder (elab Nothing body) binders
  where
  addBinder :: (Plicit, NonEmpty CBinder, Maybe CST) -> Scoped Term -> Scoped Term
  addBinder (plicit, binder, mty) inner = do
    tyT <- case mty of
      Nothing -> error "Missing type for lambda/pi/sigma"
      Just ty -> elab Nothing ty
    evalCtx <- asks ctx
    let tytyT = U.quickTermType evalCtx tyT
    let tyE = E.eval (snd <$> evalCtx) tyT
    runContT (elabMultiBinderCont tyE binder) \binderB ->
      multiCons plicit binderB tyT <$> inner
  multiCons plicit bounders tyT inner =
    foldr (\(i, b) -> cons plicit b (E.shift i tyT) . Scoped)
      inner
      (zip [0..] (NE.toList bounders))

elabMultiBinder :: ("ty" @:: Eval) -> NonEmpty CBinder -> Scoped (NonEmpty Binder, GLScope -> GLScope)
elabMultiBinder tyE (b0 :| []) = first pure <$> elabBinder1 tyE b0
elabMultiBinder tyE (b0 :| (b1 : bs)) = do
  (c0, f0) <- elabBinder1 tyE b0
  local f0 do
    (cs, fs) <- elabMultiBinder tyE (b1 :| bs)
    pure (NE.cons c0 cs, fs . f0)

elabBinder1 :: ("ty" @:: Eval) -> CBinder -> Scoped (Binder, GLScope -> GLScope)
elabBinder1 tyE = \case
  CVar (Just (PlainName [] text)) PlainVar -> do
    name <- mintName names text
    let binder = BVar (Meta (canonicalName name))
    pure $ (binder, ) $ \outer ->
      let neutral = Neutral (NVar mempty (Level (size (ctx outer)))) Nil
          addVar = name & M.alter do Just . (:> ENeut neutral) . fromMaybe Nil
      in outer { locals = addVar (locals outer), ctx = ctx outer :> (binder, (tyE, ENeut neutral)) }
  CPlaceholder -> do
    pure $ (BUnused,) $ \outer ->
      let neutral = Neutral (NVar mempty (Level (size (ctx outer)))) Nil
      in outer { ctx = ctx outer :> (BUnused, (tyE, ENeut neutral)) }
  _ -> error "Bad/unsupported binder"

elabMultiBinderCont :: ("ty" @:: Eval) -> NonEmpty CBinder -> ContT c Scoped (NonEmpty Binder)
elabMultiBinderCont tyE = traverse (elabBinder1Cont tyE)

localize :: MonadReader r m => a -> (r -> r) -> ContT c m a
localize c f = ContT \k -> local f (k c)

elabBinder1Cont :: ("ty" @:: Eval) -> CBinder -> ContT c Scoped Binder
elabBinder1Cont tyE b = do
  (c, f) <- lift $ elabBinder1 tyE b
  ContT \k -> do
    local f $ k c
