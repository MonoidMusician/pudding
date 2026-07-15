-- | The elaborator is the most important piece for user experience: it handles
-- | converting the surface syntax into terms in the core language. Thanks to
-- | the nature of dependent types, it is heavily interleaved with evaluation
-- | in addition to typechecking. It does need to tame this to stay logically
-- | sound and to be predictable for the user.
-- |
-- | There are three main areas of responsibility, in order:
-- | 1. Handling namespacing ((sub)modules, imports, renames, resolving names).
-- | 2. User operators: disambiguation, grouping, precedence, associativity.
-- | 3. Synthesizing expressions into core `Term`s based on an expected type.
-- |
-- | The third is the most important and complicated, involving unification and
-- | and evaluation.
{-# LANGUAGE ApplicativeDo #-}
module Pudding.Surface.Elaborator where

import Prelude

import Data.Functor ((<&>), void)
import Data.Function ((&))
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)
import Pudding.Types.Name (Name (..), internalize, NameTable, canonicalName)
import Pudding.Types.Base (Plicit (Explicit, Implicit), type (@::))
import Pudding.Types.Metadata
import Pudding.Types.Stack (Stack, ToLevel(level), ToIndex(index), Level(Level), Index(Index), StackLike(size, Elem), pattern Nil, pattern (:>), StackFunctor (mapWithLevel), (@@?))
import Control.Monad.State.Strict (StateT (runStateT), gets, modify', MonadIO, MonadTrans (lift))
import Pudding.Core.Types (GlobalInfo (..), Term (..), GlobalDefn (GlobalDefn), GlobalTerm (GlobalTerm), Binder (BVar, BUnused, BMulti), ScopedTerm (Scoped), Eval (..), Neutral (Neutral), NeutFocus (NVar), ULevel (UBase), globalsFrom, Ctx (ctxGlobals), GlobalTypeInfo (GlobalTypeInfo, typeParams, typeIndices), Closure, ConstructorInfo (ConstructorInfo), Globals (globalDefns))
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Data.IORef (IORef)
import Pudding.Surface.Parser (Decl (..), CST (..), CBinder, CBinderGroup)
import Data.Foldable (Foldable (fold), foldlM, for_)
import Data.Functor.Compose (Compose (Compose))
import Control.Monad.Reader.Class (MonadReader (local, ask), asks)
import Data.List.NonEmpty (NonEmpty(..))
import Pudding.Core.Eval (EvalTypeCtx)
import qualified Pudding.Core.Unify as U
import qualified Pudding.Core.Eval as E
import Pudding.Surface.Lexer (VariableDB(..), NameForm (..), VariableName)
import Data.Maybe (fromMaybe, catMaybes)
import qualified Pudding.Core.Printer as P
import qualified Data.Text as T
import Control.Arrow (Arrow(first))
import qualified Data.List.NonEmpty as NE
import Control.Monad.Trans.Cont (ContT(ContT, runContT), evalContT)
import Data.Traversable (for)
import qualified Data.Vector as Vector
import Control.Monad (join, when)

class Applicative m => TwoPhase m where
  twoPhases :: m (m r) -> m r



-- | Gather global names. Merely an applicative, not a monad.
data GGather m r = GGather
  (Map Name (m GlobalInfo))
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
  { glNames :: IORef NameTable
  , glGlobals :: Map Name (Scoped GlobalInfo)
  , glLocals :: Map Name (Stack Eval)
  , glCtx :: EvalTypeCtx
  }

mintName :: forall r m. MonadIO m => MonadReader r m => (r -> IORef NameTable) -> Text -> m Name
mintName getTable t = do
  tbl <- asks getTable
  internalize tbl t


-- | Global Local Monad
-- | Stage 1: Text -> Name
-- | Stage 2: gather global definitions
-- | Stage 3: initialize global definitions
-- | Stage 4: evaluate expressions with globals, locals, and names
type GLM = Compose (ReaderT (IORef NameTable) IO) (GGather Scoped)
-- | Scoped has GInit which tracks the state of initializing all global
-- | definitions, so they are all initialized once and circular dependencies
-- | are caught (TODO: define exactly what circular dependencies are).
-- | GLScope holds the global scope as it is *expected* to be defined, and
-- | also the local context that is pushed under binders and such.
type Scoped = GInit (ReaderT GLScope IO)
-- | Continuation monad, so `traverse` can adjust locals
type Scoping r = ContT r Scoped

willInitGLM :: Text -> (Name -> Scoped GlobalInfo) -> GLM (Name, Scoped GlobalInfo)
willInitGLM text creator = Compose $ mintName id text <&>
  \name -> (name,) <$> willInit name (creator name)

-- | For `@example`, for example
willUseGLM :: Scoped r -> GLM r
willUseGLM = Compose . pure . GGather mempty . const

initedGLM :: Name -> Scoped GlobalInfo
initedGLM n = do
  asks (M.lookup n . glGlobals) >>= \case
    Nothing -> error $ "Missing name: " <> show n
    Just i -> i

joinScoped :: GLM (Scoped r) -> GLM r
joinScoped (Compose stage0) = Compose $ stage0 <&>
  \(GGather outs ins) -> GGather outs $ join <$> ins

eval :: Term -> Scoped Eval
eval t = do
  c <- fmap snd <$> currentCtx
  pure $ E.eval c t

quote :: Eval -> Scoped Term
quote e = do
  c <- void <$> currentCtx
  pure $ E.quote c e

reinfer :: Term -> Scoped Eval
reinfer t = do
  c <- currentCtx
  pure $ U.quickTermType c t

validate :: Term -> Scoped Eval
validate t = do
  c <- currentCtx
  pure $! U.validate c t

conversionCheck :: Eval -> Eval -> Scoped Bool
conversionCheck e1 e2 = do
  c <- void <$> currentCtx
  pure $ U.conversionCheck c e1 e2

globalEval :: Term -> Scoped GlobalTerm
globalEval t = do
  e <- eval t
  pure $ GlobalTerm t e

globalQuote :: Eval -> Scoped GlobalTerm
globalQuote e = do
  t <- quote e
  pure $ GlobalTerm t e



runElabFull :: forall r. IORef NameTable -> GLM r -> IO (Map Name GlobalInfo, r)
runElabFull tbl (Compose stage0) = do
  -- First we provide the name table to mint all the names
  GGather items stage1 <- runReaderT stage0 tbl
  let
    -- Now we run a scoped computation
    stage2 :: Scoped (Map Name GlobalInfo, r)
    stage2 = do
      -- Do whatever computation the user asked for
      r <- stage1 items
      -- Ensure all of the items are elaborated
      env <- sequence items
      pure (env, r)
  -- Keep track of all the globals in state, and provide the default
  -- global context with no locals, plus the name table to mint more names
  (r, _) <- runReaderT (runStateT stage2 (Uninitialized <$ items))
    (GLScope tbl items M.empty Nil)
  pure r

runElabScoped :: IORef NameTable -> Scoped r -> IO r
runElabScoped tbl stage2 = do
  fmap fst $ runReaderT (runStateT stage2 M.empty) $
    GLScope tbl M.empty M.empty Nil




elaborateModule :: [Decl] -> GLM (Vector.Vector (Maybe Name, GlobalInfo))
elaborateModule decls = joinScoped do
  traverse elaborateDecl decls <&> \loading -> do
    loaded <- for loading \(name, cachedCreator) ->
      (name,) <$> cachedCreator
    pure $ Vector.fromList loaded

-- TODO: memoize
currentCtx :: Scoped EvalTypeCtx
currentCtx = do
  -- Here we want to gather all the things that have actually been defined
  initialized <- gets $ M.mapMaybe \case
    Initialized r -> Just r
    _ -> Nothing
  let currentGlobals = U.bootGlobals $ globalsFrom initialized
  localCtx <- asks glCtx
  pure $ localCtx { ctxGlobals = currentGlobals }

intoClosure :: Eval -> Closure -> (Eval -> Scoped r) -> Scoped r
intoClosure argTy clo cb = do
  outer <- ask
  let neutral = Neutral (NVar mempty (Level (size (glCtx outer)))) Nil
  local (const $ outer { glCtx = glCtx outer :> (BUnused, (argTy, ENeut neutral)) }) do
    cb $ E.instantiateClosure clo $ ENeut neutral


-- | Elaborate a top-level declaration. This tells the `GGather` layer about
-- | the name and definition, which is then available in the `GInit` layer to
-- | handle the graph of dependencies.
elaborateDecl :: Decl -> GLM (Maybe Name, Scoped GlobalInfo)
elaborateDecl = \case
  DDefine (Just (PlainName [] text), PlainVar) mty tm ->
    first Just <$> willInitGLM text \_name -> DefnGlobal <$> do
      elaborateDefn mty tm
  -- An example, e.g. declared by `@example` or `@define _ := Type`
  DDefine (Nothing, PlainVar) mty tm -> willUseGLM do
    tm' <- elaborateDefn mty tm
    pure (Nothing, pure $ DefnGlobal tm')

  -- Elaborating inductive types is by far the most complicated, it has
  -- a dedicated fnuction
  DDataType (Just (PlainName [] tyText), PlainVar) rawParams rawIndices mdest rawConstrs -> do
    ret <- first Just <$> willInitGLM tyText \name -> TypeGlobal <$> do
      elaborateDataType name rawParams rawIndices mdest rawConstrs
    for_ rawConstrs \(cname, _, _) -> do
      let
        ctor = case cname of
          (Just (PlainName [] ctext), PlainVar) -> ctext
          _ -> error "Bad constructor name"
      willInitGLM ctor \ctorName -> do
        tyName <- mintName glNames tyText
        asks (M.lookup tyName . glGlobals) >>= \case
          Just tyDef -> tyDef >>= \case
            TypeGlobal (GlobalTypeInfo _ _ ctors) -> do
              ctx <- currentCtx
              pure $ DefnGlobal $ fromMaybe (error "wat") $ M.lookup ctorName $ globalDefns $ ctxGlobals ctx
            _ -> error "Impossible"
          Nothing -> error "Impossible!"
    pure ret

  _ -> error "Not supported"

-- | Elaborate a type (optional) and a term of that type, into a "global"
-- | definition which caches the term and type as both `Term` and `Eval`.
-- | (The definition does not have to be global, just the wrapper is called that.)
elaborateDefn :: Maybe CST -> CST -> Scoped GlobalDefn
elaborateDefn mty tm = do
  mty' <- for mty \ty -> do
    tyT <- elabType ty
    tyE <- eval tyT
    pure (tyT, tyE)
  tmT <- elab (snd <$> mty') tm
  ty' <- case mty' of
    Just (tyT, tyE) -> pure $ GlobalTerm tyT tyE
    Nothing -> globalQuote =<< reinfer tmT
  -- TODO: arity
  GlobalDefn 0 ty' <$> globalEval tmT


elabType :: CST -> Scoped Term
elabType = elab Nothing -- TODO: Type

-- | Coerce a synthesized term to an expected type, if provided.
synth :: Maybe ("expected type" @:: Eval) -> Term -> Scoped Term
synth Nothing term = pure term
synth (Just expE) term = do
  actE <- reinfer term
  fromMaybe term <$> do
    coe term (actE, expE) >>= traverse
      \result -> do
        actE' <- reinfer result
        conversionCheck actE' expE >>= \case
          True -> pure result
          False -> error "Synthesized coercion failed"

-- | Generate a term coerced from actual type to expected type, or `Nothing` if
-- | no coercion is necessary.
coe :: Term -> ("actual type" @:: Eval, "expected type" @:: Eval) -> Scoped (Maybe Term)
coe term = \case
  -- Both are lifted terms? operate inside the lifted value
  (ELift _ actE, ELift _ expE) -> do
    coeMap (TQuote mempty) (TSplice mempty) (actE, expE)
  -- Lifted term where it is not expected?
  (ELift _ actE, expE) -> do
    -- Splice, and continue coercing
    Just <$> coe' (TSplice mempty term) (actE, expE)
  -- Otherwise make sure they match literally
  (actE, expE) -> conversionCheck actE expE >>= \case
    True -> pure Nothing
    False -> error "Synthesized type mismatch"
  where
  coe' inner tys = fromMaybe inner <$> coe inner tys
  coeMap outOf inTo tys = fmap @Maybe outOf <$> coe (inTo term) tys

-- | Elaborate a piece of surface syntax against an expected type.
elab :: Maybe ("expected type" @:: Eval) -> CST -> Scoped Term
elab mexp = \case
  CApps fun args -> synth mexp =<< do
    funTmT <- elab Nothing fun
    funTyE <- validate funTmT
    let
      thingy (_, EPi _ Implicit _ _ _) _ = error "cannot handle implicits"
      thingy (funT, EPi _ Explicit _ argTy clo) arg = do
        argT <- elab (Just argTy) arg
        argE <- eval argT
        pure (TApp mempty Explicit funT argT, E.instantiateClosure clo argE)
      thingy _ _ = error "not a function/overapplied"
    -- TODO: stash type?
    fst <$> foldlM thingy (funTmT, funTyE) args
  CUniv -> synth mexp $ TUniv mempty (UBase 0)

  CLambda binders body -> elabBinders (TLambda mempty) binders body
  CPi     binders body -> elabBinders (TPi     mempty) binders body
  CSigma  binders body -> elabBinders (TSigma  mempty) binders body
  -- | CLet    ![(CBinder, "ty" @:: Maybe CST, "tm" @:: CST)]    !CST

  -- | CSentence !(NonEmpty (Either L.OpForm CST))

  CVar (Just (PlainName [] text)) PlainVar -> synth mexp =<< do
    name <- mintName glNames text
    asks (M.lookup name . glLocals) >>= \case
      Just (_ :> e) -> quote e
      _ -> asks (M.lookup name . glGlobals) >>= \case
        Just getter -> getter <&> \case
          TypeGlobal (GlobalTypeInfo { typeParams, typeIndices }) ->
            let
              abstract ((p, b, paramType) : more) focus =
                TLambda mempty p b paramType $ Scoped $ abstract more focus
              abstract [] focus = focus

              toVars :: forall i. Int -> Vector.Vector i -> Vector.Vector Term
              toVars skipped = mapWithLevel \(_, Index idx) _ ->
                TVar mempty $ Index $ idx + skipped
            in abstract (Vector.toList typeParams <> Vector.toList typeIndices) $
              TTyCtor mempty name (toVars (Vector.length typeIndices) typeParams) (toVars 0 typeIndices)
          DefnGlobal (GlobalDefn _ _ _) -> TGlobal mempty name
        _ -> error $ "Missing name: " <> show name
  CVar Nothing idxOrLvl -> synth mexp =<< case idxOrLvl of
    PlainVar -> error "impossible: CVar Nothing PlainVar"
    DBIndex i -> do
      c <- currentCtx
      pure $ TVar mempty $ index c i
    DBLevel l -> do
      c <- currentCtx
      pure $ TVar mempty $ index c $ level c l
  CVar (Just (PlainName [] text)) idxOrLvl -> synth mexp =<< do
    name <- mintName glNames text
    asks (M.lookup name . glLocals) >>= \case
      Just stack | Just found <- stack @@? idxOrLvl -> do
        quote found
      Just _ -> error $ "Local stack too small: " <> T.unpack (nameText name)
      Nothing -> error $ "Missing local: " <> T.unpack (nameText name)

  -- | CMod  ![Text]

  -- | CNum !Text
  -- | CStr ![Either Text CST]
  -- | CHole !(Maybe Text)

  CLift t -> synth mexp . TLift mempty =<< elabType t
  CQuote e -> do
    mexp' <- case mexp of
      Just (ELift _ exp') -> pure (Just exp')
      Just _ -> error "Quote needs to go to a lifted type"
      Nothing -> pure Nothing
    TQuote mempty <$> elab mexp' e
  CSplice e -> TSplice mempty <$> elab (ELift mempty <$> mexp) e

  -- | CMatch ![CST] !("cases" @:: [("pats" @:: [CST], "body" @:: CST)])
  CField tm field -> do
    name <- mintName glNames field
    tm' <- elab Nothing tm
    pure $ TField mempty tm' name

  CAscribe tm ty -> do
    tyT <- elabType ty
    tyE <- eval tyT
    tmT <- elab (Just tyE) tm
    tmtyE <- validate tmT
    conversionCheck tyE tmtyE >>= \case
      True -> pure tmT
      False -> do
        tyN <- quote tyE
        tmtyT <- quote tmtyE
        ps <- asks (P.PS 0 . size . glCtx)
        error $ fold
          [ "Type error: "
          , "\n" <> T.unpack do P.format P.Ansi $ P.printCore tyN ps
          , "\n" <> T.unpack do P.format P.Ansi $ P.printCore tmtyT ps
          , "\n" <> T.unpack do P.format P.Ansi $ P.printCore tmT ps
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
    tyE <- eval tyT
    runContT (elabMultiBinderCont tyE binder) \binderB ->
      multiCons plicit binderB tyT <$> inner
  multiCons plicit bounders tyT inner =
    foldr (\(i, b) -> cons plicit b (E.shift i tyT) . Scoped)
      inner
      (zip [0..] (NE.toList bounders))

elabBinder1 :: ("ty" @:: Eval) -> CBinder -> Scoped (Binder, GLScope -> GLScope)
elabBinder1 tyE = \case
  CVar (Just (PlainName [] text)) PlainVar -> do
    name <- mintName glNames text
    let binder = BVar (Meta (canonicalName name))
    pure $ (binder, ) $ \outer ->
      let neutral = Neutral (NVar mempty (Level (size (glCtx outer)))) Nil
          addVar = name & M.alter do Just . (:> ENeut neutral) . fromMaybe Nil
      in outer { glLocals = addVar (glLocals outer), glCtx = glCtx outer :> (binder, (tyE, ENeut neutral)) }
  CPlaceholder -> do
    pure $ (BUnused,) $ \outer ->
      let neutral = Neutral (NVar mempty (Level (size (glCtx outer)))) Nil
      in outer { glCtx = glCtx outer :> (BUnused, (tyE, ENeut neutral)) }
  CAssign l r -> do
    (b1, f1) <- elabBinder1 tyE l
    (b2, f2) <- elabBinder1 tyE r
    pure (BMulti b1 b2, f2 . f1)
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


elaborateDataType :: Name -> [CBinderGroup] -> [CBinderGroup] -> Maybe CST -> [(VariableName, "arguments" @:: [CBinderGroup], "result" @:: Maybe CST)] -> Scoped GlobalTypeInfo
elaborateDataType name rawParams rawIndices mdest rawConstrs = do
  (newParams, newIndices) <- evalContT do
    termParams <- processBinders rawParams $
      error "Missing type for datatype parameter"
    explicitTermIndices <- processBinders rawIndices $
      error "Missing type for datatype index"
    implicitTermIndices <- fromMaybe [] <$> for mdest \dest -> lift do
      term <- elabType dest
      e <- eval term
      fst <$> peelToUniv e
    let termIndices = explicitTermIndices <> implicitTermIndices
    pure (Vector.fromList termParams, Vector.fromList termIndices)
  let prelim = GlobalTypeInfo newParams newIndices M.empty
  modify' $ M.insert name $ Initializing $ Just $ TypeGlobal prelim
  constructors <- for rawConstrs \(cname, argTypes, resultType) -> do
    ctor <- case cname of
      (Just (PlainName [] text), PlainVar) -> mintName glNames text
      _ -> error "Bad constructor name"
    (ctor,) <$> evalContT do
      explicitArguments <- processBinders argTypes $
        error "Missing type for constructor argument"
      (implicitArguments, (params, indices)) <- do
        fromMaybe mempty <$> for resultType \r -> do
          rE <- lift $ eval =<< elabType r
          peelToTyCtor rE
      for_ (zip [0..] (Vector.toList params)) \case
        (i, ENeut (Neutral (NVar _ (Level j)) Nil)) | i == j -> pure ()
        _ -> error "Bad constructor parameter: must be a plain variable, in order"
      let ctorArguments = Vector.fromList (explicitArguments <> implicitArguments)
      ctorIndices <- lift $ traverse quote indices
      pure $ ConstructorInfo ctorArguments ctorIndices
  pure $ GlobalTypeInfo newParams newIndices (M.fromList constructors)
  where
  multiCons plicit bounders tyT =
    foldr (\(i, b) -> (:) (plicit, b, E.shift i tyT))
      []
      (zip [0..] (NE.toList bounders))
  processBinders :: forall c. [CBinderGroup] -> (forall void. Scoped void) -> Scoping c [(Plicit, Binder, Term)]
  processBinders rawBinders nope =
    join <$> for rawBinders \(plicit, binder, mty) -> do
      tyT <- lift case mty of
        Nothing -> nope
        Just ty -> elab Nothing ty
      tyE <- lift $ eval tyT
      multiCons plicit <$> elabMultiBinderCont tyE binder <*> pure tyT
  peelToUniv :: Eval -> Scoped ([(Plicit, Binder, Term)], ULevel)
  peelToUniv = \case
    EPi _ plicit binder indexTy inner -> do
      idx <- quote indexTy
      first ((plicit, binder, idx) :) <$>
        intoClosure indexTy inner peelToUniv
    EUniv _ univ -> pure ([], univ)
    _ -> error "Bad annotation for datatype"
  peelToTyCtor :: forall c. Eval -> Scoping c ([(Plicit, Binder, Term)], ("params" @:: Vector.Vector Eval, "indices" @:: Vector.Vector Eval))
  peelToTyCtor = \case
    EPi _ plicit binder indexTy inner -> do
      idx <- lift $ quote indexTy
      peeled <- ContT $ intoClosure indexTy inner
      first ((plicit, binder, idx) :) <$> peelToTyCtor peeled
    ETyCtor _ tyName params indices -> do
      when (tyName /= name) do
        error "Constructor for wrong datatype"
      pure ([], (params, indices))
    _ -> error "Bad annotation for constructor"
