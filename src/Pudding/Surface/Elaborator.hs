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
{-# LANGUAGE ApplicativeDo, PartialTypeSignatures #-}
module Pudding.Surface.Elaborator where

import Prelude hiding (exp)

import Data.Functor ((<&>))
import Data.Function ((&))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Pudding.Types.Name (Name(..), internalize, NameTable, canonicalName, CanonicalName (chosenName))
import Pudding.Types.Base (Plicit(..), type (@::))
import Pudding.Types.Metadata
import Pudding.Types.Stack (Stack, ToLevel(level), ToIndex(index), Level(Level), pattern Nil, pattern (:>), (@@?), size)
import Control.Monad.State.Strict (StateT (runStateT), gets, modify', MonadIO (liftIO), MonadTrans (lift), MonadState)
import Pudding.Core.Types (GlobalInfo(..), Term(..), GlobalDefn (GlobalDefn), GlobalTerm (GlobalTerm), Binder (BVar, BUnused, BMulti, BFresh, BPair), ScopedTerm (Scoped), Eval(..), Neutral (Neutral), NeutFocus (NVar, NGlobal), ULevel (ULevel), Ctx (Ctx), GlobalTypeInfo (GlobalTypeInfo), Closure (Closure, ConstClosure), ConstructorInfo (ConstructorInfo), Globals (globalDefns), arityOfTerm, RequestSubsumption (IdentitySubsumption, GenerateSubsumption), UnifyDir (RSubsumesL, Invariant), UnifyMode (UnifyMode), Unifying (Unifying), addGlobal, freshGlobals, pattern ENeutral, pattern ENeutralVar, pattern ENeutralHole)
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Data.IORef (IORef)
import Pudding.Surface.Parser (Decl(..), CST(..), CBinder, CBinderGroup, RawAttribute (RawAttribute), Attributes (aNormalize, Attributes))
import Data.Foldable (foldlM, for_)
import Data.Functor.Compose (Compose (Compose))
import Control.Monad.Reader.Class (MonadReader (local), asks)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Pudding.Core.Eval as E
import Pudding.Surface.Lexer (VariableDB(..), NameForm(..), VariableName)
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import Control.Arrow (Arrow(first))
import qualified Data.List.NonEmpty as NE
import Data.Traversable (for)
import qualified Data.Vector as Vector
import Control.Monad (join, when)
import GHC.Stack (HasCallStack)
import qualified Data.List as List
import Data.Monoid (Any(Any), Endo (Endo))
import qualified Data.Foldable as F
import Pudding.Types.Monads (Freshener(freshen), eval, quote, reinfer)
import qualified Pudding.Types.Monads as M
import Data.Pair (Pair(..))
import Pudding.Types.Monads.Prover (Prover (Prover), runProverMonad, ProverS (proofGlobals, uvState, uvConstraints))
import Pudding.Types.Config (Field(dflt))
import Pudding.Types.Monads.Cont1T (Cont1T, adaptCont1, runCont1pT, evalCont1pT, localizeCont1)
import Pudding.Core.Boot (typeAuxDefns)
import Data.Generics.Constructor (ctorName)
import qualified Data.IntMap.Strict as IntMap
import Pudding.Types.Monads.Types (UnivarState, AfterSolve)
import qualified Pudding.Core.Eval as Eval

class Applicative m => TwoPhase m where
  twoPhases :: m (m r) -> m r



-- | Gather global names. Merely an applicative, not a monad.
data GGather m r = GGather
  (Map Name (m GlobalInfo))
  (Map Name (m GlobalInfo) -> m r)
  deriving (Functor)

instance Applicative m => Applicative (GGather m) where
  pure = GGather Map.empty . const . pure
  liftA2 f (GGather ml cl) (GGather mr cr) = GGather
    (Map.unionWith (\_ r -> r) ml mr)
    (liftA2 (liftA2 f) cl cr)

instance Monad m => TwoPhase (GGather m) where
  twoPhases (GGather m1 c1) = GGather m1 \m2 ->
    c1 m2 >>= \case
      GGather m3 c2 -> c2 (Map.unionWith (\_ r -> r) m2 m3)

type GInit = StateT (Map Name (Initializing GlobalInfo))

data Initializing t
  = Uninitialized
  | Initializing (Maybe t)
  | InitFailed
  | Initialized t
  deriving (Eq, Ord, Functor, Foldable, Traversable)

willInit :: forall m. Monad m => Name -> GInit m GlobalInfo -> GGather (GInit m) (GInit m GlobalInfo)
willInit !n creator = GGather (Map.singleton n cachedCreator)
  \_items -> pure cachedCreator
  where
  cachedCreator :: GInit m GlobalInfo
  cachedCreator = do
    gets (Map.lookup n) >>= \case
      Nothing -> error $ "Missing name: " <> show n
      Just InitFailed -> error $ "Init failed: " <> show n
      Just (Initialized r) -> pure r
      Just (Initializing (Just r)) -> pure r
      Just (Initializing Nothing) -> error $ "Circular dependency: " <> show n
      Just Uninitialized -> do
        modify' $ Map.insert n (Initializing Nothing)
        r <- creator
        modify' $ Map.insert n (Initialized r)
        pure r

inited :: forall m. Monad m => Name -> GGather (GInit m) GlobalInfo
inited !n = GGather Map.empty \items ->
  case Map.lookup n items of
    Nothing -> error $ "Missing name: " <> show n
    Just r -> r

data GLScope = GLScope
  { glNames :: IORef NameTable
  , glGlobals :: Map Name (Scoped GlobalInfo)
  , glLocals :: Map Name (Stack Eval)
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
type Scoped = GInit (ReaderT GLScope Prover)
-- | Continuation monad, so `traverse` can adjust locals
type Scoping r = Cont1T r Scoped
-- | Abstract over both
type ScopeLike m =
  (MonadState (Map Name (Initializing GlobalInfo)) m, MonadReader GLScope m, M.Evaling m)



willInitGLM :: Text -> (Name -> Scoped GlobalInfo) -> GLM (Name, Scoped GlobalInfo)
willInitGLM text creator = Compose $ mintName id text <&>
  -- TODO: better way than clearLocals?
  \name -> (name,) <$> willInit name do
    result <- clearLocals (creator name)
    addProofGlobal name result
    pure result

clearLocals :: Scoped r -> Scoped r
clearLocals inner = do
  let clearGL gl = gl { glLocals = Map.empty }
  g <- M.askGlobals
  local clearGL $ M.withCtx (Ctx g Nil) inner

-- | For `@example`, for example
willUseGLM :: Scoped r -> GLM r
willUseGLM = Compose . pure . GGather mempty . const . clearLocals

initedGLM :: Name -> Scoped GlobalInfo
initedGLM n = do
  asks (Map.lookup n . glGlobals) >>= \case
    Nothing -> error $ "Missing name: " <> show n
    Just i -> i

joinScoped :: GLM (Scoped r) -> GLM r
joinScoped (Compose stage0) = Compose $ stage0 <&>
  \(GGather outs ins) -> GGather outs $ join <$> ins

normalize :: HasCallStack => Bool -> Term -> Scoped Term
normalize ridGlobals t = do
  c <- M.askEvalCtx
  pure $ (if ridGlobals then E.selfContained else E.normalizeCtx) c t

withForced :: forall m r. ScopeLike m => HasCallStack => (Eval -> m r) -> Eval -> m r
withForced f e = do
  let e' = E.undeferred e
  e'' <- fromMaybe e' <$> M.forceNeutral e'
  f e''


runElabFull :: forall r. IORef NameTable -> GLM r -> IO ((Globals, IntMap.IntMap UnivarState, AfterSolve), r)
runElabFull tbl (Compose stage0) = do
  -- First we provide the name table to mint all the names
  GGather items stage1 <- runReaderT stage0 tbl
  let
    -- Now we run a scoped computation
    stage2 :: Scoped (_, r)
    stage2 = do
      -- Do whatever computation the user asked for
      r <- stage1 items
      -- Ensure all of the items are elaborated
      env <- M.askGlobals
      lift $ lift $ Prover do
        univars <- gets uvState
        constraints <- gets uvConstraints
        pure ((env, univars, constraints), r)
  -- Keep track of all the globals in state, and provide the default
  -- global context with no locals, plus the name table to mint more names
  (r, _) <- runProverMonad dflt $ runReaderT (runStateT stage2 (Uninitialized <$ items))
    (GLScope tbl items Map.empty)
  pure r

runElabScoped :: IORef NameTable -> Scoped r -> IO r
runElabScoped tbl stage2 = do
  fmap fst $ runProverMonad dflt $ runReaderT (runStateT stage2 Map.empty) $
    GLScope tbl Map.empty Map.empty




elaborateModule :: [Decl] -> GLM (Vector.Vector (Maybe Name, GlobalInfo))
elaborateModule decls = joinScoped do
  traverse elaborateDecl decls <&> \loading -> do
    loaded <- for loading \(name, cachedCreator) ->
      (name,) <$> cachedCreator
    pure $ Vector.fromList loaded

intoClosure :: Eval -> Closure -> (Eval -> Scoped r) -> Scoped r
intoClosure argTy clo =
  runCont1pT (intoClosure1 argTy clo)

intoClosure1 :: Eval -> Closure -> Cont1T r Scoped Eval
intoClosure1 argTy clo = do
  let
    bdr = case clo of
      Closure _ b _ -> b
      ConstClosure _ -> BUnused
  (_lvl, neut) <- M.bindNeut1 mempty bdr argTy
  pure $ E.instantiateClosure clo neut

parseAttributes :: [RawAttribute] -> Attributes
parseAttributes = foldMap \case
  RawAttribute [] "normalize" [] -> mempty { aNormalize = Any True }
  _ -> mempty

mayNormalize :: HasCallStack => Attributes -> Term -> Scoped Term
mayNormalize (Attributes { aNormalize = Any True }) = normalize True
mayNormalize _ = pure


-- | Elaborate a top-level declaration. This tells the `GGather` layer about
-- | the name and definition, which is then available in the `GInit` layer to
-- | handle the graph of dependencies.
elaborateDecl :: Decl -> GLM (Maybe Name, Scoped GlobalInfo)
elaborateDecl = \case
  DDefine attrs (Just (PlainName [] text), PlainVar) mty tm ->
    first Just <$> willInitGLM text \_name -> DefnGlobal <$> do
      elaborateDefn (parseAttributes attrs) mty tm
  -- An example, e.g. declared by `@example` or `@define _ := Type`
  DDefine attrs (Nothing, PlainVar) mty tm -> willUseGLM do
    tm' <- elaborateDefn (parseAttributes attrs) mty tm
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
        asks (Map.lookup tyName . glGlobals) >>= \case
          Just tyDef -> tyDef >>= \case
            TypeGlobal (GlobalTypeInfo _ _ _ctors) -> do
              ctx <- M.askGlobals
              pure $ DefnGlobal $ fromMaybe (error "wat") $ Map.lookup ctorName $ globalDefns ctx
            _ -> error "Impossible"
          Nothing -> error "Impossible!"
    pure ret

  decl -> error $ "Not supported: " <> ctorName decl

-- | Elaborate a type (optional) and a term of that type, into a "global"
-- | definition which caches the term and type as both `Term` and `Eval`.
-- | (The definition does not have to be global, just the wrapper is called that.)
elaborateDefn :: HasCallStack => Attributes -> Maybe CST -> CST -> Scoped GlobalDefn
elaborateDefn attrs mty tm = do
  -- lift . lift . evaluate . force =<< do
    mty' <- for mty \ty -> do
      tyTm <- elabType ty
      tyEv <- eval tyTm
      pure (tyTm, tyEv)
    tmT0 <- elab (snd <$> mty') tm
    tmT <- mayNormalize attrs tmT0
    ty' <- case mty' of
      Just (tyTm, tyEv) -> pure $ GlobalTerm tyTm tyEv
      Nothing -> M.globalQuote =<< reinfer tmT
    GlobalDefn (arityOfTerm tmT) ty' <$> M.globalEval tmT


elabType :: HasCallStack => CST -> Scoped Term
elabType cst = do
  (_, _, univ) <- M.freshUniv
  elab (Just univ) cst

elabEvalType :: HasCallStack => CST -> Scoped Eval
elabEvalType cst = elabType cst >>= M.eval

elabAndEval :: HasCallStack => Maybe ("expected type" @:: Eval) -> CST -> Scoped (Term, Eval)
elabAndEval mty cst = do
  tm <- elab mty cst
  (tm,) <$> M.eval tm

-- | Coerce a synthesized term to an expected type, if provided.
synth :: HasCallStack => Maybe ("expected type" @:: Eval) -> Term -> Scoped Term
synth Nothing term = pure term
synth (Just expE) term = do
  actE <- reinfer term
  fromMaybe term <$> coe term (actE, expE)

-- | Generate a term coerced from actual type to expected type, or `Nothing` if
-- | no coercion is necessary.
coe :: HasCallStack => Term -> ("actual type" @:: Eval, "expected type" @:: Eval) -> Scoped (Maybe Term)
coe term (actE, expE) = do
  (_tys, coercion) <- M.subsume (UnifyMode RSubsumesL GenerateSubsumption Unifying) (actE :# expE)
  for coercion \fn ->
    TApp mempty Explicit <$> M.quote fn <*> pure term

-- | Elaborate a piece of surface syntax against an expected type.
elab :: HasCallStack => Maybe ("expected type" @:: Eval) -> CST -> Scoped Term
elab mexp = \case
  CApps fun args -> synth mexp =<< do
    funTmT <- elab Nothing fun
    funTyE <- M.validate funTmT
    let
      prethingy (funT, funTy) arg = do
        funTy' <- fromMaybe funTy <$> M.forceNeutral funTy
        thingy (funT, funTy') arg
      thingy (funT, EPi _ Explicit _ argTy clo) arg = do
        (argT, argE) <- elabAndEval (Just argTy) arg
        pure (TApp mempty Explicit funT argT, E.instantiateClosure clo argE)
      thingy (funT, EPi _ implicit _ impTy clo) arg = do
        (_, impT, impE) <- M.initUVTerm impTy
        thingy (TApp mempty implicit funT impT, E.instantiateClosure clo impE) arg
      thingy (funT, univar@(ENeutralHole _ which locals spine@Nil)) arg = do
        -- FIXME assert the hole has a universe type
        (_, _, dom0) <- M.initUVType
        (argT, argE) <- elabAndEval (Just dom0) arg
        -- Maybe it was solved
        -- TODO: instantiate univars but do not force globals
        dom <- fromMaybe dom0 <$> M.forceNeutral dom0
        (_, codT, cod) <- M.bindNeut mempty BFresh dom \_ _ -> M.initUVType
        clo <- M.bindClosure BFresh $ Scoped codT
        -- Instantiate the univar
        let
          -- FIXME: is this the right scope and such?
          synthesized = EPi mempty Explicit BFresh dom clo
        _ <- M.subsume (UnifyMode Invariant IdentitySubsumption Unifying)
          (univar :# synthesized)
        pure (TApp mempty Explicit funT argT, Eval.instantiateClosure clo argE)
      thingy _ _ = error "not a function/overapplied"

      -- TODO: have metadata to indicate a constructor, so this is cheap
      peel :: Stack Term -> (Term, Term) -> Maybe Term
      peel as (TLambda _ _ _ _ (Scoped b), TApp _ _ f a) = peel (as :> a) (b, f)
      peel as (TTyCtor meta name xs _, _) = Just $
        uncurry (TTyCtor meta name) (Vector.splitAt (Vector.length xs) $ Vector.fromList $ F.toList as)
      peel as (TTmCtor meta name xs _, _) = Just $
        uncurry (TTmCtor meta name) (Vector.splitAt (Vector.length xs) $ Vector.fromList $ F.toList as)
      peel _ _ = Nothing

      inlineConstructor appliedT =
        fromMaybe appliedT $ peel Nil (funTmT, appliedT)
    -- TODO: stash type?
    inlineConstructor . fst <$> foldlM prethingy (funTmT, funTyE) args
  CUniv -> do
    lvl <- ULevel <$> freshen <*> freshen
    synth mexp $ TUniv mempty lvl

  -- TODO: elab against Pi type
  CLambda binders body -> elabBinders (TLambda mempty) binders [] $ elab Nothing body
  CPi     binders body -> elabBinders (TPi     mempty) binders [] $ elabType body
  CSigma  binders body -> elabBinders (TSigma  mempty) binders [] $ elabType body
  -- | CLet    ![(CBinder, "ty" @:: Maybe CST, "tm" @:: CST)]    !CST

  -- | CSentence !(NonEmpty (Either L.OpForm CST))

  CVar (Just (PlainName [] text)) PlainVar -> synth mexp =<< do
    name <- mintName glNames text
    here <- asks id
    asks (Map.lookup name . glLocals) >>= \case
      Just (_ :> e) -> quote e
      _ -> asks (Map.lookup name . glGlobals) >>= \case
        Just getter -> getter <&> \case
          TypeGlobal (GlobalTypeInfo _ _ _) ->
            TGlobal mempty name
          DefnGlobal (GlobalDefn _ _ _) -> TGlobal mempty name
        _ -> error $ "Missing name: " <> show name <> " " <> show (Map.keys (glLocals here)) <> " " <> show (Map.keys (glGlobals here))
  CVar Nothing idxOrLvl -> synth mexp =<< case idxOrLvl of
    PlainVar -> error "impossible: CVar Nothing PlainVar"
    DBIndex i -> do
      c <- M.askCtx
      pure $ TVar mempty $ index c i
    DBLevel l -> do
      c <- M.askCtx
      pure $ TVar mempty $ index c $ level c l
  CVar (Just (PlainName [] text)) idxOrLvl -> synth mexp =<< do
    name <- mintName glNames text
    asks (Map.lookup name . glLocals) >>= \case
      Just stack | Just found <- stack @@? idxOrLvl -> do
        quote found
      Just _ -> error $ "Local stack too small: " <> T.unpack (nameText name)
      Nothing -> error $ "Missing local: " <> T.unpack (nameText name)

  -- | CMod  ![Text]

  -- | CNum !Text
  -- | CStr ![Either Text CST]

  CPlaceholder -> elab mexp (CHole Nothing Nothing)
  CHole _name Nothing -> do
    ty <- case mexp of
      Nothing -> M.initUVType <&> \(_, _, e) -> e
      Just e -> pure e
    (_, tm, _) <- M.initUVTerm ty
    pure tm
  CHole _name (Just _) -> error "CHole should not come with context filled"

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

  CPair l r | Just exp@(ESigma _ _ _ lTy (ConstClosure rTy)) <- mexp -> do
    lT <- elab (Just lTy) l
    rT <- elab (Just rTy) r
    expT <- quote exp
    pure $ TPair mempty expT lT rT
  CPair l r | Just exp@(ESigma _ _ _ lTy rTy) <- mexp -> do
    (lT, lE) <- elabAndEval (Just lTy) l
    rT <- elab (Just (E.instantiateClosure rTy lE)) r
    expT <- quote exp
    pure $ TPair mempty expT lT rT
  -- Synthesize a non-dependent pair
  CPair l r | Nothing <- mexp -> do
    lT <- elab Nothing l
    lTy <- M.reinfer lT
    rT <- elab Nothing r
    rTy <- M.reinfer rT
    ty <- M.quote $ ESigma mempty Explicit BUnused lTy $ ConstClosure $ rTy
    pure $ TPair mempty ty lT rT

  CAscribe tm ty -> do
    tyT <- elabType ty
    tyE <- eval tyT
    tmT <- elab (Just tyE) tm
    pure (TAscribe mempty tmT tyT)

  -- | CAssign !CST !CST -- for patterns and do notation

  cst -> error $ "Cannot elaborate yet: " <> show cst

elabBinders ::
  (Plicit -> Binder -> Term -> ScopedTerm -> Term) ->
  NonEmpty (Plicit, NonEmpty CBinder, "ty" @:: Maybe CST) -> [Eval] -> Scoped Term -> Scoped Term
elabBinders cons binders telescope elabBody = do
  runCont1pT (foldMap addBinder binders) \(Endo wrap) ->
    wrap <$> elabBody
  where
  addBinder :: (Plicit, NonEmpty CBinder, Maybe CST) -> Cont1T r Scoped (Endo Term)
  addBinder (plicit, binder, mty) = do
    tyT <- lift case mty of
      Nothing -> M.initUVType <&> \(_, ty, _) -> ty
      Just ty -> elabType ty
    tyE <- eval tyT
    elabMultiBinder tyE binder <&> \binderB ->
      Endo (multiCons plicit binderB tyT)
  multiCons plicit bounders tyT inner =
    foldr (\(i, b) -> cons plicit b (E.shift i tyT) . Scoped)
      inner
      (zip [0..] (NE.toList bounders))

elabBinder1 :: ("ty" @:: Eval) -> CBinder -> Cont1T r Scoped Binder
elabBinder1 tyE = \case
  CVar (Just (PlainName [] text)) PlainVar -> do
    name <- mintName glNames text
    let binder = BVar (Meta (canonicalName name))
    (_, neutral) <- M.bindNeut1 mempty binder tyE
    localizeCont1 \outer ->
      let addVar = name & Map.alter do Just . (:> neutral) . fromMaybe Nil
      in outer { glLocals = addVar (glLocals outer) }
    pure binder
  CPlaceholder ->
    BUnused <$ M.bindNeut1 mempty BUnused tyE
  CAssign l r -> BMulti
    <$> elabBinder1 tyE l
    <*> elabBinder1 tyE r
  bdr -> error $ "Bad/unsupported binder: " <> ctorName bdr

elabMultiBinder :: ("ty" @:: Eval) -> NonEmpty CBinder -> Cont1T c Scoped (NonEmpty Binder)
elabMultiBinder tyE = traverse (elabBinder1 tyE)

localize :: MonadReader r m => a -> (r -> r) -> Cont1T c m a
localize c f = c <$ adaptCont1 (local f)


-- Add an entry to the Globals, stored in the Prover part of the stack.
-- `willInitGLM` already uses this for when something is fully initialized,
-- but partial initialization is done manually, and inductive types add
-- additional declarations to globals too.
addProofGlobal :: Name -> GlobalInfo -> Scoped ()
addProofGlobal name decl =
  lift . lift $ Prover $ modify' \s -> s
    { proofGlobals = Just $ addGlobal (fromMaybe freshGlobals $ proofGlobals s) name decl }

addTypeAuxDefns :: HasCallStack => Name -> GlobalTypeInfo -> Scoped ()
addTypeAuxDefns name final =
  for_ (typeAuxDefns name final) \(auxName, tm) -> do
    ty <- M.reinfer tm
    defn <- GlobalDefn (arityOfTerm tm)
      <$> M.globalQuote ty
      <*> M.globalEval  tm
    addProofGlobal auxName $ DefnGlobal defn




-- Elaborating an inductive type is a multi-step process
elaborateDataType :: Name -> [CBinderGroup] -> [CBinderGroup] -> Maybe CST -> [(VariableName, "arguments" @:: [CBinderGroup], "result" @:: Maybe CST)] -> Scoped GlobalTypeInfo
elaborateDataType name rawParams rawIndices mdest rawConstrs = do
  -- First we need to process two groups of binders, to determine the parameters
  -- and indices of the inductive type
  (newParams, newIndices) <- evalCont1pT do
    -- Parameters are listed first; enter that telescoping context
    termParams <- processBinders rawParams
    -- Indices may be listed next
    explicitTermIndices <- processBinders rawIndices
    -- Finally the type may reduce to a Pi type, providing more indices
    implicitTermIndices <- fromMaybe [] <$> for mdest \dest -> lift do
      ty <- elabEvalType dest
      -- But it must end in a universe, like `Type`
      fst <$> peelToUniv ty
    let termIndices = explicitTermIndices <> implicitTermIndices
    pure (Vector.fromList termParams, Vector.fromList termIndices)

  -- Provisionally initialize an empty inductive datatype, so that it exists
  -- with the correct type while checking each constructor
  let prelim = GlobalTypeInfo newParams newIndices Map.empty
  -- This is the only place that `Initializing $ Just` is used
  modify' $ Map.insert name $ Initializing $ Just $ TypeGlobal prelim
  addProofGlobal name $ TypeGlobal prelim
  addTypeAuxDefns name prelim

  -- Now loop over the constructors, in order.
  -- (Order matters for the user, not semantically)
  constructors <- for rawConstrs \(cname, argTypes, resultType) -> do
    -- It must be a plain name
    ctor <- case cname of
      (Just (PlainName [] text), PlainVar) -> mintName glNames text
      _ -> error "Bad constructor name"
    -- Process binders, this time representing the parameters then arguments
    -- of the constructor: the parameters are boringly repeated, as they must be,
    -- while the arguments represent the actual data that the constructor holds,
    -- which becomes available for pattern matching.
    (ctor,) <$> evalCont1pT do
      -- Explicit binders
      explicitArguments <- processBinders argTypes
      -- Again, it can result in a pi type with more binders
      (implicitArguments, (params, indices)) <- do
        fromMaybe mempty <$> for resultType \r -> do
          rE <- lift $ elabEvalType r
          -- But it must end with the type constructor that names the type,
          -- instantiated with all parameters and indices
          peelToTyCtor rE
      -- Check that the parameters are boringly correct
      for_ (zip [0..] (Vector.toList params)) \case
        (i, ENeut (Neutral (NVar _ (Level j)) Nil)) | i == j -> pure ()
        (i, ENeut (Neutral (NVar _ (Level j)) Nil)) -> error $ "Bad constructor parameter " <> show ctor <> ": " <> show i <> " /= " <> show j
        _ -> error "Bad constructor parameter: must be a plain variable, in order"
      -- Get the arguments, coming after the parameters
      let ctorArguments = Vector.fromList $ List.drop (Vector.length params) $ explicitArguments <> implicitArguments
      -- Because the indices are coming from an evaluated type, they need to be quoted back
      -- TODO: might be nice to preserve the original terms, in simple cases
      ctorIndices <- lift $ traverse quote indices
      -- ctx <- M.askCtx
      -- ctx' <- lift $ traverse (quote . snd . snd) $ ctxStack ctx
      -- Dbg.traceM $ show $ C.Print.formatCoreFrom C.Print.Plain (size ctx) <$> view (from stack) ctx'
      -- ctx'' <- lift $ traverse (quote . fst . snd) $ ctxStack ctx
      -- Dbg.traceM $ show $ C.Print.formatCoreFrom C.Print.Plain (size ctx) <$> view (from stack) ctx''
      -- Dbg.traceM $ show $ C.Print.formatCoreFrom C.Print.Plain (size ctx) <$> ctorIndices

      -- Crystallize this information into the heartless core language
      pure $ ConstructorInfo ctorArguments ctorIndices

  -- Now the full info is available for the inductive type
  let final = GlobalTypeInfo newParams newIndices (Map.fromList constructors)

  addProofGlobal name $ TypeGlobal final
  -- Add its auxiliary definitions to the booted globals as well
  -- (This requires the above line, to see the update immediately)
  addTypeAuxDefns name final

  pure final
  where
  multiCons plicit bounders tyT =
    foldr (\(i, b) -> (:) (plicit, b, E.shift i tyT))
      []
      (zip [0..] (NE.toList bounders))
  processBinders :: forall c. [CBinderGroup] -> Scoping c [(Plicit, Binder, Term)]
  processBinders rawBinders =
    join <$> for rawBinders \(plicit, binder, mty) -> do
      tyT <- lift case mty of
        Nothing -> M.initUVType <&> \(_, ty, _) -> ty
        Just ty -> elabType ty
      tyE <- lift $ eval tyT
      multiCons plicit <$> elabMultiBinder tyE binder <*> pure tyT
  peelToUniv :: Eval -> Scoped ([(Plicit, Binder, Term)], ULevel)
  peelToUniv = withForced \case
    EPi _ plicit binder indexTy inner -> do
      idx <- quote indexTy
      first ((plicit, binder, idx) :) <$>
        intoClosure indexTy inner peelToUniv
    EUniv _ univ -> pure ([], univ)
    ENeutralVar _ (Level l) _ -> do
      ctx <- M.askCtx
      let
        showBinder = \case
          BFresh -> "fresh"
          BUnused -> "_"
          BVar (Meta names) -> show $ chosenName names
          BMulti _ _ -> ":="
          BPair _ _ -> ","
      liftIO $ putStrLn $ maybe "none" showBinder $ fmap fst $ ctx @@? l
      error $ "Bad annotation for datatype " <> show (Level l) <> " "
    ENeutral x _ -> error $ "Bad annotation for datatype " <> ctorName x
    v -> error $ "Bad annotation for datatype " <> ctorName v
  peelToTyCtor :: forall c. Eval -> Scoping c ([(Plicit, Binder, Term)], ("params" @:: Vector.Vector Eval, "indices" @:: Vector.Vector Eval))
  peelToTyCtor = withForced \case
    EPi _ plicit binder indexTy inner -> do
      idx <- lift $ quote indexTy
      peeled <- intoClosure1 indexTy inner
      first ((plicit, binder, idx) :) <$> peelToTyCtor peeled
    ETyCtor _ tyName params indices -> do
      when (tyName /= name) do
        error $ "Constructor for wrong datatype: " <> show tyName <> " instead of " <> show name
      pure ([], (params, indices))
    ENeutralVar _ (Level l) _ -> do
      ctx <- M.askCtx
      let
        showBinder = \case
          BFresh -> "fresh"
          BUnused -> "_"
          BVar (Meta names) -> show $ chosenName names
          BMulti _ _ -> ":="
          BPair _ _ -> ","
      liftIO $ putStrLn $ maybe "none" showBinder $ fmap fst $ ctx @@? l
      error $ "Bad annotation for constructor " <> show (Level l) <> " "
    ENeutral (NGlobal _ _ n) _ -> error $ "Bad annotation for constructor " <> show n
    ENeutral x _ -> error $ "Bad annotation for constructor " <> ctorName x
    v -> error $ "Bad annotation for constructor " <> ctorName v
