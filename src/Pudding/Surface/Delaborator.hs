-- | This module is a kind of inverse for elaboration: turning core terms back
-- | into (hopefully readable) surface syntax. It uses stored binders, names,
-- | and other metadata to synthesize syntax like what the user wrote.
-- |
-- | The two steps are delaborating the core `Term` to a surface `CST` and
-- | rendering that `CST` to a prettyprinter.
-- |
-- | Delaborating binders has a bit of tricky monad business to bracket the
-- | work for each binder in a composable way.
{-# LANGUAGE ApplicativeDo #-}
module Pudding.Surface.Delaborator where

import Prelude

import Prettyprinter qualified as Doc
import Prettyprinter.Render.Text (renderStrict)
import qualified Prettyprinter.Render.Terminal as Ansi
import Control.DeepSeq (NFData)
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.Function ((&))
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)
import GHC.Generics (Generic, Generically(..))
import Pudding.Types.Name (CanonicalName (..), Name (..))
import Pudding.Types.Base (Plicit (Explicit, Implicit), type (@::), Fresh (Fresh))
import Pudding.Types.Metadata
import Pudding.Types.Stack
import Control.Monad.State.Strict (State, gets, modify', MonadState (state), runState)
import Pudding.Core.Types (Term (..), Binder(..), ScopedTerm (Scoped), Eval(..), Neutral(..), NeutFocus(..), NeutPrj(..), Ctx)
import Pudding.Surface.Parser (CST (..), CBinder, PartOfSpeech(..))
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Traversable (for)
import Control.Monad.Reader.Class (MonadReader (local, ask), asks)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Pudding.Core.Eval as E
import Pudding.Surface.Lexer (VariableDB(..), NameForm (..))
import Data.Maybe (fromMaybe)
import qualified Pudding.Core.Printer as P
import qualified Data.Text as T
import Data.Monoid (Ap(Ap, getAp))
import Data.Semigroup.Foldable (intercalateMap1)
import Control.Monad.RWS.Strict (RWS, censor, MonadWriter (listen, tell), evalRWS)
import Data.Set (Set)
import qualified Data.Set as S
import Control.Applicative ((<|>))
import Control.Applicative.Backwards (Backwards (forwards, Backwards))
import qualified Data.Vector as Vector


type Delab = RWS DelabR DelabW DelabS

data DelabR = DelabR
  { ctx :: Ctx (Maybe (Name, Level), "tm" @:: Eval, "ty" @:: Eval)
  , locals :: Map Name (Stack Neutral)
  }

data DelabW = DelabW
  { demand :: Set (Name, Level)
  }
  deriving (Eq, Ord, Show, Generic, NFData)
  deriving Monoid via Generically DelabW
  deriving Semigroup via Generically DelabW

data DelabS = DelabS
  { fresh :: Fresh
  }

-- | Use a state monad to adapt the reader context (forwards) and writer context
-- | (backwards) to bind and get demand information in a single traversal.
type DelabIO = Compose (State DelabR) (Backwards (State DelabW))

-- | This is how the adaptation works:
-- | - Run the first phase to intercept the reader context, via `ask` and `local`
-- | - Run the inner computation in that context
-- | - Intercept the writer output, via `listen` and `censor`
-- | - Run the second phase, `tell` the updated output, and return the results
adaptRW ::
  forall m r w x y z.
    MonadReader r m =>
    MonadWriter w m =>
  (x -> y -> z) ->
  Compose (State r) (Backwards (State w)) y ->
  m x -> m z
adaptRW f (Compose firstPhase) action = do
  ctx <- ask
  let (secondPhase, ctx') = runState firstPhase ctx
  (g, out) <- censor mempty $ listen $
    local (const ctx') $ f <$> action
  let (y, out') = runState (forwards secondPhase) out
  g y <$ tell out'
{-# SPECIALISE adaptRW :: (x -> y -> z) -> DelabIO y -> Delab x -> Delab z #-}


-- | This is a magic-looking method that binds a name and gets its demand
-- | "immediately" (hidden behind applicative phases).
withDemand :: Name -> Neutral -> DelabIO Bool
withDemand name neut = Compose do
  -- Get the level that this name will have, based on the size of the stack
  -- for this name
  lvl <- gets $ Level . maybe 0 size . M.lookup name . locals
  -- Add it to the local stack
  modify' \r -> r
    { locals = M.alter (Just . (:> neut) . fromMaybe Nil) name $ locals r }
  pure $ Backwards $ do
    -- In the next phase: look for whether that name and level occurred, and
    -- delete it from the demand set if so
    state \w ->
      (              S.member (name, lvl) $ demand w
      , w { demand = S.delete (name, lvl) $ demand w }
      )

-- ApplicativeDo
mintBinders :: Binder -> ("tm" @:: Neutral, "ty" @:: Eval) -> DelabIO (Maybe CBinder)
mintBinders (BVar (Meta (CanonicalName name _))) (tm, _) = do
  wasDemanded <- withDemand name tm
  pure if wasDemanded then
    Just (CVar (Just $ PlainName [] $ nameText name) PlainVar)
  else Nothing
mintBinders (BMulti l r) tmty = do
  ml' <- mintBinders l tmty
  mr' <- mintBinders r tmty
  pure case (ml', mr') of
    (Nothing, Nothing) -> Nothing
    (Just l', Nothing) -> Just l'
    (Nothing, Just r') -> Just r'
    (Just l', Just r') -> Just (CAssign l' r')
mintBinders (BPair l r) (Neutral hd spine, ty) = case ty of
  ESigma _ _ _ ty1 ty2 -> do
    let (tm1, tm2) = (Neutral hd (spine :> NFst mempty), Neutral hd (spine :> NSnd mempty))
    ml' <- mintBinders l (tm1, ty1)
    mr' <- mintBinders r (tm2, E.instantiateClosure ty2 $ ENeut tm1)
    pure case (ml', mr') of
      (Nothing, Nothing) -> Nothing
      (Just l', Nothing) -> Just l'
      (Nothing, Just r') -> Just r'
      (Just l', Just r') -> Just (CArray [l', r'])
  _ -> pure Nothing
mintBinders BFresh _ = pure Nothing
mintBinders BUnused _ = pure Nothing

-- | TODO: Zip constructors on both sides of a `BMulti`
simplifyBinder :: Binder -> Binder
simplifyBinder b = b

binderName :: Binder -> Maybe Name
binderName (BVar (Meta (CanonicalName name _))) = Just name
binderName (BMulti l r) = binderName l <|> binderName r
binderName _ = Nothing

mintBinder :: Binder -> ("ty" @:: Eval) -> DelabIO (Maybe CBinder)
mintBinder b ty = Compose do
  rawLvl <- gets $ Level . size . ctx
  nameLvl <- for (binderName b) \name ->
    gets $ (name,) . Level . maybe 0 size . M.lookup name . locals
  let arg = Neutral (NVar mempty rawLvl) Nil
  nextPhase <- getCompose $ mintBinders b (arg, ty)
  modify' \r -> r { ctx = ctx r :> (b, (nameLvl, ENeut arg, ty)) }
  pure nextPhase

withBinder :: Binder -> ("ty" @:: Eval) -> Delab x -> (Maybe CBinder -> x -> y) -> Delab y
withBinder b ty x f =
  adaptRW (flip f) (mintBinder (simplifyBinder b) ty) x

evalD :: Term -> Delab Eval
evalD t = do
  c <- asks ctx
  pure $ E.eval (c <&> \(_, e, _) -> e) t

runDelab :: Delab t -> t
runDelab act = fst $ evalRWS act
  (DelabR { ctx = Nil, locals = M.empty })
  (DelabS { fresh = Fresh 0 })


delab :: Term -> Delab CST
delab = \case
  TVar _m (Index idx) -> do
    vars <- asks ctx
    let (_bdr, (which, _tmE, _tyE)) = vars @@ idx
    case which of
      Just named@(name, Level lvl) -> do
        varSize <- asks $ maybe (error "missing var?") size . M.lookup name . locals
        tell $ DelabW { demand = S.singleton named }
        pure $ CVar (Just (PlainName [] (nameText name))) $
          if varSize == lvl+1 then PlainVar else DBLevel $ fromIntegral lvl
      Nothing ->
        pure $ CVar Nothing $ DBIndex $ fromIntegral idx
  TGlobal _m name -> pure $
    CVar (Just $ PlainName [] $ nameText name) PlainVar
  THole _m fresh -> pure $ CHole (Just $ T.pack $ show fresh)
  TUniv _m univ -> pure CUniv
  TLambda _m p binder ty (Scoped body) -> do
    tyE <- evalD ty
    ty' <- delab ty
    withBinder binder tyE (delab body) \b' body' ->
      coalesce $ CLambda (pure (p, pure $ fromMaybe CPlaceholder b', Just ty')) body'
  TPi _m p binder ty (Scoped body) -> do
    tyE <- evalD ty
    ty' <- delab ty
    withBinder binder tyE (delab body) \b' body' ->
      coalesce $ CPi (pure (p, pure $ fromMaybe CPlaceholder b', Just ty')) body'
  TSigma _m p binder ty (Scoped body) -> do
    tyE <- evalD ty
    ty' <- delab ty
    withBinder binder tyE (delab body) \b' body' ->
      coalesce $ CSigma (pure (p, pure $ fromMaybe CPlaceholder b', Just ty')) body'
  -- TODO validate Plicit
  TApp _m p fun arg -> case p of
    Explicit -> CApps <$> delab fun <*> (pure <$> delab arg)
    Implicit -> CSentence <$> do
      fun' <- delab fun
      arg' <- delab arg
      pure $ Subexpr fun' :| [SImplicits [(Nothing, arg')]]
  TPair _m _ty left right -> CPair <$> delab left <*> delab right
  TFst _m term -> CField <$> delab term <*> pure "0"
  TSnd _m term -> CField <$> delab term <*> pure "1"
  TTyCtor _m name params indices -> apps (CVar (Just $ PlainName [] $ nameText name) PlainVar) <$>
    traverse delab
      (Vector.toList params <> Vector.toList indices)
  TTmCtor _m (tyname, name) params args -> apps (CVar (Just $ PlainName [] $ nameText name) PlainVar) <$>
    traverse delab
      (Vector.toList params <> Vector.toList args)
  -- TCase _m motive cases scrutinee -> _
  -- TRecordTy _m fields -> _
  -- TRecordTm _m fields -> _
  TField _m focus field -> CField <$> delab focus <*> pure (nameText field)
  TLift _m ty -> CLift <$> delab ty
  TQuote _m tm -> CQuote <$> delab tm
  TSplice _m tm -> CSplice <$> delab tm
  tm -> do
    c <- asks (size . ctx)
    error $ "Unsupported delab: " <> T.unpack (P.format P.Plain (P.printCore tm (P.PS 0 c)))

apps :: CST -> [CST] -> CST
apps t [] = t
apps f (a : as) = CApps f (a :| as)

coalesce :: CST -> CST
coalesce (CLambda b1 (CLambda b2 t)) = coalesce (CLambda (b1 <> b2) t)
coalesce (CPi     b1 (CPi     b2 t)) = coalesce (CPi     (b1 <> b2) t)
coalesce (CSigma  b1 (CSigma  b2 t)) = coalesce (CSigma  (b1 <> b2) t)
coalesce t = t



type Print = Doc.Doc Ansi.AnsiStyle
type Printer = PrinterState -> Print

data PrinterState = PS
  { psRainbow :: Int
  , psDepth :: Int
  , psPrec :: Prec
  }

atTop :: PrinterState
atTop = PS 0 0 PrecMin

data Style = Ansi | Plain

rainbow :: Int -> Print -> Print
rainbow i = Doc.annotate $ Ansi.color $ colors !! (i `mod` 6)
  where colors = [Ansi.Red, Ansi.Green, Ansi.Yellow, Ansi.Blue, Ansi.Magenta, Ansi.Cyan]

format :: Style -> Print -> Text
format Plain = renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions
format Ansi = Ansi.renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions

pretty :: forall a m ann. Doc.Pretty a => Applicative m => a -> m (Doc.Doc ann)
pretty = pure . Doc.pretty

lit :: forall m ann. Applicative m => Text -> m (Doc.Doc ann)
lit = pretty @Text

spaced :: forall f. Foldable f => f Printer -> Printer
spaced = sepBy (pure Doc.softline)

sepBy :: forall f. Foldable f => Printer -> f Printer -> Printer
sepBy s ds0 = case toList ds0 of
  [] -> pure mempty
  (d : ds) -> getAp $ intercalateMap1 (Ap s) Ap (d :| ds)

commas :: forall f. Foldable f => f Printer -> Printer
commas = sepBy (pure Doc.comma)

juxt :: forall f. Foldable f => f Printer -> Printer
juxt = sepBy (pure mempty)

parens :: forall f. Foldable f => f Printer -> Printer
parens = wrap "(" ")"

braces :: forall f. Foldable f => f Printer -> Printer
braces = wrap "{" "}"

wrap :: (Semigroup Printer, Foldable f) => Text -> Text -> f Printer -> Printer
wrap s e inner = setPrec PrecMin $ juxt
  [ lit s, spaced inner, lit e ]

data Prec
  = PrecMin
  | PrecTrailing
  | PrecAscribe
  | PrecPair
  | PrecLift
  | PrecApp
  | PrecMax
  deriving (Eq, Ord, Enum, Generic, Show)

data Assoc = AssocL | AssocN | AssocR

assocOf :: Prec -> Assoc
assocOf = \case
  PrecMin -> AssocN
  PrecAscribe -> AssocR
  PrecLift -> AssocN
  PrecTrailing -> AssocN
  PrecApp -> AssocL
  PrecPair -> AssocN
  PrecMax -> AssocN


withPrec :: Prec -> ([Printer] -> Printer) -> [Printer] -> Printer
withPrec inner joiner contents s =
  if inner >= psPrec s
    then joiner (resetPrec inner contents) s
    else parens [setPrec inner (joiner contents)] s

setPrec :: Prec -> Printer -> Printer
setPrec prec item s = item (s { psPrec = prec })

bookends :: (Assoc -> x -> y) -> [x] -> [y]
bookends _ [] = []
bookends f [x] = [f AssocN x]
bookends f (x0 : xs0) = f AssocL x0 : go xs0 where
  go [] = []
  go [x] = [f AssocR x]
  go (x : xs) = f AssocN x : go xs

resetPrec :: Prec -> [Printer] -> [Printer]
resetPrec prec = bookends \position item s ->
  case (assocOf prec, position) of
    (AssocL, AssocL) -> item (s { psPrec = prec })
    (AssocR, AssocR) -> item (s { psPrec = prec })
    _ -> item (s { psPrec = succ prec })


dbgPrec :: (CST -> Printer) -> (CST -> Printer)
-- dbgPrec f = (\_ s -> Doc.pretty (show (psPrec s) <> "[")) <> (<> pure (lit "]")) f
dbgPrec f = f

printCST :: CST -> Printer
printCST = dbgPrec \case
  CApps f (a :| as) -> withPrec PrecApp spaced
    (printCST f : fmap printCST (a : as))
  CLambda binders body -> printBindingForm "λ" binders body
  CPi     binders body -> printBindingForm "Π" binders body
  CSigma  binders body -> printBindingForm "Σ" binders body
  -- CLet    defns body -> _
  CLet _ _ -> error "Unsupported CLet"

  CSentence parts -> parens $ parts <&> \case
    SOp op -> pretty op
    SImplicits args -> wrap "@{" "}" $ pure @[] $ commas $
      args <&> \case
        (Nothing, e) -> printCST e
        (Just (n, v), e) -> spaced [pretty n <> pretty v, lit ":=", printCST e]
    Subexpr e -> printCST e

  CVar  n v -> foldMap pretty n <> pretty v
  CMod mods -> mods & foldMap \mname ->
    lit mname <> lit "'"

  CUniv -> lit "Type"
  CNum n -> pretty n
  -- CStr ![Either Text CST]
  -- CHole !(Maybe Text)
  CStr _ -> error "Unsupported CStr"
  CHole _ -> error "Unsupported CHole"
  CPlaceholder -> lit "_"

  CPair l r -> withPrec PrecPair spaced [printCST l <> lit ",", printCST r]

  CRecordTy [] -> printCST (CAscribe (CRecordTm []) CUniv)
  CRecordTy tys -> braces $ tys <&> \(n, t) -> juxt [ pretty n, lit ":", printCST t ]
  CRecordTm tms -> braces $ tms <&> \(n, t) -> juxt [ pretty n, lit ":=", printCST t ]

  CLift l -> withPrec PrecLift spaced [lit "%", printCST l]
  CQuote e -> wrap "$q[" "]" [printCST e]
  CSplice e -> wrap "$s[" "]" [printCST e]

  -- CMatch ![CST] !("cases" @:: [("pats" @:: [CST], "body" @:: CST)])
  CMatch _ _ -> error "Unsupported CMatch"
  CField e n -> parens [printCST e <> lit "." <> pretty n]
  CAscribe e t -> withPrec PrecAscribe spaced [printCST e, lit ":", printCST t]
  CAssign x y -> parens [printCST x, lit ":=", printCST y]
  CArray xs -> wrap "[" "]" [commas $ printCST <$> xs]


printBindingForm :: Text -> NonEmpty (Plicit, NonEmpty CBinder, "ty" @:: Maybe CST) -> CST -> Printer
printBindingForm intro binders body st =
  let bound = printBinders binders st in
  withPrec PrecTrailing spaced [ pretty intro, pure bound <> lit ".", printCST body . const (st { psPrec = PrecMin }) ] st

printBinders :: NonEmpty (Plicit, NonEmpty CBinder, "ty" @:: Maybe CST) -> Printer
printBinders = intercalateMap1 (pure Doc.space) \(p, vars, ty) -> do
  (if p == Implicit then pure (lit "@") <> braces else parens)
    [ spaced $ printBinder <$> vars
    , lit ":"
    , setPrec PrecAscribe $ printCST $ fromMaybe CPlaceholder ty
    ]

printBinder :: CBinder -> Printer
printBinder = printCST

