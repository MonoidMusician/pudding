module Pudding.Parser where

import Control.Applicative (many, (<|>))
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Reader ( MonadReader(local), asks, ReaderT (runReaderT) )
import qualified Text.Parsec as P
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.List as L
import Data.Set (singleton)
import Data.Text (Text)
import Data.Functor (void)
import qualified Data.Text as T

import Pudding.Types
import Pudding.Name (NameTable)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (when)
import GHC.IO (unsafePerformIO)
import Data.Traversable (for)
import qualified Data.Vector as Vector

type Parser = P.ParsecT Text () (ReaderT ParseCtx IO)

data Tracked a = Tracked SourceSpan a
  deriving (Functor, Foldable, Traversable)

track :: Parser a -> Parser (Tracked a)
track p = do
  begin <- P.getPosition
  result <- p
  end <- asks lastEnd >>= liftIO . readIORef
  return $ Tracked (SourceSpan begin end) result

trackMeta :: Parser (Metadata -> a) -> Parser a
trackMeta p = do
  Tracked sourceSpan fn <- track p
  return $ fn $ Metadata $ singleton sourceSpan

markEnd :: Parser ()
markEnd = do
  r <- asks lastEnd
  p <- P.getPosition
  liftIO $ writeIORef r p

spaces :: Parser ()
spaces = markEnd *> P.spaces

pragma :: Text -> Parser ()
pragma name = void $ P.string' $ "%" <> T.unpack name

lp :: Parser ()
lp = P.char '(' *> spaces

rp :: Parser ()
rp = P.char ')' *> spaces

word :: Parser a -> Parser a
word p = P.try (p <* P.notFollowedBy P.alphaNum) <* spaces

parens :: forall a. Parser a -> Parser a
parens p = lp *> p <* rp

manyParens :: Parser a -> Parser [a]
manyParens = many . parens
parensMany :: Parser a -> Parser [a]
parensMany = parens . many

ident :: Parser Name
ident = do
  t <- word $ (:) <$> P.letter <*> many P.alphaNum
  tbl <- asks table
  internalize tbl $ T.pack t

int :: Parser Int
int = read <$> P.many1 P.digit <* spaces

term :: Parser Term
term = var <|> (lp *> (P.choice terms <|> app) <* rp)
  where
  terms =
    [ abstraction (kwPlicit ["lambda", "λ"]) TLambda
    , abstraction (kwPlicit ["Pi", "Π"]) TPi
    , abstraction (kwPlicit ["Sigma", "Σ"]) TSigma
    , trackMeta do
        which <- TFst <$ P.string' "fst" <|> TSnd <$ P.string' "snd"
        P.spaces
        t <- term
        return $ \meta -> which meta t
    , trackMeta do
        _ <- keyword ["pair"]
        P.spaces
        l <- term
        dep <- term
        r <- term
        return $ \meta -> TPair meta l dep r
    , trackMeta do
        univKind <- UBase <$ keyword ["Type0"] <|> UMeta <$ keyword ["Type1"]
        lvl <- P.option 0 int
        pure \meta -> TUniv meta (univKind lvl)
    ]

data ParseCtx = ParseCtx
  { scope :: [Name]
  , table :: IORef NameTable
  , lastEnd :: IORef P.SourcePos
  }

bindIdent :: Name -> ParseCtx -> ParseCtx
bindIdent i ctx = ctx { scope = i : scope ctx }

lookupIdent :: Name -> Parser (Maybe Index)
lookupIdent i = do
  idents <- asks scope
  return $ Index <$> L.elemIndex i idents

var :: Parser Term
var = do
  Tracked s i <- track ident
  let meta = Metadata (singleton s)
  mix <- lookupIdent i
  return $ case mix of
    Just ix -> TVar meta ix
    Nothing -> TGlobal meta i

keyword :: [String] -> Parser ()
keyword kw = void $ P.choice (map (word . P.string) kw)

kwPlicit :: [String] -> Parser Plicit
kwPlicit kw = keyword kw *> plicity

plicity :: Parser Plicit
plicity = P.option Explicit (Implicit <$ P.char '?') <* P.spaces

type Abstraction = Metadata -> Plicit -> Binder -> Term -> ScopedTerm -> Term

binder :: Parser (Name, Term)
binder = lp *> ((,) <$> ident <*> term) <* rp

abstraction :: Parser Plicit -> Abstraction -> Parser Term
abstraction kw mk = do
  Tracked s finish <- track do
    plicit <- kw
    (name, ty) <- binder
    body <- local (bindIdent name) term
    let b = bName name
    return $ \meta -> mk meta plicit b ty (Scoped body)
  return (finish (Metadata (singleton s)))

bName :: Name -> Binder
bName name = BVar (Meta (CanonicalName name (singleton name)))

app :: Parser Term
app = do
  (x:xs) <- P.many1 (track term)
  let Tracked _ a = foldl trackApp x xs
  return a
  where
    trackApp :: Tracked Term -> Tracked Term -> Tracked Term
    trackApp (Tracked s1 a) (Tracked s2 b) =
      let s = s1 <> s2 in
        Tracked s (TApp (Metadata (singleton s)) a b)

-- List is in stack order, not binding order
type Binding = (Plicit, Binder, Term)
binderList :: forall r. ([Binding] -> Parser r) -> Parser r
binderList cont = parens $ go []
  where
  go acc = P.optionMaybe oneBinder >>= \case
    Nothing -> cont acc
    Just (pbty, lcl) -> lcl do go (pbty : acc)
  oneBinder = do
    p <- P.option Explicit (Implicit <$ P.char '?' <* spaces)
    (name, ty) <- binder
    let b = bName name
    pure ((p, b, ty), local (bindIdent name))

assembleInductive :: Name -> [Binding] -> [Binding] -> [(Name, ([Binding], [Term]))] -> Parser GlobalTypeInfo
assembleInductive typeName parameters indices constrs = do
  constructors <- checkMap "constructors" constrs >>= Map.traverseWithKey \conName (args, chosen) -> do
    when (L.length chosen /= L.length indices) do
      fail $ mconcat
        [ "Gave "
        , show $ L.length chosen
        , " indices in constructor "
        , show conName
        , " but needed "
        , show $ L.length indices
        ]
    pure $ ConstructorInfo
      { ctorArguments = Vector.reverse $ Vector.fromList args
      , ctorIndices = Vector.fromList $ chop chosen
      }
  pure $ GlobalTypeInfo
    { typeParams = Vector.reverse $ Vector.fromList parameters
    , typeIndices = Vector.reverse $ Vector.fromList indices
    , typeConstrs = constructors
    }
  where
  chop :: [Term] -> [Term]
  chop (TGlobal _ name : chosen) | name == typeName = chosen
  chop chosen = chosen

checkMap :: forall t. String -> [(Name, t)] -> Parser (Map Name t)
checkMap desc items = do
  let gathered = Map.fromList items
  when (Map.size gathered /= length items) do
    fail $ "Duplicate " <> desc
  pure gathered

declaration :: Parser (Name, GlobalInfo)
declaration = parens $ P.choice
  [ do
      keyword ["define"]
      n <- ident
      t <- term
      pure (n, GlobalDefn (arityOfTerm t) undefined (GlobalTerm t undefined))
  , do
      keyword ["inductive"]
      typeName <- ident
      -- Parameters do not vary between constructors: this lets the universe
      -- level be lower, and also saves on typing-as-in-keystrokes haha
      binderList \parameters -> do
        -- Indices can vary between constructors
        indices <- binderList pure
        constructors <- many $ parens do
          conName <- ident
          -- So each constructor binds data arguments
          fmap (conName,) $ P.option ([], []) $ binderList \args ->
            -- And says what each index should be
            fmap (args,) $ P.option [] $ parensMany term
        info <- assembleInductive typeName parameters indices constructors
        pure (typeName, GlobalType info)
  ]
declarations :: Parser Globals
declarations = P.many declaration >>= \decls -> do
  let globals = Map.fromList decls
  when (Map.size globals /= length decls) do
    fail "Duplicate global names"
  pure globals

runParser :: Parser a -> P.SourceName -> Text -> IO (Either P.ParseError a)
runParser p s t = runParserScope p [] s t

runParserScope :: Parser a -> [Text] -> P.SourceName -> Text -> IO (Either P.ParseError a)
runParserScope p names s t = do
  end <- newIORef undefined
  scope <- for names $ internalize globalTable
  runReaderT (P.runParserT p () s t) (ParseCtx { scope, table = globalTable, lastEnd = end })

{-# NOINLINE globalTable #-}
globalTable :: IORef NameTable
globalTable = unsafePerformIO initTable
