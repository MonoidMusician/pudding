module Pudding.Parser where

import Control.Applicative (many, (<|>))
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Reader ( MonadReader(local), asks, ReaderT (runReaderT) )
import qualified Text.Parsec as P
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.List as L
import Data.Set (singleton)
import Data.Text (Text)
import Data.Functor (void, ($>))
import qualified Data.Text as T

import Pudding.Types
import Pudding.Name (NameTable)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (when)
import GHC.IO (unsafePerformIO)

type Parser = P.ParsecT Text () (ReaderT Ctx IO)

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

ident :: Parser Name
ident = do
  t <- word $ (:) <$> P.letter <*> many P.alphaNum
  tbl <- asks table
  internalize tbl $ T.pack t

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
        p <- kwPlicit ["pair"]
        P.spaces
        l <- term
        dep <- term
        r <- term
        return $ \meta -> TPair meta p l dep r
    , trackMeta $ do keyword ["U0"] $> \meta -> TUniv meta (UBase 0)
    , trackMeta $ do keyword ["U1"] $> \meta -> TUniv meta (UMeta 0)
    ]

data Ctx = Ctx
  { scope :: [Name]
  , table :: IORef NameTable
  , lastEnd :: IORef P.SourcePos
  }

bindIdent :: Name -> Ctx -> Ctx
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

type Abstraction = Metadata -> Plicit -> Binder -> Term -> Term -> Term

binder :: Parser (Name, Term)
binder = lp *> ((,) <$> ident <*> term) <* rp

abstraction :: Parser Plicit -> Abstraction -> Parser Term
abstraction kw mk = do
  Tracked s finish <- track do
    plicit <- kw
    (name, ty) <- binder
    body <- local (bindIdent name) term
    let b = BVar (Meta (CanonicalName name (singleton name)))
    return $ \meta -> mk meta plicit b ty body
  return (finish (Metadata (singleton s)))

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

declaration :: Parser (Name, GlobalInfo)
declaration = parens $ P.choice
  [ do
      keyword ["define"]
      n <- ident
      t <- term
      pure (n, GlobalDefn undefined (GlobalTerm t undefined))
  ]
declarations :: Parser (Map Name GlobalInfo)
declarations = P.many declaration >>= \decls -> do
  let globals = Map.fromList decls
  when (Map.size globals /= length decls) do
    fail "Duplicate global names"
  pure globals

runParser :: Parser a -> P.SourceName -> Text -> IO (Either P.ParseError a)
runParser p s t = do
  end <- newIORef undefined
  runReaderT (P.runParserT p () s t) (Ctx { scope = [], table = globalTable, lastEnd = end })

{-# NOINLINE globalTable #-}
globalTable :: IORef NameTable
globalTable = unsafePerformIO initTable
