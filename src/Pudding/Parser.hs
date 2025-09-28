module Pudding.Parser where

import Control.Applicative (many, (<|>))
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Reader ( MonadReader(local), asks, ReaderT (runReaderT) )
import qualified Text.Parsec as P
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.List as L
import Data.Set (singleton)
import Data.Text (Text)
import Data.Functor (void, (<&>))
import qualified Data.Text as T

import Pudding.Types
import Pudding.Name (NameTable)

type Parser = P.ParsecT Text () (ReaderT Ctx IO)

data Tracked a = Tracked SourceSpan a
  deriving (Functor, Foldable, Traversable)

track :: Parser a -> Parser (Tracked a)
track p = do
  begin <- P.getPosition
  result <- p
  end <- asks lastEnd >>= liftIO . readIORef
  return $ Tracked (SourceSpan begin end) result

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

ident :: Parser Name
ident = do
  t <- (:) <$> P.letter <*> many P.alphaNum
  P.spaces
  tbl <- asks table
  internalize tbl $ T.pack t

term :: Parser Term
term = var <|> (lp *> (lambda <|> piType <|> app) <* rp)

data Ctx = Ctx
  { scope :: [Name]
  , table :: IORef NameTable
  , lastEnd :: IORef P.SourcePos
  }

bindIdent :: Name -> Ctx -> Ctx
bindIdent i (Ctx is tbl e) = Ctx (i:is) tbl e

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
    Nothing -> TGlobal meta i undefined

keyword :: [String] -> Parser ()
keyword kw = void $ P.choice (map P.string' kw) *> P.spaces

kwPlicit :: [String] -> Parser Plicit
kwPlicit kw = Implicit <$ keyword (kw <&> (<> "?")) <|> Explicit <$ keyword kw

lambda :: Parser Term
lambda = abstraction (kwPlicit ["lambda", "λ"]) TLambda

piType :: Parser Term
piType = abstraction (kwPlicit ["Pi", "Π"]) TPi

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

runParser :: Parser a -> P.SourceName -> Text -> IO (Either P.ParseError a)
runParser p s t = do
  tbl <- initTable
  end <- newIORef undefined
  runReaderT (P.runParserT p () s t) (Ctx [] tbl end)
