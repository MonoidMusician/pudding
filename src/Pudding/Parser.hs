module Pudding.Parser where

import Control.Applicative (many, (<|>))
import Control.Monad.Reader ( MonadReader(local), asks, ReaderT (runReaderT) )
import qualified Text.Parsec as P
import qualified Data.List as L
import Data.Text (Text)
import Data.Functor (void, (<&>))
import qualified Data.Text as T

import Pudding.Types
import Pudding.Name (NameTable)
import Data.IORef (IORef)

type Parser = P.ParsecT Text () (ReaderT Ctx IO)

pragma :: Text -> Parser ()
pragma name = void $ P.string' $ "%" <> T.unpack name

lp :: Parser ()
lp = P.char '(' *> P.spaces

rp :: Parser ()
rp = P.char ')' *> P.spaces

ident :: Parser Name
ident = do
  t <- (:) <$> P.letter <*> many P.alphaNum
  P.spaces
  tbl <- asks table
  internalize tbl $ T.pack t

term :: Parser Term
term = var <|> (lp *> (lambda <|> piType <|> app) <* rp)

data Ctx = Ctx { scope :: [Name], table :: IORef NameTable }

bindIdent :: Name -> Ctx -> Ctx
bindIdent i (Ctx is tbl) = Ctx (i:is) tbl

lookupIdent :: Name -> Parser (Maybe Index)
lookupIdent i = do
  idents <- asks scope
  return $ Index <$> L.elemIndex i idents

var :: Parser Term
var = do
  i <- ident
  mix <- lookupIdent i
  case mix of
    Just ix -> return (TVar mempty ix)
    Nothing -> return (TGlobal mempty i undefined)

keyword :: [String] -> Parser ()
keyword kw = void $ P.choice (map P.string' kw) *> P.spaces

kwPlicit :: [String] -> Parser Plicit
kwPlicit kw = Implicit <$ keyword (kw <&> (<> "?")) <|> Explicit <$ keyword kw

lambda :: Parser Term
lambda = kwPlicit ["lambda", "λ"] >>= abstraction TLambda

piType :: Parser Term
piType = kwPlicit ["Pi", "Π"] >>= abstraction TPi

type Abstraction = Metadata -> Plicit -> Binder -> Term -> Term -> Term

abstraction :: Abstraction -> Plicit -> Parser Term
abstraction mk plicit = do
  (name, ty) <- lp *> ((,) <$> ident <*> term) <* rp
  body <- local (bindIdent name) term
  let binder = BVar (Meta (CanonicalName name mempty))
  return (mk mempty plicit binder ty body)

app :: Parser Term
app = do
  (x:xs) <- P.many1 term
  return $ foldl (TApp mempty) x xs

runParser :: Parser a -> P.SourceName -> Text -> IO (Either P.ParseError a)
runParser p s t = do
  tbl <- initTable
  runReaderT (P.runParserT p () s t) (Ctx [] tbl)
