module Pudding.Parser where

import Control.Applicative (many, (<|>))
import Control.Monad.Reader ( MonadReader(local), asks, Reader )
import qualified Text.Parsec as P
import qualified Data.List as L
import Data.Text (Text)
import Data.Functor (void)
import qualified Data.Text as T

import Pudding.Types

type Parser = P.ParsecT Text () (Reader Ctx)

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
  return $ Name (T.pack t)

term :: Parser Term
term = var <|> (lp *> (lambda <|> piType <|> app) <* rp)

newtype Ctx = Ctx { scope :: [Name] }

bindIdent :: Name -> Ctx -> Ctx
bindIdent i (Ctx is) = Ctx (i:is)

lookupIdent :: Name -> Parser (Maybe Index)
lookupIdent i = do
  idents <- asks scope
  return $ Index <$> L.elemIndex i idents

var :: Parser Term
var = do
  i <- ident
  mix <- lookupIdent i
  case mix of
    Just ix -> return (TVar ix)
    Nothing -> return (TGlobal i undefined)

keyword :: [String] -> Parser ()
keyword kw = void $ P.choice (map P.string' kw)

lambda :: Parser Term
lambda = keyword ["lambda", "λ"] *> abstraction TLambda

piType :: Parser Term
piType = keyword ["Pi", "Π"] *> abstraction TPi

type Abstraction = Plicit -> Binder -> Term -> Term -> Term

abstraction :: Abstraction -> Parser Term
abstraction mk = do
  (name, ty) <- lp *> ((,) <$> ident <*> term) <* rp
  body <- local (bindIdent name) term
  let binder = BVar (Meta (CanonicalName name mempty))
  return (mk Explicit binder ty body)

app :: Parser Term
app = do
  (x:xs) <- P.many1 term
  return $ foldl TApp x xs
