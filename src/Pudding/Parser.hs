module Pudding.Parser where

import Control.Applicative (many, (<|>))
import Control.Monad.Error.Class
import Control.Monad.Reader
import qualified Text.Parsec as P
import qualified Text.Parsec.Text as PT
import qualified Data.List as L
import Data.Text (Text)
import Data.Functor (void)
import qualified Data.Text as T

import Pudding.Types

type Parser = PT.Parser

pragma :: Text -> Parser ()
pragma name = void $ P.string' $ "%" <> T.unpack name

data SExpr = Ident Text | List [SExpr]

lp :: Parser ()
lp = P.char '(' *> P.spaces

rp :: Parser ()
rp = P.char ')' *> P.spaces

ident :: Parser Text
ident = do
  t <- (:) <$> P.letter <*> many P.alphaNum
  P.spaces
  return (T.pack t)

list :: Parser [SExpr]
list = lp *> many sexpr <* rp

sexpr :: Parser SExpr
sexpr = Ident <$> ident <|> List <$> list

newtype Ctx = Ctx { scope :: [Text] }

bindIdent :: Text -> Ctx -> Ctx
bindIdent i (Ctx is) = Ctx (i:is)

-- TODO: Track source locations for errors
type SExprParser a = ReaderT Ctx (Either String) a

lookupIdent :: Text -> SExprParser (Maybe Index)
lookupIdent i = do
  idents <- asks scope
  return $ Index <$> L.elemIndex i idents

parseTerm :: SExpr -> SExprParser Term
parseTerm e = case e of
  Ident i -> do
    mix <- lookupIdent i
    case mix of
      Just ix -> return (TVar ix)
      Nothing -> return (TGlobal (Name i) undefined)
  List (x:xs) -> case x of
    _ | isLambda x -> do
          (binder, ty, body) <- parseBinder xs
          return (TLambda Explicit binder ty body)
    _ | isPi x -> do
          (binder, ty, body) <- parseBinder xs
          return (TPi Explicit binder ty body)
    _ -> foldl TApp <$> parseTerm x <*> mapM parseTerm xs
  List [] -> throwError "Empty list"

isKeyword :: [String] -> SExpr -> Bool
isKeyword kw (Ident i) = let i' = T.unpack i in elem i' kw
isKeyword _ _ = False

isLambda :: SExpr -> Bool
isLambda = isKeyword ["lambda", "λ"]

isPi :: SExpr -> Bool
isPi = isKeyword ["Pi", "Π"]

parseBinder :: [SExpr] -> SExprParser (Binder, Term, Term)
parseBinder xs = case xs of
  [List [Ident name, ty], body] -> do
    ty' <- parseTerm ty
    body' <- local (bindIdent name) $ parseTerm body
    let binder = BVar (Meta (CanonicalName (Name name) mempty))
    return (binder, ty', body')
  -- TODO: Better error message
  _ -> throwError "Invalid expression"

term :: Parser Term
term = do
  e <- sexpr
  case runReaderT (parseTerm e) (Ctx []) of
    Left err -> fail err
    Right t -> return t
