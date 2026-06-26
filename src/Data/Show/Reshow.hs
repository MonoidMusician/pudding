module Data.Show.Reshow where

import Prelude hiding (lex, head, tail)
import Control.Applicative (many, (<|>), asum, optional)
import Data.Foldable (fold)
import Data.Functor ((<&>))
import Data.Text (Text)
import Pudding.Types ()
import Data.Foldable1 (intercalate1)
import Data.List.NonEmpty (NonEmpty((:|)))

import Prettyprinter qualified as Doc
import qualified Text.Parsec as P
import Prettyprinter.Render.Text (renderStrict)
import qualified Prettyprinter.Render.Terminal as Ansi
import qualified Data.List.NonEmpty as NE
import qualified Data.Text as T

type Print = Doc.Doc Ansi.AnsiStyle
type Printer = PrinterState -> Print

data PrinterState = PS
  { psRainbow :: Int
  }

data Style = Ansi | Plain

_rainbow :: Int -> Print -> Print
_rainbow i = Doc.annotate $ Ansi.color $ colors !! (i `mod` 6)
  where colors = [Ansi.Red, Ansi.Green, Ansi.Yellow, Ansi.Blue, Ansi.Magenta, Ansi.Cyan]

rainbow :: Printer -> Printer
rainbow f c = _rainbow (psRainbow c) (f c)

format :: Style -> Print -> Text
format Plain = renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions
format Ansi = Ansi.renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions


type Parser = P.Parsec Text ()

sourceOf :: Parser a -> Parser Text
sourceOf parser = do
  i1 <- P.getInput
  _r <- parser
  i2 <- P.getInput
  pure $ T.take (T.length i1 - T.length i2) i1

string :: Parser Text
string = sourceOf $ asum
  [ P.char '"' *> P.manyTill
      ((P.char '\\' *> P.anyChar) <|> P.anyChar)
      (P.char '"')
  , P.char '\'' *> P.manyTill
      ((P.char '\\' *> P.anyChar) <|> P.anyChar)
      (P.char '\'')
  ]

boring :: Parser Text
boring = sourceOf $ P.skipMany1 $
  P.notFollowedBy (P.oneOf "[](){}\"'," <|> P.space) *> P.anyChar

token :: String -> Parser String
token = P.string

parseShown :: Parser Printer
parseShown = asum
  [ matched "(" parseShown ")"
  , matched "[" parseShown "]"
  , matched "{" parseShown "}"
  , const . Doc.pretty <$> (string <|> boring)
  ] <* P.many P.space
  where
  matched :: String -> Parser Printer -> String -> Parser Printer
  matched o more c =
    fmap (Doc.align . Doc.group) <$> fold
      [ rainbow . const . Doc.pretty <$> token o
      , P.many P.space *> asum
          [ fold
            [ pure $ const Doc.space
            , layers more <&> \f (PS i) -> f (PS (i+1))
            , pure $ const Doc.line
            ]
          , pure mempty
          ]
      , rainbow . const . Doc.pretty <$> token c
      ]

layers :: Parser Printer -> Parser Printer
layers more =
  separated (const $ Doc.pretty ("," :: String)) (P.char ',' *> P.many P.space) $
    separated' (const Doc.line) (P.many1 P.space) $
      more

separated :: forall x. Printer -> Parser x -> Parser Printer -> Parser Printer
separated docSep parseSep item = many1SepEndBy parseSep item <&>
  \items -> intercalate1
    ((Doc.flatAlt <$> (const Doc.line <> docSep) <*> docSep) <> const Doc.space)
    $ fmap Doc.group <$> items

separated' :: forall x. Printer -> Parser x -> Parser Printer -> Parser Printer
separated' docSep parseSep item =
  manySurBy parseSep item <&>
    \case
      [] -> mempty
      [head] -> head
      (head : x : ys) ->
        head <> (Doc.nest 2 . (docSep <> intercalate1 docSep (x :| ys)))

manySurBy :: forall x a. Parser x -> Parser a -> Parser [a]
manySurBy s p = fmap NE.toList (many1SurBy (fmap Just s <|> pure Nothing) p) <|> ([] <$ s)

many1SurBy :: forall x a. Parser x -> Parser a -> Parser (NonEmpty a)
many1SurBy s p = s *> many1SepBy s p <* s

many1SepBy :: forall x a. Parser x -> Parser a -> Parser (NonEmpty a)
many1SepBy s p = liftA2 (:|) p (many (s *> p))

many1SepEndBy :: forall x a. Parser x -> Parser a -> Parser (NonEmpty a)
many1SepEndBy s p = do
  x0 <- p
  let
    go (x1 :| xs) =
      optional (s *> optional p) >>= \case
        Just (Just x) -> go (x :| x1 : xs)
        _ -> pure $ NE.reverse (x1 :| xs)
  go (x0 :| [])

parseAll :: Parser Printer
parseAll = layers parseShown <|> pure mempty

reformat :: Text -> Text
reformat i = case P.runP (parseAll <* P.eof) () "<shown>" i of
  Left _err -> i
  Right p -> format Ansi (p $ PS 0)

reshow :: forall s. Show s => s -> Text
reshow = reformat . T.pack . show

reshowS :: forall s. Show s => s -> String
reshowS = T.unpack . reformat . T.pack . show
