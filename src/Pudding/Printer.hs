module Pudding.Printer where

import Prettyprinter qualified as Doc

import Pudding.Types
import Prettyprinter.Render.Text (renderStrict)
import qualified Prettyprinter.Render.Terminal as Ansi
import Data.Text (Text)

type Print = Doc.Doc Ansi.AnsiStyle
type Printer = (Int, QuoteCtx) -> Print

data Style = Ansi | Plain

rainbow :: Int -> Print -> Print
rainbow i = Doc.annotate $ Ansi.color $ colors !! (i `mod` 6)
  where colors = [Ansi.Red, Ansi.Green, Ansi.Yellow, Ansi.Blue, Ansi.Magenta, Ansi.Cyan]

format :: Style -> Print -> Text
format Plain = renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions
format Ansi = Ansi.renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions

sexp :: [Printer] -> Printer
sexp fs (i, ctx) = Doc.hang 1 (clr "(" <> spaced fs i' <> clr ")")
  where
  i' = (i+1, ctx)
  clr = rainbow i

spaced :: [i -> Doc.Doc ann] -> (i -> Doc.Doc ann)
spaced [] = mempty
spaced [x] = x
spaced (x : y : zs) = x <> const Doc.softline <> spaced (y : zs)

bound :: Binder -> Printer -> Printer
bound _ f (i, QuoteCtx lvl) = f (i, QuoteCtx (lvl + 1))

formatCore :: Style -> Term -> Text
formatCore style term = format style $ printCore term (0, QuoteCtx 0)

printCore :: Term -> Printer
printCore = \case
  TVar _m idx -> \(_, ctx) -> "$" <>
    Doc.pretty (idx2lvl (quoteSize ctx) idx)
  TGlobal _m name _ -> pure $ Doc.pretty name
  THole _m fresh -> pure $ Doc.pretty fresh
  TUniv _m univ -> pure $ Doc.pretty $ case univ of
    UBase lvl -> "U0 " <> show lvl
    UMeta lvl -> "U1 " <> show lvl
    UVar fresh incr -> "U?" <> show fresh <> "+" <> show incr
  TLambda _m p binder ty body -> sexp
    [ pure $ "λ" <> if p == Implicit then "?" else ""
    , sexp
      [ \(_, ctx) -> "$" <> Doc.pretty (quoteSize ctx)
      , printCore ty
      ]
    , pure Doc.hardline
    , bound binder $ printCore body
    ]
  TPi _m p binder ty body -> sexp
    [ pure $ "Π" <> if p == Implicit then "?" else ""
    , sexp
      [ \(_, ctx) -> "$" <> Doc.pretty (quoteSize ctx)
      , printCore ty
      ]
    , pure Doc.hardline
    , bound binder $ printCore body
    ]
  app@(TApp _m _ _) ->
    let (fun, args) = spine app in
    sexp $ printCore <$> fun : args
  TSigma _m p binder ty body -> sexp
    [ pure $ "Σ" <> if p == Implicit then "?" else ""
    , sexp
      [ \(_, ctx) -> "$" <> Doc.pretty (quoteSize ctx)
      , printCore ty
      ]
    , pure Doc.hardline
    , bound binder $ printCore body
    ]
  TPair _m p left ltr right -> sexp
    [ pure $ "pair" <> if p == Implicit then "?" else ""
    , printCore left
    , printCore ltr
    , printCore right
    ]
  TFst _m term -> sexp [ pure "fst", printCore term ]
  TSnd _m term -> sexp [ pure "snd", printCore term ]

