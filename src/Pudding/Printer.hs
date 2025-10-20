module Pudding.Printer where

import Prettyprinter qualified as Doc

import Pudding.Types
import Prettyprinter.Render.Text (renderStrict)
import qualified Prettyprinter.Render.Terminal as Ansi
import Data.Text (Text)
import qualified Data.Vector as Vector
import Control.Monad (join)

type Print = Doc.Doc Ansi.AnsiStyle
type Printer = PrinterState -> Print

data PrinterState = PS
  { psRainbow :: Int
  , psDepth :: Int
  }

data Style = Ansi | Plain

rainbow :: Int -> Print -> Print
rainbow i = Doc.annotate $ Ansi.color $ colors !! (i `mod` 6)
  where colors = [Ansi.Red, Ansi.Green, Ansi.Yellow, Ansi.Blue, Ansi.Magenta, Ansi.Cyan]

format :: Style -> Print -> Text
format Plain = renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions
format Ansi = Ansi.renderStrict . Doc.layoutPretty Doc.defaultLayoutOptions

sexp :: [Printer] -> Printer
sexp fs (PS i ctx) = Doc.hang 1 (clr "(" <> spaced fs i' <> clr ")")
  where
  i' = PS (i + 1) ctx
  clr = rainbow i

spaced :: [i -> Doc.Doc ann] -> (i -> Doc.Doc ann)
spaced [] = mempty
spaced [x] = x
spaced (x : y : zs) = x <> const Doc.softline <> spaced (y : zs)

bound :: Binder -> (Term -> Printer) -> (ScopedTerm -> Printer)
bound _ f (Scoped term) (PS i depth) = f term (PS i (depth + 1))

formatCore :: Style -> Term -> Text
formatCore style term = format style $ printCore term (PS empty 0)

printCore :: Term -> Printer
printCore = \case
  TVar _m idx -> \(PS _ ctx) -> mconcat
    [ "_" <> Doc.pretty (level ctx idx)
    -- , "." <> Doc.pretty idx
    ]
  TGlobal _m name -> pure $ Doc.pretty name
  THole _m fresh -> pure $ Doc.pretty fresh
  TUniv _m univ -> pure $ Doc.pretty $ case univ of
    UBase lvl -> "(Type0 " <> show lvl <> ")" -- (Type0 0), (Type0 1), ...
    UMeta lvl -> "(Type1 " <> show lvl <> ")" -- (Type1 0), ...
    UVar fresh incr -> "(Type?" <> show fresh <> "+" <> show incr <> ")"
  TLambda _m p binder ty body -> sexp
    [ pure $ "λ" <> if p == Implicit then "?" else ""
    , sexp
      [ \(PS _ ctx) -> "_" <> Doc.pretty ctx
      , printCore ty
      ]
    , pure Doc.hardline
    , bound binder printCore body
    ]
  TPi _m p binder ty body -> sexp
    [ pure $ "Π" <> if p == Implicit then "?" else ""
    , sexp
      [ \(PS _ ctx) -> "_" <> Doc.pretty ctx
      , printCore ty
      ]
    , pure Doc.hardline
    , bound binder printCore body
    ]
  app@(TApp _m _ _) ->
    let (fun, args) = spine app in
    sexp $ printCore <$> fun : args
  TSigma _m p binder ty body -> sexp
    [ pure $ "Σ" <> if p == Implicit then "?" else ""
    , sexp
      [ \(PS _ ctx) -> "_" <> Doc.pretty ctx
      , printCore ty
      ]
    , pure Doc.hardline
    , bound binder printCore body
    ]
  TPair _m ty left right -> sexp
    [ pure "pair"
    , printCore ty
    , printCore left
    , printCore right
    ]
  TFst _m term -> sexp [ pure "fst", printCore term ]
  TSnd _m term -> sexp [ pure "snd", printCore term ]
  TTyCtor _m name params indices ->
    sexp $ join
      [ pure $ pure $ Doc.pretty name
      , printCore <$> Vector.toList params
      , printCore <$> Vector.toList indices
      ]
  TConstr _m (_, name) params args ->
    sexp $ join
      [ pure $ pure $ Doc.pretty name
      , printCore <$> Vector.toList params
      , printCore <$> Vector.toList args
      ]
  TLift _m ty -> sexp [ pure "Lift", printCore ty ]
  TQuote _m ty -> sexp [ pure "quote", printCore ty ]
  TSplice _m ty -> sexp [ pure "splice", printCore ty ]
