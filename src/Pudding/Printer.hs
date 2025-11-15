module Pudding.Printer where

import Prettyprinter qualified as Doc

import Pudding.Types
import Prettyprinter.Render.Text (renderStrict)
import qualified Prettyprinter.Render.Terminal as Ansi
import Data.Foldable (fold)
import Data.Functor ((<&>))
import Data.Text (Text)
import qualified Data.Vector as Vector
import Control.Monad (join)
import qualified Data.Map as Map
import Control.Lens (view)
import Text.Parsec.Pos (sourceLine, sourceColumn)
import Pudding.Parser (SourceSpan(SourceSpan))
import qualified Data.Set as Set
import Data.List (intercalate)

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
formatCore style term = format style $ printCore term (PS 0 empty)

formatCoreWithSpan :: Style -> Term -> Text
formatCoreWithSpan style term = format style $ withSpan printCore term (PS 0 empty)

withSpan :: (Term -> Printer) -> Term -> Printer
withSpan main term = fold
  [ pure $ "@{" <> Doc.pretty (intercalate "," spans) <> "} "
  , main term
  ]
  where
  Metadata { sourcePos } = view metadata term
  compactPos pos = show (sourceLine pos) <> ":" <> show (sourceColumn pos)
  spans = Set.toList sourcePos <&> \(SourceSpan lower upper) ->
    "(" <> compactPos lower <> "--" <> compactPos upper <> ")"

printCore :: Term -> Printer
printCore = \case
  TVar _m idx -> \(PS _ ctx) -> fold
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
  TCase _m motive cases inspect ->
    sexp
      [ pure "case"
      , printCore motive
      , sexp $ (\(name, fn) -> sexp [ pure $ Doc.pretty name, printCore fn ]) <$> Map.toList cases
      , printCore inspect
      ]
  TLift _m ty -> sexp [ pure "Lift", printCore ty ]
  TQuote _m ty -> sexp [ pure "quote", printCore ty ]
  TSplice _m ty -> sexp [ pure "splice", printCore ty ]
