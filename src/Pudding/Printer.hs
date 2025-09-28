module Pudding.Printer where

import Prettyprinter qualified as Doc

import Pudding.Types

sexp :: [i -> Doc.Doc ann] -> (i -> Doc.Doc ann)
sexp fs i = "(" <> Doc.indent 2 (spaced fs i) <> ")"

spaced :: [i -> Doc.Doc ann] -> (i -> Doc.Doc ann)
spaced [] = mempty
spaced [x] = x
spaced (x : y : zs) = x <> const Doc.softline <> spaced (y : zs)

bound :: Binder -> (QuoteCtx -> Doc.Doc ann) -> QuoteCtx -> Doc.Doc ann
bound _ f (QuoteCtx lvl) = f (QuoteCtx (lvl + 1))

printCore :: forall ann. Term -> QuoteCtx -> Doc.Doc ann
printCore = \case
  TVar _m idx -> pure $ Doc.pretty $ "x" <> show idx
  TGlobal _m (Name _ name) _ -> pure $ Doc.pretty name
  TLambda _m p binder ty body -> sexp
    [ pure $ "lambda" <> if p == Implicit then "?" else ""
    , sexp
      [ \ctx -> "x" <> Doc.pretty (quoteSize ctx)
      , printCore ty
      ]
    , bound binder $ printCore body
    ]
  TPi _m p binder ty body -> sexp
    [ pure $ "pi" <> if p == Implicit then "?" else ""
    , sexp
      [ \ctx -> "x" <> Doc.pretty (quoteSize ctx)
      , printCore ty
      ]
    , bound binder $ printCore body
    ]
  TApp _m fun arg -> sexp [ printCore fun, printCore arg ]

