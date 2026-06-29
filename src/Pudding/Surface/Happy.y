{
module Pudding.Surface.Happy where

import Prelude hiding (lex)

import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty)

import Pudding.Surface.Lexer
import Pudding.Surface.Parser
import Pudding.Types.Base (type (@::), Plicit (..))
import qualified Data.Text as T
import Data.Text (Text)
import Control.Monad (join)
import Data.Foldable (fold, traverse_)
import Data.Functor (void, (<&>))
import Data.Function ((&))
}

%expect 0

%tokentype { Token }
%monad { Either String }
%error { Left . show }

%name parseExpr expr
%name parseExprInParens exprInParens
%name parseBinderInner binderInner
%name parseImplicits implicits


%token
  'λ' { Token _ (Syntax SLambda) }
  'Π' { Token _ (Syntax SPi) }
  'Σ' { Token _ (Syntax SSigma) }

  ','   { Token _ (Syntax SComma) }
  '|'   { Token _ (Syntax SDisj) }
  '&'   { Token _ (Syntax SConj) }
  ':'   { Token _ (Syntax SAscribe) }
  ':='  { Token _ (Syntax SAssignL) }
  '=:'  { Token _ (Syntax SAssignR) }
  '??'  { Token _ (Syntax SInspect) }
  '?='  { Token _ (Syntax SMatchL) }
  '=?'  { Token _ (Syntax SMatchR) }
  '.'   { Token _ (Syntax SPeriod) }
  '_'   { Token _ (Syntax SPlaceholder) }

  '%'   { Token _ (Content (QualifiedOp (PlainOp [] "%"))) }

  'Type' { Token _ (Content Univ) }

  QNAME { Token _ (Content (QualifiedName _)) }
  VNAME { Token _ (Content (VariableName _ _)) }
  MNAME { Token _ (Content (ModuleName _)) }
  ONAME { Token _ (Content (QualifiedOp _)) }
  CNAME { Token _ (Content (Command _ _)) }
  NUM { Token _ (Content (Number _)) }

  PARENS { Token _ (Content (Parens _)) }
  BRACES { Token _ (Content (Braces _)) }
  IMPLICITS { Token _ (Content (Implicits _)) }

%%

QualifiedName :: { NameForm }
  : QNAME { case $1 of Token _ (Content (QualifiedName n)) -> n }
VariableName :: { (NameForm, VariableDB) }
  : VNAME { case $1 of Token _ (Content (VariableName n d)) -> (n, d) }
ModuleName :: { [Text] }
  : MNAME { case $1 of Token _ (Content (ModuleName m)) -> m }
QualifiedOp :: { OpForm }
  : ONAME { case $1 of Token _ (Content (QualifiedOp o)) -> o }
Command :: { ([Text], Text) }
  : CNAME { case $1 of Token _ (Content (Command m n)) -> (m, n) }
Number :: { Text }
  : NUM { case $1 of Token _ (Content (Number n)) -> n }
Parens :: { [Token] }
  : PARENS { case $1 of Token _ (Content (Parens ts)) -> ts }
Braces :: { [Token] }
  : BRACES { case $1 of Token _ (Content (Braces ts)) -> ts }
Implicits :: { [Token] }
  : IMPLICITS { case $1 of Token _ (Content (Implicits ts)) -> ts }


-- Main expression precedence ladder
expr :: { CST }
  : exprAscribe { $1 }

-- Type ascriptions are lowest precedence / bind weakest
exprAscribe :: { CST }
  -- %shift here disambiguates `\(X : Type). X : Type`
  : exprSentence %shift { $1 }
  | exprSentence ':' exprAscribe { CAscribe $1 $3 }

-- A sentence is a sequence of operators and function applications
exprSentence :: { CST }
  : exprTrailing { $1 }
  | '%' exprTrailing { CLift $2 }
  -- Handle things with operators (including function application)
  -- as a flat list of operators \/ expressions, which gets parsed into
  -- a tree after resolving namespaces. Being a list automatically takes care
  -- of parenthesization.
  | someAux(wordAtom) word(exprTrailing) { cSentence (NE.reverse (NE.cons $2 $1)) }

  wordAtom :: { PartOfSpeech CST }
    : word(exprAtom) { $1 }

  word(inner) :: { PartOfSpeech CST }
    : QualifiedOp { SOp $1 }
    | Implicits {% fmap SImplicits (parseImplicits $1) }
    | inner { Subexpr $1 }

  implicits :: { [(Maybe (NameForm, VariableDB), CST)] }
    : commas(implicit) { $1 }

  implicit :: { (Maybe (NameForm, VariableDB), CST) }
    : VariableName ':=' expr { (Just $1, $3) }
    | expr { (Nothing, $1) }

-- Operators open on the right with trailing precedence
exprTrailing :: { CST }
  : exprAtom { $1 }
  | 'λ' binders '.' expr { CLambda $2 $4 }
  | 'Π' binders '.' expr { CPi $2 $4 }
  | 'Σ' binders '.' expr { CSigma $2 $4 }

-- Atomic expressions with well-defined start and end
exprAtom :: { CST }
  : Parens {% parseExprInParens $1 }
  | var { $1 }
  | num { $1 }
  | 'Type' { CUniv }
  | QualifiedName { CName $1 }
  | ModuleName { CMod $1 }

-- Parse an expression inside parens
exprInParens :: { CST }
  : expr { $1 }
  -- for patterns
  | expr ':=' expr { CAssign $1 $3 }


var :: { CST }
  : VariableName { CVar (fst $1) (snd $1) }

num :: { CST }
  : Number { CNum $1 }

-- A list of binders
binders :: { NonEmpty (Plicit, NonEmpty CBinder, "ty" @:: Maybe CST) }
  : some(binder) { $1 }

binder :: { (Plicit, NonEmpty CBinder, "ty" @:: Maybe CST) }
  : var { (Explicit, pure $1, Nothing) }
  | Parens {% parseBinderInner $1 <&> \(vs, t) -> (Explicit, vs, t) }
  | Braces {% parseBinderInner $1 <&> \(vs, t) -> (Implicit, vs, t) }

binderInner :: { (NonEmpty CBinder, Maybe CST) }
  : some(var) { ($1, Nothing) }
  | some(var) ':' expr { ($1, Just $3) }




------


many(a) :: { [a] }
  : {- empty -} { [] }
  | many(a) { NE.toList $1 }

some(a) :: { NE.NonEmpty a }
  : someAux(a) %shift { NE.reverse $1 }

someAux(a) :: { NE.NonEmpty a }
  : a { pure $1 }
  | someAux(a) a { NE.cons $2 $1 }

manySep(a, sep) :: { [a] }
  : {- empty -} { [] }
  | someSep(a, sep) { NE.toList $1 }

someSep(a, sep) :: { NE.NonEmpty a }
  : someSepAux(a, sep) { NE.reverse $1 }

someSepAux(a, sep) :: { NE.NonEmpty a }
  : a { pure $1 }
  | someSepAux(a, sep) sep a { NE.cons $3 $1 }

commas(a) :: { [a] }
  : commas1(a) ',' { NE.toList $1 }
  | commas1(a)     { NE.toList $1 }
  | {- empty -} { [] }
  | ',' { [] }

commas1(a) :: { NE.NonEmpty a }
  : a %shift { pure $1 }
  | a ',' commas1(a) { NE.cons $1 $3 }

-- sep(a, s) :: { Separated a }
--   : sep1(a, s) { separated $1 }

-- sep1(a, s) :: { [(SourceToken, a)] }
--   : a %shift { [(placeholder, $1)] }
--   | sep1(a, s) s a { ($2, $3) : $1 }

-- delim(a, b, c, d) :: { Delimited b }
--   : a d { Wrapped $1 Nothing $2 }
--   | a sep(b, c) d { Wrapped $1 (Just $2) $3 }
