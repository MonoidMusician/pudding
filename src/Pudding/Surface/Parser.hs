module Pudding.Surface.Parser where

import Prelude hiding (lex)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text)
import qualified Text.Parsec as P
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Control.Monad.Identity (Identity)

import qualified Pudding.Surface.Lexer as L
import Pudding.Types.Base (type (@::), Plicit (..))
import Pudding.Surface.Lexer (VariableDB)
import Data.Traversable (for)

type Parser = P.ParsecT [L.Token] () Identity

_parseInner :: [L.Token] -> Parser t -> Parser t
_parseInner contents inner =
  P.getInput >>= \was ->
    P.setInput contents *> inner <* P.setInput was

parens :: Parser t -> Parser t
parens inner = do
  contents <- L.pParens
  _parseInner contents inner

braces :: Parser t -> Parser t
braces inner = do
  contents <- L.pBraces
  _parseInner contents inner

-- | A binder currently is just the same CST type since it shares overlap
-- | and parsing.
type CBinder = CST

-- | These are all bound with the *same* type: even if the expression contains
-- | variables that are mentioned in the binders, they are not reinterpreted
-- | each time. This is important, this is why `CBinderGroup` has a field of
-- | `NonEmpty CBinder` instead of just `CBinder` and letting it spill out
-- | into the larger multiple-binding structure.
type CBinderGroup = (Plicit, NonEmpty CBinder, "ty" @:: Maybe CST)

-- | A top-level declaration: data types, definitions, nested modules, etc.
data Decl
  -- A datatype declaration
  -- ```
  -- @data Vector (T : Type) : Π (len : Nat). Type
  -- | Nil : Vector zero
  -- | Cons (len : Nat) (hd : T) (tl : Vector len) : Vector (succ len)
  -- ```
  -- @data Vector (T : Type) : Π (len : Nat). Type | Nil : Vector zero | Cons (len : Nat) (hd : T) (tl : Vector len) : Vector (succ len)
  = DDataType L.VariableName
    -- Parameters
    ![CBinderGroup]
    -- Indices into Type:
    ![CBinderGroup] -- those that are written out?
    !(Maybe CST) -- must evaluate to a Pi type resulting in Type
    -- Constructors
    ![(L.VariableName, "arguments" @:: [CBinderGroup], "indices" @:: [CST])]
  | DDefine L.VariableName !(Maybe CST) !CST
  | DModule ![Text] ![Decl]
  deriving (Eq, Ord, Show, Generic, NFData)

data PartOfSpeech t
  = SOp L.OpForm
  | SImplicits ![(Maybe (Maybe L.NameForm, L.VariableDB), t)]
  | Subexpr t
  deriving (Eq, Ord, Show, Generic, NFData, Functor, Foldable, Traversable)

data CST
  = CApp !CST !CST
  | CLambda !(NonEmpty CBinderGroup) !CST
  | CPi     !(NonEmpty CBinderGroup) !CST
  | CSigma  !(NonEmpty CBinderGroup) !CST
  | CLet    ![(CBinder, "ty" @:: Maybe CST, "tm" @:: CST)]    !CST

  | CSentence !(NonEmpty (PartOfSpeech CST))

  | CVar  !(Maybe L.NameForm) !VariableDB
  | CMod  ![Text]

  | CUniv
  | CNum !Text
  | CStr ![Either Text CST]
  | CHole !(Maybe Text)

  | CRecordTy ![(L.NameForm, CST)]
  | CRecordTm ![(L.NameForm, CST)]

  | CLift !CST
  | CQuote !CST
  | CSplice !CST

  | CMatch ![CST] !("cases" @:: [("pats" @:: [CST], "body" @:: CST)])
  | CField  !CST !Text
  | CAscribe !CST !CST
  | CAssign !CST !CST -- for patterns and do notation
  | CPlaceholder
  | CArray ![CST]
  deriving (Eq, Ord, Show, Generic, NFData)

-- | Construct a sentence, handling easy cases that do not rely on precedence
-- | info (and thus name and import resolution).
cSentence :: NonEmpty (PartOfSpeech CST) -> CST
-- No operators, just function applications
cSentence sentence | Just appForm <- for sentence x =
  apps appForm
  where
  x = \case
    Subexpr e -> Just e
    _ -> Nothing
-- Single infix op
cSentence (Subexpr l :| [SOp (L.PlainOp qual op), Subexpr r]) =
  apps (CVar (Just $ L.OperatorName qual Nothing [op] Nothing) L.PlainVar :| [l, r])
-- Single prefix op
cSentence (SOp (L.PlainOp qual op) :| [Subexpr arg]) =
  apps (CVar (Just $ L.OperatorName qual (Just op) [] Nothing) L.PlainVar :| [arg])
-- Single postfix op
cSentence (Subexpr arg :| [SOp (L.PlainOp qual op)]) =
  apps (CVar (Just $ L.OperatorName qual Nothing [] (Just op)) L.PlainVar :| [arg])
-- Pair
cSentence (SOp (L.PlainOp [] "[") :| [Subexpr l, SOp (L.PlainOp [] ","), Subexpr r, SOp (L.PlainOp [] "]")]) =
  CArray [l, r]
-- Needs disambiguation still
cSentence sentence = CSentence sentence

apps :: NonEmpty CST -> CST
apps (f :| args) = foldl CApp f args

-- map {A B : % Type} : (% A -> % B) -> % List A -> % List B
-- map A B f as := $q[
--   foldr @{A, List B} (λ a bs. cons @{B} $s[f $q[a]] bs) (nil @{B})
-- ]
-- map {A B : % Type} : (% $s[A] -> % $s[B]) -> % List $s[A] -> % List $s[B]
-- map A B f as := $q[
--   foldr @{$s[A], List $s[B]} (λ a bs. cons @{$s[B]} $s[f $q[a]] bs) (nil @{$s[B]})
-- ]
-- exp : Nat -> % Nat -> % Nat
-- exp := λ x y. iter x (λ n. $q[ y * n ]) $q[ 1 ]
-- exp : Nat -> % Nat -> % Nat
-- exp := λ x y. iter x (λ n. $q[ $s[y] * $s[n] ]) $q[ 1 ]

-- map : (𝐴 𝐵 : ⇑U0) → (⇑ ∼𝐴 → ⇑ ∼𝐵) → ⇑(List0 ∼𝐴) → ⇑(List0 ∼𝐵)
-- map := 𝜆 𝐴 𝐵 𝑓 as. ⟨foldr0 ∼𝐴 (List0∼𝐵) (𝜆 𝑎 bs. cons0 ∼𝐵 ∼(𝑓 ⟨𝑎⟩) bs) (nil0 ∼𝐵) ∼𝑎𝑠⟩

-- exp : Nat1 → ⇑Nat0 → ⇑Nat0
-- exp := 𝜆 𝑥 𝑦. iter1 𝑥 (𝜆 𝑛. ⟨∼𝑦 ∗0 ∼𝑛⟩) ⟨1⟩
