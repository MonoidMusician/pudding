module Pudding.Surface.Parser where

import Prelude hiding (lex)
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import qualified Text.Parsec as P
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Control.Monad.Identity (Identity)

import qualified Pudding.Surface.Lexer as L
import Pudding.Types.Base (type (@::), Plicit (..))
import Pudding.Surface.Lexer (VariableDB)

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


type CBinder = CST

data Decl
  = DDataType
    ![(Plicit, CBinder, CST)]
    ![(Plicit, CBinder, CST)]
    ![(Text, [(Plicit, CBinder, CST)], [CST])]
  | DDefine !Text !(Maybe CST) !CST
  deriving (Eq, Ord, Show, Generic, NFData)

data CST
  = CApp !CST !CST
  | CLambda !(NonEmpty (Plicit, CBinder, "ty" @:: Maybe CST)) !CST
  | CPi     !(NonEmpty (Plicit, CBinder, "ty" @:: Maybe CST)) !CST
  | CSigma  !(NonEmpty (Plicit, CBinder, "ty" @:: Maybe CST)) !CST
  | CLet    ![(CBinder, "ty" @:: Maybe CST, "tm" @:: CST)]    !CST

  | CSentence !(NonEmpty (Either L.OpForm CST))

  | CVar  !L.NameForm !VariableDB
  | CName !L.NameForm
  | CMod  ![Text]

  | CNum !Text
  | CStr ![Either Text CST]
  | CHole !(Maybe Text)

  | CLift !CST
  | CQuote !CST
  | CSplice !CST

  | CMatch ![CST] !("cases" @:: [("pats" @:: [CST], "body" @:: CST)])
  | CField  !CST !Text
  | CAscribe !CST !CST
  | CAssign !CST !CST -- for patterns and do notation
  deriving (Eq, Ord, Show, Generic, NFData)

-- Lift: Text
-- quote:
-- splice:

-- map {A B : ~~ Type} : (~~ A.~ -> ~~ B.~) -> ~~ List A.~ -> ~~ List B.~
-- map A B f as := ~[
--   foldr @{A.~, List B.~} (λ a bs. cons @{B.~} (f ~[a]).~ bs) (nil @{B.~})
-- ]

-- map {A B : %% Type} : (%% A.% -> %% B.%) -> %% List A.% -> %% List B.%
-- map A B f as := %[
--   foldr @{A.%, List B.%} (λ a bs. cons @{B.%} (f %[a]).% bs) (nil @{B.%})
-- ]

-- map {A B : $$ Type} : ($$ A.$ -> $$ B.$) -> $$ List A.$ -> $$ List B.$
-- map A B f as := $[
--   foldr @{A.$, List B.$} (λ a bs. cons @{B.$} (f $[a]).$ bs) (nil @{B.$})
-- ]

-- map {A B : $$ Type} : ($$ A.$ -> $$ B.$) -> $$ List A.$ -> $$ List B.$
-- map A B f as := $[
--   foldr @{A.$, List B.$} (λ a bs. cons @{B.$} (f $[a]).$ bs) (nil @{B.$})
-- ]

-- map {A B : $$ Type} : ($$ &A -> $$ &B) -> $$ List &A -> $$ List &B
-- map A B f as := $[
--   foldr @{&A, List &B} (λ a bs. cons @{&B} &(f $[a]) bs) (nil @{&B})
-- ]

-- map {A B : $$ Type} : ($$ !A -> $$ !B) -> $$ List !A -> $$ List !B
-- map A B f as := $[
--   foldr @{!A, List !B} (λ a bs. cons @{!B} !(f $[a]) bs) (nil @{!B})
-- ]

-- map {A B : Quoted Type} : (Quoted A -> Quoted B) -> Quoted (List A) -> Quoted (List B)
-- map A B f as := $[
--   foldr @{A, List B} (λ a bs. cons @{B} .(f $[a]) bs) (nil @{B})
-- ]

-- map : (𝐴 𝐵 : ⇑U0) → (⇑ ∼𝐴 → ⇑ ∼𝐵) → ⇑(List0 ∼𝐴) → ⇑(List0 ∼𝐵)
-- map := 𝜆 𝐴 𝐵 𝑓 as. ⟨foldr0 ∼𝐴 (List0∼𝐵) (𝜆 𝑎 bs. cons0 ∼𝐵 ∼(𝑓 ⟨𝑎⟩) bs) (nil0 ∼𝐵) ∼𝑎𝑠⟩
