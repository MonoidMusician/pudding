module Pudding.Surface.Lexer where

import Prelude hiding (lex)
import Control.Applicative (many, (<|>), empty, asum, Alternative (some))
import Data.Foldable (fold, traverse_)
import Data.Functor (void, (<&>))
import Data.Function ((&))
import qualified Data.Text as T
import Data.Text (Text)
import Pudding.Types ()
import qualified Text.Parsec as P
import qualified Data.Set as Set
import GHC.Unicode (isAlpha, isAlphaNum, generalCategory, GeneralCategory (..))
import qualified Data.Text.IO.Utf8 as TIO
import GHC.Generics (Generic)
import Control.DeepSeq (NFData, rnf)
import Control.Monad.Identity (Identity (runIdentity))
import Witherable (Filterable(catMaybes))
import qualified Data.List as List
import qualified Prettyprinter as Doc
import Data.List.NonEmpty (NonEmpty(..), some1)
import Data.Semigroup.Foldable (intercalateMap1)
import Prettyprinter.Util (reflow)

instance NFData P.SourcePos where
  rnf a = seq a ()

demo :: IO ()
demo = do
  line <- TIO.getLine
  prelexed <- pure $ runIdentity (P.runPT (prelex <* P.eof) WHITESPACE "<input>" line)
  case prelexed of
    Left err -> TIO.putStrLn $ T.pack $ show err
    Right r -> do
      TIO.putStrLn $ T.pack $ show r
      tokenized <- pure $ runIdentity (P.runPT (tokenize <* P.eof) Nothing "<input>" r)
      case tokenized of
        Left err -> TIO.putStrLn $ T.pack $ show err
        Right ts -> do
          TIO.putStrLn $ T.pack $ show ts
  demo

-- Parsing the surface syntax is ... pretty complicated. I wanted nice pretty
-- syntax.
--
-- So there will be four(?) phases:
-- - Pre-lex, where the very basic lexems are recognized: names, operators,
--   and things that could be builtins.
-- - Tokenizing, where these are grouped into tokens that the parser actually
--   cares about. Things that are actually treated as names and operators
--   in the source.
-- - Basic parsing, that assembles the overall structure.
-- - Advanced parsing, that resolves operator precedence and so on.


--------------------------------------------------------------------------------
-- Data types and basics for prelexing
--------------------------------------------------------------------------------

-- This is a basic parsec parser, from text to basic lexemes.
-- TODO: add better source spans and handle indentation, eventually.
-- (megaparsec?)
type Prelexer = P.ParsecT Text LEX Identity

-- | Individual reserved characters: not allowed in any operators. That is,
-- | they are always filtered out of operators.
reserved :: Set.Set Char
reserved = Set.fromList
  [ ',' -- comma is used to separate lots of syntax
  , '\'', '"', '`' -- important for strings, comments, modules
  , '·', ':' -- these are really really special separators
  , '(', ')' -- parens and braces are always reserved
  , '{', '}' -- (not brackets ... i think those will technically be resolved as user operators)
  ]

-- | Semi-reserved characters that we need to distinguish after prelexing
-- | but may get coalesced back into user operators/names
semiReserved :: Set.Set Char
semiReserved = Set.fromList
  [ '_' -- uhh not sure on this!
  , '[', ']'
  ] <> reserved

-- | These are grabbed from the operator (or name) that they would match.
builtins :: [String]
builtins = List.nub $
  [ "@", "@^", "@_"
  , ":", "::"
  , ".", ";"
  , "|", "&"
  , ":=", "=:"
  , "?=", "=?", "??"
  , "\\", "λ", "Π", "Σ", "\\*", "\\+", "∀"
  ] <> (syntaxTable <&> \(_, b, _) -> T.unpack b)

-- | A lexeme from prelexing, with its source position and lexeme data.
data LEXED = LEXED !P.SourcePos !LEX
  deriving (Eq, Ord, Generic, NFData)
instance Show LEXED where
  show (LEXED _ l) = show l

-- | The types of comments: a line comment, and area comment, and a code comment.
data Comment
  = LineC !Text
  | AreaC !Text
  | CodeC ![LEXED]
  deriving (Eq, Ord, Show, Generic, NFData)

-- | A piece of syntax with comments, before and after if applicable.
data Commented t = Commented ![Comment] !t ![Comment]
  deriving (Eq, Ord, Generic, NFData, Functor, Foldable, Traversable)

-- TODO
-- I really think there should be some kind of hashconsed Name structure that
-- stores interned text, integers, and lists of names ... something like that
data Qualified t = Qualified ![Text] !t

-- | Basic lexeme data, as recognized during prelexing.
data LEX
  = WHITESPACE
  | COMMENT !Comment
  | BUILTIN !Text -- As enumerated in `builtins` and `reserved`/`semiReserved`
  | NAME !Text -- Roughly a recognizeable “word”: letters, combining marks, ...
  | OP !Text -- The operator syntax, including all the symbols
  | MOD !Text -- A module is a name followed by an apostrophe
  | NUM !Text -- Number
  | STR !Text -- String (raw contents, not processed)
  | UNKNOWN !Char
  deriving (Eq, Ord, Show, Generic, NFData)


--------------------------------------------------------------------------------
-- Some parser helpers
--------------------------------------------------------------------------------


-- | Run the parser. If it succeeds, revert to the state from before running it,
-- | and return the source position it ended at plus an action to resume from
-- | where it left off with the parsed result. Used to implement `longestOf`.
revertWithPos ::
  forall s u m a.
    Monad m =>
  P.ParsecT s u m a ->
  P.ParsecT s u m (P.SourcePos, P.ParsecT s u m a)
revertWithPos parser = do
  saved <- P.getParserState
  r <- parser
  p2 <- P.getPosition
  resumption <- P.getParserState
  _ <- P.setParserState saved
  pure (p2, r <$ P.setParserState resumption)

-- | Try several parsers and return the result of the one that parsed the most.
longestOf ::
  forall s u m a.
    Monad m =>
  [P.ParsecT s u m a] ->
  P.ParsecT s u m a
longestOf = go Nothing
  where
  go :: Maybe (P.SourcePos, P.ParsecT s u m a) -> [P.ParsecT s u m a] -> P.ParsecT s u m a
  go (Just (_, resultAndResume)) [] = resultAndResume
  go Nothing [] = empty -- throwError (userError "No token matched")
  go running (parser : more) = asum
    [ P.try do
        newResult <- revertWithPos parser
        let
          newRunning = Just case (running, newResult) of
            (Just (oldLen, r), (newLen, _)) | oldLen >= newLen ->
              (oldLen, r)
            (_, r) -> r
        go newRunning more
    , go running more
    ]

-- | During prelexing, run a parser and return the text that it matched.
sourceOf :: Prelexer a -> Prelexer Text
sourceOf parser = do
  i1 <- P.getInput
  _r <- parser
  i2 <- P.getInput
  pure $ T.take (T.length i1 - T.length i2) i1


--------------------------------------------------------------------------------
-- Actual stuff for the prelex pass
--------------------------------------------------------------------------------


-- | Parse something that looks like a name.
nameLike :: Prelexer Text
nameLike = sourceOf do
  _ <- P.satisfy isAlpha
  _ <- many $ P.satisfy \c -> isAlphaNum c ||
    -- Need to double check, but I think this covers combining diacritics
    -- and stuff like that.
    generalCategory c `elem` [NonSpacingMark, SpacingCombiningMark, EnclosingMark]
  pure ()

-- | Parse something that looks like an operator.
opLike :: Prelexer Text
opLike = sourceOf $ some do
  -- TODO: v@[+5]+2 ???
  -- P.notFollowedBy do
  --   P.anyChar
  --   _ <- numSign
  --   P.digit
  P.satisfy \c -> (&& not (Set.member c semiReserved)) $
    generalCategory c `elem`
    -- All the punctuation categories
    -- (Open and Close are not treated specially)
    -- (But open and close brackets may be... to be seen.)
    [ ConnectorPunctuation
    , DashPunctuation
    , OpenPunctuation
    , ClosePunctuation
    , OtherPunctuation
    -- Quotes
    , InitialQuote
    , FinalQuote
    -- All the symbols
    , MathSymbol
    , CurrencySymbol
    , ModifierSymbol
    , OtherSymbol
    ]

-- | Parse something that looks like a number: a sign, a base prefix, underscores
-- | as grouping, period as a decimal point, and an exponential suffix that is
-- | appropriate for the base.
numLike :: Prelexer Text
numLike = sourceOf do
  P.optional do
    -- Parse `3+5` as `3 + 5`
    P.getState >>= \case
      NAME _ -> empty
      OP _ -> empty
      NUM _ -> empty
      BUILTIN ")" -> empty
      BUILTIN "}" -> empty
      _ -> pure ()
    numSign
  asum $ numFormats <&> \(pre, chars, suf) -> do
    _ <- P.try $ P.string pre
    _ <- P.sepBy1 (P.many1 chars) (void (P.char '_'))
    P.optional $ P.char '.' <* P.sepBy1 (P.many1 chars) (void (P.char '_'))
    P.optional suf

-- | Number signs that we will consider prefixes to a number.
numSign :: Prelexer Char
numSign = P.char '+' <|> P.char '-' <|>
  P.char '±' <|> P.char '∓' <|> P.char '−' -- minus sign U+2212
    -- superscripts?

-- | Number formats: decimal, hexadecimal, octal, and binary.
numFormats :: [(String, Prelexer (), Prelexer ())]
numFormats =
  [ ("0x", void P.hexDigit, suffix "pP" P.digit)
  , ("0o", void P.octDigit, suffix "pP" P.digit)
  , ("0b", void (P.char '0' <|> P.char '1'), suffix "pP" P.digit)
  , ("", void P.digit, suffix "eE" P.digit)
  ]
  where
  suffix chars dig =
    void $ P.oneOf chars <* P.many1 dig

-- | Turn a text stream into a stream of prelexed tokens.
prelex :: Prelexer [LEXED]
prelex = do
  before <- (`LEXED` WHITESPACE) <$> P.getPosition
  inner <- many prelex1
  after <- (`LEXED` WHITESPACE) <$> P.getPosition
  pure $ [before] <> inner <> [after]

prelex1 :: Prelexer LEXED
prelex1 = liftA2 LEXED P.getPosition $ (>>= \t -> t <$ P.setState t) $ asum
  -- These options take priority
  [ asum
    [ WHITESPACE <$ some P.space
    -- Single line comments
    , ((P.try (P.string "''") <* some P.space) <|> P.try (P.string "#!")) *> do
        COMMENT . LineC . T.pack <$> P.manyTill P.anyChar (void (P.char '\n') <|> P.eof)
    -- Multi line comments (plain nesting)
    , P.try (P.string "/'") *> do
        COMMENT . AreaC . T.pack <$> P.manyTill P.anyChar (P.try (P.string "'/"))
    -- Multi line comments (tokenized nesting)
    , P.try (P.string "/`") *> (COMMENT . CodeC <$> prelex) <* P.try (P.string "`/")
    -- P.try (P.string "'\"'")
    -- Plain strings: returns the literal source
    , P.char '"' *> do
        STR . T.dropEnd 1 <$> sourceOf do
          P.manyTill
            -- This just selects one character of a backslash escape, because
            -- that handles escaping a quote and escaping a backslash
            ((P.char '\\' *> P.anyChar) <|> P.anyChar)
            (P.char '"')
    ]
  -- These options are lexed based on the longest available
  , longestOf
    -- A builtin, from `builtins`/`reserved`/`semiReserved`
    [ BUILTIN <$> longestOf (builtins <&> \s -> T.pack s <$ P.string s)
    , BUILTIN <$> asum (Set.toList semiReserved <&> \c -> T.singleton c <$ P.char c)
    -- Parse something that looks like a name:
    --   if it ends in an apostrophe, it becomes a module name
    --   (but it cannot end in two apostrophes, cuz that looks like a comment)
    , nameLike >>= \name ->
        -- Uhm module names are not *that* special,
        -- there is this trickiness about making sure we don't swallow comments here ...
        -- but I think since almost every Token ends up being qualified, it will be
        -- nice to have them handled up front!
        MOD name <$ ((P.char '\'' <* P.notFollowedBy (P.char '\'')) <|> P.char '§')
          <|> pure (NAME name)
    -- An operator
    , OP <$> opLike
    -- A number
    , NUM <$> P.try numLike
    ]
  -- Finally, a fallback
  , UNKNOWN <$> P.anyChar
  ]

--------------------------------------------------------------------------------
-- Now onto tokenizing
--------------------------------------------------------------------------------


-- | Relexing takes lexemes from prelexing and turns them into tokens.
-- | Whitespace+comments and handled specially: whitespace may be consumed but
-- | state is set so it can act again, as an assertion. Comments may be consumed
-- | or left for someone else to consume.
type Relexer = P.ParsecT [LEXED] (Maybe [Comment]) Identity


-- | A lexed token, with its position and token data.
-- TODO: source spans and indentation
data Token = Token !P.SourcePos !Tok
  deriving (Eq, Ord, Generic, NFData)

instance Show Token where show (Token _ t) = show t

-- | Tokens are divided into content words (containing data about what the user
-- | wrote), and functional words that shape the core syntax (commas and the like).
data Tok
  -- Content words, with data
  = Content !Content
  -- Functional words
  | Syntax !Syntax
  -- Comments
  | Comment !Comment
  deriving (Eq, Ord, Generic, NFData)

instance Show Tok where
  show (Content c) = show c
  show (Syntax s) = show s
  show (Comment c) = show c

data VariableDB
  = PlainVar
  | DBIndex !Word
  | DBLevel !Word
  deriving (Eq, Ord, Show, Generic, NFData)

instance Doc.Pretty VariableDB where
  pretty = \case
    PlainVar -> mempty
    DBIndex i -> reflow "@^" <> Doc.pretty i
    DBLevel l -> reflow "@_" <> Doc.pretty l

-- | Content words include names, operators, numbers, and so on. Names and
-- | operators are tricky because operators can be turned into names and names
-- | can serve as distfix operators, hence the need for pre-lexing. Also because
-- | some characters (especially the poor colon) are overloaded so much. In
-- | pursuit of an ASCII-amenable source code for a dependently typed language
-- | with custom user operators. Ahem.
data Content
  -- | A variable name, including (un)qualified names and names with a de Bruijn
  -- | index `x@^0` for index `0` of variable `x` (innermost/most recently bound,
  -- | i.e. always equal to `x`), and de Bruijn level `x@_0` for level `0` of
  -- | variable `x` (outermost/first bound)
  = VariableName !(Maybe NameForm) !VariableDB
  -- | A bare module name
  | ModuleName ![Text]
  -- | An operator, for the purposes of the syntax
  | QualifiedOp !OpForm
  -- | A command `@data`, `@module`, `@Builtin'thingy`, etc.
  | Command ![Text] !Text
  -- | Just a numeric literal
  | Number !Text
  -- | A string, lexed into its literal and template components
  | String ![Either Text [Token]]
  -- | Universe
  | Univ
  -- | A field `(expr).fieldName`
  | Field !Text
  -- | An index `(expr).0`
  | Index !Text
  -- | A symbol `(.symbolName)` (hmm maybe having the parentheses isn't a bad idea)
  | Symbol !Text
  -- | An dimension `(.1)` i guess?
  | Dimension !Text
  -- | An attribute annotation `@(derive stuff ...)`, `@(Qualified'attribute data ...)`
  | Attribute ![Text] !Text ![Token]
  -- | An implicit argument `@{Int}`, `@{T := Int}`
  | Implicits ![Token]
  -- | An operator section, like `(: 2 + _ :)`
  | Section ![Token]
  -- | A splice or quote, `$s[ ... ]` and `$q[ ... ]`
  | Splote ![Text] !Text ![Token]
  -- | Bracketed operator, like `Module'+[ ... ]+` for `Module'(+[:]+)`
  -- | (the bracket *is not* included in the texts, but should be included
  -- | in the Name later). Note that some operators like `,` may be parsed
  -- | as user operators inside brackets
  | Bracketed ![Text] !Text (NonEmpty ([Token], Text))

  | Parens ![Token]
  | Braces ![Token]
  deriving (Eq, Ord, Show, Generic, NFData)
-- | Functional syntax, like separators, parentheses, assignment, and so on.
data Syntax
  = SComma -- ,
  | SDisj -- |
  | SConj -- &
  | SAscribe -- :
  | SAssignL -- :=
  | SAssignR -- =:
  | SInspect -- ??
  | SMatchL -- ?=
  | SMatchR -- =?
  | SPeriod -- .
  | SPlaceholder -- _

  | SLambda
  | SPi
  | SSigma
  deriving (Eq, Ord, Show, Generic, NFData)
-- | Forms of names.
data NameForm
  -- | Just a plain name: `Quali'fied'name`, `thingy`
  = PlainName ![Text] !Text
  -- | Operators and names may be smushed together into a name with the use
  -- | of underscore or interpunct. (To be decided on interpunct, it may
  -- | conflict with other syntax where interpunct stands for colon...)
  -- | This will be nice for theorem names and so on.
  -- |
  -- | I want to keep good ol' ASCII hyphen-minus for minus, so you do not need
  -- | Unicode to do arithmetic (and so spaces are not required. is the whole
  -- | point of this elaborate dance with names and operators).
  -- | Hehehe, you are not the first to suggest `&nbsp;`!
  -- |
  -- | Examples: `Quali§fied§+_commutative`, `Q'f'commutate·+`
  | CompoundName ![Text] !(NonEmpty Text)
  -- | Like Haskell, it is nice to refer to operators in positions where a name
  -- | is expected. This may need some workshopping, especially to handle
  -- | disfixes. Is more aspirational right now.
  -- |
  -- | `(+)` short for `(:+:)`, `(:Vector'@[:])`, `(:+[:]+:)`, `($[:+:])`
  | OperatorName  ![Text] !(Maybe Text) ![Text] !(Maybe Text)
  -- | `(Control'if:then:else:)`, `Control'(:if:else:)`,
  | DistfixPhrase ![Text] !(Maybe Text) ![Text] !(Maybe Text)
  deriving (Eq, Ord, Show, Generic, NFData)
-- | Forms of operators.
data OpForm
  -- | Just a plain operator, `+` or `<>`
  = PlainOp ![Text] !Text
  -- | Distfix prefix: `if:`, `Control'if:`
  | DistPrefix ![Text] !Text
  -- | Distfix infix: `:then:`, `:Control'then:`
  -- | (that would not occur: you only qualify the first operator in a phrase)
  | DistInfix ![Text] !Text
  -- | Distfix postfix: `:else`, `:Control'else`
  | DistPostfix ![Text] !Text
  deriving (Eq, Ord, Show, Generic, NFData)


prettyMod :: [Text] -> Doc.Doc ann
prettyMod = foldMap \mname ->
  Doc.pretty mname <> reflow "'"

instance Doc.Pretty NameForm where
  pretty = \case
    PlainName qual name -> prettyMod qual <> Doc.pretty name
    CompoundName qual name -> prettyMod qual <> intercalateMap1 (Doc.pretty ".") Doc.pretty name
    OperatorName qual pre inf post -> prettyMod qual <> fold
      [ reflow "("
      , reflow $ T.intercalate ":"
        [ fold pre
        , T.intercalate ":" inf
        , fold post
        ]
      , reflow ")"
      ]
    DistfixPhrase qual pre inf post -> prettyMod qual <> fold
      [ reflow "("
      , reflow $ T.intercalate ":"
        [ fold pre
        , T.intercalate ":" inf
        , fold post
        ]
      , reflow ")"
      ]
instance Doc.Pretty OpForm where
  pretty = \case
    PlainOp qual name -> prettyMod qual <> Doc.pretty name
    DistPrefix qual name -> prettyMod qual <> Doc.pretty name <> reflow ":"
    DistInfix qual name -> prettyMod qual <> reflow ":" <> Doc.pretty name <> reflow ":"
    DistPostfix qual name -> prettyMod qual <> reflow ":" <> Doc.pretty name

-- | Match a lexeme and reset the cached whitespace/comment state.
lexeme :: forall r. (LEX -> Maybe r) -> Relexer r
lexeme f = P.setState Nothing *> P.tokenPrim show (\_ (LEXED pos _) _ -> pos)
  \(LEXED _ lexed) -> f lexed

-- | Match a specific value from a parser.
is :: forall t. Eq t => t -> Relexer t -> Relexer ()
is t p = P.try $ p >>= \r ->
  if r == t then pure () else empty


-- | Required whitespace, returns comments that may have occurred and clears
-- | them (so the next `comments` returns `mempty`).
comments1 :: Relexer [Comment]
comments1 = P.try $ asum
  [ P.getState >>= maybe empty pure
  , catMaybes <$> some do
      Nothing <$ pWHITESPACE <|> Just <$> pCOMMENT
  ] <* P.setState (Just mempty)

-- | Optional whitespace.
comments :: Relexer [Comment]
comments = comments1 <|> pure mempty

-- | Required whitespace. Leaves comments in state for the next `comments`.
-- | (They may never be read, that is okay.)
spaces1 :: Relexer ()
spaces1 = P.try $ asum
  [ P.getState >>= maybe empty (pure . const ())
  , do
      savedComments <- catMaybes <$> some do
        Nothing <$ pWHITESPACE <|> Just <$> pCOMMENT
      void $ P.setState (Just savedComments)
  ]

-- | Required whitespace on both sides of the given parser.
spaced :: Relexer t -> Relexer t
spaced p = spaces1 *> p <* spaces1

-- | Optional whitespace.
spaces :: Relexer Bool
spaces = True <$ spaces1 <|> pure False

-- | Assert there is no whitespace, no comments.
-- | TODO: maybe multiline comments can be used?
nospace :: Relexer ()
nospace = P.notFollowedBy spaces1


pWHITESPACE :: Relexer ()
pWHITESPACE = lexeme \case
  WHITESPACE -> pure ()
  _ -> empty
pCOMMENT :: Relexer Comment
pCOMMENT = lexeme \case
  COMMENT v -> pure v
  _ -> empty
pBUILTIN :: Relexer Text
pBUILTIN = lexeme \case
  BUILTIN v -> pure v
  _ -> empty
-- Consolidate underscores into a name
pNAME :: Relexer Text
pNAME = do
  pre <- many $ "_" <$ pB "_"
  body <- lexeme \case
    NAME v -> pure v
    _ -> empty
  pure $ fold pre <> body
pOP :: Relexer Text
pOP = lexeme \case
  OP v -> pure v
  _ -> empty
pMOD :: Relexer Text
pMOD = lexeme \case
  MOD v -> pure v
  _ -> empty
pNUM :: Relexer Text
pNUM = lexeme \case
  NUM v -> pure v
  _ -> empty
pSTR :: Relexer Text
pSTR = lexeme \case
  STR v -> pure v
  _ -> empty
pUNKNOWN :: Relexer Char
pUNKNOWN = lexeme \case
  UNKNOWN v -> pure v
  _ -> empty


-- | Match a specific builtin.
pB :: Text -> Relexer ()
pB t = pBUILTIN & is t

pBs :: [Text] -> Relexer ()
pBs = P.try . traverse_ pB

parens :: forall t. Relexer t -> Relexer t
parens inner = pB "(" *> spaces *> inner <* spaces <* pB ")"

braces :: forall t. Relexer t -> Relexer t
braces inner = pB "{" *> spaces *> inner <* spaces <* pB "}"

qualifier :: Relexer [Text]
qualifier = many pMOD


-- Table of operators/syntax to recognize. Note that
-- `SPlaceholder` is deliberately omitted.
syntaxTable :: [(Syntax, Text, Relexer () -> Relexer ())]
syntaxTable =
  [ (SComma, ",", id)
  , (SDisj, "|", id)
  , (SConj, "&", id)
  , (SAscribe, ":", P.try . spaced)
  , (SAssignL, ":=", id)
  , (SAssignR, "=:", id)
  , (SInspect, "??", id)
  , (SMatchL, "?=", id)
  , (SMatchR, "=?", id)
  , (SLambda, "λ", id)
  , (SLambda, "\\", id)
  , (SPi, "Π", id)
  , (SPi, "∀", id)
  , (SSigma, "Σ", id)
  , (SPi, "\\*", id)
  , (SSigma, "\\+", id)
  , (SPeriod, ".", P.try . (<* spaces1))
  ]




-- | Transform the prelexed stream to proper tokens.
tokenize :: Relexer [Token]
tokenize = spaces *> many (tokenize1 <* spaces)

-- And that is where it is at, currently!
tokenize1 :: Relexer Token
tokenize1 = liftA2 Token P.getPosition $ asum
  -- All the bits and bobs of syntax that stand on their own
  [ Syntax <$> asum do
      -- e.g. `SAssignL` recognizes `BUILTIN ":="`
      syntaxTable <&> \(r, s, w) -> r <$ w (pB s)
  -- The main tokens we recognize
  , Content <$> longestOf
    -- A number
    [ Number <$> pNUM
    , Univ <$ do pNAME & is "Type"
    -- Splice/quote
    , Splote <$> (is "$" pOP *> qualifier) <*> pNAME <*>
        (pB "[" *> tokenize <* pB "]")
    -- Bracketed operators
    , Bracketed <$> qualifier <*> (pOP <|> pure mempty) <*>
        some1 (liftA2 (,) (pB "[" *> tokenize <* pB "]") (pOP <|> pure mempty))
    -- A variable, including a bare name and `x@^0`/`x@_0` index/level notation
    , VariableName . Just
        <$> anyNameForm []
        <*> asum
          [ DBIndex . read . T.unpack <$> (pB "@^" *> pNUM)
          , DBLevel . read . T.unpack <$> (pB "@_" *> pNUM)
          , pure PlainVar
          ]
    -- A strictly qualified name, `Module'Path'To'identifier`
    , VariableName . Just <$> (qualifier >>= anyNameForm) <*> pure PlainVar
    -- An anonymous variable index or level
    , VariableName Nothing <$> asum
        [ DBIndex . read . T.unpack <$> (pB "@^" *> pNUM)
        , DBLevel . read . T.unpack <$> (pB "@_" *> pNUM)
        ]
    -- Plain operators and distfix operators
    , QualifiedOp <$> longestOf
        [ PlainOp <$> qualifier <*> pOP
        , DistPrefix  <$>                       qualifier  <*> (pNAME <* pB ":" <* spaces1)
        , DistInfix   <$> (spaces1 *> pB ":" *> qualifier) <*> (pNAME <* pB ":" <* spaces1)
        , DistPostfix <$> (spaces1 *> pB ":" *> qualifier) <*> pNAME
        , DistPrefix  <$>                       qualifier  <*> (pNAME <* pB "·" <* spaces1)
        , DistInfix   <$> (spaces1 *> pB "·" *> qualifier) <*> (pNAME <* pB "·" <* spaces1)
        , DistPostfix <$> (spaces1 *> pB "·" *> qualifier) <*> pNAME
        -- TODO: smart errors
        ]
    -- A module name on its own, `Control'Monad'`
    , ModuleName <$> some pMOD
    -- An attribute
    , do
        let inner = Attribute <$> qualifier <*> pNAME <*> tokenize
        pB "@" *> pB "(" *> spaces *> inner <* spaces <* pB ")"
    -- An implicit argument
    , Implicits <$> do
        pB "@" *> pB "{" *> spaces *> tokenize <* spaces <* pB "}"
    -- Field/index access
    , nospace *> pB "." *> do
        Field <$> pNAME <|> Index <$> pNUM
    -- A symbol/dimension
    , parens do
        nospace *> pB "."
        Symbol <$> pNAME <|> Dimension <$> pNUM
    ]
  , asum
    [ Syntax SPlaceholder <$ pB "_" -- FIXME: re-disallow +_+
    , pBs ["{", ":"] *> (Content . Section <$> tokenize) <* pBs [":", "}"]
    , Content . Parens <$> parens tokenize
    , Content . Braces <$> braces tokenize
    ]
  ]

anyNameForm :: [Text] -> Relexer NameForm
anyNameForm qual = longestOf
  -- Plain names (single identifiers)
  [ PlainName qual <$> pNAME
  -- Compound names
  , CompoundName qual <$> compoundName
  , parens $ asum
    -- Mixfix operator names
    [ P.try $ phrase (pB ":") pOP True $ OperatorName qual
    -- Distfix phrases
    , P.try $ phrase (pB ":") pNAME False $ DistfixPhrase qual
    ]
  ]
  where
  phrase :: forall t r.
    Relexer () -> Relexer t -> Bool ->
    (Maybe t -> [t] -> Maybe t -> r) -> Relexer r
  phrase sep item singletonAllowed ast = do
    hasPre <- False <$ sep <|> pure True
    let
      items :: Relexer (Bool, [t])
      items = do
        hd <- item
        asum
          [ do
              sep
              fmap (hd :) <$> items
                <|> pure (False, [hd])
          , pure (True, [hd])
          ]
    (hasPost, ops) <- items
    -- Reject `(if)` but allow `(+)` for `(:+:)`
    case (hasPre, ops, hasPost) of
      (True, [_], True)
        | singletonAllowed ->
            assemble ast False ops False
        | otherwise -> empty
      _ -> assemble ast hasPre ops hasPost
  assemble :: forall t r.
    (Maybe t -> [t] -> Maybe t -> r) ->
    Bool -> [t] -> Bool ->
    Relexer r
  assemble ast hasPre ops0 hasPost = do
    (pre, ops1) <- pure if hasPre
      then (Just (head ops0), tail ops0)
      else (Nothing, ops0)
    (post, ops) <- pure if hasPost
      then (Just (last ops1), init ops1)
      else (Nothing, ops1)
    pure $! ast pre ops post

-- TODO: require that at least one is a name?
compoundName :: Relexer (NonEmpty Text)
compoundName = do
  let
    part = asum
      [ (True,) <$> pNAME
      , (False,) <$> pOP
      , (False,) <$> pNUM
      ]
    sep = pB "_" <|> pB "·"
  parts <- liftA2 (:|)
    do part <* sep
    do P.sepBy1 part sep
  if any fst parts
    then pure $ snd <$> parts
    else error "Compound name requires one part to be a name"

type Parser r = forall u m. Monad m => P.ParsecT [Token] u m r

token :: forall u m r. Monad m => (Tok -> Maybe r) -> P.ParsecT [Token] u m r
token f = P.tokenPrim show (\_ (Token pos _) _ -> pos)
  \(Token _ tok) -> f tok

content :: forall u m. Monad m => P.ParsecT [Token] u m Content
content = token \case
  Content c -> pure c
  _ -> empty

syntax :: forall u m. Monad m => P.ParsecT [Token] u m Syntax
syntax = token \case
  Syntax s -> pure s
  _ -> empty

pVariableName :: Parser (Maybe NameForm, VariableDB)
pVariableName = token \case
  Content (VariableName a b) -> pure (a, b)
  _ -> empty
pModuleName :: Parser [Text]
pModuleName = token \case
  Content (ModuleName a) -> pure a
  _ -> empty
pQualifiedOp :: Parser OpForm
pQualifiedOp = token \case
  Content (QualifiedOp a) -> pure a
  _ -> empty
pCommand :: Parser ([Text], Text)
pCommand = token \case
  Content (Command a b) -> pure (a, b)
  _ -> empty
pNumber :: Parser Text
pNumber = token \case
  Content (Number a) -> pure a
  _ -> empty
pString :: Parser [Either Text [Token]]
pString = token \case
  Content (String a) -> pure a
  _ -> empty
pField :: Parser Text
pField = token \case
  Content (Field a) -> pure a
  _ -> empty
pIndex :: Parser Text
pIndex = token \case
  Content (Index a) -> pure a
  _ -> empty
pSymbol :: Parser Text
pSymbol = token \case
  Content (Symbol a) -> pure a
  _ -> empty
pDimension :: Parser Text
pDimension = token \case
  Content (Dimension a) -> pure a
  _ -> empty
pAttribute :: Parser ([Text], Text, [Token])
pAttribute = token \case
  Content (Attribute a b c) -> pure (a, b, c)
  _ -> empty
pImplicits :: Parser [Token]
pImplicits = token \case
  Content (Implicits a) -> pure a
  _ -> empty
pSection :: Parser [Token]
pSection = token \case
  Content (Section a) -> pure a
  _ -> empty
pParens :: Parser [Token]
pParens = token \case
  Content (Parens a) -> pure a
  _ -> empty
pBraces :: Parser [Token]
pBraces = token \case
  Content (Braces a) -> pure a
  _ -> empty

pComma :: Parser ()
pComma = token \case
  Syntax SComma -> pure ()
  _ -> empty
pDisj :: Parser ()
pDisj = token \case
  Syntax SDisj -> pure ()
  _ -> empty
pConj :: Parser ()
pConj = token \case
  Syntax SConj -> pure ()
  _ -> empty
pAscribe :: Parser ()
pAscribe = token \case
  Syntax SAscribe -> pure ()
  _ -> empty
pAssignL :: Parser ()
pAssignL = token \case
  Syntax SAssignL -> pure ()
  _ -> empty
pAssignR :: Parser ()
pAssignR = token \case
  Syntax SAssignR -> pure ()
  _ -> empty
pInspect :: Parser ()
pInspect = token \case
  Syntax SInspect -> pure ()
  _ -> empty
pMatchL :: Parser ()
pMatchL = token \case
  Syntax SMatchL -> pure ()
  _ -> empty
pMatchR :: Parser ()
pMatchR = token \case
  Syntax SMatchR -> pure ()
  _ -> empty
pPeriod :: Parser ()
pPeriod = token \case
  Syntax SPeriod -> pure ()
  _ -> empty
pPlaceholder :: Parser ()
pPlaceholder = token \case
  Syntax SPlaceholder -> pure ()
  _ -> empty
pLambda :: Parser ()
pLambda = token \case
  Syntax SLambda -> pure ()
  _ -> empty
pPi :: Parser ()
pPi = token \case
  Syntax SPi -> pure ()
  _ -> empty
pSigma :: Parser ()
pSigma = token \case
  Syntax SSigma -> pure ()
  _ -> empty