- `:=` for definitions, `=` for builtin equality type
  - maybe parenthesized `:=` in binders too, like at-patterns in Haskell and `=` the compound pattern operator in Erlang
  - `& expr =? binder` and `& binder ?= expr` for case guards, `expr ?? | L | R` for Agda's `with` (multi-case guards).
  - `(binder1 := binder2)` for as-patterns
- `x@^0` for index `0` of variable `x` (innermost/most recently bound, i.e. always equal to `x`), and `x@_0` for level `0` of variable `x` (outermost/first bound)
- `t : T` for type ascription (with spaces around it)
- `prefix:` `:infix:` `:postfix` for distfix (eventually)
  - interpunct also allowed: `prefix·`, `·infix·`, `·postfix`
  - `{: 1 + _ :}` for operator sections
  - keep operator vs name vs numeral distinction from haskell
    - each operator lexeme must be consistent as infix vs prefix vs postfix, i guess! for mixing with function application
  - and `(+)`, `(:+:)` will turn an operator into a name
    - `(if:then:else:)`, `(Control'if:then:else:)`, `Control'(if:then:else:)`
    - `(:if:else:)`, `(:Control'if:else:)`, `Control'(:if:else:)`
    - `(:@[:])`, `(:+[:]+:)`, `($[:+:])`
  - but allow ${operator}_${name} or ${operator}·${name}, e.g. `+_comm` is a name, but `+-comm` is not, that would parse as `+- comm`
  - no distinction between constructors vs other names, though!
  - (especially because definitions should be able to be used in patterns)
  - (if you need to disambiguate, use `x@^0` vs `'x`?)
  - (`'x 'y` is not a char literal, yeah)
- mixfix operators with operator-lexemes
  - must all be operator names, not distfix names
  - can have sometimes-prefix operators in unambiguous positions, e.g. `(-5)` or `x + -5`
    - maybe `+5`/`-5` with no space is special cased anyway
    - i guess we just assume that there are no suffix operators?
  - other operators will be declared always-prefix, `f !!False`
- `::` is unused-reserved, but `:::` is okay
- `Module'name` for namespacing stuff
  - `@import Data'List'{List, length}`
  - `@import Data'List'{length} qualified as List'`
  - `@import Data'Map'{Int} as IntMap'`
  - maybe `Data'List'_` for `Data'List'List`?, uhh `'List'_` for `'List'List`? nothanks
- `.` is reserved
  - `expr.name` for record projection
  - maybe `.name` and `.1` for symbols and such. idk yet
- explicit quantifiers: `Π`/`\Pi`, `Σ`/`\Sigma`, `λ`/`\`, with binders like `Π x y (f1 f2 : x -> y) (g : y -> z). f1 ⨾ g = f2 ⨾ g`
  - ascii Pi, Forall, Sigma, Exists, Lambda
  - always have prefixes, no implicit `(x : T) -> o`
  - but I still want parameterized definitions/modules/datatypes, so we need some affordances there
  - maybe `\\` can optionally be the lambda binder if algebraists want to use `\` for converse division
  - maybe `\*` and `\+` for Pi and Sigma lol
- `|` to separate cases (like OCaml i guess), `,` and `;` are also reserved (for arrays/records/whatnot)
  - but maybe `;;` can be allowed
- `&` might as well get used for something too?
  - use it for case guards. that sounds nice
    - `| left x, left y & x == y & unify x y =? just z := z`
      - `if just z ?= unify x y then _ else _`
    - `& unify x y ??` to do a case, like `with` in agda
- `#` for `flip ($)` like PureScript
  - `start # add5 # add7 # sub10`
  - `start |> add5 |> add7 |> sub10`
- declarations/commands
  - prefixed with `@`?
  - maybe annotations can be `@(name ...)` and commands are just `@name`
  - qualified `@Module'name` too
- implicits
  - bind with `identity {I} : I -> I`, apply with `identity @{Int}`, possibly named `identity @{I := Int}`
- comments?? idk
  - `'' ` with a space? and `#!`
    - wanna leave `///` for a user operator
  - might as well have `/' ... '/`, nested in the slightly boring sense (i.e. not with string detection)
    - so if you do not have `'/` in a string literal and do not have `'' ... '/` on one line, then adding a layer of nesting will work fine
    - maybe ``/` `` and `` `/`` for code comments that do check string literals? idk
- indentation
  - maybe all functions introduce indentation? all constructs??
  - `let` vs `let ... in`
    - needs to dedent, so `let` should be at the start of the line...
    - otherwise `in` is required, e.g. for single line
  - `do`, `where` are okay, can be trailing
  - lambdas/binders act via indentation, so they can form bullet points
    - also can be trailing, but that does not allow bullet pointing?
    - or just take indentation of start of line
  - so each token needs to record what its indentation is, and access to what the indentation of the first token on the line is and the previous indentation level
    - record as (tabs, spaces) ... guess at graphemes if needed???

- `Module'prefix:`, `:Module'infix:`, `:Module'postfix`; `Module§prefix:`, `:Module§infix:`, `:Module§postfix`
  - no `Module':infix:` or `Module':postfix` i think ...

this is a little table i made of what things are builtin, reserved, or available for user operators
we like the idea that users could use tripled operators for, well, stuff

- Builtin, Reserved, or User (or Error)
  - `:` B, `::` R, `:::` U
  - `|` B, `||` U, `|||` U
  - `&` B, `&&` U, `&&&` U
  - `/` U, `//` U, `///` U
  - `\` B, `\\` R, `\\\` U
  - `'` B, `''` B, `'''` R
  - `"` B, `""` B, `"""` B
  - `(`, `)`, `{`, `}` B
  - `@` B, `@^` B, `@_` B
  - `...@[...]` U, `@@` U       <- this is the important line, brackets are for users
  - `=` U, `:=` B, `=:` R, `==` U
  - `??` B, `?=` B, `=?` B, `???` U, `?` U
  - `.` B
  - `Π`, `Σ`, `λ` B
  - `,` B, `,,` R, `,,,` R
  - `;` B, `;;` U, `;;;` U      <- I am not set on this, but I don't see harm in it yet
  - `` ` `` R (backtick is reserved)

```pudding
#!pudding

Fun I O := Π (i : I). O

@(infix 50 .r)
(->) : Type -> Type -> Type := Fun

identity : Π {T : Type}. Fun T T := λ x. x

compose : Π {X Y Z : Type}. Fun Y Z -> Fun X Y -> Fun X Z
compose f g x := f (g x)

'' The standard right-associative list type
@data List (T : Type) : Type
| nil : List T
| cons : T -> List T -> List T

@derive Functor List
  '' Generates something like this:
  /'
  List'map {I O} (f : I -> O) : List I -> List O
  | nil := nil
  | cons (t : I) (ts : List I) :=
    cons (f t : O) (List'map f ts : List O)
  '/

List'append {T} : List T -> List T -> List T
| nil, tail := tail
| cons t ts, tail := cons t (List'append ts tail)

'' Left-associative
@data Tsil : Π (T : Type). Type
| lin : Tsil T
| snoc : Tsil T -> T -> Tsil T

@data Nat : Type
| zero : Nat
| succ : Nat -> Nat

'' Match the associativity of List'append
Nat'add : Nat -> Nat -> Nat
| succ n, m := succ ('add n m) '' omit the namespace?
| zero, m := m


@(infix 50 .r)
(+) := Nat'add

@module List
  length {T} : List T -> Nat
  | nil := zero
  | cons _ ts := succ (length ts)

  length_homo {T} : Π (l1 l2 : List T). length (append l1 l2) = length l1 + length l2
  | nil, l2 := refl
  | cons _ l1, l2 :=
  prove:
      succ
        length (l1 <> l2)
    = succ (length l1)
    + length l2
  :by:
    cong
      succ
      length_homo l1 l2
  '' aka
  /'
  prove: succ (length (append l1 l2)) = succ (length l1) + length l2
    :by: cong succ (length_homo l1 l2)
  '/

  while_just {I O} :
    (I -> Maybe O) ->
    List I ->
    { justs : List O, tail : List I }
  '' interrogate `f i`, to match it against `just o`
  | f, cons i is & f i ??
  | f, cons _ is , just o
    '' bind the recursive call here, since it is convenient,
    '' even though this pattern guard cannot fail
    & { justs, tail } ?= while_just f is
    '' cons onto `justs`
    := { justs := cons o justs, tail }
  '' we revert the `& f i ??` now, by just matching two items
  | f, tail := { justs := nil, tail }
 
  while_right {I L R} :
    (I -> Either (I -> L) R) ->
    List I ->
    { rights : List R, leftover : List L }
  | f, cons i is & f i ??
  | f, cons _ is , right o
    '' we can also bind the other way
    & while_right f is =? { rights, leftover }
    := { rights := cons o rights, leftover }
  '' here is an example of using another case with `??`
  ''  (rebind `is := cons i is` since we
  ''   need the elements together anyways)
  | f, is        , left g
    := { rights := nil, leftover := List'map g is }
  '' maybe we will allow omitting field names
  | f, nil := { nil, nil }

match: thingy1, thingy2
| just x, left y := x + y
| _, right z := z
| _, _ := 0
```

`n:`: **`not:`** | `neg:`
(ambiguator)



- `()` and `{}` are never allowed in user operators, just `[]`
  - kind of want to allow `...@[...]` for vector indexing
- `:=` should be recognized just as a regular operator, i guess
- same with quantifiers

`''\s[^\n]*` -> TComment _
`\s:\s` -> TAnnotation
`@name` -> TCommand _
`@(` -> TAnnotate
`name@^num` -> TVar _ _
`name@_num` -> TVar _ _
`\S.name`, `\S.num` -> TField _
`\s.name`, `\s.num` -> TSymbol _
`.\s` -> TPeriod
`|`, `,`, `;` -> TSep _

- op: `:name`, `:name:`, `name:` (no spaces)
- name: `(:op:)` (no spaces)
- name: `(:Module'op:)` (no spaces)
- name: `op_name` (each component is either an operator or a name, and altogether they are a name)
- `{:`, `:}` for sections


- pre-lex (parse atomic names, numbers, operators, and language syntax tokens, keeping around spacing information)
  - Comment/Whitespace
  - NameLike
  - OperatorLike
  - NumberLike
  - Underscore `_`
  - Interpunct `·`
  - Colon `:`
  - At `@`
  - Section `'` or `§`
  - Assign `:=`
  - Period `.`
  - Comma `,`
  - Semicolon `;`
  - Bar `|`
  - {L,R}Paren
  - {L,R}Brace
- lex (parse compound tokens)
  - QualifiedName
  - QualifiedOperator
  - Number
  - Annotated
  - Field
  - Symbol
  - etc.
- handle identation and language syntax i guess
- into declarations and expressions
- finally expressions are interpreted according to operator precedence
