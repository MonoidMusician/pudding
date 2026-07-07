Proofs Using Dependent Data In New Guises

_The Proofs are in the Pudding._

- Install/build instructions: docs/haskell.txt
- Design of syntax: docs/syntax.md
- Overview of code structure: docs/structure.md
- Glossary of type theory terms: docs/glossary.md

## Features

Pudding is just a new implementation of dependent type theory.
It is aimed a little more at the programming side of dependent type theory (“why doesn't every programming language use dependent types now?”), while still retaining logical consistency.

Particular things I want to explore in Pudding are:

- staging, via 2LTT (two-level type theory), generalized to arbitrary levels
- higher-order parametric polymorphism over universe levels, as arbitrary poset constraints (no successor universes!)
- row types via staging and constraints
- maybe something for nominal types for typeclasses
- maybe even a non-dependent fragment that compiles directly to Haskell

Staging should unlock better metaprogramming features, which will be good for the usability of Pudding and also potentially enable better codegen.

Staging enables using applicative parsers to implement LR parser generators.
The first stage, of assembling the grammar and then generating the parse table/automaton, can be cleanly separated from the second stage, of processing an input and building the output from the resulting parse tree.

## Sample

```pudding
@data Natural
| zero : Natural
| succ : Natural -> Natural


'' The standard right-associative list type
@data List (T : Type) : Type
| nil : List T
| cons : T -> List T -> List T

@derive Functor List
  '' Generates something like this:
  /'
  List'map @{I, O} (f : I -> O) : List I -> List O
  | nil := nil
  | cons (t : I) (ts : List I) :=
    cons (f t : O) (List'map f ts : List O)
  '/

List'append @{T} : List T -> List T -> List T
| nil, tail := tail
| cons t ts, tail := cons t (List'append ts tail)


@data Vector : Natural -> Type -> Type
| nil @{T} : Vector zero T
| cons @{n, T} : T -> Vector n T -> Vector (succ n) T

StagedVector : Natural -> % Type -> % Type
StagedVector zero     T := $quote[ Unit ]
StagedVector (succ n) T :=
  $quote[ Tuple $splice[T] $splice[StagedVector n T] ]

HList : List (% Type) -> % Type
HList nil := $q[Unit]
HList (cons T Ts) := $q[Tuple T (HList Ts)]
```

You can describe `StagedVector` as “compute a preview of a runtime type (`% (Type 1)`), given a compile-time natural number for its length (`n : Natural : Type 0`) and a preview of its runtime item type (`T : % (Type 1)`)”.
In the compile-time `zero` case, this is given by statically quoting the singleton type `Unit : Type 1` at the runtime stage `1`.
In the compile-time `succ n` case, it applies a runtime tuple type `Tuple : Type 1 -> Type 1 -> Type 1` with the splice of the item type `T` and the splice of the tail of the vector: `StagedVector n T`, which is still computed at compile time.
The elaborator can insert `$splice` as necessary, so this can be written `$quote[ Tuple T (StagedVector n T) ]`.

`$quote` then delimits the computation that happens at a later stage, and inside it, `$splice` will revert to computation at a previous stage.

Note that compile-time and runtime are meant figuratively here.
For one, it is polymorphic, so it is only *more* compile-time and *more* runtime in comparison to each other.
And previewed runtime values may be evaluated at compile-time too, especially if they are types, but even if they are involved in proofs.
Any mechanism that forces an ordinary term to be evaluated during typechecking can force a previewed term to be evaluated too.

## Stages, Axioms, and Constraints

Types are indexed by stage and universe level.

Stages right now are indexed with integers (positive and negative), with top-level polymorphism.
(Higher-order polymorphism is possible, but really limited in applicability, at least with this current setup.)

Universes are modeled by arbitrary posets with higher-order polymorphism.
Every construction in type theory is parametrically polymorphic over universe level, so why shouldn't we have nice things?

`Type 0 0` would refer to the type universe at stage zero, level zero.
`Type -1 0` and `Type +1 0` would be its adjacent stages.
Universe levels are always variables, though, so it would be `Type 0 u`, and so on.
These variables are almost always fresh variables and not written, just typechecked.

The typing of a universe keeps the stage and generates a strict constraint on the levels: `Type s u : Type s v =| u < v`.
To emphasize: **there is no successor universe**, only two level variables related by strict equality.
(I designed a poset solver to make this efficient.)


Pi/function types must have the *same stage* for input and output, and they again generate a constraint on the levels.
(You can think of this as taking the maximum of the universe levels.)

```
Γ |- I : Type s u
Γ, i : I |- O : Type s v
______________________________________________
Γ |- Π (i : I). O : Type s w =| u <= w, v <= w
```

Note that constraints are always aggregated, so this is shorthand for the following:

```
Γ |- I : Type s u =| C1
Γ, i : I |- O : Type s v =| C2
______________________________________________
Γ |- Π (i : I). O : Type s w
  =| C1, C2, u <= w, v <= w
```

The system for stages is really simple.
The type former is `%`, which lowers stage by one.
You can think of it as previewing a type associated with a later stage, in an earlier stage.
Then there is an introduction form `$quote[ ... ]` or `$q[ ... ]` for this type former and an elimination form `$splice[ ... ]` or `$s[ ... ]`.

```
Γ |- T : Type (s+1)
___________________
Γ |- % T : Type s

Γ |- t : T
______________________
Γ |- $quote[ t ] : % T

Γ |- t : % T
_____________________
Γ |- $splice[ t ] : T
```

Note that all of these are builtin syntax: because they transition between stages, they cannot be given Pi types, and thus cannot be given first-class names.

(There could maybe be a system for macro-like functions with hetereogeneous stages, where they must be saturated enough to sidestep the issue.)

### Row Types?

Hopefully staging will help with row types.

Symbols (used to index the rows) will be given by more-compile-time strings.

`Row : % Type 1 -> % Type 1`
`RNil @{T : Type 1} : % (Row T : Type 1) : Type 0`
`RCons @{T : Type 1} : (String : Type 0) -> % T -> % Row T -> % Row T : Type 0`

Magic constructors so that `RCons` can commute disparate symbols definitionally:

`RCons "x" T1 (RCons "y" T2 r) = RCons "y" T2 (RCons "x" T1 r)`

So that you can unify `RCons "x" _ _` with either one.

Note that a term of type `String : Type 0` is *not* a closed term.
Only after the first stage is fully evaluated is it guaranteed to be a closed term (a string/symbol literal).

Not every useful operation can be expressed as unification with a row, so it needs a system of constraints.

The constraints will all be solveable when the first stage is evaluated.

## Syntax

Type ascription is denoted by `:` as is customary, but it must have spaces on either side of it.
(In the interest of keeping Pudding ASCII-compatible, `:` is overloaded as a sigil for distfix operators. Most builtin symbols are this way.)
Unlike Agda/Mikan, type ascription is usable as both an expression and a binder: `(t : T)` should act the same as the term or binder `t`, just with the type `T` given/enforced.

Assignments always use `:=`, with `=` being reserved for the equality type: `(=) : Π @{T : Type} (t1 & t2 : T). Type`.
So top-level definitions may look like:

```
ex1 : Natural
ex1 := 1

ex2 : Natural := 2

ex3 := 3 : Natural
```

The binders for lambda, Pi, and Sigma should all have the same syntax so you can copy between them.
If `subsingleton : Π (T : Prop) (t1 & t2 : T). t1 = t2`, then it is applied as `subsingleton Unit unit unit : unit = unit`, meaning `T := Unit`, `t1 := unit`, and `t2 := unit`.
Its implementation can look like `λ T t1 t2. proof` or `λ T (t1 & t2). proof` and so on (with `t1 & t2` binding two terms of the same type), with the appropriate ascription to pin down the types, with the fully annotated `λ (T : Prop) (t1 & t2 : T). proof` not needing an expected type, as long as the type of `proof` can be synthesized.

These are actual binders, so they can have irrefutable pattern matches: unwrapping singletons, matching on records, and so on.

Implicit arguments are written `@{ ... }`, both in abstraction and in application.
They are record-like, having named positions.

```pudding
($) : Π @{I : Type} @{O : Type} (f : I -> O) (i : I). O
($) : Π @{I : Type, O : Type} (f : I -> O) (i : I). O
($) : Π @{I & O : Type} (f : I -> O) (i : I). O
($) : Π @{I := In : Type, O := Out : Type} (f : In -> Out) (i : In). Out
($) := λ @{I := Input, O := Output} (f : Input -> Output) i. f i

($) @{I := Natural, O := String} showNatural : Natural -> String

($) @{O := String} mempty
```

This defines a function whose implicits are named `I` and `O`: this is its public interface.
Within the Pi type or lambda, they can be renamed: to `In` and `Out` or `Input` and `Output` and so on.
The naming allows applying arguments out of order: only set `@{O := }`, for example.

### Lexical syntax

The lexical syntax is quite complicated because I want to preserve human syntax conventions.

Pudding borrows an operator/name/module/number distinction from Haskell, but it does not have case distinctions.
(Haskell uses case to distinguish constructors from variables: type constructors from type variables, and term variables from term constructors.)

The reason to distinguish operators and names is to not require spaces everywhere, like Agda does.
It is cool that `[_,_]` can be a tuple constructor, but having to write `[ x , y ]` all the time feels so unnatural.

Like Haskell, operators can also be turned into names: `(+)` is the name form of the operator `+`, usable in binders and so on.

Only literal names (not operator names) can be used as *distfix* operators.
Distfix operators are marked with a sigil before and/or after the name that indicates whether it is prefix, infix, or distfix.
The sigil is `·`, or `:` in ASCII (this is why type ascription needs a space around `:`).
A full distfix phrase can be turned into an operator name: the individual distfix operators do not have meaning on their own.
So `if: true :then: yay :else: boo` uses the infix operator named `(if:then:else:)`, and `yay :if: true :else: boo` uses the operator `(:if:else:)`; also `if· true ·then· yay ·else· boo` and `yay ·if· true ·else· boo` are equivalent.

Modules are written with apostrophes: `Control'`, `Control'Monad'`, `Data'List'Internal'`, and so on.

So you might write `Control'Monad'join` or `Control'Monad'(>>=)` to make qualified names, and even `ControlMonad'>>=` as a qualified infix operator.

Conversely, to disambiguate local variables (not qualified names), you can refer to them by de Bruijn indices and levels: named as `x@^0` (index zero: most recently bound `x`) or `x@_0` (level zero: first bound `x`), or even anonymous as `@^0` and `@_0` (the most recent or first bound variable of any name).
This ensures that every local variable can always be refrerenced, which is great for dependently-typed languages in particular.

Finally, commands are `@data`, `@module`, etc., and attributes are `@(infixr 0)` and so on.

There are also numbers and strings.
And details about operators with brackets.

### Datatypes and pattern matching

Inductive types are declared with `@data`, following the usual CIC (Calculus of Inductive Constructions) rules.
