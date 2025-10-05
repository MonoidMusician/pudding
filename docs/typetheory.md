## Substitution & reductions (small step semantics), as a precursor to Normalization by Evaluation

```haskell
-- Substitution & reduction rules, for partial evaluation
-- - Very direct, easy to implement (just need to be careful about de Bruijn indices), works on any terms (especially open terms)
-- - Inefficient, lots of re-traversing, accidentally quadratic in some cases
substitute :: Index -> Desc "substitution" Term -> Term -> Term
substitute target subst = \case
  TVar _ idx | idx == target -> subst
  TVar meta idx -> TVar meta idx
  TLambda x y z ty body -> TLambda x y z (substitute target subst ty) (substitute (target + 1) (shift 1 subst) body)
  _ -> undefined

-- De Bruijn Levels are good for evaluation: they are stable during evaluation,
-- where you have one fixed context you are working in, that you push and pop from

-- Map Level Eval
-- 0 : first variable you introduced
-- 1 : second variable you introduced
-- ...
-- newest : arg

-- De Bruijn Indices work well: a closed term (\0 -> 0) is stable in different
-- contexts, you can move it around the syntax tree. And this is useful for
-- manipulating syntax.

partialEval :: Term -> Term
partialEval = \case
  TFst _ (TPair _ _ left right) -> left
  TSnd _ (TPair _ _ left right) -> right
  TApp _ (TLambda _ _ _ _ body) arg ->
    shift (-1) $ substitute (Index 0) (shift 1 arg) body
  _ -> undefined

-- Shifts are necessary cuz the syntax uses Indices here, using Levels
-- would save some of the headache at the expense of one pass remapping before
-- and one pass remapping after partial evaluation
shift :: Int -> Term -> Term
shift = undefined

-- ^ That is what not to do, but it is familiar and you can write it down “on paper”
```

This is how Dhall is specified on paper, although implementations should use NbE for efficiency: https://github.com/dhall-lang/dhall-lang/blob/master/standard/beta-normalization.md#functions

## Intrinsic vs Extrinsic typing

Intrinsic is where each term has a unique type: when you have a lambda, its argument is annotated, for example.

Dhall is one example of intrinsic types.
If you're given a Dhall term, you can always infer its type (if it is well typed). `inferTopLevel :: Term -> Maybe Term`.
`\(x : Int) -> x`
`identity = \(T : Type) -> \(x : T) -> x`
`identity Int +523`

Extrinsic types means that *programs* exist independently of types, and the same program can be assigned multiple types.
`\x -> x` is a valid program, `Int -> Int`, or `Nat -> Int`.
So here, typing would look like `checkType :: Term -> Type -> Boolean`.

Mathematically, they both are a relation (between terms and types), and intrinsic means this relation is functional and decidable.

Languages like Lean and Agda have a core syntax that is intrinsically typed, but the surface syntax does not look like that: it has implicits and other features that make it nicer to write.
Going from sugary surface syntax to filled-in core syntax is called elaboration, and involves type inference, type checking, and unification.

Implementation-wise, intrinsically typed languages do not need to be as elaborated as Dhall's syntax: their core syntax can be a little more lenient / less annotated, as long as the correct type can be passed down separately when needed.

```agda
id : {T : Type} -> T -> T
id x = x

id 45
-- means
id {T = Nat} (45 : Nat)

-- or you can annotate to a specific type, which fills in the implicit
(id : Nat -> Nat)
(id {T = Nat} : Nat -> Nat)
-- which is a different program than
(id {T = Int} : Int -> Int)
```

Examples of extrinsic typed languages: Isabelle (higher-order logic (HOL) theorem prover)

## Intensional vs Extensional

```
x0 : X
x1 : X
x0 = x1
-- in extensional typing, this proof would become a *definitional equality*, regardless of
```

```
-- in intensional (and HoTT), we need one end to be a free variable
x0 : X
.x1 : X := x0
-- dot marks it as already determined, so it does not actually participate in the context
refl : x0 = x1
-- it is determined because of this reflexivity here
```

[View from the Left](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/view-from-the-left/F8A44CAC27CCA178AF69DD84BC585A2D)

## [Observational type theory (OTT)](https://people.cs.nott.ac.uk/psztxa/publ/obseqnow.pdf)

The inductive equality type in MLTT computes on its constructor `refl {T} {t1 t2 : T} : t1 = t2`, via the induction principle called the “J” axiom.
Without `refl`, computation is blocked.
(Cubical type theory has a different builtin equality type, that uses a synthetic interval type, and computes differently. It can be converted to the inductive equality type too, with the usual issues of converting between types that compute differently.)

In OTT, I would summarize it by saying that equality *types* compute *on types*, in two senses of that phrase:

- For an equality on a known type former, `t0 : T0 = t1 : T1`, the equality type will also reduce to a compound type of equalities (§3.1)
  - If `T0` and `T1` are sigma types, it reduces to equality of the first projections conjoined with equality of the second projections
    ```
    (p0 : Σx0 : S0. T0) = (p1 : Σx1 : S1. T1)  ↦  (reduces to)
      (fst p0 : S0) = (fst p1 : S1) ∧
      (snd p0 : T0[fst p0]) = (snd p1 : T1[fst p1])
    ```
  - For pi types, it reduces to a principle that is closely equivalent to function extensionality: equality of arguments implies equality of results
    ```
    (f0 : Πx0 : S0. T0) = (f1 : Πx1 : S1. T1)  ↦  (reduces to)
      ∀x0 : S0. ∀x1 : S1. (x0 : S0) = (x1 : S1) ⇒
      (f0 x0 : T0[x0]) = (f1 x1 : T1[x1])
    ```

    OTT is a great way to bake in function extensionality, instead of having to add it as an uncomputable axiom!

- For an equality between types, `T0 = T1 : Type`, the equality type may reduce to a compound type of equalities (§3)
  - If `T0` and `T1` are sigma types, it reduces to equality of the first types conjoined with equality of the second types, under the assumption that the first _values_ are equal
    ```
    (Σx0 : S0. T0) = (Σx1 : S1. T1)  ↦  (reduces to)
      S0 = S1 ∧
      ∀x0 : S0. ∀x1 : S1. (x0 : S0) = (x1 : S1) ⇒ T0[x0] = T1[x1]
    ```
  - Similar for pi types
    ```
    (Πx0 : S0. T0) = (Πx1 : S1. T1)  ↦  (reduces to)
      S1 = S0 ∧
      ∀x1 : S1. ∀x0 : S0. (x1 : S1) = (x0 : S0) ⇒ T0[x0] = T1[x1]
    ```

The cool part is that, OTT actually matches up better with the semantic view here: verifying type theories often requires this kind of work on type equalities (e.g. a lot of the work of Alternkirch).

It definitely needs to be built-in to the system, because this kind of type-casing is not allowed within the system.
And heterogeneous equality is normally not well behaved either!

Is OTT compatible with univalence?

## Eta conversion (eta expansion / eta reduction)

https://ncatlab.org/nlab/show/eta-conversion

A couple options for implementation:

- Easiest: Eta-long in `quote`, conversion checking does not need to care, potentially eta-reduce during pretty printing
- Trickier: ignore eta in `quote`/`eval`, specifically handle eta-mismatches in conversion checking, and do nothing with the pretty printer
- ??: eta-reduce in `quote` (except for the unit type), handle the unit type specially in conversion checking, and maybe also handle the unit type in pretty printing

## De Bruijn Indexes vs Levels

These are the two opposite ways of numbering variables (to remove the need for alpha conversion, arising from different names given to variables).

- De Bruijn Indexes (the more common / historical variant) number the *most recent variable as zero*, and it counts upward into the older context
- De Bruijn Levels count the *first bound variable as zero* (outermost context), and it counts up as *new* variables are introduced

De Bruijn *Levels* work well for evaluation: they work just like familiar variables do or as a stack does.
Once a number is assigned to a variable, that number is used to refer to it from then on.

De Bruijn *Indexes* solve the opposite problem: they allow a term to be self-contained, and work the same in any context it is embedded in.
The de Bruijn-indexed lambda `λ 0` always refers to the identity function, returning the newly bound variable regardless of the syntax around it.

The formula to convert one into the other is the same as reversing the indices in an array: `(size of context) - 1 - (index or level)`, since the max value is `(size of context) - 1` and that is what the minimum value (`0`) needs to be mapped to.
See `idx2lvl` and `lvl2idx`.

## Identity function example

as one example:
in Haskell, the identity function is `id :: forall a. a -> a` and you use it like `id False` which means `id (False :: Bool) :: Bool`

in dependent type theory, the identity function is something like `id : Π(t : Type), Π(x : t), t`, and you use it like `id Bool False`

`(t : Type)` uses a type universe `Type` to function like `forall` in Haskell, but it is the same as any other dependent function

`Π(x : t), t` is a dependent function without any dependence (`x` does not appear after being bound), so we write it as `t -> t`

and finally, we don't want to have to _specify_ `Bool` to instantiate `id`: one could use a hole to indicate this, like `id _ False : Bool` which could solve for `_ = Bool`

or, we could introduce _implicit_ arguments which are filled in by default by an _elaborator_: `id : Π{t : Type}, t -> t` so that you use it like `id False` again, standing for `id {t = Bool} False`

## Misc / scratchpad


```javascript
function(evaledArg) {
  if (evaledArg instanceof Neutral)
    return evaledArg.addApp(evaledArg);
  return fn(evaledArg);
}
```

```haskell
-- Maybe a helpful idea?
generateBytecode :: Term -> Bytecode
runBytecode :: Bytecode -> (EvalCtx -> Eval)
evaling = runBytecode . generateBytecode
```
