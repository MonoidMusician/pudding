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

-- De Bruijn Indices work well: a Lambda term (\0 -> 0) is stable in different
-- contexts, you can move around the syntax tree. And this is useful during
-- typechecking.

partialEval :: Term -> Term
partialEval = \case
  TFst _ (TPair _ _ left _ right) -> left
  TSnd _ (TPair _ _ left _ right) -> right
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

NuPRL, Isabelle (higher-order logic (HOL) theorem prover)

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
-- it is determiend because of this reflexivity here
```

[View from the Left](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/view-from-the-left/F8A44CAC27CCA178AF69DD84BC585A2D)

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
evaling = runBytecode . generateByte
```
