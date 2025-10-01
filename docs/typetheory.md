
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
