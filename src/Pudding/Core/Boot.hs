module Pudding.Core.Boot where

import Data.Foldable (fold)
import Data.Functor ((<&>), void)
import GHC.Stack (HasCallStack)
import Pudding.Core.Eval
import Pudding.Core.Unify
import Pudding.Core.Types
import Pudding.Types.Monads.Prover (unsafeRunProver)
import qualified Data.Map as Map
import qualified Data.Vector as Vector

-- Typecheck and share partial evaluation of globals

-- TODO: make sure definitions are acyclic!
bootGlobals, bootGlobalDefns, bootGlobalTypes :: HasCallStack => Globals -> Globals
bootGlobals = bootGlobalDefns . bootGlobalTypes

bootGlobalDefns globals =
  let
    newDefns = globalDefns globals <&> \case
      GlobalDefn _ _ (GlobalTerm defn _) -> unsafeRunProver ctx do
        ty <- typeofGlobal defn
        return $ GlobalDefn (arityOfTerm defn) ty (globalTerm defn)
    newGlobals = globals { globalDefns = newDefns }
    ctx :: forall t. Ctx t
    ctx = ctxOfGlobals newGlobals
    globalTerm tm = GlobalTerm tm (evalGlobal tm)
    evalGlobal = undeferred . eval ctx
    typeofGlobal tm = do
        ty <- validate tm
        return $ GlobalTerm (quote (void ctx) ty) (undeferred ty)
  in newGlobals

-- Add all the auxiliary definitions for all the auxiliary types
bootGlobalTypes globals =
  globals { globalDefns = globalDefns globals `disjointUnion` constructors (globalTypes globals) }
  where
  disjointUnion = Map.union
  -- disjointUnion = Map.unionWithKey \k _ _ -> error $ "Duplicate global: " <> show k
  fakeGlobal tm = GlobalDefn (arityOfTerm tm) undefined (GlobalTerm tm undefined)
  constructors = fold . Map.mapWithKey \typeName info ->
    fakeGlobal <$> Map.fromList (typeAuxDefns typeName info)

-- Auxiliary definitions for inductive types: add the type constructor and the
-- inductive constructors as terms to the global environment.
--
-- (This returns a list so that the type constructor comes first)
typeAuxDefns :: ("type name" @:: Name) -> GlobalTypeInfo -> [("type name" @:: Name, Term)]
typeAuxDefns typeName (GlobalTypeInfo { typeParams, typeIndices, typeConstrs }) = foldMap Map.toList
  -- The type constructor: take all of the parameters and the indices,
  -- and then make the fully applied type constructor term.
  [ Map.singleton typeName $
      abstract (Vector.toList typeParams <> Vector.toList typeIndices) $
        TTyCtor mempty typeName (toVars (Vector.length typeIndices) typeParams) (toVars 0 typeIndices)
  -- The term constructors: take all of the parameters and constructor
  -- arguments, then make the fully applied inductive constructor. (Note
  -- that the type indices are inferred from the parameters and arguments.)
  , flip Map.mapWithKey typeConstrs \ctorName (ConstructorInfo { ctorArguments }) ->
      abstract (Vector.toList typeParams <> Vector.toList ctorArguments) $
        TTmCtor mempty (typeName, ctorName) (toVars (Vector.length ctorArguments) typeParams) (toVars 0 ctorArguments)
  ]
  where
  -- Form repeated lambdas to turn the raw constructor into a curried function
  abstract ((p, b, paramType) : more) focus =
    TLambda mempty p b paramType $ Scoped $ abstract more focus
  abstract [] focus = focus

  toVars :: forall i. Int -> Vector.Vector i -> Vector.Vector Term
  toVars skipped = mapWithLevel \(_, Index idx) _ ->
    TVar mempty $ Index $ idx + skipped
