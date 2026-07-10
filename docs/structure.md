# Overview of Code Structure

Like many Haskell codebases, start with the types at the center of it all: Pudding/Core/Types.hs.

`Term` and `Eval` are the main ASTs for the core language: all of evaluation and typechecking happen on these types.
They define the logic and behavior of the language: what terms are allowed, when they are considered equal, and so on.

The user interacts with the surface language, which is nicer to write but leaves important details implicit, so it is not suitable for evaluation and typechecking.
The process of going from surface syntax to core syntax is called elaboration.
Interpreting surface syntax requires evaluation, typechecking, unification, constraint solving – everything you can think of.

## Core

The core language is intrinsically typed, meaning that they carry enough information to have a unique type, which can be obtained from the term.
This is inefficient in some ways but it increases confidence: the term can always be validated to typecheck on its own, given the correct context.

The evaluator for the core is in Pudding/Core/Eval.hs.
It uses normalization by evaluation (NbE), where `eval :: EvalCtx -> Term -> Eval` beta-reduces until it reaches binders (lambda, pi, sigma), which it captures in closures, and `quote :: QuoteCtx -> Eval -> Term` finishes evaluation under those closures and reads the expression back.
Normalizing a term, then, is the composition: `normalizeCtx :: EvalCtx -> Term -> Term`.
(This replaces rewriting systems, which would identify reductions directly on `Term` and perform intermediate substitutions often.)

Typechecking and unification build on evaluation, in Pudding/Core/Unify.hs.
(Evaluation diligently preserves types, but it does not need to reference this module.
Typechecking *does* depend on evaluation, so this avoids a cycle.)

Unification is not implemented yet.
Just conversion checking/validation/inference.


## Surface

The surface parser has a unique architecture, gradually parsing in four stages.

At the end emerges a CST type, which is the input to the elaborator.


