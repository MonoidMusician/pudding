# Overview of Code Structure

Like many Haskell codebases, start with the types at the center of it all: Pudding/Types.hs.

`Term` and `Eval` are the main ASTs for the core language: all of evaluation and typechecking happen there.

There will eventually be a surface syntax with its own AST, parser, and printer.
The process of going from surface syntax to core syntax is called elaboration.

The evaluator for the core is is in Pudding/Eval.hs.
It uses normalization by evaluation, where `eval :: EvalCtx -> Term -> Eval` beta-reduces until it reaches binders (lambda, pi, sigma), which it captures in closures, and `quote :: QuoteCtx -> Eval -> Term` finishes evaluation under those closures and reads the expression back.


