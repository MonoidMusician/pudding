The goal is to keep implementations compact: there shouldn't be too many places to update when you add a constructor to `Term` and `Eval`/`Neutral`.

Tricks:

- `EDeferred`
- `NGlobal`

Non-goals (for now):

- Coinductive types
- HoTT/Cubical/HITs, although it would be nice to be compatible with univalence
- Formal proof of consistency

Housekeeping TODOs:

- Pudding/{Syntax,Semantics,Types}
- move Meta/Desc/Fresh/Level/Index/(insert name here) to Pudding.Types.Base: stuff that isn't part of expressions
- move Name to Pudding.Types.Name
- but split most of it into Pudding.Types.WithStableName or something
- add sets and maps for WithStableName, using IntMap probably?
- add Pudding.Types.Name.Global to handle the global symbol table, implicit mutation
- (eventually get around to adding a memoization thingy to WithStableName too)
- maybe a map for Fresh too, also using IntMap


https://github.com/AndrasKovacs/smalltt
https://gist.github.com/AndrasKovacs
