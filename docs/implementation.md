The goal is to keep implementations compact: there shouldn't be too many places to update when you add a constructor to `Term` and `Eval`/`Neutral`.

Tricks:

- `EDeferred`
- `NGlobal`
- `NHole`

Non-goals (for now):

- Coinductive types
- HoTT/Cubical/HITs, although it would be nice to be compatible with univalence
- Formal proof of consistency

Housekeeping TODOs:

- add Pudding.Types.Name.Global to handle the global symbol table, implicit mutation
- (eventually get around to adding a memoization thingy to WithStableName too)


https://github.com/AndrasKovacs/smalltt
https://gist.github.com/AndrasKovacs
