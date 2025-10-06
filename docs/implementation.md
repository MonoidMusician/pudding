The goal is to keep implementations compact: there shouldn't be too many places to update when you add a constructor to `Term` and `Eval`/`Neutral`.

Tricks:

- `EDeferred`
- `NGlobal`

Non-goals (for now):

- Coinductive types
- HoTT/Cubical/HITs, although it would be nice to be compatible with univalence
- Formal proof of consistency
