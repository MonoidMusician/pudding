Equality is a funny thing.

Each theory really only comes with one notion of equality, up to equivalence.
Maybe one per modality.
But that does not prevent theorists from debating it endlessly.

Semantically there are a few places to stand:

- Start with an underspecified notion of equality, like Martin-Löf Type Theory (MLTT).
- Decide if you choose homotopy type theory, with a rich notion of equality between types (equivalent to isomorphism) and thus higher equalities, or Axiom K, which says that a proof of equality is trivial
- If you choose HoTT, you get function extensionality in the package deal.
  If you choose Axiom K, you can decide whether you want to add function extensionality (though it may not be pretty – it may not compute), or leave it out, or even negate it if you want to go for a hyperintensional theory (… although I would argue that is not really modeling mathematics at that point).

Computationally there are more nuances.

Reflexivity is the first ground rule.

All of equality originates from reflexivity, which the proof assistant decides from definitional/judgmental/algorithmic equality.
Everything that the proof assistant can compute to be equal, are equal for all notions of equality.
In fact, it forms a trivial proof of equality.

(Do not mistake this for saying that equalities between judgmentally equal types are always trivial: `Bool = Bool` has the reflexive proof, corresponding to the identity function, and a nontrivial path coming from `not` in HoTT.)

We also know that equality is symmetric and transitive: `x = y` implies `y = x` for symmetry, and for transitivity, `x = y` and `y = z` together imply `x = z`.

So far, this is what it means to be an equivalence relation.
But equality is the _smallest_ reflexive relation.

The “smallest” reflexive relation means that there is an induction principle based on reflexivity.
One formulation of this is known as Axiom J, but more on this later.

<!-- λΠΣ§·× -->

Leibniz equality is a common meeting ground.
Phrased as “the identity of indiscernables”, Leibniz equality means that, if nothing in the theory can tell two things apart, then they are in fact identical.
The property of being “indiscernable” can be expressed as “for all testers, the tester behaves equivalently for the indiscernable values”.
If you throw enough testers at it – a clever enough proposition or a comprehensive enough function – you should be able to distinguish any terms that are in fact distinct.
Contrapositively, any terms that are equal in one context need to be indistiguishable by everything in the theory, every tester, no matter how you compose them.

Set theorists are partial to using predicates for their testers, thus the formalization `LeibEqProp (T : Type) (t0 & t1 : T) : Prop := Π (P : T -> Prop). P t0 <-> P t1`, since `<->` (logical equivalence) is equality for propositions.
We could use functions, too: choose any type for the codomain, `LeibEqFun (T : Type) (t0 & t1 : T) : Type := Π (Codomain : Type) (F : T -> Codomain). F t0 = F t1` – using the equality for `Codomain`.

Of course that does not do much good if you do not have a primitive notion of equality.
So it often becomes `LeibEq (T : Type) (t0 & t1 : T) : Type := Π (F : T -> Type). F t0 -> F t1`: given *any* type function, a term of `F` at `t0` can be used to produce a term of `F` at `t1`, without any special knowledge of what `F` is.
It is pretty easy to see why this gives transitivity, and it gives symmetry by a clever choice of `F t := t = t0` and reflexivity.

Importantly, because any other notion of equality can be expressed as a type function by partial application, Leibniz equality implies those other equalities.

Now, this is much more comforting if you know that equality is a proposition: getting your hands on any element of the right equality type is technically all you need.
“A proof is a proof.”
If you are working in homotopy type theory, you want to know that you get the right equality, the right _path_ between terms.

Inductively defined equality, a classic of MLTT.

```
@data IndEq : Π (T : Type) (t0 & t1 : T). Type
| refl @{T : Type} @{t : T} : IndEq T t t
```

The major problem with this is that it only computes on `refl`.
Equalities are mostly just stuck, waiting to become `refl`, lacking important equations that would help along the way.
In cubical type theories, the inductive equality type has computational forms coming from univalence too.
Without cubical, univalence is postulated and has no computational content.


Observational Type Theory takes a different tact, which resembles the semantic story.
Observational equality computes on *type formers*, not on reflexivity.
The computational content of equality at each type is defined to be the right thing: inductively for inductive types, pointwise for functions (extensionality by definition!).
For dependent pairs, you get a dependent pair of equalities for the first and second projections.
And so on.
This is nice because it is still an equality type, but it comes in the form that you usually want to work with.


Cubical paths are _not_ inductively defined.
The non-fibrant interval type `I` with endpoints `0 : I` and `1 : I` (and some algebra – the exact algebra depends on the flavor of cubical type theory).
A path is described as a function `I -> T`.
The endpoints, at `0` and `1`, can compute differently but are semantically equal: their different computation must be justified by coming from a path.
These paths are generated by reflexivity (constant paths), path constructors for Higher Inductive Types (HITs), and glue types (used to implement univalence, turning isomorphisms into paths).

One great feature of cubical paths is that function extensionality is trivial to express, and equalities do not have to be decomposed into congruence and application and so on: they just need to be indexed by `i : I` in the right places.

- https://homepages.inf.ed.ac.uk/wadler/papers/leibniz/leibniz.pdf
