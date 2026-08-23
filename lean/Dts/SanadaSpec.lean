namespace Dts.SanadaSpec

/-! # Sanada Parameterized Strong-Promonad Arrow-Handler Specification

This document records the mathematical interface that the concrete, parameterized
arrow-handler semantics must implement.  It is based on the existing Lean files
`lean/Dts/Sanada.lean`, `lean/Dts/SanadaExperiment.lean`,
`lean/Dts/Commutativity.lean`, `paper/PAPER.md`, and on the fragments of
Sanada's work that were available through web search (JFP 2024 and the PhD
thesis).  Direct PDF retrieval was not possible from this environment, so the
exact equations that were not present in the search snippets are marked as
**gaps** and are filled in with the project plan as fallback.

## 1. Definitions

### 1.1 Strong promonad

Following Sanada, Definition 2.3 (strong promonad, Asada 2010; Asada & Hasuo
2010), let `C = (C, ⊗, J)` be a monoidal category.  A **strong promonad** on
`C` is an endoprofunctor

```
A : C ⇸ C
```

equipped with three 2-cells:

* **unit** `η^A : I_C ⇒ A`,
* **multiplication** `μ^A : A ∘ A ⇒ A`,
* **strength** `σ^A : (⊗*) ∘ (A × I_C) ⇒ A ∘ (⊗*)`.

They must satisfy the promonad unit, associativity and strength coherence
axioms.  In the concrete `Set` model used for the denotational semantics `A`
takes values in `Ens` (large sets):

```
A : Set^op × Set → Ens
```

with `η` playing the role of `arr`, `μ` the role of `(>>>)`, and `σ` the role
of `first`.

### 1.2 Signature

An effect signature `Σ` is a set of operation symbols.  Each `op ∈ Σ` has a
parameter (arity) type `γ` and a coarity (result) type `δ`, written

```
op : γ ⇝ δ.
```

### 1.3 Free strong promonad `A_Σ^*`

For a signature `Σ`, `A_Σ^*` is the **free strong promonad over `Σ`**.  It is
the initial `Σ`-generated strong promonad in `Ens`-Prof.  Sanada proves that it
is `Set`-small by counting normal forms of `Σ`-arrow terms (Yallop normal
forms).  For `X, Y ∈ Set`,

```
A_Σ^*(X, Y)
```

is the set of `Σ`-arrow terms of type `X → Y`.

**Gap.** The exact inductive presentation of `A_Σ^*(X, Y)` (its `pure` and `op`
term constructors and equations) was not recovered from the available search
snippets.  Fallback: the one-object `P0` in `SanadaExperiment.lean` (`pure f |
op a k`) is the seed of the general `Set`-small construction; it should be
lifted to an arbitrary small category with `lmap`/`rmap` and closure under the
free promonad operations.

### 1.4 Parameter set/object `S`

The denotational interpretation is parameterized by a fixed set

```
S ∈ Set.
```

`S` is the parameter object that is threaded through the input side of arrow
types and through handler clauses, allowing the `first`/strength of the
promonad to be treated without branching.

### 1.5 Interpretation of the arrow type

For each type `A`, `[[A]]_S` is a set.  For the arrow type the concrete target
is

```
[[A → B]]_S = A_Σ^*([[A]]_S × S, [[B]]_S).
```

The source of the free-promonad value is the product of the value input and the
parameter `S`.

### 1.6 `A`-algebra

For a strong promonad `A` on `C`, an **A-algebra** is a presheaf
`G : C^op → Set` (equivalently a profunctor `1 ⇸ C`) together with an action

```
α : A ∘ G ⇒ G
```

satisfying unit and multiplication (Eilenberg-Moore) axioms.

In the concrete `Set` model with carrier set `D`, an `A_Σ^*`-algebra is a
natural family of maps

```
act_X : A_Σ^*(X, D) → Set(X, D)
```

for `X ∈ Set`, such that

* `act_X(η(f)) = f` for every `f : X → D`,
* `act` is natural in `X`,
* `act` is compatible with the promonad multiplication (the multiplication law
  to be stated in §2).

This matches the `PromonadAlgebra` structure in `Sanada.lean`, except that the
general Eilenberg-Moore multiplication law for `act` is missing there and must
be added.

### 1.7 Handler-induced `A_Σ^*`-algebra

A handler

```
H = { x : C → P } ∪ { op, k : δ_D  z : γ → Q_op }_{op ∈ Σ}
```

of arrow type `C ⇒ D` induces an `A_Σ^*`-algebra `Alg_H` with carrier
`D = [[D]]_S`.

* The **return clause** `x : C → P` supplies the return map, i.e. the
  `A_Σ^*`-algebra homomorphism from the free algebra on `C` to `Alg_H` on the
  generator.
* The **operation clauses** `Q_op` supply, for each `op : γ ⇝ δ`, the
  operation interpretation

```
[[Q^op]]_S : A_Σ^*([[δ]]_S × S, D) → A_Σ^*([[γ]]_S × S, D),
```

which is used in the definition of `act_H`.

**Gap.** The exact recipe for building the full algebra action `act_H` from the
family `[[Q^op]]_S` and the return clause was not extracted from the available
sources.  Fallback: the recursive `handledAct h` in `SanadaExperiment.lean`
gives the intended shape; it must be generalized from `String → String` to the
parameterized free-promonad setting.

### 1.8 Operation interpretation `[[Q^op]]_S`

For each `op : γ ⇝ δ`, the handler clause `Q_op` is interpreted as a morphism
between free-promonad values

```
[[Q^op]]_S : A_Σ^*([[δ]]_S × S, D) → A_Σ^*([[γ]]_S × S, D)
```

with `D = [[D]]_S`.  Intuitively, `[[Q^op]]_S` takes a continuation `k` that
consumes a `δ`-value together with the parameter `S` and produces a `D`, and
returns an arrow that consumes a `γ`-value together with `S` and produces a
`D`.

## 2. Equations to implement

### 2.1 Promonad laws in Kleisli form

For `p ∈ A(X, Y)`, `q ∈ A(Y, Z)`, `f : W → X`, `g : Y → Z`:

```
bind(η(f), p) = lmap f p
bind(p, η(g)) = rmap g p
bind(bind(p, q), r) = bind(p, bind(q, r))
```

together with the `lmap`/`rmap`/`bind` naturality equations already present in
`Sanada.lean`.

### 2.2 Strength axioms

The strength `σ` must satisfy the standard strong-monad/profunctor strength
coherence laws.  In the `Set` model these translate into the usual `arr`/
`(>>>)`/`first` equations for arrows.  The exact six coherence diagrams from
Sanada's Fig. 1 were not recovered, so the fallback is to implement the Haskell
`Arrow` class laws:

```
first (arr f)      = arr (f × id_S)
first (p >>> q)    = first p >>> first q
first p >>> arr (id × g) = arr (id × g) >>> first p
```

and verify them against Definition 2.3.

### 2.3 Free-algebra universal property

For any object `C`, the free `A_Σ^*`-algebra on `C` is the presheaf
`A_Σ^*(-, C)` with multiplication `μ`.  For every `A_Σ^*`-algebra `(D, act_D)`,
there is a bijection

```
Hom_Alg(Free(C), (D, act_D)) ≅ Nat(C(-, C), D(-))
```

given by the universal property of the free algebra.  A handler is therefore the
unique `A_Σ^*`-algebra homomorphism

```
handle_H : A_Σ^*(-, C) → D(-)
```

induced by the return clause.

### 2.4 Algebra-homomorphism preservation

The unique homomorphism `h = handle_H` from the free algebra on `C` to the
handler algebra `Alg_H` on `D` must preserve the `A_Σ^*`-action.  In the
specialization of `PromonadHom.preserves` from `Sanada.lean` to the free
algebra, the equation is

```
h ∘ act_Free(p) = act_H( A_Σ^*(-, h)(p) )
```

where `act_Free` is the free algebra action (the multiplication `bind`) and
`A_Σ^*(-, h)(p)` is the profunctorial image of `p` under `h`.

**Gap.** The exact Kleisli form of this preservation equation for the
parameterized free promonad was not found in the snippets.  Fallback: the above
specialization of the abstract `PromonadHom` preservation equation.

### 2.5 Return clause

The return clause determines the algebra homomorphism on the generator of the
free algebra:

```
h( η( id_{[[C]]_S × S} ) ) = [[P]]_S : [[C]]_S × S → D.
```

Equivalently, the return map is the image of the identity under `h`.

### 2.6 Action of the induced algebra on an operation node

For an operation node `op(a, k) ∈ A_Σ^*(X, D)` with argument
`a : X → [[γ]]_S` and continuation `k ∈ A_Σ^*([[δ]]_S × S, D)`, the induced
algebra action `act_H` should satisfy

```
act_H( op(a, k) ) = act_H( [[Q^op]]_S(k) ) ∘ (a × id_S).
```

Here `[[Q^op]]_S(k) ∈ A_Σ^*([[γ]]_S × S, D)`, so `act_H` turns it into a
function `[[γ]]_S × S → D`; precomposing with
`⟨a, id_S⟩ : X × S → [[γ]]_S × S` yields the desired `X × S → D`.

**Gap.** This equation is the research conjecture derived from the type of
`[[Q^op]]_S` and the project experiment; it must be confirmed against the
full semantics in Sanada's paper.

### 2.7 Operation interpretation type

The central type to be inhabited in Lean, for every `op : γ ⇝ δ` in `Σ` and
every handler clause `Q_op`, is

```
[[Q^op]]_S : A_Σ^*([[δ]]_S × S, D) → A_Σ^*([[γ]]_S × S, D).
```

This is the definition that must be implemented before the recursive handler
action can be defined.

## 3. Gaps and recommended fallbacks

| Missing exact definition | Fallback in the repository |
|---|---|
| Inductive presentation of `A_Σ^*(X, Y)` | `SanadaExperiment.lean` (`P0` with `pure`/`op a k`); lift to a `Set`-small profunctor with `lmap`/`rmap` and normal forms. |
| Eilenberg-Moore multiplication law for `act` | Add the missing `bind`/`act` associativity equation to `PromonadAlgebra` in `Sanada.lean`. |
| Exact handler-induced algebra action | Use the `handledAct h` recursion in `SanadaExperiment.lean`; replace `String → String` with the parameterized `A_Σ^*([[δ]]_S × S, D)` continuation. |
| Full strength coherence diagrams | Implement the standard `arr`/`(>>>)`/`first` arrow laws and check them against Sanada's Definition 2.3. |
| Exact algebra-homomorphism equation in Kleisli form | Use `PromonadHom.preserves` from `Sanada.lean` specialized to the free algebra. |

## 4. Concrete milestone targets

### Milestone A

Construct a nontrivial handler `H` for a single operation `op : γ ⇝ δ` with a
clause `Q_op` that changes the operation's result (e.g. by applying
`h : γ → δ` to the argument before the continuation is run) and show that the
induced `PromonadHom` from the free `A_Σ^*`-algebra to the handled algebra
satisfies the preservation equation.  This is the first go/no-go test.

### Milestone B

For two operations `get : γ₁ ⇝ δ₁` and `log : γ₂ ⇝ δ₂` with disjoint handlers
`Cache` and `Logger`, prove that the right-P actions commute on all programs,
i.e. `ProfunctorCommute2` holds.

### Milestone C

Derive the programmer-facing reordering theorem:
`DisjointEffects(Cache, Logger) ⇒ SafeReorder(Cache, Logger)`.

### Milestone D (optional)

Expose compact `HandlerCertificate` values with `handledOps`, `semanticAction`,
and `commuteProof` so that separately compiled libraries can be reordered
without exposing source.

## 5. File plan

* `Dts/SanadaStrong.lean` (Phase 2): multi-object category, strong profunctor,
  promonad, algebras, homomorphisms, commutativity theorems.
* `Dts/SanadaParameterized.lean` (Phases 3-5): parameter `S`, free promonad
  `A_Σ^*`, the interpretation `[[A → B]]_S`, one nontrivial handler, and its
  preservation proof.
* `Dts/SanadaTwoHandlers.lean` (Phases 7-9): `get`/`log` example, `Cache` and
  `Logger`, the disjointness bridge, and `ProfunctorCommute2`.
* `Dts/SanadaBridge.lean` (Phases 10-11): derive safe reordering and connect
  to the existing concrete `Dts.Commutativity` theorem.

All new files should be additive only; do not modify `Dts/Commutativity.lean` or
`Dts/Sanada.lean` unless a genuine generalization is mathematically required.

-/

end Dts.SanadaSpec
