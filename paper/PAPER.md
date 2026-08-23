---
title: "Declarative Handler Topology Synthesis for Arrow Effects"
author: "Luis Emidio"
date: "2025-08-23"
geometry: margin=1in
fontsize: 11pt
documentclass: article
number-sections: false
format:
  pdf:
    engine: xelatex
    linestretch: 1.15
    latex-max-runs: 1
---

# Declarative Handler Topology Synthesis for Arrow Effects

## Abstract

Sanada's arrow calculus makes the nesting of `handle` constructs a structural part of the program: the programmer must explicitly encode the order in which handlers intercept operations. We ask whether this topology can instead be declared as a precedence relation and compiled into the correct nesting.

Because the arrow calculus restricts handler composition to a linear, static sequence, the synthesis problem is not a search over arbitrary runtime topologies; it is the order-theoretic problem of finding a linear extension of a finite partial order over handlers. We present a compile-time pass that lowers such a relation into the nested `handle` expressions required by the calculus, and we formally establish that the pass preserves well-formedness, precedence, and staticity. For clause-disjoint handlers, we prove that swapping their order preserves the trace, and we machine-check the abstract `ProfunctorCommute2` certificate and the concrete bridge to the `Dts` trace theorem in a Sanada-style two-operation promonad fragment. The core structural and trace-level theorems are machine-checked in Lean 4.

The key result is that the declarative layer is added without changing the arrow calculus, its runtime, or admitting the dynamic effectful branching that the calculus excludes. The compiler emits ordinary nested `handle` terms that the existing runtime already executes.

## 1. Introduction

Algebraic effects allow programs to describe operations independently of their interpretation. Effect handlers subsequently determine how those operations are handled. This separation provides a useful foundation for modular programming, but the composition of handlers remains an explicit part of the program structure.

In Sanada's calculus for algebraic effects and handlers for arrows, handler composition is expressed by nested `handle` constructs. For example, a request `P` might be handled first by `Cache` and then by `Auth`:

```text
handle (handle P with Cache) with Auth
```

The nesting determines handler scope and therefore potentially affects program behavior. The programmer must consequently encode the desired handler topology directly in the term.

We investigate whether this topology can instead be specified declaratively.

The problem considered in this paper is narrower than general topology synthesis. We do not attempt to infer arbitrary computational graphs, physical layouts, or dynamic effect-routing structures. Rather, we consider the specific problem of **synthesizing the static nesting topology of arrow effect handlers**.

This approach is compatible with the structural restriction of the arrow calculus. In the semantic setting considered by Sanada, the algebraic structure associated with arrows corresponds to a sequence of operations rather than the branching operation trees associated with ordinary monads. In particular, the problematic case is runtime branching between effectful commands. Our synthesis pass does not introduce such branching: its output is a statically determined sequence of nested handlers.

Our central contribution is to identify handler topology as a declarative compilation target for arrow effects. Because the arrow calculus already fixes handler composition as a linear, static sequence, the compiler's task is not to invent a new runtime topology but to resolve a partial order into one of its linear extensions. We show that this resolution can be performed entirely at compile time, producing ordinary `handle` terms without extending the arrow calculus or its runtime and without admitting the dynamic effectful branching that the calculus rules out.

The contributions of this paper are:

1. **A declarative handler-topology model.** We define handler declarations independently of their syntactic nesting and express precedence as a relation over handlers.
2. **A static synthesis algorithm.** We reduce handler-topology synthesis to finding a linear extension of the declared precedence relation and lower the result to nested `handle` expressions.
3. **Structural correctness properties.** We establish that synthesis produces valid arrow-calculus terms and preserves declared handler precedence.
4. **A minimal implementation.** We describe a compile-time AST transformation for arrow-effect languages that reuses existing handler representations and virtual machines.
5. **An explicit expressiveness boundary.** We distinguish static synthesis, which produces a fixed handler topology, from runtime dynamic selection of effectful computations, which lies outside the arrow semantics considered here.
6. **A Lean 4 formalization.** The core structural and trace-level properties are mechanically verified in Lean 4. The Sanada promonad bridge is formalized for the two-handler fragment; §7.3 records the status of each claim.

## 2. Background

### 2.1 Sanada's Arrow Calculus

Sanada extends the arrow calculus of Lindley, Wadler, and Yallop with operations and handlers.

The relevant syntax (Figure 2 of the thesis) is:

```text
Terms       M, N, L ::= x | ⟨M, N⟩ | fst M | snd M | λx:A. M | M N | λ•x:A. P
Values      V, W    ::= x | ⟨V, W⟩ | λx:A. M | λ•x:A. P
Commands    P, Q, R ::= ⌊M⌋ | let x ⇐ P in Q | L • M | op(M) | handle R with H
Handlers    H       ::= { x:C → P } ∪ { op, k:δ_D z:γ → Q_op }_{op ∈ Σ}
```

A handler `H` consists of a return clause `{ x:C → P }` and a set of
operation clauses `{ op, k:δ_D z:γ → Q_op }`. Each operation clause binds:

* `z : γ` — the operation argument (arity γ);
* `k : δ_D` — the continuation (coarity δ);
* `Q_op` — the handler body for that operation.

The construct

```text
handle R with H
```

evaluates command `R` under handler `H`.

Handler nesting determines which handler is considered first when an operation is encountered. Thus the following two terms are structurally different:

```text
handle (handle P with H₁) with H₂
```

and:

```text
handle (handle P with H₂) with H₁
```

A declarative system must therefore synthesize this ordering explicitly.

### 2.2 Handler Topology

We distinguish handler topology from computational topology.

**Handler topology** is the nesting relation between effect handlers:

```text
H₁
 └── H₂
      └── H₃
           └── P
```

**Computational topology**, by contrast, describes dependencies between computations.

The present paper concerns only the former.

This distinction is important because the system does not infer a dataflow graph or physical layout. Its output is a valid handler nesting that realizes a declaratively specified precedence relation.

### 2.3 Arrow Operations and Sequential Structure

Sanada's semantic treatment of arrow effects is based on strong promonads. A relevant consequence is that the algebraic structure associated with arrows represents a sequence of operations rather than the branching operation trees associated with ordinary monadic effects.

This restriction has two consequences for our system.

First, a declarative handler topology must ultimately produce a linear nesting of handlers.

Second, a runtime construct that dynamically chooses between effectful commands based on the result of another effect cannot simply be introduced into the arrow calculus without changing its semantic model.

Our synthesis mechanism avoids both issues by computing the handler ordering statically.

## 3. The Declarative Handler Model

### 3.1 Handler Declarations

Let a declarative handler specification be:

```text
D = (H, ≺)
```

where:

- `H` is a finite set of handler declarations;
- `≺` is a precedence relation over `H`.

For example:

```text
fetch ≺ cache
cache ≺ log
```

states that `fetch` must be nested inside `cache`, and `cache` must be nested inside `log`.

The relation is not itself a nesting tree. It describes constraints on the eventual linear handler topology.

### 3.2 Partial Orders

The precedence relation is assumed to form a strict partial order.

Thus it is taken as finite, irreflexive, and transitive. Asymmetry is not an independent requirement: if `Hᵢ ≺ Hⱼ` and `Hⱼ ≺ Hᵢ` held together, transitivity would imply `Hᵢ ≺ Hᵢ`, contradicting irreflexivity. The Lean formalization proves this derivation explicitly as `irreflexive_transitive_implies_asymmetric`.

If two handlers are unrelated by the declared relation, the compiler is free to choose either relative order, subject to any additional semantic requirements imposed by the implementation.

If the relation contains a cycle:

```text
H₁ ≺ H₂
H₂ ≺ H₃
H₃ ≺ H₁
```

then no valid linear handler topology exists.

The compiler must reject such a specification rather than arbitrarily choosing an order.

### 3.3 Linear Extensions

A **linear extension** of `(H, ≺)` is a sequence:

```text
H₁, H₂, ..., Hₙ
```

such that:

```text
Hᵢ ≺ Hⱼ ⇒ i < j
```

The synthesis problem is therefore:

> Given a finite declarative handler specification `(H, ≺)`, compute a linear extension of its precedence relation.

A standard topological-sort algorithm is sufficient for this purpose.

The important point is that this is a compile-time ordering problem. No runtime branching is necessary.

## 4. Handler Topology Synthesis

### 4.1 Synthesis Function

Let:

```text
S(D, P)
```

be the synthesis function that takes a declarative specification `D` and an arrow command `P`.

Suppose the linear extension computed from `D` is:

```text
H₁, H₂, ..., Hₙ
```

The synthesized command is:

```text
handle (... handle (handle P with H₁) with H₂ ... ) with Hₙ
```

Equivalently:

```text
S(D, P) =
  handle (...(handle (handle P with H₁) with H₂)... ) with Hₙ
```

Thus the first handler in the linear extension is the innermost handler.

### 4.2 Example: a pipeline with multiple independent constraints

Consider a declarative specification for an HTTP request pipeline:

```text
Validate before Auth
Auth before Cache
Cache before Metrics
Auth before Audit
```

These constraints form the DAG:

```text
Validate → Auth → Cache → Metrics
              ↘
                Audit
```

`Audit` and `Metrics` are not comparable, and a `Retry` handler has no constraints with the others. The compiler must first validate that the relation is acyclic and then compute a linear extension. Two valid linear extensions are:

```text
[Validate, Auth, Cache, Audit, Metrics, Retry]
[Validate, Auth, Cache, Metrics, Audit, Retry]
```

Synthesizing the first yields:

```text
handle (
  handle (
    handle (
      handle (
        handle (
          handle body with Validate
        ) with Auth
      ) with Cache
    ) with Audit
  ) with Metrics
) with Retry
```

The second swaps `Audit` and `Metrics`. Both are topologically correct, but they are not necessarily observationally equivalent. If `Audit` and `Metrics` both handle the same operation, the one placed innermost catches it first, so the choice between the two extensions matters. Only when the handlers are clause-disjoint can they be safely reordered without changing behavior; that semantic admissibility condition is the subject of §14.1.

This example makes the partial-order formulation essential rather than decorative: the programmer declares the constraints that must hold and leaves the compiler to choose among the valid linearizations, subject to the semantic admissibility of the chosen order.

### 4.3 Priority as a Convenience Syntax

A total numeric priority is one convenient way to specify a precedence relation:

```text
priority(H₁) < priority(H₂)
```

implies:

```text
H₁ ≺ H₂
```

That is, a lower numeric priority means the handler is required to be nested more deeply. The compiler expands a priority assignment `H : n` into pairwise constraints: for every other handler `K`, if `n < priority(K)` then `H ≺ K`; if `n > priority(K)` then `K ≺ H`; and if `n = priority(K)` then no constraint is introduced between `H` and `K`. These derived constraints are merged with any explicit `before` constraints, and duplicates are removed. Thus the formal core of the language remains the partial-order relation; priorities are only syntactic sugar for a total order and are not semantically fundamental.

The more general representation is a partial-order specification:

```text
H₁ ≺ H₂
H₁ ≺ H₃
```

which leaves `H₂` and `H₃` unordered.

This distinction allows the compiler to reject genuinely contradictory constraints while avoiding unnecessary ordering requirements. It also means that two handlers with the same priority are not forced into a particular relative order; the compiler may use declaration order as a deterministic tie-break.

### 4.4 Synthesis as Two Problems

It is useful to separate synthesis into two distinct problems.

**Structural synthesis.** Given an acyclic partial order over handlers, find a linear extension and fold `handle` over it. This is the problem solved in §4.1 and §5. The guarantee is purely topological: every declared precedence constraint is realized in the generated nesting.

**Semantic admissibility.** When several linear extensions are valid, the compiler must choose one. Not every valid choice is observationally equivalent. The question is when a chosen order is guaranteed to produce the same trace as another. The two-handler case is treated in §14.1: when two handlers are clause-disjoint, the `synthesize_commutative_two` theorem states that the two orders produce identical traces, and the `SanadaBridge` module supplies a categorical `ProfunctorCommute2` certificate for that commutativity.

The structural problem is solved in this paper. The semantic admissibility problem is introduced and solved for the two-handler case; the general case remains future work.

## 5. Synthesis Algorithm

### 5.1 Algorithm

Given:

```text
D = (H, ≺)
```

and body `P`:

1. Validate that `≺` is acyclic.
2. Compute a linear extension of `≺`.
3. Initialize `R = P`.
4. For each handler in the linear extension, from innermost to outermost:

   - construct a `handle` node containing `R`;
   - replace `R` with the new node.

5. Return `R`.

In pseudocode:

```text
synthesize(D, P):
    ordered = topological_sort(D.precedence)

    result = P

    for H in ordered:
        result = handle(result, H)

    return result
```

### 5.2 Complexity

Let:

- `n = |H|` be the number of handlers;
- `m = |≺|` be the number of precedence constraints.

Using a standard topological-sort algorithm, ordering requires:

```text
O(n + m)
```

time.

Constructing the resulting nested AST requires:

```text
O(n)
```

additional time.

Thus the synthesis phase is linear in the size of the handler specification, assuming the precedence relation is represented explicitly.

### 5.3 Determinism and Multiple Linear Extensions

A partial order may have multiple valid linear extensions. For example, given:

```text
A ≺ C
B ≺ C
```

both `[A, B, C]` and `[B, A, C]` are valid linear extensions. The choice between them affects which of `A` or `B` is the innermost handler, which may in turn affect runtime behavior if `A` and `B` intercept overlapping operations.

For reproducible builds, the compiler can impose a deterministic tie-breaking rule, such as declaration order or handler identifier.

This does not change the declared precedence relation:

```text
H₁ ≺ H₂
```

remains mandatory, while unrelated handlers receive a deterministic but otherwise arbitrary ordering.

The question of when two handlers can be safely reordered without changing behavior is a semantic question (see §14.1).

## 6. Correctness Properties

The results in this section concern the relationship between the declarative specification and the generated term. They are intentionally separated by level:

1. **Syntactic correctness** — the generated `handle` term is well-formed.
2. **Topological correctness** — the nesting realizes every declared precedence constraint.
3. **Staticity** — the synthesis pass introduces no runtime `cond` branching.
4. **Trace-semantic equivalence** — the synthesized term has the same observable trace as a manually nested term, obtained here as a corollary of syntactic identity.

A richer operational or denotational semantics, including continuation capture and resumption, is left for future work.

### 6.1 Well-Formedness

We define a command as **well-formed** if every handler in it has at least one operation clause and all sub-terms are well-formed. This is a structural property checked recursively:

```text
isWellFormed(handle P with H) = |H.clauses| > 0 ∧ isWellFormed(P)
isWellFormed(let x ⇐ P in Q)   = isWellFormed(P) ∧ isWellFormed(Q)
isWellFormed(cond P Q R)       = isWellFormed(P) ∧ isWellFormed(Q) ∧ isWellFormed(R)
isWellFormed(op(M))            = true
isWellFormed(⌊M⌋)              = true
```

**Proposition 1 — Well-Formedness.**

For every finite acyclic handler specification `D = (H, ≺)` and well-formed command `P`, if every handler in the linear extension of `≺` has at least one clause, then `S(D, P)` is well-formed.

**Proof sketch.**

The synthesis folds `handle` over the linear extension. Each step wraps the current term with a handler `Hᵢ` that has at least one clause. By the definition of `isWellFormed`, wrapping a well-formed term with a handler that has clauses preserves well-formedness. Induction over the handler sequence establishes the result. The accompanying Lean formalization proves this as `synthesize_well_formed`.

### 6.2 Precedence Preservation

**Proposition 2 — Precedence Preservation.**

For every pair of handlers `Hᵢ` and `Hⱼ`:

```text
Hᵢ ≺ Hⱼ
```

implies that `Hᵢ` is nested inside `Hⱼ` in `S(D, P)`.

**Proof sketch.**

The synthesis algorithm uses a linear extension of `≺`. By definition of a linear extension:

```text
Hᵢ ≺ Hⱼ ⇒ position(Hᵢ) < position(Hⱼ)
```

Since handlers are folded from the innermost position toward the outermost position, `Hᵢ` is constructed before `Hⱼ` and is therefore nested inside it.

The key invariant is that if `Hᵢ` appears before `Hⱼ` in the ordered list, then for any body term, `Hᵢ` is nested inside `Hⱼ` in the result of folding `handle` over that list. This is proved by induction on the `AppearsBefore` relation, with two helper lemmas handling the fold accumulation pattern. The accompanying Lean formalization proves this as `synthesize_preserves_precedence`. 

**Corollary — Completeness.**

If `ordered` is a linear extension of `≺` (i.e., `∀ a b, a ≺ b ⇒ AppearsBefore(a, b, ordered)`), then for every constraint `Hᵢ ≺ Hⱼ` in `≺`, `Hᵢ` is nested inside `Hⱼ` in `synthesize(P, ordered)`.

This follows directly from Proposition 2: the linear extension property ensures `AppearsBefore(Hᵢ, Hⱼ, ordered)`, and Proposition 2 converts this into structural nesting. The Lean formalization proves this as `synthesize_completeness`.

The soundness of the topological sort — the fact that it produces a list satisfying the linear extension property — is also formally verified, as `exists_linear_extension` in `TopoSort.lean` (§7.2). This theorem proves that for any finite list of handlers with an irreflexive and transitive precedence relation, there exists a linear extension realizing all precedence constraints as `AppearsBefore`.

### 6.3 No Introduced Runtime Branching

We define a command as **static** if it contains no `cond` (runtime conditional branching) constructor. The `isStatic` predicate is checked recursively:

```text
isStatic(handle P with H) = isStatic(P)
isStatic(cond P Q R)      = false
isStatic(let x ⇐ P in Q)  = isStatic(P) ∧ isStatic(Q)
isStatic(op(M))           = true
isStatic(⌊M⌋)             = true
```

**Proposition 3 — Static Topology.**

If the body command `P` is static (contains no `cond`), then `S(D, P)` is also static. Synthesis introduces no runtime branching over effectful commands.

**Proof sketch.**

The synthesis function folds `handle` over the ordered list. Since `isStatic(handle P with H) = isStatic(P)`, wrapping with a handler preserves staticity. By induction over the handler list, if the initial body is static, the result remains static. The `cond` constructor is never introduced by synthesis — it only appears if it was already present in the body.

The accompanying Lean formalization proves this as `synthesize_static_topology`, with the `cond` constructor explicitly included in the `Command` type to make the theorem non-vacuous.

### 6.4 Semantic Boundary

The preceding property should not be interpreted as proving that arbitrary dynamic effect-routing programs can be represented in the arrow calculus.

Rather, the result establishes a narrower fact:

> A static declarative description of handler precedence can be compiled into the existing static handler-nesting mechanism without introducing the dynamic command branching excluded by the underlying arrow model.

This distinction is central to the scope of the system.

## 7. Formalization in Lean 4

The properties described in §6 — syntactic, topological, staticity, and trace-semantic — have been mechanically verified in Lean 4. The formalization is split across the following files under `Dts/`.

Core synthesis and semantics:

- `Basic.lean` — core types (`Command`, `Handler`, `isStatic`, `isWellFormed`)
- `Precedence.lean` — precedence model, partial orders, acyclicity
- `Synthesis.lean` — synthesis function, well-formedness, precedence preservation, staticity, completeness
- `TopoSort.lean` — topological sort soundness (`exists_linear_extension`)
- `Semantics.lean` — trace semantics for `Command` (observable handler-dispatch events)
- `SemanticEquivalence.lean` — semantic equivalence of synthesized and manually nested terms
- `Commutativity.lean` — semantic commutativity of disjoint handlers, with counterexample

Sanada arrow-calculus bridge:

- `Sanada.lean` — abstract profunctor, promonad, and P-algebra model
- `SanadaStrong.lean` — multi-object strong profunctors and diamond commutativity
- `SanadaParameterized.lean` — concrete one-operation parameterized strong promonad
- `SanadaTwoHandlers.lean` — two-operation term model and `ProfunctorCommute2`
- `SanadaBridge.lean` — derives concrete `Dts.Commutativity` from the promonad certificate
- `SanadaSpec.lean` — specification and gaps for the full Sanada semantics (kept as documentation, not a required model)
- `EffectBridge.lean` — concrete `get`/`log` example instantiating the abstract diamond

Topological sort is also implemented in the self-hosted `ListDigraph/` library (`ListDigraph.Basic.lean` and `ListDigraph.TopSort.lean`).

The root `Dts.lean` imports the core modules. The project is intended to compile with no `sorry` and no admitted proofs; the status of each component is given in §7.3. Mathlib is used for tactic utilities only (e.g., `omega`, `push_neg`); no mathematical content is imported from it.

### 7.1 Model

The Lean model mirrors the paper's definitions:

- `Command` is an inductive type with constructors `pure`, `op`, `letin`, `handle`, and `cond`. The `cond` constructor represents runtime conditional branching; its inclusion makes the staticity theorem (Proposition 3) non-vacuous.
- `Precedence` is a function `Handler → Handler → Bool`.
- `synthesize body ordered` is a left fold over the ordered handler list, matching the paper's `S(D, P)`.
- `AppearsBefore` is an inductive predicate capturing list ordering without relying on numeric indices.
- `NestedInside` is an inductive predicate capturing handler nesting structure.

### 7.2 Proven Theorems

- `irreflexive_transitive_implies_asymmetric` — Lemma: asymmetry is derivable (not assumed)
- `partialOrder_acyclic` — Acyclicity of partial orders
- `synthesize_well_formed` — Proposition 1 (conditional on non-empty clauses)
- `synthesize_preserves_precedence` — Proposition 2
- `synthesize_static_topology` — Proposition 3 (conditional on body being static)
- `synthesize_completeness` — Corollary (completeness given linear extension)
- `reachable_implies_edge` — Lemma: reachability implies a direct edge (used by acyclicity)
- `exists_linear_extension` — Topological sort soundness (existence of linear extension)
- `synthesize_eq_manuallyNested` — Syntactic equality of synthesis and explicit nesting
- `synthesize_equiv_manuallyNested` — Trace equivalence as a corollary of syntactic identity (not an independent semantic theorem)
- `synthesize_commutative_two` — Semantic commutativity for disjoint handlers (§14.1)
- `handler_commute_iff_profunctor_commute` — Abstract iff: two endo-handlers commute iff their right-P actions commute (`Sanada.lean`)
- `handler_diamond_commute` — Diamond commutativity from `ProfunctorCommute2` (`SanadaStrong.lean`)
- `eval_preserves` — Nontrivial one-operation handler preserves the `P`-algebra action (`SanadaParameterized.lean`)
- `profunctorCommute₂` — Concrete `P₂` commutation for two independent one-operation handlers (`SanadaTwoHandlers.lean`)
- `Commutativity_from_ProfunctorCommute2` — Machine-checked bridge from the promonad certificate to concrete `Command.Equiv` (`SanadaBridge.lean`)

### 7.3 Formalization status

The repository is divided into three formalization categories so that the paper's claims can be verified against the code at any point.

**Formally complete.** The following results are machine-checked in the current `lake build`:

- `irreflexive_transitive_implies_asymmetric`, `partialOrder_acyclic`, `exists_linear_extension` — partial-order/topological properties;
- `synthesize_well_formed`, `synthesize_preserves_precedence`, `synthesize_static_topology`, `synthesize_completeness` — core synthesis correctness;
- `synthesize_eq_manuallyNested`, `synthesize_equiv_manuallyNested` — syntactic and trace equivalence of synthesis to explicit nesting;
- `synthesize_commutative_two`, `firstHandler_swap`, `evalWith_swap` — two-handler trace commutativity;
- `eval_synthesize` — `eval (synthesize b hs)` equals `evalWith hs b`;
- `synthesize_adjacent_swap` — swapping any adjacent disjoint pair of handlers in the synthesized list preserves the trace;
- `profunctorCommute₂` in `SanadaTwoHandlers.lean` — abstract `P₂` commutation for two independent one-operation handlers;
- `handler_commute_iff_profunctor_commute`, `handler_diamond_commute` in `Sanada.lean` and `SanadaStrong.lean` — abstract profunctor-level iff and diamond theorems.

**Formally complete within a fragment.** `SanadaBridge.lean` is now machine-checked and part of the current `lake build`: it shows that the abstract `ProfunctorCommute2` certificate in `SanadaTwoHandlers.lean` implies the concrete two-handler `Command.Equiv` trace-equality theorem in `Dts.Commutativity.lean` (`Commutativity_from_ProfunctorCommute2`).

**Proofs in progress / future work.** The full arrow-calculus bridge connecting the abstract strong-promonad model to every `Dts` command is intentionally not attempted. The `get`/`log` concrete example in `EffectBridge.lean` instantiates the abstract diamond with two independent operations, but it is not yet wired into the root `Dts.lean` build.

The `exists_linear_extension` result used by `synthesize_completeness` is a constructive version of the standard order-theoretic linear-extension theorem (Szpilrajn's extension theorem) and is proved in `TopoSort.lean`.

## 8. Relationship to Arrow Expressiveness

Sanada's arrow calculus restricts effectful commands to a linear, static sequence. The problematic case for our purposes is runtime branching between effectful commands, such as:

```text
v ⇐ op()
if v then P₁ else P₂
```

where `P₁` and `P₂` are effectful. Our synthesis pass does not introduce such branching. The handler topology is fixed at compile time:

```text
H₁ → H₂ → H₃ → P
```

Pure term-level branching remains possible, but the handler order itself is independent of operation results. This restriction is what makes compile-time synthesis well defined: if the topology could depend on runtime paths, a static linear nesting would no longer suffice.

## 9. Declarative Language Design

### 9.1 Syntax

A concrete configuration syntax can expose handler precedence without exposing the underlying nesting. The grammar is intentionally small, with two kinds of top-level declarations: handler declarations and precedence constraints. Handler declarations may optionally list the operation clauses they handle; constraints may be explicit `before` relations or numeric priorities.

A grammar is:

```text
<spec>      ::= <decl>*
<decl>      ::= "handler" <name> ("handles" <op> ("," <op>)*)?
              | <name> "before" <name>
              | <name> ":" <integer>
              | "#" <comment>
<name>      ::= <identifier>
<op>        ::= <identifier>
<integer>   ::= <decimal integer>
```

For example:

```text
events:
  - handler: Cache
    before: [Logging]

  - handler: Authentication
    before: [Cache]

  - handler: Logging

body:
  application
```

This corresponds to:

```text
Authentication ≺ Cache ≺ Logging
```

An equivalent syntax using explicit relations and numeric priorities is:

```text
handler Authentication handles authenticate
handler Cache handles lookup, store
handler Logger handles log

Authentication before Cache
Cache before Logger
```

or:

```text
handler Authentication
handler Cache
handler Logger

Authentication: 10
Cache: 20
Logger: 30
```

The configuration language need not expose `handle` directly. The frontend parses these declarations into a `Spec = (H, ≺)` value, where `H` is the set of declared handlers and `≺` is the transitive, acyclic closure of the explicit and derived constraints.

### 9.2 Explicit Relations versus Priorities

We recommend treating explicit precedence constraints as the semantic core:

```text
Authentication before Cache
Cache before Logging
```

Numeric priorities can be provided as syntactic sugar:

```text
Authentication: 10
Cache: 20
Logging: 30
```

This avoids coupling the language semantics to an arbitrary numeric scale.

### 9.3 Invalid Specifications

The compiler should diagnose at least:

- cyclic precedence constraints;
- duplicate handler identities;
- references to undefined handlers;
- malformed handler clauses;
- conflicting declarations.

For example:

```text
A before B
B before A
```

must produce a compile-time error because no valid linear nesting satisfies both constraints.

## 10. Implementation

The proposed implementation is deliberately small.

The declarative frontend produces handler declarations and precedence constraints. A synthesis pass then transforms the existing AST before VM evaluation.

Conceptually:

```text
Declarative specification
          │
          ▼
 Handler declarations
          │
          ▼
 Precedence graph
          │
          ▼
 Topological sort
          │
          ▼
 Nested handler expressions
          │
          ▼
 Existing compiler / VM
```

The synthesis pass is therefore a pure AST transformation.

A simplified implementation in pseudocode:

```text
synthesize_topology(body, handlers):
    ordered = topological_sort(handlers.precedence)

    result = body

    for H in ordered:
        result = handle(result, H)

    return result
```

The implementation does not require a new runtime representation of handlers. The generated nodes use the existing handler-expression representation of the target language.

Likewise, the VM continues to perform ordinary handler lookup and evaluation.

The principal implementation advantage is therefore not that handlers become intrinsically cheaper, but that the declarative layer introduces **no additional runtime dispatch mechanism**.

## 11. Evaluation

We validated the system through a Python reference implementation and a Lean 4 mechanical formalization. The Python suite covers the concrete syntax, the synthesis algorithm, and three representative case studies. All tests pass.

### 11.1 Parser Tests

The precedence parser is exercised with 46 unit tests covering explicit `before` relations, numeric priority sugar, mixed specifications, malformed input, duplicate handlers, and round-trip formatting. The tests verify that priority values expand correctly into partial-order constraints and that errors such as undeclared handlers, invalid priorities, and self-before constraints are diagnosed as expected.

### 11.2 Case Studies

Three case studies exercise realistic handler topologies:

1. **HTTP middleware pipeline.** A total order `Auth ≺ Cache ≺ Logger` is parsed and synthesized into the nested `handle` term `handle (handle (handle body with Auth) with Cache) with Logger`.
2. **Event-driven partial order.** A validator must run before both authentication and logging; both must run before metrics. Authentication and logging are incomparable under the partial order, so the compiler is free to order them deterministically. The test confirms that both possible relative orders preserve the declared constraints and that no cycle is introduced.
3. **Cyclic detection.** Two- and three-handler cycles (`A ≺ B ≺ A` and `A ≺ B ≺ C ≺ A`) are rejected, while an acyclic chain `A ≺ B ≺ C` is accepted and ordered correctly.

### 11.3 Property-Based Tests

A randomized harness generates 50 acyclic specifications, 50 cyclic specifications, 50 constraint-respecting term examples, and a set of edge cases. Each trial checks that synthesis produces a nesting consistent with the declared precedence and that cyclic inputs are rejected. The `synthesize` implementation is therefore tested against a much larger space of inputs than the hand-written case studies alone.

### 11.4 Compilation and Runtime Cost

The ordering phase is a standard topological sort and runs in:

```text
O(|H| + |≺|)
```

AST construction adds `O(|H|)` nodes. Because the emitted code is a sequence of the same `handle` nodes the runtime already uses, there is no additional dispatch cost after lowering: the VM evaluates `handle (handle ... body with H₁) with H₂` exactly as it would a manually nested program. The only new work is at compile time.

Empirical measurements were produced by `python/benchmark.py` on a modern Linux laptop. The benchmark uses a linear Kahn topological sort (without the deterministic tie-breaking sort used by the reference Python case studies) to isolate the core `O(|H| + |≺|)` scaling of the synthesis pass. Each handler handles one unique operation, and the precedence relation is a simple chain `H₀ ≺ H₁ ≺ … ≺ Hₙ₋₁`.

| `n` handlers | `m` constraints | toposort (ms) | synthesis (ms) | AST `handle` nodes | cycle detection (ms) |
|-------------:|----------------:|--------------:|---------------:|-------------------:|---------------------:|
| 10           | 9               | 0.015         | 0.004          | 10                 | 0.007                |
| 100          | 99              | 0.056         | 0.012          | 100                | 0.028                |
| 1,000        | 999             | 0.549         | 0.056          | 1,000              | 0.255                |
| 10,000       | 9,999           | 6.593         | 0.716          | 10,000             | 3.713                |

The toposort and cycle-detection times grow linearly with the input size, as expected. AST construction is `O(|H|)` and remains below one millisecond even for 10,000 handlers. Because the emitted term is a plain nested `handle` expression, the VM evaluates it with the same dispatch cost as a manually nested program.

## 12. Relationship to Prior Work

### 12.1 The Arrow Calculus

The arrow calculus of Lindley, Wadler, and Yallop provides the foundational calculus for reasoning about computations with explicit structure.

Our work does not introduce a new arrow calculus. Instead, it uses the existing handler mechanism as the target of a declarative compilation layer.

### 12.2 Lindley's λ_flow

Lindley's λ_flow explored algebraic effects and handlers across idioms, arrows, and monads and provided static effect distinctions.

This work is relevant because it demonstrates that effect structure can be exposed statically.

Our contribution is different: we use a declarative specification to **construct the handler topology itself**.

Thus the relationship can be summarized as:

```text
λ_flow
  │
  │ static effect structure
  ▼
Sanada
  │
  │ formal arrow handlers
  ▼
Declarative synthesis
  │
  │ handler precedence
  ▼
nested handle expressions
```

### 12.3 Algebraic Effects and Handlers

General algebraic-effects research establishes the separation between effect declaration and interpretation.

Our system applies this principle specifically to handler composition: the declarative specification describes how handlers should relate, while the compiler determines the concrete nesting required by the target calculus.

### 12.4 Handler Order and Commutativity

The question of when two handlers can be safely reordered has been studied directly. Yang and Wu (2021), in *Reasoning about effect interaction by fusion*, derive sufficient conditions under which handler composition is insensitive to order, using fold/build fusion and continuation-passing style. Their work focuses on semantic conditions for commutativity; it does not propose a declarative, compile-time precedence language that emits the nesting automatically.

Our contribution is therefore not the observation that handlers can commute, but the combination of (1) a declarative partial-order specification, (2) a compile-time linear-extension synthesis pass, and (3) a machine-checked account of the resulting static topology. The `get`/`log` and two-handler `Dts` examples instantiate existing commutativity ideas in the concrete Sanada setting; the novelty lies in the declarative-to-nested compilation pipeline and its formal correctness.

## 13. Scope and Limitations

The system is intentionally minimal. We do not view these as weaknesses; they delimit the current contribution and point to §14.

Precedence must be declared or derived from a separate static policy; we do not infer it from arbitrary program behavior. A partial order may admit multiple valid linear extensions, and a complete semantic account of when two such extensions are observationally equivalent is only solved here for the two-handler, clause-disjoint case (§14.1). The implementation does not optimize the generated `handle` composition; the output is ordinary nested `handle` terms for the existing runtime.

The Sanada bridge in §7 is a categorical certificate for the two-handler commutativity theorem, not a full arrow-calculus interpretation of every `Dts` command.

## 14. Future Work

The minimal system described here forms a self-contained foundation: it defines the declarative-to-nested lowering, proves its correctness, and provides a practical implementation path. The extensions below are natural next steps that build directly on this foundation.

### 14.1 Semantic Commutativity

An important question is when two handlers can safely be reordered.

We provide a partial answer, formalized in `Commutativity.lean`. Two handlers are **clause-disjoint** when no operation name is handled by both:

```text
disjointClauses(H₁, H₂) := ∀ op. ¬(H₁ handles op ∧ H₂ handles op)
```

**Theorem 4 — Two-Handler Commutativity.** For a static body `P`, if `H₁` and `H₂` are clause-disjoint, then:

```text
eval(synthesize(P, [H₁, H₂])) = eval(synthesize(P, [H₂, H₁]))
```

That is, the trace is identical regardless of which disjoint handler is innermost.

The proof proceeds by showing that swapping two disjoint adjacent handlers in the handler context does not change which handler first catches any operation (`firstHandler_swap`), and then lifting this to all static command forms by induction (`evalWith_swap`).

A counterexample demonstrates that the disjointness condition is necessary: when two handlers both handle the same operation, the innermost handler catches it, so reordering changes the trace.

The same two-handler equivalence has a categorical certificate in the Sanada formalization. `SanadaBridge.lean` shows that `ProfunctorCommute2` for the two-operation promonad model implies the concrete `Command.Equiv` equality above (`Commutativity_from_ProfunctorCommute2`). In other words, the syntactic trace-equality theorem is grounded in the profunctor-level commutation of the handlers' right actions.

The two-handler case is fully proved. The `eval_synthesize` and `synthesize_adjacent_swap` theorems in `Commutativity.lean` extend this to a single adjacent swap of two disjoint handlers inside an arbitrary surrounding list. The full `List.Perm` induction over arbitrary permutations of a pairwise-disjoint handler list is the remaining step.

### 14.2 Inferred Precedence

Some precedence constraints could potentially be inferred from operation signatures or handler dependencies.

For example, if a handler invokes an operation that another handler must intercept, the compiler could derive a necessary nesting relationship.

### 14.3 Optimization

A synthesis pass could eliminate redundant handlers, merge compatible handlers, or specialize handler nesting when their operation sets are statically known.

### 14.4 Beyond Formalization

The Lean formalization (§7) establishes both structural and semantic correctness of synthesis: well-formedness, precedence preservation, staticity, completeness, existence of linear extensions, semantic equivalence between synthesized and manually nested terms (§7.2), and two-handler commutativity for disjoint handlers (§14.1). Further formalization work could verify:

1. The general commutativity conjecture: for a static body, if all handlers in a list are pairwise clause-disjoint, then any permutation of that list produces the same trace. The adjacent-swap step (`synthesize_adjacent_swap`) and the `eval_synthesize` connection are in place; the remaining work is the `List.Perm` induction.
2. Semantic equivalence under a richer operational semantics that models continuation capture and resumption, beyond the trace semantics currently formalized.
3. A full Sanada arrow-calculus interpretation connecting the abstract strong-promonad model to every `Dts` command, beyond the two-handler fragment already bridged in `SanadaBridge.lean`.

### 14.5 Beyond Total Handler Order

Although the final arrow representation is linear, future work could investigate richer declarative descriptions that compile into multiple statically selected handler configurations. For example, a specification might describe two alternative handler orderings guarded by a compile-time condition (e.g. debug vs production mode). The compiler would then generate two separate nested `handle` expressions and select between them using permitted term-level branching (`if M then N₁ else N₂` where `N₁` and `N₂` are terms, not commands). This stays within the arrow calculus because the selection is static or term-level — it does not introduce runtime branching on effectful commands. The key insight is that multiple static topologies can coexist as long as the choice between them does not depend on operation results.

## 15. Conclusion

We presented a declarative system for synthesizing handler topology in an arrow calculus with algebraic effects and handlers.

The key idea is to separate **handler specification** from **handler syntax**. A programmer declares a set of handlers and a precedence relation. The compiler computes a linear extension of that relation and lowers it to the nested `handle` expressions required by the underlying calculus.

This transformation is fundamentally static. It does not introduce runtime branching over effectful commands and therefore does not require an extension of the arrow semantic model. The synthesis problem is consequently reduced to a well-defined compile-time ordering problem. Its structural and trace-level properties have been mechanically verified in Lean 4 (§7), covering well-formedness, precedence preservation, staticity, completeness, trace equivalence, and two-handler commutativity for disjoint handlers.

The approach also provides a minimal implementation path. In a language with existing handler-expression AST nodes, the declarative system can be implemented as an AST-to-AST transformation producing those nodes. The existing runtime remains responsible for ordinary handler evaluation.

The principal result is therefore not a new runtime effect mechanism, but a new **declarative layer for constructing an existing arrow-effect mechanism**. The boundary is precise:

```text
static handler topology
        + synthesizable

runtime effect-dependent command topology
        - not introduced by this system
```

This boundary turns a limitation of arrow effects into a useful design constraint. Because the generated handler structure is linear and statically known, its synthesis is simple, deterministic, and amenable to formal verification.

The resulting system provides a small example of a broader principle: when a programming language exposes a structurally constrained semantic representation, a declarative layer can synthesize that representation without changing the underlying runtime. In the present case, Sanada's explicit handler topology becomes not merely a syntactic requirement, but the target of a compile-time synthesis process.

## References

1. Sanada, T. (2024). *Algebraic effects and handlers for arrows.* Journal
   of Functional Programming, 34. doi:10.1017/S0956796824000066
2. Sanada, T. (2024). *Algebraic effects and handlers for arrows.* PhD
   thesis, Kyoto University.
   https://www.kurims.kyoto-u.ac.jp/~tsanada/papers/phdthesis.pdf
3. Lindley, S. (2014). *Algebraic effects and effect handlers for idioms
   and arrows.* In Proceedings of the 19th International Conference on
   Functional Programming (ICFP). doi:10.1145/2633628.2633636
4. Lindley, S., Wadler, P., and Yallop, J. (2010). *The arrow calculus.*
   Journal of Functional Programming, 20(1), pp. 51–87.
5. Plotkin, G. and Pretnar, M. (2013). *Handling algebraic effects.*
   Logical Methods in Computer Science, 9(4).
6. Hughes, J. (2000). *Generalising monads to arrows.* Science of
   Computer Programming, 37(1–3), pp. 67–111.
