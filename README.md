# Declarative Topology Synthesis (DTS)

Lean 4 formalization of correctness proofs for declarative handler topology synthesis in Sanada's arrow calculus with algebraic effects.

## The problem

In Sanada's arrow calculus, **handler topology** — which handler wraps which — must be written explicitly by the programmer:

```
handle (handle (handle body H1) H2) H3
```

This is tedious and error-prone. The programmer knows *what* precedence they want (e.g., "H1 must be inside H2"), but has to manually figure out the correct nesting.

## The idea

**Declarative topology synthesis**: the programmer specifies a *precedence relation* (a partial order on handlers), and the compiler automatically generates the correct nesting via a linear extension — a sorted list that respects all constraints.

```
-- programmer writes:
synthesize body [H1, H2, H3]  -- linear extension of the precedence

-- compiler produces:
handle (handle (handle body H1) H2) H3
```

Arrow effects impose a **linear (sequence) structure** on operations — no runtime branching on commands — so a static linear ordering is sufficient. This is a compile-time problem, not a runtime dispatch problem.

## What the Lean proofs verify

The formalization in `Dts/` proves that the synthesis algorithm is correct:

| Theorem | What it proves | Why it matters |
|---|---|---|
| `irreflexive_transitive_implies_asymmetric` | Asymmetry is derivable from irreflexivity + transitivity | The precedence relation can't have both `a ≺ b` and `b ≺ a` |
| `partialOrder_acyclic` | Partial orders are acyclic | The precedence relation can't have cycles — otherwise no valid nesting exists |
| `synthesize_well_formed` | Synthesis preserves well-formedness (non-empty handler clauses) | The output isn't garbage — every handler actually handles something |
| `synthesize_preserves_precedence` | If `hi` appears before `hj` in the list, `hi` is nested inside `hj` | **Core theorem**: the synthesized nesting respects the ordering |
| `synthesize_static_topology` | Synthesis never introduces runtime branching (`cond`) | The output is still a valid arrow-effect term — no dynamic dispatch sneaks in |
| `synthesize_completeness` | If the list is a linear extension of `prec`, every precedence constraint is realized | **Preservation + completeness = full correctness**: the synthesis does exactly what the precedence specification asks |
| `exists_linear_extension` | For any finite acyclic precedence relation, a linear extension exists | **Topological sort soundness**: the compiler can always find a valid ordering |
| `synthesize_eq_manuallyNested` | Synthesis produces the same term as explicit manual nesting | Syntactic equivalence: the fold is just sugar for manual nesting |
| `synthesize_equiv_manuallyNested` | Synthesized and manually nested programs have identical traces | **Semantic equivalence**: behavior is preserved, not just structure |
| `synthesize_commutative_two` | Two clause-disjoint handlers can be swapped without changing the trace | **Commutativity**: unordered handlers with disjoint operations are safe to reorder |

## Relevance to Language Design

Any language with an AST that includes explicit handler nesting and a runtime that executes that nesting can benefit from this research. The DTS research shows that:

1. **A synthesis pass is possible** — it's a compile-time fold over a sorted handler list
2. **It's provably correct** — the Lean proofs guarantee precedence preservation, well-formedness, staticity, semantic equivalence, and commutativity for disjoint handlers
3. **It doesn't change the runtime** — the runtime still sees explicit `handle` nesting; only the frontend changes

The paper at `PAPER.md` proposes this as a language design for arrow-effect languages with explicit handler nesting. The Lean file is the machine-verified evidence that the design is sound.

## Utility

- **For the language designer**: confidence that declarative handler ordering is safe to add
- **For the implementer**: the `synthesize` function is a simple fold that wraps each handler around the body in order
- **For the formalist**: the proofs are machine-checked by Lean 4 (`lake build` passes), not just pen-and-paper sketches

## Build

```sh
lake build
```

Requires Lean 4 (toolchain specified in `lean-toolchain`). Mathlib is used for tactic utilities only.

## Case study

A runnable HTTP middleware example is in `case_study/`:

```sh
python3 case_study/http_middleware.py
```

It demonstrates the full pipeline: declarative spec (Auth → Cache → Logger) → topological sort → synthesized nesting → execution.