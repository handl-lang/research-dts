# Declarative Topology Synthesis (DTS)

Research project on **declarative handler topology synthesis** for functional programming languages with algebraic effects and handlers. The central goal is to let programmers specify *which handler wraps which* as a precedence relation, and have the compiler synthesize the correct nested `handle` structure statically.

This is a practical language-design problem: in effect systems with explicit handler nesting, the programmer often knows the desired precedence (e.g., "Auth must be inside Cache") but must still write the nesting by hand. DTS proposes a compile-time synthesis pass that converts a declarative specification into a linearly nested handler expression.

The project combines a research paper, a machine-checked formalization, and reference tooling/case studies.

## The problem

In effect-handler languages that use nested `handle` constructs, the programmer writes the topology explicitly:

```
handle (handle (handle body H1) H2) H3
```

This is tedious and error-prone. The programmer knows the desired precedence, but must manually work out the correct nesting order.

## The idea

**Declarative topology synthesis**: the programmer supplies a precedence relation (a partial order over handlers), and the compiler computes a linear extension — a valid ordering — and folds it into the corresponding nested `handle` term.

```
-- programmer writes:
synthesize body [H1, H2, H3]  -- a linear extension of the precedence

-- compiler produces:
handle (handle (handle body H1) H2) H3
```

Because arrow effects impose a linear, sequential structure on operations, a static ordering is sufficient. Synthesis is a compile-time transformation, not a runtime dispatch mechanism.

## Project structure

This repository contains three complementary artifacts:

### `PAPER.md`

The research paper, "Declarative Handler Topology Synthesis for Arrow Effects." It presents:

- the declarative handler model and precedence relation;
- the synthesis algorithm as topological sort + AST fold;
- correctness properties (well-formedness, precedence preservation, staticity, semantic equivalence, commutativity for disjoint handlers);
- an implementation strategy for arrow-effect languages that reuses existing handler AST nodes and runtimes.

### `lean/`

A Lean 4 formalization of the paper's correctness claims. The proofs are machine-checked (the project builds with `lake build` and contains no admitted proofs).

Relevant theorems include:

- `synthesize_well_formed` — synthesis preserves well-formedness;
- `synthesize_preserves_precedence` — the generated nesting respects the declared precedence;
- `synthesize_static_topology` — synthesis introduces no runtime `cond` branching;
- `synthesize_completeness` — every precedence constraint is realized;
- `exists_linear_extension` — a topological sort is always available for finite acyclic relations;
- `synthesize_equiv_manuallyNested` — synthesized and manually nested programs have identical traces;
- `synthesize_commutative_two` — disjoint handlers can be reordered without changing behavior.

Build:

```sh
cd lean
lake build
```

### `python/`

Python tooling and case studies for the research. Includes:

- a precedence parser and cycle-detection harness;
- a working AST-to-AST synthesis pass;
- case studies such as HTTP middleware pipelines and event-driven handler chains;
- property-based and integration tests.

Build:

```sh
cd python
uv run python tests/test_precedence_parser.py
```

### `project/`

Implementation and evaluation tracking.

## Relevance to functional programming

Any functional language with an AST that includes explicit handler nesting and a runtime that executes that nesting can adopt this design. DTS shows that:

1. **A synthesis pass is possible** — it is a compile-time fold over a topologically sorted handler list.
2. **It is provably correct** — the paper argues the properties, and the Lean formalization verifies them mechanically.
3. **It does not change the runtime** — the runtime still sees ordinary nested `handle` expressions; only the frontend grows a declarative layer.

## Further reading

- `PAPER.md` — full paper.
- `lean/Dts/` — formalized definitions and proofs.
- `python/tests/` — executable tests and case studies.
- `project/TODO.md` — implementation and evaluation task list.
