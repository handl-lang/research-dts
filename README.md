# Declarative Topology Synthesis (DTS)

[![Lean CI](https://github.com/luisfuturist/dts/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/luisfuturist/dts/actions/workflows/lean_action_ci.yml)
[![Python CI](https://github.com/luisfuturist/dts/actions/workflows/python_ci.yml/badge.svg)](https://github.com/luisfuturist/dts/actions/workflows/python_ci.yml)
[![Paper CI](https://github.com/luisfuturist/dts/actions/workflows/paper_ci.yml/badge.svg)](https://github.com/luisfuturist/dts/actions/workflows/paper_ci.yml)

Research project on **declarative handler topology synthesis** for functional programming languages with algebraic effects and handlers, with a Sanada-style strong-promonad formalization of arrow-handler commutativity. The central goal is to let programmers specify *which handler wraps which* as a precedence relation, and have the compiler synthesize the correct nested `handle` structure statically.

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

### `paper/`

The research paper, "Declarative Handler Topology Synthesis for Arrow Effects." It presents:

- the declarative handler model and precedence relation;
- the synthesis algorithm as topological sort + AST fold;
- correctness properties (well-formedness, precedence preservation, staticity, semantic equivalence, commutativity for disjoint handlers);
- an implementation strategy for arrow-effect languages that reuses existing handler AST nodes and runtimes.

The PDF is available as [`paper/paper.pdf`](paper/paper.pdf) and the Markdown source is [`paper/PAPER.md`](paper/PAPER.md).

Build:

```sh
cd paper
quarto render PAPER.md --to pdf
mv PAPER.pdf paper.pdf
```

### `lean/`

A Lean 4 formalization of the paper's correctness claims. The core structural and trace-level proofs are machine-checked. The Sanada promonad bridge is formalized for the two-handler fragment; the current build status is recorded in `paper/PAPER.md` §7.3.

The topological sort is implemented in a self-hosted `ListDigraph` package that provides a finite, executable, `List`-returning `topSort` correctness proof, decoupled from `Mathlib.Combinatorics.Digraph`.

The formalization also includes a Sanada-style strong-promonad model. It builds from an abstract profunctor/promonad layer up to a concrete two-operation parameterized model, and ends with `SanadaBridge.lean`, which derives the concrete two-handler `Dts.Commutativity` theorem from a categorical `ProfunctorCommute2` certificate.

Relevant theorems include:

- `synthesize_well_formed` — synthesis preserves well-formedness;
- `synthesize_preserves_precedence` — the generated nesting respects the declared precedence;
- `synthesize_static_topology` — synthesis introduces no runtime `cond` branching;
- `synthesize_completeness` — every precedence constraint is realized;
- `exists_linear_extension` — a topological sort is always available for finite acyclic relations;
- `synthesize_equiv_manuallyNested` — synthesized and manually nested programs have identical traces;
- `synthesize_commutative_two` — disjoint handlers can be reordered without changing behavior;
- `Commutativity_from_ProfunctorCommute2` — the concrete two-handler bridge from the Sanada promonad certificate is formalized (build status in `paper/PAPER.md` §7.3).

Build:

```sh
cd lean
lake build
```

### `python/`

Python tooling and case studies for the research. Includes:

- a precedence parser and cycle-detection harness;
- a reference AST-to-AST synthesis pass;
- case studies such as HTTP middleware pipelines and event-driven handler chains;
- executable parser tests.

Build:

```sh
cd python
uv run python tests/test_precedence_parser.py
uv run python tests/test_synthesis.py
uv run python benchmark.py
```

### `project/`

Implementation and evaluation tracking.

## Relevance to functional programming

Any functional language with an AST that includes explicit handler nesting and a runtime that executes that nesting can adopt this design. DTS shows that:

1. **A synthesis pass is possible** — it is a compile-time fold over a topologically sorted handler list.
2. **It is provably correct** — the paper argues the properties, and the Lean formalization verifies them mechanically.
3. **It does not change the runtime** — the runtime still sees ordinary nested `handle` expressions; only the frontend grows a declarative layer.

## License and Citation

This project is released under the [MIT License](LICENSE). If you use this software or the accompanying Lean formalization, please cite it using the information in [CITATION.cff](CITATION.cff).

## Further reading

- `paper/PAPER.md` — full paper source.
- `paper/paper.pdf` — compiled PDF.
- `lean/Dts/` — formalized definitions and proofs.
- `lean/Dts/SanadaBridge.lean` — categorical bridge from profunctor commutativity to concrete handler equivalence.
- `lean/ListDigraph/` — self-hosted list-based topological sort package.
- `python/tests/` — executable tests and case studies.
- `project/TODO.md` — implementation and evaluation task list.
