# Reference

## Lean 4 formalization (`lean/`)

A Lake project (`lakefile.toml`, `lean-toolchain`).

| module | contents |
|---|---|
| `Dts/Basic.lean` | handlers, bodies, the core terms |
| `Dts/Precedence.lean` | the precedence relation and its well-formedness |
| `Dts/Synthesis.lean` | `synthesize`: precedence → nested `handle` |
| `Dts/TopoSort.lean` | the topological sort and its properties |
| `Dts/Semantics.lean` | operational semantics of nested handlers |
| `Dts/SemanticEquivalence.lean` | synthesis preserves semantics |
| `Dts/Commutativity.lean` | when unrelated handlers may be reordered |
| `ListDigraph/Basic.lean`, `ListDigraph/TopSort.lean` | the digraph + topological sort the proof is built on |

## Python reference implementation (`python/`)

| module | contents |
|---|---|
| `dts.precedence_parser` | `parse_spec`, `format_spec`, `Spec`, `Handler`, `ParseError` |
| `dts.case_studies.http_middleware` | `synthesize(body, ordered)` over an HTTP middleware precedence |
| `dts.case_studies.event_driven_partial_order` | the same over an event-driven partial order |
| `dts.case_studies.cyclic_detection` | a spec with a cycle: parse + reject with a diagnostic |
| `dts.eval.property_tests` | generated specs asserted against the synthesis |

`synthesize` lives with each case study on purpose: the interesting part is the
*linear extension* the parser derives, and each study exercises a different
precedence shape.

## Paper

| target | output |
|---|---|
| `make pdf` | `paper/paper.pdf` (pandoc, defaults in `pandoc.yaml`) |
| `make tex` | `paper/main.tex` |
| `make clean` | removes generated artifacts |

Citation metadata is in `CITATION.cff`.

## Build and test

```bash
# Lean
cd lean && lake build

# Python
cd python && pytest

# Paper
cd paper && make pdf
```
