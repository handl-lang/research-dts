# Declarative Topology Synthesis (DTS)

Programmers of effect handlers know which handler must wrap which — yet they still
write the nesting by hand. DTS makes that declaration: you supply a **precedence
relation** over handlers, and the compiler synthesizes the nested `handle`
structure at compile time.

```
-- given: Auth before Cache before Logging
synthesize body [Auth, Cache, Logging]

-- synthesizes
handle (handle (handle body Auth) Cache) Logging
```

## What is in this repo

| artifact | where | what it is |
|---|---|---|
| Paper | [`paper/`](https://github.com/handl-lang/research-dts/blob/main/paper/PAPER.md) | the write-up ([PDF](https://github.com/handl-lang/research-dts/blob/main/paper/paper.pdf)) |
| Formalization | `lean/` | Lean 4: precedence, synthesis, and the topological-sort soundness proof |
| Reference implementation | `python/` | the synthesis pipeline, case studies and property tests |

## Start here

- **Reference** — [Lean modules, Python API, paper targets](/research-dts/reference/)
- **How-to** — [build the proof, run the pipeline, rebuild the paper](/research-dts/how-to/)
- **Explanation** — [why a static ordering is enough](/research-dts/explanation/)

## The claim in one paragraph

In an arrow-effect language the operations of a handler are **linear and
sequential**, so the topology can be decided statically: synthesis is a
compile-time transformation, not a runtime dispatch mechanism. The formalization
pins down when that transformation is sound — a linear extension of the
declared precedence, with deterministic tie-breaking — and the Python
implementation exists to keep the formalization honest against concrete
programs.

Decision records and the task log live on the `project` branch
(`project/TODO.md`).
