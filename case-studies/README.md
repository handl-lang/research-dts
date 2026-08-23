# Case Studies — Declarative Handler Topology Synthesis

Three runnable Python case studies demonstrating the paper's `synthesize` idea.

## Case Study 1: HTTP Middleware Pipeline (total order)

`http_middleware.py` — Auth → Cache → Logger with a total precedence order.

```sh
python3 case-studies/http_middleware.py
```

Shows: declarative spec, topological sort, synthesis of nested `handle` term,
and a tiny execution wrapping an HTTP request.

## Case Study 2: Event-Driven Handler Chain (partial order)

`event_driven_partial_order.py` — Validator, Auth, Logger, Metrics with a
*partial* order (Auth and Logger are incomparable).

```sh
python3 case-studies/event_driven_partial_order.py
```

Shows: incomparable pair detection, two valid linear extensions for the same
partial order, and execution of both synthesized nestings.

## Case Study 3: Cyclic Precedence Detection

`cyclic_detection.py` — Three scenarios: simple cycle (A < B < A), longer
cycle (A < B < C < A), and a valid acyclic spec for contrast.

```sh
python3 case-studies/cyclic_detection.py
```

Shows: cycle detection during topological sort, DFS-based cycle path
identification, and user-friendly error diagnostics with fix suggestions.

---

None of these scripts modify files in `Dts/` or `PAPER.md`.
