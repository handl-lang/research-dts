# DTS — Implementation & Evaluation Tasks

## Working compiler pass

- [x] Implement `synthesize_topology` as an actual AST-to-AST pass in a target language
- [x] Handle precedence parsing (both explicit `before` relations and numeric priority sugar)
- [x] Implement cycle detection with user-friendly error messages
- [x] Implement deterministic tie-breaking for unrelated handlers (declaration order)
- [x] Integration test: declarative input → verify generated AST nesting matches expected linear extension

## Case studies

- [x] Case study 1: HTTP middleware pipeline (auth → cache → logging) — show declarative vs. manual nesting
- [x] Case study 2: Event-driven handler chain with partial order (some handlers unordered)
- [x] Case study 3: Cyclic precedence detection — verify compiler rejects with clear diagnostics
- [x] Case study 4: Behavioral equivalence — run synthesized vs. manually nested programs, confirm identical output
- [x] Document each case study with input spec, expected output, and verification method

## Evaluation infrastructure

- [x] Build a test harness that generates random acyclic precedence graphs and verifies synthesis correctness
- [x] Build a test harness that generates cyclic graphs and verifies rejection
- [x] Property-based test: for any acyclic spec, synthesized nesting respects all precedence constraints

## Benchmarks

- [ ] Measure synthesis time vs. handler count (n) and constraint count (m) — verify O(n + m)
- [ ] Compare compile time with and without synthesis pass (overhead should be negligible)
- [ ] Test with realistic handler counts (10, 50, 100, 500 handlers)
- [ ] Benchmark topological sort separately from AST construction
