# TODO — research-dts

## Working compiler pass


## Case studies


## Evaluation infrastructure


## Benchmarks

- [ ] T-001 Measure synthesis time vs. handler count (n) and constraint count (m) — verify O(n + m)
- [ ] T-002 Compare compile time with and without synthesis pass (overhead should be negligible)
- [ ] T-003 Test with realistic handler counts (10, 50, 100, 500 handlers)
- [ ] T-004 Benchmark topological sort separately from AST construction

## Publication

- [ ] T-005 Add arXiv/DOI badge and link to README once published

## Handler commutativity (Sanada/DTS bridge) — open next steps

- [ ] T-006 Formalize enough of Sanada free strong promonad and its S-parameterized interpretation to represent a nontrivial operation-rewriting handler
- [ ] T-007 Define handler-induced promonad-algebra actions from operation clauses for the Sanada/DTS bridge
- [ ] T-008 Instantiate the abstract ProfunctorCommute2 diamond theorem with concrete get/log handlers and prove disjoint operation clauses induce safe handler reordering
- [ ] T-009 Revisit EffectBridge.lean once the parameterized algebra infrastructure is in place.

## Next steps surfaced from the 2026-10-30 formalization pass

- [ ] T-010 Prove the full List.Perm generalization for static body and any permutation of pairwise-disjoint handler list (adjacent-swap step and eval_synthesize bridge already in place)
- [ ] T-011 Complete the full Sanada arrow-calculus interpretation for every Dts command beyond the two-handler bridge and concrete get/log fragment

## Repo state (from 2026-10-29 cleanup)

- [ ] T-012 Review sanada-bridge branch: rescued uncommitted work (EvalRel, EffectInterface, InferenceSoundness, Commutativity/Semantics diffs) not on main — integrate or discard
- [ ] T-013 Repo is archived on GitHub — unarchive before any future push
