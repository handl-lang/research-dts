# TODO — research-dts

## Working compiler pass


## Case studies


## Evaluation infrastructure


## Benchmarks

- [ ] Measure synthesis time vs. handler count (n) and constraint count (m) — verify O(n + m)
- [ ] Compare compile time with and without synthesis pass (overhead should be negligible)
- [ ] Test with realistic handler counts (10, 50, 100, 500 handlers)
- [ ] Benchmark topological sort separately from AST construction

## Publication

- [ ] Add arXiv/DOI badge and link to README once published

## Handler commutativity (Sanada/DTS bridge) — open next steps

- [ ] Formalize enough of Sanada's free strong promonad `A_Σ^*` and its `S`-parameterized interpretation `[[A → B]]_S = A_Σ^*([[A]]_S × S, [[B]]_S)` to represent a nontrivial operation-rewriting handler.
- [ ] Define handler-induced `A_Σ^*`-algebra actions from clauses `Q_op` (`[[Q^op]]_S : A_Σ^*([[δ]] × S, [[D]]) → A_Σ^*([[γ]] × S, [[D]])`).
- [ ] Instantiate the abstract `ProfunctorCommute2` diamond theorem with the concrete `get`/`log` handlers and prove disjoint operation clauses induce safe handler reordering.
- [ ] Revisit `EffectBridge.lean` once the parameterized algebra infrastructure is in place.

## Next steps surfaced from the 2026-10-30 formalization pass

- [ ] Prove the full `List.Perm` generalization: for a static body and any permutation of a pairwise-disjoint handler list, `eval (synthesize body ordered) = eval (synthesize body ordered')`. The adjacent-swap step (`synthesize_adjacent_swap`) and the `eval_synthesize` bridge are already in place.
- [ ] Complete the full Sanada arrow-calculus interpretation for every `Dts` command, beyond the two-handler bridge and the concrete `get`/`log` fragment.

## Repo state (from 2026-10-29 cleanup)

- [ ] Review `sanada-bridge` branch: holds rescued uncommitted work (EvalRel, EffectInterface, InferenceSoundness, extended Commutativity/Semantics diffs) not on `main` — integrate or discard
- [ ] Repo is archived on GitHub — unarchive before any future push
