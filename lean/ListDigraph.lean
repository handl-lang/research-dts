import ListDigraph.Basic
import ListDigraph.TopSort

/-! # ListDigraph

This package provides a finite, executable, `List`-based directed graph
(`ListDigraph.Graph`) and a constructive proof that every acyclic such
digraph has a `List` topological sort (`ListDigraph.exists_topological_sort`).

`Mathlib.Combinatorics.Digraph` gives a general `Adj : V → V → Prop` digraph
with lattice/order infrastructure, but it does not currently provide
reachability, acyclicity, or a `List`-returning topological sort. `ListDigraph`
fills that specific gap for the DTS use case. -/
