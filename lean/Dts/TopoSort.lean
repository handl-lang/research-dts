import Mathlib.Tactic
import Dts.Basic
import Dts.Precedence
import ListDigraph.Basic
import ListDigraph.TopSort

namespace TopologySynthesis

open ListDigraph

/-- **Topological Sort Soundness**: For any finite set of handlers with
    an irreflexive and transitive precedence relation, there exists a
    list (linear extension) such that every precedence constraint is
    realized as `AppearsBefore`. -/
theorem exists_linear_extension
    (handlers : List Handler) (prec : Precedence)
    (h_irrefl : Precedence.irreflexive prec)
    (h_tr : Precedence.transitive prec) :
    ∃ ordered : List Handler,
      (∀ h ∈ handlers, h ∈ ordered) ∧
      (∀ a b : Handler, a ∈ handlers → b ∈ handlers →
        prec a b = true → AppearsBefore a b ordered) := by
  let g := Graph.mk handlers prec
  have h_acyclic : g.acyclic :=
    fun v => partialOrder_acyclic prec ⟨h_irrefl, h_tr⟩ v
  have h_eq : ∀ a b : Handler, g.precedence a b ↔ prec a b = true := by
    intro a b
    constructor
    · intro h
      exact reachable_implies_edge prec h_tr a b h
    · intro h
      exact Relation.TransGen.single h
  obtain ⟨ordered, h_contain, h_prec⟩ := ListDigraph.exists_topological_sort g h_acyclic
  refine ⟨ordered, h_contain, fun a b a_in b_in h_ab => h_prec a b a_in b_in ((h_eq a b).mpr h_ab)⟩

end TopologySynthesis
