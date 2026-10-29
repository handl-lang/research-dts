import Mathlib.Tactic
import Dts.Basic
import Dts.Precedence
import Dts.Commutativity
import Dts.Synthesis
import Dts.Semantics
import ListDigraph.Basic

namespace TopologySynthesis

open ListDigraph

/-! # Main theorem: soundness of the inference algorithm

The topological inference algorithm produces a linear extension of the
precedence relation.  We show that any such ordering is semantically
equivalent to the original valid ordering, provided the handlers are
pairwise clause-disjoint.
-/

/-- **Main theorem**: any two linear extensions of the same acyclic precedence
    over a pairwise-disjoint set of handlers produce semantically equivalent
    synthesized programs.

    In other words, every ordering produced by the topological inference
    algorithm is trace-equivalent to the original valid ordering. -/
theorem inference_soundness (body : Command) (prec : Precedence) (handlers : List Handler)
    (valid inferred : List Handler)
    (h_valid_perm : List.Perm valid handlers)
    (h_inferred_perm : List.Perm inferred handlers)
    (_h_valid_linext : ∀ a b, a ∈ handlers → b ∈ handlers → prec a b = true → AppearsBefore a b valid)
    (_h_inferred_linext : ∀ a b, a ∈ handlers → b ∈ handlers → prec a b = true → AppearsBefore a b inferred)
    (_h_po : Precedence.isPartialOrder prec)
    (h_disjoint : ∀ h1 h2, h1 ∈ handlers → h2 ∈ handlers → h1 ≠ h2 → disjointClauses h1 h2)
    (_hs : body.isStatic = true) :
    Command.Equiv (synthesize body valid) (synthesize body inferred) := by
  have h_perm : List.Perm valid inferred :=
    h_valid_perm.trans h_inferred_perm.symm
  have h_pairwise : pairwiseDisjoint valid := by
    intro h1 h2 h1v h2v hne
    have h1h : h1 ∈ handlers := (perm_mem h_valid_perm h1).mp h1v
    have h2h : h2 ∈ handlers := (perm_mem h_valid_perm h2).mp h2v
    exact h_disjoint h1 h2 h1h h2h hne
  exact synthesize_perm_equiv body valid inferred h_perm h_pairwise

end TopologySynthesis
