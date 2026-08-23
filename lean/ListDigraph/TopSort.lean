import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.RelClasses
import ListDigraph.Basic

set_option linter.style.haveILetI false

namespace ListDigraph

open Graph

variable {V : Type}

/-- Helper: strong induction on list length. -/
theorem list_strong_induction
    (P : List V → Prop)
    (h_ind : ∀ s : List V, (∀ t : List V, t.length < s.length → P t) → P s) :
    ∀ s : List V, P s := by
  intro s
  have h : ∀ n, ∀ t, t.length = n → P t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht
      apply h_ind
      intro u hu
      exact ih u.length (by omega) u rfl
  exact h s.length s rfl

variable [DecidableEq V]

-- Section 4: Topological sort soundness

/-- Filtering out an element that is in the list makes it shorter. -/
theorem filter_length_lt_of_mem (a : V) (l : List V) (h : a ∈ l) :
    (List.filter (· ≠ a) l).length < l.length := by
  conv_rhs => rw [List.length_eq_length_filter_add ((· ≠ a))]
  have hpos : 0 < (List.filter (! (· ≠ a) ·) l).length := by
    rw [List.length_pos_iff_ne_nil]
    apply List.ne_nil_of_mem
    exact List.mem_filter_of_mem h (by simp)
  exact Nat.lt_add_of_pos_right hpos

/-- For any non-empty finite list of vertices with an acyclic precedence relation,
    there exists a minimal element. -/
theorem exists_minimal
    (g : Graph V) (s : List V)
    (h_acyclic : g.acyclic)
    (h_nonempty : s ≠ []) :
    ∃ v : V, g.IsMinimal v s := by
  let S : Finset V := s.toFinset
  have hS_ne : (S : Set V).Nonempty := by
    have hpos : 0 < s.length := List.length_pos_of_ne_nil h_nonempty
    use s.get ⟨0, hpos⟩
    exact List.mem_toFinset.2 (List.get_mem s ⟨0, hpos⟩)
  letI : IsStrictOrder V g.precedence :=
    { irrefl := h_acyclic, trans := fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2 }
  letI : PartialOrder V := partialOrderOfSO g.precedence
  have hS_wf : (S : Set V).WellFoundedOn (· < ·) :=
    S.finite_toSet.wellFoundedOn
  obtain ⟨v, hv⟩ := Set.WellFoundedOn.exists_minimal hS_wf hS_ne
  use v
  constructor
  · simpa [S] using hv.1
  · intro u u_in huv
    have hu_in_S : u ∈ (S : Set V) := by simpa [S] using u_in
    have hle' := hv.2 hu_in_S (Or.inr huv)
    rcases hle' with (heq | hvu)
    · -- v = u: the edge u -> v becomes a self-loop, contradicting acyclicity
      have h_eq : u = v := heq.symm
      have hvv : g.precedence v v := by rwa [h_eq] at huv
      exact (h_acyclic v) hvv
    · -- v -> u and u -> v form a cycle, contradicting acyclicity
      have hcycle : g.precedence v v := Relation.TransGen.trans hvu huv
      exact (h_acyclic v) hcycle

/-- **Topological sort soundness**: For any finite acyclic digraph there exists a
    list `order` such that every vertex appears in it and every precedence edge
    `u → v` is realized as `AppearsBefore u v order`. -/
theorem exists_topological_sort
    (g : Graph V)
    (h_acyclic : g.acyclic) :
    ∃ order : List V,
      (∀ v, v ∈ g.vertices → v ∈ order) ∧
      (∀ a b, a ∈ g.vertices → b ∈ g.vertices →
        g.precedence a b → AppearsBefore a b order) := by
  induction g.vertices using list_strong_induction with
  | h_ind handlers ih =>
    cases handlers with
    | nil =>
      exact ⟨[], ⟨fun _ h => by simp at h, fun _ _ a_in _ _ => by simp at a_in⟩⟩
    | cons h rest =>
      have full_nonempty : (h :: rest) ≠ [] := by simp
      obtain ⟨hmin, hmin_min⟩ := exists_minimal g (h :: rest) h_acyclic full_nonempty
      set remaining := List.filter (· ≠ hmin) (h :: rest)
      have remaining_shorter : remaining.length < (h :: rest).length :=
        filter_length_lt_of_mem _ _ hmin_min.1
      obtain ⟨ordered_rest, ih_contain, ih_prec⟩ := ih remaining remaining_shorter
      have mem_remaining_iff (h' : V) : h' ∈ remaining ↔ h' ∈ (h :: rest) ∧ h' ≠ hmin := by
        show h' ∈ List.filter (· ≠ hmin) (h :: rest) ↔ _
        simp [List.mem_filter, and_comm]
      refine ⟨hmin :: ordered_rest, ?_⟩
      constructor
      · -- containment: every handler is in hmin :: ordered_rest
        intro h0 h0_in
        by_cases h0_eq : h0 = hmin
        · subst h0_eq; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih_contain h0
            ((mem_remaining_iff h0).mpr ⟨h0_in, h0_eq⟩))
      · -- precedence preservation
        intro a b a_in b_in h_ab
        by_cases a_eq : a = hmin
        · -- a = hmin: b ≠ hmin (acyclicity), b ∈ remaining ⊆ ordered_rest
          have b_ne_hmin : b ≠ hmin := by
            intro h_eq; rw [a_eq, h_eq] at h_ab; exact absurd h_ab (h_acyclic hmin)
          have b_in_ordered : b ∈ ordered_rest :=
            ih_contain b ((mem_remaining_iff b).mpr ⟨b_in, b_ne_hmin⟩)
          subst a_eq
          exact AppearsBefore.head ordered_rest b_in_ordered
        · -- a ≠ hmin: a ∈ remaining
          have a_in_remaining : a ∈ remaining :=
            (mem_remaining_iff a).mpr ⟨a_in, a_eq⟩
          by_cases b_eq : b = hmin
          · -- b = hmin: a has precedence over hmin, contradicting minimality
            exact (hmin_min.2 a a_in (b_eq ▸ h_ab)).elim
          · -- a, b both in remaining: use IH
            have b_in_remaining : b ∈ remaining :=
              (mem_remaining_iff b).mpr ⟨b_in, b_eq⟩
            have ab_before := ih_prec a b a_in_remaining b_in_remaining h_ab
            exact AppearsBefore.tail hmin ordered_rest ab_before

end ListDigraph
