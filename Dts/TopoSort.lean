import Mathlib.Tactic
import Dts.Basic
import Dts.Precedence
import Dts.Synthesis

namespace TopologySynthesis

-- Topological Sort Soundness

/-- A handler `h` is minimal in a list if no other handler in the list
    has precedence over it. -/
def IsMinimalIn (prec : Precedence) (h : Handler) (s : List Handler) : Prop :=
  h ∈ s ∧ ∀ h' ∈ s, prec h' h = true → False

/-- Filtering out an element that is in the list makes it shorter. -/
theorem filter_length_lt_of_mem (a : Handler) (l : List Handler) (h : a ∈ l) :
    (List.filter (· ≠ a) l).length < l.length := by
  induction l with
  | nil => simp at h
  | cons x rest ih =>
    by_cases xeq : x = a
    · -- x = a: filter removes x
      have hdec : ¬ decide (x ≠ a) = true := by rw [xeq]; simp
      rw [List.filter_cons, if_neg hdec]
      have : (List.filter (· ≠ a) rest).length ≤ rest.length := List.length_filter_le _ _
      simp [List.length_cons]; omega
    · -- x ≠ a: filter keeps x
      have hdec : decide (x ≠ a) = true := by rw [xeq]; simp
      rw [List.filter_cons, if_pos hdec, List.length_cons]
      have h_in_rest : a ∈ rest := by
        obtain h_eq | h_in := h
        · exact absurd h_eq.symm xeq
        · exact h_in
      have := ih h_in_rest
      omega

/-- Helper: strong induction on list length. -/
theorem list_strong_induction
    (P : List Handler → Prop)
    (h_ind : ∀ s : List Handler, (∀ t : List Handler, t.length < s.length → P t) → P s) :
    ∀ s : List Handler, P s := by
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

/-- For any non-empty finite list of handlers with an irreflexive precedence
    relation, there exists a minimal element. -/
theorem exists_minimal
    (prec : Precedence) (s : List Handler)
    (h_irrefl : Precedence.irreflexive prec)
    (h_tr : Precedence.transitive prec)
    (h_nonempty : s ≠ []) :
    ∃ h : Handler, IsMinimalIn prec h s := by
  induction s using list_strong_induction with
  | h_ind s ih =>
    cases s with
    | nil => exact absurd rfl h_nonempty
    | cons h' rest =>
      by_cases h_min : IsMinimalIn prec h' (h' :: rest)
      · exact ⟨h', h_min⟩
      · simp only [IsMinimalIn, not_and] at h_min
        have h''_exists := h_min List.mem_cons_self
        push Not at h''_exists
        obtain ⟨h'', h''_in, h''_prec, _⟩ := h''_exists
        have h''_in_rest : h'' ∈ rest := by
          simp at h''_in; cases h''_in
          case inl h_eq => rw [h_eq] at h''_prec; exact absurd h''_prec (h_irrefl h')
          case inr h => exact h
        have rest_nonempty : rest ≠ [] := by
          intro h_empty
          rw [h_empty] at h''_in_rest
          simp at h''_in_rest
        have rest_shorter : rest.length < (h' :: rest).length := by simp
        obtain ⟨hmin, hmin_min⟩ := ih rest rest_shorter rest_nonempty
        refine ⟨hmin, ?_⟩
        constructor
        · exact List.mem_cons_of_mem _ hmin_min.1
        · intro h''' h'''_in h'''_prec
          cases h'''_in with
          | head =>
            have h_tr' : prec h'' hmin = true := h_tr h'' h' hmin h''_prec h'''_prec
            exact hmin_min.2 h'' h''_in_rest h_tr'
          | tail _ h'''_in_rest =>
            exact hmin_min.2 h''' h'''_in_rest h'''_prec

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
  induction handlers using list_strong_induction with
  | h_ind handlers ih =>
    cases handlers with
    | nil =>
      exact ⟨[], ⟨fun _ h => by simp at h, fun _ _ a_in _ _ => by simp at a_in⟩⟩
    | cons h rest =>
      have full_nonempty : (h :: rest) ≠ [] := by simp
      obtain ⟨hmin, hmin_min⟩ := exists_minimal prec (h :: rest) h_irrefl h_tr full_nonempty
      set remaining := List.filter (· ≠ hmin) (h :: rest)
      have remaining_shorter : remaining.length < (h :: rest).length :=
        filter_length_lt_of_mem _ _ hmin_min.1
      obtain ⟨ordered_rest, ih_contain, ih_prec⟩ := ih remaining remaining_shorter
      have mem_remaining_iff (h' : Handler) : h' ∈ remaining ↔ h' ∈ (h :: rest) ∧ h' ≠ hmin := by
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
        · -- a = hmin: b ≠ hmin (irreflexivity), b ∈ remaining ⊆ ordered_rest
          have b_ne_hmin : b ≠ hmin := by
            intro h_eq; rw [a_eq, h_eq] at h_ab; exact absurd h_ab (h_irrefl hmin)
          have b_in_ordered : b ∈ ordered_rest :=
            ih_contain b ((mem_remaining_iff b).mpr ⟨b_in, b_ne_hmin⟩)
          subst a_eq
          exact AppearsBefore.head ordered_rest b_in_ordered
        · -- a ≠ hmin: a ∈ remaining
          have a_in_remaining : a ∈ remaining :=
            (mem_remaining_iff a).mpr ⟨a_in, a_eq⟩
          by_cases b_eq : b = hmin
          · -- b = hmin: prec a hmin contradicts minimality
            exact (hmin_min.2 a a_in (b_eq ▸ h_ab)).elim
          · -- a, b both in remaining: use IH
            have b_in_remaining : b ∈ remaining :=
              (mem_remaining_iff b).mpr ⟨b_in, b_eq⟩
            have ab_before := ih_prec a b a_in_remaining b_in_remaining h_ab
            exact AppearsBefore.tail hmin ordered_rest ab_before

end TopologySynthesis
