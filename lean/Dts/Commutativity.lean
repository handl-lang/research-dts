import Mathlib.Tactic
import Dts.Basic
import Dts.Synthesis
import Dts.Semantics

namespace TopologySynthesis

/-! # Semantic commutativity of disjoint handlers

Open question: when can two handlers be safely reordered? We give a partial
answer: handlers with disjoint handled operation sets commute. We also give a
concrete counterexample where overlapping handlers do not commute.
-/

/-- Two handlers are clause-disjoint when no operation name is handled by both. -/
def disjointClauses (h1 h2 : Handler) : Prop :=
  ∀ (op : OpName), ¬ (handlerHandles h1 op = true ∧ handlerHandles h2 op = true)

theorem disjointClauses.symm {h1 h2 : Handler} (d : disjointClauses h1 h2) :
    disjointClauses h2 h1 := by
  intro op h
  exact d op ⟨h.2, h.1⟩

/-- Swapping two disjoint adjacent handlers in the handler context does not
    change which handler is the first to catch an operation. -/
theorem firstHandler_swap {h1 h2 : Handler} (d : disjointClauses h1 h2)
    (pre post : List Handler) (op : OpName) :
    firstHandler (pre ++ h1 :: h2 :: post) op =
    firstHandler (pre ++ h2 :: h1 :: post) op := by
  induction pre with
  | nil =>
    cases h1b : handlerHandles h1 op with
    | true =>
      cases h2b : handlerHandles h2 op with
      | true =>
        exfalso
        exact d op ⟨h1b, h2b⟩
      | false =>
        simp [firstHandler, h1b, h2b]
    | false =>
      cases h2b : handlerHandles h2 op with
      | true =>
        simp [firstHandler, h1b, h2b]
      | false =>
        simp [firstHandler, h1b, h2b]
  | cons h pre ih =>
    cases hb : handlerHandles h op with
    | true =>
      simp [firstHandler, hb]
    | false =>
      simp [firstHandler, hb, ih]

/-- For any static command, swapping two disjoint adjacent handlers anywhere
    in the surrounding handler context does not change the trace. -/
theorem evalWith_swap {h1 h2 : Handler} (d : disjointClauses h1 h2)
    {c : Command} (pre post : List Handler) :
    evalWith (pre ++ h1 :: h2 :: post) c =
    evalWith (pre ++ h2 :: h1 :: post) c := by
  induction c generalizing pre post with
  | pure v =>
    simp [evalWith]
  | op n a =>
    simp [evalWith, firstHandler_swap d pre post n]
  | letin x p q ihp ihq =>
    have hp_eq := ihp pre post
    have hq_eq := ihq pre post
    simp [evalWith, hp_eq, hq_eq]
  | handle body h ih =>
    have eq := ih (h :: pre) post
    have h_eq : h :: (pre ++ h1 :: h2 :: post) = (h :: pre) ++ h1 :: h2 :: post := by
      rw [List.cons_append]
    have h_eq' : h :: (pre ++ h2 :: h1 :: post) = (h :: pre) ++ h2 :: h1 :: post := by
      rw [List.cons_append]
    simp [evalWith]
    rw [h_eq, h_eq']
    exact eq
  | cond c t e ihc iht ihe =>
    simp [evalWith]

/-- **Two-handler semantic commutativity theorem**: for a static body, if
    `h1` and `h2` have disjoint operation clauses, then nesting `h1` inside
    `h2` or `h2` inside `h1` produces the same trace. -/
theorem synthesize_commutative_two (body : Command) (h1 h2 : Handler)
    (d : disjointClauses h1 h2) (_hs : body.isStatic = true) :
    Command.Equiv (synthesize body [h1, h2]) (synthesize body [h2, h1]) := by
  simp [Command.Equiv, eval, synthesize, evalWith, List.foldl_cons, List.foldl_nil]
  exact evalWith_swap d [] []

section Counterexample

def H1 : Handler := { name := "H1", clauses := [{ op := "op" }] }
def H2 : Handler := { name := "H2", clauses := [{ op := "op" }] }
def counterBody : Command := Command.op "op" "x"

/-- Overlapping handlers are not disjoint. -/
example : ¬ disjointClauses H1 H2 := by
  simp [disjointClauses]
  use "op"
  native_decide

/-- When both handlers handle the same operation, the synthesized order
    changes the trace: the innermost handler catches the operation. -/
example : eval (synthesize counterBody [H1, H2]) ≠
          eval (synthesize counterBody [H2, H1]) := by
  simp [eval, synthesize, evalWith, H1, H2, counterBody, List.foldl_cons, List.foldl_nil]
  native_decide

end Counterexample

section FutureWork
/-
Generalization: for a static body, if `ordered` and `ordered'` are two lists
of handlers that are pairwise disjoint in their handled operation names and
one is a permutation of the other, then `eval (synthesize body ordered) =
eval (synthesize body ordered')`. The single adjacent step is now in
`synthesize_adjacent_swap`; the full `List.Perm` induction remains future work.
-/

/-- General fact: `synthesize` simply prepends the handler list as the
    `evalWith` context (innermost first). -/
theorem eval_synthesize (b : Command) (hs : List Handler) :
    eval (synthesize b hs) = evalWith hs b := by
  induction hs generalizing b with
  | nil =>
    simp [synthesize, eval]
  | cons h hs ih =>
    unfold synthesize
    change eval (synthesize (b.handle h) hs) = evalWith (h :: hs) b
    rw [ih (b.handle h)]
    simp [evalWith]

/-- Adjacent-swap generalization: if `h1` and `h2` are disjoint, swapping them
    anywhere in the handler list does not change the trace of the synthesized
    static program. -/
theorem synthesize_adjacent_swap (body : Command) (pre post : List Handler)
    (h1 h2 : Handler) (d : disjointClauses h1 h2) :
    eval (synthesize body (pre ++ [h1, h2] ++ post)) =
    eval (synthesize body (pre ++ [h2, h1] ++ post)) := by
  rw [eval_synthesize, eval_synthesize]
  rw [List.append_assoc pre [h1, h2] post]
  rw [List.append_assoc pre [h2, h1] post]
  exact evalWith_swap (c := body) d pre post
end FutureWork

section Permutation

/-- A list of handlers is pairwise clause-disjoint when any two distinct
    handlers in the list handle disjoint operation sets. -/
def pairwiseDisjoint (hs : List Handler) : Prop :=
  ∀ (h1 h2 : Handler), h1 ∈ hs → h2 ∈ hs → h1 ≠ h2 → disjointClauses h1 h2

theorem perm_mem {l l' : List Handler} (h : List.Perm l l') (a : Handler) : a ∈ l ↔ a ∈ l' := by
  induction h with
  | nil =>
    simp
  | cons b h ih =>
    simp [ih]
  | swap x y l =>
    simp
    tauto
  | trans h1 h2 ih1 ih2 =>
    exact ih1.trans ih2

/-- Pairwise disjointness is preserved under permutation. -/
theorem pairwiseDisjoint_of_perm {l l' : List Handler} (h : List.Perm l l') :
    pairwiseDisjoint l ↔ pairwiseDisjoint l' := by
  constructor
  · intro hp h1 h2 h1' h2' hne
    have h1l : h1 ∈ l := (perm_mem h h1).mpr h1'
    have h2l : h2 ∈ l := (perm_mem h h2).mpr h2'
    exact hp h1 h2 h1l h2l hne
  · intro hp h1 h2 h1l h2l hne
    have h1' : h1 ∈ l' := (perm_mem h h1).mp h1l
    have h2' : h2 ∈ l' := (perm_mem h h2).mp h2l
    exact hp h1 h2 h1' h2' hne

/-- Permuting a pairwise-disjoint handler list does not change the trace of
    the synthesized program. This completes the `List.Perm` induction left as
    future work in `synthesize_adjacent_swap`. -/
theorem synthesize_perm (body : Command) (ordered ordered' : List Handler)
    (h_perm : List.Perm ordered ordered')
    (h_pairwise : pairwiseDisjoint ordered) :
    eval (synthesize body ordered) = eval (synthesize body ordered') := by
  revert h_pairwise
  revert body
  induction h_perm with
  | nil =>
    intro body h_pairwise
    simp [synthesize, eval, List.foldl_nil]
  | cons a h ih =>
    intro body h_pairwise
    rename_i l l'
    have hpl : pairwiseDisjoint l := by
      intro h1 h2 h1l h2l hne
      exact h_pairwise h1 h2 (List.mem_cons_of_mem _ h1l) (List.mem_cons_of_mem _ h2l) hne
    have eq1 : synthesize body (a :: l) = synthesize (Command.handle body a) l := by
      unfold synthesize
      rw [List.foldl_cons]
    have eq2 : synthesize body (a :: l') = synthesize (Command.handle body a) l' := by
      unfold synthesize
      rw [List.foldl_cons]
    rw [eq1, eq2]
    exact ih (Command.handle body a) hpl
  | swap x y l =>
    intro body h_pairwise
    by_cases heq : x = y
    · -- x = y: the two lists are identical
      rw [heq]
    · -- x ≠ y: apply the two-handler adjacent-swap theorem
      have hxy : disjointClauses y x := by
        apply h_pairwise y x
        · simp
        · simp
        · exact Ne.symm heq
      rw [eval_synthesize body (y :: x :: l), eval_synthesize body (x :: y :: l)]
      exact evalWith_swap hxy (c := body) [] l
  | trans h1 h2 ih1 ih2 =>
    intro body h_pairwise
    rename_i l1 l2 l3
    have hpl2 : pairwiseDisjoint l2 := (pairwiseDisjoint_of_perm h1).mp h_pairwise
    have eq1 := ih1 body h_pairwise
    have eq2 := ih2 body hpl2
    exact Eq.trans eq1 eq2

/-- `Command.Equiv` version of the permutation invariance. -/
theorem synthesize_perm_equiv (body : Command) (ordered ordered' : List Handler)
    (h_perm : List.Perm ordered ordered')
    (h_pairwise : pairwiseDisjoint ordered) :
    Command.Equiv (synthesize body ordered) (synthesize body ordered') := by
  rw [Command.Equiv]
  exact synthesize_perm body ordered ordered' h_perm h_pairwise

end Permutation

end TopologySynthesis
