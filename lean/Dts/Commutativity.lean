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
General conjecture: for a static body, if `ordered` and `ordered'` are two
lists of handlers that are pairwise disjoint in their handled operation
names, then `eval (synthesize body ordered) = eval (synthesize body ordered')`.
This would follow from `evalWith_swap` together with a permutation/insertion
argument over the handler list. The two-handler case is fully proved above.
-/
end FutureWork

end TopologySynthesis
