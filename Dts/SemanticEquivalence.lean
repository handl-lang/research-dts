import Mathlib.Tactic
import Dts.Basic
import Dts.Synthesis
import Dts.Semantics

namespace TopologySynthesis

/-! # Semantic equivalence of synthesis and explicit nested handlers

The main gap was a semantic result: does the synthesized command behave the
same as a manually written nested `handle` term? We define an explicit
reference nesting and show that `synthesize` produces exactly that term, so
the trace semantics gives the same behavior.
-/

/-- Build the explicit nested `handle` term from an ordered handler list.
    The first handler becomes the innermost. -/
def manuallyNested (body : Command) : List Handler → Command
  | [] => body
  | h :: hs => manuallyNested (Command.handle body h) hs

/-- `synthesize` and the explicit `manuallyNested` recursion produce the
    same `Command`. -/
theorem synthesize_eq_manuallyNested (body : Command) (ordered : List Handler) :
    synthesize body ordered = manuallyNested body ordered := by
  induction ordered generalizing body with
  | nil =>
    simp [synthesize, manuallyNested, List.foldl_nil]
  | cons h hs ih =>
    simp [manuallyNested]
    unfold synthesize
    rw [List.foldl_cons]
    exact ih (Command.handle body h)

/-- Equality of syntax implies equality of traces. -/
theorem eval_congr {c1 c2 : Command} (h : c1 = c2) : eval c1 = eval c2 := by
  rw [h]

/-- **Semantic equivalence**: the synthesized command and the manually
    nested reference have identical traces. -/
theorem synthesize_eval_eq_manuallyNested (body : Command) (ordered : List Handler) :
    eval (synthesize body ordered) = eval (manuallyNested body ordered) := by
  rw [synthesize_eq_manuallyNested]

/-- The same result stated via `Command.Equiv`. -/
theorem synthesize_equiv_manuallyNested (body : Command) (ordered : List Handler) :
    Command.Equiv (synthesize body ordered) (manuallyNested body ordered) := by
  rw [Command.Equiv, synthesize_eq_manuallyNested]

end TopologySynthesis
