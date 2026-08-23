import Dts.Basic
import Dts.Synthesis
import Dts.Semantics
import Dts.Commutativity
import Dts.SanadaTwoHandlers

namespace SanadaBridge

open SanadaTwoHandlers TopologySynthesis

/-! # Phase 11: Concrete `ProfunctorCommute2` certificate for `Dts` handlers

We model the static fragment of `Command` (pure values, operation calls, and
let-binding) as the two-operation `Term₂` promonad from `SanadaTwoHandlers`.

- `op₁` represents any operation handled by `h₁`.
- `op₂` represents any operation handled by `h₂`.
- `Term₂.bind` (called `termBind₂` here) encodes `letin`.
- `Term₂` evaluation via `eval₁` then `eval₂'` (or `eval₂` then `eval₁'`)
  gives exactly the `Dts` trace for `synthesize body [h1, h2]` (resp.
  `[h2, h1]`).

The `ProfunctorCommute2` certificate from `SanadaTwoHandlers.profunctorCommute₂`
is therefore a model construction: for every `Command` in the fragment, the
`P₂` continuation built from its `Term₂` translation makes the two handler
orders agree.
-/

-- Make the core `Term`/`Term₂` evaluation functions available to `simp`.
attribute [simp] SanadaParameterized.eval eval₁ eval₂ termMap₂

section CommandAsTerm₂

/-- The static, two-handler fragment of `Command`.
    It contains no `cond` or nested `handle`. -/
inductive WellFormed : Command → Prop where
  | pure (v : String) : WellFormed (.pure v)
  | op (n : OpName) (a : String) : WellFormed (.op n a)
  | letin (x : String) (p q : Command) : WellFormed p → WellFormed q →
      WellFormed (.letin x p q)

/-- State for both operations: operations in `Dts` are stateless in this model. -/
abbrev CmdS : Type := Unit

/-- The input to an `op₁`/`op₂` is the operation name and its argument. -/
abbrev CmdOp : Type := OpName × String

/-- The output of one operation is the single trace event it generates. -/
abbrev CmdDelta : Type := List TraceEvent

/-- The final value of a `Term₂` computation is the full trace. -/
abbrev CmdB0 : Type := List TraceEvent

/-- Handler map for `op₁`: operations handled by `h₁`. -/
def h₁ (h : Handler) (p : CmdOp) : CmdDelta :=
  let (n, a) := p
  [TraceEvent.handled h.name n a]

/-- Handler map for `op₂`: operations handled by `h₂`. -/
def h₂ (h : Handler) (p : CmdOp) : CmdDelta :=
  let (n, a) := p
  [TraceEvent.handled h.name n a]

/-- Monadic bind for `Term₂`: sequence two `Term₂` computations. -/
@[simp]
def termBind₂ {B B' : Type}
    (t : Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B)
    (f : B → Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B') :
    Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B' :=
  match t with
  | .pure b => f b
  | .op₁ z s k =>
      .op₁ z s (fun (d, s') => termBind₂ (k (d, s')) f)
  | .op₂ z s k =>
      .op₂ z s (fun (d, s') => termBind₂ (k (d, s')) f)

/-- `termBind₂` commutes with `eval₁`/`eval₂'`. -/
lemma eval₂'_eval₁_bind {B B' : Type}
    (t : Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B)
    (f : B → Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B') :
    eval₂' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
      (eval₁ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
        (termBind₂ t f)) =
    eval₂' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
      (eval₁ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
        (f (eval₂' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
              (eval₁ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1) t)))) := by
  induction t with
  | pure b =>
    simp [termBind₂, eval₂']
  | op₁ z s k ih =>
    simp [termBind₂, eval₂', eval₁]
    apply ih
  | op₂ z s k ih =>
    simp [termBind₂, eval₂', eval₁]
    apply ih

/-- `termMap₂` commutes with `eval₁`/`eval₂'`. -/
lemma eval₂'_eval₁_map {B B' : Type} (g : B → B')
    (t : Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B) :
    eval₂' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
      (eval₁ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
        (termMap₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta g t)) =
    g (eval₂' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
         (eval₁ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1) t)) := by
  induction t with
  | pure b =>
    simp [termMap₂, eval₂']
  | op₁ z s k ih =>
    simp [termMap₂, eval₂', eval₁]
    apply ih
  | op₂ z s k ih =>
    simp [termMap₂, eval₂', eval₁]
    apply ih

/-- `termBind₂` commutes with `eval₂`/`eval₁'`. -/
lemma eval₁'_eval₂_bind {B B' : Type}
    (t : Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B)
    (f : B → Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B') :
    eval₁' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
      (eval₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
        (termBind₂ t f)) =
    eval₁' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
      (eval₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
        (f (eval₁' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
              (eval₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2) t)))) := by
  induction t with
  | pure b =>
    simp [termBind₂, eval₁']
  | op₁ z s k ih =>
    simp [termBind₂, eval₁', eval₂]
    apply ih
  | op₂ z s k ih =>
    simp [termBind₂, eval₁', eval₂]
    apply ih

/-- `termMap₂` commutes with `eval₂`/`eval₁'`. -/
lemma eval₁'_eval₂_map {B B' : Type} (g : B → B')
    (t : Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta B) :
    eval₁' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
      (eval₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
        (termMap₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta g t)) =
    g (eval₁' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
         (eval₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2) t)) := by
  induction t with
  | pure b =>
    simp [termMap₂, eval₁']
  | op₁ z s k ih =>
    simp [termMap₂, eval₁', eval₂]
    apply ih
  | op₂ z s k ih =>
    simp [termMap₂, eval₁', eval₂]
    apply ih

/-- Translate a well-formed `Command` into a `Term₂` computation whose value is
    the `Dts` trace for `synthesize c [h1, h2]`. -/
@[simp]
def toTerm₂ (h1 h2 : Handler) : Command →
    Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta CmdB0
  | .pure v => .pure [TraceEvent.pure v]
  | .op n a =>
      if handlerHandles h1 n then
        .op₁ (n, a) () (fun _ => .pure [TraceEvent.handled h1.name n a])
      else if handlerHandles h2 n then
        .op₂ (n, a) () (fun _ => .pure [TraceEvent.handled h2.name n a])
      else
        .pure [TraceEvent.unhandled n a]
  | .letin _x p q =>
      termBind₂ (toTerm₂ h1 h2 p) (fun d =>
        termMap₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta
          (fun qTrace => d ++ qTrace) (toTerm₂ h1 h2 q))
  | .handle _ _ => .pure []
  | .cond _ _ _ => .pure []

/-- Evaluation through the `eval₁`-then-`eval₂'` path gives the `Dts` trace for
    `synthesize c [h1, h2]`. -/
lemma eval_synthesize_eq_eval₂' (h1 h2 : Handler) (c : Command)
    (hw : WellFormed c) :
    eval (synthesize c [h1, h2]) =
    eval₂' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
      (eval₁ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
        (toTerm₂ h1 h2 c)) := by
  induction hw with
  | pure v =>
    simp [synthesize, eval, evalWith, toTerm₂, eval₂', eval₁]
  | op n a =>
    simp [synthesize, eval, evalWith, toTerm₂]
    split_ifs with h1b h2b
    · simp [firstHandler, h1b, eval₂', eval₁]
    · simp [firstHandler, h1b, h2b, eval₂', eval₁]
    · simp [firstHandler, h1b, h2b, eval₂', eval₁]
  | letin x p q _ _ ihp ihq =>
    have hp : eval (synthesize p [h1, h2]) = evalWith [h1, h2] p := by
      simp [synthesize, eval, evalWith]
    have hq : eval (synthesize q [h1, h2]) = evalWith [h1, h2] q := by
      simp [synthesize, eval, evalWith]
    simp [synthesize, eval, evalWith, toTerm₂]
    rw [eval₂'_eval₁_bind]
    rw [eval₂'_eval₁_map]
    simp only [←hp, ←hq]
    rw [ihp, ihq]

/-- Evaluation through the `eval₂`-then-`eval₁'` path gives the `Dts` trace for
    `synthesize c [h2, h1]`. -/
lemma eval_synthesize_eq_eval₁' (h1 h2 : Handler) (c : Command)
    (d : disjointClauses h1 h2) (hw : WellFormed c) :
    eval (synthesize c [h2, h1]) =
    eval₁' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1)
      (eval₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2)
        (toTerm₂ h1 h2 c)) := by
  induction hw with
  | pure v =>
    simp [synthesize, eval, evalWith, toTerm₂, eval₁', eval₂]
  | op n a =>
    simp [synthesize, eval, evalWith, toTerm₂]
    split_ifs with h1b h2b
    · have h2b' : handlerHandles h2 n = false := by
        by_contra h
        have : handlerHandles h2 n = true := by
          have hne : handlerHandles h2 n ≠ false := h
          cases h' : handlerHandles h2 n with
          | true => rfl
          | false => contradiction
        have := d n ⟨h1b, this⟩
        contradiction
      simp [firstHandler, h1b, h2b', eval₁', eval₂]
    · simp [firstHandler, h2b, eval₁', eval₂]
    · simp [firstHandler, h1b, h2b, eval₁', eval₂]
  | letin x p q _ _ ihp ihq =>
    have hp : eval (synthesize p [h2, h1]) = evalWith [h2, h1] p := by
      simp [synthesize, eval, evalWith]
    have hq : eval (synthesize q [h2, h1]) = evalWith [h2, h1] q := by
      simp [synthesize, eval, evalWith]
    simp [synthesize, eval, evalWith, toTerm₂]
    rw [eval₁'_eval₂_bind]
    rw [eval₁'_eval₂_map]
    simp only [←hp, ←hq]
    rw [ihp, ihq]

end CommandAsTerm₂

section Certificate

/-- The `P₂` continuation induced by a well-formed `Command`. -/
def commandContinuation (h1 h2 : Handler) (c : Command) :
    P₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta Unit
      (Term₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta CmdB0) :=
  fun _ => Term₂.pure (toTerm₂ h1 h2 c)

/-- Concrete `ProfunctorCommute2` certificate for two disjoint `Dts` handlers:
    the `Term₂` continuation derived from any well-formed `Command` makes the
    two handler-evaluation orders agree. -/
theorem profunctorCommute2_of_disjoint (h1 h2 : Handler)
    (_d : disjointClauses h1 h2) (c : Command) (_hw : WellFormed c) :
    rmap₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta
      (eval₂' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2))
      (rmap₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta
        (eval₁ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1))
        (commandContinuation h1 h2 c)) () =
    rmap₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta
      (eval₁' CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₁ h1))
      (rmap₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta
        (eval₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta (h₂ h2))
        (commandContinuation h1 h2 c)) () := by
  apply profunctorCommute₂ CmdS CmdOp CmdDelta CmdS CmdOp CmdDelta
    (h₁ h1) (h₂ h2) (commandContinuation h1 h2 c) ()

/-- The `ProfunctorCommute2` certificate implies `Command.Equiv` for the
    well-formed two-handler fragment. -/
theorem Commutativity_from_ProfunctorCommute2 (body : Command) (h1 h2 : Handler)
    (d : disjointClauses h1 h2) (hw : WellFormed body) :
    Command.Equiv (synthesize body [h1, h2]) (synthesize body [h2, h1]) := by
  have h := profunctorCommute2_of_disjoint h1 h2 d body hw
  simp [rmap₂, termMap₂, commandContinuation] at h
  unfold Command.Equiv
  rw [eval_synthesize_eq_eval₂' h1 h2 body hw]
  rw [eval_synthesize_eq_eval₁' h1 h2 body d hw]
  exact h

end Certificate

end SanadaBridge
