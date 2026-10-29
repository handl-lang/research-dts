import Mathlib.Tactic
import Dts.Basic
import Dts.Semantics
import Dts.Synthesis

namespace TopologySynthesis

/-! # Relational semantics for `Command`

This file defines a big-step evaluation relation `Eval` (and an analogous
`Exec` relation) for the full `Command` semantics.  The relation records the
observable `TraceEvent` trace and the final `Nat` state.

It also defines a syntactic may-emit relation `CanEmit` that over-approximates
the operation names a command can produce.  This is used to give a logical
(non-`partial`) reading of handler effect independence.
-/

/-- Syntactic over-approximation of the operation names a command (or one of
    the continuations in a handler inside it) may produce at run time. -/
inductive CanEmit : Command → OpName → Prop where
  | op (name : OpName) (arg : String) :
      CanEmit (Command.op name arg) name
  | op_cont (name : OpName) (arg : String) (h : Handler) (c : HandlerClause)
      (k : Command) (op : OpName) :
      c ∈ h.clauses →
      c.op = name →
      c.cont = some k →
      CanEmit k op →
      CanEmit (Command.op name arg) op
  | letin_left (x : String) (p q : Command) (op : OpName) :
      CanEmit p op → CanEmit (Command.letin x p q) op
  | letin_right (x : String) (p q : Command) (op : OpName) :
      CanEmit q op → CanEmit (Command.letin x p q) op
  | handle (body : Command) (h : Handler) (op : OpName) :
      CanEmit body op → CanEmit (Command.handle body h) op
  | handle_clause (body : Command) (h : Handler) (c : HandlerClause)
      (k : Command) (op : OpName) :
      c ∈ h.clauses →
      c.cont = some k →
      CanEmit k op →
      CanEmit (Command.handle body h) op
  | cond_cond (c t e : Command) (op : OpName) :
      CanEmit c op → CanEmit (Command.cond c t e) op
  | cond_t (c t e : Command) (op : OpName) :
      CanEmit t op → CanEmit (Command.cond c t e) op
  | cond_e (c t e : Command) (op : OpName) :
      CanEmit e op → CanEmit (Command.cond c t e) op

/-- A handler emits `op` if one of its clause continuations can emit `op`. -/
def Handler.emits (h : Handler) (op : OpName) : Prop :=
  ∃ (c : HandlerClause), c ∈ h.clauses ∧
    ∃ (k : Command), c.cont = some k ∧ CanEmit k op

/-- Logical (relation-based) effect independence: disjoint handled sets and no
    mutual emission-into-handles. -/
def Handler.effectIndependent' (h1 h2 : Handler) : Prop :=
  (∀ op, op ∈ h1.handles → op ∉ h2.handles) ∧
  (∀ op, h1.emits op → op ∉ h2.handles) ∧
  (∀ op, h2.emits op → op ∉ h1.handles)

def pairwiseEffectIndependent' (hs : List Handler) : Prop :=
  ∀ (h1 h2 : Handler), h1 ∈ hs → h2 ∈ hs → h1 ≠ h2 →
    h1.effectIndependent' h2

/-- Observable trace evaluation relation. -/
inductive Eval : List Handler → Command → Nat → List TraceEvent → Nat → Prop where
  | pure (ctx : List Handler) (val : String) (s : Nat) :
      Eval ctx (Command.pure val) s [TraceEvent.pure val s] s
  | op_handled_no_cont {ctx : List Handler} (op arg : String) (s : Nat)
      (handler : Handler) (clause : HandlerClause) (rest : List Handler)
      (hfr : findHandlerRest ctx op = some (handler, clause, rest))
      (hcont : clause.cont = none) :
      Eval ctx (Command.op op arg) s
        [TraceEvent.handled handler.name op arg s]
        (clause.stateUpdate s)
  | op_handled_cont {ctx : List Handler} (op arg : String) (s : Nat)
      (handler : Handler) (clause : HandlerClause) (rest : List Handler)
      (k : Command) (t : List TraceEvent) (s' : Nat)
      (hfr : findHandlerRest ctx op = some (handler, clause, rest))
      (hcont : clause.cont = some k)
      (hk : Eval rest k (clause.stateUpdate s) t s') :
      Eval ctx (Command.op op arg) s
        ([TraceEvent.handled handler.name op arg s] ++ t)
        s'
  | op_unhandled {ctx : List Handler} (op arg : String) (s : Nat)
      (hfr : findHandlerRest ctx op = none) :
      Eval ctx (Command.op op arg) s [TraceEvent.unhandled op arg s] s
  | letin {ctx : List Handler} (x : String) (p q : Command) (s s1 s2 : Nat)
      (t1 t2 : List TraceEvent)
      (hp : Eval ctx p s t1 s1)
      (hq : Eval ctx q s1 t2 s2) :
      Eval ctx (Command.letin x p q) s (t1 ++ t2) s2
  | handle {ctx : List Handler} (body : Command) (h : Handler) (s s' : Nat)
      (t : List TraceEvent)
      (hb : Eval (h :: ctx) body s t s') :
      Eval ctx (Command.handle body h) s t s'
  | cond_true {ctx : List Handler} (c t e : Command) (s s' s'' : Nat)
      (tc tb : List TraceEvent)
      (hc : Eval ctx c s tc s')
      (hval : lastTraceVal tc = "true")
      (ht : Eval ctx t s' tb s'') :
      Eval ctx (Command.cond c t e) s (tc ++ tb) s''
  | cond_false {ctx : List Handler} (c t e : Command) (s s' s'' : Nat)
      (tc tb : List TraceEvent)
      (hc : Eval ctx c s tc s')
      (hval : lastTraceVal tc ≠ "true")
      (he : Eval ctx e s' tb s'') :
      Eval ctx (Command.cond c t e) s (tc ++ tb) s''

/-- Execution trace relation (optional but useful). -/
inductive Exec : List Handler → Command → Nat → List ExecEvent → Nat → Prop where
  | pure (ctx : List Handler) (val : String) (s : Nat) :
      Exec ctx (Command.pure val) s [ExecEvent.pure val (ctx.map (·.name)) s] s
  | op_handled_no_cont {ctx : List Handler} (op arg : String) (s : Nat)
      (handler : Handler) (clause : HandlerClause) (rest : List Handler)
      (hfr : findHandlerRest ctx op = some (handler, clause, rest))
      (hcont : clause.cont = none) :
      Exec ctx (Command.op op arg) s
        [ExecEvent.handled handler.name op arg (ctx.map (·.name)) s]
        (clause.stateUpdate s)
  | op_handled_cont {ctx : List Handler} (op arg : String) (s : Nat)
      (handler : Handler) (clause : HandlerClause) (rest : List Handler)
      (k : Command) (es : List ExecEvent) (s' : Nat)
      (hfr : findHandlerRest ctx op = some (handler, clause, rest))
      (hcont : clause.cont = some k)
      (hk : Exec rest k (clause.stateUpdate s) es s') :
      Exec ctx (Command.op op arg) s
        ([ExecEvent.handled handler.name op arg (ctx.map (·.name)) s] ++ es)
        s'
  | op_unhandled {ctx : List Handler} (op arg : String) (s : Nat)
      (hfr : findHandlerRest ctx op = none) :
      Exec ctx (Command.op op arg) s
        [ExecEvent.unhandled op arg (ctx.map (·.name)) s] s
  | letin {ctx : List Handler} (x : String) (p q : Command) (s s1 s2 : Nat)
      (es1 es2 : List ExecEvent)
      (hp : Exec ctx p s es1 s1)
      (hq : Exec ctx q s1 es2 s2) :
      Exec ctx (Command.letin x p q) s (es1 ++ es2) s2
  | handle {ctx : List Handler} (body : Command) (h : Handler) (s s' : Nat)
      (es : List ExecEvent)
      (hb : Exec (h :: ctx) body s es s') :
      Exec ctx (Command.handle body h) s es s'
  | cond_true {ctx : List Handler} (c t e : Command) (s s' s'' : Nat)
      (ec eb : List ExecEvent)
      (hc : Exec ctx c s ec s')
      (hval : lastExecVal ec = "true")
      (ht : Exec ctx t s' eb s'') :
      Exec ctx (Command.cond c t e) s (ec ++ eb) s''
  | cond_false {ctx : List Handler} (c t e : Command) (s s' s'' : Nat)
      (ec eb : List ExecEvent)
      (hc : Exec ctx c s ec s')
      (hval : lastExecVal ec ≠ "true")
      (he : Exec ctx e s' eb s'') :
      Exec ctx (Command.cond c t e) s (ec ++ eb) s''

/-- Relational top-level `eval`: a trace/final-state pair is an `eval` of `c`
    when `c` evaluates to that trace from state `0` with the empty handler
    stack. -/
def evalRel (c : Command) (t : List TraceEvent) (s' : Nat) : Prop :=
  Eval [] c 0 t s'

/-- Relational program equivalence: two commands produce the same set of
    top-level observable traces. -/
def Command.equiv (c1 c2 : Command) : Prop :=
  ∀ (t : List TraceEvent) (s' : Nat), evalRel c1 t s' ↔ evalRel c2 t s'

theorem Eval_synthesize (body : Command) (ordered : List Handler)
    (t : List TraceEvent) (s' : Nat) :
    Eval [] (synthesize body ordered) 0 t s' ↔
    Eval ordered body 0 t s' := by
  induction ordered generalizing body with
  | nil =>
    simp [synthesize]
  | cons h hs ih =>
    have step1 : Eval [] (synthesize (Command.handle body h) hs) 0 t s' ↔
                 Eval hs (Command.handle body h) 0 t s' :=
      ih (Command.handle body h)
    have step2 : Eval hs (Command.handle body h) 0 t s' ↔
                 Eval (h :: hs) body 0 t s' := by
      constructor
      · intro e
        cases e with
        | handle _ _ _ _ _ hb => exact hb
      · intro hb
        apply Eval.handle
        exact hb
    exact Iff.trans step1 step2

private theorem findHandlerRest_append {pre : List Handler} {ctx : List Handler} {op : OpName} :
    findHandlerRest (pre ++ ctx) op =
    match findHandlerRest pre op with
    | some (handler, clause, rest) => some (handler, clause, rest ++ ctx)
    | none => findHandlerRest ctx op := by
  induction pre with
  | nil =>
    simp [findHandlerRest]
  | cons h t ih =>
    by_cases hc : h.clauses.find? (fun c => c.op == op) = none
    · simp [findHandlerRest, hc, List.cons_append]
      rw [ih]
    · cases h_eq : h.clauses.find? (fun c => c.op == op) with
      | some c =>
        simp [findHandlerRest, h_eq]
      | none =>
        contradiction

private theorem mem_of_findHandlerRest_some {ctx op h c rest}
    (hfr : findHandlerRest ctx op = some (h, c, rest)) : c ∈ h.clauses := by
  induction ctx with
  | nil =>
    simp [findHandlerRest] at hfr
  | cons h' t ih =>
    by_cases hc : h'.clauses.find? (fun c => c.op == op) = none
    · simp [findHandlerRest, hc] at hfr
      exact ih hfr
    · cases h_eq : h'.clauses.find? (fun c => c.op == op) with
      | some c' =>
        simp [findHandlerRest, h_eq] at hfr
        rcases hfr with ⟨rfl, rfl, rfl⟩
        exact List.mem_of_find?_eq_some h_eq
      | none =>
        contradiction

private theorem op_eq_of_findHandlerRest_some {ctx op h c rest}
    (hfr : findHandlerRest ctx op = some (h, c, rest)) : c.op = op := by
  induction ctx with
  | nil =>
    simp [findHandlerRest] at hfr
  | cons h' t ih =>
    by_cases hc : h'.clauses.find? (fun c => c.op == op) = none
    · simp [findHandlerRest, hc] at hfr
      exact ih hfr
    · cases h_eq : h'.clauses.find? (fun c => c.op == op) with
      | some c' =>
        have h_eq' : findHandlerRest (h' :: t) op = some (h', c', t) := by
          simp [findHandlerRest, h_eq]
        rw [h_eq'] at hfr
        have heq1 : (h', c', t) = (h, c, rest) := by injection hfr
        have heq_c : c' = c := congrArg (fun x => x.2.1) heq1
        have hop : (fun (c0 : HandlerClause) => c0.op == op) c' :=
          @List.find?_some _ (fun (c0 : HandlerClause) => c0.op == op) c' h'.clauses h_eq
        rw [beq_iff_eq] at hop
        rw [heq_c] at hop
        exact hop
      | none =>
        contradiction

private theorem findHandlerRest_inert {pre : List Handler} {h : Handler} {ctx : List Handler} {op : OpName}
    (hh : op ∉ h.handles) :
    findHandlerRest (pre ++ h :: ctx) op =
    match findHandlerRest pre op with
    | some (handler, clause, rest) => some (handler, clause, rest ++ h :: ctx)
    | none => findHandlerRest ctx op := by
  induction pre with
  | nil =>
    have hnone : h.clauses.find? (fun c => c.op == op) = none := by
      by_contra h_contra
      push_neg at h_contra
      cases h_eq : h.clauses.find? (fun c => c.op == op) with
      | some c =>
        have hmem : c ∈ h.clauses := List.mem_of_find?_eq_some h_eq
        have hop : (fun (c0 : HandlerClause) => c0.op == op) c :=
          @List.find?_some _ (fun (c0 : HandlerClause) => c0.op == op) c h.clauses h_eq
        have hcop : c.op = op := by rw [beq_iff_eq] at hop; exact hop
        have : op ∈ h.handles := by
          simp [Handler.handles, Handler.handlesList, List.mem_toFinset, List.mem_map]
          use c, hmem, hcop
        contradiction
      | none =>
        contradiction
    simp [findHandlerRest, hnone]
  | cons h' t ih =>
    by_cases hc : h'.clauses.find? (fun c => c.op == op) = none
    · simp [findHandlerRest, hc, List.cons_append]
      rw [ih]
    · cases h_eq : h'.clauses.find? (fun c => c.op == op) with
      | some c =>
        simp [findHandlerRest, h_eq, List.cons_append]
      | none =>
        contradiction

private theorem Eval_inert_aux {pre : List Handler} {h : Handler} {ctx : List Handler} {c : Command}
    {s : Nat} {t : List TraceEvent} {s' : Nat}
    (h_inert : ∀ op, CanEmit c op → op ∉ h.handles) :
    Eval (pre ++ h :: ctx) c s t s' ↔ Eval (pre ++ ctx) c s t s' := by
  constructor
  · -- remove the inert handler
    suffices aux : ∀ (ctx' : List Handler) (c' : Command) (s : Nat) (t : List TraceEvent) (s' : Nat),
                   Eval ctx' c' s t s' →
                   ∀ (pre : List Handler) (h : Handler) (ctx0 : List Handler),
                     ctx' = pre ++ h :: ctx0 →
                     (∀ op, CanEmit c' op → op ∉ h.handles) →
                     Eval (pre ++ ctx0) c' s t s' by
      intro e
      apply aux _ _ _ _ _ e _ _ _ rfl h_inert
    intro ctx' c' s t s' e
    induction e with
    | pure val s =>
      intro pre h ctx0 h_eq h_inert
      apply Eval.pure
    | op_unhandled op arg s hfr =>
      intro pre h ctx0 h_eq h_inert
      rw [h_eq] at hfr
      have hop : op ∉ h.handles := h_inert op (CanEmit.op op arg)
      have hsrc := findHandlerRest_inert (pre := pre) (ctx := ctx0) hop
      rw [hsrc] at hfr
      have htarg : findHandlerRest (pre ++ ctx0) op = none := by
        rw [findHandlerRest_append]
        by_cases hnone : findHandlerRest pre op = none
        · simp [hnone]
          simp [hnone] at hfr
          exact hfr
        · have hsome : ∃ p, findHandlerRest pre op = some p := by
            have hne : findHandlerRest pre op ≠ none := by
              intro h_contra; apply hnone; simp [h_contra]
            have hsome' : (findHandlerRest pre op).isSome := by
              exact Option.ne_none_iff_isSome.mp hne
            exact ⟨(findHandlerRest pre op).get hsome', Option.get_mem hsome'⟩
          rcases hsome with ⟨p, hpre⟩
          have hpre' : findHandlerRest pre op = some (p.1, p.2.1, p.2.2) := by
            rw [show p = (p.1, p.2.1, p.2.2) by simp]
            exact hpre
          simp [hpre'] at hfr
      apply Eval.op_unhandled
      exact htarg
    | op_handled_no_cont op arg s handler clause rest hfr hcont =>
      intro pre h ctx0 h_eq h_inert
      rw [h_eq] at hfr
      have hop : op ∉ h.handles := h_inert op (CanEmit.op op arg)
      have hsrc := findHandlerRest_inert (pre := pre) (ctx := ctx0) hop
      rw [hsrc] at hfr
      by_cases hnone : findHandlerRest pre op = none
      · simp [hnone] at hfr
        have htarg : findHandlerRest (pre ++ ctx0) op = some (handler, clause, rest) := by
          rw [findHandlerRest_append]
          simp [hnone]
          exact hfr
        apply Eval.op_handled_no_cont
        · exact htarg
        · exact hcont
      · have hsome : ∃ p, findHandlerRest pre op = some p := by
          have hne : findHandlerRest pre op ≠ none := by
            intro h_contra; apply hnone; simp [h_contra]
          have hsome' : (findHandlerRest pre op).isSome := by
            exact Option.ne_none_iff_isSome.mp hne
          exact ⟨(findHandlerRest pre op).get hsome', Option.get_mem hsome'⟩
        rcases hsome with ⟨p, hpre⟩
        have hpre' : findHandlerRest pre op = some (p.1, p.2.1, p.2.2) := by
          rw [show p = (p.1, p.2.1, p.2.2) by simp]
          exact hpre
        simp [hpre'] at hfr
        have htarg : findHandlerRest (pre ++ ctx0) op = some (p.1, p.2.1, p.2.2 ++ ctx0) := by
          rw [findHandlerRest_append]
          simp [hpre']

        rw [hfr.2.1.symm] at hcont
        rw [hfr.1.symm, hfr.2.1.symm]
        apply Eval.op_handled_no_cont
        · exact htarg
        · exact hcont
    | op_handled_cont op arg s handler clause rest k t s' hfr hcont hk ihhk =>
      intro pre h ctx0 h_eq h_inert
      rw [h_eq] at hfr
      have hop : op ∉ h.handles := h_inert op (CanEmit.op op arg)
      have hsrc := findHandlerRest_inert (pre := pre) (ctx := ctx0) hop
      rw [hsrc] at hfr
      by_cases hnone : findHandlerRest pre op = none
      · simp [hnone] at hfr
        have htarg : findHandlerRest (pre ++ ctx0) op = some (handler, clause, rest) := by
          rw [findHandlerRest_append]
          simp [hnone]
          exact hfr
        apply Eval.op_handled_cont
        · exact htarg
        · exact hcont
        · exact hk
      · have hsome : ∃ p, findHandlerRest pre op = some p := by
          have hne : findHandlerRest pre op ≠ none := by
            intro h_contra; apply hnone; simp [h_contra]
          have hsome' : (findHandlerRest pre op).isSome := by
            exact Option.ne_none_iff_isSome.mp hne
          exact ⟨(findHandlerRest pre op).get hsome', Option.get_mem hsome'⟩
        rcases hsome with ⟨p, hpre⟩
        have hpre' : findHandlerRest pre op = some (p.1, p.2.1, p.2.2) := by
          rw [show p = (p.1, p.2.1, p.2.2) by simp]
          exact hpre
        simp [hpre'] at hfr
        rw [hfr.2.1.symm] at hcont
        have h_inert_k : ∀ op', CanEmit k op' → op' ∉ h.handles := by
          intro op' hkemit
          apply h_inert op'
          apply CanEmit.op_cont op arg p.1 p.2.1 k op'
          · exact mem_of_findHandlerRest_some hpre'
          · exact op_eq_of_findHandlerRest_some hpre'
          · exact hcont
          · exact hkemit
        have hk' := ihhk p.2.2 h ctx0 (show rest = p.2.2 ++ h :: ctx0 by exact hfr.2.2.symm) h_inert_k
        rw [hfr.2.1.symm] at hk'
        have htarg : findHandlerRest (pre ++ ctx0) op = some (p.1, p.2.1, p.2.2 ++ ctx0) := by
          rw [findHandlerRest_append]
          simp [hpre']

        rw [hfr.1.symm]
        apply Eval.op_handled_cont
        · exact htarg
        · exact hcont
        · exact hk'
    | letin x p q s s1 s2 t1 t2 hp hq ihp ihq =>
      intro pre h ctx0 h_eq h_inert
      have hp' := ihp pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.letin_left x p q op hcan))
      have hq' := ihq pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.letin_right x p q op hcan))
      apply Eval.letin
      · exact hp'
      · exact hq'
    | handle body h' s s' t hb ihb =>
      intro pre h ctx0 h_eq h_inert
      have h_inert_body : ∀ op, CanEmit body op → op ∉ h.handles :=
        fun op hcan => h_inert op (CanEmit.handle body h' op hcan)
      have h_eq' : h' :: (pre ++ h :: ctx0) = (h' :: pre) ++ h :: ctx0 := by simp [List.cons_append]
      rw [h_eq] at ihb
      have hb' := ihb (h' :: pre) h ctx0 h_eq' h_inert_body
      apply Eval.handle
      exact hb'
    | cond_true c t e s s' s'' tc tb hc hval ht ihc iht =>
      intro pre h ctx0 h_eq h_inert
      have hc' := ihc pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_cond c t e op hcan))
      have ht' := iht pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_t c t e op hcan))
      apply Eval.cond_true
      · exact hc'
      · exact hval
      · exact ht'
    | cond_false c t e s s' s'' tc tb hc hval he ihc ihe =>
      intro pre h ctx0 h_eq h_inert
      have hc' := ihc pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_cond c t e op hcan))
      have he' := ihe pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_e c t e op hcan))
      apply Eval.cond_false
      · exact hc'
      · exact hval
      · exact he'
  · -- add the inert handler back
    suffices aux : ∀ (ctx' : List Handler) (c' : Command) (s : Nat) (t : List TraceEvent) (s' : Nat),
                   Eval ctx' c' s t s' →
                   ∀ (pre : List Handler) (h : Handler) (ctx0 : List Handler),
                     ctx' = pre ++ ctx0 →
                     (∀ op, CanEmit c' op → op ∉ h.handles) →
                     Eval (pre ++ h :: ctx0) c' s t s' by
      intro e
      apply aux _ _ _ _ _ e _ _ _ rfl h_inert
    intro ctx' c' s t s' e
    induction e with
    | pure val s =>
      intro pre h ctx0 h_eq h_inert
      apply Eval.pure
    | op_unhandled op arg s hfr =>
      intro pre h ctx0 h_eq h_inert
      rw [h_eq] at hfr
      have hop : op ∉ h.handles := h_inert op (CanEmit.op op arg)
      have htarg : findHandlerRest (pre ++ h :: ctx0) op = none := by
        rw [findHandlerRest_inert (pre := pre) (ctx := ctx0) hop]
        rw [findHandlerRest_append] at hfr
        by_cases hnone : findHandlerRest pre op = none
        · simp [hnone]
          simp [hnone] at hfr
          exact hfr
        · have hsome : ∃ p, findHandlerRest pre op = some p := by
            have hne : findHandlerRest pre op ≠ none := by
              intro h_contra; apply hnone; simp [h_contra]
            have hsome' : (findHandlerRest pre op).isSome := by
              exact Option.ne_none_iff_isSome.mp hne
            exact ⟨(findHandlerRest pre op).get hsome', Option.get_mem hsome'⟩
          rcases hsome with ⟨p, hpre⟩
          have hpre' : findHandlerRest pre op = some (p.1, p.2.1, p.2.2) := by
            rw [show p = (p.1, p.2.1, p.2.2) by simp]
            exact hpre
          simp [hpre'] at hfr
      apply Eval.op_unhandled
      exact htarg
    | op_handled_no_cont op arg s handler clause rest hfr hcont =>
      intro pre h ctx0 h_eq h_inert
      rw [h_eq] at hfr
      rw [findHandlerRest_append] at hfr
      have hop : op ∉ h.handles := h_inert op (CanEmit.op op arg)
      by_cases hnone : findHandlerRest pre op = none
      · have htarg : findHandlerRest (pre ++ h :: ctx0) op = some (handler, clause, rest) := by
          rw [findHandlerRest_inert (pre := pre) (ctx := ctx0) hop]
          simp [hnone]
          simp [hnone] at hfr
          exact hfr
        apply Eval.op_handled_no_cont
        · exact htarg
        · exact hcont
      · have hsome : ∃ p, findHandlerRest pre op = some p := by
          have hne : findHandlerRest pre op ≠ none := by
            intro h_contra; apply hnone; simp [h_contra]
          have hsome' : (findHandlerRest pre op).isSome := by
            exact Option.ne_none_iff_isSome.mp hne
          exact ⟨(findHandlerRest pre op).get hsome', Option.get_mem hsome'⟩
        rcases hsome with ⟨p, hpre⟩
        have hpre' : findHandlerRest pre op = some (p.1, p.2.1, p.2.2) := by
          rw [show p = (p.1, p.2.1, p.2.2) by simp]
          exact hpre
        simp [hpre'] at hfr
        have htarg : findHandlerRest (pre ++ h :: ctx0) op = some (p.1, p.2.1, p.2.2 ++ h :: ctx0) := by
          rw [findHandlerRest_inert (pre := pre) (ctx := ctx0) hop]
          simp [hpre']

        rw [hfr.2.1.symm] at hcont
        rw [hfr.1.symm, hfr.2.1.symm]
        apply Eval.op_handled_no_cont
        · exact htarg
        · exact hcont
    | op_handled_cont op arg s handler clause rest k t s' hfr hcont hk ihhk =>
      intro pre h ctx0 h_eq h_inert
      rw [h_eq] at hfr
      rw [findHandlerRest_append] at hfr
      have hop : op ∉ h.handles := h_inert op (CanEmit.op op arg)
      by_cases hnone : findHandlerRest pre op = none
      · have htarg : findHandlerRest (pre ++ h :: ctx0) op = some (handler, clause, rest) := by
          rw [findHandlerRest_inert (pre := pre) (ctx := ctx0) hop]
          simp [hnone]
          simp [hnone] at hfr
          exact hfr
        apply Eval.op_handled_cont
        · exact htarg
        · exact hcont
        · exact hk
      · have hsome : ∃ p, findHandlerRest pre op = some p := by
          have hne : findHandlerRest pre op ≠ none := by
            intro h_contra; apply hnone; simp [h_contra]
          have hsome' : (findHandlerRest pre op).isSome := by
            exact Option.ne_none_iff_isSome.mp hne
          exact ⟨(findHandlerRest pre op).get hsome', Option.get_mem hsome'⟩
        rcases hsome with ⟨p, hpre⟩
        have hpre' : findHandlerRest pre op = some (p.1, p.2.1, p.2.2) := by
          rw [show p = (p.1, p.2.1, p.2.2) by simp]
          exact hpre
        have htarg : findHandlerRest (pre ++ h :: ctx0) op = some (p.1, p.2.1, p.2.2 ++ h :: ctx0) := by
          rw [findHandlerRest_inert (pre := pre) (ctx := ctx0) hop]
          simp [hpre']

        simp [hpre'] at hfr
        rw [hfr.2.1.symm] at hcont
        have h_inert_k : ∀ op', CanEmit k op' → op' ∉ h.handles := by
          intro op' hkemit
          apply h_inert op'
          apply CanEmit.op_cont op arg p.1 p.2.1 k op'
          · exact mem_of_findHandlerRest_some hpre'
          · exact op_eq_of_findHandlerRest_some hpre'
          · exact hcont
          · exact hkemit
        have hk' := ihhk p.2.2 h ctx0 (show rest = p.2.2 ++ ctx0 by exact hfr.2.2.symm) h_inert_k
        rw [hfr.2.1.symm] at hk'
        rw [hfr.1.symm]
        apply Eval.op_handled_cont
        · exact htarg
        · exact hcont
        · exact hk'
    | letin x p q s s1 s2 t1 t2 hp hq ihp ihq =>
      intro pre h ctx0 h_eq h_inert
      have hp' := ihp pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.letin_left x p q op hcan))
      have hq' := ihq pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.letin_right x p q op hcan))
      apply Eval.letin
      · exact hp'
      · exact hq'
    | handle body h' s s' t hb ihb =>
      intro pre h ctx0 h_eq h_inert
      have h_inert_body : ∀ op, CanEmit body op → op ∉ h.handles :=
        fun op hcan => h_inert op (CanEmit.handle body h' op hcan)
      have h_eq' : (h' :: pre) ++ ctx0 = h' :: (pre ++ ctx0) := by simp [List.cons_append]
      rw [h_eq] at ihb
      have hb' := ihb (h' :: pre) h ctx0 h_eq' h_inert_body
      apply Eval.handle
      exact hb'
    | cond_true c t e s s' s'' tc tb hc hval ht ihc iht =>
      intro pre h ctx0 h_eq h_inert
      have hc' := ihc pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_cond c t e op hcan))
      have ht' := iht pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_t c t e op hcan))
      apply Eval.cond_true
      · exact hc'
      · exact hval
      · exact ht'
    | cond_false c t e s s' s'' tc tb hc hval he ihc ihe =>
      intro pre h ctx0 h_eq h_inert
      have hc' := ihc pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_cond c t e op hcan))
      have he' := ihe pre h ctx0 h_eq (fun op hcan => h_inert op (CanEmit.cond_e c t e op hcan))
      apply Eval.cond_false
      · exact hc'
      · exact hval
      · exact he'

theorem Eval_inert {ctx : List Handler} {h : Handler} {c : Command} {s : Nat} {t : List TraceEvent} {s' : Nat}
    (h_inert : ∀ op, CanEmit c op → op ∉ h.handles) :
    Eval (h :: ctx) c s t s' ↔ Eval ctx c s t s' :=
  Eval_inert_aux (pre := []) h_inert

end TopologySynthesis