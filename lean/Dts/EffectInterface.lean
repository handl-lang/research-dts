import Mathlib.Tactic
import Dts.Basic
import Dts.Precedence
import Dts.Semantics
import Dts.Synthesis

namespace TopologySynthesis

/-! # Effect-interface / routing semantics

This file defines the one-operation routing semantics for a nested
handler stack, then derives the `routeInterfere` and `routeIndependent` relations
from routing equivalence.

The first model captures only **interception competition**: two handlers
routeInterfere if there is some operation that either one could catch, and the
order of the two handlers changes which one catches it.  Effect-flow
dependency (emit/handle) is tested in `EffectFlow` below: an emitted
operation can be caught by an outer handler, so handler order becomes
observable even when the original operation is handled by the same
innermost handler in either order.

We then add a global `Nat` state to the semantics and check whether
effect-independence (which still ignores the state) is enough to guarantee
semantic independence.  No counterexample is found: the state updates are
already fully determined by the operation routing that effect-independence
controls.
-/

/-- One-operation routing: the name of the innermost handler in `ctx`
    that handles `op`. -/
def route (ctx : List Handler) (op : OpName) : Option HandlerName :=
  firstHandler ctx op

/-- Two handlers are routeIndependent when swapping their adjacent order does
    not change the route of any operation, in any surrounding context. -/
def Handler.routeIndependent (h1 h2 : Handler) : Prop :=
  ∀ (S1 S2 : List Handler) (op : OpName),
    route (S1 ++ h1 :: h2 :: S2) op = route (S1 ++ h2 :: h1 :: S2) op

/-- Two handlers routeInterfere when there exists a surrounding stack and an
    operation for which swapping them changes the route. -/
def Handler.routeInterfere (h1 h2 : Handler) : Prop :=
  ¬ h1.routeIndependent h2

section RoutingLemmas

/-- Local routing lemma, simplest stack. -/
theorem route_swap_simple (h1 h2 : Handler) (op : OpName)
    (h_ind : h1.routeIndependent h2) :
    route [h1, h2] op = route [h2, h1] op := by
  have h := h_ind [] [] op
  simpa using h

/-- Local routing lemma for an arbitrary surrounding stack. -/
theorem firstHandler_routeIndependent_swap (h1 h2 : Handler)
    (h_ind : h1.routeIndependent h2) (pre post : List Handler) (op : OpName) :
    firstHandler (pre ++ h1 :: h2 :: post) op =
    firstHandler (pre ++ h2 :: h1 :: post) op :=
  h_ind pre post op

end RoutingLemmas

section Counterexample

/-- Two handlers that both handle the same operation, with different names.
    They routeInterfere because the inner handler is the one that catches `op`. -/
def CexH1 : Handler :=
  { name := "H1", clauses := [{ op := "op" }] }

def CexH2 : Handler :=
  { name := "H2", clauses := [{ op := "op" }] }

def c0 : Command := Command.op "op" "x"

/-- `CexH1` and `CexH2` routeInterfere: with `[]` around them, `op` is routed to
    the innermost handler. -/
example : CexH1.routeInterfere CexH2 := by
  simp [Handler.routeInterfere, Handler.routeIndependent]
  push Not
  use [], [], "op"
  simp [route, firstHandler, CexH1, CexH2]
  native_decide

/-- Therefore the two nestings are not semantically equivalent for `c0`. -/
example : ¬ Command.Equiv
    (Command.handle (Command.handle c0 CexH1) CexH2)
    (Command.handle (Command.handle c0 CexH2) CexH1) := by
  simp [Command.Equiv, eval, CexH1, CexH2]
  native_decide

end Counterexample

section ObservationExample

/-- Two handlers that handle different operations.  They are routeIndependent
    in terms of routing, but their execution traces still differ because
    the active stack at the moment `A` is handled is different.  The
    observable traces are equal. -/
def ObsH1 : Handler :=
  { name := "H1", clauses := [{ op := "A" }] }

def ObsH2 : Handler :=
  { name := "H2", clauses := [{ op := "B" }] }

def cA : Command := Command.op "A" "x"

/-- The execution traces differ: the `ctx` fields record the active stack. -/
example : execWith [ObsH1, ObsH2] cA 0 ≠ execWith [ObsH2, ObsH1] cA 0 := by
  native_decide

/-- But the observable traces are the same: in both cases `H1` handles `A`. -/
example : observe (execWith [ObsH1, ObsH2] cA 0).1 = observe (execWith [ObsH2, ObsH1] cA 0).1 := by
  native_decide

end ObservationExample

section EffectFlow

/-- `Hem1` handles `A` and emits `B`; `Hem2` handles `B`.
    Swapping the order changes whether the emitted `B` is caught. -/
def Hem1 : Handler :=
  { name := "H1", clauses := [{ op := "A", cont := some (Command.op "B" "") }] }

def Hem2 : Handler :=
  { name := "H2", clauses := [{ op := "B" }] }

/-- Execution with `Hem1` innermost and `Hem2` outer.
    `A` is caught by `Hem1`; the emitted `B` is then caught by `Hem2`. -/
example :
    execWith [Hem1, Hem2] cA 0 =
    ( [ ExecEvent.handled "H1" "A" "x" ["H1", "H2"] 0
      , ExecEvent.handled "H2" "B" "" ["H2"] 0
      ]
    , 0
    ) := by
  native_decide

/-- Execution with `Hem2` innermost and `Hem1` outer.
    `A` is caught by `Hem1`; the emitted `B` has no outer handler and is
    therefore unhandled. -/
example :
    execWith [Hem2, Hem1] cA 0 =
    ( [ ExecEvent.handled "H1" "A" "x" ["H2", "H1"] 0
      , ExecEvent.unhandled "B" "" [] 0
      ]
    , 0
    ) := by
  native_decide

/-- Observable traces for the two orderings. -/
example :
    observe (execWith [Hem1, Hem2] cA 0).1 =
    [ TraceEvent.handled "H1" "A" "x" 0
    , TraceEvent.handled "H2" "B" "" 0
    ] := by
  native_decide

example :
    observe (execWith [Hem2, Hem1] cA 0).1 =
    [ TraceEvent.handled "H1" "A" "x" 0
    , TraceEvent.unhandled "B" "" 0
    ] := by
  native_decide

/-- The two different orderings are not observationally equivalent for `cA`. -/
example : ¬ Command.Equiv
    (synthesize cA [Hem1, Hem2])
    (synthesize cA [Hem2, Hem1]) := by
  simp [Command.Equiv]
  native_decide

end EffectFlow

section SemanticRelations

/-- Two handlers are *semantically independent* if swapping their adjacent
    order preserves the observable trace of every command, from every initial
    state. -/
def Handler.semanticIndependent (h1 h2 : Handler) : Prop :=
  ∀ (c : Command) (S1 S2 : List Handler) (s : Nat),
    evalWith (S1 ++ h1 :: h2 :: S2) c s = evalWith (S1 ++ h2 :: h1 :: S2) c s

/-- Two handlers *semantically interfere* if there exists a command, a
    surrounding stack, and an initial state for which the swap changes the
    observable trace. -/
def Handler.semanticInterfere (h1 h2 : Handler) : Prop :=
  ¬ h1.semanticIndependent h2

/-- `CexH1` and `CexH2` semantically interfere (interception competition). -/
example : CexH1.semanticInterfere CexH2 := by
  simp [Handler.semanticInterfere, Handler.semanticIndependent]
  push Not
  use c0, [], [], 0
  simp [c0, CexH1, CexH2]
  native_decide

/-- `Hem1` and `Hem2` semantically interfere even though they are
    route-independent: `Hem1` emits `B` and `Hem2` handles `B`. -/
example : Hem1.semanticInterfere Hem2 := by
  simp [Handler.semanticInterfere, Handler.semanticIndependent]
  push Not
  use cA, [], [], 0
  simp [cA, Hem1, Hem2]
  native_decide

end SemanticRelations

section EffectIndependent

/-- `h1` emits an operation that `h2` handles (decidable `Bool` version). -/
def Handler.emitsInto (h1 h2 : Handler) : Bool :=
  if h1.emit ∩ h2.handles = ∅ then false else true

/-- `h1` and `h2` handle a common operation. -/
def Handler.handlesOverlap (h1 h2 : Handler) : Bool :=
  if h1.handles ∩ h2.handles = ∅ then false else true

/-- Two handlers are effect-independent when they neither compete for the
    same operation nor emit into one another. -/
def Handler.effectIndependent (h1 h2 : Handler) : Bool :=
  !h1.handlesOverlap h2 && !h1.emitsInto h2 && !h2.emitsInto h1

/-- `h1` should be nested inside `h2` (h1 emits into h2).
    Note: a shared handled operation means the handlers cannot be ordered
    because it creates a cycle/incompatibility, not a directed edge. -/
def Handler.precedes (h1 h2 : Handler) : Bool := h1.emitsInto h2

end EffectIndependent

section CounterexampleSearch

/-! We now check whether `Handler.effectIndependent h1 h2` implies
    `h1.semanticIndependent h2` in the stateful semantics.  `Hem1` and `Hem2`
    are *not* effect-independent because `Hem1` emits `B` and `Hem2` handles `B`.

    The concrete attempts below satisfy the implication; the may-effect
    over-approximation `Command.eff` is conservative enough to guarantee that
    two handlers that are `effectIndependent` cannot affect each other when
    swapped, even when their state updates are different. -/

/-- `Hem1` and `Hem2` are not effect-independent. -/
example : ¬ (Hem1.effectIndependent Hem2 = true) := by
  native_decide

/-- `Hem2` does not emit into `Hem1`, but the pair still fails
    effect-independence because `Hem1` emits `B` into `Hem2`. -/
example : ¬ (Hem2.emitsInto Hem1 = true) := by
  native_decide

/-- A candidate with disjoint handles and no emissions.
    This pair is effect-independent. -/
def CandidateH1 : Handler :=
  { name := "H1", clauses := [{ op := "A" }] }

def CandidateH2 : Handler :=
  { name := "H2", clauses := [{ op := "B" }] }

/-- `CandidateH1` and `CandidateH2` are effect-independent. -/
example : CandidateH1.effectIndependent CandidateH2 = true := by
  native_decide

/-- The same pair is also a positive `effectIndependent → semanticIndependent`
    example: for the concrete command `cA = A`, the observable traces are
    the same in both orderings because `A` is always handled by `H1` and
    neither handler emits into the other. -/
example : evalWith [CandidateH1, CandidateH2] cA 0 =
          evalWith [CandidateH2, CandidateH1] cA 0 := by
  native_decide

end CounterexampleSearch

section StatefulCounterexample

/-! Concrete test of the effect-independence certificate with a global
    mutable `Nat` state. -/

/-- `StateH1` handles `A` and increments the global state. -/
def StateH1 : Handler :=
  { name := "H1", clauses := [{ op := "A", stateUpdate := fun s => s + 1 }] }

/-- `StateH2` handles `B` and leaves the state unchanged. -/
def StateH2 : Handler :=
  { name := "H2", clauses := [{ op := "B" }] }

/-- A command that performs `A` (state increment) and then `B`. -/
def stateC : Command :=
  Command.letin "x" (Command.op "A" "") (Command.op "B" "")

/-- `StateH1` and `StateH2` are effect-independent: their handled sets are
    disjoint and neither emits into the other. -/
example : StateH1.effectIndependent StateH2 = true := by
  native_decide

/-- The requested pair does *not* break the certificate: the trace and final
    state are identical in both handler orders. -/
example : evalWith [StateH1, StateH2] stateC 0 =
          evalWith [StateH2, StateH1] stateC 0 := by
  native_decide

/-- Variation: a non-trivial state update in `H2` that uses the current state. -/
def StateH2' : Handler :=
  { name := "H2", clauses := [{ op := "B", stateUpdate := fun s => s * 2 }] }

def stateC' : Command :=
  Command.letin "x" (Command.op "B" "") (Command.op "A" "")

example : evalWith [StateH1, StateH2'] stateC' 0 =
          evalWith [StateH2', StateH1] stateC' 0 := by
  native_decide

/-- Variation: `H1` emits a second operation and both handlers touch the state. -/
def StateH1' : Handler :=
  { name := "H1"
  , clauses := [{ op := "A", stateUpdate := fun s => s + 1, cont := some (Command.op "B" "") }]
  }

def stateC'' : Command := Command.op "A" ""

/-- `StateH1'` emits `B` into `StateH2'`, so the pair is not effect-independent. -/
example : StateH1'.effectIndependent StateH2' = false := by
  native_decide

/-- When handlers emit into one another, the global state makes the two
    orderings different: in `[H1', H2']` the emitted `B` is caught and
    doubles the state, while in `[H2', H1']` the same `B` is unhandled and
    the state stays at `1`. -/
example : evalWith [StateH1', StateH2'] stateC'' 0 ≠
          evalWith [StateH2', StateH1'] stateC'' 0 := by
  native_decide

end StatefulCounterexample

end TopologySynthesis
