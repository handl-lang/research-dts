import Mathlib.Tactic
import Dts.Basic

namespace TopologySynthesis

/-! # A two-level trace semantics for `Command` with global mutable state

`ExecEvent` records the full execution, including the active handler stack
and the current global state for every event.  `TraceEvent` is the
observable trace, with the context stripped out but the state preserved.

This gives us three layers:

- execution semantics: `exec` / `execWith` (produces `ExecEvent`)
- observation: `ExecEvent.observe` / `observe`
- program equivalence: `Command.Equiv` (equality of observed traces)
-/

/-- An observable event during execution. The current global state is recorded. -/
inductive TraceEvent where
  | pure (val : String) (state : Nat)
  | handled (handler : HandlerName) (op : OpName) (arg : String) (state : Nat)
  | unhandled (op : OpName) (arg : String) (state : Nat)
  deriving DecidableEq, Repr

/-- An execution event. Includes the active handler stack and current state. -/
inductive ExecEvent where
  | pure (val : String) (ctx : List HandlerName) (state : Nat)
  | handled (handler : HandlerName) (op : OpName) (arg : String) (ctx : List HandlerName) (state : Nat)
  | unhandled (op : OpName) (arg : String) (ctx : List HandlerName) (state : Nat)
  deriving DecidableEq, Repr

/-- Observation: forget the handler stack context, but keep the state. -/
def ExecEvent.observe : ExecEvent → TraceEvent
  | .pure val _ s => .pure val s
  | .handled h o a _ s => .handled h o a s
  | .unhandled o a _ s => .unhandled o a s

/-- Lift observation to lists of events. -/
def observe (es : List ExecEvent) : List TraceEvent :=
  es.map ExecEvent.observe

/-- Does `h` contain a clause for `op`? -/
def handlerHandles (h : Handler) (op : OpName) : Bool :=
  h.clauses.any (fun c => c.op == op)

/-- Find the innermost handler in `ctx` that handles `op`, also returning
    the matching clause and the remaining context outside that handler. -/
def findHandlerRest (ctx : List Handler) (op : OpName) : Option (Handler × HandlerClause × List Handler) :=
  match ctx with
  | [] => none
  | h :: rest =>
      match h.clauses.find? (fun c => c.op == op) with
      | some c => some (h, c, rest)
      | none => findHandlerRest rest op

/-- Find the innermost handler in `ctx` that handles `op`.
    The context is ordered innermost-first. -/
def firstHandler (ctx : List Handler) (op : OpName) : Option HandlerName :=
  findHandlerRest ctx op |>.map (fun (h, _, _) => h.name)

/-- The value of the last `pure` event, defaulting to "" if none. -/
def lastTraceVal (trace : List TraceEvent) : String :=
  trace.foldl (fun acc e =>
    match e with
    | .pure v _ => v
    | _ => acc) ""

/-- The value of the last `pure` execution event, defaulting to "" if none. -/
def lastExecVal (es : List ExecEvent) : String :=
  es.foldl (fun acc e =>
    match e with
    | .pure v _ _ => v
    | _ => acc) ""

mutual
  /-- Observable trace for a single operation call.  `ctx` is the active
      handler stack; the definition recurses on it to find the innermost
      handler.  If a clause has a continuation command, that command is
      evaluated in the context outside the handler that caught the
      original operation.  The handler's `stateUpdate` is applied to the
      current global state. -/
  partial def evalOp (ctx : List Handler) (op : OpName) (arg : String) (s : Nat) : List TraceEvent × Nat :=
    match ctx with
    | [] => ([TraceEvent.unhandled op arg s], s)
    | h :: rest =>
        match h.clauses.find? (fun c => c.op == op) with
        | some c =>
            let t := [TraceEvent.handled h.name op arg s]
            let s' := c.stateUpdate s
            match c.cont with
            | some k =>
                let (t', s'') := evalWith rest k s'
                (t ++ t', s'')
            | none => (t, s')
        | none => evalOp rest op arg s

  /-- Observable trace semantics. The `cond` case uses the last `pure`
      value to choose the branch. -/
  partial def evalWith (ctx : List Handler) : Command → Nat → List TraceEvent × Nat
    | .pure val, s => ([TraceEvent.pure val s], s)
    | .op name arg, s => evalOp ctx name arg s
    | .letin _ p q, s =>
        let (t1, s1) := evalWith ctx p s
        let (t2, s2) := evalWith ctx q s1
        (t1 ++ t2, s2)
    | .handle body h, s => evalWith (h :: ctx) body s
    | .cond c t e, s =>
        let (tc, s') := evalWith ctx c s
        let v := lastTraceVal tc
        let (tb, s'') := if v == "true" then evalWith ctx t s' else evalWith ctx e s'
        (tc ++ tb, s'')
end

/-- Top-level observable trace of a command. -/
def eval (c : Command) : List TraceEvent := (evalWith [] c 0).1

/-- Semantic equivalence is equality of observable traces. -/
def Command.Equiv (c1 c2 : Command) : Prop := eval c1 = eval c2

mutual
  /-- Execution trace for a single operation call.  `full` records the
      complete active stack for the event; `ctx` is the search suffix.
      When a handler is found, the continuation command is executed with
      `full` reset to the handlers outside that handler. -/
  partial def execOp (ctx full : List Handler) (op : OpName) (arg : String) (s : Nat) : List ExecEvent × Nat :=
    match ctx with
    | [] => ([ExecEvent.unhandled op arg (full.map (·.name)) s], s)
    | h :: rest =>
        match h.clauses.find? (fun c => c.op == op) with
        | some c =>
            let e := [ExecEvent.handled h.name op arg (full.map (·.name)) s]
            let s' := c.stateUpdate s
            match c.cont with
            | some k =>
                let (es, s'') := execWith rest k s'
                (e ++ es, s'')
            | none => (e, s')
        | none => execOp rest full op arg s

  /-- Execution semantics. Records the active handler stack and current state. -/
  partial def execWith (ctx : List Handler) : Command → Nat → List ExecEvent × Nat
    | .pure val, s => ([ExecEvent.pure val (ctx.map (·.name)) s], s)
    | .op name arg, s => execOp ctx ctx name arg s
    | .letin _ p q, s =>
        let (t1, s1) := execWith ctx p s
        let (t2, s2) := execWith ctx q s1
        (t1 ++ t2, s2)
    | .handle body h, s => execWith (h :: ctx) body s
    | .cond c t e, s =>
        let (tc, s') := execWith ctx c s
        let v := lastExecVal tc
        let (tb, s'') := if v == "true" then execWith ctx t s' else execWith ctx e s'
        (tc ++ tb, s'')
end

/-- Top-level execution trace of a command. -/
def exec (c : Command) : List ExecEvent := (execWith [] c 0).1

end TopologySynthesis
