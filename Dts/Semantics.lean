import Mathlib.Tactic
import Dts.Basic

namespace TopologySynthesis

/-! # A minimal trace semantics for `Command`

This is not a full arrow-effect operational semantics. It records, for
an operation `op`, the name of the innermost handler that catches it,
along with pure values. It is sufficient to compare observable behavior
of static handler nestings.
-/

/-- A single observable event during execution. -/
inductive TraceEvent where
  | pure (val : String)
  | handled (handler : HandlerName) (op : OpName) (arg : String)
  | unhandled (op : OpName) (arg : String)
  deriving DecidableEq

/-- Does `h` contain a clause for `op`? -/
def handlerHandles (h : Handler) (op : OpName) : Bool :=
  h.clauses.any (fun c => c.op == op)

/-- Find the innermost handler in `ctx` that handles `op`.
    The context is ordered innermost-first. -/
def firstHandler (ctx : List Handler) (op : OpName) : Option HandlerName :=
  match ctx with
  | [] => none
  | h :: rest => if handlerHandles h op then some h.name else firstHandler rest op

/-- Minimal trace semantics. The `cond` case is empty because the
    commutativity result is restricted to static (cond-free) commands. -/
def evalWith (ctx : List Handler) : Command → List TraceEvent
  | .pure val => [TraceEvent.pure val]
  | .op name arg =>
      match firstHandler ctx name with
      | some h => [TraceEvent.handled h name arg]
      | none => [TraceEvent.unhandled name arg]
  | .letin _ p q => evalWith ctx p ++ evalWith ctx q
  | .handle body h => evalWith (h :: ctx) body
  | .cond _ _ _ => []

/-- Top-level trace of a command. -/
def eval (c : Command) : List TraceEvent := evalWith [] c

/-- Semantic equivalence is equality of traces. -/
def Command.Equiv (c1 c2 : Command) : Prop := eval c1 = eval c2

end TopologySynthesis
