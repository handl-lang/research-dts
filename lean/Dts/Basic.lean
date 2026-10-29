import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-
# Declarative Handler Topology Synthesis for Arrow Effects
Lean 4 formalization. All proofs complete (no sorry).

## Summary

- `irreflexive_transitive_implies_asymmetric`: asymmetry is derivable
- `partialOrder_acyclic`: partial orders (irreflexive + transitive) are acyclic
- `synthesize_well_formed`: synthesis preserves well-formedness (non-empty handlers)
- `synthesize_preserves_precedence`: if `hi` appears before `hj` in the ordered
  list, `hi` is nested inside `hj` in the synthesized term
- `synthesize_static_topology`: synthesis preserves staticity (no runtime branching)
- `synthesize_completeness`: if `ordered` is a linear extension of `prec`, every
  precedence constraint is realized in the synthesized term
- `exists_linear_extension`: for any finite acyclic precedence relation,
  a linear extension exists (topological sort soundness)

## Assumptions

None. All proofs are complete, including topological sort soundness.

## Module structure

- `Basic.lean` — core types: `Command`, `Handler`, `isStatic`, `isWellFormed`
- `Precedence.lean` — `Precedence`, partial order, `Reachable`, acyclicity
- `Synthesis.lean` — `synthesize`, well-formedness, precedence preservation, staticity, completeness
- `TopoSort.lean` — `removeAll`, `exists_minimal`, `exists_linear_extension`
-/

namespace TopologySynthesis

abbrev OpName := String
abbrev HandlerName := String

/-- A handler clause captures one operation `op` and an optional continuation. -/
structure HandlerClauseCore (α : Type) where
  op : OpName
  cont : Option α := none
  stateUpdate : Nat → Nat := id

/-- A handler is a named list of clauses. The continuation type `α` is a
    parameter so that we can break the type dependency cycle: a `Command` will
    use `Handler Command` and a `Handler Command` will use `Command` in its
    continuations. -/
structure HandlerCore (α : Type) where
  name : HandlerName
  clauses : List (HandlerClauseCore α)

/-- A command in the arrow-effect calculus.
    `cond` represents runtime conditional branching — its presence makes
    a term non-static. -/
inductive Command where
  | pure (val : String)
  | op (name : OpName) (arg : String)
  | letin (x : String) (p : Command) (q : Command)
  | handle (body : Command) (handler : HandlerCore Command)
  | cond (c : Command) (t : Command) (e : Command)

-- Concrete names for the command-continuation version used throughout the model.
abbrev HandlerClause := HandlerClauseCore Command
abbrev Handler := HandlerCore Command

/-- Operations handled by a handler (as a list). -/
def Handler.handlesList (h : Handler) : List OpName :=
  h.clauses.map (·.op)

/-- Operations handled by a handler. -/
def Handler.handles (h : Handler) : Finset OpName :=
  h.handlesList.toFinset

mutual
  /-- May-effect over-approximation of a command. -/
  partial def Command.eff (cmd : Command) : Finset OpName :=
    match cmd with
    | .pure _ => ∅
    | .op name _ => {name}
    | .letin _ p q => p.eff ∪ q.eff
    | .handle body h => (body.eff \ Handler.handles h) ∪ Handler.emit h
    | .cond c t e => c.eff ∪ t.eff ∪ e.eff

  /-- Operations emitted by a handler (derived from continuation clauses). -/
  partial def Handler.emit (h : Handler) : Finset OpName :=
    emitClauses h.clauses

  partial def emitClauses (cs : List HandlerClause) : Finset OpName :=
    match cs with
    | [] => ∅
    | c :: cs' =>
        (match c.cont with
         | some k => k.eff
         | none => ∅) ∪
        emitClauses cs'
end

/-- A term is static iff it contains no `cond` (runtime branching). -/
def Command.isStatic : Command → Bool
  | .pure _ => true
  | .op _ _ => true
  | .letin _ p q => p.isStatic && q.isStatic
  | .handle body _ => body.isStatic
  | .cond _ _ _ => false

/-- A term is well-formed iff every handler has at least one clause
    and all sub-terms are well-formed. -/
def Command.isWellFormed : Command → Bool
  | .pure _ => true
  | .op _ _ => true
  | .letin _ p q => p.isWellFormed && q.isWellFormed
  | .handle body handler => handler.clauses.length > 0 && body.isWellFormed
  | .cond c t e => c.isWellFormed && t.isWellFormed && e.isWellFormed

/-- Decidable equality on handlers is required by the topological-sort
    machinery, but it is not computable because it would need to compare
    continuation commands recursively. The `Graph` and `TopoSort` proofs use
    this only to reason about finite lists of concrete handlers. -/
noncomputable instance : DecidableEq Handler :=
  fun _ _ => Classical.propDecidable _

end TopologySynthesis
