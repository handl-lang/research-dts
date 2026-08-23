import Mathlib.Tactic

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

structure HandlerClause where
  op : OpName
  deriving DecidableEq

structure Handler where
  name : HandlerName
  clauses : List HandlerClause
  deriving DecidableEq

/-- A command in the arrow-effect calculus.
    `cond` represents runtime conditional branching — its presence makes
    a term non-static. -/
inductive Command where
  | pure (val : String)
  | op (name : OpName) (arg : String)
  | letin (x : String) (p : Command) (q : Command)
  | handle (body : Command) (handler : Handler)
  | cond (c : Command) (t : Command) (e : Command)

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

end TopologySynthesis
