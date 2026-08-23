import Mathlib.Tactic
import Mathlib.Logic.Relation

namespace ListDigraph

/-- A finite directed graph over a vertex type `V` with decidable equality. -/
structure Graph (V : Type) [DecidableEq V] where
  vertices : List V
  edge : V → V → Bool

variable {V : Type} [DecidableEq V]

/-- The precedence relation is the (reflexive-free) transitive closure of the
    edge relation. -/
def Graph.precedence (g : Graph V) : V → V → Prop :=
  Relation.TransGen (fun a b => g.edge a b = true)

/-- A digraph is acyclic when no vertex is reachable from itself. -/
def Graph.acyclic (g : Graph V) : Prop :=
  ∀ v, ¬ g.precedence v v

/-- A vertex is minimal in a list if no other listed vertex has precedence over it. -/
def Graph.IsMinimal (g : Graph V) (v : V) (s : List V) : Prop :=
  v ∈ s ∧ ∀ u ∈ s, ¬ g.precedence u v

/-- `AppearsBefore a b xs` means `a` occurs before `b` in the list `xs`. -/
inductive AppearsBefore (a b : V) : List V → Prop where
  | head (rest : List V) (h : b ∈ rest) : AppearsBefore a b (a :: rest)
  | tail (h : V) (rest : List V) (h_ab : AppearsBefore a b rest) :
      AppearsBefore a b (h :: rest)

end ListDigraph
