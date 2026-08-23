import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.Unbundled
import Dts.Basic

set_option linter.style.haveILetI false

namespace TopologySynthesis

-- Section 3: Precedence model

/-- Precedence is a relation on handlers (not just their names),
    matching the types used by `synthesize` and `AppearsBefore`. -/
def Precedence := Handler → Handler → Bool

/-- The `Prop`-valued reading of a `Bool` precedence relation. -/
def precRel (r : Precedence) (a b : Handler) : Prop := r a b = true

def Precedence.irreflexive (r : Precedence) : Prop := ∀ h, ¬ r h h = true
def Precedence.transitive (r : Precedence) : Prop :=
  ∀ a b c, r a b = true → r b c = true → r a c = true
def Precedence.asymmetric (r : Precedence) : Prop :=
  ∀ a b, r a b = true → ¬ r b a = true

/-- A partial order is irreflexive and transitive. Asymmetry is derivable
    (see `irreflexive_transitive_implies_asymmetric`), so it is not
    included as a separate conjunct. -/
def Precedence.isPartialOrder (r : Precedence) : Prop :=
  Precedence.irreflexive r ∧ Precedence.transitive r

/-- Asymmetry follows from irreflexivity and transitivity. -/
theorem irreflexive_transitive_implies_asymmetric
    (r : Precedence) (hirr : Precedence.irreflexive r)
    (htr : Precedence.transitive r) : Precedence.asymmetric r := by
  haveI : IsTrans Handler (precRel r) := ⟨fun _ _ _ hab hbc => htr _ _ _ hab hbc⟩
  haveI : Std.Irrefl (precRel r) := ⟨hirr⟩
  haveI ha : Std.Asymm (precRel r) := by infer_instance
  intro a b hab
  exact ha.asymm a b hab

/-- Reachability in the precedence relation is the transitive closure. -/
def Reachable (r : Precedence) : Handler → Handler → Prop :=
  Relation.TransGen (precRel r)

def Precedence.acyclic (r : Precedence) : Prop := ∀ h, ¬ Reachable r h h

/-- The transitive closure of a transitive relation is contained in the
    relation itself. -/
theorem reachable_implies_edge
    (r : Precedence) (htr : Precedence.transitive r)
    (a b : Handler) (reach : Reachable r a b) : r a b = true := by
  haveI : IsTrans Handler (precRel r) := ⟨fun _ _ _ hab hbc => htr _ _ _ hab hbc⟩
  simpa [Reachable, precRel, Relation.transGen_eq_self (r := precRel r)] using reach

/-- **Proposition 0**: A partial order (irreflexive + transitive) is acyclic. -/
theorem partialOrder_acyclic
    (r : Precedence) (hpo : Precedence.isPartialOrder r) :
    Precedence.acyclic r := by
  obtain ⟨h_irrefl, h_tr⟩ := hpo
  haveI : IsTrans Handler (precRel r) := ⟨fun _ _ _ hab hbc => h_tr _ _ _ hab hbc⟩
  intro h h_cycle
  exact h_irrefl h (by simpa [Reachable, precRel, Relation.transGen_eq_self (r := precRel r)] using h_cycle)

end TopologySynthesis
