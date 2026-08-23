import Mathlib.Tactic
import Dts.Basic

namespace TopologySynthesis

-- Section 3: Precedence model

/-- Precedence is a relation on handlers (not just their names),
    matching the types used by `synthesize` and `AppearsBefore`. -/
def Precedence := Handler → Handler → Bool

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
  intro a b hab hba
  exact absurd (htr a b a hab hba) (hirr a)

inductive Reachable (r : Precedence) : Handler → Handler → Prop where
  | one (a b : Handler) (h : r a b = true) : Reachable r a b
  | reach_trans (a b c : Handler) (h1 : Reachable r a b) (h2 : Reachable r b c) :
    Reachable r a c

def Precedence.acyclic (r : Precedence) : Prop := ∀ h, ¬ Reachable r h h

theorem reachable_implies_edge
    (r : Precedence) (htr : Precedence.transitive r)
    (a b : Handler) (reach : Reachable r a b) : r a b = true := by
  induction reach with
  | one _ _ h => exact h
  | reach_trans _ _ _ _ _ ih1 ih2 => exact htr _ _ _ ih1 ih2

/-- **Proposition 0**: A partial order (irreflexive + transitive) is acyclic. -/
theorem partialOrder_acyclic
    (r : Precedence) (hpo : Precedence.isPartialOrder r) :
    Precedence.acyclic r := by
  obtain ⟨h_irrefl, h_tr⟩ := hpo
  intro h h_cycle
  exact absurd (reachable_implies_edge r h_tr h h h_cycle) (h_irrefl h)

end TopologySynthesis
