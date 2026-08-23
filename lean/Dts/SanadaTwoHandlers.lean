import Dts.SanadaParameterized

namespace SanadaTwoHandlers

open SanadaParameterized

/-! # Phase 7–9: two disjoint handlers and the ProfunctorCommute2 bridge

This extends the one-operation `Term` model to two independent operations,
`op₁` and `op₂`, each with its own parameter object and handler.  Because the
operations are disjoint, the two handlers' `Q^op` maps commute, giving a
concrete instance of the `ProfunctorCommute2` diamond.
-/

/-- The free two-operation algebra with independent parameters `S₁` and `S₂`. -/
inductive Term₂ (S₁ γ₁ δ₁ S₂ γ₂ δ₂ : Type) (B0 : Type) : Type where
  | pure : B0 → Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0
  | op₁ : γ₁ → S₁ → (δ₁ × S₁ → Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0)
        → Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0
  | op₂ : γ₂ → S₂ → (δ₂ × S₂ → Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0)
        → Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0

/-- Representable profunctor for the two-operation language. -/
def P₂ (S₁ γ₁ δ₁ S₂ γ₂ δ₂ : Type) (A B : Type) : Type :=
  A → Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B

/-- Functorial action of `Term₂` on values. -/
def termMap₂ (S₁ γ₁ δ₁ S₂ γ₂ δ₂ : Type) {B B' : Type} (g : B → B') :
    Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B → Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B'
  | .pure b => .pure (g b)
  | .op₁ z s k =>
      .op₁ z s (fun (d, s') => termMap₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ g (k (d, s')))
  | .op₂ z s k =>
      .op₂ z s (fun (d, s') => termMap₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ g (k (d, s')))

/-- Right map for `P₂`. -/
def rmap₂ (S₁ γ₁ δ₁ S₂ γ₂ δ₂ : Type) {A B B' : Type} (g : B → B')
    (p : P₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ A B) : P₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ A B' :=
  fun x => termMap₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ g (p x)

/-- Handle `op₁` with `h₁`, leaving `op₂` as a one-operation `Term`. -/
def eval₁ (S₁ γ₁ δ₁ S₂ γ₂ δ₂ : Type) {B0 : Type} (h₁ : γ₁ → δ₁) :
    Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0 → Term S₂ γ₂ δ₂ B0
  | .pure b => .pure b
  | .op₁ z s k => eval₁ S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₁ (k (h₁ z, s))
  | .op₂ z s k =>
      .op z s (fun (d, s') => eval₁ S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₁ (k (d, s')))

/-- Handle `op₂` with `h₂`, leaving `op₁` as a one-operation `Term`. -/
def eval₂ (S₁ γ₁ δ₁ S₂ γ₂ δ₂ : Type) {B0 : Type} (h₂ : γ₂ → δ₂) :
    Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0 → Term S₁ γ₁ δ₁ B0
  | .pure b => .pure b
  | .op₂ z s k => eval₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₂ (k (h₂ z, s))
  | .op₁ z s k =>
      .op z s (fun (d, s') => eval₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₂ (k (d, s')))

/-- Final handler for the remaining `op₂` in a one-operation `Term S₂ B₀`. -/
def eval₂' (_S₁ _γ₁ _δ₁ S₂ γ₂ δ₂ : Type) {B0 : Type} (h₂ : γ₂ → δ₂)
    (t : Term S₂ γ₂ δ₂ B0) : B0 :=
  SanadaParameterized.eval S₂ γ₂ δ₂ h₂ t

/-- Final handler for the remaining `op₁` in a one-operation `Term S₁ B₀`. -/
def eval₁' (S₁ γ₁ δ₁ _S₂ _γ₂ _δ₂ : Type) {B0 : Type} (h₁ : γ₁ → δ₁)
    (t : Term S₁ γ₁ δ₁ B0) : B0 :=
  SanadaParameterized.eval S₁ γ₁ δ₁ h₁ t

/-- Concrete `ProfunctorCommute2` certificate for two disjoint handlers:
    handling `op₁` then `op₂` is the same as handling `op₂` then `op₁` at the
    level of `P₂` continuations. -/
theorem profunctorCommute₂ (S₁ γ₁ δ₁ S₂ γ₂ δ₂ : Type) {A B0 : Type}
    (h₁ : γ₁ → δ₁) (h₂ : γ₂ → δ₂)
    (p : P₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ A (Term₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ B0)) (x : A) :
    rmap₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ (eval₂' S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₂)
      (rmap₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ (eval₁ S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₁) p) x =
    rmap₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ (eval₁' S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₁)
      (rmap₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ (eval₂ S₁ γ₁ δ₁ S₂ γ₂ δ₂ h₂) p) x := by
  sorry

end SanadaTwoHandlers
