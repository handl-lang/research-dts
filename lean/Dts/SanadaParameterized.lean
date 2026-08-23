import Dts.SanadaStrong

namespace SanadaParameterized

open SanadaStrong

/-! # Phase 3–5: concrete parameterized one-operation model

A minimal, buildable instantiation of Sanada's parameterized
strong-promonad semantics.  The carrier `Term S γ δ B₀` is the free algebra of
one operation with parameter `S`; the profunctor is the representable one
`P S γ δ A B = A → Term S γ δ B`.  The handler `h : γ → δ` induces the
`P`-algebra on `B₀` via `eval h`, and we prove the preservation equation.
-/

/-- The free one-operation algebra with parameter `S`.
    A closed `B₀`-valued term. -/
inductive Term (S γ δ : Type) (B0 : Type) : Type where
  | pure : B0 → Term S γ δ B0
  | op : γ → S → (δ × S → Term S γ δ B0) → Term S γ δ B0

/-- The representable profunctor `P S γ δ A B = A → Term S γ δ B`. -/
def P (S γ δ : Type) (A B : Type) : Type := A → Term S γ δ B

section Profunctor

/-- Functorial action of `Term` on the value type. -/
def termMap (S γ δ : Type) {B B' : Type} (g : B → B') :
    Term S γ δ B → Term S γ δ B'
  | .pure b => .pure (g b)
  | .op z s k => .op z s (fun (d, s') => termMap S γ δ g (k (d, s')))

/-- Kleisli composition / substitution in `Term`. -/
def termBind (S γ δ : Type) {B C : Type} (t : Term S γ δ B)
    (q : B → Term S γ δ C) : Term S γ δ C :=
  match t with
  | .pure b => q b
  | .op z s k => .op z s (fun (d, s') => termBind S γ δ (k (d, s')) q)

/-- Left map: precompose with a function on the source. -/
def lmap (S γ δ : Type) {A A' B : Type} (f : A' → A) (p : P S γ δ A B) :
    P S γ δ A' B :=
  fun x => p (f x)

/-- Right map: postcompose with `termMap` on the target. -/
def rmap (S γ δ : Type) {A B B' : Type} (g : B → B') (p : P S γ δ A B) :
    P S γ δ A B' :=
  fun x => termMap S γ δ g (p x)

/-- Unit: a pure function `A → B` becomes `A → Term S γ δ B`. -/
def eta (S γ δ : Type) {A B : Type} (f : A → B) : P S γ δ A B :=
  fun x => .pure (f x)

/-- Kleisli composition: `bind p q` is `p` followed by `q`. -/
def bind (S γ δ : Type) {A B C : Type} (p : P S γ δ A B) (q : P S γ δ B C) :
    P S γ δ A C :=
  fun x => termBind S γ δ (p x) q

end Profunctor

section Algebras

/-- Evaluate a `Term S γ δ B₀` to a handled `B₀` using `h : γ → δ`. -/
def eval (S γ δ : Type) {B0 : Type} (h : γ → δ) : Term S γ δ B0 → B0
  | .pure b => b
  | .op z s k => eval S γ δ h (k (h z, s))

/-- The free `P`-algebra on `B₀`.
    Carrier is `Term S γ δ B₀`; the action is the `termBind` / `join`. -/
def act_Free (S γ δ : Type) {A B0 : Type}
    (p : P S γ δ A (Term S γ δ B0)) : A → Term S γ δ B0 :=
  fun x => termBind S γ δ (p x) (fun t => t)

/-- The handled `P`-algebra on `B₀` for a handler `h : γ → δ`.
    The operation's result is transformed by `h` before the continuation runs. -/
def act_H (S γ δ : Type) {A B0 : Type} (h : γ → δ) (p : P S γ δ A B0) :
    A → B0 :=
  fun x => eval S γ δ h (p x)

/-- The handler-induced operation interpretation
    `[[Q^op]]_S : A_Σ^*(δ × S, D) → A_Σ^*(γ × S, D)`
    is given by pre-composing the continuation with `h` on the result value. -/
def Q_op (S γ δ : Type) {B : Type} (h : γ → δ) (k : P S γ δ (δ × S) B) :
    P S γ δ (γ × S) B :=
  lmap S γ δ (fun (b, s') => (h b, s')) k

end Algebras

section Theorems

/-- Multiplication law for `eval`: joining then evaluating is the same as
    mapping `eval` over the inner terms and then evaluating.  This is the
    algebra-homomorphism equation for the free `Term`-algebra. -/
lemma eval_join (S γ δ : Type) {B0 : Type} (h : γ → δ)
    (t : Term S γ δ (Term S γ δ B0)) :
    eval S γ δ h (termBind S γ δ t (fun t => t)) =
    eval S γ δ h (termMap S γ δ (eval S γ δ h) t) := by
  induction t with
  | pure b =>
    simp [termBind, termMap, eval]
  | op z s k ih =>
    simp [termBind, termMap, eval]
    apply ih

/-- Nontrivial handler theorem: the unique map `eval h` preserves the `P`-action.
    This shows the operation's result may be transformed by `h` while the
    continuation is preserved. -/
theorem eval_preserves (S γ δ : Type) {A B0 : Type} (h : γ → δ)
    (p : P S γ δ A (Term S γ δ B0)) (x : A) :
    eval S γ δ h (act_Free S γ δ p x) =
    act_H S γ δ h (rmap S γ δ (eval S γ δ h) p) x := by
  simp [act_Free, act_H, rmap]
  apply eval_join S γ δ h (p x)

end Theorems
