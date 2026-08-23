import Mathlib.Tactic

namespace SanadaPromonad

/-!
# Phase 0–2: a minimal strong-promonad model for arrow-handler commutativity

This is the first milestone of the Sanada-style arrow-handler investigation.
We set up the smallest categorical machinery needed to ask the core question:

1. a small category `SCategory`
2. a `Profunctor` over it
3. a `Promonad` in Kleisli form
4. `PromonadAlgebra` (object with a P-action)
5. `PromonadHom` (handler as algebra homomorphism)
6. handler composition
7. the open commutativity conjecture

The model is intentionally skeletal.  Full `Prof` construction, strength, and
arrow syntax are deferred.  The objective is to expose the algebraic core and
let the proof obligations for commutativity drive the next definitions.
-/

/-- A small category with explicit objects and hom-sets. -/
structure SCategory where
  Obj : Type
  Hom : Obj → Obj → Type
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  id_comp : ∀ {X Y} (f : Hom X Y), comp (id Y) f = f
  comp_id : ∀ {X Y} (f : Hom X Y), comp f (id X) = f
  comp_assoc : ∀ {X Y Z W} (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y),
    comp h (comp g f) = comp (comp h g) f

/-- A profunctor `P : C^op × C → Set` in the small model. -/
structure Profunctor (C : SCategory) where
  P : C.Obj → C.Obj → Type
  lmap : {X X' Y : C.Obj} → C.Hom X' X → P X Y → P X' Y
  rmap : {X Y Y' : C.Obj} → C.Hom Y Y' → P X Y → P X Y'
  lmap_id : ∀ {X Y} (p : P X Y), lmap (C.id X) p = p
  rmap_id : ∀ {X Y} (p : P X Y), rmap (C.id Y) p = p
  lmap_comp : ∀ {X X' X'' Y} (f : C.Hom X' X) (g : C.Hom X'' X') (p : P X Y),
    lmap (C.comp f g) p = lmap g (lmap f p)
  rmap_comp : ∀ {X Y Y' Y''} (f : C.Hom Y Y') (g : C.Hom Y' Y'') (p : P X Y),
    rmap (C.comp g f) p = rmap g (rmap f p)

/-- Promonad in Kleisli form. -/
structure Promonad (C : SCategory) (P : Profunctor C) where
  eta : {X Y : C.Obj} → C.Hom X Y → P.P X Y
  bind : {X Y Z : C.Obj} → P.P X Y → P.P Y Z → P.P X Z
  -- `eta` is a profunctor morphism `Hom ⇒ P`
  eta_lmap : ∀ {X' X Y} (f : C.Hom X' X) (g : C.Hom X Y),
    P.lmap f (eta g) = eta (C.comp g f)
  eta_rmap : ∀ {X Y Y'} (f : C.Hom Y Y') (g : C.Hom X Y),
    P.rmap f (eta g) = eta (C.comp f g)
  -- `bind` is natural in both profunctor arguments
  bind_lmap : ∀ {X' X Y Z} (f : C.Hom X' X) (p : P.P X Y) (q : P.P Y Z),
    P.lmap f (bind p q) = bind (P.lmap f p) q
  bind_rmap : ∀ {X Y Z Z'} (f : C.Hom Z Z') (p : P.P X Y) (q : P.P Y Z),
    P.rmap f (bind p q) = bind p (P.rmap f q)
  -- monad laws in Kleisli form
  bind_assoc : ∀ {X Y Z W} (p : P.P X Y) (q : P.P Y Z) (r : P.P Z W),
    bind (bind p q) r = bind p (bind q r)
  left_unit : ∀ {X Y Z} (f : C.Hom X Y) (p : P.P Y Z),
    bind (eta f) p = P.lmap f p
  right_unit : ∀ {X Y Z} (p : P.P X Y) (f : C.Hom Y Z),
    bind p (eta f) = P.rmap f p

/-- A P-algebra: an object `carrier` with a natural action
    `P(-, carrier) ⇒ Hom(-, carrier)`.

  This is the small-category rendering of Sanada's algebras.  The full
  Eilenberg-Moore multiplication law is intentionally omitted; the point is
  to get the homomorphism notion right first. -/
structure PromonadAlgebra (C : SCategory) (P : Profunctor C) (M : Promonad C P) where
  carrier : C.Obj
  act : (X : C.Obj) → P.P X carrier → C.Hom X carrier
  naturality : ∀ {X X'} (g : C.Hom X' X) (p : P.P X carrier),
    C.comp (act X p) g = act X' (P.lmap g p)
  unit : ∀ {X} (f : C.Hom X carrier),
    act X (M.eta f) = f

/-- A handler/homomorphism of P-algebras. -/
structure PromonadHom {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    (A B : PromonadAlgebra C P M) where
  f : C.Hom A.carrier B.carrier
  preserves : ∀ (X : C.Obj) (p : P.P X A.carrier),
    C.comp f (A.act X p) = B.act X (P.rmap f p)

/-- Sequential composition of handlers: apply `H`, then `K`. -/
def handlerComp {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A B D : PromonadAlgebra C P M}
    (H : PromonadHom A B) (K : PromonadHom B D) : PromonadHom A D where
  f := C.comp K.f H.f
  preserves := by
    intro X p
    calc
      C.comp (C.comp K.f H.f) (A.act X p)
        = C.comp K.f (C.comp H.f (A.act X p)) := by rw [C.comp_assoc]
      _ = C.comp K.f (B.act X (P.rmap H.f p)) := by rw [H.preserves X p]
      _ = D.act X (P.rmap K.f (P.rmap H.f p)) := by rw [K.preserves X (P.rmap H.f p)]
      _ = D.act X (P.rmap (C.comp K.f H.f) p) := by rw [← P.rmap_comp]

/-!
# Phase 4–6: the commutativity conjecture

We want a certificate `C(H, K)` that is checkable without seeing the
implementations of `H` and `K`, yet implies `H ⋙ K ≃ K ⋙ H`.

The trivial certificate is the equality itself.  The first milestone is to
state the problem and expose the proof obligations.  A useful, modular
certificate is the research target.
-/

/-- Sequential composition of endo-handlers. -/
def handlerCompEndo {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A) : PromonadHom A A :=
  handlerComp H K

/-- The dumbest possible commutativity theorem: if the handlers are the same
    morphism, their compositions are the same. -/
theorem handler_commute_trivial
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A)
    (h : H.f = K.f) :
    (handlerCompEndo H K).f = (handlerCompEndo K H).f := by
  simp [handlerCompEndo, handlerComp, h]

/-- A modular certificate for `H` and `K` to commute.

  In this milestone the certificate *is* the conclusion.  The next task is to
  replace it with a weaker, implementation-independent condition (e.g. an
  interchange law or a disjoint-effect certificate) and prove that it implies
  this one. -/
structure CommuteCert
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A) : Prop where
  commute : (handlerCompEndo H K).f = (handlerCompEndo K H).f

/-- Certified commutativity.  This is the interface an opaque, separately
    compiled library would expose: a client sees `CommuteCert H K` and obtains
    the equality without access to the handler implementations. -/
theorem handler_commute_certified
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A)
    (cert : CommuteCert H K) :
    (handlerCompEndo H K).f = (handlerCompEndo K H).f := by
  exact cert.commute

/-
# Phase 5–6: first useful certificate

A handler acts on the algebra through the right-P action.  In fact, the
unit law of the algebra already makes the family of actions jointly epic, so
the only certificate a client needs is `ProfunctorCommute`.
-/

/-- The family of algebra actions `A.act X p` is jointly epimorphic:
    any two morphisms out of `A.carrier` that agree on every action are equal. -/
def JointlyEpic
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    (A : PromonadAlgebra C P M) : Prop :=
  ∀ {Z : C.Obj} (g h : C.Hom A.carrier Z),
    (∀ (X : C.Obj) (p : P.P X A.carrier),
      C.comp g (A.act X p) = C.comp h (A.act X p)) →
    g = h

/-- Joint epicity is automatic for any promonad algebra: the `eta` of the
    identity `A.carrier → A.carrier` is mapped by `act` to the identity, and the
    identity itself detects equality of all morphisms out of `A.carrier`. -/
theorem joint_epic_always
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    (A : PromonadAlgebra C P M) : JointlyEpic A := by
  intro Z g h H
  have h_id : C.comp g (A.act A.carrier (M.eta (C.id A.carrier))) =
              C.comp h (A.act A.carrier (M.eta (C.id A.carrier))) :=
    H A.carrier (M.eta (C.id A.carrier))
  rw [A.unit (C.id A.carrier)] at h_id
  simp [C.comp_id] at h_id
  exact h_id

/-- The right-P actions induced by `H` and `K` commute elementwise. -/
def ProfunctorCommute
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A) : Prop :=
  ∀ (X : C.Obj) (p : P.P X A.carrier),
    P.rmap K.f (P.rmap H.f p) = P.rmap H.f (P.rmap K.f p)

/-- Nontrivial certificate: profunctor-level commutation implies handler
    commutativity.  The `JointlyEpic` condition is automatic, so the only
    exported certificate needs to be `ProfunctorCommute`. -/
theorem handler_commute_profunctor
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A)
    (hpc : ProfunctorCommute H K) :
    (handlerCompEndo H K).f = (handlerCompEndo K H).f := by
  apply joint_epic_always A
  intro X p
  calc
    C.comp (handlerCompEndo H K).f (A.act X p)
      = C.comp (C.comp K.f H.f) (A.act X p) := by rfl
    _ = C.comp K.f (C.comp H.f (A.act X p)) := by rw [C.comp_assoc]
    _ = C.comp K.f (A.act X (P.rmap H.f p)) := by rw [H.preserves X p]
    _ = A.act X (P.rmap K.f (P.rmap H.f p)) := by rw [K.preserves X (P.rmap H.f p)]
    _ = A.act X (P.rmap H.f (P.rmap K.f p)) := by rw [hpc X p]
    _ = C.comp H.f (A.act X (P.rmap K.f p)) := by rw [← H.preserves X (P.rmap K.f p)]
    _ = C.comp H.f (C.comp K.f (A.act X p)) := by rw [← K.preserves X p]
    _ = C.comp (C.comp H.f K.f) (A.act X p) := by rw [C.comp_assoc]
    _ = C.comp (handlerCompEndo K H).f (A.act X p) := by rfl

/-- A modular certificate built from `ProfunctorCommute` alone. -/
theorem CommuteCert.ofProfunctor
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A)
    (hpc : ProfunctorCommute H K) :
    CommuteCert H K where
  commute := handler_commute_profunctor H K hpc

/-
# Phase 8: separately compiled library experiment

Two libraries can each export a handler and a `ProfunctorCommute` certificate
without exposing implementation details.  The client proves commutativity using
only that certificate and the generic theorem.
-/

section LibraryExperiment

variable {C : SCategory} {P : Profunctor C} {M : Promonad C P}
  {A : PromonadAlgebra C P M}
  (H K : PromonadHom A A)

/-- Client code: proves `H ⋙ K ≃ K ⋙ H` from the exported `ProfunctorCommute`
    certificate only.  The implementations of `H` and `K` are not inspected. -/
theorem client_commute
  (hpc : ProfunctorCommute H K) :
  (handlerCompEndo H K).f = (handlerCompEndo K H).f :=
  handler_commute_profunctor H K hpc

end LibraryExperiment

/-
# Phase 6/11: open conjectures and counterexamples

The certificate is now down to a single condition: `ProfunctorCommute`.  The
remaining question is whether it is necessary, or whether a weaker condition
suffices.
-/

/-- `ProfunctorCommute` is necessary.  If two endo-handlers commute, then their
    right-P actions must commute.  This follows purely from the profunctor law
    `P.rmap (g ∘ f) = P.rmap g ∘ P.rmap f`. -/
theorem profunctor_commute_necessary
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A)
    (h : (handlerCompEndo H K).f = (handlerCompEndo K H).f) :
    ProfunctorCommute H K := by
  intro X p
  have h_eq : C.comp K.f H.f = C.comp H.f K.f := by
    simpa [handlerCompEndo, handlerComp] using h
  calc
    P.rmap K.f (P.rmap H.f p)
      = P.rmap (C.comp K.f H.f) p := by rw [P.rmap_comp]
    _ = P.rmap (C.comp H.f K.f) p := by rw [h_eq]
    _ = P.rmap H.f (P.rmap K.f p) := by rw [P.rmap_comp]

/-- Complete characterization: two arrow handlers commute if and only if their
    induced right-P actions commute. -/
theorem handler_commute_iff_profunctor_commute
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A) :
    (handlerCompEndo H K).f = (handlerCompEndo K H).f ↔ ProfunctorCommute H K :=
  ⟨profunctor_commute_necessary H K, handler_commute_profunctor H K⟩

/-
# Phase 12/13: concrete effect-level bridge (open)

The abstract criterion `ProfunctorCommute` is semantic and exact.  The next
milestone is to construct the free promonad over an effect signature and prove
that concrete "disjoint handled operations" imply `ProfunctorCommute`.  Then
the existing `Dts.Commutativity` disjoint-handler theorem becomes a corollary.

This is the bridge from the abstract if-and-only-if characterization back to
practical, checkable compiler certificates.
-/

/- # Generalized diamond commutativity

The iff theorem above is for endohomomorphisms `H K : PromonadHom A A`.  In a
concrete handler stack, handlers are usually maps from the free algebra to
different target algebras.  The following theorem covers that case.

Given:

    H  : PromonadHom A B        (e.g. Cache)
    K  : PromonadHom A C        (e.g. Logger)
    H' : PromonadHom B D        (e.g. apply Logger after Cache)
    K' : PromonadHom C D        (e.g. apply Cache after Logger)

The diamond is:

    H' ∘ H  : A → D
    K' ∘ K  : A → D

The certificate `ProfunctorCommute2` says the right-P actions compose the same
way into `D`:

    P.rmap H'.f (P.rmap H.f p) = P.rmap K'.f (P.rmap K.f p)

Joint epicity of `A` then makes the two `A → D` composites equal.
-/

def ProfunctorCommute2
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A B C' D : PromonadAlgebra C P M}
    (H : PromonadHom A B) (K : PromonadHom A C')
    (H' : PromonadHom B D) (K' : PromonadHom C' D) : Prop :=
  ∀ (X : C.Obj) (p : P.P X A.carrier),
    P.rmap H'.f (P.rmap H.f p) = P.rmap K'.f (P.rmap K.f p)

theorem handler_diamond_commute
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A B C' D : PromonadAlgebra C P M}
    (H : PromonadHom A B) (K : PromonadHom A C')
    (H' : PromonadHom B D) (K' : PromonadHom C' D)
    (h : ProfunctorCommute2 H K H' K') :
    (handlerComp H H').f = (handlerComp K K').f := by
  apply joint_epic_always A
  intro X p
  calc
    C.comp (handlerComp H H').f (A.act X p)
      = C.comp (C.comp H'.f H.f) (A.act X p) := by rfl
    _ = C.comp H'.f (C.comp H.f (A.act X p)) := by rw [C.comp_assoc]
    _ = C.comp H'.f (B.act X (P.rmap H.f p)) := by rw [H.preserves X p]
    _ = D.act X (P.rmap H'.f (P.rmap H.f p)) := by rw [H'.preserves X (P.rmap H.f p)]
    _ = D.act X (P.rmap K'.f (P.rmap K.f p)) := by rw [h X p]
    _ = C.comp K'.f (C'.act X (P.rmap K.f p)) := by rw [← K'.preserves X (P.rmap K.f p)]
    _ = C.comp K'.f (C.comp K.f (A.act X p)) := by rw [← K.preserves X p]
    _ = C.comp (C.comp K'.f K.f) (A.act X p) := by rw [C.comp_assoc]
    _ = C.comp (handlerComp K K').f (A.act X p) := by rfl

end SanadaPromonad
