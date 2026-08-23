import Mathlib.Tactic

namespace SanadaStrong

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

/-- Parameterized strong profunctor structure for a fixed parameter object `S`.
    The formula `P (A × S) (B × S)` is interpreted by a chosen object
    `tensor A` for each `A` (thought of as `A ⊗ S`) together with a functorial
    action on morphisms.  Only the operations needed for the parameterized
    semantics are included: the parameter map `strength` and its naturality in
    both profunctor arguments. -/
structure StrongProfunctor (C : SCategory) (P : Profunctor C) where
  S : C.Obj
  tensor : C.Obj → C.Obj
  Tmap : {A B : C.Obj} → C.Hom A B → C.Hom (tensor A) (tensor B)
  Tmap_id : ∀ A, Tmap (C.id A) = C.id (tensor A)
  Tmap_comp : ∀ {A B D} (f : C.Hom A B) (g : C.Hom B D),
    Tmap (C.comp g f) = C.comp (Tmap g) (Tmap f)
  strength : {A B : C.Obj} → P.P A B → P.P (tensor A) (tensor B)
  strength_lmap : ∀ {A A' B} (f : C.Hom A' A) (p : P.P A B),
    P.lmap (Tmap f) (strength p) = strength (P.lmap f p)
  strength_rmap : ∀ {A B B'} (g : C.Hom B B') (p : P.P A B),
    P.rmap (Tmap g) (strength p) = strength (P.rmap g p)

/-- Promonad in Kleisli form. -/
structure Promonad (C : SCategory) (P : Profunctor C) where
  eta : {X Y : C.Obj} → C.Hom X Y → P.P X Y
  bind : {X Y Z : C.Obj} → P.P X Y → P.P Y Z → P.P X Z
  eta_lmap : ∀ {X' X Y} (f : C.Hom X' X) (g : C.Hom X Y),
    P.lmap f (eta g) = eta (C.comp g f)
  eta_rmap : ∀ {X Y Y'} (f : C.Hom Y Y') (g : C.Hom X Y),
    P.rmap f (eta g) = eta (C.comp f g)
  bind_lmap : ∀ {X' X Y Z} (f : C.Hom X' X) (p : P.P X Y) (q : P.P Y Z),
    P.lmap f (bind p q) = bind (P.lmap f p) q
  bind_rmap : ∀ {X Y Z Z'} (f : C.Hom Z Z') (p : P.P X Y) (q : P.P Y Z),
    P.rmap f (bind p q) = bind p (P.rmap f q)
  bind_assoc : ∀ {X Y Z W} (p : P.P X Y) (q : P.P Y Z) (r : P.P Z W),
    bind (bind p q) r = bind p (bind q r)
  left_unit : ∀ {X Y Z} (f : C.Hom X Y) (p : P.P Y Z),
    bind (eta f) p = P.lmap f p
  right_unit : ∀ {X Y Z} (p : P.P X Y) (f : C.Hom Y Z),
    bind p (eta f) = P.rmap f p

/-- A P-algebra. -/
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

/-- Sequential composition of endo-handlers. -/
def handlerCompEndo {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A) : PromonadHom A A :=
  handlerComp H K

/-- The family of algebra actions `A.act X p` is jointly epimorphic. -/
def JointlyEpic
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    (A : PromonadAlgebra C P M) : Prop :=
  ∀ {Z : C.Obj} (g h : C.Hom A.carrier Z),
    (∀ (X : C.Obj) (p : P.P X A.carrier),
      C.comp g (A.act X p) = C.comp h (A.act X p)) →
    g = h

/-- Joint epicity is automatic for any promonad algebra. -/
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

/-- Profunctor-level commutation implies handler commutativity. -/
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

/-- `ProfunctorCommute` is necessary. -/
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

/-- Complete characterization: two endo-handlers commute iff their right-P
    actions commute. -/
theorem handler_commute_iff_profunctor_commute
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A : PromonadAlgebra C P M} (H K : PromonadHom A A) :
    (handlerCompEndo H K).f = (handlerCompEndo K H).f ↔ ProfunctorCommute H K :=
  ⟨profunctor_commute_necessary H K, handler_commute_profunctor H K⟩

/-- Diamond commutativity certificate. -/
def ProfunctorCommute2
    {C : SCategory} {P : Profunctor C} {M : Promonad C P}
    {A B C' D : PromonadAlgebra C P M}
    (H : PromonadHom A B) (K : PromonadHom A C')
    (H' : PromonadHom B D) (K' : PromonadHom C' D) : Prop :=
  ∀ (X : C.Obj) (p : P.P X A.carrier),
    P.rmap H'.f (P.rmap H.f p) = P.rmap K'.f (P.rmap K.f p)

/-- Diamond handler commutativity. -/
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

end SanadaStrong
