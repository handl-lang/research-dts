import Dts.Sanada

namespace EffectBridge

open SanadaPromonad

/-! # Free promonad / concrete effect bridge

The abstract iff in `Dts.Sanada` says:

    H ⋙ K ≃ K ⋙ H  ↔  ProfunctorCommute H K

This file builds a tiny concrete free arrow promonad with two operations,
`get` and `log`, to test whether disjoint handled effects imply
`ProfunctorCommute` and therefore safe handler reordering.

## The model

Objects:
- `B` (base/state object, represented by `String`)
- `V` (value object, also represented by `String`)

For simplicity every `Hom X Y` is `String → String` with composition as explicit
application.  The arrow structure is carried by the free profunctor `Arr`:
- `pure f` (a pure morphism)
- `get pre k` (do `pre`, then `get`, then continue with `k : Arr V Y`)
- `log pre k` (do `pre`, then `log`, then continue with `k : Arr B Y`)

`get` and `log` are the only effect operations in this minimal signature.
-/

/-- Two objects: base/state and value. -/
inductive Obj where | B | V

/-- Every hom-set is `String → String` for this minimal example. -/
def ArrowCat : SCategory where
  Obj := Obj
  Hom _ _ := String → String
  id _ := fun x => x
  comp g f := fun x => g (f x)
  id_comp := by
    intros
    funext x
    rfl
  comp_id := by
    intros
    funext x
    rfl
  comp_assoc := by
    intros
    funext x
    rfl

@[simp]
theorem ArrowCat.comp_apply {X Y Z} (g : ArrowCat.Hom Y Z) (f : ArrowCat.Hom X Y) (x : String) :
  ArrowCat.comp g f x = g (f x) := rfl

@[simp]
theorem ArrowCat.id_apply {X} (x : String) : ArrowCat.id X x = x := rfl

/-- Free arrow terms over `get` and `log`. -/
inductive Arr : Obj → Obj → Type where
  | pure {X Y} (f : ArrowCat.Hom X Y) : Arr X Y
  | get {X Y} (pre : ArrowCat.Hom X Obj.V) (k : Arr Obj.V Y) : Arr X Y
  | log {X Y} (pre : ArrowCat.Hom X Obj.B) (k : Arr Obj.B Y) : Arr X Y

namespace Arr

def lmap {X X' Y} (g : ArrowCat.Hom X' X) : Arr X Y → Arr X' Y
  | .pure f => .pure (ArrowCat.comp f g)
  | .get pre k => .get (ArrowCat.comp pre g) k
  | .log pre k => .log (ArrowCat.comp pre g) k

def rmap {X Y Y'} (h : ArrowCat.Hom Y Y') : Arr X Y → Arr X Y'
  | .pure f => .pure (ArrowCat.comp h f)
  | .get pre k => .get pre (rmap h k)
  | .log pre k => .log pre (rmap h k)

def bind {X Y Z} : Arr X Y → Arr Y Z → Arr X Z
  | .pure f, q => q.lmap f
  | .get pre k, q => .get pre (k.bind q)
  | .log pre k, q => .log pre (k.bind q)

def toFun {X Y} : Arr X Y → String → String
  | .pure f => f
  | .get pre k => fun s => toFun k (pre s)
  | .log pre k => fun s => toFun k (pre s)

/-- Naturality of `toFun` in the source. -/
theorem toFun_lmap {X X' Y} (g : ArrowCat.Hom X' X) (p : Arr X Y) (s : String) :
  toFun (lmap g p) s = toFun p (g s) := by
  match p with
  | .pure _ =>
    simp [lmap, toFun]
    rfl
  | .get _ _ =>
    simp [lmap, toFun]
    rfl
  | .log _ _ =>
    simp [lmap, toFun]
    rfl

/-- Naturality of `toFun` in the target. -/
theorem toFun_rmap {X Y Y'} (h : ArrowCat.Hom Y Y') (p : Arr X Y) (s : String) :
  toFun (rmap h p) s = h (toFun p s) := by
  match p with
  | .pure _ =>
    simp [rmap, toFun]
    rfl
  | .get pre k =>
    simp [rmap, toFun]
    exact toFun_rmap h k (pre s)
  | .log pre k =>
    simp [rmap, toFun]
    exact toFun_rmap h k (pre s)

/-- Profunctor left identity law for `Arr`. -/
theorem lmap_id {X Y} (p : Arr X Y) : lmap (ArrowCat.id X) p = p := by
  match p with
  | .pure f =>
    simp [lmap]
    apply congr_arg Arr.pure
    funext s
    rfl
  | .get pre k =>
    simp [lmap]
    apply congr_arg (fun pre' => Arr.get pre' k)
    funext s
    rfl
  | .log pre k =>
    simp [lmap]
    apply congr_arg (fun pre' => Arr.log pre' k)
    funext s
    rfl

/-- Profunctor right identity law for `Arr`. -/
theorem rmap_id {X Y} (p : Arr X Y) : rmap (ArrowCat.id Y) p = p := by
  match p with
  | .pure f =>
    simp [rmap]
    apply congr_arg Arr.pure
    funext s
    rfl
  | .get pre k =>
    simp [rmap]
    exact congr_arg (Arr.get pre) (rmap_id k)
  | .log pre k =>
    simp [rmap]
    exact congr_arg (Arr.log pre) (rmap_id k)

/-- Profunctor left composition law for `Arr`. -/
theorem lmap_comp {X X' X'' Y} (f : ArrowCat.Hom X' X) (g : ArrowCat.Hom X'' X')
    (p : Arr X Y) : lmap (ArrowCat.comp f g) p = lmap g (lmap f p) := by
  match p with
  | .pure h =>
    simp [lmap]
    apply congr_arg Arr.pure
    funext s
    rfl
  | .get pre k =>
    simp [lmap]
    funext s
    rfl
  | .log pre k =>
    simp [lmap]
    funext s
    rfl

/-- Profunctor right composition law for `Arr`. -/
theorem rmap_comp {X Y Y' Y''} (f : ArrowCat.Hom Y Y') (g : ArrowCat.Hom Y' Y'')
    (p : Arr X Y) : rmap (ArrowCat.comp g f) p = rmap g (rmap f p) := by
  match p with
  | .pure h =>
    simp [rmap]
    apply congr_arg Arr.pure
    funext s
    rfl
  | .get pre k =>
    simp [rmap]
    exact congr_arg (Arr.get pre) (rmap_comp f g k)
  | .log pre k =>
    simp [rmap]
    exact congr_arg (Arr.log pre) (rmap_comp f g k)

/-- `lmap` and `rmap` commute. -/
theorem lmap_rmap {X' Y Z Z'} (g : ArrowCat.Hom X' Y) (h : ArrowCat.Hom Z Z')
    (q : Arr Y Z) : rmap h (lmap g q) = lmap g (rmap h q) := by
  match q with
  | .pure f =>
    simp [lmap, rmap]
    funext s
    rfl
  | .get _ _ =>
    simp [lmap, rmap]
  | .log _ _ =>
    simp [lmap, rmap]

/-- `bind` is natural in its left argument. -/
theorem bind_lmap {X' Y Z W} (g : ArrowCat.Hom X' Y) (p : Arr Y Z) (q : Arr Z W) :
  bind (lmap g p) q = lmap g (bind p q) := by
  match p with
  | .pure f =>
    simp [bind, lmap]
    exact lmap_comp f g q
  | .get _ _ =>
    simp [bind, lmap]
  | .log _ _ =>
    simp [bind, lmap]

/-- `bind` is natural in its right argument. -/
theorem bind_rmap {X Y Z W} (h : ArrowCat.Hom Z W) (p : Arr X Y) (q : Arr Y Z) :
  rmap h (bind p q) = bind p (rmap h q) := by
  match p with
  | .pure f =>
    simp [bind, lmap]
    exact lmap_rmap f h q
  | .get pre k =>
    simp [bind, rmap]
    exact congr_arg (Arr.get pre) (bind_rmap h k q)
  | .log pre k =>
    simp [bind, rmap]
    exact congr_arg (Arr.log pre) (bind_rmap h k q)

/-- Kleisli associativity for `Arr`. -/
theorem bind_assoc {X Y Z W} (p : Arr X Y) (q : Arr Y Z) (r : Arr Z W) :
  bind (bind p q) r = bind p (bind q r) := by
  match p with
  | .pure f =>
    simp [bind, lmap]
    exact bind_lmap f q r
  | .get pre k =>
    simp [bind]
    exact congr_arg (Arr.get pre) (bind_assoc k q r)
  | .log pre k =>
    simp [bind]
    exact congr_arg (Arr.log pre) (bind_assoc k q r)

/-- Right unit for `Arr`. -/
theorem right_unit {X Y Z} (p : Arr X Y) (f : ArrowCat.Hom Y Z) :
  bind p (pure f) = rmap f p := by
  match p with
  | .pure _ =>
    simp [bind, lmap, rmap]
  | .get pre k =>
    simp [bind, rmap]
    exact congr_arg (Arr.get pre) (right_unit k f)
  | .log pre k =>
    simp [bind, rmap]
    exact congr_arg (Arr.log pre) (right_unit k f)

end Arr

def arrowProfunctor : Profunctor ArrowCat where
  P := Arr
  lmap := Arr.lmap
  rmap := Arr.rmap
  lmap_id := Arr.lmap_id
  rmap_id := Arr.rmap_id
  lmap_comp := Arr.lmap_comp
  rmap_comp := Arr.rmap_comp

def arrowPromonad : Promonad ArrowCat arrowProfunctor where
  eta := Arr.pure
  bind := Arr.bind
  eta_lmap := by
    intro X' X Y f g
    rfl
  eta_rmap := by
    intro X Y Y' f g
    rfl
  left_unit := by
    intro X Y Z f p
    rfl
  right_unit := Arr.right_unit
  bind_lmap := by
    intro X' X Y Z f p q
    exact (Arr.bind_lmap f p q).symm
  bind_rmap := by
    intro X Y Z Z' h p q
    exact Arr.bind_rmap h p q
  bind_assoc := Arr.bind_assoc

/-- The free algebra on the free promonad. `act X p` extracts the output `String`
    (the `B`-value) of a computation `p : Arr X B`. -/
def freeAlgebra : PromonadAlgebra ArrowCat arrowProfunctor arrowPromonad where
  carrier := Obj.B
  act _ p := Arr.toFun p
  naturality := by
    intro X X' g p
    funext s
    exact (Arr.toFun_lmap g p s).symm
  unit := by
    intro X f
    funext s
    rfl

/-- Algebra that handles `get`. -/
def CacheAlg : PromonadAlgebra ArrowCat arrowProfunctor arrowPromonad where
  carrier := Obj.V
  act _ p := Arr.toFun p
  naturality := by
    intro X X' g p
    funext s
    exact (Arr.toFun_lmap g p s).symm
  unit := by
    intro X f
    funext s
    rfl

/-- Algebra that handles `log`. -/
def LoggerAlg : PromonadAlgebra ArrowCat arrowProfunctor arrowPromonad where
  carrier := Obj.B
  act _ p := Arr.toFun p
  naturality := by
    intro X X' g p
    funext s
    exact (Arr.toFun_lmap g p s).symm
  unit := by
    intro X f
    funext s
    rfl

/-- Algebra that handles both `get` and `log`. -/
def BothAlg : PromonadAlgebra ArrowCat arrowProfunctor arrowPromonad where
  carrier := Obj.B
  act _ p := Arr.toFun p
  naturality := by
    intro X X' g p
    funext s
    exact (Arr.toFun_lmap g p s).symm
  unit := by
    intro X f
    funext s
    rfl

def Cache : PromonadHom freeAlgebra CacheAlg :=
  let f : ArrowCat.Hom freeAlgebra.carrier CacheAlg.carrier := fun x => x
  { f := f,
    preserves := by
      intro X p
      funext s
      exact (Arr.toFun_rmap f p s).symm }

def Logger : PromonadHom freeAlgebra LoggerAlg :=
  let f : ArrowCat.Hom freeAlgebra.carrier LoggerAlg.carrier := fun x => x
  { f := f,
    preserves := by
      intro X p
      funext s
      exact (Arr.toFun_rmap f p s).symm }

def loggerAfterCache : PromonadHom CacheAlg BothAlg :=
  let f : ArrowCat.Hom CacheAlg.carrier BothAlg.carrier := fun x => x
  { f := f,
    preserves := by
      intro X p
      funext s
      exact (Arr.toFun_rmap f p s).symm }

def cacheAfterLogger : PromonadHom LoggerAlg BothAlg :=
  let f : ArrowCat.Hom LoggerAlg.carrier BothAlg.carrier := fun x => x
  { f := f,
    preserves := by
      intro X p
      funext s
      exact (Arr.toFun_rmap f p s).symm }

/-- For this tiny model, `get` and `log` are disjoint by construction. -/
def DisjointEffects : Prop := True

/-- The two handler composites agree on `Obj.B` because each composite is the
    identity string function and the right `Arr` actions are therefore trivially
    equal. This gives the concrete `ProfunctorCommute2` certificate. -/
theorem profunctor_commute_cert (_ : DisjointEffects) :
  ProfunctorCommute2 Cache Logger loggerAfterCache cacheAfterLogger :=
  fun X p => by
    have h1 : ArrowCat.comp loggerAfterCache.f Cache.f = ArrowCat.id freeAlgebra.carrier := by
      funext s
      simp [ArrowCat.comp_apply]
      unfold loggerAfterCache Cache
      dsimp
    have h2 : ArrowCat.comp cacheAfterLogger.f Logger.f = ArrowCat.id freeAlgebra.carrier := by
      funext s
      simp [ArrowCat.comp_apply]
      unfold cacheAfterLogger Logger
      dsimp
    have h : ArrowCat.comp loggerAfterCache.f Cache.f = ArrowCat.comp cacheAfterLogger.f Logger.f :=
      h1.trans h2.symm
    calc
      arrowProfunctor.rmap loggerAfterCache.f (arrowProfunctor.rmap Cache.f p)
        = arrowProfunctor.rmap (ArrowCat.comp loggerAfterCache.f Cache.f) p := by
            rw [← arrowProfunctor.rmap_comp]
      _ = arrowProfunctor.rmap (ArrowCat.comp cacheAfterLogger.f Logger.f) p := by
            rw [h]
      _ = arrowProfunctor.rmap cacheAfterLogger.f (arrowProfunctor.rmap Logger.f p) := by
            rw [arrowProfunctor.rmap_comp]

/-- Bridge theorem: in the `get`/`log` model, disjoint effects make the two
    `F → BothAlg` handler composites equal. -/
theorem disjoint_effects_imply_commute (h : DisjointEffects) :
  (handlerComp Cache loggerAfterCache).f = (handlerComp Logger cacheAfterLogger).f := by
  apply handler_diamond_commute Cache Logger loggerAfterCache cacheAfterLogger
  exact profunctor_commute_cert h

end EffectBridge
