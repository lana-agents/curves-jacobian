/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Dual
import Mathlib.CategoryTheory.Monoidal.Skeleton

/-!
# The Picard group of a scheme

`X.Modules` is a symmetric monoidal category (`CurvesJacobian.Picard.Tensor`), so the
isomorphism classes of `𝒪_X`-modules form a commutative monoid `Skeleton X.Modules`. The classes
of invertible sheaves are units (with inverse the dual, `Modules.tensorDualIso`) and form a
subgroup `X.picSubgroup` of its group of units. The Picard group (Stacks, Tag 01CX) is
`X.PicLarge := Additive X.picSubgroup`, written additively: `[L] + [M] = [L ⊗ M]`, `-[L] = [L^∨]`.

* `PicLarge.mk L`: the class of an invertible sheaf `L`.
* `PicLarge.mk_eq_mk_iff`: `[L] = [M] ↔ L ≅ M`; `PicLarge.mk_eq_zero_iff`: `[L] = 0 ↔ L ≅ 𝟙_`.
* `PicLarge.mk_tensor`, `PicLarge.mk_dual`, `PicLarge.mk_surjective`.
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace Modules

/-- An isomorphism class of `𝒪_X`-modules is invertible if its representative is. -/
def SkIsInvertible (x : Skeleton X.Modules) : Prop := ((fromSkeleton _).obj x).IsInvertible

lemma skIsInvertible_toSkeleton (L : X.Modules) :
    SkIsInvertible (toSkeleton L) ↔ L.IsInvertible :=
  isInvertible_iff_of_iso (fromSkeletonToSkeletonIso L)

/-- The class of an invertible sheaf, as a unit of the monoid of isomorphism classes. -/
def unitOf (L : X.Modules) [L.IsInvertible] : (Skeleton X.Modules)ˣ where
  val := toSkeleton L
  inv := toSkeleton (dual L)
  val_inv := by
    rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact congr_toSkeleton_of_iso (tensorDualIso L)
  inv_val := by
    rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact congr_toSkeleton_of_iso ((β_ _ _) ≪≫ tensorDualIso L)

end Modules

open Modules

variable (X) in
/-- The subgroup of the units of the monoid of isomorphism classes of `𝒪_X`-modules consisting
of the classes of invertible sheaves. -/
def picSubgroup : Subgroup (Skeleton X.Modules)ˣ where
  carrier := {x | SkIsInvertible x.val}
  one_mem' := by
    change SkIsInvertible (toSkeleton (𝟙_ X.Modules))
    rw [skIsInvertible_toSkeleton]
    infer_instance
  mul_mem' {a b} ha hb := by
    change SkIsInvertible (a.val * b.val)
    rw [Skeleton.mul_eq, skIsInvertible_toSkeleton]
    exact @isInvertible_tensor X _ _ ha hb
  inv_mem' {a} ha := by
    have : ((fromSkeleton _).obj a.val).IsInvertible := ha
    change SkIsInvertible (a⁻¹).val
    have hval : a.val = (unitOf ((fromSkeleton _).obj a.val)).val :=
      (toSkeleton_fromSkeleton_obj a.val).symm
    have : a = unitOf ((fromSkeleton _).obj a.val) := Units.ext hval
    rw [this]
    change SkIsInvertible (toSkeleton (dual _))
    rw [skIsInvertible_toSkeleton]
    infer_instance

variable (X) in
/-- The Picard group of a scheme (Stacks, Tag 01CX): isomorphism classes of invertible sheaves,
with the group law `[L] + [M] = [L ⊗ M]`, as a type in the universe `u + 1`. The Picard group
`X.Pic : Type u` is obtained by shrinking it (`CurvesJacobian.Picard.Small`). -/
def PicLarge : Type (u + 1) := Additive (picSubgroup X)

instance : AddCommGroup X.PicLarge := inferInstanceAs (AddCommGroup (Additive (picSubgroup X)))

namespace PicLarge

/-- The class of an invertible sheaf in the Picard group. -/
def mk (L : X.Modules) [L.IsInvertible] : X.PicLarge :=
  Additive.ofMul ⟨unitOf L, by
    change SkIsInvertible (toSkeleton L)
    rw [skIsInvertible_toSkeleton]
    infer_instance⟩

lemma toMul_mk_val (L : X.Modules) [L.IsInvertible] :
    ((Additive.toMul (mk L) : picSubgroup X) : (Skeleton X.Modules)ˣ).val = toSkeleton L := rfl

lemma mk_eq_mk_iff {L M : X.Modules} [L.IsInvertible] [M.IsInvertible] :
    mk L = mk M ↔ Nonempty (L ≅ M) := by
  rw [← toSkeleton_eq_toSkeleton_iff, ← toMul_mk_val L, ← toMul_mk_val M]
  constructor
  · intro h; rw [h]
  · intro h
    apply Additive.toMul.injective
    exact Subtype.ext (Units.ext h)

lemma mk_eq_of_iso {L M : X.Modules} [L.IsInvertible] [M.IsInvertible] (e : L ≅ M) :
    mk L = mk M :=
  mk_eq_mk_iff.mpr ⟨e⟩

lemma mk_tensor (L M : X.Modules) [L.IsInvertible] [M.IsInvertible] :
    mk (L ⊗ M) = mk L + mk M := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change toSkeleton (L ⊗ M) = toSkeleton L * toSkeleton M
  exact Skeleton.toSkeleton_tensorObj L M

lemma mk_unit : mk (𝟙_ X.Modules) = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rfl

lemma mk_eq_zero_iff (L : X.Modules) [L.IsInvertible] :
    mk L = 0 ↔ Nonempty (L ≅ 𝟙_ X.Modules) := by
  rw [← mk_unit, mk_eq_mk_iff]

lemma mk_dual (L : X.Modules) [L.IsInvertible] : mk (dual L) = -mk L := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← mk_tensor, mk_eq_zero_iff]
  exact ⟨tensorDualIso L⟩

lemma mk_surjective (x : X.PicLarge) : ∃ (L : X.Modules) (_ : L.IsInvertible), mk L = x := by
  rcases hx : Additive.toMul x with ⟨a, ha⟩
  have : ((fromSkeleton _).obj a.val).IsInvertible := ha
  refine ⟨(fromSkeleton _).obj a.val, this, ?_⟩
  apply Additive.toMul.injective
  rw [hx]
  apply Subtype.ext
  apply Units.ext
  exact toSkeleton_fromSkeleton_obj a.val

/-- Induction principle for the Picard group. -/
@[elab_as_elim]
lemma ind {p : X.PicLarge → Prop} (h : ∀ (L : X.Modules) [L.IsInvertible], p (mk L))
    (x : X.PicLarge) :
    p x := by
  obtain ⟨L, _, rfl⟩ := mk_surjective x
  exact h L

/-- A representative of a class in the Picard group. -/
def rep (x : X.PicLarge) : X.Modules :=
  (fromSkeleton _).obj ((Additive.toMul x : picSubgroup X) : (Skeleton X.Modules)ˣ).val

instance (x : X.PicLarge) : (rep x).IsInvertible := (Additive.toMul x).2

lemma mk_rep (x : X.PicLarge) : mk (rep x) = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact toSkeleton_fromSkeleton_obj _

lemma rep_mk (L : X.Modules) [L.IsInvertible] : Nonempty (rep (mk L) ≅ L) :=
  mk_eq_mk_iff.mp (mk_rep (mk L))

end PicLarge

end AlgebraicGeometry.Scheme

end
