/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicSmooth
import CurvesJacobian.Picard.BasisLift
import CurvesJacobian.Picard.EpsDecomp
import CurvesJacobian.Picard.TangentAlg

/-!
# Tangent spaces of the Picard scheme: setup

Infrastructure for the computation of the tangent spaces of `Pic_{C/k,σ}`
(`CurvesJacobian.PicTangent`).

* `PicTangent.gB B : Spec B ⟶ S` for an algebra `B` over `Γ(S, ⊤)` (`S` affine), and the
  points of an affine `Y ⟶ S` with values in `Spec B` as ring maps
  `PicTangent.ptOf ψ = Spec ψ ≫ Y.isoSpec⁻¹` (`ptOf_injective`, `exists_ptOf`,
  `ptOf_comp_eq_gB_iff`: the point lies over `S` iff `ψ` is a `Γ(S)`-algebra map).
* For a curve `C` over `k` and a `Γ(Spec k)`-algebra `B`, the base change
  `C_B = C ×_k Spec B` (`PicTangent.CT`), the pulled back functions `fA` and constants `fE`, and
  the classes `twK n = [𝒪(1 + n)]` of the twists of the two-chart covering by `1 + n` for a
  square-zero function `n` on the overlap (`TwoChart.twPic`), with their behaviour under base
  change (`PicTangent.map_twK`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TrivSqZeroExt

universe u

noncomputable section

namespace CurvesJacobian.PicTangent

open Scheme

/-! ### Points of affine schemes -/

section SpecPoint

variable {S : Scheme.{u}} [IsAffine S]

/-- The structure morphism `Spec B ⟶ S` of an algebra `B` over `Γ(S, ⊤)`. -/
def gB (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] : Spec (CommRingCat.of B) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv

lemma isoSpec_inv_appTop' : S.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(S, ⊤)).inv := by
  have h := congrArg Scheme.Hom.appTop S.isoSpec.inv_hom_id
  rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop,
    Scheme.Hom.id_appTop] at h
  rw [← Category.id_comp S.isoSpec.inv.appTop, ← Iso.inv_hom_id (Scheme.ΓSpecIso Γ(S, ⊤)),
    Category.assoc, h, Category.comp_id]

variable (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B]

lemma gB_appTop (r : Γ(S, ⊤)) :
    (gB (S := S) B).appTop r =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap Γ(S, ⊤) B r) := by
  rw [gB, Scheme.Hom.comp_appTop, isoSpec_inv_appTop', ← Scheme.ΓSpecIso_inv_naturality]
  rfl

lemma gB_appLE (r : Γ(S, ⊤)) :
    (gB (S := S) B).appLE ⊤ ⊤ (gB (S := S) B).preimage_top.ge r =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap Γ(S, ⊤) B r) := by
  rw [← gB_appTop]
  exact congrArg (fun φ ↦ φ r) (Scheme.Hom.appLE_eq_app (f := gB (S := S) B) (U := ⊤))

/-- `Spec` of an algebra map is a morphism over `S`. -/
lemma spec_map_comp_gB {B' : Type u} [CommRing B'] [Algebra Γ(S, ⊤) B'] (φ : B →ₐ[Γ(S, ⊤)] B') :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ gB (S := S) B = gB B' := by
  rw [gB, gB, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact φ.commutes r

variable {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ S)

/-- The `Spec B`-point of the affine scheme `Y` given by `ψ : Γ(Y) ⟶ B`. -/
def ptOf {B : CommRingCat.{u}} (ψ : Γ(Y, ⊤) ⟶ B) : Spec B ⟶ Y :=
  Spec.map ψ ≫ Y.isoSpec.inv

variable {B} in
lemma ptOf_injective {B : CommRingCat.{u}} : Function.Injective (ptOf (Y := Y) (B := B)) := by
  intro ψ ψ' h
  exact Spec.map_injective ((cancel_mono Y.isoSpec.inv).mp h)

variable {B} in
lemma exists_ptOf {B : CommRingCat.{u}} (f : Spec B ⟶ Y) : ∃ ψ, ptOf ψ = f :=
  ⟨Spec.preimage (f ≫ Y.isoSpec.hom), by
    rw [ptOf, Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

variable {B} in
lemma map_comp_ptOf {B B' : CommRingCat.{u}} (ψ : Γ(Y, ⊤) ⟶ B) (φ : B ⟶ B') :
    Spec.map φ ≫ ptOf ψ = ptOf (ψ ≫ φ) := by
  rw [ptOf, ptOf, ← Category.assoc, Spec.map_comp]

omit [Algebra Γ(S, ⊤) B] in
lemma ptOf_comp (ψ : Γ(Y, ⊤) ⟶ CommRingCat.of B) :
    ptOf ψ ≫ q = Spec.map (q.appTop ≫ ψ) ≫ S.isoSpec.inv := by
  rw [ptOf, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp]

/-- **A point lies over `S` iff it is an algebra map.** -/
lemma ptOf_comp_eq_gB_iff (ψ : Γ(Y, ⊤) ⟶ CommRingCat.of B) :
    ptOf ψ ≫ q = gB B ↔ q.appTop ≫ ψ = CommRingCat.ofHom (algebraMap Γ(S, ⊤) B) := by
  rw [ptOf_comp, gB]
  constructor
  · intro h
    exact Spec.map_injective ((cancel_mono S.isoSpec.inv).mp h)
  · intro h
    rw [h]

end SpecPoint

/-! ### Local rings -/

lemma isLocalRing_of_isField {R : Type*} [CommRing R] (hR : IsField R) : IsLocalRing R := by
  letI := hR.toField
  infer_instance

lemma isLocalRing_trivSqZeroExt {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (hR : IsField R) :
    IsLocalRing (TrivSqZeroExt R M) := by
  letI := hR.toField
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  by_cases hx : x.fst = 0
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_sub, fst_one, hx, sub_zero]
    exact isUnit_one
  · left
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact IsUnit.mk0 _ hx

/-- `1 + n` for a square-zero `n`. -/
def sqUnit {R : Type*} [CommRing R] (n : R) (hn : n * n = 0) : Rˣ where
  val := 1 + n
  inv := 1 - n
  val_inv := by
    calc (1 + n) * (1 - n) = 1 - n * n := by ring
      _ = 1 := by rw [hn, sub_zero]
  inv_val := by
    calc (1 - n) * (1 + n) = 1 - n * n := by ring
      _ = 1 := by rw [hn, sub_zero]

lemma sqUnit_val {R : Type*} [CommRing R] (n : R) (hn : n * n = 0) :
    (sqUnit n hn : R) = 1 + n := rfl

lemma sqUnit_zero {R : Type*} [CommRing R] : sqUnit (0 : R) (mul_zero 0) = 1 :=
  Units.ext (add_zero 1)

/-! ### The curve over `Spec B` -/

section Curve

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "R₀" => Γ(Sk, ⊤)

lemma appLE_apply_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) : f.appLE U V e a = g.appLE U V e' a := by
  subst h; rfl

lemma appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (a : Γ(Z, U)) :
    f.appLE V W e₂ (g.appLE U V e₁ a) = (f ≫ g).appLE U W (e₂.trans (f.preimage_mono e₁)) a :=
  congrArg (fun φ ↦ φ a) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

lemma map_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (a : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e a) = f.appLE U V' (h.trans e) a :=
  congrArg (fun φ ↦ φ a) (Scheme.Hom.appLE_map f e (homOfLE h).op)

lemma appLE_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map (homOfLE h).op a) =
      f.appLE U' V (e.trans (f.preimage_mono h)) a :=
  congrArg (fun φ ↦ φ a) (Scheme.Hom.map_appLE f e (homOfLE h).op)

variable (B : Type u) [CommRing B] [Algebra Γ(Spec (CommRingCat.of k), ⊤) B]

variable (k) in
/-- `C_B = C ×_k Spec B`. -/
abbrev CT : Scheme.{u} := pullback (C ↘ Sk) (gB (S := Sk) B)

variable (k) in
/-- The projection `C_B ⟶ C`. -/
abbrev pB : CT k C B ⟶ C := pullback.fst _ _

variable (k) in
/-- The projection `C_B ⟶ Spec B`. -/
abbrev sB : CT k C B ⟶ Spec (CommRingCat.of B) := pullback.snd _ _

variable (k) in
/-- Functions on `C` pulled back to `C_B`. -/
def fA {O : C.Opens} {O' : (CT k C B).Opens} (h : O' ≤ pB k C B ⁻¹ᵁ O) :
    Γ(C, O) →+* Γ(CT k C B, O') :=
  ((pB k C B).appLE O O' h).hom

variable (k) in
/-- Constants from `B`. -/
def fE (O' : (CT k C B).Opens) : B →+* Γ(CT k C B, O') :=
  ((sB k C B).appLE ⊤ O' (le_top.trans (sB k C B).preimage_top.ge)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

variable {C B}

lemma fA_res {O : C.Opens} {O' O'' : (CT k C B).Opens} (h : O' ≤ pB k C B ⁻¹ᵁ O) (h' : O'' ≤ O')
    (a : Γ(C, O)) :
    (CT k C B).presheaf.map (homOfLE h').op (fA k C B h a) = fA k C B (h'.trans h) a :=
  map_appLE_apply _ _ _ _

lemma fA_map {O O₁ : C.Opens} {O' : (CT k C B).Opens} (h : O' ≤ pB k C B ⁻¹ᵁ O₁) (h₁ : O₁ ≤ O)
    (a : Γ(C, O)) :
    fA k C B h (C.presheaf.map (homOfLE h₁).op a) =
      fA k C B (h.trans ((pB k C B).preimage_mono h₁)) a :=
  appLE_map_apply _ _ _ _

lemma fE_res {O' O'' : (CT k C B).Opens} (h' : O'' ≤ O') (e : B) :
    (CT k C B).presheaf.map (homOfLE h').op (fE k C B O' e) = fE k C B O'' e :=
  map_appLE_apply _ _ _ _

/-- Constants from `Γ(S)` are pulled back from `C`. -/
lemma fE_algebraMap {O : C.Opens} {O' : (CT k C B).Opens} (h : O' ≤ pB k C B ⁻¹ᵁ O) (r : R₀) :
    fE k C B O' (algebraMap R₀ B r) =
      fA k C B h ((C ↘ Sk).appLE ⊤ O (le_top.trans (C ↘ Sk).preimage_top.ge) r) := by
  change (sB k C B).appLE ⊤ O' _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap R₀ B r)) =
    (pB k C B).appLE O O' h ((C ↘ Sk).appLE ⊤ O _ r)
  rw [← gB_appLE B r, appLE_appLE_apply, appLE_appLE_apply]
  exact appLE_apply_eq pullback.condition.symm _ _ r

/-! ### Base change along algebra maps -/

variable {B' : Type u} [CommRing B'] [Algebra Γ(Spec (CommRingCat.of k), ⊤) B']
  (φ : B →ₐ[Γ(Spec (CommRingCat.of k), ⊤)] B')

/-- The base change `C_{B'} ⟶ C_B` along `φ : B → B'`. -/
abbrev bc : CT k C B' ⟶ CT k C B :=
  bcMap (C ↘ Sk) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (gB (S := Sk) B) (gB (S := Sk) B')
    (spec_map_comp_gB B φ)

lemma bc_preimage (O : C.Opens) : bc φ ⁻¹ᵁ (pB k C B ⁻¹ᵁ O) = pB k C B' ⁻¹ᵁ O := by
  rw [← Scheme.Hom.comp_preimage, bcMap_fst]

lemma bc_fA {O : C.Opens} {O' : (CT k C B).Opens} {O'' : (CT k C B').Opens}
    (h : O' ≤ pB k C B ⁻¹ᵁ O) (h' : O'' ≤ bc φ ⁻¹ᵁ O') (h'' : O'' ≤ pB k C B' ⁻¹ᵁ O) (a : Γ(C, O)) :
    (bc φ).appLE O' O'' h' (fA k C B h a) = fA k C B' h'' a := by
  change (bc φ).appLE O' O'' h' ((pB k C B).appLE O O' h a) = (pB k C B').appLE O O'' h'' a
  rw [appLE_appLE_apply]
  exact appLE_apply_eq (bcMap_fst _ _ _ _ _) _ _ a

lemma bc_fE {O' : (CT k C B).Opens} {O'' : (CT k C B').Opens} (h' : O'' ≤ bc φ ⁻¹ᵁ O') (e : B) :
    (bc φ).appLE O' O'' h' (fE k C B O' e) = fE k C B' O'' (φ e) := by
  change (bc φ).appLE O' O'' h' ((sB k C B).appLE ⊤ O' _
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv e)) =
    (sB k C B').appLE ⊤ O'' _ ((Scheme.ΓSpecIso (CommRingCat.of B')).inv (φ e))
  have e1 : (Scheme.ΓSpecIso (CommRingCat.of B')).inv (φ e) =
      (Spec.map (CommRingCat.ofHom φ.toRingHom)).appLE ⊤ ⊤ (by simp)
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv e) := by
    exact (congrArg (fun ψ ↦ ψ e)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))).trans
      (congrArg (fun ψ ↦ ψ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv e))
        (Scheme.Hom.appLE_eq_app (f := Spec.map (CommRingCat.ofHom φ.toRingHom)) (U := ⊤))).symm
  rw [e1, appLE_appLE_apply, appLE_appLE_apply]
  exact appLE_apply_eq (bcMap_snd _ _ _ _ _) _ _ _

/-! ### Twists on the two-chart covering of `C_B` -/

variable (U V : C.Opens) (hUV : U ⊔ V = ⊤)

include hUV in
lemma chart_sup : pB k C B ⁻¹ᵁ U ⊔ pB k C B ⁻¹ᵁ V = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]

variable (k C B) in
/-- The class of the twist `𝒪(1 + n)` for a square-zero `n` on the overlap of the charts. -/
def twK (n : Γ(CT k C B, pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V)) (hn : n * n = 0) : (CT k C B).Pic :=
  TwoChart.twPic (chart_sup U V hUV) (sqUnit n hn)

lemma twK_congr {n n' : Γ(CT k C B, pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V)} (hn : n * n = 0)
    (hn' : n' * n' = 0) (h : n = n') : twK k C B U V hUV n hn = twK k C B U V hUV n' hn' := by
  subst h; rfl

lemma twK_zero : twK k C B U V hUV 0 (mul_zero 0) = 0 := by
  rw [twK, sqUnit_zero]
  exact TwoChart.twPic_one _

/-- **Base change of a twist.** -/
lemma map_twK (n : Γ(CT k C B, pB k C B ⁻¹ᵁ U ⊓ pB k C B ⁻¹ᵁ V)) (hn : n * n = 0)
    (n' : Γ(CT k C B', pB k C B' ⁻¹ᵁ U ⊓ pB k C B' ⁻¹ᵁ V)) (hn' : n' * n' = 0)
    (h : (bc φ).appLE _ _ (by rw [Scheme.Hom.preimage_inf, bc_preimage, bc_preimage]) n = n') :
    Scheme.Pic.map (bc φ) (twK k C B U V hUV n hn) = twK k C B' U V hUV n' hn' := by
  refine TwoChart.map_twPic _ _ (bc (C := C) φ) (bc_preimage φ U) (bc_preimage φ V) _ _ ?_
  rw [sqUnit_val, sqUnit_val, map_add, map_one]
  exact congrArg (1 + ·) h.symm

end Curve

end CurvesJacobian.PicTangent
