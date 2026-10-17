/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Pushouts of commutative rings: quotients and nonzerodivisors

The commutative algebra behind the base change of relative effective Cartier divisors
(Stacks, Tag 056Q).

* `CurvesJacobian.ker_inl_of_isPushout`: in a pushout square of commutative rings along a
  surjection `q : A → C`, the kernel of `B → D` is the extension of `ker q` to `B`.
* `CurvesJacobian.isSMulRegular_inl_of_isPushout`: if `g ∈ R` is a nonzerodivisor and `R/g` is
  flat over `A`, then the image of `g` in `D = R ⊗_A B` is a nonzerodivisor.
-/

open CategoryTheory Limits TensorProduct

universe u

namespace CurvesJacobian

section Kernel

variable {A B C D : CommRingCat.{u}} {φ : A ⟶ B} {q : A ⟶ C} {q' : B ⟶ D} {φ' : C ⟶ D}

/-- The map `C ≅ A/ker q → B/(ker q)B` used to compare a pushout along a surjection with a
quotient. -/
noncomputable def quotPushoutAux (φ : A ⟶ B) (q : A ⟶ C) (hq : Function.Surjective q) :
    C ⟶ CommRingCat.of (B ⧸ (RingHom.ker q.hom).map φ.hom) :=
  CommRingCat.ofHom ((Ideal.quotientMap _ φ.hom Ideal.le_comap_map).comp
    (RingHom.quotientKerEquivOfSurjective hq).symm.toRingHom)

lemma quotPushoutAux_comp (φ : A ⟶ B) (q : A ⟶ C) (hq : Function.Surjective q) (a : A) :
    quotPushoutAux φ q hq (q a) = Ideal.Quotient.mk _ (φ a) := by
  have : (RingHom.quotientKerEquivOfSurjective hq).symm (q a) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [quotPushoutAux, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, Ideal.quotientMap_mk]

/-- In a pushout square of commutative rings along a surjection `q : A → C`, the kernel of the
map `B → D` is the extension of `ker q`. -/
theorem ker_inl_of_isPushout (h : IsPushout φ q q' φ') (hq : Function.Surjective q) :
    RingHom.ker q'.hom = (RingHom.ker q.hom).map φ.hom := by
  apply le_antisymm
  · intro x hx
    let π : B ⟶ CommRingCat.of (B ⧸ (RingHom.ker q.hom).map φ.hom) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    have w : φ ≫ π = q ≫ quotPushoutAux φ q hq := by
      ext a
      exact (quotPushoutAux_comp φ q hq a).symm
    have hπ : π x = 0 := by
      rw [← h.inl_desc π _ w, CommRingCat.comp_apply, RingHom.mem_ker.mp hx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hπ
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply, h.w,
      CommRingCat.comp_apply, RingHom.mem_ker.mp ha, map_zero]

end Kernel

section Regular

variable {A R B : Type u} [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]

/-- Multiplication by `g ⊗ 1` on `R ⊗_A B` is `(g ·) ⊗ id`. -/
lemma mul_tmul_one_eq_rTensor (g : R) (x : R ⊗[A] B) :
    (g ⊗ₜ[A] (1 : B)) * x = ((LinearMap.mulLeft A g).rTensor B) x := by
  induction x with
  | zero => simp
  | tmul r b => simp
  | add x y hx hy => rw [mul_add, hx, hy, map_add]

/-- If `g ∈ R` is a nonzerodivisor and `R/g` is `A`-flat, then `g ⊗ 1` is a nonzerodivisor of
`R ⊗_A B`. -/
theorem isSMulRegular_tmul_one {g : R} (hg : IsSMulRegular R g)
    [Module.Flat A (R ⧸ Ideal.span {g})] :
    IsSMulRegular (R ⊗[A] B) (g ⊗ₜ[A] (1 : B)) := by
  have hex : Function.Exact (LinearMap.mulLeft A g)
      (Ideal.Quotient.mkₐ A (Ideal.span {g})).toLinearMap := by
    intro x
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton',
      Set.mem_range, LinearMap.mulLeft_apply]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]⟩⟩
  have hinj : Function.Injective ((LinearMap.mulLeft A g).lTensor B) :=
    LinearMap.lTensor_injective_of_exact_of_flat _ (Ideal.Quotient.mkₐ_surjective A _) _
      (fun x y hxy ↦ hg hxy) hex B
  have hinj' : Function.Injective ((LinearMap.mulLeft A g).rTensor B) := by
    have : (LinearMap.mulLeft A g).rTensor B = (TensorProduct.comm A B R).toLinearMap ∘ₗ
        (LinearMap.mulLeft A g).lTensor B ∘ₗ (TensorProduct.comm A R B).toLinearMap := by
      ext r b
      simp
    rw [this]
    simpa using hinj
  intro x y hxy
  simp only [smul_eq_mul, mul_tmul_one_eq_rTensor] at hxy
  exact hinj' hxy

end Regular

section PushoutRegular

variable {A R B D : CommRingCat.{u}} {φ : A ⟶ R} {ψ : A ⟶ B} {φ' : R ⟶ D} {ψ' : B ⟶ D}

/-- In a pushout square of commutative rings `D = R ⊗_A B`, if `g ∈ R` is a nonzerodivisor and
`R/g` is `A`-flat, then the image of `g` in `D` is a nonzerodivisor. -/
theorem isSMulRegular_inl_of_isPushout (h : IsPushout φ ψ φ' ψ') {g : R}
    (hg : IsSMulRegular R g)
    (hflat : ((Ideal.Quotient.mk (Ideal.span {g})).comp φ.hom).Flat) :
    IsSMulRegular D (φ' g) := by
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  haveI : Module.Flat A (R ⧸ Ideal.span {g}) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact hflat
  let t := CommRingCat.isPushout_tensorProduct A R B
  let e := t.isoPushout ≪≫ h.isoPushout.symm
  have he : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom) ≫ e.hom = φ' := by
    simp [e]
  have hreg := isSMulRegular_tmul_one (A := A) (B := B) hg
  intro x y hxy
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  apply hreg
  simp only [smul_eq_mul] at hxy ⊢
  have hg' : g ⊗ₜ[A] (1 : B) = e.inv (φ' g) := by
    rw [← he, CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id,
      CommRingCat.id_apply]
    rfl
  rw [hg', ← map_mul, ← map_mul, hxy]

end PushoutRegular

end CurvesJacobian
