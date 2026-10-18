/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RelEffCartierFinite
import Belyi.Converse.PuncturedLineBelyi
import Belyi.Curve.GeomIntegralTensorDomain
import Belyi.P1.Curve
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# The chart rings of `C ×_k T₀` and their fibres

Let `C` be a curve over a perfect field `k` (`Belyi.IsCurveOver`), `π : C → ℙ¹_k` finite, `T₀`
an affine `k`-scheme with `A = Γ(T₀)`, and let `U_i ⊆ X_{T₀} = C ×_k T₀` be the preimages of the
standard charts `D₊(x_i)` of `ℙ¹`, with chart rings `R_i = Γ(X_{T₀}, U_i)`, on which `A[X]` acts
through the chart coordinate (`CurvesJacobian.chartAlgebra`). This file proves the algebraic
inputs of the fibrewise flatness argument used for Stacks, Lemma 44.6.4 (Tag 0B9X):

* `CurvesJacobian.free_sections_chart`: `R_i` is a free (`projective_sections_chart`:
  projective) `A[X]`-module. Indeed `π` is finite and dominant (belyi's
  `isDominant_of_isFinite`), so `k[X] → Γ(C, π⁻¹D₊(x_i))` is injective and the chart ring of
  `C` is a finite torsion-free module over the PID `k[X]` (`free_curveChart`); and
  `R_i = A ⊗_k Γ(C, π⁻¹D₊(x_i))` is its base change along `k[X] → A[X]`
  (`free_tensor_polynomial`, via `Algebra.IsPushout`).
* `CurvesJacobian.isDomain_tensor_chart`, `isDomain_tensor_chart_inf`: for every field `K` over
  `A`, `K ⊗_A R_i` and `K ⊗_A R_{01}` are domains (`K ⊗_A R ≅ K ⊗_k Γ(C, W)` and `C` is
  geometrically integral: belyi's `isDomain_tensorProduct_of_geometricallyIntegral`); in
  particular `K ⊗_A R_{01} ≠ 0` (`nontrivial_tensor_chart_inf`).
* `CurvesJacobian.isLocalization_chart_inf_zero`, `isLocalization_chart_inf_one`:
  `R_{01} = Γ(X_{T₀}, U_0 ∩ U_1)` is the localization of `R_0` at the chart coordinate `τ`, and
  of `R_1` at `σ`, via restriction.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Polynomial Belyi
open TensorProduct

universe u

noncomputable section

namespace CurvesJacobian

section Algebra

/-- If `B` is free over `k₀[X]` acting through `r`, then `A ⊗_{k₀} B` is free over `A[X]` acting
through `1 ⊗ r`. -/
theorem free_tensor_polynomial {k₀ B : Type u} [CommRing k₀] [CommRing B] [Algebra k₀ B]
    (A : Type u) [CommRing A] [Algebra k₀ A] (r : B)
    (hB : letI := (aeval (R := k₀) r).toRingHom.toAlgebra; Module.Free k₀[X] B) :
    letI := (aeval (R := A) ((1 : A) ⊗ₜ[k₀] r)).toRingHom.toAlgebra
    Module.Free A[X] (A ⊗[k₀] B) := by
  letI i1 : Algebra k₀[X] B := (aeval (R := k₀) r).toRingHom.toAlgebra
  letI i2 : Algebra A[X] (A ⊗[k₀] B) := (aeval (R := A) ((1 : A) ⊗ₜ[k₀] r)).toRingHom.toAlgebra
  letI i3 : Algebra k₀[X] (A ⊗[k₀] B) :=
    (aeval (R := k₀) ((1 : A) ⊗ₜ[k₀] r)).toRingHom.toAlgebra
  letI i4 : Algebra B (A ⊗[k₀] B) := Algebra.TensorProduct.rightAlgebra
  letI i5 : Algebra k₀[X] A[X] := Polynomial.algebra k₀ A
  haveI : IsScalarTower k₀ k₀[X] B := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = aeval r (algebraMap k₀ k₀[X] c)
    rw [Polynomial.algebraMap_eq, aeval_C]
  haveI : IsScalarTower k₀ B (A ⊗[k₀] B) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = (1 : A) ⊗ₜ[k₀] algebraMap k₀ B c
    rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  haveI : IsScalarTower k₀[X] B (A ⊗[k₀] B) := IsScalarTower.of_algebraMap_eq fun p ↦ by
    change aeval ((1 : A) ⊗ₜ[k₀] r) p = (1 : A) ⊗ₜ[k₀] aeval r p
    rw [show (1 : A) ⊗ₜ[k₀] r = Algebra.TensorProduct.includeRight r from rfl,
      aeval_algHom_apply]
    rfl
  haveI : IsScalarTower k₀[X] A[X] (A ⊗[k₀] B) := IsScalarTower.of_algebraMap_eq fun p ↦ by
    change aeval ((1 : A) ⊗ₜ[k₀] r) p = aeval ((1 : A) ⊗ₜ[k₀] r) (p.map (algebraMap k₀ A))
    rw [aeval_map_algebraMap]
  haveI : IsScalarTower k₀ A[X] (A ⊗[k₀] B) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = aeval ((1 : A) ⊗ₜ[k₀] r) (algebraMap k₀ A[X] c)
    rw [Polynomial.algebraMap_apply, aeval_C, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  haveI : IsScalarTower A A[X] (A ⊗[k₀] B) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = aeval ((1 : A) ⊗ₜ[k₀] r) (algebraMap A A[X] c)
    rw [Polynomial.algebraMap_eq, aeval_C]
  have h₁ : Algebra.IsPushout k₀[X] B A[X] (A ⊗[k₀] B) :=
    (Algebra.IsPushout.comp_iff k₀ k₀[X] A A[X] (T := B) (T' := A ⊗[k₀] B)).mp inferInstance
  exact (Algebra.isPushout_iff _ _ _ _).mp h₁.symm |>.free

/-- If `k ≃ k'` and `K ⊗_k B` is a domain (for the `k`-structures induced from `k'`), then so is
`K ⊗_{k'} B`. -/
theorem isDomain_tensor_of_ringEquiv {k k' K B : Type u} [Field k] [CommRing k'] [Field K]
    [CommRing B] [Algebra k' K] [Algebra k' B] (e : k ≃+* k')
    (h : letI := ((algebraMap k' K).comp e.toRingHom).toAlgebra
      letI := ((algebraMap k' B).comp e.toRingHom).toAlgebra
      IsDomain (K ⊗[k] B)) : IsDomain (K ⊗[k'] B) := by
  letI : Algebra k k' := e.toRingHom.toAlgebra
  letI : Algebra k K := ((algebraMap k' K).comp e.toRingHom).toAlgebra
  letI : Algebra k B := ((algebraMap k' B).comp e.toRingHom).toAlgebra
  haveI : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hK : ∀ (c : k') (x : K), c • x = e.symm c • x := fun c x ↦ by
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hB : ∀ (c : k') (x : B), c • x = e.symm c • x := fun c x ↦ by
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  haveI : TensorProduct.CompatibleSMul k k' K B :=
    ⟨fun c x y ↦ by rw [hK, hB, TensorProduct.smul_tmul]⟩
  let φ := Algebra.TensorProduct.equivOfCompatibleSMul k k' K K B
  exact Function.Injective.isDomain (φ : K ⊗[k'] B →+* K ⊗[k] B) φ.injective

/-- Sections of an affine open over a basic open: restriction realises the localization. -/
lemma isLocalization_of_basicOpen_eq {X : Scheme.{u}} {U V : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) (hV : X.basicOpen f = V) (hle : V ≤ U) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    IsLocalization.Away f Γ(X, V) := by
  subst hV
  exact hU.isLocalization_basicOpen f

/-- An affine open with nonzero ring of sections is nonempty. -/
lemma nonempty_of_isAffineOpen {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    [Nontrivial Γ(X, W)] : Nonempty W :=
  ⟨hW.isoSpec.inv.base (Nonempty.some inferInstance)⟩

end Algebra

/-! ### The chart rings of a curve -/

section Curve

open Cech

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  {T₀ : Scheme.{u}} [T₀.Over (Spec (CommRingCat.of k))] [IsAffine T₀]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T₀ ↘ Sk)
local notation "pX" => pullback.fst (C ↘ Sk) (T₀ ↘ Sk)

variable [PerfectField k] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)

attribute [local instance] chartAlgebra curveChartAlgebra

/-- A finite morphism from a curve to `ℙ¹` is injective on sections (it is dominant and `ℙ¹` is
reduced). -/
lemma injective_app_of_isFinite [IsFinite π] (U : (ProjectiveLine.scheme k).Opens) :
    Function.Injective (π.app U) := by
  haveI : IsDominant π := @Belyi.isDominant_of_isFinite k _ _ C _ _ π (by assumption)
  haveI : IsReduced (ProjectiveLine.scheme k) := (inferInstance : IsReduced (P1 k))
  haveI := IsSchemeTheoreticallyDominant.of_isDominant π
  exact π.app_injective U

/-- The chart rings of `C` are nonzero. -/
lemma nontrivial_chart [IsFinite π] (i : Fin 2) :
    Nontrivial Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) := by
  haveI : Nontrivial Γ(ProjectiveLine.scheme k, ProjectiveLine.U k i) :=
    (ProjectiveLine.chartSections k i).symm.injective.nontrivial
  exact (injective_app_of_isFinite π _).nontrivial

/-- The charts of `C` are nonempty. -/
lemma nonempty_chart [IsFinite π] (i : Fin 2) : Nonempty (π ⁻¹ᵁ ProjectiveLine.U k i) :=
  haveI := nontrivial_chart π i
  nonempty_of_isAffineOpen ((ProjectiveLine.isAffineOpen_U k i).preimage π)

/-- The overlap of the charts of `C` is nonempty (it contains the generic point). -/
lemma nonempty_chart_inf [IsFinite π] :
    Nonempty (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)) := by
  haveI := IsCurveOver.isIntegral k C
  have h : ∀ i, genericPoint C ∈ π ⁻¹ᵁ ProjectiveLine.U k i := fun i ↦ by
    obtain ⟨x⟩ := nonempty_chart π i
    exact ((genericPoint_spec C).mem_open_set_iff (π ⁻¹ᵁ _).isOpen).mpr ⟨x.1, trivial, x.2⟩
  exact ⟨⟨genericPoint C, h 0, h 1⟩⟩

/-- The chart ring `Γ(C, π⁻¹ D₊(x_i))` is a domain. -/
lemma isDomain_chart [IsFinite π] (i : Fin 2) : IsDomain Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) := by
  haveI := IsCurveOver.isIntegral k C
  haveI := nonempty_chart π i
  infer_instance

/-- The chart ring `Γ(C, π⁻¹ D₊(x_i))` is not a field (it is integral over `k[X]`). -/
lemma not_isField_chart [IsFinite π] (i : Fin 2) : ¬ IsField Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) := by
  haveI := isDomain_chart π i
  letI := (π.app (ProjectiveLine.U k i)).hom.toAlgebra
  haveI : Module.Finite Γ(ProjectiveLine.scheme k, ProjectiveLine.U k i)
      Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) :=
    π.finite_app (ProjectiveLine.U k i) (ProjectiveLine.isAffineOpen_U k i)
  rw [← Algebra.IsIntegral.isField_iff_isField
    (R := Γ(ProjectiveLine.scheme k, ProjectiveLine.U k i)) (injective_app_of_isFinite π _)]
  intro h
  exact Polynomial.not_isField k ((ProjectiveLine.chartSections k i).symm.toMulEquiv.isField h)

/-- The chart coordinate `τ` of `Γ(C, π⁻¹ D₊(x_i))` is transcendental over the constants:
`Γ(Spec k)[X] → Γ(C, π⁻¹ D₊(x_i))`, `X ↦ τ`, is injective. -/
lemma injective_aeval_chart [IsFinite π] (i : Fin 2) :
    Function.Injective (aeval (R := Γ(Sk, ⊤))
      (π.app _ (ProjectiveLine.coord k i) : Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i))) := by
  set B := Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i)
  set τ : B := π.app _ (ProjectiveLine.coord k i)
  haveI := isDomain_chart π i
  have hk := isField_ΓSpec (k := k)
  have hinj : Function.Injective (algebraMap Γ(Sk, ⊤) B) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hne
    obtain ⟨d, hd⟩ := hk.mul_inv_cancel hne
    have := congrArg (algebraMap Γ(Sk, ⊤) B) hd
    rw [map_mul, hc, zero_mul, map_one] at this
    exact zero_ne_one this
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  obtain ⟨u, hu⟩ := hk.mul_inv_cancel (leadingCoeff_ne_zero.mpr hne)
  have hτ : IsIntegral Γ(Sk, ⊤) τ := by
    refine ⟨Polynomial.C u * p,
      monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [mul_comm]; exact hu), ?_⟩
    rw [← aeval_def, map_mul, hp, mul_zero]
  haveI : Module.Finite Γ(Sk, ⊤)[X] B := finite_curveChart π i
  set S := Algebra.adjoin Γ(Sk, ⊤) {τ}
  haveI : Module.Finite Γ(Sk, ⊤) S := Algebra.finite_adjoin_simple_of_isIntegral hτ
  letI : Algebra Γ(Sk, ⊤)[X] S :=
    (aeval (⟨τ, Algebra.self_mem_adjoin_singleton _ τ⟩ : S)).toRingHom.toAlgebra
  haveI : IsScalarTower Γ(Sk, ⊤)[X] S B := IsScalarTower.of_algebraMap_eq fun q ↦ by
    change aeval τ q = S.val (aeval (⟨τ, Algebra.self_mem_adjoin_singleton _ τ⟩ : S) q)
    rw [← aeval_algHom_apply]
    rfl
  haveI : Module.Finite S B := Module.Finite.of_restrictScalars_finite Γ(Sk, ⊤)[X] S B
  haveI : Module.Finite Γ(Sk, ⊤) B := Module.Finite.trans S B
  exact not_isField_chart π i ((Algebra.IsIntegral.isField_iff_isField hinj).mp hk)

/-- `Γ(C, π⁻¹ D₊(x_i))` is a free `Γ(Spec k)[X]`-module (finite torsion-free over a PID). -/
theorem free_curveChart [IsFinite π] (i : Fin 2) :
    Module.Free Γ(Sk, ⊤)[X] Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) := by
  haveI := isDomain_chart π i
  haveI : IsDomain Γ(Sk, ⊤) := (isField_ΓSpec (k := k)).isDomain
  haveI : IsPrincipalIdealRing Γ(Sk, ⊤)[X] := by
    let e : k ≃+* Γ(Sk, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact IsPrincipalIdealRing.of_surjective (mapRingHom e.toRingHom)
      (Polynomial.map_surjective _ e.surjective)
  haveI := finite_curveChart π i
  haveI : Module.IsTorsionFree Γ(Sk, ⊤)[X] Γ(C, π ⁻¹ᵁ ProjectiveLine.U k i) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (injective_aeval_chart π i)
  exact Module.free_of_finite_type_torsion_free'

omit [PerfectField k] [IsCurveOver k C] in
/-- The ring isomorphism `Γ(T₀) ⊗_k Γ(C, W) ≅ Γ(X_{T₀}, p⁻¹W)` as `Γ(T₀)`-algebras. -/
def sectionsBaseChangeAlgEquiv (W : C.Opens) (hW : IsAffineOpen W) (W' : (XT).Opens)
    (hW' : W' = pX ⁻¹ᵁ W) :
    Γ(T₀, ⊤) ⊗[Γ(Sk, ⊤)] Γ(C, W) ≃ₐ[Γ(T₀, ⊤)] Γ(XT, W') :=
  AlgEquiv.ofRingEquiv (f := pushoutTensorEquiv (isPushout_sections W hW W' hW')) fun c ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      pushoutTensorEquiv_tmul, map_one, mul_one]
    rfl

omit [PerfectField k] [IsCurveOver k C] in
lemma sectionsBaseChangeAlgEquiv_tmul (W : C.Opens) (hW : IsAffineOpen W) (W' : (XT).Opens)
    (hW' : W' = pX ⁻¹ᵁ W) (b : Γ(T₀, ⊤)) (r : Γ(C, W)) :
    sectionsBaseChangeAlgEquiv W hW W' hW' (b ⊗ₜ r) =
      (pullback.snd (C ↘ Sk) (T₀ ↘ Sk)).appLE ⊤ W' (by simp) b * (pX).appLE W W' hW'.le r :=
  pushoutTensorEquiv_tmul _ b r

/-- **The chart rings are free over `Γ(T₀)[X]`**: `Γ(X_{T₀}, U_i)` is a free module over
`Γ(T₀)[X]` acting through the chart coordinate. -/
theorem free_sections_chart [IsFinite π] (i : Fin 2) :
    Module.Free Γ(T₀, ⊤)[X]
      ((XT).presheaf.obj (op (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i))) := by
  set W := π ⁻¹ᵁ ProjectiveLine.U k i
  have hW : IsAffineOpen W := (ProjectiveLine.isAffineOpen_U k i).preimage π
  set r : Γ(C, W) := π.app _ (ProjectiveLine.coord k i)
  let e := sectionsBaseChangeAlgEquiv (T₀ := T₀) W hW
    (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i) rfl
  have h₀ := free_tensor_polynomial (k₀ := Γ(Sk, ⊤)) Γ(T₀, ⊤) r (free_curveChart π i)
  letI := (aeval (R := Γ(T₀, ⊤)) ((1 : Γ(T₀, ⊤)) ⊗ₜ[Γ(Sk, ⊤)] r)).toRingHom.toAlgebra
  have he : e ((1 : Γ(T₀, ⊤)) ⊗ₜ r) = chartCoord π i := by
    rw [sectionsBaseChangeAlgEquiv_tmul, map_one, one_mul]
    change _ = (pX).app W r
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  let e' : Γ(T₀, ⊤) ⊗[Γ(Sk, ⊤)] Γ(C, W) ≃ₗ[Γ(T₀, ⊤)[X]]
      (XT).presheaf.obj (op (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i)) :=
    { e.toLinearEquiv with
      map_smul' := fun p y ↦ by
        change e (aeval _ p * y) = aeval (chartCoord (T₀ := T₀) π i) p * e y
        rw [map_mul, ← he, ← aeval_algHom_apply] }
  exact Module.Free.of_equiv e'

/-- The chart rings are projective over `Γ(T₀)[X]`. -/
theorem projective_sections_chart [IsFinite π] (i : Fin 2) :
    Module.Projective Γ(T₀, ⊤)[X]
      ((XT).presheaf.obj (op (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i))) :=
  haveI := free_sections_chart (T₀ := T₀) π i
  inferInstance

omit [PerfectField k] [IsCurveOver k C] in
/-- The chart rings are flat over `Γ(T₀)`. -/
theorem flat_sections_chart [IsFinite π] (i : Fin 2) :
    Module.Flat Γ(T₀, ⊤)
      ((XT).presheaf.obj (op (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i))) :=
  flat_sections_baseChange _ ((ProjectiveLine.isAffineOpen_U k i).preimage π) _ rfl

omit [PerfectField k] [IsCurveOver k C] in
/-- The overlap of the charts has sections flat over `Γ(T₀)`. -/
theorem flat_sections_chart_inf [IsFinite π] :
    Module.Flat Γ(T₀, ⊤) Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) :=
  flat_sections_baseChange _ ((ProjectiveLine.isAffineOpen_U_inf k).preimage π) _ rfl

omit [PerfectField k] [IsCurveOver k C] in
/-- For a field `K` over `Γ(T₀)` and a nonempty affine open `W` of `C`,
`K ⊗_{Γ(T₀)} Γ(X_{T₀}, p⁻¹W) ≅ K ⊗_k Γ(C, W)` is a domain (`C` is geometrically integral). -/
theorem isDomain_tensor_sections [GeometricallyIntegral (C ↘ Sk)] (W : C.Opens)
    (hW : IsAffineOpen W) [Nonempty W] (W' : (XT).Opens) (hW' : W' = pX ⁻¹ᵁ W)
    (K : Type u) [Field K] [Algebra Γ(T₀, ⊤) K] :
    IsDomain (K ⊗[Γ(T₀, ⊤)] Γ(XT, W')) := by
  letI : Algebra Γ(Sk, ⊤) K :=
    ((algebraMap Γ(T₀, ⊤) K).comp (algebraMap Γ(Sk, ⊤) Γ(T₀, ⊤))).toAlgebra
  haveI : IsScalarTower Γ(Sk, ⊤) Γ(T₀, ⊤) K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e₂ := sectionsBaseChangeAlgEquiv (T₀ := T₀) W hW W' hW'
  let e₃ : K ⊗[Γ(T₀, ⊤)] Γ(XT, W') ≃ₐ[K] K ⊗[Γ(Sk, ⊤)] Γ(C, W) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e₂.symm).trans
      (Algebra.TensorProduct.cancelBaseChange Γ(Sk, ⊤) Γ(T₀, ⊤) K K Γ(C, W))
  suffices IsDomain (K ⊗[Γ(Sk, ⊤)] Γ(C, W)) from
    Function.Injective.isDomain e₃.toRingEquiv.toRingHom e₃.toRingEquiv.injective
  let e : k ≃+* Γ(Sk, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  refine isDomain_tensor_of_ringEquiv e ?_
  letI : Algebra k K := ((algebraMap Γ(Sk, ⊤) K).comp e.toRingHom).toAlgebra
  letI : Algebra k Γ(C, W) := ((algebraMap Γ(Sk, ⊤) Γ(C, W)).comp e.toRingHom).toAlgebra
  haveI : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton (C ↘ Sk)
  haveI : Nonempty (Spec (CommRingCat.of Γ(C, W))) := (inferInstance : Nonempty (Spec Γ(C, W)))
  refine Belyi.isDomain_tensorProduct_of_geometricallyIntegral (C ↘ Sk) hW.fromSpec ?_
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (C ↘ Sk) (isAffineOpen_top Sk) hW (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- **The fibres of the chart rings are domains**: for every field `K` over `Γ(T₀)`,
`K ⊗_{Γ(T₀)} Γ(X_{T₀}, U_i)` is a domain. -/
theorem isDomain_tensor_chart [IsFinite π] (i : Fin 2) (K : Type u) [Field K]
    [Algebra Γ(T₀, ⊤) K] :
    IsDomain (K ⊗[Γ(T₀, ⊤)]
      (XT).presheaf.obj (op (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i))) :=
  haveI := nonempty_chart π i
  isDomain_tensor_sections _ ((ProjectiveLine.isAffineOpen_U k i).preimage π) _ rfl K

/-- The fibres of the overlap ring are domains. -/
theorem isDomain_tensor_chart_inf [IsFinite π] (K : Type u) [Field K] [Algebra Γ(T₀, ⊤) K] :
    IsDomain (K ⊗[Γ(T₀, ⊤)] Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1)) :=
  haveI := nonempty_chart_inf π
  isDomain_tensor_sections _ ((ProjectiveLine.isAffineOpen_U_inf k).preimage π) _ rfl K

/-- **The fibres of the overlap ring are nonzero**: `K ⊗_{Γ(T₀)} Γ(X_{T₀}, U_0 ∩ U_1) ≠ 0`. -/
theorem nontrivial_tensor_chart_inf [IsFinite π] (K : Type u) [Field K] [Algebra Γ(T₀, ⊤) K] :
    Nontrivial (K ⊗[Γ(T₀, ⊤)] Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1)) :=
  (isDomain_tensor_chart_inf (T₀ := T₀) π K).toNontrivial

omit [PerfectField k] [IsCurveOver k C] in
/-- **The overlap ring is a localization of `R_0`**: restriction realises
`Γ(X_{T₀}, U_0 ∩ U_1)` as `Γ(X_{T₀}, U_0)[1/τ]`. -/
theorem isLocalization_chart_inf_zero [IsFinite π] :
    letI := ((XT).presheaf.map (homOfLE (inf_le_left :
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
        curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _)).op).hom.toAlgebra
    IsLocalization.Away (chartCoord (T₀ := T₀) π 0)
      Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
        curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) :=
  isLocalization_of_basicOpen_eq (isAffineOpen_chart π 0) _ (basicOpen_chartτ _) _

omit [PerfectField k] [IsCurveOver k C] in
/-- **The overlap ring is a localization of `R_1`**: restriction realises
`Γ(X_{T₀}, U_0 ∩ U_1)` as `Γ(X_{T₀}, U_1)[1/σ]`. -/
theorem isLocalization_chart_inf_one [IsFinite π] :
    letI := ((XT).presheaf.map (homOfLE (inf_le_right :
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
        curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _)).op).hom.toAlgebra
    IsLocalization.Away (chartCoord (T₀ := T₀) π 1)
      Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
        curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) :=
  isLocalization_of_basicOpen_eq (isAffineOpen_chart π 1) _ (basicOpen_chartσ _) _

end Curve

end CurvesJacobian
