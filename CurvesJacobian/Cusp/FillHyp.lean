/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithmeticFill
import CurvesJacobian.Cusp.HypOfNonabelian

/-!
# Hyperbolicity of a filled curve from a non-commutative `Δ_{U'}`

Let `C = (X̄ ⊇ U)` be a hyperbolic curve over a number field `K` and `U ⊆ U' ⊆ X̄` an open with
a cusp. Before knowing that `(X̄, U')` is hyperbolic, the arithmetic fundamental group
`Π_{U'} = π₁ᵉᵗ(Spec Γ(U'), fillPoint)` and its projection `projGkFill : Π_{U'} → G_K` are
already defined. This file shows:

* `CurvesJacobian.Cusp.ker_projGkFill_eq_range`: `ker(Π_{U'} → G_K)` is the image of the
  geometric fundamental group `π₁ᵉᵗ(Spec (Ω ⊗[K] Γ(U')), fillPoint)` (homotopy exact sequence,
  pi1 `ker_toGaloisGroup_eq_range`);
* **`CurvesJacobian.Cusp.two_lt_of_not_commute_ker_projGkFill`**: if `ker projGkFill` is not
  commutative then `2 < 2 g(X̄) + Σ_{c ∉ U'} [κ(c) : K]`, i.e. `(X̄, U')` is hyperbolic (the
  hypothesis `hyp` of `fillCurve`);
* the corollaries `two_lt_of_not_commute_subgroup_projGkFill` (a non-commutative subgroup of
  `ker projGkFill`) and `two_lt_of_not_commute_fillMap` (two elements of `ker projGk` whose images
  under `fillMap` do not commute).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens} (h : C.U ≤ U')
  (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [Algebra.IsAlgebraic K Ω] in
/-- `fillPoint` is an `Ω`-rational point of `Spec (Ω ⊗[K] Γ(U'))`. -/
lemma fillPoint_spec_ratl :
    fillPoint Ω C hc h ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] Γ(C.Xbar, U')))) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) := by
  have e : Spec.map (CommRingCat.ofHom (tensorRes K Ω h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] Γ(C.Xbar, U')))) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] Γ(C.Xbar, C.U)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (tensorRes K Ω h).commutes x
  rw [fillPoint, Category.assoc, e]
  exact basePoint_spec₁ Ω C hc

include hc' in
/-- **`Δ_{U'} = ker(Π_{U'} → G_K)` is the image of the geometric fundamental group**
`π₁ᵉᵗ(Spec (Ω ⊗[K] Γ(U')), fillPoint)` (homotopy exact sequence). -/
theorem ker_projGkFill_eq_range :
    (projGkFill Ω C hc h).toMonoidHom.ker =
      (fundamentalGroupMap (baseChangeSpec K Ω Γ(C.Xbar, U'))
        (rfl : fillPoint Ω C hc h ≫ _ = _)).toMonoidHom.range := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty U' := (C.nonempty.mono h).to_subtype
  haveI : IsIntegral (Spec (CommRingCat.of Γ(C.Xbar, U'))) :=
    isIntegral_spec_sections (isAffineOpen_of_le C h hc')
  haveI := isIntegral_specTensor_of_le Ω C h hc'
  rw [← ker_toGaloisGroup_eq_range (fillPoint Ω C hc h) (fillPoint_spec_ratl Ω C hc h)
    (fillPoint_spec₂ Ω C hc h)]
  ext γ
  simp only [MonoidHom.mem_ker, toGaloisGroup, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  rfl

include hc' in
/-- **Hyperbolicity of the filled curve `(X̄, U')` from a non-commutative `Δ_{U'}`**: if
`ker(projGkFill : Π_{U'} → G_K)` is not commutative then `2 < 2 g(X̄) + Σ_{c ∉ U'} [κ(c) : K]`
(the hypothesis `hyp` of `fillCurve`). -/
theorem two_lt_of_not_commute_ker_projGkFill
    (hnc : ∃ a ∈ (projGkFill Ω C hc h).toMonoidHom.ker,
      ∃ b ∈ (projGkFill Ω C hc h).toMonoidHom.ker, a * b ≠ b * a) :
    haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U' := by
  have hU' := isAffineOpen_of_le C h hc'
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  rw [ker_projGkFill_eq_range Ω C hc h hc'] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  let e := fundamentalGroupEquivOfIso (specTensorIsoBaseChangeOpen K Ω hU') (fillPoint Ω C hc h)
  refine two_lt_locAn_of_not_commute_baseChange K Ω U' (C.nonempty.mono h) hc'
    (fillPoint Ω C hc h ≫ (specTensorIsoBaseChangeOpen K Ω hU').hom) ⟨e a', e b', fun H ↦ ?_⟩
  apply hab
  have H' : a' * b' = b' * a' := e.injective (by rw [map_mul, map_mul]; exact H)
  rw [← map_mul, ← map_mul]
  exact congrArg _ H'

include hc' in
/-- **Hyperbolicity of `(X̄, U')` from a non-commutative subgroup of `Δ_{U'}`.** -/
theorem two_lt_of_not_commute_subgroup_projGkFill
    {H : Subgroup π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U'))}
    (hH : H ≤ (projGkFill Ω C hc h).toMonoidHom.ker) (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) :
    haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U' := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  exact two_lt_of_not_commute_ker_projGkFill Ω C hc h hc' ⟨a, hH ha, b, hH hb, hab⟩

include hc' in
/-- **Hyperbolicity of `(X̄, U')` from `Δ_U`**: if two elements of `Δ_U = ker(Π_U → G_K)` have
non-commuting images under `fillMap : Π_U → Π_{U'}`, then `(X̄, U')` is hyperbolic. -/
theorem two_lt_of_not_commute_fillMap
    (hnc : ∃ a ∈ (projGk Ω C hc).toMonoidHom.ker, ∃ b ∈ (projGk Ω C hc).toMonoidHom.ker,
      fillMap Ω C hc h a * fillMap Ω C hc h b ≠ fillMap Ω C hc h b * fillMap Ω C hc h a) :
    haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U' := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  have hmem : ∀ x ∈ (projGk Ω C hc).toMonoidHom.ker,
      fillMap Ω C hc h x ∈ (projGkFill Ω C hc h).toMonoidHom.ker := fun x hx ↦ by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (projGkFill_fillMap Ω C hc h x).trans hx
  exact two_lt_of_not_commute_ker_projGkFill Ω C hc h hc'
    ⟨_, hmem a ha, _, hmem b hb, hab⟩

end CurvesJacobian.Cusp
