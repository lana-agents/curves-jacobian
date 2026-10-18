/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Cor37c
import CurvesJacobian.Cusp.FillAutUnique

/-!
# [AbsTopII] Corollary 3.8, uniqueness, and Corollary 3.7 (b), uniqueness of the lifting

`Topics in Absolute Anabelian Geometry II.txt` l.4794–4842 (Corollary 3.8): for `φ : Π₁ ≅ Π₂`
and `U_{X₁}`, the isomorphism `φ_U : Π_{U_{X₁}} ≅ Π_{U_{X₂}}` compatible with `φ` is unique up to
composition with inner automorphisms of `Π_{U_{X₂}}` defined by elements of
`ker(Π_{U_{X₂}} ↠ Π₂)` ("follows immediately from our assumption that the rel-isom-DGC holds",
l.4840). Here `X = CX.U` is an affine hyperbolic curve over a number field, `U_X ⊆ X` a nonempty
open (`subCurve`), `Π_{U_X} ↠ Π_X` is `fillMap` followed by a change of base point `α₀` to the
base point of `X` (`cor38Fill`), and the DGC is the explicit hypothesis `hDGC : RelIsomDGC K`.

* `CurvesJacobian.Cusp.cor38_unique`: two continuous isomorphisms `φ₁, φ₂ : P ≃ₜ* Π_{U_X}` with
  the same composite `P → Π_X` differ by `conj(n)`, `n ∈ ker(Π_{U_X} ↠ Π_X)`.
* `CurvesJacobian.Cusp.cor37b_lift_unique`: two automorphisms of `Π_{U_X}` lifting the same
  automorphism of `Π_X` up to an inner automorphism agree up to an inner automorphism (the
  uniqueness of the lifting of the outer action in [AbsTopII] Cor 3.7 (b), l.4698–4775, for the
  filling `Π_U ↠ Π_V`, applied with `X := V`, `U_X := U`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (CX : HypCurve K)
  (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
  (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **`Π_{U_X} ↠ Π_X`**: filling the cusps of `U_X` in `X`, moved to the base point of `X`
along `α₀`. -/
def cor38Fill : (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi →*
    (arithmeticExt Ω CX hcX).Pi :=
  (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
    α₀)).symm.toMulEquiv.toMonoidHom.comp
      (fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX).toMonoidHom

lemma cor38Fill_eq_iff (x y) : cor38Fill Ω CX hcX UX hUX hne α₀ x =
    cor38Fill Ω CX hcX UX hUX hne α₀ y ↔
      fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX x =
        fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX y :=
  (autContinuousMulEquivOfIso _).symm.injective.eq_iff

/-- **[AbsTopII] Corollary 3.8, uniqueness**: continuous isomorphisms `φ₁, φ₂ : P ≃ₜ* Π_{U_X}`
with the same composite to `Π_X` differ by an inner automorphism of `Π_{U_X}` defined by an
element of `ker(Π_{U_X} ↠ Π_X)`. -/
theorem cor38_unique (hDGC : RelIsomDGC K) {P : Type*} [Group P] [TopologicalSpace P]
    (φ₁ φ₂ : P ≃ₜ* (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi)
    (hφ : ∀ p, cor38Fill Ω CX hcX UX hUX hne α₀ (φ₂ p) = cor38Fill Ω CX hcX UX hUX hne α₀ (φ₁ p)) :
    ∃ n ∈ (cor38Fill Ω CX hcX UX hUX hne α₀).ker, ∀ p, φ₂ p = n * φ₁ p * n⁻¹ := by
  obtain ⟨n, hn, h⟩ := exists_eq_conj_comp_of_fillMap Ω (subCurve CX UX hUX hne)
    (compl_nonempty_of_le hUX hcX) hUX hcX CX.hyperbolic hDGC φ₁ φ₂ 1 fun p ↦ by
      rw [one_mul, inv_one, mul_one]
      exact (cor38Fill_eq_iff Ω CX hcX UX hUX hne α₀ _ _).1 (hφ p)
  refine ⟨n, ?_, h⟩
  rw [MonoidHom.mem_ker, ← map_one (cor38Fill Ω CX hcX UX hUX hne α₀)]
  exact (cor38Fill_eq_iff Ω CX hcX UX hUX hne α₀ _ _).2 (hn.trans (map_one _).symm)

/-- **[AbsTopII] Corollary 3.7 (b), uniqueness of the lifting**: two automorphisms `ψ₁, ψ₂` of
`Π_{U_X}` lifting automorphisms of `Π_X` that differ by `conj(s)` differ by `conj(n)` with `n`
over `s`. -/
theorem cor37b_lift_unique (hDGC : RelIsomDGC K)
    (ψ₁ ψ₂ : (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi ≃ₜ*
      (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi)
    (s : (arithmeticExt Ω CX hcX).Pi)
    (hs : ∀ σ, cor38Fill Ω CX hcX UX hUX hne α₀ (ψ₂ σ) =
      s * cor38Fill Ω CX hcX UX hUX hne α₀ (ψ₁ σ) * s⁻¹) :
    ∃ n, cor38Fill Ω CX hcX UX hUX hne α₀ n = s ∧ ∀ σ, ψ₂ σ = n * ψ₁ σ * n⁻¹ := by
  set e := autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
    α₀)
  have hfill : ∀ x, fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX x =
      e (cor38Fill Ω CX hcX UX hUX hne α₀ x) := fun x ↦
    (e.apply_symm_apply _).symm
  obtain ⟨n, hn, h⟩ := exists_eq_conj_comp_of_fillMap Ω (subCurve CX UX hUX hne)
    (compl_nonempty_of_le hUX hcX) hUX hcX CX.hyperbolic hDGC ψ₁ ψ₂ (e s) fun σ ↦ by
      have := congrArg e (hs σ)
      rw [map_mul, map_mul, map_inv] at this
      rw [hfill, hfill]
      exact this
  refine ⟨n, e.injective ?_, h⟩
  rw [← hfill, hn]

end CurvesJacobian.Cusp
