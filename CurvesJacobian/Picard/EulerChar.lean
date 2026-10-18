/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CurvePerfect
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Local constancy of the Euler characteristic (Stacks, Lemma 36.32.2, Tag 0B9T)

Stacks, Lemma 36.32.2 (Tag 0B9T): for `f : X → S` proper of finite presentation and `ℱ` of
finite presentation and flat over `S`, the function `s ↦ χ(X_s, ℱ_s)` is locally constant on
`S`, and its formation commutes with base change. This is the input to the decomposition
`Pic_{X/k} = ∐_d Pic^d_{X/k}` (degree via `χ = d + 1 − g`) in the proof of Stacks,
Lemma 44.6.7 (Tag 0BA0).

* `CurvesJacobian.TwoTerm.finrank_ker_sub_finrank_coker`: for a map `δ : K₀ → K₁` of finite
  projective `A`-modules and a field `B` over `A`, `dim ker(B ⊗ δ) − dim coker(B ⊗ δ)` is
  `rank K₀ − rank K₁` at the image point of `Spec B` in `Spec A` (rank–nullity).
* `CurvesJacobian.exists_isLocallyConstant_chi`: for an invertible sheaf `L` on `C ×_k T`
  (`C` a curve, `T` any affine `k`-scheme) there is a locally constant `χ : Spec Γ(T) → ℤ` such
  that for every affine `T`-scheme `T'` with `Γ(T')` a field, the Euler characteristic
  `h⁰ − h¹` of the chart Čech complex of `L_{T'}` is `χ` at the image point of `T'` (via the
  perfect model of `CurvesJacobian.exists_finite_projective_cech'`, the curve case of
  Stacks, Lemma 36.30.4, Tag 0B91).
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct Module

universe u

noncomputable section

namespace CurvesJacobian

namespace TwoTerm

variable {A : Type u} [CommRing A] {K₀ K₁ : Type u} [AddCommGroup K₀] [Module A K₀]
  [AddCommGroup K₁] [Module A K₁] [Module.Finite A K₀] [Module.Projective A K₀]
  [Module.Finite A K₁] [Module.Projective A K₁]

lemma finrank_baseChange_eq_rankAtStalk (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] (B : Type u) [Field B] [Algebra A B]
    (q : PrimeSpectrum B) :
    finrank B (B ⊗[A] M) = rankAtStalk M (q.comap (algebraMap A B)) := by
  rw [← rankAtStalk_baseChange]
  simp

/-- **Euler characteristic of a two-term perfect complex at a point** (rank–nullity): for a
map `δ : K₀ → K₁` of finite projective `A`-modules and a field `B` over `A`, the Euler
characteristic `dim ker(B ⊗ δ) − dim coker(B ⊗ δ)` is `rank K₀ − rank K₁` at the image of
`Spec B` in `Spec A`. -/
theorem finrank_ker_sub_finrank_coker (δ : K₀ →ₗ[A] K₁) (B : Type u) [Field B] [Algebra A B]
    (q : PrimeSpectrum B) :
    (finrank B (LinearMap.ker (δ.baseChange B)) : ℤ) -
        finrank B ((B ⊗[A] K₁) ⧸ LinearMap.range (δ.baseChange B)) =
      (rankAtStalk K₀ (q.comap (algebraMap A B)) : ℤ) -
        rankAtStalk K₁ (q.comap (algebraMap A B)) := by
  have h0 := LinearMap.finrank_range_add_finrank_ker (δ.baseChange B)
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (δ.baseChange B))
  rw [← finrank_baseChange_eq_rankAtStalk K₀ B q, ← finrank_baseChange_eq_rankAtStalk K₁ B q]
  omega

omit [Module.Finite A K₀] [Module.Projective A K₀] [Module.Finite A K₁]
  [Module.Projective A K₁] in
/-- The rank difference `p ↦ rank_p K₀ − rank_p K₁` of finite projective modules is locally
constant on `Spec A`. -/
theorem isLocallyConstant_rank_sub [Module.FinitePresentation A K₀] [Module.Flat A K₀]
    [Module.FinitePresentation A K₁] [Module.Flat A K₁] :
    IsLocallyConstant fun p : PrimeSpectrum A ↦
      (rankAtStalk K₀ p : ℤ) - rankAtStalk K₁ p :=
  IsLocallyConstant.comp₂ isLocallyConstant_rankAtStalk isLocallyConstant_rankAtStalk
    fun a b : ℕ ↦ (a : ℤ) - b

end TwoTerm

section Curve

open Cech Belyi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]
  (π : C ⟶ ProjectiveLine.scheme k) [PerfectField k] [IsCurveOver k C] [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T ↘ Sk)

/-- **The Euler characteristic of a line bundle on `C ×_k T` is locally constant on `T`**
(Stacks, Lemma 36.32.2, Tag 0B9T, for invertible sheaves on a curve, computed by the chart
Čech complex): for `L` invertible on `X_T`, `T` any affine `k`-scheme, there is a locally
constant `χ : Spec Γ(T) → ℤ` such that for every affine `T`-scheme `T'` whose ring of global
sections is a field, `h⁰(L_{T'}) − h¹(L_{T'}) = χ(t')` with `t'` the image of `T'`. -/
theorem exists_isLocallyConstant_chi (L : (XT).Modules) [L.IsInvertible] :
    ∃ χ : PrimeSpectrum Γ(T, ⊤) → ℤ, IsLocallyConstant χ ∧
      ∀ (T' : Scheme.{u}) [T'.Over T] [IsAffine T'] (_ : IsField Γ(T', ⊤))
        (q : PrimeSpectrum Γ(T', ⊤)),
        (finrank Γ(T', ⊤) (cechModH0 T' (lineBundleBaseChange (S := T) (T := T') L)
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0))
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1))) : ℤ) -
          finrank Γ(T', ⊤) (cechModH1 T' (lineBundleBaseChange (S := T) (T := T') L)
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0))
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1))) =
        χ (q.comap (algebraMap Γ(T, ⊤) Γ(T', ⊤))) := by
  obtain ⟨K₀, K₁, δ, h₁, h₂, h₃, h₄, H⟩ := exists_finite_projective_cech' (T := T) π L
  haveI : Module.FinitePresentation Γ(T, ⊤) K₀ := Module.finitePresentation_of_projective _ _
  haveI : Module.FinitePresentation Γ(T, ⊤) K₁ := Module.finitePresentation_of_projective _ _
  refine ⟨fun p ↦ (rankAtStalk K₀ p : ℤ) - rankAtStalk K₁ p,
    TwoTerm.isLocallyConstant_rank_sub, fun T' _ _ hF q ↦ ?_⟩
  letI := hF.toField
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := H T'
  rw [← e₀.finrank_eq, ← e₁.finrank_eq]
  exact TwoTerm.finrank_ker_sub_finrank_coker δ Γ(T', ⊤) q

end Curve

end CurvesJacobian
