/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Inertia
import CurvesJacobian.Cusp.PlaceTransitivity

/-!
# Cuspidal inertia groups over one place of `L` are conjugate (MR8.3, task 2 (iii))

Setting of `CurvesJacobian.Cusp.Inertia`. For `σ ∈ H` and a place `W` of `Ω`:

* `GaloisPi1.conj_mem_inertia`: `σ τ σ⁻¹` is an inertia element of `σ(W)` for every inertia
  element `τ` of `W`;
* `CurvesJacobian.Cusp.cuspInertia_comap`: `cuspInertia U (σ W)` is the conjugate of
  `cuspInertia U W` by the image of `σ` in `π₁ᵉᵗ(U)`;
* `CurvesJacobian.Cusp.isCentredOn_comap_iff`: `σ(W)` is centred on `U` iff `W` is;
* `CurvesJacobian.Cusp.exists_cuspInertia_eq_conj`: **if `W, W'` restrict to the same place of
  the function field `L`, their cuspidal inertia groups in `π₁ᵉᵗ(U)` are conjugate** (Galois
  transitivity, `CurvesJacobian.Cusp.exists_algEquiv_comap_eq`).

So the kernel of filling in the cusps over one place of `L` is topologically normally generated
by a single cuspidal inertia group ([AbsTopI] Definition 4.2 (iii)(c),
`Topics in Absolute Anabelian Geometry I.txt` l.3011–3014).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

namespace GaloisPi1

variable {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω]

/-- Inertia elements are transported by conjugation: if `τ` is an inertia element of `W`, then
`σ τ σ⁻¹` is an inertia element of `σ(W) = W.comap σ⁻¹`. -/
theorem conj_mem_inertia {W : ValuationSubring Ω} {τ : Ω ≃ₐ[P] Ω} (hτ : τ ∈ inertia W)
    (σ : Ω ≃ₐ[P] Ω) : σ * τ * σ⁻¹ ∈ inertia (W.comap (σ.symm : Ω →+* Ω)) := by
  intro a ha
  rw [ValuationSubring.mem_comap] at ha
  rw [CurvesJacobian.Cusp.valuation_comap_lt_one_iff]
  have := hτ _ ha
  convert this using 2
  simp [AlgEquiv.aut_inv, AlgEquiv.mul_apply]

/-- `σ(W)` for a place `W` and `σ`: `W.comap σ⁻¹`; transport back. -/
lemma comap_symm_comap (W : ValuationSubring Ω) (σ : Ω ≃ₐ[P] Ω) :
    (W.comap (σ.symm : Ω →+* Ω)).comap (σ : Ω →+* Ω) = W := by
  ext a
  simp [ValuationSubring.mem_comap]

theorem mem_inertia_comap_iff {W : ValuationSubring Ω} (σ τ : Ω ≃ₐ[P] Ω) :
    τ ∈ inertia (W.comap (σ.symm : Ω →+* Ω)) ↔ σ⁻¹ * τ * σ ∈ inertia W := by
  constructor
  · intro h
    have := conj_mem_inertia h σ⁻¹
    rwa [inv_inv, AlgEquiv.aut_inv, AlgEquiv.symm_symm, comap_symm_comap] at this
  · intro h
    have := conj_mem_inertia h σ
    simpa [mul_assoc] using this

end GaloisPi1

namespace CurvesJacobian.Cusp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [IsIntegral X]
  (eL : X.functionField ≃+* D.L)

/-- `σ ∈ H_L` fixes the function field `L` pointwise. -/
lemma apply_eq_of_mem_HL {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ D.HL) (x : D.L) : σ x = x :=
  (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ hσ

/-- Centredness is invariant under `H_L`. -/
lemma isCentredOn_comap_iff (U : X.Opens) [Nonempty U] {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ D.HL)
    (W : ValuationSubring Ω) :
    IsCentredOn D X eL U (W.comap (σ.symm : Ω →+* Ω)) ↔ IsCentredOn D X eL U W := by
  have hσ' : σ.symm ∈ D.HL := by simpa [AlgEquiv.aut_inv] using D.HL.inv_mem hσ
  have hk : ∀ c : k, σ.symm (algebraMap k Ω c) = algebraMap k Ω c := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (K₀ k t) Ω, AlgEquiv.commutes]
  simp only [IsCentredOn, ValuationSubring.mem_comap, RingHom.coe_coe, hk,
    apply_eq_of_mem_HL D hσ']

variable [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)

/-- **Conjugating a cuspidal inertia group**: for `σ ∈ H`, the cuspidal inertia group of `σ(W)`
is the conjugate of that of `W` by the image of `σ` in `π₁ᵉᵗ(U)`. -/
theorem cuspInertia_comap (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω) (σ : D.H) :
    cuspInertia D X eL hH U (W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω)) =
      (cuspInertia D X eL hH U W).map
        (MulAut.conj (D.chartHom hH (genericL D X eL U) σ)).toMonoidHom := by
  rw [cuspInertia, cuspInertia, MonoidHom.map_closure]
  congr 1
  ext γ
  simp only [Set.mem_image, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨_, ⟨σ⁻¹ * τ * σ, ?_, rfl⟩, ?_⟩
    · rw [GaloisPi1.mem_inertia_comap_iff] at hτ
      simpa using hτ
    · simp [map_mul, mul_assoc]
  · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    refine ⟨σ * τ * σ⁻¹, ?_, by simp [map_mul]⟩
    rw [GaloisPi1.mem_inertia_comap_iff]
    simpa [mul_assoc] using hτ

/-- **Cuspidal inertia groups of places over the same place of `L` are conjugate.** -/
theorem exists_cuspInertia_eq_conj (U : X.Opens) [Nonempty U] (W W' : ValuationSubring Ω)
    (h : W.comap (algebraMap D.L Ω) = W'.comap (algebraMap D.L Ω)) :
    ∃ γ, cuspInertia D X eL hH U W' =
      (cuspInertia D X eL hH U W).map (MulAut.conj γ).toMonoidHom := by
  haveI : IsGalois D.L Ω := IsGalois.tower_top_of_isGalois (K₀ k t) D.L Ω
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comap_eq W W' h
  set σ' : Ω ≃ₐ[K₀ k t] Ω := σ.restrictScalars (K₀ k t)
  have hσL : σ' ∈ D.HL := by
    have hcl : IsClosed (D.HL : Set (Ω ≃ₐ[K₀ k t] Ω)) := D.isClosed_HL
    have h := InfiniteGalois.fixingSubgroup_fixedField (⟨D.HL, hcl⟩ : ClosedSubgroup _)
    change σ' ∈ (⟨D.HL, hcl⟩ : ClosedSubgroup _).toSubgroup
    rw [← h, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  refine ⟨D.chartHom hH (genericL D X eL U) ⟨σ', D.le hσL⟩, ?_⟩
  rw [← cuspInertia_comap, hσ]
  rfl

end CurvesJacobian.Cusp
