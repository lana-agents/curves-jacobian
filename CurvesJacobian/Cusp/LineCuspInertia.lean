/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Inertia
import CurvesJacobian.Cusp.LineInertiaIso

/-!
# The cusp-compatible `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π̂_{0,3}` for `CurvesJacobian.Cusp.cuspInertia`

`CurvesJacobian.Cusp.exists_continuousMulEquiv_lineInertia` is stated for the Galois action at
the geometric generic point of `Spec k[t, 1/(t(t-1))]`. Here it is transported to the Galois
model of `CurvesJacobian/Cusp/Inertia.lean`: for Galois data `D` with `L = k(t)` (every element
of `Gal(Ω / k(t))` lies in `H`), a curve `X` with `eL : K(X) ≃ L`, and an open `U ⊆ X` with an
isomorphism `e : U ≅ Spec k[t, 1/(t(t-1))]` identifying the geometric generic points (for
`X = ℙ¹`, `U = ℙ¹ ∖ {0, 1, ∞}`), there is `Θ : π₁ᵉᵗ(U) ≃ₜ* Π̂_{0,3}` mapping a conjugate of
`cuspInertia D X eL hH U W` onto `Iⱼ = ⟨cⱼ⟩‾` for every place `W` over the cusp `j`
(`CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia`).

Ingredients: the inertia elements of a place form a closed subgroup
(`GaloisPi1.inertiaSubgroup`; inverses because orbits of automorphisms on algebraic elements
are finite), so `cuspInertia` is the image of a compact subgroup and equals the closed subgroup
`lineInertia` after transport along `e` (naturality of the Galois action,
`fundamentalGroupMap_galoisAction`, `galoisAction_eq_of_apply_eq`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold

noncomputable section

universe u

namespace GaloisPi1

variable {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω] (W : ValuationSubring Ω)

lemma one_mem_inertia : (1 : Ω ≃ₐ[P] Ω) ∈ inertia W := fun a _ ↦ by simp

lemma mem_of_mem_inertia {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) {a : Ω} (ha : a ∈ W) :
    σ a ∈ W := by
  have h := (W.valuation_le_one_iff _).1 (hσ a ha).le
  simpa using W.add_mem _ _ h ha

lemma mul_mem_inertia {σ τ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) (hτ : τ ∈ inertia W) :
    σ * τ ∈ inertia W := by
  intro a ha
  have e : (σ * τ) a - a = (σ (τ a) - τ a) + (τ a - a) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [e]
  exact lt_of_le_of_lt (W.valuation.map_add _ _)
    (max_lt (hσ _ (mem_of_mem_inertia W hτ ha)) (hτ a ha))

lemma pow_mem_inertia {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) (n : ℕ) : σ ^ n ∈ inertia W := by
  induction n with
  | zero => exact one_mem_inertia W
  | succ n ih => rw [pow_succ]; exact mul_mem_inertia W ih hσ

variable [Algebra.IsAlgebraic P Ω]

/-- Every automorphism of an algebraic extension has a finite orbit on each element. -/
lemma exists_pow_apply_eq (σ : Ω ≃ₐ[P] Ω) (a : Ω) : ∃ n : ℕ, 0 < n ∧ (σ ^ n) a = a := by
  let S := (minpoly P a).rootSet Ω
  have hS : S.Finite := (minpoly P a).rootSet_finite Ω
  have hmem : ∀ n : ℕ, (σ ^ n) a ∈ S := fun n ↦ by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral a), ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
  obtain ⟨i, j, hij, h⟩ := hS.exists_lt_map_eq_of_forall_mem hmem
  refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
  have : (σ ^ i) ((σ ^ (j - i)) a) = (σ ^ i) a := by
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le, h]
  exact (σ ^ i).injective this

lemma inv_mem_inertia {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) : σ⁻¹ ∈ inertia W := by
  intro a ha
  obtain ⟨n, hn, h⟩ := exists_pow_apply_eq σ a
  have e : σ⁻¹ a = (σ ^ (n - 1)) a := by
    apply σ.injective
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, ← AlgEquiv.mul_apply,
      ← pow_succ', Nat.sub_add_cancel hn, h]
  rw [e]
  exact pow_mem_inertia W hσ _ a ha

/-- **The inertia group of a place**, as a subgroup. -/
def inertiaSubgroup : Subgroup (Ω ≃ₐ[P] Ω) where
  carrier := inertia W
  one_mem' := one_mem_inertia W
  mul_mem' := mul_mem_inertia W
  inv_mem' := inv_mem_inertia W

end GaloisPi1

namespace CurvesJacobian.Cusp

section Closed

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} [IsGalois (K₀ k t) Ω]

/-- The inertia group of a place is closed in `Gal(Ω / k(t))`. -/
lemma isClosed_inertia (W : ValuationSubring Ω) :
    IsClosed (GaloisPi1.inertia (P := K₀ k t) W) := by
  have hloc : ∀ (a : Ω) (σ₀ : Ω ≃ₐ[K₀ k t] Ω),
      {σ : Ω ≃ₐ[K₀ k t] Ω | σ a = σ₀ a} ∈ 𝓝 σ₀ := by
    intro a σ₀
    have ho := isOpen_setOf_apply_eq (k := k) (t := t) a
    have : {σ : Ω ≃ₐ[K₀ k t] Ω | σ a = σ₀ a} = (σ₀⁻¹ * ·) ⁻¹' {σ | σ a = a} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, AlgEquiv.mul_apply]
      constructor
      · intro h; rw [h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      · intro h
        have := congrArg σ₀ h
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
        exact this
    rw [this]
    exact (ho.preimage (continuous_const_mul _)).mem_nhds (by simp)
  have : GaloisPi1.inertia (P := K₀ k t) W =
      ⋂ a ∈ W, {σ : Ω ≃ₐ[K₀ k t] Ω | W.valuation (σ a - a) < 1} := by
    ext σ; simp [GaloisPi1.inertia]
  rw [this]
  refine isClosed_biInter fun a _ ↦ isClosed_iff_nhds.2 fun σ₀ hσ₀ ↦ ?_
  obtain ⟨σ, hσa, hσ⟩ := hσ₀ _ (hloc a σ₀)
  simp only [Set.mem_setOf_eq] at hσ hσa ⊢
  rwa [← hσa]

end Closed

variable {k Ω : Type} [Field k] [IsAlgClosed k] [CharZero k] [Countable k] [Field Ω]
  [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω]

omit [IsAlgClosed k] [CharZero k] [Countable k] in
/-- The inertia group in `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}, η)` is the image of the inertia subgroup. -/
lemma lineInertia_eq_map (ht : Transcendental k t) (W : ValuationSubring Ω) :
    lineInertia ht W = (GaloisPi1.inertiaSubgroup (P := K₀ k t) W).map (lineGalois ht) := by
  have hcl : Subgroup.closure (lineGalois ht '' GaloisPi1.inertia (P := K₀ k t) W) =
      (GaloisPi1.inertiaSubgroup (P := K₀ k t) W).map (lineGalois ht) := by
    rw [← MonoidHom.map_closure]
    congr 1
    exact Subgroup.closure_eq (GaloisPi1.inertiaSubgroup W)
  rw [lineInertia, hcl]
  refine le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl ?_)
    (Subgroup.le_topologicalClosure _)
  rw [Subgroup.coe_map]
  exact ((isClosed_inertia W).isCompact.image (continuous_galoisAction _ _ _)).isClosed

variable {D : GaloisData k t} {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of k))]
  [IsIntegral X] (eL : X.functionField ≃+* D.L)
  (hH : D.H ≤ D.HL)

omit [IsAlgClosed k] [CharZero k] [Countable k] [X.Over (Spec (CommRingCat.of k))] in
/-- The cuspidal inertia group is the image of the inertia subgroup (in `H`). -/
lemma cuspInertia_eq_map (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω) :
    cuspInertia D X eL hH U W =
      ((GaloisPi1.inertiaSubgroup (P := K₀ k t) W).comap D.H.subtype).map
        (D.chartHom hH (genericL D X eL U)) := by
  have : (Subtype.val ⁻¹' GaloisPi1.inertia W : Set D.H) =
      ((GaloisPi1.inertiaSubgroup (P := K₀ k t) W).comap D.H.subtype : Set D.H) := rfl
  rw [cuspInertia, this, ← MonoidHom.map_closure, Subgroup.closure_eq]

omit [IsAlgClosed k] [CharZero k] [Countable k] [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] in
/-- `chartHom` followed by a morphism to `Spec k[t, 1/(t(t-1))]` compatible with the geometric
points is the Galois action `lineGalois`. -/
lemma fundamentalGroupMap_chartHom_line (ht : Transcendental k t) {Y : Scheme.{0}}
    (j : Spec (.of D.L) ⟶ Y) (φ : Y ⟶ Spec (.of (lineRing k)))
    (h : (specPoint D.L Ω ≫ j) ≫ φ = lineGen ht) (σ : D.H) :
    fundamentalGroupMap φ h (D.chartHom hH j σ) = lineGalois ht σ := by
  rw [GaloisData.chartHom_apply, fundamentalGroupMap_galoisAction D.L j φ rfl h
    (by rw [← Category.assoc]; exact h)]
  exact galoisAction_eq_of_apply_eq D.L _ _ _ _ _ _ fun _ ↦ rfl

omit [X.Over (Spec (CommRingCat.of k))] in
/-- **`π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π̂_{0,3}` with `cuspInertia` at the cusps ↦ conjugates of `Iⱼ`.**
Galois data `D` with `L = k(t)` (every automorphism of `Ω / k(t)` lies in `H`), a curve `X` with
`eL : K(X) ≃ L`, and an open `U ⊆ X` with `e : U ≅ Spec k[t, 1/(t(t-1))]` identifying the
geometric generic points (`X = ℙ¹`, `U = ℙ¹ ∖ {0, 1, ∞}`). For every place `W ⊇ k` of `Ω` over
the cusp `j` (`cuspCoord j t ∈ 𝔪_W`), a conjugate of `cuspInertia D X eL hH U W` is mapped onto
`Iⱼ = ⟨cⱼ⟩‾`, where `c₀, c₁` are loops around `0, 1` (a free basis of `π₁(ℂ ∖ {0, 1})`) and
`c₀ c₁ c₂ = 1`. -/
theorem exists_continuousMulEquiv_cuspInertia (ht : Transcendental k t)
    (hHtop : ∀ σ : Ω ≃ₐ[K₀ k t] Ω, σ ∈ D.H) (U : X.Opens) [Nonempty U]
    (e : (U : Scheme) ≅ Spec (.of (lineRing k)))
    (he : (specPoint D.L Ω ≫ genericL D X eL U) ≫ e.hom = lineGen ht) :
    ∃ Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* Pi1.ProfiniteSurfaceGroup 0 3,
      ∀ (j : Fin 3) (W : ValuationSubring Ω), (∀ c : k, algebraMap k Ω c ∈ W) →
        W.valuation (cuspCoord j t) < 1 →
          ∃ σ, (cuspInertia D X eL hH U W).map
            ((Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Pi1.ProfiniteSurfaceGroup 0 3).comp
              (MulAut.conj σ).toMonoidHom) = Pi1.SurfaceGroup.inertia j := by
  obtain ⟨Θ₀, hΘ₀⟩ := exists_continuousMulEquiv_lineInertia ht
  -- transport along `e`
  let φ := fundamentalGroupMap e.hom he
  let m := MulEquiv.ofBijective φ.toMonoidHom
    (fundamentalGroupMap_bijective_of_isIso e.hom he)
  let hm := Continuous.homeoOfEquivCompactToT2 (f := m.toEquiv) φ.continuous_toFun
  let Φ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ* π₁ᵉᵗ(lineGen ht) :=
    { m with
      continuous_toFun := hm.continuous_toFun
      continuous_invFun := hm.continuous_invFun }
  have hΦ : ∀ σ : D.H, Φ (D.chartHom hH (genericL D X eL U) σ) = lineGalois ht σ := by
    intro σ
    exact fundamentalGroupMap_chartHom_line hH ht _ e.hom he σ
  have hmap : ∀ W : ValuationSubring Ω,
      (cuspInertia D X eL hH U W).map (Φ : _ →* π₁ᵉᵗ(lineGen ht)) = lineInertia ht W := by
    intro W
    rw [cuspInertia_eq_map, lineInertia_eq_map, Subgroup.map_map]
    ext γ
    simp only [Subgroup.mem_map, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, (hΦ σ).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨⟨σ, hHtop σ⟩, hσ, hΦ _⟩
  refine ⟨Φ.trans Θ₀, fun j W hWk hWj ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := hΘ₀ j W hWk hWj
  refine ⟨Φ.symm σ, ?_⟩
  refine Eq.trans ?_ hσ
  rw [← hmap W, Subgroup.map_map]
  congr 1
  ext γ
  simp [MulAut.conj_apply]

end CurvesJacobian.Cusp
