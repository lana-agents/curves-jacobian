/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SectionBridgeDelta
import CurvesJacobian.LocAn.ThmCMLF
import CurvesJacobian.Scheme.CurvePlaces

/-!
# [LocAn] Theorem C for `π₁ᵉᵗ`: rational points with `Δ_X`-conjugate sections are equal

Let `X` be a proper curve over a field `k` of characteristic `0` and `x, y : Spec k ⟶ X`
`k`-rational points. Their scheme-theoretic sections `G_k → π₁ᵉᵗ(X)` (`schSection`, transported
to the geometric generic point `η̄` along the specialisation paths of
`LocAn/SectionBridge.lean`) are compared by conjugation with an element `γ ∈ π₁ᵉᵗ(X, η̄)` of
`Δ_X = ker(π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k))`. Then:

* `CurvesJacobian.LocAn.SectionBridge.eq_of_apply_closedPoint_eq`: two `k`-rational points with
  the same image point are equal;
* `CurvesJacobian.LocAn.SectionBridge.eq_of_placeOfF_eq`: in a Galois model with `H_L = H`,
  rational points with the same place of `F` (`placeOfF (ratPointOf x)`) are equal (the place
  dominates `𝒪_{X,x}`, and `x ↦ 𝒪_{X,x}` is injective on the separated scheme `X`);
* **`eq_of_schSection_conj_padic`**, **`eq_of_schSection_conj_numberField`**: [LocAn] Thm C
  (profinite, proper curves of geometric genus `≠ 0`) in the `π₁ᵉᵗ` form, over finite
  extensions of `ℚ_p` and over number fields, for the curve's own Galois model
  `curveGaloisData` (`H_L = H` holds by `rfl`). Proof: `etalePi1EquivPiX'_schSection` and
  `mem_DeltaX_of_fundamentalGroupMap_eq_one` turn the hypothesis into `Δ_X`-conjugacy of the
  Galois-model sections `xSectionGk`, then `placeOfF_eq_of_xSectionGk_conj_{padic,numberField}`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi IsLocalRing Pi1.Orbifold
open AlgebraicGeometry.FiniteEtale WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian.LocAn.SectionBridge

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve CurvesJacobian.Cusp

/-- **Rational points are determined by their image**: two sections `x, y : Spec k ⟶ X` of
`X ⟶ Spec k` with `x(pt) = y(pt)` are equal. -/
theorem eq_of_apply_closedPoint_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {x y : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _) (h : x (closedPoint k) = y (closedPoint k)) : x = y := by
  have h1 : ∃ φ : X.residueField (x (closedPoint k)) ⟶ .of k,
      Spec.map φ ≫ X.fromSpecResidueField _ = x :=
    ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x⟩
  have h2 : ∃ φ : X.residueField (x (closedPoint k)) ⟶ .of k,
      Spec.map φ ≫ X.fromSpecResidueField _ = y := by
    rw [h]
    exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X y⟩
  generalize x (closedPoint k) = p at h1 h2
  obtain ⟨φ₁, rfl⟩ := h1
  obtain ⟨φ₂, rfl⟩ := h2
  obtain ⟨c, hc⟩ : ∃ c, X.fromSpecResidueField p ≫ (X ↘ Spec (.of k)) = Spec.map c :=
    ⟨Spec.preimage _, (Spec.map_preimage _).symm⟩
  have key : ∀ φ : X.residueField p ⟶ .of k,
      (Spec.map φ ≫ X.fromSpecResidueField p) ≫ (X ↘ Spec (.of k)) = 𝟙 _ → c ≫ φ = 𝟙 _ := by
    intro φ hφ
    apply Spec.map_injective
    rw [Spec.map_comp, ← hc, ← Category.assoc, hφ, Spec.map_id]
  have e₁ := key φ₁ hx
  have e₂ := key φ₂ hy
  suffices hφ : φ₁ = φ₂ by rw [hφ]
  ext z
  have hz : c.hom (φ₁.hom z) = z := φ₁.hom.injective (congrArg (fun f ↦ f.hom (φ₁.hom z)) e₁)
  calc φ₁.hom z = φ₂.hom (c.hom (φ₁.hom z)) := (congrArg (fun f ↦ f.hom (φ₁.hom z)) e₂).symm
    _ = φ₂.hom z := by rw [hz]

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  [CharZero k] [IsCurveOver k X] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- **A rational point is determined by its place**: in a Galois model with `H_L = H`, rational
points `x, y` of the proper curve `X` with `placeOfF (ratPointOf x) = placeOfF (ratPointOf y)`
are equal. -/
theorem eq_of_placeOfF_eq {x y : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _) (hHL : D.HL = D.H)
    (h : placeOfF (xh D eL hk x hx hHL) = placeOfF (xh D eL hk y hy hHL)) : x = y := by
  haveI := isSeparated_of_over k X
  have hs : stalkVS k (ratPt x) = stalkVS k (ratPt y) := by
    refine (comapK_ratPlace D eL hk (ratPt x)).symm.trans (Eq.trans ?_
      (comapK_ratPlace D eL hk (ratPt y)))
    ext z
    have hLF : ∀ w : Ω, w ∈ D.L → w ∈ F D := fun w hw ↦ by
      unfold GaloisData.L at hw
      rwa [hHL] at hw
    have hz : ((eL z : D.L) : Ω) ∈ F D := hLF _ (eL z).2
    exact Iff.of_eq (congrArg (fun P : Place k (F D) ↦ (⟨_, hz⟩ : F D) ∈ P.1) h)
  exact eq_of_apply_closedPoint_eq hx hy
    (stalkValuationSubring_injective (valuationRing_stalk_of_isCurveOver k X) hs)

end Galois

section Curve

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- The scheme-theoretic section of a rational point `x` of `X`, in the curve's Galois model. -/
abbrev curveSchSection (x : Spec (.of k) ⟶ X) (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) :
    Gk k (FFClosure X) →* π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)) :=
  schSection (curveGaloisData k hτ) (curveEquivL k hτ) (curveEquivL_algebraMap k hτ) x hx rfl

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- `Δ_X`-conjugate scheme-theoretic sections become `Δ_X`-conjugate Galois-model sections. -/
theorem xSectionGk_conj_of_schSection_conj {x y : Spec (.of k) ⟶ X}
    (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (γ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (h : ∀ g, curveSchSection k hτ y hy g = γ * curveSchSection k hτ x hx g * γ⁻¹) (g) :
    xSectionGk (xh (curveGaloisData k hτ) (curveEquivL k hτ) (curveEquivL_algebraMap k hτ) y hy rfl)
        g =
      etalePi1EquivPiX' (curveGaloisData k hτ) X (curveEquivL k hτ) (curveEquivL_algebraMap k hτ)
          (curveEquivL_τ k hτ) le_rfl γ *
        xSectionGk (xh (curveGaloisData k hτ) (curveEquivL k hτ) (curveEquivL_algebraMap k hτ) x
          hx rfl) g *
        (etalePi1EquivPiX' (curveGaloisData k hτ) X (curveEquivL k hτ)
          (curveEquivL_algebraMap k hτ) (curveEquivL_τ k hτ) le_rfl γ)⁻¹ := by
  rw [← etalePi1EquivPiX'_schSection _ _ _ y hy rfl (curveEquivL_τ k hτ),
    ← etalePi1EquivPiX'_schSection _ _ _ x hx rfl (curveEquivL_τ k hτ)]
  have := h g
  rw [curveSchSection, curveSchSection] at this
  rw [this, map_mul, map_mul, map_inv]

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for `π₁ᵉᵗ`, over a finite extension `k` of `ℚ_p`**: rational
points `x, y` of a proper curve `X` of geometric genus `≠ 0` whose sections `G_k → π₁ᵉᵗ(X)` are
conjugate by an element of `Δ_X = ker(π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k))` are equal. -/
theorem eq_of_schSection_conj_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k]
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {x y : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (γ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (hγ : fundamentalGroupMap (X ↘ Spec (.of k)) rfl γ = 1)
    (h : ∀ g, curveSchSection k hτ y hy g = γ * curveSchSection k hτ x hx g * γ⁻¹) : x = y :=
  eq_of_placeOfF_eq _ _ _ hx hy rfl (placeOfF_eq_of_xSectionGk_conj_padic k hτ p x hx hg
    (mem_DeltaX_of_fundamentalGroupMap_eq_one _ _ (curveEquivL_algebraMap k hτ) rfl
      (curveEquivL_τ k hτ) γ hγ)
    (xSectionGk_conj_of_schSection_conj k hτ hx hy γ h))

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for `π₁ᵉᵗ`, over a number field `k`**: rational points `x, y` of
a proper curve `X` of geometric genus `≠ 0` whose sections `G_k → π₁ᵉᵗ(X)` are conjugate by an
element of `Δ_X = ker(π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k))` are equal. -/
theorem eq_of_schSection_conj_numberField [NumberField k]
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {x y : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (γ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (hγ : fundamentalGroupMap (X ↘ Spec (.of k)) rfl γ = 1)
    (h : ∀ g, curveSchSection k hτ y hy g = γ * curveSchSection k hτ x hx g * γ⁻¹) : x = y :=
  eq_of_placeOfF_eq _ _ _ hx hy rfl (placeOfF_eq_of_xSectionGk_conj_numberField k hτ x hx hg
    (mem_DeltaX_of_fundamentalGroupMap_eq_one _ _ (curveEquivL_algebraMap k hτ) rfl
      (curveEquivL_τ k hτ) γ hγ)
    (xSectionGk_conj_of_schSection_conj k hτ hx hy γ h))

end Curve

end CurvesJacobian.LocAn.SectionBridge
