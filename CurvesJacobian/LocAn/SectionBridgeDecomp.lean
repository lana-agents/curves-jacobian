/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SectionBridgeThmC

/-!
# Rational points are determined by their decomposition groups ([GalSect] Thm 1.3 (i))

[GalSect] = Mochizuki, *Galois Sections in Absolute Anabelian Geometry*, Theorem 1.3 (i)
(`Galois Sections.txt` l.265–266): "The closed point `x` is completely determined by the
conjugacy class of the closed subgroup `D_x ⊆ Π_{X_K}`". For a rational point `x` of a proper curve
`X` over `k`, the decomposition group is the image `D_x = s_x(G_k)` of the section
`s_x = schSection x : G_k → π₁ᵉᵗ(X, η̄)` (`LocAn/SectionBridge.lean`). This file proves the
statement for rational points of proper curves of genus `≠ 0` over finite extensions of `ℚ_p`
and over number fields, in the stronger form `D_y ⊆ γ D_x γ⁻¹ ⇒ x = y` for an arbitrary
`γ ∈ π₁ᵉᵗ(X)` (the proof of [GalSect]: "follows … formally from [Mzk1], Theorem C", l.280–281).

## Main results

* `CurvesJacobian.LocAn.SectionBridge.exists_conj_of_forall_exists` (group theory): if the image
  of a section `s'` of `p : G → Q` lies in a conjugate `γ · s(Q) · γ⁻¹` of the image of another
  section `s`, then `s' = δ s δ⁻¹` for `δ = γ · s(p γ)⁻¹ ∈ ker p`;
* **`eq_of_schSection_le_conj_padic`**, **`eq_of_schSection_le_conj_numberField`**: rational points
  `x, y` with `s_y(G_k) ⊆ γ s_x(G_k) γ⁻¹` are equal (via [LocAn] Thm C,
  `eq_of_placeOfF_eq` and `placeOfF_eq_of_xSectionGk_conj_{padic,numberField}`).
-/

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi IsLocalRing Pi1.Orbifold
open AlgebraicGeometry.FiniteEtale WeilCurves.FunctionField

noncomputable section

namespace CurvesJacobian.LocAn.SectionBridge

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve CurvesJacobian.Cusp

/-- **Sections with conjugate images are conjugate by a kernel element**: if `s, s'` are sections
of `p : G → Q` and every `s' g` lies in `γ · s(Q) · γ⁻¹`, then `s' = δ · s · δ⁻¹` with
`δ = γ · s(p γ)⁻¹ ∈ ker p`. -/
theorem exists_conj_of_forall_exists {G Q : Type*} [Group G] [Group Q] (p : G →* Q)
    (s s' : Q →* G) (hs : ∀ g, p (s g) = g) (hs' : ∀ g, p (s' g) = g) (γ : G)
    (h : ∀ g, ∃ g', s' g = γ * s g' * γ⁻¹) :
    ∃ δ, p δ = 1 ∧ ∀ g, s' g = δ * s g * δ⁻¹ := by
  refine ⟨γ * (s (p γ))⁻¹, by rw [map_mul, map_inv, hs, mul_inv_cancel], fun g ↦ ?_⟩
  obtain ⟨g', hg'⟩ := h g
  have hp : g = p γ * g' * (p γ)⁻¹ := by
    have := congrArg p hg'
    rwa [hs', map_mul, map_mul, map_inv, hs] at this
  have hg'' : g' = (p γ)⁻¹ * g * p γ := by
    rw [hp]
    group
  rw [hg', hg'', map_mul, map_mul, map_inv]
  group

section Curve

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- `D_y ⊆ γ D_x γ⁻¹` for the scheme-theoretic sections gives `Δ_X`-conjugate Galois-model
sections. -/
theorem exists_xSectionGk_conj_of_le_conj {x y : Spec (.of k) ⟶ X}
    (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (γ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (h : ∀ g, ∃ g', curveSchSection k hτ y hy g = γ * curveSchSection k hτ x hx g' * γ⁻¹) :
    ∃ δ ∈ DeltaX (curveGaloisData k hτ), ∀ g,
      xSectionGk (xh (curveGaloisData k hτ) (curveEquivL k hτ) (curveEquivL_algebraMap k hτ) y
          hy rfl) g =
        δ * xSectionGk (xh (curveGaloisData k hτ) (curveEquivL k hτ)
          (curveEquivL_algebraMap k hτ) x hx rfl) g * δ⁻¹ := by
  set e := etalePi1EquivPiX' (curveGaloisData k hτ) X (curveEquivL k hτ)
    (curveEquivL_algebraMap k hτ) (curveEquivL_τ k hτ) le_rfl
  have hPi : ∀ g, ∃ g',
      xSectionGk (xh (curveGaloisData k hτ) (curveEquivL k hτ) (curveEquivL_algebraMap k hτ) y
          hy rfl) g =
        e γ * xSectionGk (xh (curveGaloisData k hτ) (curveEquivL k hτ)
          (curveEquivL_algebraMap k hτ) x hx rfl) g' * (e γ)⁻¹ := fun g ↦ by
    obtain ⟨g', hg'⟩ := h g
    refine ⟨g', ?_⟩
    rw [← etalePi1EquivPiX'_schSection _ _ _ y hy rfl (curveEquivL_τ k hτ),
      ← etalePi1EquivPiX'_schSection _ _ _ x hx rfl (curveEquivL_τ k hτ)]
    rw [curveSchSection, curveSchSection] at hg'
    rw [hg', map_mul, map_mul, map_inv]
  obtain ⟨δ, hδ, hconj⟩ := exists_conj_of_forall_exists (piXToGk (curveGaloisData k hτ)) _ _
    (piXToGk_xSectionGk _) (piXToGk_xSectionGk _) (e γ) hPi
  exact ⟨δ, hδ, hconj⟩

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[GalSect] Thm 1.3 (i) for rational points, over a finite extension `k` of `ℚ_p`**: rational
points `x, y` of a proper curve `X` of genus `≠ 0` whose decomposition groups satisfy
`s_y(G_k) ⊆ γ s_x(G_k) γ⁻¹` for some `γ ∈ π₁ᵉᵗ(X)` are equal. -/
theorem eq_of_schSection_le_conj_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] (hg : curveGenus k X ≠ 0)
    {x y : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (γ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (h : ∀ g, ∃ g', curveSchSection k hτ y hy g = γ * curveSchSection k hτ x hx g' * γ⁻¹) :
    x = y := by
  obtain ⟨δ, hδ, hconj⟩ := exists_xSectionGk_conj_of_le_conj k hτ hx hy γ h
  exact eq_of_placeOfF_eq _ _ _ hx hy rfl (placeOfF_eq_of_xSectionGk_conj_padic k hτ p x hx
    (Kummer.genus_baseChange_ne_zero_of_curveGenus k hτ hg) hδ hconj)

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[GalSect] Thm 1.3 (i) for rational points, over a number field `k`**: rational points
`x, y` of a proper curve `X` of genus `≠ 0` with `s_y(G_k) ⊆ γ s_x(G_k) γ⁻¹` are equal. -/
theorem eq_of_schSection_le_conj_numberField [NumberField k] (hg : curveGenus k X ≠ 0)
    {x y : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (hy : y ≫ (X ↘ Spec (.of k)) = 𝟙 _)
    (γ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (h : ∀ g, ∃ g', curveSchSection k hτ y hy g = γ * curveSchSection k hτ x hx g' * γ⁻¹) :
    x = y := by
  obtain ⟨δ, hδ, hconj⟩ := exists_xSectionGk_conj_of_le_conj k hτ hx hy γ h
  exact eq_of_placeOfF_eq _ _ _ hx hy rfl (placeOfF_eq_of_xSectionGk_conj_numberField k hτ x hx
    (Kummer.genus_baseChange_ne_zero_of_curveGenus k hτ hg) hδ hconj)

end Curve

end CurvesJacobian.LocAn.SectionBridge
