/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.ExteriorLoops

/-!
# Big circles of different radii are conjugate

In `ℂ ∖ {0, 1}`, the counterclockwise circles of radii `R₁, R₂ > 1/2` around `1/2`
(`Complex.PuncturedPlane.ZeroOne.bigArrow`, loops around `∞`) are conjugate along a path
(`Complex.PuncturedPlane.ZeroOne.bigArrow_eq_conj`), with exponent `1`.

Proof: under `z ↦ (z - 1/2)⁻¹` the exterior of a disc of radius `R < R₁, R₂` is the punctured
disc `B(0, R⁻¹) ∖ {0}`, and the big circles become reversed circles around `0`; each of these is a
loop around `0` (it has a lift of winding one along `exp`,
`Complex.PuncturedPlane.isLoopAround_of_lift`), and all loops around the puncture of a convex
region agree (`Complex.PuncturedPlane.conj_circle_eq`).
-/

open Set Topology Metric CategoryTheory

namespace Complex.PuncturedPlane.ZeroOne

variable {R R' : ℝ}

/-- **The reversed small circle is a loop around `0`** in `B(0, R⁻¹) ∖ {0}`. -/
theorem isLoopAround_smallLoop_symm (hR : 1 / 2 < R) (hR' : 1 / 2 < R') (hRR' : R < R') :
    IsLoopAround (FundamentalGroup.fromPath
      (.mk (smallLoop (pos_of_half_lt hR) hR' hRR').symm)) 0 := by
  have hR0 : 0 < R := pos_of_half_lt hR
  set s := smallLoop (pos_of_half_lt hR) hR' hRR'
  set L : ℂ := Complex.log ((-(R' : ℂ) * Complex.I)⁻¹)
  let Γ : Path L (L + 2 * Real.pi * Complex.I) :=
    { toFun := fun t ↦ L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp only [Set.Icc.coe_one, mul_one]; push_cast; ring }
  have hne : (-(R' : ℂ) * Complex.I)⁻¹ ≠ 0 := by
    have : (R' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pos_of_half_lt hR').ne'
    simp [this]
  have hΓ : ∀ t, Complex.exp (Γ t) = (s.symm t : ℂ) - 0 := by
    intro t
    change Complex.exp (L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) =
      (((bigPath R' (unitInterval.symm t) : ℂ) - 1 / 2))⁻¹ - 0
    rw [Complex.exp_add, Complex.exp_log hne, bigPath_apply, sub_sub_cancel_left, sub_zero,
      unitInterval.coe_symm_eq, exp_two_pi_sub]
    have hE := Complex.exp_ne_zero (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
    field_simp
  exact (isLoopAround_of_lift isOpen_ball (convex_ball (0 : ℂ) R⁻¹)
    (mem_ball_self (inv_pos.2 hR0)) s.symm Γ hΓ).1

/-- Two loops around the puncture of a convex region, at the same base point, are equal. -/
theorem IsLoopAround.eq_of_convex {C : Set ℂ} {a : ℂ} (hCc : Convex ℝ C) {x : Region C {a}}
    {γ₁ γ₂ : FundamentalGroup (Region C {a}) x} (h₁ : IsLoopAround γ₁ a)
    (h₂ : IsLoopAround γ₂ a) : γ₁ = γ₂ := by
  obtain ⟨r₁, h₁, δ₁, rfl⟩ := h₁
  obtain ⟨r₂, h₂, δ₂, rfl⟩ := h₂
  exact conj_circle_eq hCc h₁ h₂ δ₁ δ₂

lemma groupoid_conj_solve {C : Type*} [Groupoid C] {a a' b b' : C} (e₁ : a = a') (e₂ : b = b')
    (F : a ⟶ b) (B₁ : a' ⟶ a') (B₂ : b' ⟶ b')
    (h : eqToHom e₁ ≫ B₁ ≫ eqToHom e₁.symm = F ≫ (eqToHom e₂ ≫ B₂ ≫ eqToHom e₂.symm) ≫ inv F) :
    B₁ = (eqToHom e₁.symm ≫ F ≫ eqToHom e₂) ≫ B₂ ≫
      Groupoid.inv (eqToHom e₁.symm ≫ F ≫ eqToHom e₂) := by
  subst e₁ e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  rw [Groupoid.inv_eq_inv]
  exact h

/-- **Big circles of different radii around `1/2` are conjugate** in `ℂ ∖ {0, 1}`. -/
theorem bigArrow_eq_conj {R₁ R₂ : ℝ} (hR₁ : 1 / 2 < R₁) (hR₂ : 1 / 2 < R₂) :
    ∃ β : FundamentalGroupoid.mk (bigBase hR₁) ⟶ FundamentalGroupoid.mk (bigBase hR₂),
      bigArrow hR₁ = β ≫ bigArrow hR₂ ≫ Groupoid.inv β := by
  set R := (1 / 2 + min R₁ R₂) / 2 with hRdef
  have hR : 1 / 2 < R := by
    have := lt_min hR₁ hR₂
    rw [hRdef]; linarith
  have hRR₁ : R < R₁ := by
    have := min_le_left R₁ R₂; have := lt_min hR₁ hR₂; rw [hRdef]; linarith
  have hRR₂ : R < R₂ := by
    have := min_le_right R₁ R₂; have := lt_min hR₁ hR₂; rw [hRdef]; linarith
  have hR0 : 0 < R := pos_of_half_lt hR
  haveI : PathConnectedSpace (Disc R) := (pathConnectedSpace_disc_and_bijective hR hR₁ hRR₁).1
  set s₁ := smallLoop hR0 hR₁ hRR₁
  set s₂ := smallLoop hR0 hR₂ hRR₂
  -- the two reversed small circles, moved to a common base point, agree
  let b₁ := discPt hR0 (bigBase hR₁) (src_lt (bigLoop hR₁) (lt_norm_bigLoop_sub hR₁ hRR₁))
  let b₂ := discPt hR0 (bigBase hR₂) (src_lt (bigLoop hR₂) (lt_norm_bigLoop_sub hR₂ hRR₂))
  let β' : FundamentalGroupoid.mk b₁ ⟶ FundamentalGroupoid.mk b₂ :=
    ⟦PathConnectedSpace.somePath b₁ b₂⟧
  have h₁ := isLoopAround_smallLoop_symm hR hR₁ hRR₁
  have h₂ := (isLoopAround_smallLoop_symm hR hR₂ hRR₂).conj
    ((Groupoid.isoEquivHom _ _).symm β').symm
  have heq := IsLoopAround.eq_of_convex (convex_ball (0 : ℂ) R⁻¹) h₁ h₂
  rw [Iso.conj_apply] at heq
  -- map to `ℂ ∖ {0, 1}`
  let F := FundamentalGroupoid.map (invIncl hR)
  have hm₁ := map_toDisc hR (bigLoop hR₁) (lt_norm_bigLoop_sub hR₁ hRR₁)
  have hm₂ := map_toDisc hR (bigLoop hR₂) (lt_norm_bigLoop_sub hR₂ hRR₂)
  have e₁ : (FundamentalGroup.fromPath (.mk s₁.symm) : FundamentalGroupoid.mk b₁ ⟶ _) =
      Groupoid.inv (⟦s₁⟧ : FundamentalGroupoid.mk b₁ ⟶ FundamentalGroupoid.mk b₁) := rfl
  have e₂ : (FundamentalGroup.fromPath (.mk s₂.symm) : FundamentalGroupoid.mk b₂ ⟶ _) =
      Groupoid.inv (⟦s₂⟧ : FundamentalGroupoid.mk b₂ ⟶ FundamentalGroupoid.mk b₂) := rfl
  rw [e₁, e₂] at heq
  change Groupoid.inv ⟦s₁⟧ = β' ≫ Groupoid.inv ⟦s₂⟧ ≫ Groupoid.inv β' at heq
  have heq' : (⟦s₁⟧ : FundamentalGroupoid.mk b₁ ⟶ FundamentalGroupoid.mk b₁) =
      β' ≫ ⟦s₂⟧ ≫ inv β' := by
    have := congrArg Groupoid.inv heq
    simp only [Groupoid.inv_eq_inv, IsIso.inv_comp, IsIso.inv_inv, Category.assoc] at this
    exact this
  have key := congrArg F.map heq'
  rw [Functor.map_comp, Functor.map_comp, Functor.map_inv] at key
  change F.map ⟦s₁⟧ = _ at hm₁
  change F.map ⟦s₂⟧ = _ at hm₂
  have key' := hm₁.symm.trans (key.trans
    (congrArg (fun g ↦ F.map β' ≫ g ≫ inv (F.map β')) hm₂))
  exact ⟨_, groupoid_conj_solve _ _ _ _ _ key'⟩

end Complex.PuncturedPlane.ZeroOne
