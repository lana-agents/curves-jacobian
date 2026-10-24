/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThetaPullback
import Pi1.Surface.Cup

/-!
# From (P6) to the transport of Weil forms (the hypothesis `hP6` of MR7's T′)

MR7's `TPrime.tprime_of_star_P6` takes (P6) in the form `e₂(Φ t, Φ s) = e₁(t, s)^m` on `T₁`
(`Φ = α^{ab} ⋊ id`). This file derives that form from the cup-product statement
`JacInput.WeilCupG` for both curves, using Poincaré duality of the surface group (pi1's
`Pi1.SurfaceGroup.eq_of_forall_cupClass_eq`):

* `h2lcToContH2_injective`: pi1's `H2lc` and LCFT's `ContH2` agree (same cocycles and
  coboundaries);
* `cupClass_eq_h2lc`: `JacInput.cupClass` is the image of pi1's `Pi1.Profinite.cupClass`;
* **`weilForm_transport`**: for `α : Π_{X₁} ≃ Π_{X₂}` over `G_k` with
  `α^* res c^{ar}(E₂) = (res c^{ar}(E₁))^λ` on `Δ_X`, `deg E₂` a unit mod `n`, `Δ_{X₁} ≅ Π̂_{g,0}`,
  and the cup-product identities of (P6) for both curves, there is `m : ℕ` with
  `e₂(α δ, α δ') = e₁(δ, δ')^m` for all `δ, δ' ∈ Δ_{X₁}^{ab}`.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField
open CurvesJacobian.Kummer CurvesJacobian.LocAn.SemiAb CurvesJacobian.LocAn.WeilForm
open CurvesJacobian.LocAn.ArithChern CurvesJacobian.LocAn.JacInput

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.WeilCupTransport

universe u

/-! ### `H2lc` and `ContH2` -/

section Compare

variable {A M : Type*} [Group A] [TopologicalSpace A] [CommGroup M] [MulDistribMulAction A M]

/-- **`H2lc → ContH2` is injective** (both are locally constant cocycles modulo coboundaries of
locally constant cochains). -/
theorem h2lcToContH2_injective :
    Function.Injective (ChernClass.h2lcToContH2 : Pi1.Profinite.H2lc A M →* ContH2 A M) := by
  refine (injective_iff_map_eq_one _).2 fun y hy => ?_
  induction y using QuotientGroup.induction_on with
  | H c =>
    rw [ChernClass.h2lcToContH2_mk, ContH2.mk_eq_one_iff] at hy
    obtain ⟨x, hx, hxc⟩ := hy
    exact (QuotientGroup.eq_one_iff c).2 ⟨x, hx, hxc⟩

end Compare

/-! ### The cup product -/

section Cup

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {n : ℕ} [NeZero n]

attribute [local instance 2000] Kummer.group_piX

theorem mu_pow_n (ζ : Mu n Ω) : ζ ^ n = 1 := Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])

/-- `JacInput.cupClass` is pi1's cup product (in `ContH2`). -/
theorem cupClass_eq_h2lc (χ : DeltaX D →* Mu n Ω) (hχ : IsLocallyConstant χ)
    (ψ : DeltaX D →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    cupClass χ hχ ψ hψ = ChernClass.h2lcToContH2
      (Pi1.Profinite.cupClass deltaX_smul_mu mu_pow_n χ hχ ψ hψ) := rfl

/-- Classes in `H²(Δ_X, μ_n)` are killed by `n`. -/
theorem pow_n_eq_one (c : ContH2 (DeltaX D) (Mu n Ω)) : c ^ n = 1 := by
  induction c using ContH2.induction_on with
  | h c =>
    rw [← map_pow]
    exact ThetaClass.mk_eq_one_of_eq_one fun p => by
      change (c : _ → Mu n Ω) p ^ n = 1
      exact mu_pow_n _

theorem zpow_eq_of_modEq (c : ContH2 (DeltaX D) (Mu n Ω)) {a b : ℤ} (h : a ≡ b [ZMOD n]) :
    c ^ a = c ^ b := by
  obtain ⟨q, hq⟩ := (Int.modEq_iff_dvd.1 h)
  have hb : b = a + n * q := by omega
  rw [hb, zpow_add, zpow_mul, zpow_natCast, pow_n_eq_one, one_zpow, mul_one]

theorem cupClass_congr' {χ χ' : DeltaX D →* Mu n Ω} (hχ : IsLocallyConstant χ)
    (hχ' : IsLocallyConstant χ') {ψ ψ' : DeltaX D →* Multiplicative (ZMod n)}
    (hψ : IsLocallyConstant ψ) (hψ' : IsLocallyConstant ψ') (h₁ : χ = χ') (h₂ : ψ = ψ') :
    cupClass χ hχ ψ hψ = cupClass χ' hχ' ψ' hψ' := by
  subst h₁ h₂
  rfl

theorem cupClass_pow (χ : DeltaX D →* Mu n Ω) (hχ : IsLocallyConstant χ)
    (ψ : DeltaX D →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) (m : ℕ) :
    cupClass χ hχ ψ hψ ^ m = cupClass (χ ^ m) (hχ.comp fun x => x ^ m) ψ hψ := by
  rw [cupClass_eq_h2lc, cupClass_eq_h2lc,
    Pi1.Profinite.cupClass_pow_left deltaX_smul_mu mu_pow_n χ hχ m _ ψ hψ, map_pow]

end Cup

/-! ### Transport of the Weil form -/

section Transport

attribute [local instance] isFunctionField_F

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t₁ t₂ : Ω}
  {D₁ : Pi1.Orbifold.GaloisData k t₁} {D₂ : Pi1.Orbifold.GaloisData k t₂} [CharZero k]
  [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω] [IsAlgClosed Ω]
  [Fact (Function.Surjective (piJ1ToGk D₁))] [Fact (Function.Surjective (piJ1ToGk D₂))]
  {n : ℕ} [NeZero n] [Finite (JT D₁ n)] [Finite (JT D₂ n)]
  (hW₁ : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (Kummer.baseChange D₁)) (n := n)))
  (hW₂ : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (Kummer.baseChange D₂)) (n := n)))

attribute [local instance 2000] Kummer.group_piX

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures of the quotients `Π_X` are slow to synthesize
set_option maxHeartbeats 800000 in
-- unifying the two cup products through `H2lc` and the restriction along `α_Δ` is slow
/-- **(P6) ⟹ transport of the Weil forms** (the hypothesis `hP6` of MR7's
`TPrime.tprime_of_star_P6`). Let `α : Π_{X₁} ≃ Π_{X₂}` be an isomorphism over `G_k`
(`α_Δ : Δ_{X₁} ≃ Δ_{X₂}` its restriction) with `α_Δ^* r₂ = r₁^λ`, `r_i = res_{Δ} c^{ar}(E_i)`,
`deg E₂ · u ≡ 1 mod n`, and `Δ_{X₁} ≅ Π̂_{g,0}`. If both curves satisfy the cup-product identity of
(P6) (`WeilCupG`, with signs `s_i`) for `E_i`, then `e₂(α δ, α δ') = e₁(δ, δ')^m` for some `m`. -/
theorem weilForm_transport {g : ℕ} (eΔ : DeltaX D₁ ≃ₜ* Pi1.ProfiniteSurfaceGroup g 0)
    (α : PiX D₁ ≃* PiX D₂) (hαc : Continuous α) (hαc' : Continuous α.symm)
    (hα : ∀ u, piXToGk D₂ (α u) = piXToGk D₁ u)
    {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    {E₁ : Divisor (kbar k Ω) (F (Kummer.baseChange D₁))} {f₁ : Ω} (hf₁ : IsArithRep D₁ n E₁ f₁)
    {E₂ : Divisor (kbar k Ω) (F (Kummer.baseChange D₂))} {f₂ : Ω} (hf₂ : IsArithRep D₂ n E₂ f₂)
    (hP₁ : ∀ (δ : DeltaX D₁) (ψ : DeltaX D₁ →* Multiplicative (ZMod n))
      (hψ : IsLocallyConstant ψ),
      cupClass (chiDelta hW₁ δ) (isLocallyConstant_chiDelta hW₁ δ) ψ hψ ^ E₁.deg =
        JacInput.resDelta (D := D₁) (n := n) hf₁.chern ^
          (s₁ * ((Multiplicative.toAdd (ψ δ)).val : ℤ)))
    (hP₂ : ∀ (δ : DeltaX D₂) (ψ : DeltaX D₂ →* Multiplicative (ZMod n))
      (hψ : IsLocallyConstant ψ),
      cupClass (chiDelta hW₂ δ) (isLocallyConstant_chiDelta hW₂ δ) ψ hψ ^ E₂.deg =
        JacInput.resDelta (D := D₂) (n := n) hf₂.chern ^
          (s₂ * ((Multiplicative.toAdd (ψ δ)).val : ℤ)))
    (lam : ℤ)
    (hlam : ContH2.map (SemiAb.resDelta α.toMonoidHom hα)
        ((hαc.comp continuous_subtype_val).subtype_mk _) (MonoidHom.id _)
        (fun _ _ => (deltaX_smul_mu _ _).trans (deltaX_smul_mu _ _).symm)
        (JacInput.resDelta (D := D₂) (n := n) hf₂.chern) =
          JacInput.resDelta (D := D₁) (n := n) hf₁.chern ^ lam)
    {u : ℤ} (hu : E₂.deg * u ≡ 1 [ZMOD n]) :
    ∃ m : ℕ, ∀ δ δ' : DeltaAb D₁,
      weilForm hW₂ (mapAb α.toMonoidHom hαc hα δ) (mapAb α.toMonoidHom hαc hα δ') =
        weilForm hW₁ δ δ' ^ m := by
  classical
  have hα' : ∀ v, piXToGk D₁ (α.symm v) = piXToGk D₂ v := fun v => by
    rw [← hα, α.apply_symm_apply]
  set αΔ := SemiAb.resDelta α.toMonoidHom hα with hαΔ
  set βΔ := SemiAb.resDelta α.symm.toMonoidHom hα' with hβΔ
  have hαΔc : Continuous αΔ := (hαc.comp continuous_subtype_val).subtype_mk _
  have hβΔc : Continuous βΔ := (hαc'.comp continuous_subtype_val).subtype_mk _
  have hβα : ∀ y, βΔ (αΔ y) = y := fun y => Subtype.ext (α.symm_apply_apply (y : PiX D₁))
  set r₁ := JacInput.resDelta (D := D₁) (n := n) hf₁.chern
  set mz : ℤ := u * E₁.deg * lam * s₁ * s₂
  refine ⟨(mz % n).toNat, fun δ δ' => ?_⟩
  have hm : ((mz % n).toNat : ℤ) ≡ mz [ZMOD n] := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne n))]
    exact Int.mod_modEq _ _
  obtain ⟨x, rfl⟩ := deltaAbMk_surjective D₁ δ
  obtain ⟨x', rfl⟩ := deltaAbMk_surjective D₁ δ'
  set χ₂ := chiDelta hW₂ (αΔ x)
  have hχ₂ := isLocallyConstant_chiDelta hW₂ (αΔ x)
  set χ₁ := chiDelta hW₁ x
  have hχ₁ := isLocallyConstant_chiDelta hW₁ x
  have hχ : IsLocallyConstant (χ₂.comp αΔ) := hχ₂.comp_continuous hαΔc
  have hχ' : IsLocallyConstant (χ₁ ^ (mz % n).toNat) := hχ₁.comp fun z => z ^ (mz % n).toNat
  have key : χ₂.comp αΔ = χ₁ ^ (mz % n).toNat := by
    refine Pi1.SurfaceGroup.eq_of_forall_cupClass_eq eΔ n mu_pow_n deltaX_smul_mu _ _ hχ hχ'
      fun ψ hψ => ?_
    apply h2lcToContH2_injective
    rw [← cupClass_eq_h2lc, ← cupClass_eq_h2lc]
    set ψ₂ := ψ.comp βΔ
    have hψ₂ : IsLocallyConstant ψ₂ := hψ.comp_continuous hβΔc
    have hψψ : ψ₂.comp αΔ = ψ := MonoidHom.ext fun y => by
      change ψ (βΔ (αΔ y)) = ψ y
      rw [hβα]
    set v : ℤ := ((Multiplicative.toAdd (ψ x)).val : ℤ)
    have hv : ((Multiplicative.toAdd (ψ₂ (αΔ x))).val : ℤ) = v := by
      change ((Multiplicative.toAdd (ψ (βΔ (αΔ x)))).val : ℤ) = v
      rw [hβα]
    -- left side
    have hL : cupClass (χ₂.comp αΔ) hχ ψ hψ = r₁ ^ (lam * (s₂ * v) * u) := by
      have hnat : cupClass (χ₂.comp αΔ) hχ ψ hψ =
          ContH2.map αΔ hαΔc (MonoidHom.id _)
            (fun _ _ => (deltaX_smul_mu _ _).trans (deltaX_smul_mu _ _).symm)
            (cupClass χ₂ hχ₂ ψ₂ hψ₂) :=
        cupClass_congr' hχ hχ hψ (hψ₂.comp_continuous hαΔc) rfl hψψ.symm
      have h1 : cupClass (χ₂.comp αΔ) hχ ψ hψ =
          cupClass (χ₂.comp αΔ) hχ ψ hψ ^ (E₂.deg * u) := by
        rw [zpow_eq_of_modEq _ hu, zpow_one]
      rw [h1, zpow_mul, hnat, ← map_zpow, hP₂, hv, map_zpow, hlam, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    -- right side
    have hR : cupClass (χ₁ ^ (mz % n).toNat) hχ' ψ hψ = r₁ ^ (lam * (s₂ * v) * u) := by
      rw [← cupClass_pow χ₁ hχ₁ ψ hψ, ← zpow_natCast, zpow_eq_of_modEq _ hm]
      have hs : s₁ * s₁ = 1 := by rcases hs₁ with h | h <;> subst h <;> norm_num
      have e : mz = E₁.deg * (u * lam * s₁ * s₂) := by simp only [mz]; ring
      rw [e, zpow_mul, hP₁, ← zpow_mul]
      congr 1
      linear_combination (u * lam * s₂ * v) * hs
    rw [hL, hR]
  have h := DFunLike.congr_fun key x'
  exact h

end Transport

end CurvesJacobian.LocAn.WeilCupTransport
