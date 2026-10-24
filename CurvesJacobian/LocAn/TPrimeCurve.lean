/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.TPrimeAssembly
import CurvesJacobian.LocAn.WeilCupTransport

/-!
# Route T′ at the level of curves (MR7 stage S4)

The group-level assembly `TPrime.map_pullback_thetaClass` (`LocAn/TPrimeAssembly.lean`) applied
to two Galois models `D₁, D₂` of curves inside one algebraically closed field `Ω` (so that `G_k`
and `μ_n(Ω)` are shared):

* `E_i = Δ_{X_i}^{ab} ⋊ G_k` (`SemiAb.EAb`), `p_i = π_{σ_i} = piSigma σ_i : Π_{X_i} → E_i`;
* `α : Π_{X₁} ≃ Π_{X₂}` over `G_k`, `Φ = α^{ab} ⋊ id = mapE α`; the compatibility
  `Φ ∘ π_{σ₁} = π_{σ₂} ∘ α` holds when `α ∘ σ̃₁ = σ̃₂ ∘ α` (`SemiAb.map_piSigma`);
* (★) for both curves: `c_i = π_{σ_i}^* θ_{e_i^{r_i}}` (`WeilForm.thetaE`, `r_i = ±1`), the
  conclusion of `JacInput.ThetaPullbackG` for `P_{σ_i}`;
* (P6) for both curves (`JacInput.WeilCupG`, for divisors `E_i` with `α_Δ^* res c^{ar}(E₂) =
  (res c^{ar}(E₁))^λ` and `deg E₂` a unit mod `n`) together with `Δ_{X₁} ≅ Π̂_{g,0}`, which give the
  transport of the Weil forms `e₂(α δ, α δ') = e₁(δ, δ')^{m₀}`
  (`WeilCupTransport.weilForm_transport`, JAC).

**Claim T′** ([TopSurr] Thm 4.12 proof, step "α preserves the Chern class of an ample bundle up
to a scalar"; R-D3 in `MR7-plan.md`): `α^* c₂ = c₁^m` in `H²(Π_{X₁}, μ_n)` for some `m : ℕ`.

The inputs (★) (as the equations `hc₁`, `hc₂`), (P6) (`hP₁`, `hP₂`) and `Δ_{X₁} ≅ Π̂_{g,0}` (`eΔ`)
are explicit arguments: they are the JAC track's statements `ThetaPullbackG`, `WeilCupG` and the
surface-group presentation, recorded as debts in `MR7-plan.md`. The perfectness `hW_i` and
`[Finite (JT D_i n)]` are hypotheses on a general Galois model (discharged for curve models by
`weilDual_bijective_baseChange`).

## Main results

* `CurvesJacobian.LocAn.TPrimeCurve.zpow_eq_of_modEq_mu`: `ζ^a = ζ^b` in `μ_n` if `a ≡ b mod n`;
* **`CurvesJacobian.LocAn.TPrimeCurve.tprime_curve`**: Claim T′ for two curves;
  `tprime_curve_of_weilCupG`: the same with (P6) as `JacInput.WeilCupG` for both models.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField
open CurvesJacobian.Kummer CurvesJacobian.LocAn.SemiAb CurvesJacobian.LocAn.WeilForm
open CurvesJacobian.LocAn.ArithChern CurvesJacobian.LocAn.JacInput
open CurvesJacobian.LocAn.WeilCupTransport

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.TPrimeCurve

universe u

attribute [local instance] isFunctionField_F

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t₁ t₂ : Ω}
  {D₁ : Pi1.Orbifold.GaloisData k t₁} {D₂ : Pi1.Orbifold.GaloisData k t₂} [CharZero k]
  [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω] [IsAlgClosed Ω]
  [Fact (Function.Surjective (piJ1ToGk D₁))] [Fact (Function.Surjective (piJ1ToGk D₂))]
  {n : ℕ} [NeZero n] [Finite (JT D₁ n)] [Finite (JT D₂ n)]
  (hW₁ : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (Kummer.baseChange D₁)) (n := n)))
  (hW₂ : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (Kummer.baseChange D₂)) (n := n)))

attribute [local instance 2000] Kummer.group_piX

omit [CharZero k] [Finite (JT D₁ n)] [Finite (JT D₂ n)] in
/-- In `μ_n(Ω)`, `ζ^a = ζ^b` whenever `a ≡ b mod n`. -/
theorem zpow_eq_of_modEq_mu (ζ : Mu n Ω) {a b : ℤ} (h : a ≡ b [ZMOD n]) : ζ ^ a = ζ ^ b := by
  rw [zpow_eq_zpow_iff_modEq]
  exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one (mu_pow_n ζ))) h

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures of the quotients `Π_X` are slow to synthesize
set_option maxHeartbeats 800000 in
-- elaborating the two theta classes and the transport of the Weil forms is slow
/-- **Claim T′ for two curves** (MR7 S4, Route T′; [TopSurr] Thm 4.12, step T′): let
`α : Π_{X₁} ≃ Π_{X₂}` be an isomorphism over `G_k` of the arithmetic fundamental groups of two
curves with Galois models in a common `Ω`, compatible with lifts `σ̃₁, σ̃₂` (`hσα`). Assume
(★) for both curves (`hc_i : c_i = π_{σ_i}^* θ_{e_i^{r_i}}`), (P6) for both curves for divisors
`E_i` (`hP_i`), `α_Δ^* res c^{ar}(E₂) = (res c^{ar}(E₁))^λ`, `deg E₂` a unit mod `n`, and
`Δ_{X₁} ≅ Π̂_{g,0}`. Then `α^* c₂ = c₁^m` in `H²(Π_{X₁}, μ_n)` for some `m : ℕ`. -/
theorem tprime_curve {g : ℕ} (eΔ : DeltaX D₁ ≃ₜ* Pi1.ProfiniteSurfaceGroup g 0)
    (α : PiX D₁ ≃* PiX D₂) (hαc : Continuous α) (hαc' : Continuous α.symm)
    (hα : ∀ u, piXToGk D₂ (α u) = piXToGk D₁ u)
    (σ₁ : OverGk D₁) (σ₂ : OverGk D₂) (hσα : ∀ u, α (σ₁.toHom u) = σ₂.toHom (α u))
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
    {u : ℤ} (hu : E₂.deg * u ≡ 1 [ZMOD n])
    {r₁ r₂ : ℤ} (hr₁ : r₁ = 1 ∨ r₁ = -1)
    {c₁ : ContH2 (PiX D₁) (Mu n Ω)} {c₂ : ContH2 (PiX D₂) (Mu n Ω)}
    (hc₁ : c₁ = ContH2.map (piSigma σ₁) (continuous_piSigma _) (MonoidHom.id _)
      (fun _ _ => rfl) (thetaE hW₁ r₁))
    (hc₂ : c₂ = ContH2.map (piSigma σ₂) (continuous_piSigma _) (MonoidHom.id _)
      (fun _ _ => rfl) (thetaE hW₂ r₂)) :
    ∃ m : ℕ, ContH2.map α.toMonoidHom hαc (MonoidHom.id _)
        (fun v x => by rw [piX_smul_mu, piX_smul_mu, MulEquiv.coe_toMonoidHom, hα]; rfl) c₂ =
      c₁ ^ m := by
  obtain ⟨m₀, hm₀⟩ := weilForm_transport hW₁ hW₂ eΔ α hαc hαc' hα hs₁ hf₁ hf₂ hP₁ hP₂ lam hlam hu
  set mz : ℤ := (m₀ : ℤ) * r₂ * r₁
  have hm : ((mz % n).toNat : ℤ) ≡ mz [ZMOD n] := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne n))]
    exact Int.mod_modEq _ _
  have hr : r₁ * r₁ = 1 := by rcases hr₁ with h | h <;> subst h <;> norm_num
  refine ⟨(mz % n).toNat, ?_⟩
  have hb : ∀ a b : EAb D₁, piE D₁ a = 1 → piE D₁ b = 1 →
      bE hW₂ r₂ (mapE α.toMonoidHom hαc hα a) (mapE α.toMonoidHom hαc hα b) =
        bE hW₁ r₁ a b ^ (mz % n).toNat := by
    intro a b _ _
    change weilForm hW₂ (mapAb α.toMonoidHom hαc hα a.left) (mapAb α.toMonoidHom hαc hα b.left) ^
        r₂ = (weilForm hW₁ a.left b.left ^ r₁) ^ (mz % n).toNat
    rw [hm₀, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      zpow_eq_of_modEq_mu _ (hm.mul_left r₁)]
    congr 1
    simp only [mz]
    linear_combination -(m₀ : ℤ) * r₂ * hr
  have key := TPrime.map_pullback_thetaClass (continuous_piE _) (continuous_epsE _) (piE_epsE _)
    (piE_comm _) (continuous_piE _) (continuous_epsE _) (piE_epsE _) (piE_comm _)
    (continuous_piSigma σ₁) (fun _ _ => rfl) (continuous_piSigma σ₂) (fun _ _ => rfl)
    (α := α.toMonoidHom) hαc
    (fun v x => by rw [piX_smul_mu, piX_smul_mu, MulEquiv.coe_toMonoidHom, hα])
    (continuous_mapE α.toMonoidHom hαc hα) (fun _ => rfl) (mapE_epsE α.toMonoidHom hαc hα)
    (fun _ _ => rfl)
    (fun v => (map_piSigma σ₁ σ₂ α.toMonoidHom hαc hα hσα v).symm)
    (isBilin_bE hW₁ r₁) (isEquivar_bE hW₁ r₁) (isLocallyConstant_bE hW₁ r₁)
    (isBilin_bE hW₂ r₂) (isEquivar_bE hW₂ r₂) (isLocallyConstant_bE hW₂ r₂) _ hb
  rw [hc₁, hc₂]
  exact key

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures of the quotients `Π_X` are slow to synthesize
set_option maxHeartbeats 800000 in
-- elaborating the two theta classes and the transport of the Weil forms is slow
/-- **Claim T′ for two curves, from the JAC statements**: as `tprime_curve`, with (P6) taken as
`JacInput.WeilCupG` for both Galois models (genus `≥ 1`, `G_k`-invariant divisors `E_i`). -/
theorem tprime_curve_of_weilCupG {g : ℕ} (eΔ : DeltaX D₁ ≃ₜ* Pi1.ProfiniteSurfaceGroup g 0)
    (hWC₁ : WeilCupG D₁ n hW₁) (hWC₂ : WeilCupG D₂ n hW₂)
    (hg₁ : 1 ≤ genus (kbar k Ω) (F (Kummer.baseChange D₁)))
    (hg₂ : 1 ≤ genus (kbar k Ω) (F (Kummer.baseChange D₂)))
    (α : PiX D₁ ≃* PiX D₂) (hαc : Continuous α) (hαc' : Continuous α.symm)
    (hα : ∀ u, piXToGk D₂ (α u) = piXToGk D₁ u)
    (σ₁ : OverGk D₁) (σ₂ : OverGk D₂) (hσα : ∀ u, α (σ₁.toHom u) = σ₂.toHom (α u))
    {E₁ : Divisor (kbar k Ω) (F (Kummer.baseChange D₁))} {f₁ : Ω} (hf₁ : IsArithRep D₁ n E₁ f₁)
    (hE₁ : ∀ h : D₁.H, divMap (autF _ h) E₁ = E₁)
    {E₂ : Divisor (kbar k Ω) (F (Kummer.baseChange D₂))} {f₂ : Ω} (hf₂ : IsArithRep D₂ n E₂ f₂)
    (hE₂ : ∀ h : D₂.H, divMap (autF _ h) E₂ = E₂)
    (lam : ℤ)
    (hlam : ContH2.map (SemiAb.resDelta α.toMonoidHom hα)
        ((hαc.comp continuous_subtype_val).subtype_mk _) (MonoidHom.id _)
        (fun _ _ => (deltaX_smul_mu _ _).trans (deltaX_smul_mu _ _).symm)
        (JacInput.resDelta (D := D₂) (n := n) hf₂.chern) =
          JacInput.resDelta (D := D₁) (n := n) hf₁.chern ^ lam)
    {u : ℤ} (hu : E₂.deg * u ≡ 1 [ZMOD n])
    {r₁ r₂ : ℤ} (hr₁ : r₁ = 1 ∨ r₁ = -1)
    {c₁ : ContH2 (PiX D₁) (Mu n Ω)} {c₂ : ContH2 (PiX D₂) (Mu n Ω)}
    (hc₁ : c₁ = ContH2.map (piSigma σ₁) (continuous_piSigma _) (MonoidHom.id _)
      (fun _ _ => rfl) (thetaE hW₁ r₁))
    (hc₂ : c₂ = ContH2.map (piSigma σ₂) (continuous_piSigma _) (MonoidHom.id _)
      (fun _ _ => rfl) (thetaE hW₂ r₂)) :
    ∃ m : ℕ, ContH2.map α.toMonoidHom hαc (MonoidHom.id _)
        (fun v x => by rw [piX_smul_mu, piX_smul_mu, MulEquiv.coe_toMonoidHom, hα]; rfl) c₂ =
      c₁ ^ m := by
  obtain ⟨s₁, hs₁, hP₁⟩ := hWC₁ hg₁
  obtain ⟨s₂, -, hP₂⟩ := hWC₂ hg₂
  exact tprime_curve hW₁ hW₂ eΔ α hαc hαc' hα σ₁ σ₂ hσα hs₁ hf₁ hf₂ (hP₁ E₁ f₁ hf₁ hE₁)
    (hP₂ E₂ f₂ hf₂ hE₂) lam hlam hu hr₁ hc₁ hc₂

end CurvesJacobian.LocAn.TPrimeCurve
