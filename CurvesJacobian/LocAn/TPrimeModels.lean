/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.TPrimeCurve
import CurvesJacobian.LocAn.WeilCupProof

/-!
# Claim T′ for two curves with (P6) discharged

`CurvesJacobian.LocAn.TPrimeCurve.tprime_curve_of_models`: `tprime_curve_of_model` with both
(P6) inputs `WeilCupG D_i n hW_i` discharged by JAC's `JacInput.weilCupG_of_model`, from scheme
models `X̄_i` of the base changes `baseChange D_i` over `k̄`. The remaining Jacobian-side input
of T′ is (★) (`JacInput.ThetaPullbackG`, in the form of the equations `hc₁`, `hc₂`); the
compatibility `hσα` and the exponent hypothesis `hlam` are the S5 side.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField
open CurvesJacobian.Kummer CurvesJacobian.LocAn.SemiAb CurvesJacobian.LocAn.WeilForm
open CurvesJacobian.LocAn.ArithChern CurvesJacobian.LocAn.JacInput
open CurvesJacobian.LocAn.WeilCupTransport
open scoped Belyi

set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace CurvesJacobian.LocAn.TPrimeCurve

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
-- elaborating the two theta classes and the transport of the Weil forms is slow
/-- **Claim T′ for two curves, (P6) and `Δ_{X₁} ≅ Π̂_{g,0}` discharged**: as
`tprime_curve_of_model`, with `WeilCupG D_i n hW_i` from scheme models `X̄_i` of `baseChange D_i`
over `k̄` (`JacInput.weilCupG_of_model`). -/
theorem tprime_curve_of_models {X₁ X₂ : AlgebraicGeometry.Scheme.{u}}
    [X₁.Over (AlgebraicGeometry.Spec (.of (kbar k Ω)))]
    [Belyi.IsCurveOver (kbar k Ω) X₁] [AlgebraicGeometry.IsIntegral X₁]
    [Nonempty (⊤ : X₁.Opens)]
    [X₂.Over (AlgebraicGeometry.Spec (.of (kbar k Ω)))]
    [Belyi.IsCurveOver (kbar k Ω) X₂] [AlgebraicGeometry.IsIntegral X₂]
    [Nonempty (⊤ : X₂.Opens)]
    {eL₁ : X₁.functionField ≃+* (Kummer.baseChange D₁).L}
    (hH₁ : (Kummer.baseChange D₁).H ≤ (Kummer.baseChange D₁).HL)
    (hk₁ : ∀ c : kbar k Ω, ((eL₁ (algebraMap (kbar k Ω) X₁.functionField c) :
      (Kummer.baseChange D₁).L) : Ω) = algebraMap (kbar k Ω) Ω c)
    {τ₁ : X₁.functionField} (hτ₁ : ((eL₁ τ₁ : (Kummer.baseChange D₁).L) : Ω) = t₁)
    {eL₂ : X₂.functionField ≃+* (Kummer.baseChange D₂).L}
    (hH₂ : (Kummer.baseChange D₂).H ≤ (Kummer.baseChange D₂).HL)
    (hk₂ : ∀ c : kbar k Ω, ((eL₂ (algebraMap (kbar k Ω) X₂.functionField c) :
      (Kummer.baseChange D₂).L) : Ω) = algebraMap (kbar k Ω) Ω c)
    {τ₂ : X₂.functionField} (hτ₂ : ((eL₂ τ₂ : (Kummer.baseChange D₂).L) : Ω) = t₂)
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
      c₁ ^ m :=
  tprime_curve_of_model hW₁ hW₂ hH₁ hk₁ hτ₁ (weilCupG_of_model hH₁ hk₁ hτ₁ hW₁)
    (weilCupG_of_model hH₂ hk₂ hτ₂ hW₂) hg₁ hg₂ α hαc hαc' hα σ₁ σ₂ hσα hf₁ hE₁ hf₂ hE₂ lam
    hlam hu hr₁ hc₁ hc₂

end CurvesJacobian.LocAn.TPrimeCurve
