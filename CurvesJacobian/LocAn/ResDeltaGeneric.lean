/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.DeltaXEquiv

/-!
# `res_{Δ_X} c^{ar}(E)` generates `H²(Δ_X, μ_n)` for any Galois model (JAC, generic `hgen`)

The curve-level results of `LocAn/ArithChernCurve.lean` and `LocAn/DeltaXEquiv.lean`
(`isFix_rhoPi_iff`, `map_iotaBar_chern`, `mapEquiv_resDelta`, `resDelta_generates`) for an
arbitrary Galois model `D : GaloisData k t` (`char k = 0`, `Ω` algebraically closed) whose base
change `baseChange D` is modelled by a curve `X` over `k̄` (`eL`, `hH`, `hk`, `hτ` as in
`nonempty_deltaX_equiv_surface`), so that MR7's common-`Ω` statements need no generation
hypothesis:

* **`isFix_rhoPi_iff_rhoX`**: the universal covers of `Π_X = PiX D` and of `π₁ᵉᵗ(X)` agree
  (`ker_bcToDeltaX`, `ker_rhoX`);
* `IsArithRep.toIsChernRepDivG`: an arithmetic representative is a geometric one (MR5's
  `IsChernRepDiv` for the model `X`);
* `deltaXEquivPi1 : π₁ᵉᵗ(X) ≃ₜ* Δ_X` and `iotaG : π₁ᵉᵗ(X) → Π_X`;
  **`map_iotaG_chern`**: `ι^* c^{ar}(E) = c₁(E)` (MR5's `c1Div`);
* **`mapEquiv_resDeltaG`**: `res_{Δ_X} c^{ar}(E) ↦ c₁(pt)^{deg E}` under `π₁ᵉᵗ(X) ≃ Δ_X`;
* **`resDelta_generatesG`**: if `deg E` is a unit mod `n` (genus `≥ 1`), `res_{Δ_X} c^{ar}(E)`
  generates `H²(Δ_X, μ_n)`;
* **`exists_hlam_isUnitG`**: `exists_hlam_isUnit` with the generation hypotheses discharged.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open WeilCurves.FunctionField CurvesJacobian.ChernClass CurvesJacobian.Kummer

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.DeltaXEquiv

universe u

attribute [local instance 2000] Kummer.group_piX
attribute [local instance] isFunctionField_F

section GenericChern

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {X : Scheme.{u}} [X.Over (Spec (.of (kbar k Ω)))] [IsCurveOver (kbar k Ω) X] [IsIntegral X]
  [Nonempty (⊤ : X.Opens)]
  {eL : X.functionField ≃+* (baseChange D).L} (hH : (baseChange D).H ≤ (baseChange D).HL)
  (hk : ∀ c : kbar k Ω, ((eL (algebraMap (kbar k Ω) X.functionField c) :
    (baseChange D).L) : Ω) = algebraMap (kbar k Ω) Ω c)
  {τ : X.functionField} (hτ : ((eL τ : (baseChange D).L) : Ω) = t)
  {n : ℕ} [NeZero n]

include hk hτ in
/-- `ker ρ_X ⊆ ker ρ` in their action on `Ω`. -/
theorem isFix_rhoX_of_isFix_rhoPi {f : Ω} (hf : IsFix (ArithChern.rhoPi D) f) :
    IsFix (rhoX (baseChange D) eL hH) f := by
  intro σ hσ
  rw [ker_rhoX (hH := hH) hk hτ] at hσ
  exact hf _ ((QuotientGroup.eq_one_iff _).2 (bcToDeltaTilde_mem_kernel hσ))

include hk hτ in
/-- `ker ρ ⊆ ker ρ_X` in their action on `Ω`. -/
theorem isFix_rhoPi_of_isFix_rhoX {f : Ω} (hf : IsFix (rhoX (baseChange D) eL hH) f) :
    IsFix (ArithChern.rhoPi D) f := by
  intro σ hσ
  have hσ1 : (QuotientGroup.mk' _ σ : PiX D) = 1 := MonoidHom.mem_ker.1 hσ
  have hmem : σ ∈ deltaTilde D := by
    change (QuotientGroup.mk' _ σ : PiX D) ∈ DeltaX D
    rw [hσ1]
    exact one_mem _
  obtain ⟨σ', hσ'⟩ := bcToDeltaTilde_surjective (D := D) ⟨σ, hmem⟩
  have he : ((bcToDeltaTilde D σ' : deltaTilde D) : D.H) = σ := congrArg Subtype.val hσ'
  have h1 : σ' ∈ (bcToDeltaX D).ker := by
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    rw [coe_bcToDeltaX, he]
    exact hσ1
  rw [ker_bcToDeltaX, ← ker_rhoX (hH := hH) hk hτ] at h1
  rw [← he]
  exact hf σ' h1

include hk hτ in
/-- **The universal covers agree**: `IsFix ρ f ↔ IsFix ρ_X f`. -/
theorem isFix_rhoPi_iff_rhoX {f : Ω} :
    IsFix (ArithChern.rhoPi D) f ↔ IsFix (rhoX (baseChange D) eL hH) f :=
  ⟨isFix_rhoX_of_isFix_rhoPi hH hk hτ, isFix_rhoPi_of_isFix_rhoX hH hk hτ⟩

include hk hτ in
/-- **An arithmetic representative is a geometric one** (for the model `X` of `baseChange D`). -/
theorem IsArithRep.toIsChernRepDivG {E : Divisor (kbar k Ω) (F (baseChange D))} {f : Ω}
    (hf : ArithChern.IsArithRep D n E f) : IsChernRepDiv (baseChange D) eL hH n E f where
  ne := hf.ne
  fix := isFix_rhoX_of_isFix_rhoPi hH hk hτ hf.fix
  inv σ := by
    obtain ⟨g, hg, h⟩ := hf.inv ((bcToDeltaTilde D σ : deltaTilde D) : D.H)
    exact ⟨g, isFix_rhoX_of_isFix_rhoPi hH hk hτ hg, h⟩
  loc := hf.loc

/-- **`π₁ᵉᵗ(X) ≃ₜ* Δ_X`** (`pi1TopEquivPiX` and `deltaXEquivPiBc`). -/
noncomputable def deltaXEquivPi1 :
    π₁ᵉᵗ(specPoint (baseChange D).L Ω ≫ genericL (baseChange D) X eL ⊤) ≃ₜ* DeltaX D :=
  (pi1TopEquivPiX hH hk hτ).trans (deltaXEquivPiBc D).symm

theorem deltaXEquivPi1_rhoX (σ : (baseChange D).H) :
    deltaXEquivPi1 hH hk hτ (rhoX (baseChange D) eL hH σ) = bcToDeltaX D σ := by
  rw [deltaXEquivPi1, ContinuousMulEquiv.trans_apply, ← pi1TopEquivPiX_symm_mk (hH := hH) hk hτ,
    ContinuousMulEquiv.apply_symm_apply]
  rfl

variable (D) in
/-- `κ : H_{k̄} ≅ Δ̃ ⊆ H`. -/
noncomputable def kappaG : (baseChange D).H →* D.H :=
  (deltaTilde D).subtype.comp (bcToDeltaTilde D)

/-- **`ι : π₁ᵉᵗ(X) ≃ Δ_X ⊆ Π_X`.** -/
noncomputable def iotaG :
    π₁ᵉᵗ(specPoint (baseChange D).L Ω ≫ genericL (baseChange D) X eL ⊤) →* PiX D :=
  (DeltaX D).subtype.comp (deltaXEquivPi1 hH hk hτ).toMulEquiv.toMonoidHom

theorem continuous_iotaG : Continuous (iotaG hH hk hτ) :=
  continuous_subtype_val.comp (deltaXEquivPi1 hH hk hτ).continuous

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
theorem iotaG_rhoX (σ : (baseChange D).H) :
    ArithChern.rhoPi D (kappaG D σ) = iotaG hH hk hτ (rhoX (baseChange D) eL hH σ) := by
  change _ = ((deltaXEquivPi1 hH hk hτ (rhoX (baseChange D) eL hH σ) : DeltaX D) : PiX D)
  rw [deltaXEquivPi1_rhoX, coe_bcToDeltaX]
  rfl

/-- `ι(π₁ᵉᵗ(X)) ⊆ Δ_X` acts trivially on `μ_n`. -/
theorem iotaG_smul_mu (γ : π₁ᵉᵗ(specPoint (baseChange D).L Ω ≫ genericL (baseChange D) X eL ⊤))
    (ζ : Mu n Ω) : iotaG hH hk hτ γ • ζ = ζ :=
  JacInput.deltaX_smul_mu (deltaXEquivPi1 hH hk hτ γ) ζ

set_option synthInstance.maxHeartbeats 400000 in
-- the group structure of the quotient `Π_X` is slow to synthesize
attribute [local instance] instTrivMu in
/-- **`ι^* c^{ar}(E) = c₁(E)`** on the model `X` of `baseChange D` (MR5's `c1Div`, via
`h2lcToContH2`). -/
theorem map_iotaG_chern {E : Divisor (kbar k Ω) (F (baseChange D))} {f : Ω}
    (hg : 0 < (curveGenus (kbar k Ω) X).toNat) (hf : ArithChern.IsArithRep D n E f) :
    ContH2.map (iotaG hH hk hτ) (continuous_iotaG hH hk hτ) (MonoidHom.id _)
      (fun γ ζ => (iotaG_smul_mu hH hk hτ γ ζ).trans rfl) hf.chern =
      h2lcToContH2 (Additive.toMul (c1Div hH hk hτ n hg E)) := by
  rw [c1Div_eq hk hτ hg (IsArithRep.toIsChernRepDivG hH hk hτ hf), toMul_ofMul]
  exact map_chernClassA (ArithChern.rhoPi_sPi D)
    (ArithChern.rhoPi_smul_mu (n := n) D) (ArithChern.isOpen_stabilizer_H D)
    (ArithChern.isOpen_of_rhoPi D) (rhoX_sX hH hk hτ)
    (fun σ ζ ↦ (smul_eq_of_pow_eq_one (baseChange D) n σ (by
      rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one])).symm)
    (isOpen_stabilizer (baseChange D)) (isOpen_of_rhoX hk hτ) (kappaG D)
    (fun _ _ => rfl) (iotaG hH hk hτ) (continuous_iotaG hH hk hτ)
    (fun σ => iotaG_rhoX hH hk hτ σ)
    (fun σ hσ => by rw [iotaG_rhoX hH hk hτ σ, hσ, map_one])
    (fun γ ζ => (iotaG_smul_mu hH hk hτ γ ζ).trans rfl)
    hf.toKummerInv (IsArithRep.toIsChernRepDivG hH hk hτ hf).toKummerInv

attribute [local instance] instTrivMu in
theorem deltaXEquivPi1_smul
    (γ : π₁ᵉᵗ(specPoint (baseChange D).L Ω ≫ genericL (baseChange D) X eL ⊤)) (ζ : Mu n Ω) :
    (deltaXEquivPi1 hH hk hτ).toMulEquiv γ • ζ = γ • ζ :=
  JacInput.deltaX_smul_mu (deltaXEquivPi1 hH hk hτ γ) ζ

attribute [local instance] instTrivMu in
/-- Restriction to `Δ_X` followed by `π₁ᵉᵗ(X) ≃ Δ_X` is restriction along `iotaG`. -/
theorem mapEquiv_resDeltaG_eq (c : ContH2 (PiX D) (Mu n Ω)) :
    ContH2.mapEquiv (deltaXEquivPi1 hH hk hτ).toMulEquiv (deltaXEquivPi1 hH hk hτ).continuous
        (deltaXEquivPi1 hH hk hτ).symm.continuous (deltaXEquivPi1_smul hH hk hτ)
        (JacInput.resDelta (D := D) (n := n) c) =
      ContH2.map (iotaG hH hk hτ) (continuous_iotaG hH hk hτ) (MonoidHom.id _)
        (fun γ ζ => (iotaG_smul_mu hH hk hτ γ ζ).trans rfl) c := by
  change ContH2.map _ _ _ _ (ContH2.map _ _ _ _ c) = _
  rw [contH2_map_map]
  exact contH2_map_congr _ _ _ _ (fun γ => rfl) c

set_option maxHeartbeats 2000000 in
-- unifying the restriction along `π₁ᵉᵗ(X) ≃ Δ_X ⊆ Π_X` with MR5's `c1Div` is slow
attribute [local instance] instTrivMu in
/-- `res_{Δ_X} c^{ar}(E)` corresponds to `c₁(pt)^{deg E}` under `π₁ᵉᵗ(X) ≃ Δ_X`. -/
theorem mapEquiv_resDeltaG (hg : 0 < (curveGenus (kbar k Ω) X).toNat)
    {E : Divisor (kbar k Ω) (F (baseChange D))} {f : Ω} (hf : ArithChern.IsArithRep D n E f) :
    ContH2.mapEquiv (deltaXEquivPi1 hH hk hτ).toMulEquiv (deltaXEquivPi1 hH hk hτ).continuous
        (deltaXEquivPi1 hH hk hτ).symm.continuous (deltaXEquivPi1_smul hH hk hτ)
        (JacInput.resDelta (D := D) (n := n) hf.chern) =
      ChernClass.h2lcToContH2 (c1One hH hk hτ n hg) ^ E.deg := by
  have h1 := map_iotaG_chern hH hk hτ hg hf
  have h2 := mapEquiv_resDeltaG_eq hH hk hτ (n := n) hf.chern
  refine h2.trans (h1.trans ?_)
  rw [c1Div_eq_deg_smul_c1One, toMul_zsmul, toMul_ofMul, map_zpow]

include hH hk hτ in
attribute [local instance] instTrivMu in
/-- **`res_{Δ_X} c^{ar}(E)` generates `H²(Δ_X, μ_n)`** for any Galois model `D` whose base
change is modelled by a curve `X` of genus `≥ 1`, if `deg E` is a unit mod `n`: it is
`c₁(pt)^{deg E}` (`mapEquiv_resDeltaG`) and `c₁(pt)` generates (MR5's `c1One_generates`). -/
theorem resDelta_generatesG (hg : 0 < (curveGenus (kbar k Ω) X).toNat)
    {E : Divisor (kbar k Ω) (F (baseChange D))} {f : Ω} (hf : ArithChern.IsArithRep D n E f)
    {u : ℤ} (hu : E.deg * u ≡ 1 [ZMOD n]) (c : ContH2 (DeltaX D) (Mu n Ω)) :
    c ∈ Subgroup.zpowers (JacInput.resDelta (D := D) (n := n) hf.chern) := by
  refine forall_mem_zpowers_of_equiv _ (mapEquiv_resDeltaG hH hk hτ hg hf) (fun b => ?_)
    WeilCupTransport.pow_n_eq_one hu c
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (c1One_generates hk hτ hg (h2lcEquivContH2.symm b))
  refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
  rw [← map_zpow, hj]
  exact h2lcEquivContH2.apply_symm_apply b

end GenericChern

section GenericLambda

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] [IsAlgClosed Ω]
  {n : ℕ} [NeZero n] {t₁ t₂ : Ω} {D₁ : Pi1.Orbifold.GaloisData k t₁}
  {D₂ : Pi1.Orbifold.GaloisData k t₂} [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω]
  [Fact (Function.Surjective (piJ1ToGk D₁))] [Fact (Function.Surjective (piJ1ToGk D₂))]
  {X₁ : Scheme.{u}} [X₁.Over (Spec (.of (kbar k Ω)))] [IsCurveOver (kbar k Ω) X₁]
  [IsIntegral X₁] [Nonempty (⊤ : X₁.Opens)]
  {eL₁ : X₁.functionField ≃+* (baseChange D₁).L} (hH₁ : (baseChange D₁).H ≤ (baseChange D₁).HL)
  (hk₁ : ∀ c : kbar k Ω, ((eL₁ (algebraMap (kbar k Ω) X₁.functionField c) :
    (baseChange D₁).L) : Ω) = algebraMap (kbar k Ω) Ω c)
  {τ₁ : X₁.functionField} (hτ₁ : ((eL₁ τ₁ : (baseChange D₁).L) : Ω) = t₁)
  {X₂ : Scheme.{u}} [X₂.Over (Spec (.of (kbar k Ω)))] [IsCurveOver (kbar k Ω) X₂]
  [IsIntegral X₂] [Nonempty (⊤ : X₂.Opens)]
  {eL₂ : X₂.functionField ≃+* (baseChange D₂).L} (hH₂ : (baseChange D₂).H ≤ (baseChange D₂).HL)
  (hk₂ : ∀ c : kbar k Ω, ((eL₂ (algebraMap (kbar k Ω) X₂.functionField c) :
    (baseChange D₂).L) : Ω) = algebraMap (kbar k Ω) Ω c)
  {τ₂ : X₂.functionField} (hτ₂ : ((eL₂ τ₂ : (baseChange D₂).L) : Ω) = t₂)

include hH₁ hk₁ hτ₁ hH₂ hk₂ hτ₂ in
/-- **`hlam` with `λ` a unit, for any two Galois models in a common `Ω`** whose base changes are
modelled by curves `X₁`, `X₂` of genus `≥ 1`: for representatives of divisors `E_i` of degree a
unit mod `n`, `α_Δ^* res c^{ar}(E₂) = (res c^{ar}(E₁))^λ` with `λ` a unit mod `n` (no generation
hypotheses: `resDelta_generatesG`, `natCard_contH2_deltaX`). -/
theorem exists_hlam_isUnitG (hg₁ : 0 < (curveGenus (kbar k Ω) X₁).toNat)
    (hg₂ : 0 < (curveGenus (kbar k Ω) X₂).toNat)
    (α : PiX D₁ ≃* PiX D₂) (hαc : Continuous α)
    (hαc' : Continuous α.symm) (hα : ∀ u, piXToGk D₂ (α u) = piXToGk D₁ u)
    {E₁ : Divisor (kbar k Ω) (F (baseChange D₁))} {f₁ : Ω}
    (hf₁ : ArithChern.IsArithRep D₁ n E₁ f₁) {u₁ : ℤ} (hu₁ : E₁.deg * u₁ ≡ 1 [ZMOD n])
    {E₂ : Divisor (kbar k Ω) (F (baseChange D₂))} {f₂ : Ω}
    (hf₂ : ArithChern.IsArithRep D₂ n E₂ f₂) {u₂ : ℤ} (hu₂ : E₂.deg * u₂ ≡ 1 [ZMOD n]) :
    ∃ lam : ℤ, ContH2.map (SemiAb.resDelta α.toMonoidHom hα)
        ((hαc.comp continuous_subtype_val).subtype_mk _) (MonoidHom.id _)
        (fun _ _ => (JacInput.deltaX_smul_mu _ _).trans (JacInput.deltaX_smul_mu _ _).symm)
        (JacInput.resDelta (D := D₂) (n := n) hf₂.chern) =
      (JacInput.resDelta (D := D₁) (n := n) hf₁.chern) ^ lam ∧ IsUnit (lam : ZMod n) := by
  obtain ⟨e⟩ := nonempty_deltaX_equiv_surface (D := D₁) hH₁ hk₁ hτ₁
  exact exists_hlam_isUnit α hαc hαc' hα _ _ (resDelta_generatesG hH₁ hk₁ hτ₁ hg₁ hf₁ hu₁)
    (resDelta_generatesG hH₂ hk₂ hτ₂ hg₂ hf₂ hu₂) (natCard_contH2_deltaX hg₁ e)

end GenericLambda

end CurvesJacobian.LocAn.DeltaXEquiv
