/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ArithChernCurve
import CurvesJacobian.LocAn.WeilCupTransport

/-!
# `Δ_X ≅ Π̂_{g,0}` for the geometric subgroup of a Galois model (JAC, input `eΔ` of (P6))

For a Galois model `D : GaloisData k t` (`char k = 0`, `Ω` algebraically closed) the geometric
subgroup `Δ_X = DeltaX D = ker(Π_X ↠ G_k)` is the fundamental group of the base change
`baseChange D` (the model of `X_{k̄}` inside the same `Ω`):

* `exists_SAll_baseChange`: an inertia element of `H` comes from an inertia element of
  `H_{k̄} = (baseChange D).H` (it fixes `k̄` pointwise);
* **`ambientKernel_le_map_baseChange`**: `⟨⟨S⟩⟩_H ⊆ res(⟨⟨S_{k̄}⟩⟩_{H_{k̄}})` (closure argument:
  the image of the compact `⟨⟨S_{k̄}⟩⟩` under `res = resK₀` is closed);
* `bcToDeltaX : H_{k̄} ↠ Δ_X` with kernel `⟨⟨S_{k̄}⟩⟩` (`ker_bcToDeltaX`), hence
  **`deltaXEquivPiBc D : Δ_X ≃ₜ* Π_{X_{k̄}} = PiX (baseChange D)`**;
* `pi1TopEquivPiX`: for a scheme model `(X', eL)` of a Galois model over an algebraically closed
  field, `π₁ᵉᵗ(X')` at the geometric generic point is `PiX` (SGA 1 V.8.2 via `genericL_spec`);
* **`nonempty_deltaX_equiv_surface`**: if `X'` is a curve over `k̄` modelling `baseChange D`,
  then `Δ_X ≃ₜ* Π̂_{g,0}`, `g = g(X')` (MR5's `nonempty_orientation`);
* for curves (`D₀ = curveGaloisData k hτ`): **`deltaXEquivBar hτ : Δ_X(MR5) ≃ₜ* DeltaX D₀`**
  with `coe_deltaXEquivBar` (`= ArithChern.iotaBar`), and **`nonempty_deltaX_equiv_curve`**:
  `DeltaX D₀ ≃ₜ* Π̂_{g(X),0}` — the hypothesis `eΔ` of `WeilCupTransport.weilForm_transport`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open WeilCurves.FunctionField CurvesJacobian.ChernClass CurvesJacobian.Kummer

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.DeltaXEquiv

universe u

attribute [local instance 2000] Kummer.group_piX

/-! ### `Δ_X = Π_{X_{k̄}}` for any Galois model -/

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- `H` permutes the inertia elements. -/
theorem conj_mem_SAll {g : Ω ≃ₐ[K₀ k t] Ω} (hg : g ∈ D.H) {s : Ω ≃ₐ[K₀ k t] Ω}
    (hs : s ∈ SAll D) : g * s * g⁻¹ ∈ SAll D := by
  obtain ⟨hsH, W, hkW, hsW⟩ := hs
  refine ⟨D.H.mul_mem (D.H.mul_mem hg hsH) (D.H.inv_mem hg),
    W.comap ((g⁻¹ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv : Ω →+* Ω), fun c => ?_, ?_⟩
  · rw [ValuationSubring.mem_comap]
    have : (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap k Ω c) = algebraMap k Ω c := by
      rw [IsScalarTower.algebraMap_apply k (K₀ k t) Ω, AlgEquiv.commutes]
    change (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap k Ω c) ∈ W
    rw [this]
    exact hkW c
  · refine ChernClass.mem_inertia_comap (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (fun x => ?_) hsW
    change (g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) ((g * s * g⁻¹) x) = s ((g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) x)
    simp [AlgEquiv.mul_apply]

/-- **Inertia elements of `H` come from `H_{k̄}`** (they fix `k̄` pointwise). -/
theorem exists_SAll_baseChange {s : Ω ≃ₐ[K₀ k t] Ω} (hs : s ∈ SAll D) :
    ∃ σ ∈ SAll (baseChange D), resK₀ k t σ = s := by
  obtain ⟨hsH, W, hkW, hsW⟩ := hs
  have hfix : ∀ x ∈ kbar k Ω, s x = x := fun x hx =>
    inertia_fix_algebraic hkW hsW (mem_algebraicClosure_iff.mp hx)
  obtain ⟨σ, rfl⟩ := exists_resK₀_eq hfix
  exact ⟨σ, ⟨(mem_baseChange_H D).2 hsH, W, fun c => kbar_mem W hkW c, fun a ha => hsW a ha⟩,
    rfl⟩

/-- **`⟨⟨S⟩⟩_H ⊆ res(⟨⟨S_{k̄}⟩⟩_{H_{k̄}})`.** -/
theorem ambientKernel_le_map_baseChange :
    GaloisPi1.ambientKernel D.H (SAll D) ≤
      (GaloisPi1.ambientKernel (baseChange D).H (SAll (baseChange D))).map (resK₀ k t) := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((continuous_resK₀ (k := k) (t := t)).isClosedMap _ (GaloisPi1.isClosed_ambientKernel _ _))
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, s, hs, rfl⟩
  obtain ⟨σ, hσ, he⟩ := exists_SAll_baseChange D (conj_mem_SAll D hh hs)
  refine ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ?_), he⟩
  exact ⟨1, (baseChange D).H.one_mem, σ, hσ, by simp⟩

/-- `H_{k̄} ↠ Δ̃ ↠ Δ_X`. -/
noncomputable def bcToDeltaX : (baseChange D).H →* DeltaX D :=
  deltaTildeToDeltaX.comp (bcToDeltaTilde D)

@[simp]
theorem coe_bcToDeltaX (σ : (baseChange D).H) :
    (bcToDeltaX D σ : PiX D) =
      (QuotientGroup.mk ((bcToDeltaTilde D σ : deltaTilde D) : D.H) : PiX D) := rfl

theorem continuous_bcToDeltaX : Continuous (bcToDeltaX D) :=
  ((QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _).comp
    (continuous_bcToDeltaTilde (D := D))

theorem bcToDeltaX_surjective : Function.Surjective (bcToDeltaX D) := by
  intro δ
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (δ : PiX D)
  have hmem : h ∈ deltaTilde D := by
    change (QuotientGroup.mk' _ h : PiX D) ∈ DeltaX D
    rw [QuotientGroup.mk'_apply, hh]
    exact δ.2
  obtain ⟨σ, hσ⟩ := bcToDeltaTilde_surjective (D := D) ⟨h, hmem⟩
  refine ⟨σ, Subtype.ext ?_⟩
  rw [coe_bcToDeltaX, hσ]
  exact hh

/-- **The kernel of `H_{k̄} ↠ Δ_X` is `⟨⟨S_{k̄}⟩⟩`.** -/
theorem ker_bcToDeltaX :
    (bcToDeltaX D).ker = GaloisPi1.kernel (baseChange D).H (SAll (baseChange D)) := by
  ext σ
  constructor
  · intro hσ
    have h1 : ((bcToDeltaTilde D σ : deltaTilde D) : D.H) ∈ GaloisPi1.kernel D.H (SAll D) := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hσ)
      rw [coe_bcToDeltaX] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 : resK₀ k t (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) ∈
        GaloisPi1.ambientKernel D.H (SAll D) := Subgroup.mem_subgroupOf.1 h1
    obtain ⟨σ', hσ', he⟩ := ambientKernel_le_map_baseChange D h2
    rw [resK₀_injective he] at hσ'
    exact Subgroup.mem_subgroupOf.2 hσ'
  · intro hσ
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    rw [coe_bcToDeltaX]
    exact (QuotientGroup.eq_one_iff _).2 (bcToDeltaTilde_mem_kernel hσ)

/-- `Π_X` is Hausdorff (quotient by the closed normal subgroup `⟨⟨S⟩⟩`). -/
instance t2Space_piX : T2Space (PiX D) := by
  haveI : IsClosed (GaloisPi1.kernel D.H (SAll D) : Set D.H) := GaloisPi1.isClosed_kernel _ _
  infer_instance

instance t2Space_deltaX : T2Space (DeltaX D) := inferInstance

/-- **`Δ_X ≃ₜ* Π_{X_{k̄}}`**: the geometric subgroup of `Π_X` is the fundamental group of the
base change `baseChange D` (inverse induced by `H_{k̄} ≅ Δ̃`). -/
noncomputable def deltaXEquivPiBc : DeltaX D ≃ₜ* PiX (baseChange D) :=
  GaloisPi1.equivOfSurjective (baseChange D).H (baseChange D).isClosed_H (SAll (baseChange D))
    (bcToDeltaX D) (continuous_bcToDeltaX D) (bcToDeltaX_surjective D) (ker_bcToDeltaX D)

theorem deltaXEquivPiBc_symm_mk (σ : (baseChange D).H) :
    (deltaXEquivPiBc D).symm (QuotientGroup.mk σ : PiX (baseChange D)) = bcToDeltaX D σ :=
  rfl

end Generic

/-! ### `π₁ᵉᵗ` of a scheme model and the orientation -/

section Model

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

include hk hτ in
theorem ker_rhoX : (rhoX D eL hH).ker = GaloisPi1.kernel D.H (SAll D) := by
  rw [(genericL_spec D X eL hk hH hτ ⊤ (by simp)).1, SU_top D X eL hk hτ]

variable (hH) in
/-- **`π₁ᵉᵗ(X) ≃ₜ* Π_X`** at the geometric generic point `specPoint D.L Ω ≫ genericL D X eL ⊤`
(SGA 1 V.8.2, `genericL_spec`; the inverse is induced by `ρ = rhoX`). -/
noncomputable def pi1TopEquivPiX : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ* PiX D :=
  GaloisPi1.equivOfSurjective D.H D.isClosed_H (SAll D) (rhoX D eL hH)
    (D.continuous_chartHom hH _) (rhoX_surjective hk hτ) (ker_rhoX hk hτ)

theorem pi1TopEquivPiX_symm_mk (σ : D.H) :
    (pi1TopEquivPiX hH hk hτ).symm (QuotientGroup.mk σ : PiX D) = rhoX D eL hH σ :=
  rfl

end Model

section Orientation

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {X : Scheme.{u}} [X.Over (Spec (.of (kbar k Ω)))] [IsCurveOver (kbar k Ω) X] [IsIntegral X]
  [Nonempty (⊤ : X.Opens)]
  {eL : X.functionField ≃+* (baseChange D).L} (hH : (baseChange D).H ≤ (baseChange D).HL)
  (hk : ∀ c : kbar k Ω, ((eL (algebraMap (kbar k Ω) X.functionField c) :
    (baseChange D).L) : Ω) = algebraMap (kbar k Ω) Ω c)
  {τ : X.functionField} (hτ : ((eL τ : (baseChange D).L) : Ω) = t)

include hH hk hτ in
/-- **`Δ_X ≃ₜ* Π̂_{g,0}`** for a Galois model `D` whose base change `baseChange D` is modelled
by a curve `X` over `k̄` (`g = g(X)`). -/
theorem nonempty_deltaX_equiv_surface :
    Nonempty (DeltaX D ≃ₜ* ProfiniteSurfaceGroup (curveGenus (kbar k Ω) X).toNat 0) := by
  obtain ⟨e⟩ := nonempty_orientation hH hk hτ
  exact ⟨(deltaXEquivPiBc D).trans ((pi1TopEquivPiX hH hk hτ).symm.trans e)⟩

end Orientation

/-! ### Curves -/

section Curve

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- **`Δ_X ≃ₜ* DeltaX D₀`** for `D₀ = curveGaloisData k hτ`: MR5's geometric fundamental group
`DeltaBarX k hτ = π₁ᵉᵗ(X_{k̄})` is the geometric subgroup of `Π_X`, via `ArithChern.iotaBar`
(`coe_deltaXEquivBar`). -/
noncomputable def deltaXEquivBar : DeltaBarX k hτ ≃ₜ* DeltaX (curveGaloisData k hτ) :=
  (pi1TopEquivPiX (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)).trans
    (deltaXEquivPiBc (curveGaloisData k hτ)).symm

theorem deltaXEquivBar_rhoBar (σ : (barData k hτ).H) :
    deltaXEquivBar hτ (rhoBar hτ σ) = bcToDeltaX (curveGaloisData k hτ) σ := by
  rw [deltaXEquivBar, ContinuousMulEquiv.trans_apply, ← pi1TopEquivPiX_symm_mk
    (hH := barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ),
    ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- `Δ_X ≃ DeltaX D₀ ⊆ Π_X` is `ArithChern.iotaBar`. -/
theorem coe_deltaXEquivBar (γ : DeltaBarX k hτ) :
    (deltaXEquivBar hτ γ : PiX (curveGaloisData k hτ)) = ArithChern.iotaBar hτ γ := by
  obtain ⟨σ, rfl⟩ := rhoBar_surjective (hτ := hτ) γ
  rw [deltaXEquivBar_rhoBar, ArithChern.iotaBar_rhoBar, coe_bcToDeltaX]
  rfl

/-- **`DeltaX D₀ ≃ₜ* Π̂_{g,0}`**, `g = g(X)`, for `D₀ = curveGaloisData k hτ` (the input `eΔ` of
`WeilCupTransport.weilForm_transport`). -/
theorem nonempty_deltaX_equiv_curve :
    Nonempty (DeltaX (curveGaloisData k hτ) ≃ₜ*
      ProfiniteSurfaceGroup (curveGenus k X).toNat 0) := by
  obtain ⟨e⟩ := nonempty_orientation_bar k hτ
  exact ⟨(deltaXEquivBar hτ).symm.trans e⟩

end Curve

/-! ### `H²(Δ_X, μ_n)` and the unit `λ` (the hypothesis `hlam` of `weilForm_transport`) -/

section Compare

variable {A A' A'' M : Type*} [Group A] [TopologicalSpace A] [Group A'] [TopologicalSpace A']
  [Group A''] [TopologicalSpace A''] [CommGroup M] [MulDistribMulAction A M]
  [MulDistribMulAction A' M] [MulDistribMulAction A'' M]

theorem h2lcToContH2_surjective :
    Function.Surjective (ChernClass.h2lcToContH2 : Pi1.Profinite.H2lc A M →* ContH2 A M) := by
  intro c
  induction c using ContH2.induction_on with
  | h c => exact ⟨QuotientGroup.mk ⟨c.1, c.2⟩, rfl⟩

/-- pi1's `H2lc` and LCFT's `ContH2` are the same group. -/
noncomputable def h2lcEquivContH2 : Pi1.Profinite.H2lc A M ≃* ContH2 A M :=
  MulEquiv.ofBijective ChernClass.h2lcToContH2
    ⟨WeilCupTransport.h2lcToContH2_injective, h2lcToContH2_surjective⟩

/-- Restriction along `φ` then along `φ'` is restriction along `φ ∘ φ'`. -/
theorem contH2_map_map (φ : A' →* A) (hφ : Continuous φ) (h : ∀ g m, φ g • m = g • m)
    (φ' : A'' →* A') (hφ' : Continuous φ') (h' : ∀ g m, φ' g • m = g • m) (c : ContH2 A M) :
    ContH2.map φ' hφ' (MonoidHom.id M) h' (ContH2.map φ hφ (MonoidHom.id M) h c) =
      ContH2.map (φ.comp φ') (hφ.comp hφ') (MonoidHom.id M)
        (fun g m => (h (φ' g) m).trans (h' g m)) c := by
  induction c using ContH2.induction_on with
  | h c => rfl

/-- `ContH2.map` only depends on the map `φ`. -/
theorem contH2_map_congr {φ φ' : A' →* A} (hφ : Continuous φ) (hφ' : Continuous φ')
    (h : ∀ g m, φ g • m = g • m) (h' : ∀ g m, φ' g • m = g • m) (he : ∀ g, φ g = φ' g)
    (c : ContH2 A M) :
    ContH2.map φ hφ (MonoidHom.id M) h c = ContH2.map φ' hφ' (MonoidHom.id M) h' c := by
  obtain rfl : φ = φ' := MonoidHom.ext he
  rfl

end Compare

section Lambda

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] [IsAlgClosed Ω]
  {n : ℕ} [NeZero n]

/-- **`#H²(Δ_X, μ_n) = n`** for `Δ_X ≅ Π̂_{g,0}`, `g ≥ 1` (`TopClass.h2EquivAny`). -/
theorem natCard_contH2_deltaX {t : Ω} {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω]
    {g : ℕ} (hg : 0 < g) (eΔ : DeltaX D ≃ₜ* ProfiniteSurfaceGroup g 0) :
    Nat.card (ContH2 (DeltaX D) (Mu n Ω)) = n := by
  rw [← Nat.card_congr (h2lcEquivContH2 (A := DeltaX D) (M := Mu n Ω)).toEquiv]
  exact (Nat.card_congr (TopClass.h2EquivAny hg eΔ JacInput.deltaX_smul_mu).toEquiv).trans
    (natCard_mu (k := k) Ω n)

variable {t₁ t₂ : Ω} {D₁ : Pi1.Orbifold.GaloisData k t₁} {D₂ : Pi1.Orbifold.GaloisData k t₂}
  [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω]
  [Fact (Function.Surjective (piJ1ToGk D₁))] [Fact (Function.Surjective (piJ1ToGk D₂))]

/-- **`hlam`**: if `r₁` generates `H²(Δ_{X₁}, μ_n)`, then `α_Δ^* r₂ = r₁^λ` for some `λ`. -/
theorem exists_hlam (α : PiX D₁ ≃* PiX D₂) (hαc : Continuous α)
    (hα : ∀ u, piXToGk D₂ (α u) = piXToGk D₁ u)
    (r₁ : ContH2 (DeltaX D₁) (Mu n Ω)) (r₂ : ContH2 (DeltaX D₂) (Mu n Ω))
    (hgen₁ : ∀ c, c ∈ Subgroup.zpowers r₁) :
    ∃ lam : ℤ, ContH2.map (SemiAb.resDelta α.toMonoidHom hα)
        ((hαc.comp continuous_subtype_val).subtype_mk _) (MonoidHom.id _)
        (fun _ _ => (JacInput.deltaX_smul_mu _ _).trans (JacInput.deltaX_smul_mu _ _).symm) r₂ =
      r₁ ^ lam := by
  obtain ⟨lam, h⟩ := Subgroup.mem_zpowers_iff.1 (hgen₁ (ContH2.map
    (SemiAb.resDelta α.toMonoidHom hα) ((hαc.comp continuous_subtype_val).subtype_mk _)
    (MonoidHom.id _)
    (fun _ _ => (JacInput.deltaX_smul_mu _ _).trans (JacInput.deltaX_smul_mu _ _).symm) r₂))
  exact ⟨lam, h.symm⟩

/-- **`hlam` with `λ` a unit**: if `r_i` generates `H²(Δ_{X_i}, μ_n)` (`i = 1, 2`) and
`#H²(Δ_{X₁}, μ_n) = n` (`natCard_contH2_deltaX`), then `α_Δ^* r₂ = r₁^λ` with `λ` a unit mod `n`
(`α_Δ^*` is an isomorphism of cyclic groups of order `n`). -/
theorem exists_hlam_isUnit (α : PiX D₁ ≃* PiX D₂) (hαc : Continuous α)
    (hαc' : Continuous α.symm) (hα : ∀ u, piXToGk D₂ (α u) = piXToGk D₁ u)
    (r₁ : ContH2 (DeltaX D₁) (Mu n Ω)) (r₂ : ContH2 (DeltaX D₂) (Mu n Ω))
    (hgen₁ : ∀ c, c ∈ Subgroup.zpowers r₁) (hgen₂ : ∀ c, c ∈ Subgroup.zpowers r₂)
    (hcard : Nat.card (ContH2 (DeltaX D₁) (Mu n Ω)) = n) :
    ∃ lam : ℤ, ContH2.map (SemiAb.resDelta α.toMonoidHom hα)
        ((hαc.comp continuous_subtype_val).subtype_mk _) (MonoidHom.id _)
        (fun _ _ => (JacInput.deltaX_smul_mu _ _).trans (JacInput.deltaX_smul_mu _ _).symm) r₂ =
      r₁ ^ lam ∧ IsUnit (lam : ZMod n) := by
  have hα' : ∀ v, piXToGk D₁ (α.symm v) = piXToGk D₂ v := fun v => by
    rw [← hα, α.apply_symm_apply]
  set αΔ := SemiAb.resDelta α.toMonoidHom hα
  set βΔ := SemiAb.resDelta α.symm.toMonoidHom hα'
  have hαΔc : Continuous αΔ := (hαc.comp continuous_subtype_val).subtype_mk _
  have hβΔc : Continuous βΔ := (hαc'.comp continuous_subtype_val).subtype_mk _
  obtain ⟨lam, hlam⟩ := exists_hlam α hαc hα r₁ r₂ hgen₁
  refine ⟨lam, hlam, ?_⟩
  -- `r₁` is the image of `β_Δ^* r₁ = r₂^j`
  have hsurj : ContH2.map αΔ hαΔc (MonoidHom.id _)
      (fun _ _ => (JacInput.deltaX_smul_mu _ _).trans (JacInput.deltaX_smul_mu _ _).symm)
      (ContH2.map βΔ hβΔc (MonoidHom.id _)
        (fun _ _ => (JacInput.deltaX_smul_mu _ _).trans (JacInput.deltaX_smul_mu _ _).symm)
        r₁) = r₁ := by
    have hβα : ∀ y, βΔ (αΔ y) = y := fun y => Subtype.ext (α.symm_apply_apply (y : PiX D₁))
    rw [contH2_map_map]
    induction r₁ using ContH2.induction_on with
    | h c =>
      rw [ContH2.map_mk]
      congr 1
      exact ContH2.cocycles_ext fun a b => by
        simp only [ContH2.cocyclesMap_apply, MonoidHom.id_apply, MonoidHom.coe_comp,
          Function.comp_apply, hβα]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hgen₂ (ContH2.map βΔ hβΔc (MonoidHom.id _)
    (fun _ _ => (JacInput.deltaX_smul_mu _ _).trans (JacInput.deltaX_smul_mu _ _).symm) r₁))
  rw [← hj, map_zpow, hlam, ← zpow_mul] at hsurj
  have hord : orderOf r₁ = n := by rw [orderOf_eq_card_of_forall_mem_zpowers hgen₁, hcard]
  have h1 : r₁ ^ (lam * j - 1) = 1 := by
    rw [zpow_sub, zpow_one, hsurj, mul_inv_cancel]
  have hdvd : (n : ℤ) ∣ lam * j - 1 := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  have h0 : ((lam * j - 1 : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 hdvd
  push_cast at h0
  exact IsUnit.of_mul_eq_one (j : ZMod n) (by linear_combination h0)

end Lambda

section CurveLambda

attribute [local instance] isFunctionField_F

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)] {n : ℕ} [NeZero n]

/-- If `G R = y^d` for a generator `y`, `d` is a unit mod `n` and the source is killed by `n`,
then `R` generates. -/
theorem forall_mem_zpowers_of_equiv {A B : Type*} [CommGroup A] [CommGroup B] (G : A ≃* B)
    {R : A} {y : B} {d : ℤ} (hR : G R = y ^ d) (hy : ∀ b, b ∈ Subgroup.zpowers y)
    (hn : ∀ a : A, a ^ n = 1) {u : ℤ} (hu : d * u ≡ 1 [ZMOD n]) (c : A) :
    c ∈ Subgroup.zpowers R := by
  have hmod : ∀ (a : A) {i j : ℤ}, i ≡ j [ZMOD n] → a ^ i = a ^ j := fun a i j h => by
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.1 h
    have hj : j = i + n * q := by omega
    rw [hj, zpow_add, zpow_mul, zpow_natCast, hn, one_zpow, mul_one]
  set x := G.symm y
  have hRx : R = x ^ d := by
    rw [← G.symm_apply_apply R, hR, map_zpow]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hy (G c))
  have hcx : c = x ^ j := by
    rw [← G.symm_apply_apply c, ← hj, map_zpow]
  have hx : x = R ^ u := by
    rw [hRx, ← zpow_mul, hmod x hu, zpow_one]
  rw [hcx, hx, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

attribute [local instance] instTrivMu in
theorem deltaXEquivBar_smul (γ : DeltaBarX k hτ) (ζ : Mu n (FFClosure X)) :
    (deltaXEquivBar hτ).toMulEquiv γ • ζ = γ • ζ :=
  JacInput.deltaX_smul_mu (deltaXEquivBar hτ γ) ζ

attribute [local instance] instTrivMu in
/-- Restriction to `DeltaX D₀` followed by `Δ_X ≃ DeltaX D₀` is restriction along `iotaBar`. -/
theorem mapEquiv_resDelta_eq (c : ContH2 (PiX (curveGaloisData k hτ)) (Mu n (FFClosure X))) :
    ContH2.mapEquiv (deltaXEquivBar hτ).toMulEquiv (deltaXEquivBar hτ).continuous
        (deltaXEquivBar hτ).symm.continuous (deltaXEquivBar_smul hτ)
        (JacInput.resDelta (D := curveGaloisData k hτ) (n := n) c) =
      ContH2.map (ArithChern.iotaBar hτ) (ArithChern.continuous_iotaBar hτ) (MonoidHom.id _)
        (fun γ ζ => (ArithChern.iotaBar_smul_mu hτ γ ζ).trans rfl) c := by
  change ContH2.map _ _ _ _ (ContH2.map _ _ _ _ c) = _
  rw [contH2_map_map]
  exact contH2_map_congr _ _ _ _ (fun γ => coe_deltaXEquivBar hτ γ) c

set_option maxHeartbeats 2000000 in
-- unifying the restriction along `Δ_X ≃ DeltaX D₀ ⊆ Π_X` with `ι^*` (MR5's `c1Div`) is slow
attribute [local instance] instTrivMu in
/-- `res_{Δ_X} c^{ar}(E)` corresponds to `c₁(pt)^{deg E}` on `X_{k̄}` under `Δ_X ≃ DeltaX D₀`. -/
theorem mapEquiv_resDelta (hg : 0 < (curveGenus k X).toNat)
    {E : Divisor (kbar k (FFClosure X)) (F (barData k hτ))} {f : FFClosure X}
    (hf : ArithChern.IsArithRep (curveGaloisData k hτ) n E f) :
    ContH2.mapEquiv (deltaXEquivBar hτ).toMulEquiv (deltaXEquivBar hτ).continuous
        (deltaXEquivBar hτ).symm.continuous (deltaXEquivBar_smul hτ)
        (JacInput.resDelta (D := curveGaloisData k hτ) (n := n) hf.chern) =
      ChernClass.h2lcToContH2 (c1OneBar hτ n hg) ^ E.deg := by
  have h1 := ArithChern.map_iotaBar_chern hτ hg hf
  have h2 := mapEquiv_resDelta_eq hτ hf.chern
  refine h2.trans (h1.trans ?_)
  rw [c1Div_eq_deg_smul_c1One, toMul_zsmul, toMul_ofMul, map_zpow]
  rfl

attribute [local instance] instTrivMu in
/-- **`res_{Δ_X} c^{ar}(E)` generates `H²(Δ_X, μ_n)`** if `deg E` is a unit mod `n`
(`D₀ = curveGaloisData k hτ`, genus `≥ 1`): it is `c₁(pt)^{deg E}` on `X_{k̄}`
(`mapEquiv_resDelta`) and `c₁(pt)` generates (MR5's `c1OneBar_generates`). This discharges
`hgen₁`, `hgen₂` of `exists_hlam_isUnit` for curves. -/
theorem resDelta_generates (hg : 0 < (curveGenus k X).toNat)
    {E : Divisor (kbar k (FFClosure X)) (F (barData k hτ))} {f : FFClosure X}
    (hf : ArithChern.IsArithRep (curveGaloisData k hτ) n E f) {u : ℤ}
    (hu : E.deg * u ≡ 1 [ZMOD n])
    (c : ContH2 (DeltaX (curveGaloisData k hτ)) (Mu n (FFClosure X))) :
    c ∈ Subgroup.zpowers (JacInput.resDelta (D := curveGaloisData k hτ) (n := n) hf.chern) := by
  refine forall_mem_zpowers_of_equiv _ (mapEquiv_resDelta hτ hg hf) (fun b => ?_)
    WeilCupTransport.pow_n_eq_one hu c
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (c1OneBar_generates n hg (h2lcEquivContH2.symm b))
  refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
  rw [← map_zpow, hj]
  exact h2lcEquivContH2.apply_symm_apply b

end CurveLambda

end CurvesJacobian.LocAn.DeltaXEquiv
