/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticArithChain
import CurvesJacobian.Cusp.EllipticSound

/-!
# Completeness of the elliptic cuspidalisation (MR8, round 30)

[AbsTopII] Corollary 3.3 (iii)(a), (b) and Example 3.2 (ii)
(`Topics in Absolute Anabelian Geometry II.txt` l.4381–4510). Let `D : EllipticData CX` give the
elliptic chain `X ⇝ V ⇝ D ⇝ U ⇝ … ⇝ D' ⇝ V ⇝ X` with candidate
`x = (Π_U ↠ Π_{D'} ↩ Π_V ↪ Π_X)` (`EllipticData.ellipticCandidate_spec`), and let `W ⊆ V` be an
open with cartesian squares `W = V ×_{D'} U` and `W = V ×_X U_X` (`U_X ⊆ X` nonempty open), and
`V → X` Galois. Then:

* **`Belyi.Anabelian.EllCandidate.exists_fibre_equiv_of_conj`** (group theory): the fibre
  product `Π_U ×_{Π_D} Π_V` of a candidate identified with `P_Y ↠ P_{Y'} ↩ P_V` is
  `P_Z = f_Y⁻¹(im ε_Z)` when `ε_Z` agrees with `P_V ↪ P_{Y'}` up to a change of base point
  `A : P_{Z'} ≅ P_V` and an inner automorphism of `P_{Y'}`.
* **`EllipticData.exists_fibre_equiv_of_isPullback`**: `Π_U ×_{Π_{D'}} Π_V ≅ π₁ᵉᵗ(W)`, with the
  projection to `Π_V` the map induced by `W ⊆ V` followed by a change of base point.
* **`EllipticData.ellipticCusp_complete`**: some candidate of `ellipticCusp (Π_X)` has normal
  `Π_V ⊆ Π_X`, lifts automorphisms of `Π_V` induced by `Π_X` to `Π_U ×_{Π_{D'}} Π_V`, and
  `Π_U ×_{Π_{D'}} Π_V ≅ Π_V ×_{Π_X} Π_{U_X}` over `Π_X` up to conjugation.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  PreGaloisCategory

universe u

noncomputable section

namespace Belyi.Anabelian.EllCandidate

variable {E : CuspidalExt.{u}} (x : EllCandidate E)

/-- **The fibre product of a candidate, up to conjugation.** Let `x = (Π_U ↠ Π_D ↩ Π_V ↪ Π)` be
identified (`eU`, `eD`, `eV`) with `f_Y : P_Y ↠ P_{Y'}` and `φ : P_V ↪ P_{Y'}`, let
`κ : P_Z ↪ P_Y` have image `f_Y⁻¹(im ε_Z)` for `ε_Z : P_{Z'} → P_{Y'}` with
`f_Y ∘ κ = ε_Z ∘ f_Z`, and let `ε_Z = conj(c) ∘ φ ∘ A` for an isomorphism `A : P_{Z'} ≅ P_V`.
Then `P_Z ≅ Π_U ×_{Π_D} Π_V` and `P_{Z'} ≅ Π_V` compatibly with the projections, the latter
being `eV⁻¹ ∘ A`. -/
theorem exists_fibre_equiv_of_conj {PY PY' PZ PZ' PV : Type*} [Group PY] [TopologicalSpace PY]
    [IsTopologicalGroup PY] [Group PY'] [TopologicalSpace PY'] [Group PZ] [TopologicalSpace PZ]
    [IsTopologicalGroup PZ] [CompactSpace PZ] [Group PZ'] [TopologicalSpace PZ']
    [IsTopologicalGroup PZ'] [CompactSpace PZ'] [Group PV] [TopologicalSpace PV]
    (eU : x.PiU ≃ₜ* PY) (eD : x.PiD ≃ₜ* PY') (eV : x.PiV ≃ₜ* PV) (fY : PY →ₜ* PY')
    (hfY : Function.Surjective fY) (hs : ∀ a, eD (x.surj a) = fY (eU a)) (φ : PV →ₜ* PY')
    (hφ : Function.Injective φ) (hi : ∀ y, eD (x.incl y) = φ (eV y)) (κ : PZ →ₜ* PY)
    (hκ : Function.Injective κ) (εZ : PZ' → PY') (fZ : PZ →ₜ* PZ')
    (hf : ∀ σ, fY (κ σ) = εZ (fZ σ)) (hκr : ∀ y, (∃ σ, κ σ = y) ↔ ∃ τ, εZ τ = fY y)
    (A : PZ' ≃ₜ* PV) (c : PY') (hc : ∀ τ, εZ τ = c * φ (A τ) * c⁻¹) :
    ∃ (ιg : PZ ≃ₜ* x.fibre) (εg : PZ' ≃ₜ* x.PiV),
      (∀ σ, x.fibreProj (ιg σ) = εg (fZ σ)) ∧ ∀ τ, eV (εg τ) = A τ := by
  obtain ⟨d, hd⟩ := hfY c
  let κ' : PZ →ₜ* PY :=
    { toFun := fun σ ↦ d⁻¹ * κ σ * d
      map_one' := by simp only [map_one, mul_one, inv_mul_cancel]
      map_mul' := fun a b ↦ by simp only [map_mul]; group
      continuous_toFun := (continuous_const.mul κ.continuous).mul continuous_const }
  have hκ'_apply : ∀ σ, κ' σ = d⁻¹ * κ σ * d := fun _ ↦ rfl
  let εZ' : PZ' →ₜ* PY' := φ.comp (ContinuousMonoidHom.toContinuousMonoidHom A)
  have hεZ'_apply : ∀ τ, εZ' τ = φ (A τ) := fun _ ↦ rfl
  have hι : ∀ σ, x.surj (eU.symm σ) = eD.symm (fY σ) := fun σ ↦ eD.injective (by
    rw [hs, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply])
  have hκ' : Function.Injective κ' := fun a b hab ↦ by
    rw [hκ'_apply, hκ'_apply] at hab
    exact hκ (mul_left_cancel (mul_right_cancel hab))
  have hfd : ∀ y, fY (d⁻¹ * y * d) = c⁻¹ * fY y * c := fun y ↦ by
    rw [map_mul, map_mul, map_inv, hd]
  have hκr' : ∀ y, (∃ σ, κ' σ = y) ↔ ∃ v, x.incl v = eD.symm (fY y) := by
    intro y
    constructor
    · rintro ⟨σ, rfl⟩
      obtain ⟨τ, hτ⟩ := (hκr (κ σ)).1 ⟨σ, rfl⟩
      refine ⟨eV.symm (A τ), eD.injective ?_⟩
      rw [hi, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply,
        hκ'_apply, hfd, ← hτ, hc]
      group
    · rintro ⟨v, hv⟩
      have hv' : fY y = φ (eV v) := by
        rw [← hi, hv, ContinuousMulEquiv.apply_symm_apply]
      obtain ⟨σ, hσ⟩ := (hκr (d * y * d⁻¹)).2 ⟨A.symm (eV v), by
        rw [hc, ContinuousMulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hd, hv']⟩
      refine ⟨σ, ?_⟩
      rw [hκ'_apply, hσ]
      group
  have hεZ' : Function.Injective εZ' := hφ.comp A.injective
  have hεZr' : ∀ w, (∃ τ, εZ' τ = w) ↔ ∃ v, x.incl v = eD.symm w := by
    intro w
    constructor
    · rintro ⟨τ, rfl⟩
      refine ⟨eV.symm (A τ), eD.injective ?_⟩
      rw [hi, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply,
        hεZ'_apply]
    · rintro ⟨v, hv⟩
      refine ⟨A.symm (eV v), ?_⟩
      rw [hεZ'_apply, ContinuousMulEquiv.apply_symm_apply, ← hi, hv,
        ContinuousMulEquiv.apply_symm_apply]
  have hf' : ∀ σ, fY.toMonoidHom (κ' σ) = εZ' (fZ σ) := fun σ ↦ by
    change fY (κ' σ) = εZ' (fZ σ)
    rw [hκ'_apply, hfd, hf, hc, hεZ'_apply]
    group
  obtain ⟨ιg, εg, hproj, hincl⟩ := x.exists_fibre_equiv eU.symm eD.symm fY.toMonoidHom hι κ'
    hκ' hκr' εZ' hεZ' hεZr' fZ hf'
  refine ⟨ιg, εg, hproj, fun τ ↦ hφ ?_⟩
  rw [← hi, hincl, ContinuousMulEquiv.apply_symm_apply, hεZ'_apply]

end Belyi.Anabelian.EllCandidate

namespace CurvesJacobian.Cusp

namespace EllipticData

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [Algebra M Ω] [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]
  {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (D : EllipticData (M := M) CX)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **`Π_U ×_{Π_{D'}} Π_V ≅ π₁ᵉᵗ(W)`** for a cartesian square `W = V ×_{D'} U`
([AbsTopII] Cor 3.3 (iii)(a)): for an open `W ⊆ V` and `FWU : W ⟶ U` finite étale with
`W = V ×_{D'} U`, there are a geometric point `u` of `Spec Γ(W)`, a change of base point
`A : π₁ᵉᵗ(V, u) ≅ Π_V` and isomorphisms `π₁ᵉᵗ(W, u) ≅ x.fibre`, `π₁ᵉᵗ(V, u) ≅ x.PiV` such that
the projection `x.fibre → x.PiV` is `π₁ᵉᵗ(W ⊆ V)`, and `x.PiV ≅ π₁ᵉᵗ(V, u) ≅ Π_V` is `eV ∘ A`
for the identification `eV` of `ellipticCandidate_spec` (with `x.emb = φ₁ ∘ eV`). -/
theorem exists_fibre_equiv_of_isPullback (W : D.CV.Xbar.Opens) (hW : W ≤ D.CV.U)
    (hWne : (W : Set D.CV.Xbar).Nonempty)
    (FWU : Spec Γ(D.CV.Xbar, W) ⟶ Spec Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩))
    (hsqD : IsPullback (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) FWU D.FD
      (Spec.map (CommRingCat.ofHom
        (resAlg M (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1))))).toRingHom))) :
    ∃ (u : Spec (.of Ω) ⟶ Spec Γ(D.CV.Xbar, W))
      (A : π₁ᵉᵗ(u ≫ Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) ≃ₜ*
        (arithmeticExt Ω D.CV D.hcV).Pi)
      (_ : IsConjInduced (𝟙 _) A)
      (eV : (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).PiV ≃ₜ*
        (arithmeticExt Ω D.CV D.hcV).Pi)
      (ιg : π₁ᵉᵗ(u) ≃ₜ*
        (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).fibre)
      (εg : π₁ᵉᵗ(u ≫ Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) ≃ₜ*
        (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).PiV),
      (∀ y, (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).emb y =
        D.φ₁ Ω hcX (eV y)) ∧
      (∀ σ, (PiChain.ellipticCandidate (D.isEllipticType Ω hcX)
        (D.terminalIso Ω hcX)).fibreProj (ιg σ) =
          εg (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) rfl σ)) ∧
      ∀ τ, eV (εg τ) = A τ := by
  obtain ⟨eU, eD, eV, hs, hi, he⟩ := D.ellipticCandidate_spec Ω hcX
  haveI : IsFiniteEtale FWU := MorphismProperty.of_isPullback (P := @IsFiniteEtale) hsqD
    inferInstance
  haveI : IsIntegral (Spec Γ(D.CV.Xbar, W)) :=
    isIntegral_specSections (subCurve D.CV W hW hWne) (compl_nonempty_of_le hW D.hcV)
  haveI : IsIntegral (Spec Γ(D.CV.Xbar, D.CV.U)) := isIntegral_specSections D.CV D.hcV
  haveI : IsIntegral (Spec Γ(D.CW.Xbar, D.UW (Fin.last D.n))) :=
    isIntegral_specSections D.CDp D.hcDp
  haveI : IsIntegral (Spec Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩)) :=
    isIntegral_specSections (fillCurve D.CW (D.hleW ⟨0, Nat.succ_pos _⟩)
      (D.hypW ⟨0, Nat.succ_pos _⟩)) (D.hcUW ⟨0, Nat.succ_pos _⟩)
  -- the base points of `U` and `D'`
  have hy : (fillPoint Ω D.CW D.hcW (D.hleW ⟨0, Nat.succ_pos _⟩) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩)) ≫
        Spec.map (CommRingCat.ofHom
          (resAlg M (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1))))).toRingHom) =
      fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.n)) ≫
        baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n)) :=
    fillPoint_step Ω D.CW D.hcW (D.hleW ⟨0, Nat.succ_pos _⟩)
      (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1))))
  -- a point `u` of `W` over the base point of `U`
  haveI : IsConnected (coverObj FWU) := (isConnected_iff_connectedSpace (coverObj FWU)).2
    (inferInstanceAs (ConnectedSpace (Spec Γ(D.CV.Xbar, W))))
  obtain ⟨p⟩ := nonempty_fiber_of_isConnected (fiber (fillPoint Ω D.CW D.hcW
    (D.hleW ⟨0, Nat.succ_pos _⟩) ≫ baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩)))
    (coverObj FWU)
  obtain ⟨u, hu⟩ : ∃ u : Spec (.of Ω) ⟶ Spec Γ(D.CV.Xbar, W), u ≫ FWU =
      fillPoint Ω D.CW D.hcW (D.hleW ⟨0, Nat.succ_pos _⟩) ≫
        baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩) :=
    ⟨_, w_left (fiberObjEquivHom _ (coverObj FWU) p)⟩
  have hv : (u ≫ Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) ≫ D.FD =
      fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.n)) ≫
        baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n)) := by
    rw [Category.assoc, hsqD.w, ← Category.assoc, hu, hy]
  -- the image of `π₁ᵉᵗ(W) → π₁ᵉᵗ(U)`
  have B1 := range_fundamentalGroupMap_of_isPullback hsqD hy
    (fillStepMap_surjective Ω D.CW D.hcW (D.hleW ⟨0, Nat.succ_pos _⟩)
      (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1)))) (D.hcUW (Fin.last D.n)))
    hu hv
  have hκr : ∀ y, (∃ σ, fundamentalGroupMap FWU hu σ = y) ↔
      ∃ τ, fundamentalGroupMap D.FD hv τ =
        D.stepHom Ω ⟨0, Nat.succ_pos _⟩ (Fin.last D.n) (Fin.mk_le_mk.2 (Nat.zero_le _)) y := by
    intro y
    have e := congrArg (y ∈ ·) B1
    simp only [MonoidHom.mem_range, Subgroup.mem_comap, eq_iff_iff] at e
    exact e
  have hf : ∀ σ, D.stepHom Ω ⟨0, Nat.succ_pos _⟩ (Fin.last D.n) (Fin.mk_le_mk.2 (Nat.zero_le _))
      (fundamentalGroupMap FWU hu σ) = fundamentalGroupMap D.FD hv
        (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) rfl σ) := by
    intro σ
    have h1 : u ≫ FWU ≫ Spec.map (CommRingCat.ofHom
        (resAlg M (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1))))).toRingHom) =
        fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.n)) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n)) := by
      rw [← Category.assoc, hu, hy]
    have h2 : u ≫ Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom) ≫ D.FD =
        fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.n)) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n)) := by
      rw [← Category.assoc, hv]
    have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp FWU _ hu hy h1) σ
    have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp _ D.FD rfl hv h2) σ
    rw [fundamentalGroupMap_congr hsqD.w.symm h1 h2] at c1
    exact c1.symm.trans c2
  -- the change of base point `A` and the comparison with `φ₅`
  obtain ⟨β⟩ := nonempty_iso_of_fiberFunctor
    (fiber (u ≫ Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)))
    (fiber (basePoint Ω D.CV D.hcV ≫ baseChangeSpec M Ω Γ(D.CV.Xbar, D.CV.U)))
  have H₁ : IsConjInduced D.FD (fundamentalGroupMap D.FD hv) :=
    isConjInduced_fundamentalGroupMap₂ _ hv
  have hjD : IsConjInduced D.FD
      (fun σ : π₁ᵉᵗ(basePoint Ω D.CV D.hcV ≫ baseChangeSpec M Ω Γ(D.CV.Xbar, D.CV.U)) ↦
        (D.jD Ω σ : π₁ᵉᵗ(basePoint Ω D.CDp D.hcDp ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n))))) :=
    ⟨coverFib Ω D.CDp D.hcDp D.CV D.hcV D.FD, fun _ ↦ rfl⟩
  have hTW : IsConjInduced (𝟙 _)
      (fun σ : π₁ᵉᵗ(basePoint Ω D.CDp D.hcDp ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n))) ↦
        (D.TW Ω σ : π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.n)) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n))))) :=
    (isConjInduced_id_autIso _).congr_fun fun _ ↦ rfl
  have H₂ : IsConjInduced D.FD (fun σ ↦ D.φ₅ Ω (autContinuousMulEquivOfIso β σ)) :=
    ((((isConjInduced_id_autIso β).comp hjD).comp hTW).congr_hom (h' := D.FD)
      (by rw [Category.id_comp]; exact Category.comp_id _)).congr_fun fun _ ↦ rfl
  obtain ⟨c, hc⟩ := H₁.exists_conj_eq H₂
  obtain ⟨ιg, εg, hproj, hεg⟩ :=
    EllCandidate.exists_fibre_equiv_of_conj _ eU eD eV
      (D.stepHom Ω ⟨0, Nat.succ_pos _⟩ (Fin.last D.n) (Fin.mk_le_mk.2 (Nat.zero_le _)))
      (fillStepMap_surjective Ω D.CW D.hcW (D.hleW ⟨0, Nat.succ_pos _⟩)
        (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1)))) (D.hcUW (Fin.last D.n)))
      hs (D.φ₅ Ω) (D.φ₅_injective Ω) hi
      (fundamentalGroupMap FWU hu) (fundamentalGroupMap_injective_of_isFiniteEtale' FWU u hu)
      (fundamentalGroupMap D.FD hv)
      (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) rfl) hf hκr
      (autContinuousMulEquivOfIso β) c (fun τ ↦ hc τ)
  exact ⟨u, autContinuousMulEquivOfIso β, isConjInduced_id_autIso β, eV, ιg, εg, he, hproj, hεg⟩

set_option quotPrecheck false in
/-- The elliptic candidate of `D`. -/
local notation "xD" => PiChain.ellipticCandidate (EllipticData.isEllipticType Ω hcX D)
  (EllipticData.terminalIso Ω hcX D)

/-- `im(Π_V ↪ Π_X) = im(π₁(FV))` for the elliptic candidate. -/
lemma ellipticCandidate_range_emb :
    (xD).emb.toMonoidHom.range = cor37bPiV Ω CX hcX D.CV D.hcV D.FV := by
  obtain ⟨-, -, eV, -, -, he⟩ := D.ellipticCandidate_spec Ω hcX
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨eV y, (he y).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨eV.symm w, ?_⟩
    change (xD).emb (eV.symm w) = D.φ₁ Ω hcX w
    rw [he, ContinuousMulEquiv.apply_symm_apply]

variable (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))

/-- **`Π_U ×_{Π_{D'}} Π_V ≅ Π_V ×_{Π_X} Π_{U_X}` over `Π_X` up to conjugation** for an open
`W ⊆ V` with cartesian squares `W = V ×_{D'} U` and `W = V ×_X U_X` and `V → X` Galois. -/
theorem exists_fibre_comap_equiv (W : D.CV.Xbar.Opens) (hW : W ≤ D.CV.U)
    (hWne : (W : Set D.CV.Xbar).Nonempty)
    (FWU : Spec Γ(D.CV.Xbar, W) ⟶ Spec Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩))
    (hsqD : IsPullback (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) FWU D.FD
      (Spec.map (CommRingCat.ofHom
        (resAlg M (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1))))).toRingHom)))
    (FU : Spec Γ(D.CV.Xbar, W) ⟶ Spec Γ(CX.Xbar, UX))
    (hsqX : IsPullback (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) FU D.FV
      (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)))
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV)) :
    ∃ (k : (arithmeticExt Ω CX hcX).Pi)
      (J : (xD).fibre ≃ₜ* (xD).emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀)),
      ∀ p, cor38Fill Ω CX hcX UX hUX hne α₀ (J p) = k * (xD).emb ((xD).fibreProj p) * k⁻¹ := by
  obtain ⟨u, A, hA, eV, ιg, εg, he, hproj, hεg⟩ :=
    D.exists_fibre_equiv_of_isPullback Ω hcX W hW hWne FWU hsqD
  have hcUX : (UX : Set CX.Xbar)ᶜ.Nonempty := compl_nonempty_of_le hUX hcX
  have hcC : ((subCurve D.CV W hW hWne).U : Set (subCurve D.CV W hW hWne).Xbar)ᶜ.Nonempty :=
    compl_nonempty_of_le hW D.hcV
  haveI : @IsFiniteEtale (Spec Γ((subCurve D.CV W hW hWne).Xbar, (subCurve D.CV W hW hWne).U))
      (Spec Γ(CX.Xbar, UX)) FU :=
    MorphismProperty.of_isPullback (P := @IsFiniteEtale) hsqX inferInstance
  haveI : @IsFiniteEtale (Spec Γ((subCurve D.CV W hW hWne).Xbar, (subCurve D.CV W hW hWne).U))
      (Spec Γ((subCurve CX UX hUX hne).Xbar, (subCurve CX UX hUX hne).U)) FU :=
    MorphismProperty.of_isPullback (P := @IsFiniteEtale) hsqX inferInstance
  haveI : IsIntegral (Spec Γ(D.CV.Xbar, W)) :=
    isIntegral_specSections (subCurve D.CV W hW hWne) hcC
  obtain ⟨δ⟩ := nonempty_iso_of_fiberFunctor (fiber u)
    (fiber (basePoint Ω (subCurve D.CV W hW hWne) hcC ≫ baseChangeSpec M Ω Γ(D.CV.Xbar, W)))
  have hU : IsConjInduced FU
      (fun σ : π₁ᵉᵗ(basePoint Ω (subCurve D.CV W hW hWne) hcC ≫
          baseChangeSpec M Ω Γ(D.CV.Xbar, W)) ↦
        (coverPiHom Ω (subCurve CX UX hUX hne) hcUX (subCurve D.CV W hW hWne) hcC FU σ :
          π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
            baseChangeSpec K Ω Γ(CX.Xbar, UX)))) :=
    ⟨coverFib Ω (subCurve CX UX hUX hne) hcUX (subCurve D.CV W hW hWne) hcC FU, fun _ ↦ rfl⟩
  have hfill : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))
      (fun σ : π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
          baseChangeSpec K Ω Γ(CX.Xbar, UX)) ↦
        (cor38Fill Ω CX hcX UX hUX hne α₀ σ :
          π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) := by
    have hη : (basePoint Ω (subCurve CX UX hUX hne) hcUX ≫
        baseChangeSpec K Ω Γ(CX.Xbar, UX)) ≫
          Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom) =
        fillPoint Ω (subCurve CX UX hUX hne) hcUX hUX ≫
          baseChangeSpec K Ω Γ(CX.Xbar, CX.U) :=
      fillPoint_spec Ω (subCurve CX UX hUX hne) hcUX hUX
    refine (isConjInduced_iff _ hη _).2 ⟨(fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U))
      rfl rfl α₀).symm, fun σ ↦ ?_⟩
    exact autContinuousMulEquivOfIso_symm_apply₂ _ _
  have hφ₁ : IsConjInduced D.FV
      (fun σ : π₁ᵉᵗ(basePoint Ω D.CV D.hcV ≫ baseChangeSpec M Ω Γ(D.CV.Xbar, D.CV.U)) ↦
        (D.φ₁ Ω hcX σ : π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) :=
    ⟨coverFib Ω CX hcX D.CV D.hcV D.FV, fun _ ↦ rfl⟩
  have L : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom) ≫ D.FV)
      (fun σ ↦ cor38Fill Ω CX hcX UX hUX hne α₀
        (coverPiHom Ω (subCurve CX UX hUX hne) hcUX (subCurve D.CV W hW hWne) hcC FU
          (autContinuousMulEquivOfIso δ σ))) :=
    (((isConjInduced_id_autIso δ).comp (hU.comp hfill)).congr_hom
      (h' := Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom) ≫ D.FV)
      (by rw [Category.id_comp]; exact hsqX.w.symm)).congr_fun fun _ ↦ rfl
  have R : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom) ≫ D.FV)
      (fun σ ↦ D.φ₁ Ω hcX (A (fundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) rfl σ))) :=
    (((isConjInduced_fundamentalGroupMap _ u).comp (hA.comp hφ₁)).congr_hom
      (h' := Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom) ≫ D.FV)
      (by rw [Category.id_comp])).congr_fun fun _ ↦ rfl
  obtain ⟨k, hk⟩ := L.exists_conj_eq R
  have hcomap := cor37b_comap Ω CX hcX UX hUX hne α₀ D.CV D.hcV D.FV (subCurve D.CV W hW hWne)
    hcC FU (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) hgal hsqX
  have hrange := D.ellipticCandidate_range_emb Ω hcX
  refine ⟨k, ?_⟩
  refine exists_comap_equiv_of_injective₂ ιg.symm (autContinuousMulEquivOfIso δ)
    (coverPiHom Ω (subCurve CX UX hUX hne) hcUX (subCurve D.CV W hW hWne) hcC FU)
    (coverPiHom_injective Ω (subCurve CX UX hUX hne) hcUX (subCurve D.CV W hW hWne) hcC FU)
    (cor38Fill Ω CX hcX UX hUX hne α₀)
    (xD).emb.toMonoidHom.range (fun z ↦ ?_) (fun p ↦ (xD).emb ((xD).fibreProj p)) k
    (fun p ↦ ?_)
  · rw [hrange, ← Subgroup.mem_comap, ← hcomap]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨ιg ((autContinuousMulEquivOfIso δ).symm y), ?_⟩
      simp only [ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.apply_symm_apply]
      rfl
  · have h1 : (xD).fibreProj p = εg (fundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) rfl (ιg.symm p)) :=
      (congrArg (xD).fibreProj (ιg.apply_symm_apply p)).symm.trans (hproj _)
    have h2 : ∀ τ, (xD).emb (εg τ) = D.φ₁ Ω hcX (A τ) := fun τ ↦ by rw [he, hεg]
    exact (hk (ιg.symm p)).trans (congrArg (fun t ↦ k * t * k⁻¹)
      ((congrArg (xD).emb h1).trans (h2 _)).symm)

/-- **[AbsTopII] Cor 3.3 (iii)(a), (b), completeness of `ellipticCusp`** (for the elliptic data
`D`): for an open `W ⊆ V` with cartesian squares `W = V ×_{D'} U` (`FWU`, `hsqD`) and
`W = V ×_X U_X` (`FU`, `hsqX`) for a nonempty open `U_X ⊆ X`, and `V → X` Galois (`hgal`), the
elliptic candidate `x` of `D` lies in `ellipticCusp (Π_X)`, has normal `Π_V ⊆ Π_X`, lifts
automorphisms of `Π_V` induced by `Π_X` to `Π_U ×_{Π_{D'}} Π_V`, and
`Π_U ×_{Π_{D'}} Π_V ≅ Π_V ×_{Π_X} Π_{U_X}` over `Π_X` up to conjugation by some `k`. -/
theorem ellipticCusp_complete (W : D.CV.Xbar.Opens) (hW : W ≤ D.CV.U)
    (hWne : (W : Set D.CV.Xbar).Nonempty)
    (FWU : Spec Γ(D.CV.Xbar, W) ⟶ Spec Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩))
    (hsqD : IsPullback (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) FWU D.FD
      (Spec.map (CommRingCat.ofHom
        (resAlg M (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1))))).toRingHom)))
    (FU : Spec Γ(D.CV.Xbar, W) ⟶ Spec Γ(CX.Xbar, UX))
    (hsqX : IsPullback (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) FU D.FV
      (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)))
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV)) :
    ∃ x ∈ ellipticCusp (arithmeticExt Ω CX hcX),
      x.toCuspCandidate.emb.toMonoidHom.range.Normal ∧
      (∀ (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω CX hcX).Pi),
        (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
          ∃ ψ : x.fibre ≃ₜ* x.fibre, ∀ p, x.fibreProj (ψ p) = B (x.fibreProj p)) ∧
      ∃ (k : (arithmeticExt Ω CX hcX).Pi)
        (J : x.fibre ≃ₜ* x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀)),
        ∀ p, cor38Fill Ω CX hcX UX hUX hne α₀ (J p) = k * x.emb (x.fibreProj p) * k⁻¹ := by
  have hN : (xD).emb.toMonoidHom.range.Normal := by
    rw [D.ellipticCandidate_range_emb Ω hcX]
    exact cor37b_normal Ω CX hcX D.CV D.hcV D.FV hgal
  obtain ⟨k, J, hJ⟩ := D.exists_fibre_comap_equiv Ω hcX UX hUX hne α₀ W hW hWne FWU hsqD FU
    hsqX hgal
  have hsurj : Function.Surjective (cor38Fill Ω CX hcX UX hUX hne α₀) := fun z ↦ by
    obtain ⟨w, hw⟩ := fillMap_surjective Ω (subCurve CX UX hUX hne)
      (compl_nonempty_of_le hUX hcX) hUX hcX
      (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
        α₀) z)
    exact ⟨w, (congrArg (autContinuousMulEquivOfIso _).symm hw).trans
      ((autContinuousMulEquivOfIso _).symm_apply_apply z)⟩
  refine ⟨_, D.ellipticCandidate_mem Ω hcX, hN, fun B g hB ↦ ?_, k, J, hJ⟩
  exact exists_lift_of_comap_equiv (xD).fibreProj (xD).emb (xD).emb_injective _ hsurj _ k J hJ
    B g hB

end EllipticData

end CurvesJacobian.Cusp
