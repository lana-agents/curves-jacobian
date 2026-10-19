/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.CuspExtClass
import CurvesJacobian.Cusp.CurveInertiaIsoAny
import CurvesJacobian.Cusp.SingleCusp

/-!
# `Δ_{U_x} ≅ Π̂_{g,1}` compatibly with `I_x` and with `Δ_{U_x} ↠ Δ_X` ([AbsTopIII] Prop. 1.4)

Let `k` be algebraically closed of characteristic `0`, `X` a proper curve over `k` of genus `g`
(Galois model `(D, eL)`), `x ∈ X` a closed point and `U = X ∖ {x}`. Here `Δ_{U_x} = π₁ᵉᵗ(U)`,
`Δ_X = π₁ᵉᵗ(X)` and `I_x = cuspInertia U W₀` for a place `W₀` over `x`.

**`exists_cuspCentral_equiv`**: there are `Θ : π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,1}` and
`Θ₀ : π₁ᵉᵗ(X) ≃ₜ* Π̂_{g,0}` with
* `Θ(I_x) = ⟨c⟩‾` (the cuspidal inertia group of `Π̂_{g,1}`),
* `Θ₀ ∘ (π₁ᵉᵗ(U) ↠ π₁ᵉᵗ(X)) = fillHat ∘ Θ`,
* `Θ(Ker(Δ_{U_x} ↠ Δ_X)) = cuspKernel g` and `Θ(\overline{[Ker, Δ_{U_x}]}) = ccnKernel g`.

So `Θ` identifies the maximal cuspidally central quotient `Δ^{c-cn}_{U_x}` with `CcnQuot g`
compatibly with `I_x` and `Δ_X`, and the group-theoretic results of `CuspFill` (the exact
sequence `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1`) and `CuspExtClass` (the class of the extension)
apply to the curve. Input: PI1TOP's inertia-compatible comparison
`CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed` and the
filling formula `CurvesJacobian.Cusp.ker_fundamentalGroupMap_homOfLE_eq_normalClosure`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite PreGaloisCategory
open Pi1 Pi1.SurfaceGroup CurvesJacobian.Cusp

universe u

noncomputable section

namespace CurvesJacobian.CuspCentral

/-- Conjugation in a topological group as a `ContinuousMulEquiv`. -/
def conjContinuousMulEquiv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (σ : G) : G ≃ₜ* G :=
  { MulAut.conj σ with
    continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
    continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }

@[simp] lemma conjContinuousMulEquiv_apply {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (σ x : G) : conjContinuousMulEquiv σ x = σ * x * σ⁻¹ := rfl

/-- `\overline{⟨⟨I⟩⟩}` for `I = ⟨c⟩‾` is `cuspKernel g`. -/
lemma topologicalClosure_normalClosure_inertia (g : ℕ) :
    (Subgroup.normalClosure (inertia (g := g) (r := 1) 0 : Set _)).topologicalClosure =
      cuspKernel g := by
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal (inertia_le_cuspKernel g)) inferInstance
  · refine Subgroup.topologicalClosure_mono (Subgroup.normalClosure_mono ?_)
    rintro _ rfl
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)

/-- A continuous surjection from a compact group to a Hausdorff group, through which a
continuous `φ` with the same kernel factors, induces `≃ₜ*`. -/
def continuousMulEquivOfKerEq {A B C : Type*} [Group A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [Group B] [TopologicalSpace B] [CompactSpace B]
    [Group C] [TopologicalSpace C] [T2Space C] [T2Space B]
    (f : A →* B) (hf : Continuous f) (hfs : Function.Surjective f)
    (φ : A →* C) (hφ : Continuous φ) (hφs : Function.Surjective φ) (h : f.ker = φ.ker) :
    B ≃ₜ* C :=
  let e : B ≃* C := (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs))
  have hq : IsQuotientMap f := (hf.isClosedMap).isQuotientMap hf hfs
  have he : ∀ a, e (f a) = φ a := fun a ↦ by
    change (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
      ((QuotientGroup.quotientMulEquivOfEq h)
        ((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f a))) = φ a
    rw [show (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f a) = (a : A ⧸ f.ker) from
      (MulEquiv.symm_apply_eq _).2 rfl]
    rfl
  have hc : Continuous e := hq.continuous_iff.2 (by
    convert hφ using 1
    funext a
    exact he a)
  let hh := hc.homeoOfEquivCompactToT2 (f := e.toEquiv)
  { e with
    continuous_toFun := hh.continuous
    continuous_invFun := hh.symm.continuous }

lemma continuousMulEquivOfKerEq_apply {A B C : Type*} [Group A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [Group B] [TopologicalSpace B] [CompactSpace B]
    [Group C] [TopologicalSpace C] [T2Space C] [T2Space B]
    (f : A →* B) (hf : Continuous f) (hfs : Function.Surjective f)
    (φ : A →* C) (hφ : Continuous φ) (hφs : Function.Surjective φ) (h : f.ker = φ.ker) (a : A) :
    continuousMulEquivOfKerEq f hf hfs φ hφ hφs h (f a) = φ a := by
  change (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
    ((QuotientGroup.quotientMulEquivOfEq h)
      ((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f a))) = φ a
  rw [show (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f a) = (a : A ⧸ f.ker) from
    (MulEquiv.symm_apply_eq _).2 rfl]
  rfl

/-- **Transport of the exact sequence** along `Θ : A ≃* Π̂_{g+1,1}` matching `I`, `N`, `N'` with
`⟨c⟩‾`, `cuspKernel`, `ccnKernel`: `I ∩ N' = 1` and `N = I N'`. -/
theorem exact_of_mulEquiv {A : Type*} [Group A] {g : ℕ} (Θ : A ≃* ProfiniteSurfaceGroup (g + 1) 1)
    {I N N' : Subgroup A} (hI : I.map Θ.toMonoidHom = inertia 0)
    (hN : N.map Θ.toMonoidHom = cuspKernel (g + 1))
    (hN' : N'.map Θ.toMonoidHom = ccnKernel (g + 1)) : I ⊓ N' = ⊥ ∧ N ≤ I ⊔ N' := by
  have hmem {H : Subgroup A} {b : ProfiniteSurfaceGroup (g + 1) 1} :
      b ∈ H.map Θ.toMonoidHom ↔ Θ.symm b ∈ H := Subgroup.mem_map_equiv
  refine ⟨eq_bot_iff.2 fun a ha ↦ ?_, fun n hn ↦ ?_⟩
  · have h1 : Θ a ∈ inertia (g := g + 1) (r := 1) 0 := hI ▸ hmem.2 (by simpa using ha.1)
    have h2 : Θ a ∈ ccnKernel (g + 1) := hN' ▸ hmem.2 (by simpa using ha.2)
    rw [← range_cuspInertia] at h1
    obtain ⟨k, hk⟩ := h1
    have : ccnInertia (g + 1) k = 1 := by
      change ((cuspInertia 0 k : ProfiniteSurfaceGroup (g + 1) 1) : CcnQuot (g + 1)) = 1
      rw [hk, QuotientGroup.eq_one_iff]
      exact h2
    rw [← map_one (ccnInertia (g + 1))] at this
    have hk1 := ccnInertia_injective this
    rw [hk1, map_one] at hk
    simpa using hk.symm
  · have h1 : Θ n ∈ cuspKernel (g + 1) := hN ▸ hmem.2 (by simpa using hn)
    have h2 : ((Θ n : ProfiniteSurfaceGroup (g + 1) 1) : CcnQuot (g + 1)) ∈
        (ccnInertia (g + 1)).range := by
      rw [← map_cuspKernel_eq_range_ccnInertia]
      exact ⟨_, h1, rfl⟩
    obtain ⟨k, hk⟩ := h2
    have h3 : (cuspInertia 0 k)⁻¹ * Θ n ∈ ccnKernel (g + 1) := QuotientGroup.eq.1 hk
    have h4 : cuspInertia 0 k ∈ inertia (g := g + 1) (r := 1) 0 := by
      rw [← range_cuspInertia]; exact ⟨k, rfl⟩
    set a := Θ.symm (cuspInertia 0 k)
    have ha : a ∈ I := hmem.1 (hI ▸ h4)
    have hb : a⁻¹ * n ∈ N' := by
      have := hmem.1 (hN' ▸ h3 : _ ∈ N'.map Θ.toMonoidHom)
      simpa [a] using this
    have : n = a * (a⁻¹ * n) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ha hb

section Curve

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  (eL : X.functionField ≃+* D.L) (hH : D.H ≤ D.HL)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  [Nonempty (⊤ : X.Opens)]

include hk hτ in
/-- **`Δ_{U_x} ≅ Π̂_{g,1}` and `Δ_X ≅ Π̂_{g,0}` compatibly with `I_x`, the filling map, its
kernel and the cuspidally central quotient** ([AbsTopIII] Prop. 1.4, T3 l.1764–1788, for `X`
over `k = k̄` of characteristic `0`). -/
theorem exists_cuspCentral_equiv (U : X.Opens) [Nonempty U] {x : X}
    (hUx : (U : Set X)ᶜ = {x}) {W₀ : ValuationSubring Ω}
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀) :
    ∃ (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
        ProfiniteSurfaceGroup (curveGenus k X).toNat 1)
      (Θ₀ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) ≃ₜ*
        ProfiniteSurfaceGroup (curveGenus k X).toNat 0),
      (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0 ∧
      (∀ γ, Θ₀ (fundamentalGroupMap (X.homOfLE le_top) (specPoint_genericL_homOfLE D X eL le_top)
        γ) = fillHat (curveGenus k X).toNat (Θ γ)) ∧
      (fundamentalGroupMap (X.homOfLE (le_top : U ≤ ⊤))
        (specPoint_genericL_homOfLE D X eL le_top)).toMonoidHom.ker.map Θ.toMulEquiv.toMonoidHom =
          cuspKernel (curveGenus k X).toNat ∧
      (⁅(fundamentalGroupMap (X.homOfLE (le_top : U ≤ ⊤))
        (specPoint_genericL_homOfLE D X eL le_top)).toMonoidHom.ker, ⊤⁆ :
          Subgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)).topologicalClosure.map
            Θ.toMulEquiv.toMonoidHom = ccnKernel (curveGenus k X).toNat := by
  set g := (curveGenus k X).toNat
  have hUfin : (U : Set X)ᶜ.Finite := hUx ▸ Set.finite_singleton x
  have hUne : (U : Set X)ᶜ.Nonempty := hUx ▸ Set.singleton_nonempty x
  have hcard : Nat.card ((U : Set X)ᶜ : Set X) = 1 := by
    rw [hUx, Nat.card_unique]
  obtain ⟨Θ₁, hΘ₁⟩ := exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed D eL hH hk hτ U
    hUfin hUne
  obtain ⟨j, σ, hjσ⟩ := hΘ₁ W₀ hW₀.1 hW₀U
  generalize hr : Nat.card ((U : Set X)ᶜ : Set X) = r at Θ₁ j hjσ
  obtain rfl : r = 1 := hr.symm.trans hcard
  obtain rfl : j = 0 := Subsingleton.elim _ _
  set Θ := (conjContinuousMulEquiv σ).trans Θ₁
  have hI : (cuspInertia D X eL hH U W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0 := hjσ
  -- the filling map and its kernel
  set f := (fundamentalGroupMap (X.homOfLE (le_top : U ≤ ⊤))
    (specPoint_genericL_homOfLE D X eL le_top))
  have hsub : (((⊤ : X.Opens) : Set X) \ U).Subsingleton := by
    intro a ha b hb
    have ha' : a ∈ (U : Set X)ᶜ := ha.2
    have hb' : b ∈ (U : Set X)ᶜ := hb.2
    rw [hUx] at ha' hb'
    exact ha'.trans hb'.symm
  have hker : f.toMonoidHom.ker =
      (Subgroup.normalClosure (cuspInertia D X eL hH U W₀ : Set _)).topologicalClosure :=
    ker_fundamentalGroupMap_homOfLE_eq_normalClosure D X eL hk hH hτ hUfin
      (by simp) le_top hsub hW₀ hW₀U
  have hkerc : IsClosed (SetLike.coe f.toMonoidHom.ker) := by
    rw [hker]
    exact Subgroup.isClosed_topologicalClosure _
  have hmapker : f.toMonoidHom.ker.map Θ.toMulEquiv.toMonoidHom = cuspKernel g := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, hker]
      haveI : (cuspKernel g).comap Θ.toMulEquiv.toMonoidHom |>.Normal :=
        Subgroup.Normal.comap inferInstance _
      refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
        ((Subgroup.isClosed_topologicalClosure _ :
          IsClosed (cuspKernel g : Set (ProfiniteSurfaceGroup g 1))).preimage Θ.continuous)
      intro a ha
      exact inertia_le_cuspKernel g (hI ▸ Subgroup.mem_map_of_mem _ ha)
    · rw [← topologicalClosure_normalClosure_inertia, ← hI]
      have hN : (f.toMonoidHom.ker.map Θ.toMulEquiv.toMonoidHom).Normal :=
        Subgroup.Normal.map inferInstance _ Θ.surjective
      have hC : IsClosed (SetLike.coe (f.toMonoidHom.ker.map Θ.toMulEquiv.toMonoidHom)) := by
        rw [Subgroup.coe_map]
        exact (hkerc.isCompact.image Θ.continuous).isClosed
      refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hC
      rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.mem_map_of_mem _ ?_
      rw [hker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ha)
  -- the isomorphism `Θ₀`
  have hfs : Function.Surjective f := by
    have hT := genericL_spec D X eL hk hH hτ ⊤ (by simp)
    intro y
    obtain ⟨σ, rfl⟩ := hT.2 y
    exact ⟨_, fundamentalGroupMap_genericL D X eL hH le_top σ⟩
  set φ := (fillHat g).comp Θ.toMulEquiv.toMonoidHom
  have hφ : Continuous φ := (continuous_fillHat g).comp Θ.continuous
  have hφs : Function.Surjective φ := (fillHat_surjective g).comp Θ.surjective
  have hkerφ : f.toMonoidHom.ker = φ.ker := by
    rw [← MonoidHom.comap_ker, ker_fillHat, ← hmapker,
      Subgroup.comap_map_eq_self_of_injective Θ.injective]
  refine ⟨Θ, continuousMulEquivOfKerEq f.toMonoidHom f.continuous hfs φ hφ hφs hkerφ, hI,
    fun γ ↦ continuousMulEquivOfKerEq_apply _ _ _ _ _ _ hkerφ γ, hmapker, ?_⟩
  -- the cuspidally central quotient
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine Subgroup.topologicalClosure_minimal _ ?_
      ((Subgroup.isClosed_topologicalClosure _ :
        IsClosed (ccnKernel g : Set (ProfiniteSurfaceGroup g 1))).preimage Θ.continuous)
    rw [Subgroup.commutator_le]
    intro a ha b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
      (hmapker ▸ Subgroup.mem_map_of_mem _ ha) (Subgroup.mem_top _))
  · have hC : IsClosed (SetLike.coe ((⁅f.toMonoidHom.ker, ⊤⁆ : Subgroup _).topologicalClosure.map
        Θ.toMulEquiv.toMonoidHom)) := by
      rw [Subgroup.coe_map]
      exact ((Subgroup.isClosed_topologicalClosure _).isCompact.image Θ.continuous).isClosed
    refine Subgroup.topologicalClosure_minimal _ ?_ hC
    rw [Subgroup.commutator_le]
    intro a ha b _
    rw [← hmapker] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := Θ.surjective b
    refine ⟨_, Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator ha' (Subgroup.mem_top b')), ?_⟩
    exact map_commutatorElement _ _ _

include hk hτ in
/-- **[AbsTopIII] Prop. 1.4(ii), the exact sequence `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1`** for a
proper curve `X` of genus `g ≥ 1` over `k = k̄` of characteristic `0`, `U = X ∖ {x}`,
`I_x = cuspInertia U W₀` (`W₀` a place over `x`), `N = Ker(Δ_{U_x} ↠ Δ_X)` and
`Δ^{c-cn}_{U_x} = Δ_{U_x} ⧸ \overline{[N, Δ_{U_x}]}`:
* `I_x ∩ \overline{[N, Δ_{U_x}]} = 1`, i.e. `I_x ↪ Δ^{c-cn}_{U_x}`;
* the image of `N` (the kernel of `Δ^{c-cn}_{U_x} ↠ Δ_X`) is the image of `I_x`;
* `Δ_{U_x} ↠ Δ_X` is surjective. -/
theorem cuspCentral_exact_curve (hg : 0 < (curveGenus k X).toNat) (U : X.Opens) [Nonempty U]
    {x : X} (hUx : (U : Set X)ᶜ = {x}) {W₀ : ValuationSubring Ω}
    (hW₀ : IsCentredOn D X eL ⊤ W₀) (hW₀U : ¬ IsCentredOn D X eL U W₀) :
    let f := fundamentalGroupMap (X.homOfLE (le_top : U ≤ ⊤))
      (specPoint_genericL_homOfLE D X eL le_top)
    let N' : Subgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) :=
      (⁅f.toMonoidHom.ker, ⊤⁆ : Subgroup _).topologicalClosure
    (cuspInertia D X eL hH U W₀ ⊓ N' = ⊥) ∧
      cuspInertia D X eL hH U W₀ ≤ f.toMonoidHom.ker ∧
      f.toMonoidHom.ker ≤ cuspInertia D X eL hH U W₀ ⊔ N' ∧ Function.Surjective f := by
  intro f N'
  have hUfin : (U : Set X)ᶜ.Finite := hUx ▸ Set.finite_singleton x
  have hle : cuspInertia D X eL hH U W₀ ≤ f.toMonoidHom.ker :=
    cuspInertia_le_ker D X eL hH hk hτ hUfin (by simp) le_top hW₀ hW₀U
  have hfs : Function.Surjective f := by
    have hT := genericL_spec D X eL hk hH hτ ⊤ (by simp)
    intro y
    obtain ⟨σ, rfl⟩ := hT.2 y
    exact ⟨_, fundamentalGroupMap_genericL D X eL hH le_top σ⟩
  obtain ⟨Θ, -, hI, -, hN, hN'⟩ := exists_cuspCentral_equiv D eL hH hk hτ U hUx hW₀ hW₀U
  revert Θ
  generalize (curveGenus k X).toNat = G at hg ⊢
  obtain ⟨g, rfl⟩ : ∃ g', G = g' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hg).symm⟩
  intro Θ hI hN hN'
  obtain ⟨h1, h2⟩ := exact_of_mulEquiv Θ.toMulEquiv hI hN hN'
  exact ⟨h1, hle, h2, hfs⟩

end Curve

end CurvesJacobian.CuspCentral
