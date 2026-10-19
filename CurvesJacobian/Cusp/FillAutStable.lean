/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.TwistDGC
import CurvesJacobian.Cusp.ConjInducedCusps

/-!
# Semilinear automorphisms of `Spec Γ(U')` lifting to `Π_U` preserve `Spec Γ(U)` (MR8.6)

Let `C` be a hyperbolic curve over a number field `M` with a cusp, `U = C.U ⊆ U'` with
`C' = fillCurve C h hyp = (X̄, U')` hyperbolic with a cusp. Let `σ'` be an automorphism of
`Spec Γ(U')` lying over `Spec β` for an automorphism `β` of `M`, inducing (up to a change of
base point) a continuous automorphism `A` of `Π_{U'}`, and let `ψ` be a continuous automorphism
of `Π_U` lifting `A` along `fillPiHom : Π_U ↠ Π_{U'}`. Assuming the rel-isom-DGC over `M`
(`hDGC : RelIsomDGC M`), `σ'` restricts to an automorphism of the open `Spec Γ(U) ⊆ Spec Γ(U')`
(**`CurvesJacobian.Cusp.exists_iso_specRes_comp_eq`**).

* `CurvesJacobian.Cusp.exists_theta_of_isConjInduced_semilinear`: a map induced by a morphism
  `Spec Γ(U₁) ⟶ Spec Γ(U₂)` over `Spec β` lies over an automorphism `Θ` of `G_M` induced by
  `Spec β`.
* `CurvesJacobian.Cusp.extIso_over_semilinear`: the extension `extIso` of an automorphism of
  `Spec Γ(U)` over `Spec β` lies over `Spec β`.

Proof of the main theorem: `ψ` lies over an automorphism of `G_M` induced by `Spec β`, so the
twisted DGC (`exists_isConjInduced_of_relIsomDGC_twist`) gives `F : Spec Γ(U) ≅ Spec Γ(U)` over
`Spec β` inducing `ψ`; `π₁ᵉᵗ(F^{±1})` preserves `ker fillMap`, so `F` extends to `F'` on
`Spec Γ(U')` (`exists_resAlg_coverRing`), `F'` lies over `Spec β` and induces `A`, hence
`F' = σ'` by the uniqueness part of the twisted DGC
(`eq_of_isConjInduced_of_relIsomDGC_twist`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {M : Type u} [Field M] [NumberField M] (Ω : Type u) [Field Ω] [Algebra M Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic M Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

set_option backward.isDefEq.respectTransparency false

/-- The point `Spec Ω ⟶ Spec M`. -/
local notation "sM" => Spec.map (CommRingCat.ofHom (algebraMap M Ω))

omit [Algebra.IsAlgebraic M Ω] [CharZero Ω] in
/-- **(L1) Galois projection of a semilinear induced map**: if `F : Spec Γ(U₁) ⟶ Spec Γ(U₂)`
lies over `Spec β` and `φ : Π_{U₁} → Π_{U₂}` is induced by `F`, then `φ` lies over a map
`Θ : G_M → G_M` induced by `Spec β`. -/
theorem exists_theta_of_isConjInduced_semilinear (β : M ≃+* M) {C₁ C₂ : HypCurve M}
    (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty) (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty)
    (F : Spec Γ(C₁.Xbar, C₁.U) ⟶ Spec Γ(C₂.Xbar, C₂.U))
    (hF : F ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv β)
    {φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) →
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U))}
    (H : IsConjInduced F φ) :
    ∃ Θ : π₁ᵉᵗ(sM) → π₁ᵉᵗ(sM), IsConjInduced (specRingEquiv β) Θ ∧
      ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ) := by
  obtain ⟨γ, hγ⟩ := H
  have hx₁ := basePoint_spec₂ Ω C₁ hc₁
  have hx₂ := basePoint_spec₂ Ω C₂ hc₂
  have h1 : ((basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≫ F) ≫ sKU C₂ =
      sM ≫ specRingEquiv β := by
    rw [Category.assoc, hF, ← Category.assoc, hx₁]
  have h3 : (basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≫ F ≫ sKU C₂ =
      sM ≫ specRingEquiv β := by
    rw [← Category.assoc]
    exact h1
  have h4 : (basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≫ sKU C₁ ≫
      specRingEquiv β = sM ≫ specRingEquiv β := by
    rw [← Category.assoc, hx₁]
  refine ⟨fun τ ↦ autContinuousMulEquivOfIso (fiberIsoMap (sKU C₂) h1 hx₂ γ)
    (fundamentalGroupMap (specRingEquiv β) rfl τ), ⟨fiberIsoMap (sKU C₂) h1 hx₂ γ, fun _ ↦ rfl⟩,
    fun σ ↦ ?_⟩
  have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp F (sKU C₂) rfl h1 h3) σ
  have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp (sKU C₁) (specRingEquiv β) hx₁ rfl
    h4) σ
  have c3 := DFunLike.congr_fun (fundamentalGroupMap_congr hF h3 h4) σ
  have c4 := fundamentalGroupMap_autContinuousMulEquivOfIso (sKU C₂) h1 hx₂ γ
    (fundamentalGroupMap F rfl σ)
  change fundamentalGroupMap (sKU C₂) hx₂ (φ σ) =
    autContinuousMulEquivOfIso (fiberIsoMap (sKU C₂) h1 hx₂ γ)
      (fundamentalGroupMap (specRingEquiv β) rfl (fundamentalGroupMap (sKU C₁) hx₁ σ))
  rw [hγ, c4]
  exact congrArg (autContinuousMulEquivOfIso (fiberIsoMap (sKU C₂) h1 hx₂ γ))
    ((c1.symm.trans c3).trans c2)

variable (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens}
  (h : C.U ≤ U') (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
  (hyp : haveI := IsCurveOver.isIntegral M C.Xbar
    2 < 2 * Anabelian.curveGenus M C.Xbar + cuspDegree M C.Xbar U')

omit [NumberField M] in
/-- **(L5) `extIso` of an automorphism over `Spec β` lies over `Spec β`** (semilinear analogue
of `extIso_over`). -/
lemma extIso_over_semilinear {F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U)}
    (hext : ∀ a : Γ(C.Xbar, U'), ∃ a', coverRing C C F.hom (resAlg M h a) = resAlg M h a')
    (hext' : ∀ a : Γ(C.Xbar, U'), ∃ a', coverRing C C F.inv (resAlg M h a) = resAlg M h a')
    (β : M ≃+* M) (hF : F.hom ≫ sKU C = sKU C ≫ specRingEquiv β) :
    (extIso C h hext hext').hom ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, U'))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, U'))) ≫ specRingEquiv β := by
  have hf : ∀ c : M, coverRing C C F.hom (algebraMap M Γ(C.Xbar, C.U) c) =
      algebraMap M Γ(C.Xbar, C.U) (β c) := by
    have e : CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U)) ≫ Spec.preimage F.hom =
        CommRingCat.ofHom (β : M →+* M) ≫ CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U)) :=
      Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, Spec.map_comp]; exact hF)
    intro c
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e) c
  rw [extIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  apply resAlg_injective C h
  change resAlg M h (extRing C h hext hext' (algebraMap M Γ(C.Xbar, U') c)) =
    resAlg M h (algebraMap M Γ(C.Xbar, U') (β c))
  rw [resAlg_extRing, AlgHom.commutes, hf, AlgHom.commutes]

omit [NumberField M] [Algebra.IsAlgebraic M Ω] [CharZero Ω] [IsAlgClosed Ω] in
lemma autContinuousMulEquivOfIso_refl_apply₂ (τ : π₁ᵉᵗ(sM)) :
    autContinuousMulEquivOfIso (Iso.refl (fiber sM)) τ = τ := by
  change (Iso.refl _).conjAut τ = τ
  rw [Iso.conjAut_apply]
  ext
  simp

include hc' hyp in
/-- **A semilinear automorphism of `Spec Γ(U')` lifting to `Π_U` preserves `Spec Γ(U)`**:
let `σ'` be an automorphism of `Spec Γ(U')` over `Spec β` inducing `A` on `Π_{U'}`, and let `ψ`
be an automorphism of `Π_U` with `fillPiHom ∘ ψ = A ∘ fillPiHom`. Assuming the rel-isom-DGC over
`M`, `σ'` maps the open `Spec Γ(U) ⊆ Spec Γ(U')` isomorphically onto itself. -/
theorem exists_iso_specRes_comp_eq (hDGC : RelIsomDGC M) (β : M ≃+* M)
    (σ' : Spec Γ(C.Xbar, U') ≅ Spec Γ(C.Xbar, U'))
    (hσ : σ'.hom ≫ sKU (fillCurve C h hyp) = sKU (fillCurve C h hyp) ≫ specRingEquiv β)
    (A : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')))
    (HA : IsConjInduced σ'.hom A)
    (ψ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)))
    (hψ : ∀ s, fillPiHom Ω C hc h hc' hyp (ψ s) = A (fillPiHom Ω C hc h hc' hyp s)) :
    ∃ G : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U),
      Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom) ≫ σ'.hom =
        G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom) := by
  haveI : Nonempty (baseChangeOpen M Ω U') := nonempty_fillOpen Ω C h
  -- (L2) the automorphism `Θ'` of `G_M` under `ψ`
  have hres := isConjInduced_fillPiHom Ω C hc h hc' hyp
  obtain ⟨Θ, hΘ, hAΘ⟩ := exists_theta_of_isConjInduced_semilinear Ω β (C₁ := fillCurve C h hyp)
    (C₂ := fillCurve C h hyp) hc' hc' σ'.hom hσ HA
  have hrefl : specRingEquiv (RingEquiv.refl M) = 𝟙 (Spec (.of M)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id M)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hres_over : Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom) ≫
      sKU (fillCurve C h hyp) = sKU C ≫ specRingEquiv (RingEquiv.refl M) := by
    rw [hrefl, Category.comp_id]
    exact specMap_resAlg_structure C h
  obtain ⟨Θ₀, hΘ₀, hΘ₀'⟩ := exists_theta_of_isConjInduced_semilinear Ω (RingEquiv.refl M)
    (C₁ := C) (C₂ := fillCurve C h hyp) hc hc' _ hres_over hres
  have Hid := isConjInduced_id_autIso (Iso.refl (fiber sM))
  obtain ⟨u, hu⟩ := (hΘ₀.congr_hom hrefl).exists_conj_eq Hid
  have hu' : ∀ τ, Θ₀ τ = u * τ * u⁻¹ := fun τ ↦ by
    rw [hu, autContinuousMulEquivOfIso_refl_apply₂]
  have H1 : IsConjInduced (𝟙 (Spec (.of M))) (fun τ : π₁ᵉᵗ(sM) ↦ u * τ * u⁻¹) :=
    (Hid.conj u).congr_fun fun τ ↦ by rw [autContinuousMulEquivOfIso_refl_apply₂]
  have H2 : IsConjInduced (specRingEquiv β) (Θ ∘ fun τ : π₁ᵉᵗ(sM) ↦ u * τ * u⁻¹) :=
    (H1.comp hΘ).congr_hom (Category.id_comp _)
  have hΘ' : IsConjInduced (specRingEquiv β) (fun τ ↦ u⁻¹ * Θ (u * τ * u⁻¹) * u) :=
    (H2.conj u⁻¹).congr_fun fun τ ↦ by rw [inv_inv]; rfl
  have hψΘ : ∀ s, projGk Ω C hc (ψ s) = u⁻¹ * Θ (u * projGk Ω C hc s * u⁻¹) * u := fun s ↦ by
    have e := hΘ₀' (ψ s)
    rw [hψ, hAΘ, hΘ₀', hu', hu'] at e
    rw [e]
    group
  -- (L3) the twisted DGC gives `F` inducing `ψ`
  obtain ⟨F, hF, HF⟩ := exists_isConjInduced_of_relIsomDGC_twist Ω β hDGC ψ _ hΘ' hψΘ
  haveI : IsFiniteEtale F.hom := MorphismProperty.of_isIso @IsFiniteEtale F.hom
  haveI : IsFiniteEtale F.inv := MorphismProperty.of_isIso @IsFiniteEtale F.inv
  -- (L4) `π₁ᵉᵗ(F^{±1})` preserves the filling kernel
  have hker : ∀ n, fillMap Ω C hc h n = 1 ↔ fillPiHom Ω C hc h hc' hyp n = 1 := fun n ↦ by
    rw [← fillTransport_fillPiHom Ω C hc h hc' hyp n]
    exact EmbeddingLike.map_eq_one_iff
  have hfill : ∀ n, fillMap Ω C hc h n = 1 → fillMap Ω C hc h (ψ n) = 1 := fun n hn ↦ by
    rw [hker] at hn ⊢
    rw [hψ, hn, map_one]
  have hfill' : ∀ n, fillMap Ω C hc h n = 1 → fillMap Ω C hc h (ψ.toMulEquiv.symm n) = 1 :=
    fun n hn ↦ by
      rw [hker] at hn ⊢
      have e := hψ (ψ.toMulEquiv.symm n)
      have e' : ψ (ψ.toMulEquiv.symm n) = n := ψ.toMulEquiv.apply_symm_apply n
      rw [e', hn] at e
      exact EmbeddingLike.map_eq_one_iff.1 e.symm
  have hN : ∀ n ∈ (fillMap Ω C hc h).toMonoidHom.ker,
      coverPiHom Ω C hc C hc F.hom n ∈ (fillMap Ω C hc h).toMonoidHom.ker := by
    obtain ⟨t, ht⟩ := (isConjInduced_iff_exists_conj F.hom (coverFib Ω C hc C hc F.hom) ψ).1 HF
    intro n hn
    have h1 : fillMap Ω C hc h (ψ n) = 1 := hfill n hn
    rw [ht, map_mul, map_mul, map_inv, conj_eq_one_iff] at h1
    exact h1
  have HF' := IsConjInduced.symm_of_iso F ψ.toMulEquiv HF
  have hN' : ∀ n ∈ (fillMap Ω C hc h).toMonoidHom.ker,
      coverPiHom Ω C hc C hc F.inv n ∈ (fillMap Ω C hc h).toMonoidHom.ker := by
    obtain ⟨t, ht⟩ := (isConjInduced_iff_exists_conj F.inv (coverFib Ω C hc C hc F.inv)
      ψ.toMulEquiv.symm).1 HF'
    intro n hn
    have h1 : fillMap Ω C hc h (ψ.toMulEquiv.symm n) = 1 := hfill' n hn
    rw [ht, map_mul, map_mul, map_inv, conj_eq_one_iff] at h1
    exact h1
  have hhyp := isHyperbolic_baseChange Ω (fillCurve C h hyp)
  have hext := exists_resAlg_coverRing Ω C hc h hc' hhyp F.hom hN
  have hext' := exists_resAlg_coverRing Ω C hc h hc' hhyp F.inv hN'
  -- (L5) the extension `F'` lies over `Spec β`
  have hF' := extIso_over_semilinear C h hext hext' β hF
  -- (L6) `F'` induces `A`
  have H3 : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom) ≫
      (extIso C h hext hext').hom)
      ((A ∘ autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec M Ω Γ(C.Xbar, U')) rfl rfl
        (fillAlpha Ω C hc h hc' hyp)).symm) ∘ fillMap Ω C hc h) :=
    ((HF.comp hres).congr_hom (specRes_extIso C h hext hext').symm).congr_fun
      fun σ ↦ (hψ σ).symm
  have H4 := IsConjInduced.of_comp_surjective (fillPoint_spec Ω C hc h)
    (A ∘ autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec M Ω Γ(C.Xbar, U')) rfl rfl
        (fillAlpha Ω C hc h hc' hyp)).symm) H3 (fillMap_surjective Ω C hc h hc')
  have H5 : IsConjInduced (extIso C h hext hext').hom A :=
    (((isConjInduced_id_autIso (fiberIsoMap (baseChangeSpec M Ω Γ(C.Xbar, U')) rfl rfl
      (fillAlpha Ω C hc h hc' hyp))).comp H4).congr_hom (Category.id_comp _)).congr_fun
      fun s ↦ by
        change A s = A ((fiberIsoMap (baseChangeSpec M Ω Γ(C.Xbar, U')) rfl rfl
          (fillAlpha Ω C hc h hc' hyp)).symm.conjAut ((fiberIsoMap
            (baseChangeSpec M Ω Γ(C.Xbar, U')) rfl rfl (fillAlpha Ω C hc h hc' hyp)).conjAut s))
        rw [← Iso.trans_conjAut, Iso.self_symm_id, Iso.conjAut_apply]
        congr 1
  -- (L7) uniqueness: `F' = σ'`
  have hEq : extIso C h hext hext' = σ' :=
    eq_of_isConjInduced_of_relIsomDGC_twist Ω β (C₁ := fillCurve C h hyp)
      (C₂ := fillCurve C h hyp) (hc₁ := hc') (hc₂ := hc') hDGC A Θ hΘ hAΘ hF' hσ H5 HA
  refine ⟨F, ?_⟩
  rw [← hEq]
  exact specRes_extIso C h hext hext'

end CurvesJacobian.Cusp
