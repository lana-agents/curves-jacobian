/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Cor38Unique
import CurvesJacobian.Cusp.PullbackCover
import CurvesJacobian.Cusp.BelyiDataExists
import Belyi.Anabelian.OutSemidirect

/-!
# [AbsTopII] Corollary 3.7 (b): `Π_{U_X} = Π_U ⋊^out (Π_X/Π_V)` (MR8.5)

`Topics in Absolute Anabelian Geometry II.txt` l.4698–4775, Corollary 3.7 (b): the surjection
`Π_{U_X} ↠ Π_X` is the out-semidirect product of `Π_U ↠ Π_V` with `Π_X/Π_V`, for the unique
lifting of the outer action of `Π_X/Π_V` on `Π_V` to an outer action on `Π_U`.

Setting (lead decision: `V → X` is assumed Galois). `X = CX.U` an affine hyperbolic curve over
a number field `K`, `U_X ⊆ X` a nonempty open (`subCurve`, filling `Π_{U_X} ↠ Π_X` is
`cor38Fill`), `V` a hyperbolic curve over a number field `M ⊇ K` with a finite étale **Galois**
cover `FV : V ⟶ X` (`PreGaloisCategory.IsGalois (coverObj FV)` in the Galois category of finite
étale `Spec Γ(X)`-schemes), and `U = V ×_X U_X` (a cartesian square `hsq` of `Spec Γ`'s, with
`FU : U ⟶ U_X` finite étale). With `Π_V = im(Π_V → Π_X)` and `Π_U = im(Π_U → Π_{U_X})`
(`coverPiHom`):

* `cor37b_normal`: `Π_V ⊴ Π_X` (the cover is Galois);
* **`cor37b_comap`**: `Π_U` is the preimage of `Π_V` under `Π_{U_X} ↠ Π_X`
  (`AlgebraicGeometry.FiniteEtale.range_fundamentalGroupMap_of_isPullback`);
* `cor37b_center`: `Π_U` has trivial centre (it is open in `Π_{U_X}`, whose `G_K` and `Δ` are
  slim, `CuspidalExt.center_eq_bot_of_isOpen`);
* **`cor37bEquiv`**: `Π_{U_X} ≃* Π_U ⋊^out (Π_{U_X}/Π_U)` (`extensionEquivOutSemidirect`), and
  `cor37bQuotEquiv : Π_{U_X}/Π_U ≃* Π_X/Π_V`.

The uniqueness of the lifting of the outer action is `cor37b_lift_unique` (`Cor38Unique`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-! ### Base point changes of images and normal subgroups -/

namespace AlgebraicGeometry.FiniteEtale

section BasePoint

variable {𝒞 : Type*} [Category 𝒞] {F G : 𝒞 ⥤ FintypeCat.{u}}

/-- The image of a normal subgroup under a change of fibre functor does not depend on the
isomorphism of fibre functors. -/
lemma map_autIso_eq_of_normal (α α' : F ≅ G) (S : Subgroup (Aut F)) [S.Normal] :
    S.map (autContinuousMulEquivOfIso α).toMulEquiv.toMonoidHom =
      S.map (autContinuousMulEquivOfIso α').toMulEquiv.toMonoidHom := by
  have key : ∀ (β β' : F ≅ G), S.map (autContinuousMulEquivOfIso β').toMulEquiv.toMonoidHom ≤
      S.map (autContinuousMulEquivOfIso β).toMulEquiv.toMonoidHom := by
    intro β β'
    obtain ⟨t, ht⟩ := CurvesJacobian.Cusp.exists_conjAut_eq_conj β β'
    rintro _ ⟨s, hs, rfl⟩
    let t' : Aut F := (autContinuousMulEquivOfIso β).symm t
    refine ⟨t' * s * t'⁻¹, Subgroup.Normal.conj_mem inferInstance s hs t', ?_⟩
    change β.conjAut (t' * s * t'⁻¹) = β'.conjAut s
    rw [ht, map_mul, map_mul, map_inv]
    change β.conjAut ((autContinuousMulEquivOfIso β).symm t) * _ *
      (β.conjAut ((autContinuousMulEquivOfIso β).symm t))⁻¹ = _
    have : β.conjAut ((autContinuousMulEquivOfIso β).symm t) = t :=
      (autContinuousMulEquivOfIso β).apply_symm_apply t
    rw [this]
  exact le_antisymm (key α' α) (key α α')

end BasePoint

variable {A B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- **The image of `π₁ᵉᵗ` of a cover at another point** is the image under the induced change of
base point. -/
lemma range_fundamentalGroupMap_eq_map (p : A ⟶ B) {u₁ u₂ : Spec (.of Ω) ⟶ A}
    {η₁ η₂ : Spec (.of Ω) ⟶ B} (h₁ : u₁ ≫ p = η₁) (h₂ : u₂ ≫ p = η₂) (β : fiber u₁ ≅ fiber u₂) :
    (fundamentalGroupMap p h₂).toMonoidHom.range =
      (fundamentalGroupMap p h₁).toMonoidHom.range.map
        (autContinuousMulEquivOfIso (fiberIsoMap p h₁ h₂ β)).toMulEquiv.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨τ, rfl⟩ := (autContinuousMulEquivOfIso β).surjective σ
    exact ⟨_, ⟨τ, rfl⟩, (fundamentalGroupMap_autContinuousMulEquivOfIso p h₁ h₂ β τ).symm⟩
  · rintro ⟨_, ⟨τ, rfl⟩, rfl⟩
    exact ⟨_, fundamentalGroupMap_autContinuousMulEquivOfIso p h₁ h₂ β τ⟩

/-- **The image of `π₁ᵉᵗ` of a Galois cover is normal.** -/
lemma normal_range_fundamentalGroupMap [ConnectedSpace B] (p : A ⟶ B) [IsFiniteEtale p]
    [IsGalois (coverObj p)] {v : Spec (.of Ω) ⟶ A} {η : Spec (.of Ω) ⟶ B} (h : v ≫ p = η) :
    (fundamentalGroupMap p h).toMonoidHom.range.Normal := by
  rw [range_fundamentalGroupMap_of_isFiniteEtale' p v h]
  exact stabilizer_normal_of_isGalois (fiber η) (coverObj p) _

end AlgebraicGeometry.FiniteEtale

/-! ### Open subgroups of `Π` are centre-free -/

namespace Belyi.Anabelian

/-- **Open subgroups of `Π` have trivial centre** (`G` and `Δ` are slim). -/
theorem CuspidalExt.center_eq_bot_of_isOpen (E : CuspidalExt.{u}) {N : Subgroup E.Pi}
    (hN : IsOpen (N : Set E.Pi)) : Subgroup.center N = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  have hcomm : ∀ n ∈ N, (z : E.Pi) * n = n * z := fun n hn ↦
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz ⟨n, hn⟩).symm)
  let NO : OpenSubgroup E.Pi := ⟨N, hN⟩
  have hpr : E.pr z = 1 := by
    have hopen := ChainObj.isOpen_map_pr E NO
    refine E.slim_G ⟨(N : Subgroup E.Pi).map (E.pr : E.Pi →* E.G), hopen⟩ (E.pr z) ?_
    rintro _ ⟨n, hn, rfl⟩
    change E.pr z * E.pr n = E.pr n * E.pr z
    rw [← map_mul, ← map_mul, hcomm n hn]
  have hzΔ : (z : E.Pi) ∈ (E.pr : E.Pi →* E.G).ker := hpr
  have h1 : (⟨z, hzΔ⟩ : (E.pr : E.Pi →* E.G).ker) = 1 := by
    refine E.slim_delta ⟨N.subgroupOf (E.pr : E.Pi →* E.G).ker,
      hN.preimage continuous_subtype_val⟩ _ ?_
    intro n hn
    exact Subtype.ext (hcomm n hn)
  have h2 : (z : E.Pi) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

end Belyi.Anabelian

/-! ### Quotients -/

/-- `E/f⁻¹(H) ≃* P/H` for a surjective `f : E →* P`. -/
def quotientComapEquiv {E P : Type*} [Group E] [Group P] (f : E →* P)
    (hf : Function.Surjective f) (H : Subgroup P) [H.Normal] : E ⧸ H.comap f ≃* P ⧸ H :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk'])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' H).comp f)
      ((QuotientGroup.mk'_surjective H).comp hf))

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω]
  (CX : HypCurve K) (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens)
  (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))
  (CV : HypCurve M) (hcV : (CV.U : Set CV.Xbar)ᶜ.Nonempty)
  (FV : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CX.Xbar, CX.U)) [IsFiniteEtale FV]
  (CU : HypCurve M) (hcU : (CU.U : Set CU.Xbar)ᶜ.Nonempty)
  (FU : Spec Γ(CU.Xbar, CU.U) ⟶ Spec Γ(CX.Xbar, UX)) [IsFiniteEtale FU]
  (j' : Spec Γ(CU.Xbar, CU.U) ⟶ Spec Γ(CV.Xbar, CV.U))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Strictly Belyi input with a Galois cover `V → X`** (lead decision for [AbsTopII]
Cor 3.7 (b)): a `StrictlyBelyiInput` whose `FV : V ⟶ X` is a Galois object of the Galois
category of finite étale `Spec Γ(X)`-schemes. For IUT's `X = E ∖ {0}` this is
`[2] : E ∖ E[2] ⟶ E ∖ {0}` over `K(E[2])` (Galois with group `E[2]`). -/
structure GaloisBelyiInput (M : Type u) [Field M] [NumberField M] [Algebra K M]
    extends StrictlyBelyiInput CX M where
  isGalois : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj toStrictlyBelyiInput.FV)

/-- `Π_V = im(Π_V → Π_X)`. -/
abbrev cor37bPiV : Subgroup (arithmeticExt Ω CX hcX).Pi :=
  (coverPiHom Ω CX hcX CV hcV FV).toMonoidHom.range

/-- `Π_U = im(Π_U → Π_{U_X})`. -/
abbrev cor37bPiU :
    Subgroup (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi :=
  (coverPiHom Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) CU hcU FU).toMonoidHom.range

omit [Algebra K M] [IsScalarTower K M Ω] in
/-- **`Π_V ⊴ Π_X`** for a Galois cover `V → X`. -/
theorem cor37b_normal
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj FV)) :
    (cor37bPiV Ω CX hcX CV hcV FV).Normal := by
  haveI := isIntegral_specSections CX hcX
  haveI := hgal
  haveI := normal_range_fundamentalGroupMap FV
    (rfl : (basePoint Ω CV hcV ≫ baseChangeSpec M Ω Γ(CV.Xbar, CV.U)) ≫ FV = _)
  have e : cor37bPiV Ω CX hcX CV hcV FV =
      (fundamentalGroupMap FV rfl).toMonoidHom.range.map
        (autContinuousMulEquivOfIso (coverFib Ω CX hcX CV hcV FV)).toMulEquiv.toMonoidHom := by
    ext z
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, ⟨σ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, rfl⟩
  rw [e]
  exact Subgroup.Normal.map inferInstance _ (autContinuousMulEquivOfIso _).surjective

omit [Algebra K M] [IsScalarTower K M Ω] in
/-- **[AbsTopII] Cor 3.7 (b): `Π_U` is the preimage of `Π_V` under `Π_{U_X} ↠ Π_X`** for
`U = V ×_X U_X` and `V → X` Galois. -/
theorem cor37b_comap
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj FV))
    (hsq : IsPullback j' FU FV (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))) :
    cor37bPiU Ω CX hcX UX hUX hne CU hcU FU =
      (cor37bPiV Ω CX hcX CV hcV FV).comap (cor38Fill Ω CX hcX UX hUX hne α₀) := by
  have hcUX : (UX : Set CX.Xbar)ᶜ.Nonempty := compl_nonempty_of_le hUX hcX
  haveI := isIntegral_specSections CX hcX
  haveI := isIntegral_specSections CV hcV
  haveI := isIntegral_specSections CU hcU
  haveI : IsIntegral (Spec Γ(CX.Xbar, UX)) := isIntegral_specSections (subCurve CX UX hUX hne) hcUX
  haveI := hgal
  -- base points
  set y := basePoint Ω (subCurve CX UX hUX hne) hcUX ≫ baseChangeSpec K Ω Γ(CX.Xbar, UX)
  set η := fillPoint Ω (subCurve CX UX hUX hne) hcUX hUX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)
  have hy : y ≫ Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom) = η :=
    fillPoint_spec Ω (subCurve CX UX hUX hne) hcUX hUX
  haveI : IsConnected (coverObj FU) := (isConnected_iff_connectedSpace (coverObj FU)).2
    (inferInstanceAs (ConnectedSpace (Spec Γ(CU.Xbar, CU.U))))
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected (fiber y) (coverObj FU)
  set u := (fiberObjEquivHom y (coverObj FU) x).left
  have hu : u ≫ FU = y := w_left _
  have hv : (u ≫ j') ≫ FV = η := by
    rw [Category.assoc, hsq.w, ← Category.assoc, hu, hy]
  have B1 := range_fundamentalGroupMap_of_isPullback hsq hy
    (fillMap_surjective Ω (subCurve CX UX hUX hne) hcUX hUX hcX) hu hv
  haveI hNV := normal_range_fundamentalGroupMap FV hv
  have hNU : (fundamentalGroupMap FU hu).toMonoidHom.range.Normal := by
    rw [B1]
    exact Subgroup.Normal.comap hNV _
  -- `Π_U` at the point `u`
  set xU := basePoint Ω CU hcU ≫ baseChangeSpec M Ω Γ(CU.Xbar, CU.U)
  obtain ⟨β⟩ := nonempty_iso_of_fiberFunctor (fiber xU) (fiber u)
  have hU : cor37bPiU Ω CX hcX UX hUX hne CU hcU FU =
      (fundamentalGroupMap FU hu).toMonoidHom.range := by
    have e1 : cor37bPiU Ω CX hcX UX hUX hne CU hcU FU =
        (fundamentalGroupMap FU (rfl : xU ≫ FU = _)).toMonoidHom.range.map
          (autContinuousMulEquivOfIso (coverFib Ω (subCurve CX UX hUX hne) hcUX CU hcU
            FU)).toMulEquiv.toMonoidHom := by
      ext z
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨_, ⟨σ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
    have hid : (autContinuousMulEquivOfIso (Iso.refl (fiber y))).toMulEquiv.toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun σ ↦ by
      change (Iso.refl _).conjAut σ = σ
      rw [Iso.conjAut_apply]
      simp
    rw [e1, range_fundamentalGroupMap_eq_map FU hu (rfl : xU ≫ FU = _) β.symm,
      ← map_autIso_trans, map_autIso_eq_of_normal _ (Iso.refl _), hid, Subgroup.map_id]
  -- `Π_V` at the point `u ≫ j'`
  set xV := basePoint Ω CV hcV ≫ baseChangeSpec M Ω Γ(CV.Xbar, CV.U)
  obtain ⟨β'⟩ := nonempty_iso_of_fiberFunctor (fiber xV) (fiber (u ≫ j'))
  haveI hNV' := normal_range_fundamentalGroupMap FV (rfl : xV ≫ FV = _)
  have hV : (cor37bPiV Ω CX hcX CV hcV FV).map (autContinuousMulEquivOfIso
      (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl α₀)).toMulEquiv.toMonoidHom =
      (fundamentalGroupMap FV hv).toMonoidHom.range := by
    have e1 : cor37bPiV Ω CX hcX CV hcV FV =
        (fundamentalGroupMap FV (rfl : xV ≫ FV = _)).toMonoidHom.range.map
          (autContinuousMulEquivOfIso (coverFib Ω CX hcX CV hcV FV)).toMulEquiv.toMonoidHom := by
      ext z
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨_, ⟨σ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
    rw [e1, ← map_autIso_trans, range_fundamentalGroupMap_eq_map FV (rfl : xV ≫ FV = _) hv β']
    exact map_autIso_eq_of_normal _ _ _
  rw [hU, B1, ← hV]
  ext σ
  exact Subgroup.mem_map_equiv

omit [Algebra K M] [IsScalarTower K M Ω] in
include hcV α₀ in
/-- `Π_U ⊴ Π_{U_X}`. -/
theorem cor37b_normalU
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj FV))
    (hsq : IsPullback j' FU FV (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))) :
    (cor37bPiU Ω CX hcX UX hUX hne CU hcU FU).Normal := by
  haveI := cor37b_normal Ω CX hcX CV hcV FV hgal
  rw [cor37b_comap Ω CX hcX UX hUX hne α₀ CV hcV FV CU hcU FU j' hgal hsq]
  exact Subgroup.Normal.comap inferInstance _

/-- `Π_U` has trivial centre. -/
theorem cor37b_center : Subgroup.center (cor37bPiU Ω CX hcX UX hUX hne CU hcU FU) = ⊥ :=
  CuspidalExt.center_eq_bot_of_isOpen _ (by
    have := isOpen_range_coverPiHom Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)
      CU hcU FU
    exact this)

/-- **[AbsTopII] Cor 3.7 (b): `Π_{U_X} ≃* Π_U ⋊^out (Π_{U_X}/Π_U)`.** -/
def cor37bEquiv [(cor37bPiU Ω CX hcX UX hUX hne CU hcU FU).Normal] :
    (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi ≃*
      outSemidirect (outerAction (cor37bPiU Ω CX hcX UX hUX hne CU hcU FU)) :=
  extensionEquivOutSemidirect _ (cor37b_center Ω CX hcX UX hUX hne CU hcU FU)

/-- **`Π_{U_X}/Π_U ≃* Π_X/Π_V`** (for `U = V ×_X U_X`, `V → X` Galois). -/
def cor37bQuotEquiv
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj FV))
    (hsq : IsPullback j' FU FV (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))) :
    haveI := cor37b_normal Ω CX hcX CV hcV FV hgal
    haveI := cor37b_normalU Ω CX hcX UX hUX hne α₀ CV hcV FV CU hcU FU j' hgal hsq
    (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi ⧸
        cor37bPiU Ω CX hcX UX hUX hne CU hcU FU ≃*
      (arithmeticExt Ω CX hcX).Pi ⧸ cor37bPiV Ω CX hcX CV hcV FV :=
  haveI := cor37b_normal Ω CX hcX CV hcV FV hgal
  haveI := cor37b_normalU Ω CX hcX UX hUX hne α₀ CV hcV FV CU hcU FU j' hgal hsq
  (QuotientGroup.quotientMulEquivOfEq
    (cor37b_comap Ω CX hcX UX hUX hne α₀ CV hcV FV CU hcU FU j' hgal hsq)).trans
    (quotientComapEquiv _ (fun z ↦ by
      obtain ⟨w, hw⟩ := fillMap_surjective Ω (subCurve CX UX hUX hne)
        (compl_nonempty_of_le hUX hcX) hUX hcX
        (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
          α₀) z)
      exact ⟨w, (congrArg (autContinuousMulEquivOfIso _).symm hw).trans
        ((autContinuousMulEquivOfIso _).symm_apply_apply z)⟩) _)

end CurvesJacobian.Cusp
