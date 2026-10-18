/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Cor37b

/-!
# [AbsTopII] Corollary 3.7 (b) for a strictly Belyi input with Galois `V → X` (MR8.5)

For `S : GaloisBelyiInput CX hcX M` (a finite étale Galois `FV : V ⟶ X` of affine hyperbolic
curves) and a nonempty open `U_X ⊆ X`, the open `U = U₀ = V ×_X U_X ⊆ V`
(`StrictlyBelyiInput.U₀`, the same open as in Cor 3.7 (a), `exists_belyiData`) is the curve
`belyiCU = (V̄, U₀)`, and the square
```
Spec Γ(U₀) --res--> Spec Γ(V)
    | FU               | FV
Spec Γ(U_X) --res--> Spec Γ(X)
```
is cartesian (`isPullback_belyiFU`) with `FU` finite étale. Hence `cor37b_comap`, `cor37bEquiv`,
`cor37bQuotEquiv` apply (**`cor37b_belyi`**): `Π_{U₀} = im(Π_{U₀} → Π_{U_X})` is the preimage of
`Π_V`, `Π_{U_X} ≃* Π_{U₀} ⋊^out (Π_{U_X}/Π_{U₀})` and `Π_{U_X}/Π_{U₀} ≃* Π_X/Π_V`.

General facts: for affine opens `W ⊆ U` of a scheme, `Spec Γ(W) ⟶ Spec Γ(U)` is an open immersion
with image `fromSpec⁻¹(W)` (`isOpenImmersion_specMap_resAlg`, `opensRange_specMap_resAlg`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section Res

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] {U W : X.Opens}
  (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U)

lemma specMap_resAlg_fromSpec :
    Spec.map (CommRingCat.ofHom (resAlg k h).toRingHom) ≫ hU.fromSpec = hW.fromSpec := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 X) hU hW h
  rw [Category.comp_id] at this
  exact this

include hU hW in
lemma isOpenImmersion_specMap_resAlg :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (resAlg k h).toRingHom)) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (resAlg k h).toRingHom) ≫
      hU.fromSpec) := by
    rw [specMap_resAlg_fromSpec k hU hW h]
    infer_instance
  exact IsOpenImmersion.of_comp _ hU.fromSpec

/-- **The image of `Spec Γ(W) ⟶ Spec Γ(U)` is `fromSpec⁻¹(W)`.** -/
lemma opensRange_specMap_resAlg :
    haveI := isOpenImmersion_specMap_resAlg k hU hW h
    (Spec.map (CommRingCat.ofHom (resAlg k h).toRingHom)).opensRange = hU.fromSpec ⁻¹ᵁ W := by
  haveI := isOpenImmersion_specMap_resAlg k hU hW h
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (Spec.map (CommRingCat.ofHom (resAlg k h).toRingHom) ≫ hU.fromSpec) y ∈ W
    rw [specMap_resAlg_fromSpec k hU hW h]
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨y, rfl⟩
  · intro hx
    have hx' : hU.fromSpec x ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, hU.fromSpec.isOpenEmbedding.injective ?_⟩
    change (Spec.map (CommRingCat.ofHom (resAlg k h).toRingHom) ≫ hU.fromSpec) y = _
    rw [specMap_resAlg_fromSpec k hU hW h]
    exact hy

end Res

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω]
  {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (S : StrictlyBelyiInput CX M)
  (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `Spec Γ(U_X) ⟶ Spec Γ(X)`. -/
abbrev belyiJX : Spec Γ(CX.Xbar, UX) ⟶ Spec Γ(CX.Xbar, CX.U) :=
  Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)

namespace StrictlyBelyiInput

/-- **The curve `U = V ×_X U_X`** (`(V̄, U₀)`). -/
abbrev belyiCU : HypCurve M :=
  subCurve S.CV (S.U₀ hcX UX) (S.U₀_le hcX UX) (S.U₀_nonempty hcX UX hUX hne)

lemma belyi_hcU : ((S.belyiCU hcX UX hUX hne).U : Set (S.belyiCU hcX UX hUX hne).Xbar)ᶜ.Nonempty :=
  compl_nonempty_of_le (S.U₀_le hcX UX) S.hcV

/-- `Spec Γ(U₀) ⟶ Spec Γ(V)`. -/
abbrev belyiJ : Spec Γ(S.CV.Xbar, S.U₀ hcX UX) ⟶ Spec Γ(S.CV.Xbar, S.CV.U) :=
  Spec.map (CommRingCat.ofHom (resAlg M (S.U₀_le hcX UX)).toRingHom)

include hcX hUX hne in
lemma isAffineOpen_UX : IsAffineOpen UX :=
  isAffineOpen_U (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)

include hUX hne in
lemma isAffineOpen_U₀ : IsAffineOpen (S.U₀ hcX UX) :=
  isAffineOpen_U (S.belyiCU hcX UX hUX hne) (S.belyi_hcU hcX UX hUX hne)

include hcX hne in
lemma isOpenImmersion_belyiJX : IsOpenImmersion (belyiJX UX hUX) :=
  isOpenImmersion_specMap_resAlg K (isAffineOpen_U CX hcX) (isAffineOpen_UX hcX UX hUX hne) hUX

include hUX hne in
lemma isOpenImmersion_belyiJ : IsOpenImmersion (S.belyiJ hcX UX) :=
  isOpenImmersion_specMap_resAlg M S.isAffineOpen_V (S.isAffineOpen_U₀ hcX UX hUX hne)
    (S.U₀_le hcX UX)

/-- The images of the two open immersions correspond under `FV`. -/
lemma opensRange_belyiJ :
    haveI := isOpenImmersion_belyiJX hcX UX hUX hne
    haveI := S.isOpenImmersion_belyiJ hcX UX hUX hne
    (S.belyiJ hcX UX).opensRange = S.FV ⁻¹ᵁ (belyiJX UX hUX).opensRange := by
  haveI := isOpenImmersion_belyiJX hcX UX hUX hne
  haveI := S.isOpenImmersion_belyiJ hcX UX hUX hne
  rw [opensRange_specMap_resAlg M S.isAffineOpen_V (S.isAffineOpen_U₀ hcX UX hUX hne)
      (S.U₀_le hcX UX),
    opensRange_specMap_resAlg K (isAffineOpen_U CX hcX) (isAffineOpen_UX hcX UX hUX hne) hUX]
  ext x
  change S.isAffineOpen_V.fromSpec x ∈ S.U₀ hcX UX ↔ _
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [S.isAffineOpen_V.fromSpec.isOpenEmbedding.injective hyx] at hy
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **`U = V ×_X U_X`: the cover `FU : Spec Γ(U₀) ⟶ Spec Γ(U_X)`.** -/
def belyiFU : Spec Γ(S.CV.Xbar, S.U₀ hcX UX) ⟶ Spec Γ(CX.Xbar, UX) :=
  haveI := isOpenImmersion_belyiJX hcX UX hUX hne
  haveI := S.isOpenImmersion_belyiJ hcX UX hUX hne
  ((S.belyiJ hcX UX).isoOpensRange ≪≫
    Scheme.isoOfEq _ (S.opensRange_belyiJ hcX UX hUX hne)).hom ≫
    (S.FV ∣_ (belyiJX UX hUX).opensRange) ≫ (belyiJX UX hUX).isoOpensRange.inv

/-- **The square `U₀ = V ×_X U_X` is cartesian.** -/
theorem isPullback_belyiFU :
    IsPullback (S.belyiJ hcX UX) (S.belyiFU hcX UX hUX hne) S.FV (belyiJX UX hUX) := by
  haveI := isOpenImmersion_belyiJX hcX UX hUX hne
  haveI := S.isOpenImmersion_belyiJ hcX UX hUX hne
  refine (isPullback_morphismRestrict S.FV (belyiJX UX hUX).opensRange).flip.of_iso
    ((S.belyiJ hcX UX).isoOpensRange ≪≫
      Scheme.isoOfEq _ (S.opensRange_belyiJ hcX UX hUX hne)).symm (Iso.refl _)
    (belyiJX UX hUX).isoOpensRange.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoOpensRange_hom_ι]
  · rw [Iso.symm_hom, Iso.symm_hom, belyiFU, Iso.inv_hom_id_assoc]
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Scheme.Hom.isoOpensRange_inv_comp]

instance isFiniteEtale_belyiFU : IsFiniteEtale (S.belyiFU hcX UX hUX hne) :=
  MorphismProperty.of_isPullback (P := @IsFiniteEtale) (S.isPullback_belyiFU hcX UX hUX hne)
    inferInstance

end StrictlyBelyiInput

variable (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))

omit [IsScalarTower K M Ω] in
/-- **[AbsTopII] Corollary 3.7 (b)** for a strictly Belyi input with Galois `V → X`: with
`U = V ×_X U_X` (`belyiCU`), `Π_U = im(Π_U → Π_{U_X})` is the preimage of
`Π_V = im(Π_V → Π_X)` under `Π_{U_X} ↠ Π_X`. -/
theorem cor37b_belyi (S : GaloisBelyiInput CX M) :
    cor37bPiU Ω CX hcX UX hUX hne (S.belyiCU hcX UX hUX hne) (S.belyi_hcU hcX UX hUX hne)
        (S.belyiFU hcX UX hUX hne) =
      (cor37bPiV Ω CX hcX S.CV S.hcV S.FV).comap (cor38Fill Ω CX hcX UX hUX hne α₀) :=
  cor37b_comap Ω CX hcX UX hUX hne α₀ S.CV S.hcV S.FV (S.belyiCU hcX UX hUX hne)
    (S.belyi_hcU hcX UX hUX hne) (S.belyiFU hcX UX hUX hne) (S.belyiJ hcX UX) S.isGalois
    (S.isPullback_belyiFU hcX UX hUX hne)

/-- **[AbsTopII] Corollary 3.7 (b)**: `Π_{U_X} ≃* Π_U ⋊^out (Π_{U_X}/Π_U)` and
`Π_{U_X}/Π_U ≃* Π_X/Π_V` for `U = V ×_X U_X`, `V → X` Galois. -/
theorem cor37b_belyi_equiv (S : GaloisBelyiInput CX M) :
    haveI := cor37b_normalU Ω CX hcX UX hUX hne α₀ S.CV S.hcV S.FV (S.belyiCU hcX UX hUX hne)
      (S.belyi_hcU hcX UX hUX hne) (S.belyiFU hcX UX hUX hne) (S.belyiJ hcX UX) S.isGalois
      (S.isPullback_belyiFU hcX UX hUX hne)
    haveI := cor37b_normal Ω CX hcX S.CV S.hcV S.FV S.isGalois
    Nonempty ((arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi ≃*
        outSemidirect (outerAction (cor37bPiU Ω CX hcX UX hUX hne (S.belyiCU hcX UX hUX hne)
          (S.belyi_hcU hcX UX hUX hne) (S.belyiFU hcX UX hUX hne)))) ∧
      Nonempty ((arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi ⧸
          cor37bPiU Ω CX hcX UX hUX hne (S.belyiCU hcX UX hUX hne) (S.belyi_hcU hcX UX hUX hne)
            (S.belyiFU hcX UX hUX hne) ≃*
        (arithmeticExt Ω CX hcX).Pi ⧸ cor37bPiV Ω CX hcX S.CV S.hcV S.FV) := by
  haveI := cor37b_normalU Ω CX hcX UX hUX hne α₀ S.CV S.hcV S.FV (S.belyiCU hcX UX hUX hne)
    (S.belyi_hcU hcX UX hUX hne) (S.belyiFU hcX UX hUX hne) (S.belyiJ hcX UX) S.isGalois
    (S.isPullback_belyiFU hcX UX hUX hne)
  exact ⟨⟨cor37bEquiv Ω CX hcX UX hUX hne (S.belyiCU hcX UX hUX hne) (S.belyi_hcU hcX UX hUX hne)
      (S.belyiFU hcX UX hUX hne)⟩,
    ⟨cor37bQuotEquiv Ω CX hcX UX hUX hne α₀ S.CV S.hcV S.FV (S.belyiCU hcX UX hUX hne)
      (S.belyi_hcU hcX UX hUX hne) (S.belyiFU hcX UX hUX hne) (S.belyiJ hcX UX) S.isGalois
      (S.isPullback_belyiFU hcX UX hUX hne)⟩⟩

end CurvesJacobian.Cusp
