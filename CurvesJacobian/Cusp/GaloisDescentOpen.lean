/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GaloisFibreTransitive
import CurvesJacobian.Cusp.Cor37bBelyi

/-!
# Descending a Galois-stable open along a Galois cover

Let `q : V ⟶ X` be a finite étale Galois cover (`coverObj q` Galois in `FiniteEtale X`) of a
connected scheme `X`, and `W₀ ⊆ V` an open stable under all deck transformations. Then
`W₀ = q⁻¹(T)` for the open `T = X ∖ q(V ∖ W₀)` (`descOpens₂`, `preimage_descOpens₂`): `q` is
finite, hence closed, and the deck group acts transitively on the fibres of `q`
(`exists_aut_apply_eq_of_isGalois`).

For affine hyperbolic curves `X = (X̄, U_X⁰)`, `V = (V̄, V⁰)` with cusps, a finite étale Galois
`q : Spec Γ(V⁰) ⟶ Spec Γ(U_X⁰)` and a nonempty open `W ⊆ V⁰` whose preimage
`W₀ = fromSpec⁻¹(W)` in `Spec Γ(V⁰)` is deck-stable, this gives a nonempty open `U_X ⊆ U_X⁰`
with `q⁻¹(fromSpec⁻¹(U_X)) = W₀` (`exists_open_preimage_eq_of_stable`), and the square
```
Spec Γ(W)   --res--> Spec Γ(V⁰)
    | descFU            | q
Spec Γ(U_X) --res--> Spec Γ(U_X⁰)
```
is cartesian with `descFU` finite étale (`isPullback_descFU`, `isFiniteEtale_descFU`;
packaged as `exists_isPullback_of_stable`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi.Anabelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section General

variable {X V : Scheme.{u}} (q : V ⟶ X) [IsFiniteEtale q] (W₀ : V.Opens)

/-- The open `X ∖ q(V ∖ W₀)` (open since the finite morphism `q` is closed). -/
def descOpens₂ : X.Opens :=
  ⟨(q '' (W₀ : Set V)ᶜ)ᶜ, (q.isClosedMap _ W₀.isOpen.isClosed_compl).isOpen_compl⟩

/-- **A deck-stable open is the preimage of its descent.** -/
theorem preimage_descOpens₂ [ConnectedSpace X] [IsGalois (coverObj q)]
    (hstab : ∀ σ : Aut (coverObj q), ∀ z ∈ W₀, σ.hom.left z ∈ W₀) :
    q ⁻¹ᵁ descOpens₂ q W₀ = W₀ := by
  ext z
  change q z ∉ q '' (W₀ : Set V)ᶜ ↔ z ∈ W₀
  constructor
  · intro h
    by_contra hz
    exact h ⟨z, hz, rfl⟩
  · rintro hz ⟨w, hw, hwz⟩
    obtain ⟨σ, hσ⟩ := exists_aut_apply_eq_of_isGalois q z w hwz.symm
    exact hw (hσ ▸ hstab σ z hz)

end General

variable {K M : Type u} [Field K] [NumberField K] [Field M] [NumberField M]
  {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)
  {CV : HypCurve M} (hcV : (CV.U : Set CV.Xbar)ᶜ.Nonempty)
  (q : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CX.Xbar, CX.U)) [IsFiniteEtale q]
  (W : CV.Xbar.Opens) (hW : W ≤ CV.U) (hWne : (W : Set CV.Xbar).Nonempty)

include hW hWne in
/-- **Descent of a Galois-stable open.** For a Galois `q : Spec Γ(V⁰) ⟶ Spec Γ(U_X⁰)` and a
nonempty open `W ⊆ V⁰` with deck-stable preimage `W₀` in `Spec Γ(V⁰)`, there is a nonempty open
`U_X ⊆ U_X⁰` with `q⁻¹(fromSpec⁻¹(U_X)) = W₀`. -/
theorem exists_open_preimage_eq_of_stable
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj q))
    (hstab : ∀ σ : Aut (coverObj q), ∀ z ∈ (isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W,
      σ.hom.left z ∈ (isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W) :
    ∃ UX : CX.Xbar.Opens, UX ≤ CX.U ∧ (UX : Set CX.Xbar).Nonempty ∧
      q ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX) =
        (isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W := by
  haveI := isIntegral_specSections CX hcX
  haveI := hgal
  have hpre := preimage_descOpens₂ q ((isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W) hstab
  refine ⟨(isAffineOpen_U CX hcX).fromSpec ''ᵁ descOpens₂ q
    ((isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W), ?_, ?_, ?_⟩
  · refine (Scheme.Hom.image_le_opensRange _ _).trans ?_
    rw [IsAffineOpen.opensRange_fromSpec]
  · obtain ⟨x, hx⟩ := hWne
    have hxr : x ∈ Set.range (isAffineOpen_U CV hcV).fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      exact hW hx
    obtain ⟨y, rfl⟩ := hxr
    have hy : y ∈ q ⁻¹ᵁ descOpens₂ q ((isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W) := by
      rw [hpre]
      exact hx
    exact ⟨_, q y, hy, rfl⟩
  · rw [Scheme.Hom.preimage_image_eq]
    exact hpre

section Square

variable (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)

/-- `Spec Γ(W) ⟶ Spec Γ(V⁰)`. -/
abbrev descJ : Spec Γ(CV.Xbar, W) ⟶ Spec Γ(CV.Xbar, CV.U) :=
  Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)

include hcV hW hWne in
lemma isAffineOpen_descW : IsAffineOpen W :=
  isAffineOpen_U (subCurve CV W hW hWne) (compl_nonempty_of_le hW hcV)

include hcX hUX hne in
lemma isAffineOpen_descUX : IsAffineOpen UX :=
  isAffineOpen_U (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)

include hcV hWne in
lemma isOpenImmersion_descJ : IsOpenImmersion (descJ W hW) :=
  isOpenImmersion_specMap_resAlg M (isAffineOpen_U CV hcV) (isAffineOpen_descW hcV W hW hWne) hW

include hcX hne in
lemma isOpenImmersion_descJX : IsOpenImmersion (belyiJX UX hUX) :=
  isOpenImmersion_specMap_resAlg K (isAffineOpen_U CX hcX) (isAffineOpen_descUX hcX UX hUX hne)
    hUX

variable (hpre : q ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX) =
  (isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W)

omit [IsFiniteEtale q] in
include hpre in
/-- The images of the two open immersions correspond under `q`. -/
lemma opensRange_descJ :
    haveI := isOpenImmersion_descJX hcX UX hUX hne
    haveI := isOpenImmersion_descJ hcV W hW hWne
    (descJ W hW).opensRange = q ⁻¹ᵁ (belyiJX UX hUX).opensRange := by
  haveI := isOpenImmersion_descJX hcX UX hUX hne
  haveI := isOpenImmersion_descJ hcV W hW hWne
  rw [opensRange_specMap_resAlg M (isAffineOpen_U CV hcV) (isAffineOpen_descW hcV W hW hWne) hW,
    opensRange_specMap_resAlg K (isAffineOpen_U CX hcX) (isAffineOpen_descUX hcX UX hUX hne) hUX]
  exact hpre.symm

/-- **The descended cover `Spec Γ(W) ⟶ Spec Γ(U_X)`** (`W = V⁰ ×_{U_X⁰} U_X`). -/
def descFU : Spec Γ(CV.Xbar, W) ⟶ Spec Γ(CX.Xbar, UX) :=
  haveI := isOpenImmersion_descJX hcX UX hUX hne
  haveI := isOpenImmersion_descJ hcV W hW hWne
  ((descJ W hW).isoOpensRange ≪≫
    Scheme.isoOfEq _ (opensRange_descJ hcX hcV q W hW hWne UX hUX hne hpre)).hom ≫
    (q ∣_ (belyiJX UX hUX).opensRange) ≫ (belyiJX UX hUX).isoOpensRange.inv

omit [IsFiniteEtale q] in
/-- **The square `Spec Γ(W) = Spec Γ(V⁰) ×_{Spec Γ(U_X⁰)} Spec Γ(U_X)` is cartesian.** -/
theorem isPullback_descFU :
    IsPullback (descJ W hW) (descFU hcX hcV q W hW hWne UX hUX hne hpre) q (belyiJX UX hUX) := by
  haveI := isOpenImmersion_descJX hcX UX hUX hne
  haveI := isOpenImmersion_descJ hcV W hW hWne
  refine (isPullback_morphismRestrict q (belyiJX UX hUX).opensRange).flip.of_iso
    ((descJ W hW).isoOpensRange ≪≫
      Scheme.isoOfEq _ (opensRange_descJ hcX hcV q W hW hWne UX hUX hne hpre)).symm (Iso.refl _)
    (belyiJX UX hUX).isoOpensRange.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoOpensRange_hom_ι]
  · rw [Iso.symm_hom, Iso.symm_hom, descFU, Iso.inv_hom_id_assoc]
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Scheme.Hom.isoOpensRange_inv_comp]

instance isFiniteEtale_descFU : IsFiniteEtale (descFU hcX hcV q W hW hWne UX hUX hne hpre) :=
  MorphismProperty.of_isPullback (P := @IsFiniteEtale)
    (isPullback_descFU hcX hcV q W hW hWne UX hUX hne hpre) inferInstance

end Square

include hWne in
/-- **Descent of a Galois-stable open, with the cartesian square.** For a Galois
`q : Spec Γ(V⁰) ⟶ Spec Γ(U_X⁰)` and a nonempty open `W ⊆ V⁰` with deck-stable preimage in
`Spec Γ(V⁰)`, there are a nonempty open `U_X ⊆ U_X⁰` with `q⁻¹(fromSpec⁻¹(U_X)) = fromSpec⁻¹(W)`
and a finite étale `FU : Spec Γ(W) ⟶ Spec Γ(U_X)` making the restriction square cartesian. -/
theorem exists_isPullback_of_stable
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj q))
    (hstab : ∀ σ : Aut (coverObj q), ∀ z ∈ (isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W,
      σ.hom.left z ∈ (isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W) :
    ∃ (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (_ : (UX : Set CX.Xbar).Nonempty)
      (_ : q ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX) =
        (isAffineOpen_U CV hcV).fromSpec ⁻¹ᵁ W)
      (FU : Spec Γ(CV.Xbar, W) ⟶ Spec Γ(CX.Xbar, UX)) (_ : IsFiniteEtale FU),
      IsPullback (Spec.map (CommRingCat.ofHom (resAlg M hW).toRingHom)) FU q
        (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)) := by
  obtain ⟨UX, hUX, hne, hpre⟩ :=
    exists_open_preimage_eq_of_stable hcX hcV q W hW hWne hgal hstab
  exact ⟨UX, hUX, hne, hpre, descFU hcX hcV q W hW hWne UX hUX hne hpre, inferInstance,
    isPullback_descFU hcX hcV q W hW hWne UX hUX hne hpre⟩

end CurvesJacobian.Cusp
