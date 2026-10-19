/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FillAutStable
import CurvesJacobian.Cusp.GaloisDescentOpen
import CurvesJacobian.Cusp.SemilinearAut

/-!
# Descent of the candidate's open `U_Y ⊆ Y'` to `X` (MR8, round 27)

Let `C = (X̄_Y, U_Y)` be a hyperbolic curve with a cusp over a number field `M ⊇ K`, `U_Y ⊆ U'`
a filling with `C' = (X̄_Y, U')` hyperbolic with a cusp, and `q : Spec Γ(U') ⟶ Spec Γ(X)` a
finite étale Galois cover over `Spec K` (`hqK`, `hgal`) of the affine hyperbolic curve
`X = (X̄, U_X⁰)` over `K`. Assume the rel-isom-DGC over `M` (`hDGC`) and that every
automorphism `A` of `Π_{U'}` induced by a deck transformation of `q` lifts along
`fillPiHom : Π_{U_Y} ↠ Π_{U'}` (`hlift`). Then the open `Spec Γ(U_Y) ⊆ Spec Γ(U')` descends:
there are a nonempty open `U_X ⊆ U_X⁰` and a finite étale `Spec Γ(U_Y) ⟶ Spec Γ(U_X)` making
the restriction square cartesian (**`CurvesJacobian.Cusp.exists_descent_of_lift`**).

* `CurvesJacobian.Cusp.deckIso₂`: the scheme automorphism underlying a deck transformation.
* `CurvesJacobian.Cusp.isoPiAut₂`: the automorphism of `π₁ᵉᵗ(Y, x)` induced by an automorphism
  of a connected scheme `Y`, composed with a change of base point
  (`isConjInduced_isoPiAut₂`).

Proof: a deck transformation `σ'` of `q` lies over `Spec K`, hence over `Spec β` for a
`K`-automorphism `β` of `M` (`exists_algEquiv_of_comp_sK`); with `A := isoPiAut₂ σ'` and the
lift `ψ` from `hlift`, `exists_iso_specRes_comp_eq` shows that `σ'` preserves the image of
`Spec Γ(U_Y) ⟶ Spec Γ(U')`, which is `fromSpec⁻¹(U_Y)` (`opensRange_specMap_resAlg`), and
`exists_isPullback_of_stable` descends it.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

set_option backward.isDefEq.respectTransparency false

section Deck

variable {V X : Scheme.{u}} {q : V ⟶ X} [IsFiniteEtale q]

/-- The scheme automorphism of `V` underlying a deck transformation `σ` of `q : V ⟶ X`. -/
def deckIso₂ (σ : Aut (coverObj q)) : V ≅ V :=
  (Over.forget X).mapIso ((FiniteEtale.forget X).mapIso σ)

lemma deckIso₂_hom (σ : Aut (coverObj q)) : (deckIso₂ σ).hom = σ.hom.left :=
  rfl

lemma deckIso₂_hom_comp (σ : Aut (coverObj q)) : (deckIso₂ σ).hom ≫ q = q :=
  Over.w σ.hom.hom

end Deck

section IsoPi

variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (.of Ω) ⟶ Y) (e : Y ≅ Y)

/-- The automorphism of `π₁ᵉᵗ(Y, x)` induced by an automorphism `e` of `Y`, followed by a
change of base point `fiber (x ≫ e) ≅ fiber x`. -/
def isoPiAut₂ : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(x) :=
  continuousMulEquivOfBijective
    ((ContinuousMonoidHom.toContinuousMonoidHom (autContinuousMulEquivOfIso
      (nonempty_iso_of_fiberFunctor (fiber (x ≫ e.hom)) (fiber x)).some)).comp
        (fundamentalGroupMap e.hom rfl))
    ((autContinuousMulEquivOfIso
      (nonempty_iso_of_fiberFunctor (fiber (x ≫ e.hom)) (fiber x)).some).bijective.comp
        (fundamentalGroupMap_bijective_of_isIso e.hom rfl))

/-- `isoPiAut₂ x e` is induced by `e` up to a change of base point. -/
lemma isConjInduced_isoPiAut₂ : IsConjInduced e.hom (isoPiAut₂ x e) :=
  ⟨(nonempty_iso_of_fiberFunctor (fiber (x ≫ e.hom)) (fiber x)).some, fun _ ↦ rfl⟩

end IsoPi

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [Algebra.IsAlgebraic K Ω] in
/-- **Descent of the candidate's open `U_Y ⊆ Y'` to `X`.** For a finite étale Galois
`q : Spec Γ(U') ⟶ Spec Γ(X)` over `Spec K` such that every automorphism of `Π_{U'}` induced by
a deck transformation of `q` lifts along `fillPiHom : Π_{U_Y} ↠ Π_{U'}` (`hlift`), assuming the
rel-isom-DGC over `M`, there are a nonempty open `U_X ⊆ U_X⁰` and a finite étale
`FU : Spec Γ(U_Y) ⟶ Spec Γ(U_X)` with `Spec Γ(U_Y) = Spec Γ(U') ×_{Spec Γ(U_X⁰)} Spec Γ(U_X)`. -/
theorem exists_descent_of_lift {M : Type u} [Field M] [NumberField M] [Algebra K M]
    [Algebra M Ω] [IsScalarTower K M Ω] [FiniteDimensional K M] [Algebra.IsAlgebraic M Ω]
    (CX : HypCurve K) (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)
    (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens}
    (h : C.U ≤ U') (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
    (hyp : haveI := IsCurveOver.isIntegral M C.Xbar
      2 < 2 * Anabelian.curveGenus M C.Xbar + cuspDegree M C.Xbar U')
    (hDGC : RelIsomDGC M)
    (q : Spec Γ(C.Xbar, U') ⟶ Spec Γ(CX.Xbar, CX.U)) [IsFiniteEtale q]
    (hqK : q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, U'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M)))
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj q))
    (hlift : ∀ (σ' : Spec Γ(C.Xbar, U') ≅ Spec Γ(C.Xbar, U')), σ'.hom ≫ q = q →
      ∀ (A : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) ≃ₜ*
        π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U'))),
        IsConjInduced σ'.hom A →
        ∃ ψ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) ≃ₜ*
          π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)),
          ∀ s, fillPiHom Ω C hc h hc' hyp (ψ s) = A (fillPiHom Ω C hc h hc' hyp s)) :
    ∃ (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (_ : (UX : Set CX.Xbar).Nonempty)
      (FU : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(CX.Xbar, UX)) (_ : IsFiniteEtale FU),
      IsPullback (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom)) FU q
        (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)) := by
  haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  haveI : IsIntegral (Spec (CommRingCat.of Γ(C.Xbar, U'))) :=
    isIntegral_specSections (fillCurve C h hyp) hc'
  have hU' : IsAffineOpen U' := isAffineOpen_U (fillCurve C h hyp) hc'
  have hU : IsAffineOpen C.U := isAffineOpen_U C hc
  haveI := isOpenImmersion_specMap_resAlg M hU' hU h
  have hr : (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom)).opensRange =
      hU'.fromSpec ⁻¹ᵁ C.U := opensRange_specMap_resAlg M hU' hU h
  have e1 : sKU (fillCurve C h hyp) ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) := hqK.symm
  have hstab : ∀ σ : Aut (coverObj q), ∀ z ∈ (isAffineOpen_U (fillCurve C h hyp) hc').fromSpec
      ⁻¹ᵁ C.U, σ.hom.left z ∈ (isAffineOpen_U (fillCurve C h hyp) hc').fromSpec ⁻¹ᵁ C.U := by
    intro σ z hz
    have h2 : (deckIso₂ σ).hom ≫ q ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K Γ(CX.Xbar, CX.U))) =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) := by
      rw [← Category.assoc, deckIso₂_hom_comp]
    have hK : (deckIso₂ σ).hom ≫ sKU (fillCurve C h hyp) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M)) =
        sKU (fillCurve C h hyp) ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) :=
      (congrArg ((deckIso₂ σ).hom ≫ ·) e1).trans (h2.trans e1.symm)
    obtain ⟨β, hβ⟩ := exists_algEquiv_of_comp_sK (K := K) (fillCurve C h hyp) (deckIso₂ σ) hK
    obtain ⟨ψ, hψ⟩ := hlift (deckIso₂ σ) (deckIso₂_hom_comp σ)
      (isoPiAut₂ (basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U'))
        (deckIso₂ σ))
      (isConjInduced_isoPiAut₂ _ _)
    obtain ⟨G, hG⟩ := exists_iso_specRes_comp_eq Ω C hc h hc' hyp hDGC β.toRingEquiv
      (deckIso₂ σ) hβ _ (isConjInduced_isoPiAut₂ _ _) ψ hψ
    have hz' : z ∈ (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom)).opensRange := by
      rw [hr]
      exact hz
    obtain ⟨y, rfl⟩ := hz'
    have e2 : (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom) ≫ (deckIso₂ σ).hom) y =
        (G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom)) y :=
      congrArg (fun f ↦ f y) hG
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e2
    have hmem : σ.hom.left (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom) y) ∈
        (Spec.map (CommRingCat.ofHom (resAlg M h).toRingHom)).opensRange :=
      ⟨G.hom y, e2.symm⟩
    rw [hr] at hmem
    exact hmem
  obtain ⟨UX, hUX, hne, -, FU, hFU, hpb⟩ := exists_isPullback_of_stable (CV := fillCurve C h hyp)
    hcX hc' q C.U h C.nonempty hgal hstab
  exact ⟨UX, hUX, hne, FU, hFU, hpb⟩

end CurvesJacobian.Cusp
