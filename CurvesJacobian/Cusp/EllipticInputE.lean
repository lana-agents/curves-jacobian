/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticChainE

/-!
# Elliptic data from a general elliptic input (MR8.7, round 30)

[AbsTopII] Example 3.2 (ii) and Corollary 3.3 (iii)
(`Topics in Absolute Anabelian Geometry II.txt` l.4381–4400, l.4459–4510): for an affine
hyperbolic curve `X = CX` over a number field `K`, a once-punctured elliptic curve `D = E ∖ {O}`
over a number field `M ⊇ K` with `M`-rational `E[2]`, a hyperbolic curve `V` over `M` and finite
étale maps `V ⟶ X` (over `Spec M ⟶ Spec K`) and `V ⟶ D` (over `Spec M`), the elliptic data
`ellipticDataOfInput` has `CQ = E ∖ {O}`, `CW = E ∖ E[2]`, `β = [2]`, the run of fillings
`E ∖ E[2] ⊆ ⋯ ⊆ E ∖ {O}` of `exists_runE`, and `FD : V ⟶ D'` the composite of `V ⟶ D` with the
identification `Spec Γ(E ∖ {O}) = Spec Γ(U_n)`. For `V = X = D` and identity maps this is
`ellipticDataE`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M] (CX : HypCurve K) (E : WeierstrassCurve M) [E.IsElliptic]

/-- **Elliptic data of a general elliptic input** ([AbsTopII] Example 3.2 (ii)): `D = E ∖ {O}`
(`E[2]` `M`-rational), `U = E ∖ E[2]`, `β = [2]`, `FV : V ⟶ X`, `FQ : V ⟶ D`, and
`FD = FQ ≫ (Spec Γ(E ∖ {O}) = Spec Γ(U_n))`. -/
def ellipticDataOfInput (hE : E.Ψ₂Sq.Splits) (CV : HypCurve M)
    (hcV : (CV.U : Set CV.Xbar)ᶜ.Nonempty) (FV : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CX.Xbar, CX.U))
    [IsFiniteEtale FV]
    (hFV : FV ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M)))
    (FQ : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U))
    [hQ : IsFiniteEtale FQ]
    (hFQ : FQ ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ((hypCurveX E).Xbar,
      (hypCurveX E).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap M M))) :
    EllipticData (M := M) CX where
  CQ := hypCurveX E
  hcQ := compl_XE_nonempty E
  CW := hypCurveV E
  hcW := compl_VE_nonempty₂ E
  n := runNE E hE
  UW := runUWE E hE
  hUW0 := (runSpecE E hE).1
  hleW := (runSpecE E hE).2.2.1
  hmonoW := (runSpecE E hE).2.2.2.2.1
  hcUW i := (compl_XE_nonempty E).mono (Set.compl_subset_compl.2 ((runSpecE E hE).2.2.2.1 i))
  hypW i := hyperbolic_of_le E ((runSpecE E hE).2.2.1 i) ((runSpecE E hE).2.2.2.1 i)
  xW := runXE E hE
  hxUW := (runSpecE E hE).2.2.2.2.2.1
  hxUW' := (runSpecE E hE).2.2.2.2.2.2.1
  hxW := (runSpecE E hE).2.2.2.2.2.2.2.1
  ratW := (runSpecE E hE).2.2.2.2.2.2.2.2
  CV := CV
  hcV := hcV
  FV := FV
  hFV := hFV
  FQ := FQ
  finFQ := hQ
  hFQ := hFQ
  β := coverXMorK E
  finβ := isFiniteEtale_coverXMorK E
  hβ := by
    change coverXMorK E ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(curveE E, XE E))) = _
    simp only [coverXMorK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ coverXHom_algebraMap E c
  FD := FQ ≫ eqToHom (congrArg (fun V : (curveE E).Opens ↦ Spec Γ(curveE E, V))
    (runSpecE E hE).2.1.symm)
  finFD := MorphismProperty.comp_mem _ _ _ hQ (isFiniteEtale_of_isIso₂ _)
  hFD := by
    have h := eqToHom_specΓ_algebraMap (K := M) (runSpecE E hE).2.1.symm
    rw [Category.assoc]
    erw [h]
    have e : Spec.map (CommRingCat.ofHom (algebraMap M M)) = 𝟙 _ := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rw [e, Category.comp_id, Category.comp_id]
    rw [e, Category.comp_id] at hFQ
    exact hFQ

end CurvesJacobian.Cusp
