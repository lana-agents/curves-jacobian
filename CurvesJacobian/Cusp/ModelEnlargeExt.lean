/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelEnlargeSetup
import CurvesJacobian.Cusp.ExtensionMap
import CurvesJacobian.Cusp.CoverCuspComap

/-!
# Enlarging a geometric model: the homomorphism `π₁ᵉᵗ(W) ↠ P'` (MR8 option (Q), step (Q-b))

In the setting of `CurvesJacobian.Cusp.ModelEnlargeSetup` (a geometric model `D`, a subgroup
`ι(Π_Y) ≤ P' ≤ N_A(ι(Π_Y))` of finite relative index, the finite group `G = autRing(P')`, the
cover `V = Spec R_{h'}` of the punctured line `L`, its quotient `W = V / G`, the extensions
`p₁ : E₁ = π₁ᵉᵗ(W) ↠ G` and `p₂ : P' ↠ G`, and `ψ : ker p₁ ↠ ker p₂`):

* `GeomModel.enlCoverAut_comp_enlJ`: the deck transformation `Spec (awayAut γ⁻¹)` of `V`
  (`γ = p₂ g`) and `F_g` on `Spec Γ(U_Y)` are intertwined by `j : V ⟶ Spec Γ(U_Y)`;
* `GeomModel.enlConj`: conjugation by `e₁ ∈ E₁` on `π₁ᵉᵗ(V, a)`, induced by the deck
  transformation `(coverAut (p₁ e₁)).hom.left` (`GeomModel.isConjInduced_enlConj`);
* **`GeomModel.exists_isExtLift_enl`** (compatibility of the outer actions): every `e₁ ∈ E₁` has
  a compatible lift `e₂ ∈ P'` (`CurvesJacobian.Cusp.IsExtLift`): both `ψ₀ ∘ conj(e₁)` and
  `conjPi g ∘ ψ₀` are induced by `j ≫ F_g`, so they differ by an inner automorphism `conj s` of
  `Π_Y`, and `e₂ = ι(s) g`;
* **`GeomModel.enlPhi : E₁ →ₜ* P'`** (`CurvesJacobian.Cusp.extMapCont`): surjective
  (`GeomModel.enlPhi_surjective`), over `G` (`GeomModel.enlP₂_enlPhi`), extending `ψ`
  (`GeomModel.enlPhi_apply_ker`), with kernel the image of `ker ψ` (`GeomModel.ker_enlPhi`);
* the quotient curve `Z₀ = GeomModel.enlZ0` (the hyperbolic curve `W` over its constant field,
  `CurvesJacobian.Cusp.lineQuotCurve`) with the embedding of the constant field induced by
  `a ≫ q`, and **`GeomModel.enlZ0PiEquiv : Π_{Z₀} ≃ₜ* E₁`**, induced by `Spec Γ(Z₀) ≅ W ⟶ L`
  (`GeomModel.isConjInduced_enlZ0PiEquiv`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp.GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A) (hDGC : RelIsomDGC.Exists D.M) {P' : Subgroup D.Nrm}
  (hrel : D.ιNHom.range.relIndex P' ≠ 0)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-! ### The deck transformations and the semilinear action -/

/-- **`j` intertwines the deck transformation `Spec (awayAut γ⁻¹)` of `V` (`γ = p₂ g`) with
`F_g`**: `Spec (awayAut γ⁻¹) ≫ j = j ≫ F_g` (`awayAut` restricts to `ρ` on `Γ(U_Y)`, and
`ρ γ⁻¹ = autRing g⁻¹ = F_g^*`). -/
theorem enlCoverAut_comp_enlJ (g : P') :
    (D.enlCoverAut hDGC hrel (D.enlP₂ hDGC hrel g)).hom.left ≫ D.enlJ hDGC hrel =
      D.enlJ hDGC hrel ≫ (D.semilinearAutOf hDGC g).hom := by
  have hF : (D.semilinearAutOf hDGC g).hom = Spec.map (CommRingCat.ofHom
      (D.autRing hDGC (g : D.Nrm)⁻¹ : Γ(D.Y.Xbar, D.Y.U) →+* Γ(D.Y.Xbar, D.Y.U))) := by
    rw [specMap_autRing, inv_inv]
    rfl
  have hρ : D.enlRho hDGC hrel (D.enlP₂ hDGC hrel g)⁻¹ = D.autRing hDGC (g : D.Nrm)⁻¹ := by
    rw [map_inv, map_inv]
    rfl
  have key : CommRingCat.ofHom (algebraMap Γ(D.Y.Xbar, D.Y.U) (D.enlRing hDGC hrel)) ≫
      CommRingCat.ofHom (awayAut (D.enlRho hDGC hrel) (D.enlRho_fix hDGC hrel)
        (quotLinePoly K (D.enlH hDGC hrel)) (D.enlP₂ hDGC hrel g)⁻¹ :
          D.enlRing hDGC hrel →+* D.enlRing hDGC hrel) =
      CommRingCat.ofHom (D.autRing hDGC (g : D.Nrm)⁻¹ :
          Γ(D.Y.Xbar, D.Y.U) →+* Γ(D.Y.Xbar, D.Y.U)) ≫
        CommRingCat.ofHom (algebraMap Γ(D.Y.Xbar, D.Y.U) (D.enlRing hDGC hrel)) := by
    ext x
    change awayAut (D.enlRho hDGC hrel) (D.enlRho_fix hDGC hrel)
        (quotLinePoly K (D.enlH hDGC hrel)) (D.enlP₂ hDGC hrel g)⁻¹ (algebraMap _ _ x) =
      algebraMap Γ(D.Y.Xbar, D.Y.U) (D.enlRing hDGC hrel) (D.autRing hDGC (g : D.Nrm)⁻¹ x)
    rw [awayAut_algebraMap, hρ]
  rw [hF, coverAut_hom_left, enlJ]
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map key).trans (Spec.map_comp _ _))

/-- **Conjugation by `e₁ ∈ E₁` on `π₁ᵉᵗ(V, a)`** (`CurvesJacobian.Cusp.coverAutConj`). -/
def enlConj (e₁ : D.enlE₁ hDGC hrel) :
    π₁ᵉᵗ(D.enlPt hDGC hrel) →ₜ* π₁ᵉᵗ(D.enlPt hDGC hrel) :=
  coverAutConj (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel) (e₁ : π₁ᵉᵗ(D.enlEta hDGC hrel))
    fun _ hs ↦ conj_mem_stabilizer (fiber (D.enlEta hDGC hrel))
      (coverPt (D.enlCover hDGC hrel) (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel))
      (map_qMap_coverPt _ _ _) (D.enlCoverAut_injective hDGC hrel) e₁.2 hs

/-- The defining property of `enlConj`: `f_* (c τ) = e₁ * f_* τ * e₁⁻¹`. -/
theorem fundamentalGroupMap_enlConj (e₁ : D.enlE₁ hDGC hrel) (τ : π₁ᵉᵗ(D.enlPt hDGC hrel)) :
    fundamentalGroupMap (D.enlCover hDGC hrel) (D.enlPt_spec hDGC hrel) (D.enlConj hDGC hrel e₁ τ) =
      (e₁ : π₁ᵉᵗ(D.enlEta hDGC hrel)) *
        fundamentalGroupMap (D.enlCover hDGC hrel) (D.enlPt_spec hDGC hrel) τ *
          (e₁ : π₁ᵉᵗ(D.enlEta hDGC hrel))⁻¹ :=
  fundamentalGroupMap_coverAutConj _ _ _ _ τ

/-- **Conjugation by `e₁` is induced by the deck transformation `coverAut (p₁ e₁)`**
(`CurvesJacobian.Cusp.isConjInduced_coverAutConj_stabQuot`). -/
theorem isConjInduced_enlConj (e₁ : D.enlE₁ hDGC hrel) :
    IsConjInduced (D.enlCoverAut hDGC hrel (D.enlP₁ hDGC hrel e₁)).hom.left
      (D.enlConj hDGC hrel e₁) :=
  isConjInduced_coverAutConj_stabQuot (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel)
    (D.enlCoverAut_injective hDGC hrel) (map_qMap_coverPt _ _ _) e₁

/-- `enlKerToV` intertwines conjugation in `E₁` with `enlConj`. -/
lemma enlKerToV_kerConj (e₁ : D.enlE₁ hDGC hrel) (n : (D.enlP₁ hDGC hrel).ker) :
    D.enlKerToV hDGC hrel (kerConj (D.enlP₁ hDGC hrel) e₁ n) =
      D.enlConj hDGC hrel e₁ (D.enlKerToV hDGC hrel n) := by
  apply fundamentalGroupMap_injective_of_isFiniteEtale' (D.enlCover hDGC hrel) (D.enlPt hDGC hrel)
    (D.enlPt_spec hDGC hrel)
  rw [fundamentalGroupMap_enlKerToV, fundamentalGroupMap_enlConj, fundamentalGroupMap_enlKerToV]
  rfl

/-! ### Compatibility of the outer actions -/

variable (hPP' : D.ιNHom.range ≤ P')

/-- **Compatibility of the outer actions (hcomp)**: every `e₁ ∈ E₁` has a compatible lift
`e₂ ∈ P'` over the same element of `G`. With `g ∈ P'`, `p₂ g = p₁ e₁`, both `ψ₀ ∘ conj(e₁)` and
`conjPi g ∘ ψ₀` are induced by `j ≫ F_g`, hence differ by `conj s`, `s ∈ Π_Y`; take
`e₂ = ι(s) g`. -/
theorem exists_isExtLift_enl (e₁ : D.enlE₁ hDGC hrel) :
    ∃ e₂ : P', IsExtLift (D.enlP₁ hDGC hrel) (D.enlP₂ hDGC hrel) (D.enlPsi hDGC hrel hPP') e₁
      e₂ := by
  obtain ⟨g, hg⟩ := D.enlP₂_surjective hDGC hrel (D.enlP₁ hDGC hrel e₁)
  have Hc : IsConjInduced (D.enlCoverAut hDGC hrel (D.enlP₂ hDGC hrel g)).hom.left
      (D.enlConj hDGC hrel e₁) := by
    rw [hg]
    exact D.isConjInduced_enlConj hDGC hrel e₁
  have H1 : IsConjInduced (D.enlJ hDGC hrel ≫ (D.semilinearAutOf hDGC g).hom)
      (D.enlPsi₀ hDGC hrel ∘ D.enlConj hDGC hrel e₁) :=
    (Hc.comp (D.isConjInduced_enlPsi₀ hDGC hrel)).congr_hom (D.enlCoverAut_comp_enlJ hDGC hrel g)
  have H2 : IsConjInduced (D.enlJ hDGC hrel ≫ (D.semilinearAutOf hDGC g).hom)
      (D.conjPi g ∘ D.enlPsi₀ hDGC hrel) :=
    (D.isConjInduced_enlPsi₀ hDGC hrel).comp (D.isConjInduced_semilinearAutOf hDGC g)
  obtain ⟨γ₂, hγ₂⟩ := H2
  obtain ⟨s, hs⟩ := (isConjInduced_iff_exists_conj _ γ₂ _).1 H1
  have hs' : ∀ τ, D.enlPsi₀ hDGC hrel (D.enlConj hDGC hrel e₁ τ) =
      s * D.conjPi g (D.enlPsi₀ hDGC hrel τ) * s⁻¹ := fun τ ↦
    (hs τ).trans (congrArg (fun x ↦ s * x * s⁻¹) (hγ₂ τ).symm)
  refine ⟨⟨D.ιN s, hPP' ⟨s, rfl⟩⟩ * g, ?_, fun n ↦ ?_⟩
  · rw [map_mul, D.enlP₂_ιN hDGC hrel hPP' s, one_mul, hg]
  · refine Subtype.ext (Subtype.ext ?_)
    have h1 : (((D.enlPsi hDGC hrel hPP' (kerConj (D.enlP₁ hDGC hrel) e₁ n) : P') : D.Nrm) :
        A.grp) = D.ι s * ((g : D.Nrm) : A.grp) *
          D.ι (D.enlPsi₀ hDGC hrel (D.enlKerToV hDGC hrel n)) * ((g : D.Nrm) : A.grp)⁻¹ *
            (D.ι s)⁻¹ := by
      refine (congrArg (fun τ ↦ D.ι (D.enlPsi₀ hDGC hrel τ))
        (D.enlKerToV_kerConj hDGC hrel e₁ n)).trans ?_
      refine (congrArg D.ι (hs' _)).trans ?_
      simp only [map_mul, map_inv, ι_conjPi]
      group
    refine h1.trans ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_enlPsi, coe_ιN]
    group

/-! ### The homomorphism `Φ : E₁ ↠ P'` -/

/-- **`Φ : π₁ᵉᵗ(W) = E₁ →ₜ* P'`**, the homomorphism of extensions of `G` extending `ψ`
(`CurvesJacobian.Cusp.extMapCont`). -/
def enlPhi : D.enlE₁ hDGC hrel →ₜ* P' :=
  extMapCont (D.center_ker_enlP₂ hDGC hrel hPP') (D.enlPsi_surjective hDGC hrel hPP')
    (D.exists_isExtLift_enl hDGC hrel hPP') (D.isOpen_ker_enlP₁ hDGC hrel)
    (D.continuous_enlPsi hDGC hrel hPP')

/-- **`Φ` is surjective.** -/
theorem enlPhi_surjective : Function.Surjective (D.enlPhi hDGC hrel hPP') :=
  extMapCont_surjective _ _ _ _ _ (D.enlP₁_surjective hDGC hrel)

/-- **`ker Φ` is the image of `ker ψ`.** -/
theorem ker_enlPhi : (D.enlPhi hDGC hrel hPP').toMonoidHom.ker =
    (D.enlPsi hDGC hrel hPP').ker.map (D.enlP₁ hDGC hrel).ker.subtype :=
  ker_extMapCont _ _ _ _ _

/-- **`Φ` extends `ψ`.** -/
theorem enlPhi_apply_ker (n : (D.enlP₁ hDGC hrel).ker) :
    D.enlPhi hDGC hrel hPP' n = D.enlPsi hDGC hrel hPP' n :=
  extMapCont_apply_ker _ _ _ _ _ n

/-- On `ker p₁ = π₁ᵉᵗ(V, a)`, `Φ` is `ι ∘ ψ₀`. -/
theorem coe_enlPhi_ker (n : (D.enlP₁ hDGC hrel).ker) :
    ((D.enlPhi hDGC hrel hPP' n : D.Nrm) : A.grp) =
      D.ι (D.enlPsi₀ hDGC hrel (D.enlKerToV hDGC hrel n)) := by
  rw [enlPhi_apply_ker]
  rfl

/-- **`Φ` lies over `G`**: `p₂ ∘ Φ = p₁`. -/
theorem enlP₂_enlPhi (e : D.enlE₁ hDGC hrel) :
    D.enlP₂ hDGC hrel (D.enlPhi hDGC hrel hPP' e) = D.enlP₁ hDGC hrel e :=
  apply_extMapCont _ _ _ _ _ e

/-- `p₂ ∘ Φ = p₁` as homomorphisms. -/
theorem enlP₂_comp_enlPhi :
    (D.enlP₂ hDGC hrel).comp (D.enlPhi hDGC hrel hPP').toMonoidHom = D.enlP₁ hDGC hrel :=
  MonoidHom.ext (D.enlP₂_enlPhi hDGC hrel hPP')

/-- **`Φ` is compatible with the conjugation actions on the kernels.** -/
theorem enlPhi_conj (e : D.enlE₁ hDGC hrel) (n : (D.enlP₁ hDGC hrel).ker) :
    (D.enlPsi hDGC hrel hPP' (kerConj (D.enlP₁ hDGC hrel) e n) : P') =
      D.enlPhi hDGC hrel hPP' e * D.enlPsi hDGC hrel hPP' n * (D.enlPhi hDGC hrel hPP' e)⁻¹ :=
  extMap_conj (D.center_ker_enlP₂ hDGC hrel hPP') (D.enlPsi_surjective hDGC hrel hPP')
    (D.exists_isExtLift_enl hDGC hrel hPP') e n

/-! ### The quotient curve `Z₀` and `Π_{Z₀} ≃ E₁` -/

/-- The quotient `W = V / G` (`CurvesJacobian.Cusp.lineQuot`). -/
abbrev enlW : Scheme.{u} :=
  lineQuot K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
    (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel) (D.enlRho_fix hDGC hrel)

/-- The finite étale map `W ⟶ Spec Γ(L)`. -/
abbrev enlWHom : D.enlW hDGC hrel ⟶ Spec Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U) :=
  lineQuotHom K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
    (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel) (D.enlRho_fix hDGC hrel)

/-- The quotient map `q : V ⟶ W`. -/
abbrev enlQ : Spec (.of (D.enlRing hDGC hrel)) ⟶ D.enlW hDGC hrel :=
  lineQuotMap K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
    (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel) (D.enlRho_fix hDGC hrel)

instance connectedSpace_enlW : ConnectedSpace (D.enlW hDGC hrel) :=
  connectedSpace_lineQuot K _ _ _ _ _ _ _ (D.transcendental_enlT hDGC hrel)

/-- The point `a ≫ q` of `W` lies over the base point of `L`. -/
lemma enlQuotPt_spec : (D.enlPt hDGC hrel ≫ D.enlQ hDGC hrel) ≫ D.enlWHom hDGC hrel =
    basePoint Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) ≫
      baseChangeSpec K Ω Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U) :=
  quotPt_spec (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel) (D.enlCoverAut hDGC hrel)

/-- The constant field `M₀` of the quotient curve. -/
abbrev enlM₀ : Type u := coverField (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) (D.enlWHom hDGC hrel)

/-- **The quotient curve `Z₀`**: `W` as a hyperbolic curve over its constant field
(`CurvesJacobian.Cusp.lineQuotCurve`). -/
abbrev enlZ0 : HypCurve (D.enlM₀ hDGC hrel) :=
  lineQuotCurve K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
    (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel) (D.enlRho_fix hDGC hrel)
    (D.transcendental_enlT hDGC hrel)

lemma enlZ0_cusp : ((D.enlZ0 hDGC hrel).U : Set (D.enlZ0 hDGC hrel).Xbar)ᶜ.Nonempty :=
  lineQuotCurve_cusp K _ _ _ _ _ _ _ _

/-- **The embedding `M₀ ⊆ Ω` induced by the point `a ≫ q` of `W`**
(`CurvesJacobian.Cusp.coverAlgebra`). -/
abbrev enlAlgebraM₀ : Algebra (D.enlM₀ hDGC hrel) Ω :=
  coverAlgebra Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) (D.enlWHom hDGC hrel)
    (D.enlPt hDGC hrel ≫ D.enlQ hDGC hrel)

lemma isAlgebraic_enlAlgebraM₀ :
    letI := D.enlAlgebraM₀ hDGC hrel
    Algebra.IsAlgebraic (D.enlM₀ hDGC hrel) Ω :=
  isAlgebraic_coverAlgebra Ω _ _ _ _ (D.enlQuotPt_spec hDGC hrel)

lemma isScalarTower_enlAlgebraM₀ :
    letI := D.enlAlgebraM₀ hDGC hrel
    IsScalarTower K (D.enlM₀ hDGC hrel) Ω :=
  isScalarTower_coverAlgebra Ω _ _ _ _ (D.enlQuotPt_spec hDGC hrel)

/-- **`Π_{Z₀} ≃ₜ* E₁ = π₁ᵉᵗ(W)`** (`CurvesJacobian.Cusp.coverCurvePiEquiv`). -/
def enlZ0PiEquiv :
    letI := D.enlAlgebraM₀ hDGC hrel
    haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
    (arithmeticExt Ω (D.enlZ0 hDGC hrel) (D.enlZ0_cusp hDGC hrel)).Pi ≃ₜ* D.enlE₁ hDGC hrel :=
  coverCurvePiEquiv Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) (D.enlWHom hDGC hrel)
    (D.enlPt hDGC hrel ≫ D.enlQ hDGC hrel) (D.enlQuotPt_spec hDGC hrel)

/-- **`Π_{Z₀} ≃ E₁ ⊆ π₁ᵉᵗ(L, η')` is induced by `Spec Γ(Z₀) ≅ W ⟶ Spec Γ(L)`.** -/
theorem isConjInduced_enlZ0PiEquiv :
    letI := D.enlAlgebraM₀ hDGC hrel
    haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
    IsConjInduced
      ((lineQuotCurveIso K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
        (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel)
        (D.enlRho_fix hDGC hrel) (D.transcendental_enlT hDGC hrel)).hom ≫ D.enlWHom hDGC hrel)
      (fun γ ↦ ((D.enlZ0PiEquiv hDGC hrel γ : D.enlE₁ hDGC hrel) : π₁ᵉᵗ(D.enlEta hDGC hrel))) :=
  letI := D.enlAlgebraM₀ hDGC hrel
  haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
  (isConjInduced_coverPiEquiv Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) (D.enlZ0 hDGC hrel)
    (D.enlZ0_cusp hDGC hrel) (D.enlWHom hDGC hrel) (D.enlPt hDGC hrel ≫ D.enlQ hDGC hrel)
    (D.enlQuotPt_spec hDGC hrel) _).congr_fun fun _ ↦ rfl

end CurvesJacobian.Cusp.GeomModel
