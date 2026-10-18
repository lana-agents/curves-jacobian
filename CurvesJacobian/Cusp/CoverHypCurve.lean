/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverGenus
import CurvesJacobian.Cusp.CoverCuspDegree

/-!
# A finite étale cover of a hyperbolic curve is a hyperbolic curve

Let `C` be a hyperbolic curve over a field `k` of characteristic zero (belyi's
`Belyi.Anabelian.HypCurve`: an open `U` with finite complement in a curve `X̄`, with
`2g - 2 + r > 0`), and `p : Y ⟶ U` finite étale with `Y` integral. Let `N` be the normalisation
of `X̄` in `Y`, `q : N ⟶ X̄`, and `k'` the constant field of `N`. We construct the hyperbolic
curve `CurvesJacobian.Cusp.coverHypCurve C p` over `k'`, with compactification `N` (over `k'`
via `CurvesJacobian.Cusp.toSpecConstField`) and open `q⁻¹ U`, and the isomorphism
`CurvesJacobian.Cusp.coverOpenIso : Y ≅ q⁻¹ U` compatible with `Y ⟶ N`.

Hyperbolicity: `g(X̄) ≤ g(N)` (`CurvesJacobian.Cusp.curveGenus_le_curveGenus_normalization`) and
`r(U) ≤ r(q⁻¹ U)` (`CurvesJacobian.Cusp.cuspDegree_le_cuspDegree_of_surjective`, `q` being
surjective). The complement of `q⁻¹ U` is finite since `q⁻¹ U` is a nonempty open of a curve.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi Belyi.Anabelian

universe u

namespace CurvesJacobian.Cusp

variable {k : Type u} [Field k] [CharZero k] (C : HypCurve k) {Y : Scheme.{u}}
  (p : Y ⟶ C.U) [IsFinite p] [Etale p]

/-- `N` is a curve over its constant field `k'`, via `toSpecConstField`. -/
lemma coverHypCurve_isCurve [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    letI := normalizationOver k p
    @IsCurveOver (constField k (p ≫ C.U.ι).normalization) _ (p ≫ C.U.ι).normalization
      ⟨toSpecConstField k _ (isIntegrallyClosed_sections_normalization (k := k) C.nonempty p)⟩ := by
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  letI := normalizationOver k p
  haveI := IsCurveOver.isIntegral k C.Xbar
  haveI : IsProper ((p ≫ C.U.ι).normalization ↘ Spec (.of k)) :=
    isProper_normalization (k := k) C.nonempty p
  haveI : SmoothOfRelativeDimension 1 ((p ≫ C.U.ι).normalization ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_normalization (k := k) C.nonempty p
  exact isCurveOver_constField k _ _ (ringKrullDim_stalk_normalization_le (k := k) C.nonempty p)

omit [CharZero k] [Etale p] in
/-- `q⁻¹ U` is nonempty: it contains the image of `Y`. -/
lemma coverHypCurve_nonempty [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    (((p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U : (p ≫ C.U.ι).normalization.Opens) :
      Set (p ≫ C.U.ι).normalization).Nonempty := by
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  refine ⟨(p ≫ C.U.ι).toNormalization y, ?_⟩
  change (p ≫ C.U.ι).fromNormalization ((p ≫ C.U.ι).toNormalization y) ∈ C.U
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization,
    Scheme.Hom.comp_apply]
  exact (p y).2

/-- The complement of `q⁻¹ U` is finite. -/
lemma coverHypCurve_cusps_finite [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    (((p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U : (p ≫ C.U.ι).normalization.Opens) :
      Set (p ≫ C.U.ι).normalization)ᶜ.Finite := by
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  letI := normalizationOver k p
  letI : (p ≫ C.U.ι).normalization.Over
      (Spec (.of (constField k (p ≫ C.U.ι).normalization))) :=
    ⟨toSpecConstField k _ (isIntegrallyClosed_sections_normalization (k := k) C.nonempty p)⟩
  haveI := coverHypCurve_isCurve C p
  haveI : CharZero (constField k (p ≫ C.U.ι).normalization) :=
    charZero_of_injective_algebraMap
      (algebraMap k (constField k (p ≫ C.U.ι).normalization)).injective
  exact finite_compl_of_isCurveOver (k := constField k (p ≫ C.U.ι).normalization) _ _
    (coverHypCurve_nonempty C p)

/-- **The cusp inequality** `r(U) ≤ r(q⁻¹ U)` for the explicit structure `toSpecConstField`. -/
theorem cuspDegree_le_cuspDegree_coverNormalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    letI := normalizationOver k p
    cuspDegree k C.Xbar C.U ≤
      @cuspDegree (constField k (p ≫ C.U.ι).normalization) _ (p ≫ C.U.ι).normalization
        ⟨toSpecConstField k _ (isIntegrallyClosed_sections_normalization (k := k) C.nonempty p)⟩
        ((p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U) := by
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  letI := normalizationOver k p
  have hN := isIntegrallyClosed_sections_normalization (k := k) C.nonempty p
  letI : (p ≫ C.U.ι).normalization.Over
      (Spec (.of (constField k (p ≫ C.U.ι).normalization))) := ⟨toSpecConstField k _ hN⟩
  haveI := coverHypCurve_isCurve C p
  exact cuspDegree_le_cuspDegree_of_surjective (p ≫ C.U.ι).fromNormalization
    (toSpecConstField_comp k _ hN) (surjective_fromNormalization (k := k) C.nonempty p) C.U
    C.nonempty

/-- **Hyperbolicity of the cover**: `2 < 2 g(N) + r(q⁻¹ U)`. -/
theorem coverHypCurve_hyperbolic [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    letI := normalizationOver k p
    letI : (p ≫ C.U.ι).normalization.Over
        (Spec (.of (constField k (p ≫ C.U.ι).normalization))) :=
      ⟨toSpecConstField k _ (isIntegrallyClosed_sections_normalization (k := k) C.nonempty p)⟩
    haveI := coverHypCurve_isCurve C p
    haveI := IsCurveOver.isIntegral (constField k (p ≫ C.U.ι).normalization)
      (p ≫ C.U.ι).normalization
    2 < 2 * Anabelian.curveGenus (constField k (p ≫ C.U.ι).normalization)
        (p ≫ C.U.ι).normalization +
      cuspDegree (constField k (p ≫ C.U.ι).normalization) (p ≫ C.U.ι).normalization
        ((p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U) := by
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  letI := normalizationOver k p
  have h1 := curveGenus_le_curveGenus_normalization (k := k) C.nonempty p
  have h2 := cuspDegree_le_cuspDegree_coverNormalization C p
  have h3 := C.hyperbolic
  exact Nat.lt_of_lt_of_le h3 (Nat.add_le_add (Nat.mul_le_mul_left 2 h1) h2)

/-- **The cover of a hyperbolic curve**: the hyperbolic curve `q⁻¹ U ⊆ N` over the constant
field `k'` of the normalisation `N` of `X̄` in `Y`. -/
noncomputable def coverHypCurve [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    letI := normalizationOver k p
    HypCurve (constField k (p ≫ C.U.ι).normalization) :=
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  letI := normalizationOver k p
  @HypCurve.mk _ _ (p ≫ C.U.ι).normalization
    ⟨toSpecConstField k _ (isIntegrallyClosed_sections_normalization (k := k) C.nonempty p)⟩
    (coverHypCurve_isCurve C p) ((p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U)
    (coverHypCurve_nonempty C p) (coverHypCurve_cusps_finite C p)
    (coverHypCurve_hyperbolic C p)

@[simp]
lemma coverHypCurve_Xbar [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    (coverHypCurve C p).Xbar = (p ≫ C.U.ι).normalization :=
  rfl

lemma coverHypCurve_over [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    letI := normalizationOver k p
    (coverHypCurve C p).over = (⟨toSpecConstField k (p ≫ C.U.ι).normalization
      (isIntegrallyClosed_sections_normalization (k := k) C.nonempty p)⟩ :
        (p ≫ C.U.ι).normalization.Over (Spec (.of (constField k (p ≫ C.U.ι).normalization)))) :=
  rfl

lemma coverHypCurve_U [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    (coverHypCurve C p).U = (p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U :=
  rfl

/-- **`Y` is the open `q⁻¹ U` of the cover**: the isomorphism `Y ≅ q⁻¹ U` through which
`toNormalization : Y ⟶ N` factors. -/
noncomputable def coverOpenIso [IsIntegral Y] : Y ≅ (coverHypCurve C p).U.toScheme :=
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  (isPullback_toNormalization p).isoIsPullback _ _
    (isPullback_morphismRestrict (p ≫ C.U.ι).fromNormalization C.U).flip

@[reassoc (attr := simp)]
lemma coverOpenIso_hom_ι [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
    (coverOpenIso C p).hom ≫ (coverHypCurve C p).U.ι = (p ≫ C.U.ι).toNormalization :=
  haveI := isLocallyNoetherian_of_isCurveOver k C.Xbar
  IsPullback.isoIsPullback_hom_fst _ _ _ _

end CurvesJacobian.Cusp
