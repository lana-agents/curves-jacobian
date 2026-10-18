/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.BelyiCoordinate
import Belyi.Converse.DefinableOfBelyi

/-!
# Models of a complete curve from a model of its affine part

Let `K / k₀` be an extension of fields of characteristic zero, `X` a curve over `K` and
`f : X ⟶ ℙ¹_K` a finite morphism over `K` with `f(η) ≠ ∞`, so that `X ∖ f⁻¹(∞) = Spec B` for the
finite `K[t]`-algebra `B = Γ(X ×_{ℙ¹} 𝔸¹)` (`Belyi.lineCoverRing`). Suppose `B` has a model over
`k₀`: a `k₀[t]`-algebra `B₀` with `e : K ⊗[k₀] B₀ ≃ₐ[K] B` compatible with `k₀[t] → K[t]`. Then
`X` is the base change of the relative normalisation `X₀` of `ℙ¹_{k₀}` in
`y₀ : Spec B₀ ⟶ 𝔸¹_{k₀} ⊆ ℙ¹_{k₀}`:

  `X ≅ X₀ ×_{k₀} K` over `K`

(`CurvesJacobian.exists_iso_pullback_normalization_lineCover`). The proof is the assembly of
belyi's `Belyi.Converse.definableOver_of_isBelyiMap_of_comp_eq` with the affine line
`𝔸¹ = D₊(X₁)` in place of the thrice-punctured line:
`X ≅ norm(Spec B ⟶ ℙ¹_K)` (`Belyi.isIso_normalizationDesc_of_isCurveOver`),
`Spec B ⟶ ℙ¹_K` is the base change of `y₀` (`CurvesJacobian.isPullback_lineCoverModel_P1`), and
normalisation commutes with base change along `k₀ ⊆ K`
(`Belyi.isIso_normalizationPullback_specAlgebraMap`).

## Main results

* `CurvesJacobian.isPullback_lineι_mapOfAlgebra`: `𝔸¹_K = 𝔸¹_{k₀} ×_{ℙ¹_{k₀}} ℙ¹_K`.
* `CurvesJacobian.isPushout_polynomial_of_tensorEquiv`: `B = K[t] ⊗_{k₀[t]} B₀`.
* `CurvesJacobian.exists_iso_pullback_normalization_lineCover`: `X ≅ X₀ ×_{k₀} K`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MvPolynomial TensorProduct Belyi

namespace CurvesJacobian

open scoped P1

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

noncomputable section

/-! ### The affine line and base change -/

section Line

variable (k : Type u) [CommRing k]

/-- The image of `𝔸¹ ⟶ ℙ¹` is `D₊(X₁)`. -/
lemma opensRange_lineι : (lineι k).opensRange = Proj.basicOpen (P1Grading k) (X 1) := by
  haveI : IsIso (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom) :=
    (P1.awayChartEquivOne k).toRingEquiv.toCommRingCatIso.isIso_hom
  change (Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom) ≫
    Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]

/-- The affine-line charts commute with the base-change morphism `ℙ¹_K ⟶ ℙ¹_{k₀}`. -/
@[reassoc]
lemma lineι_comp_mapOfAlgebra :
    lineι K ≫ P1.mapOfAlgebra k₀ K =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ K))) ≫ lineι k₀ := by
  have h := P1.awayι_comp_mapOfAlgebra k₀ K 1
  have hr : Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne K).toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (P1.chartMap k₀ K 1)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ K))) ≫
        Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k₀).toRingEquiv.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun q ↦ P1.chartMap_naturality_one k₀ K q
  change Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne K).toRingEquiv.toRingHom) ≫
      (Proj.awayι (P1Grading K) (X 1) (P1.X_mem_P1Grading K 1) one_pos ≫
        P1.mapOfAlgebra k₀ K) =
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ K))) ≫
      (Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k₀).toRingEquiv.toRingHom) ≫
        Proj.awayι (P1Grading k₀) (X 1) (P1.X_mem_P1Grading k₀ 1) one_pos)
  rw [h]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Proj.awayι (P1Grading k₀) (X 1) (P1.X_mem_P1Grading k₀ 1) one_pos) hr).trans
      (Category.assoc _ _ _))

/-- The preimage of `𝔸¹_{k₀}` under `ℙ¹_K ⟶ ℙ¹_{k₀}` is `𝔸¹_K`. -/
lemma mapOfAlgebra_preimage_opensRange_lineι :
    P1.mapOfAlgebra k₀ K ⁻¹ᵁ (lineι k₀).opensRange = (lineι K).opensRange := by
  rw [opensRange_lineι, opensRange_lineι]
  exact (Proj.map_preimage_basicOpen _ _ _).trans (by rw [P1.gradedMap_X])

/-- **`𝔸¹_K = 𝔸¹_{k₀} ×_{ℙ¹_{k₀}} ℙ¹_K`.** -/
theorem isPullback_lineι_mapOfAlgebra :
    IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ K))))
      (lineι K) (lineι k₀) (P1.mapOfAlgebra k₀ K) :=
  IsOpenImmersion.isPullback _ _ _ _ (lineι_comp_mapOfAlgebra k₀ K)
    (mapOfAlgebra_preimage_opensRange_lineι k₀ K)

end Line

/-! ### Base change of covers of the affine line -/

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
  {B₀ B : Type u} [CommRing B₀] [CommRing B] [Algebra (Polynomial k₀) B₀]
  [Algebra (Polynomial K) B]

/-- **From a tensor-product description to the pushout square.** If
`e : K ⊗[k₀] B₀ ≃ₐ[K] B` is compatible with `k₀[t] → K[t]`, then `B = K[t] ⊗_{k₀[t]} B₀`. -/
theorem isPushout_polynomial_of_tensorEquiv [Algebra k₀ B₀] [IsScalarTower k₀ (Polynomial k₀) B₀]
    [Algebra K B] [IsScalarTower K (Polynomial K) B] (e : K ⊗[k₀] B₀ ≃ₐ[K] B)
    (he : ∀ r : Polynomial k₀, e (1 ⊗ₜ algebraMap (Polynomial k₀) B₀ r) =
      algebraMap (Polynomial K) B (Polynomial.map (algebraMap k₀ K) r)) :
    IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ K)))
      (CommRingCat.ofHom (algebraMap (Polynomial k₀) B₀))
      (CommRingCat.ofHom (algebraMap (Polynomial K) B))
      (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := k₀) (A := K) (B := B₀)).toRingHom)) := by
  set φ : B₀ →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := k₀) (A := K) (B := B₀)).toRingHom with hφ
  have hpoly : Polynomial.mapRingHom (algebraMap k₀ K) =
      algebraMap (Polynomial k₀) (Polynomial K) := rfl
  rw [hpoly]
  letI : Algebra B₀ B := φ.toAlgebra
  letI : Algebra (Polynomial k₀) B :=
    ((algebraMap (Polynomial K) B).comp (algebraMap (Polynomial k₀) (Polynomial K))).toAlgebra
  letI : Algebra k₀ B := ((algebraMap K B).comp (algebraMap k₀ K)).toAlgebra
  haveI : IsScalarTower (Polynomial k₀) (Polynomial K) B :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (Polynomial k₀) B₀ B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = e (1 ⊗ₜ algebraMap (Polynomial k₀) B₀ r)
      rw [he]
      rfl
  haveI : IsScalarTower k₀ K B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k₀ B₀ B := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = e (1 ⊗ₜ algebraMap k₀ B₀ c)
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply k₀ K (K ⊗[k₀] B₀),
      AlgEquiv.commutes]
    rfl
  haveI : IsScalarTower k₀ (Polynomial K) B := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change algebraMap K B (algebraMap k₀ K c) = _
    rw [IsScalarTower.algebraMap_apply k₀ K (Polynomial K),
      ← IsScalarTower.algebraMap_apply K (Polynomial K) B]
  -- `B = K ⊗[k₀] B₀`
  haveI h1 : Algebra.IsPushout k₀ K B₀ B := by
    rw [Algebra.isPushout_iff]
    exact IsBaseChange.of_equiv e.toLinearEquiv fun _ ↦ rfl
  haveI h1' := h1.symm
  haveI h2 : Algebra.IsPushout (Polynomial k₀) B₀ (Polynomial K) B :=
    (Algebra.IsPushout.comp_iff k₀ (Polynomial k₀) K (Polynomial K)).mp h1'
  haveI := h2.symm
  exact CommRingCat.isPushout_of_isPushout (Polynomial k₀) (Polynomial K) B₀ B

/-- **Base change of a cover of the affine line, over `ℙ¹`.** If `B = K[t] ⊗_{k₀[t]} B₀`, then
`Spec B ⟶ ℙ¹_K` is the base change of `Spec B₀ ⟶ ℙ¹_{k₀}` along `ℙ¹_K ⟶ ℙ¹_{k₀}`. -/
theorem isPullback_lineCoverModel_P1 (φ : B₀ →+* B)
    (hB : IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ K)))
      (CommRingCat.ofHom (algebraMap (Polynomial k₀) B₀))
      (CommRingCat.ofHom (algebraMap (Polynomial K) B)) (CommRingCat.ofHom φ)) :
    IsPullback (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B)) ≫ lineι K)
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) B₀)) ≫ lineι k₀)
      (P1.mapOfAlgebra k₀ K) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ hB).flip.paste_vert
    (isPullback_lineι_mapOfAlgebra k₀ K)

end BaseChange

/-! ### The model of the complete curve -/

section Model

variable {k₀ K : Type u} [Field k₀] [CharZero k₀] [Field K] [CharZero K] [Algebra k₀ K]

omit [CharZero K] in
/-- The affine part `X ∖ f⁻¹(∞)` is dense if `f(η) ≠ ∞`. -/
lemma denseRange_lineCover_fst {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ P1 K)
    (hη : f.base (genericPoint X) ≠ P1.infty K) :
    DenseRange (pullback.fst f (lineι K)).base := by
  have hmem : genericPoint X ∈ Set.range (pullback.fst f (lineι K)).base := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact (mem_range_lineι_iff _).2 hη
  refine denseRange_iff_closure_range.mpr (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr hmem)

/-- **The model of a complete curve.** Let `X` be a curve over `K`, `f : X ⟶ ℙ¹_K` finite over
`K` with `f(η) ≠ ∞`, and `(B₀, e)` a model over `k₀` of the affine part `B = Γ(X ×_{ℙ¹} 𝔸¹)`,
compatible with `k₀[t] → K[t]`. Then `X ≅ X₀ ×_{k₀} K` over `K`, where `X₀` is the relative
normalisation of `ℙ¹_{k₀}` in `y₀ : Spec B₀ ⟶ 𝔸¹_{k₀} ⊆ ℙ¹_{k₀}`. -/
theorem exists_iso_pullback_normalization_lineCover {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X] [IsIntegral X] (f : X ⟶ P1 K)
    [IsFinite f] (hfK : f ≫ (P1 K ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K))
    (hη : f.base (genericPoint X) ≠ P1.infty K)
    {B₀ : Type u} [CommRing B₀] [Algebra (Polynomial k₀) B₀] [Algebra k₀ B₀]
    [IsScalarTower k₀ (Polynomial k₀) B₀] (e : K ⊗[k₀] B₀ ≃ₐ[K] lineCoverRing f)
    (he : ∀ r : Polynomial k₀, e (1 ⊗ₜ algebraMap (Polynomial k₀) B₀ r) =
      algebraMap (Polynomial K) (lineCoverRing f) (Polynomial.map (algebraMap k₀ K) r)) :
    ∃ E : X ≅ pullback ((Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) B₀)) ≫
        lineι k₀).fromNormalization ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)))
        (specAlgebraMap k₀ K),
      E.hom ≫ pullback.snd _ _ = X ↘ Spec (CommRingCat.of K) := by
  haveI := isAffine_lineCover (f := f)
  have hP1 := isPullback_lineCoverModel_P1 _ (isPushout_polynomial_of_tensorEquiv e he)
  set y₀ : Spec (CommRingCat.of B₀) ⟶ P1 k₀ :=
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) B₀)) ≫ lineι k₀
  set g := pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)
  have hP := hP1.of_iso (Iso.refl _) (Iso.refl _) (asIso (P1.toPullback k₀ K)) (Iso.refl _)
    (snd' := (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (lineCoverRing f))) ≫
      lineι K) ≫ P1.toPullback k₀ K) (f' := y₀) (g' := g)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (by simp) (by simp [y₀])
    (by simp [g])
  let a : lineCover f ≅ pullback y₀ g := (lineCover f).isoSpec ≪≫ hP.isoPullback
  have ha : a.hom ≫ pullback.snd y₀ g =
      (pullback.fst f (lineι K) ≫ f) ≫ P1.toPullback k₀ K := by
    simp only [a, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [← Category.assoc (Scheme.isoSpec _).hom, ← Category.assoc ((Scheme.isoSpec _).hom ≫ _),
      lineCover_isoSpec_hom_comp, pullback.condition_assoc, Category.assoc]
  haveI := quasiCompact_of_isCurveOver K X (pullback.fst f (lineι K))
  haveI := isIso_normalizationDesc_of_isCurveOver K X f (pullback.fst f (lineι K))
    (denseRange_lineCover_fst f hη)
  haveI := isIso_normalizationPullback_specAlgebraMap k₀ K (P1 k₀ ↘ Spec (CommRingCat.of k₀)) y₀
  let E : X ≅ pullback (y₀.fromNormalization ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)))
      (specAlgebraMap k₀ K) :=
    (asIso ((pullback.fst f (lineι K) ≫ f).normalizationDesc
      (pullback.fst f (lineι K)) f rfl)).symm ≪≫
    Converse.normalizationIsoOfArrowIso a (asIso (P1.toPullback k₀ K)) ha ≪≫
    asIso (y₀.normalizationPullback g) ≪≫ pullbackRightPullbackFstIso _ _ _
  refine ⟨E, ?_⟩
  simp only [E, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
  erw [pullbackRightPullbackFstIso_hom_snd]
  rw [Scheme.Hom.normalizationPullback_snd_assoc y₀ g,
    Converse.normalizationIsoOfArrowIso_hom_fromNormalization_assoc, asIso_hom, P1.toPullback_snd,
    IsIso.inv_comp_eq,
    ← Scheme.Hom.normalizationDesc_comp_assoc (pullback.fst f (lineι K) ≫ f)
      (pullback.fst f (lineι K)) f rfl, hfK]

end Model

end

end CurvesJacobian
