/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticDuplication
import CurvesJacobian.Cusp.EllipticGenus
import CurvesJacobian.Cusp.CoverConstantField
import CurvesJacobian.Cusp.P1Curve
import CurvesJacobian.Cusp.FillSeq
import Belyi.Anabelian.BelyiInput
import CurvesJacobian.Cusp.CoverCuspDegree
import CurvesJacobian.Cusp.CuspDegreeEq
import CurvesJacobian.Scheme.GeomIntegralConstantField
import EllipticCurves.FunctionField.ConstantFieldDomain

/-!
# The elliptic curve `Ē` as a smooth proper curve: normalisation of `ℙ¹` in `E ∖ E[2]`

Let `E` be an elliptic curve over a field `K` of characteristic zero. The double cover
`x : E ∖ E[2] = Spec K[E][1/ψ] → 𝔸¹ ∖ {g = 0} = Spec K[x, 1/g]` is finite étale
(`CurvesJacobian.Cusp.isFiniteEtale_spec`). Embedding `𝔸¹ ∖ {g = 0}` into `ℙ¹_K` through the
affine chart `D₊(X₁)` (`CurvesJacobian.Cusp.lineChart`), the normalisation of `ℙ¹_K` in
`E ∖ E[2]` is the smooth projective model `Ē` of `E` (`CurvesJacobian.Cusp.curveE`).

* `CurvesJacobian.Cusp.isCurveOver_curveE`: `Ē` is a smooth proper geometrically integral curve
  over `K`. Smoothness and properness are those of the normalisation of a curve in a finite étale
  cover (`CoverCurve`); geometric integrality holds because `K` is algebraically closed in
  `K(Ē) = K(E)` (`WeierstrassCurve.Affine.algebraicClosure_functionField_eq_bot`).
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian
open scoped TensorProduct

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-! ### The affine chart `𝔸¹ = D₊(X₁) ⊆ ℙ¹` -/

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The affine chart `Spec k[T] ≅ D₊(X₁) ⊆ ℙ¹_k`, `T = X₀/X₁`. -/
def lineChart : Spec (.of k[X]) ⟶ P1 k := point k (Polynomial.X : k[X])

instance : IsOpenImmersion (lineChart k) := by
  haveI : IsIso (CommRingCat.ofHom (awayEval k (Polynomial.X : k[X]))) :=
    (RingEquiv.toCommRingCatIso (awayChartEquivOne k).toRingEquiv).isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (awayEval k (Polynomial.X : k[X])))) :=
    inferInstance
  haveI : IsOpenImmersion (Proj.awayι (P1Grading k) (MvPolynomial.X 1) (X_mem_P1Grading k 1)
    one_pos) := inferInstance
  exact IsOpenImmersion.comp _ _

lemma lineChart_structMap :
    lineChart k ≫ (P1 k ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k k[X])) :=
  point_structMap k _

end Chart

/-! ### `E ∖ E[2]` over `𝔸¹ ∖ {g = 0} ⊆ ℙ¹` -/

section Cover

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- `𝔸¹ ∖ {g = 0} → ℙ¹_K`. -/
def lineChartE : Spec (.of (lineRingE E)) ⟶ P1 K :=
  Spec.map (CommRingCat.ofHom (algebraMap K[X] (lineRingE E))) ≫ lineChart K

instance : IsOpenImmersion (lineChartE E) := by
  unfold lineChartE
  infer_instance

/-- The open `U₀ = 𝔸¹ ∖ {g = 0}` of `ℙ¹_K`. -/
def U0E : (P1 K).Opens := (lineChartE E).opensRange

/-- `Spec K[x, 1/g] ≅ U₀`. -/
def lineIsoE : Spec (.of (lineRingE E)) ≅ (U0E E).toScheme :=
  IsOpenImmersion.isoOfRangeEq (lineChartE E) (U0E E).ι (by simp [U0E])

omit [CharZero K] in
@[reassoc (attr := simp)]
lemma lineIsoE_hom_ι : (lineIsoE E).hom ≫ (U0E E).ι = lineChartE E :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

omit [CharZero K] in
lemma isAffineOpen_U0E : IsAffineOpen (U0E E) := isAffineOpen_opensRange _

instance [E.IsElliptic] : Nontrivial (lineRingE E) := inferInstance

lemma U0E_nonempty [E.IsElliptic] : ((U0E E : (P1 K).Opens) : Set (P1 K)).Nonempty := by
  obtain ⟨y⟩ : Nonempty (Spec (.of (lineRingE E))) := inferInstance
  exact ⟨lineChartE E y, y, rfl⟩

/-- `x : E ∖ E[2] → U₀`. -/
def pE : Spec (.of (coverRingE E)) ⟶ (U0E E).toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap (lineRingE E) (coverRingE E))) ≫ (lineIsoE E).hom

instance : IsFinite (pE E) := by
  haveI := isFiniteEtale_spec E
  unfold pE
  infer_instance

instance : Etale (pE E) := by
  haveI := isFiniteEtale_spec E
  unfold pE
  infer_instance

omit [CharZero K] in
lemma pE_ι : pE E ≫ (U0E E).ι =
    Spec.map (CommRingCat.ofHom (algebraMap K[X] (coverRingE E))) ≫ lineChart K := by
  rw [pE, Category.assoc, lineIsoE_hom_ι, lineChartE, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

instance [E.IsElliptic] : IsIntegral (Spec (.of (coverRingE E))) := inferInstance

end Cover

/-! ### The curve `Ē` -/

section Curve

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

instance : IsLocallyNoetherian (P1 K) := isLocallyNoetherian_of_isCurveOver K (P1 K)

/-- **The elliptic curve `Ē`**: the normalisation of `ℙ¹_K` in `E ∖ E[2] → 𝔸¹ ∖ {g = 0}`. -/
abbrev curveE : Scheme.{u} := (pE E ≫ (U0E E).ι).normalization

/-- `x : Ē → ℙ¹`. -/
abbrev qE : curveE E ⟶ P1 K := (pE E ≫ (U0E E).ι).fromNormalization

instance : (curveE E).Over (Spec (.of K)) := normalizationOver K (pE E)

instance : IsFinite (qE E) := isFinite_fromNormalization_of_isCurveOver (k := K) (U0E_nonempty E) _

/-- `E ∖ E[2] ⊆ Ē`. -/
abbrev toCurveE : Spec (.of (coverRingE E)) ⟶ curveE E := (pE E ≫ (U0E E).ι).toNormalization

instance : IsOpenImmersion (toCurveE E) := isOpenImmersion_toNormalization K (pE E)

/-- The open `E ∖ E[2] = q⁻¹ U₀` of `Ē`. -/
abbrev VE : (curveE E).Opens := qE E ⁻¹ᵁ U0E E

lemma isAffineOpen_VE : IsAffineOpen (VE E) := (isAffineOpen_U0E E).preimage _

instance : Nonempty (VE E) := by
  obtain ⟨y⟩ : Nonempty (Spec (.of (coverRingE E))) := inferInstance
  refine ⟨⟨toCurveE E y, ?_⟩⟩
  change qE E (toCurveE E y) ∈ U0E E
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization,
    Scheme.Hom.comp_apply]
  exact (pE E y).2

/-- `E ∖ E[2] ≅ q⁻¹ U₀`. -/
def VEIso : Spec (.of (coverRingE E)) ≅ (VE E).toScheme :=
  (isPullback_toNormalization (pE E)).isoIsPullback _ _
    (isPullback_morphismRestrict (qE E) (U0E E)).flip

omit [CharZero K] [E.IsElliptic] in
@[reassoc (attr := simp)]
lemma VEIso_hom_ι : (VEIso E).hom ≫ (VE E).ι = toCurveE E :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

omit [CharZero K] [E.IsElliptic] in
lemma range_toCurveE : Set.range (toCurveE E) = (VE E : Set (curveE E)) := by
  rw [← VEIso_hom_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.2 (VEIso E).hom.surjective, Set.image_univ, Scheme.Opens.range_ι]

omit [CharZero K] [E.IsElliptic] in
lemma toCurveE_le : (⊤ : (Spec (.of (coverRingE E))).Opens) ≤ toCurveE E ⁻¹ᵁ VE E := by
  intro y _
  change toCurveE E y ∈ (VE E : Set (curveE E))
  rw [← range_toCurveE]
  exact ⟨y, rfl⟩

instance : (Spec (.of (coverRingE E))).Over (Spec (.of K)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap K (coverRingE E)))⟩

instance : (toCurveE E).IsOver (Spec (.of K)) := by
  constructor
  change toCurveE E ≫ qE E ≫ (P1 K ↘ Spec (.of K)) = _
  rw [Scheme.Hom.toNormalization_fromNormalization_assoc, pE_ι, Category.assoc,
    lineChart_structMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rfl

/-- The restriction `Γ(Ē, q⁻¹ U₀) → Γ(E ∖ E[2], ⊤)`. -/
def restrVE : Γ(curveE E, VE E) ⟶ Γ(Spec (.of (coverRingE E)), ⊤) :=
  (toCurveE E).appLE (VE E) ⊤ (toCurveE_le E)

instance : IsIso (restrVE E) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (toCurveE E) (isAffineOpen_VE E)
    (isAffineOpen_top _) (toCurveE_le E)
  rw [IsAffineOpen.fromSpec_top] at h
  have hr : Set.range ((Spec (.of (coverRingE E))).isoSpec.inv ≫ toCurveE E) =
      Set.range (isAffineOpen_VE E).fromSpec := by
    rw [IsAffineOpen.range_fromSpec, ← range_toCurveE]
    ext y
    refine ⟨fun ⟨z, hz⟩ ↦ ⟨_, hz⟩, fun ⟨z, hz⟩ ↦ ⟨(Spec (.of (coverRingE E))).isoSpec.hom z, ?_⟩⟩
    rw [← hz, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  have h' : Spec.map (restrVE E) = (IsOpenImmersion.isoOfRangeEq _ _ hr).hom := by
    rw [← cancel_mono (isAffineOpen_VE E).fromSpec, IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact h
  haveI : IsIso (Spec.map (restrVE E)) := by rw [h']; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).2 (isIso_SpecMap_iff.1 inferInstance)

/-- **`Γ(Ē, q⁻¹ U₀) = K[E][1/ψ]`.** -/
def sectionsVEEquiv : Γ(curveE E, VE E) ≃+* coverRingE E :=
  (asIso (restrVE E) ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

lemma sectionsVEEquiv_algebraMap (c : K) :
    sectionsVEEquiv E (algebraMap K Γ(curveE E, VE E) c) = algebraMap K (coverRingE E) c := by
  have h := congrArg (fun f ↦ f c) (FiniteEtale.appLE_comp_algebraMap (toCurveE E) K (VE E) ⊤
    (toCurveE_le E))
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  change (Scheme.ΓSpecIso _).hom (restrVE E (algebraMap K Γ(curveE E, VE E) c)) = _
  rw [restrVE, h]
  change (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom (algebraMap K (coverRingE E)))).appLE
    ⊤ ⊤ _ ((Scheme.ΓSpecIso (.of K)).inv c)) = _
  change (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom
    (algebraMap K (coverRingE E)))).appTop ((Scheme.ΓSpecIso (.of K)).inv c)) = _
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]
  rfl

/-- `Γ(Ē, q⁻¹ U₀) ≃ₐ[K] K[E][1/ψ]`. -/
def sectionsVEAlgEquiv : Γ(curveE E, VE E) ≃ₐ[K] coverRingE E :=
  AlgEquiv.ofRingEquiv (f := sectionsVEEquiv E) (sectionsVEEquiv_algebraMap E)

instance : IsIntegrallyClosed Γ(curveE E, VE E) :=
  isIntegrallyClosed_normalization (isIntegrallyClosed_of_isCurveOver (k := K)) (U0E_nonempty E)
    (pE E) (isAffineOpen_VE E)

instance : IsFractionRing Γ(curveE E, VE E) (curveE E).functionField :=
  functionField_isFractionRing_of_isAffineOpen (curveE E) (VE E) (isAffineOpen_VE E)

instance : IsScalarTower K Γ(curveE E, VE E) (curveE E).functionField :=
  IsScalarTower.of_algebraMap_eq fun c ↦ algebraMap_functionField_eq_germ K (curveE E) (VE E) c

/-- **`K` is algebraically closed in `K(Ē)`**: an element algebraic over `K` is regular on
`q⁻¹ U₀ ≅ E ∖ E[2]`, hence lies in `K[E][1/ψ] ⊆ K(E)`, where `K` is algebraically closed
(`WeierstrassCurve.Affine.algebraicClosure_functionField_eq_bot`). -/
theorem curveE_isAlgClosedIn (α : (curveE E).functionField) (hα : IsAlgebraic K α) :
    α ∈ (algebraMap K (curveE E).functionField).range := by
  have hαi : IsIntegral K α := hα.isIntegral
  obtain ⟨s, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (hαi.tower_top (A := Γ(curveE E, VE E)))
  have hs : IsIntegral K s := (isIntegral_algHom_iff (IsScalarTower.toAlgHom K _ _)
    (IsFractionRing.injective _ _)).1 hαi
  have hb : IsIntegral K (algebraMap (coverRingE E) E.toAffine.FunctionField
      (sectionsVEAlgEquiv E s)) :=
    (hs.map (sectionsVEAlgEquiv E)).map (IsScalarTower.toAlgHom K _ _)
  have hmem : algebraMap (coverRingE E) E.toAffine.FunctionField (sectionsVEAlgEquiv E s) ∈
      algebraicClosure K E.toAffine.FunctionField := mem_algebraicClosure_iff.2 hb.isAlgebraic
  rw [WeierstrassCurve.Affine.algebraicClosure_functionField_eq_bot, IntermediateField.mem_bot]
    at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcs : s = algebraMap K _ c := by
    apply (sectionsVEAlgEquiv E).injective
    apply algebraMap_coverRingE_injective E
    rw [AlgEquiv.commutes, ← hc, ← IsScalarTower.algebraMap_apply]
  exact ⟨c, by rw [hcs, ← IsScalarTower.algebraMap_apply]⟩

/-- **`Ē` is a smooth proper geometrically integral curve over `K`.** -/
instance isCurveOver_curveE : IsCurveOver K (curveE E) where
  toSmoothOfRelativeDimension := smoothOfRelativeDimension_normalization (k := K)
    (U0E_nonempty E) (pE E)
  toIsProper := isProper_normalization (k := K) (U0E_nonempty E) (pE E)
  toGeometricallyIntegral := geometricallyIntegral_of_isAlgClosedIn (curveE_isAlgClosedIn E)

/-! ### The function field `K(Ē)` and the genus -/

/-- `K[E][1/ψ] → K(Ē)`. -/
instance : Algebra (DupB E) (curveE E).functionField :=
  ((algebraMap Γ(curveE E, VE E) (curveE E).functionField).comp
    (sectionsVEEquiv E).symm.toRingHom).toAlgebra

instance : IsFractionRing (DupB E) (curveE E).functionField :=
  (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (curveE E).functionField
    (sectionsVEEquiv E)).1 inferInstance

lemma algebraMap_dupB_functionField (b : DupB E) :
    algebraMap (DupB E) (curveE E).functionField b =
      algebraMap Γ(curveE E, VE E) (curveE E).functionField ((sectionsVEEquiv E).symm b) := rfl

instance : IsScalarTower K (DupB E) (curveE E).functionField :=
  IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [algebraMap_dupB_functionField, IsScalarTower.algebraMap_apply K Γ(curveE E, VE E)]
    congr 1
    apply (sectionsVEEquiv E).injective
    rw [RingEquiv.apply_symm_apply, sectionsVEEquiv_algebraMap]
    rfl

/-- `x ∈ K(Ē)`. -/
abbrev xN : (curveE E).functionField := algebraMap (DupB E) _ (xD E)

/-- `y ∈ K(Ē)`. -/
abbrev yN : (curveE E).functionField := algebraMap (DupB E) _ (toDupB E (yB E))

lemma algebraMap_dupB_algebraMap_K (c : K) :
    algebraMap (DupB E) (curveE E).functionField (toDupB E (algebraMap K _ c)) =
      algebraMap K (curveE E).functionField c := by
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

lemma wEq_curveE : WEq E (xN E) (yN E) := by
  have h := congrArg (fun a ↦ algebraMap (DupB E) (curveE E).functionField
    (toDupB E (algebraMap E.toAffine.CoordinateRing (coverRingE E) a))) (equation_E E)
  simp only [map_sub, map_add, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply K E.toAffine.CoordinateRing (coverRingE E),
    algebraMap_dupB_algebraMap_K] at h
  rw [show toDupB E (algebraMap _ (coverRingE E) (xE E)) = xD E from toDupB_xB E] at h
  rw [WEq, ← sub_eq_zero]
  exact h

lemma psiN_ne_zero : 2 * yN E + algebraMap K _ E.a₁ * xN E + algebraMap K _ E.a₃ ≠ 0 := by
  have h := congrArg (fun b ↦ algebraMap (DupB E) (curveE E).functionField (toDupB E b))
    (psiB_eq E)
  simp only [map_add, map_mul, map_ofNat, algebraMap_dupB_algebraMap_K] at h
  rw [toDupB_xB] at h
  rw [← h]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (DupB E) _)).2 ?_
  refine (map_ne_zero_iff _ (toDupB E).injective).2 ?_
  exact (IsLocalization.Away.algebraMap_isUnit (psiE E)).ne_zero

open KaehlerDifferential in
lemma D_xN_ne_zero : D K (curveE E).functionField (xN E) ≠ 0 := by
  haveI : Algebra.FormallyEtale (DupB E) (curveE E).functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (DupB E))
  let e : (curveE E).functionField ⊗[DupB E] Ω[DupB E⁄K] ≃ₗ[(curveE E).functionField]
      (curveE E).functionField :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (kaehlerEquivB E) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid (DupB E) (curveE E).functionField
        (curveE E).functionField
  have h1 : e (1 ⊗ₜ D K (DupB E) (xD E)) = 1 := by
    simp [e, TensorProduct.AlgebraTensorModule.congr_tmul, kaehlerEquivB_D_xD]
  have h2 : tensorKaehlerEquivOfFormallyEtale K (DupB E) (curveE E).functionField
      (1 ⊗ₜ D K (DupB E) (xD E)) = D K _ (xN E) := by
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D]
  intro h0
  rw [h0, LinearEquiv.map_eq_zero_iff] at h2
  rw [h2, map_zero] at h1
  exact zero_ne_one h1

/-- **`Ē` has genus at least one**: the invariant differential `dx/ψ` is regular. -/
theorem one_le_curveGenus_curveE : 1 ≤ Anabelian.curveGenus K (curveE E) :=
  one_le_curveGenus_of_weierstrass (curveE E) E (wEq_curveE E) (psiN_ne_zero E) (D_xN_ne_zero E)

end Curve

/-! ### The hyperbolic curves `E ∖ E[2]` and `E ∖ {O}` -/

section HypCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `∞ = [1 : 0]` is not in the affine chart `D₊(X₁)`. -/
lemma infty_not_mem_range_lineChart (k : Type u) [Field k] :
    P1.infty k ∉ Set.range (lineChart k) := by
  rintro ⟨y, hy⟩
  have h : P1.infty k ∈ Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) := by
    rw [← Proj.opensRange_awayι (P1Grading k) (MvPolynomial.X 1) (X_mem_P1Grading k 1) one_pos]
    exact ⟨_, hy⟩
  rw [Proj.mem_basicOpen] at h
  apply h
  change (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ (P1.infty k).asHomogeneousIdeal.toIdeal
  rw [P1.infty, mkPoint_asIdeal]
  exact Ideal.mem_span_singleton_self _

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- The open `E ∖ {O} = q⁻¹ 𝔸¹` of `Ē`. -/
abbrev XE : (curveE E).Opens := qE E ⁻¹ᵁ (lineChart K).opensRange

omit [CharZero K] [E.IsElliptic] in
lemma VE_le_XE : VE E ≤ XE E := by
  intro c hc
  obtain ⟨y, hy⟩ := hc
  exact ⟨_, hy.trans rfl⟩

lemma exists_point_infty : ∃ c : curveE E, qE E c = P1.infty K :=
  surjective_fromNormalization (k := K) (U0E_nonempty E) (pE E) _

lemma compl_XE_nonempty : ((XE E : (curveE E).Opens) : Set (curveE E))ᶜ.Nonempty := by
  obtain ⟨c, hc⟩ := exists_point_infty E
  refine ⟨c, fun h ↦ infty_not_mem_range_lineChart K ?_⟩
  rw [← hc]
  exact h

omit [E.IsElliptic] in
lemma VE_nonempty : ((VE E : (curveE E).Opens) : Set (curveE E)).Nonempty := by
  obtain ⟨⟨c, hc⟩⟩ : Nonempty (VE E) := inferInstance
  exact ⟨c, hc⟩

lemma one_le_cuspDegree {U : (curveE E).Opens} (hU : VE E ≤ U) (hUX : U ≤ XE E) :
    1 ≤ Anabelian.cuspDegree K (curveE E) U := by
  have hne : (U : Set (curveE E)).Nonempty := (VE_nonempty E).mono hU
  have hfin := finite_compl_of_isCurveOver (k := K) (curveE E) U hne
  obtain ⟨c, hc⟩ := (compl_XE_nonempty E).mono (Set.compl_subset_compl.2 hUX)
  unfold Anabelian.cuspDegree
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    ((Set.Finite.mem_toFinset hfin).2 hc))
  letI := Anabelian.residueFieldAlgebra K (curveE E) c
  haveI := finite_residueField K (X := curveE E) (isClosed_singleton_of_not_mem (k := K) _ U hne hc)
  exact Module.finrank_pos

lemma hyperbolic_of_le {U : (curveE E).Opens} (hU : VE E ≤ U) (hUX : U ≤ XE E) :
    haveI := IsCurveOver.isIntegral K (curveE E)
    2 < 2 * Anabelian.curveGenus K (curveE E) + Anabelian.cuspDegree K (curveE E) U := by
  have h1 := one_le_curveGenus_curveE E
  have h2 := one_le_cuspDegree E hU hUX
  omega

/-- **`E ∖ E[2]` as a hyperbolic curve over `K`** (compactification `Ē`). -/
def hypCurveV : HypCurve K where
  Xbar := curveE E
  U := VE E
  nonempty := VE_nonempty E
  cusps_finite := finite_compl_of_isCurveOver (k := K) (curveE E) _ (VE_nonempty E)
  hyperbolic := hyperbolic_of_le E le_rfl (VE_le_XE E)

/-- **IUT's once-punctured elliptic curve `X = E ∖ {O}` as a hyperbolic curve over `K`**
(compactification `Ē`, `X = q⁻¹ 𝔸¹`). -/
def hypCurveX : HypCurve K where
  Xbar := curveE E
  U := XE E
  nonempty := (VE_nonempty E).mono (VE_le_XE E)
  cusps_finite := finite_compl_of_isCurveOver (k := K) (curveE E) _
    ((VE_nonempty E).mono (VE_le_XE E))
  hyperbolic := hyperbolic_of_le E (VE_le_XE E) le_rfl

end HypCurves

end CurvesJacobian.Cusp
