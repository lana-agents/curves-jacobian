/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CurveGenus
import CurvesJacobian.Scheme.ValuationPoints
import CurvesJacobian.Scheme.PointDegree
import Belyi.Converse.NormalizationOpen
import Belyi.Curve.Existence
import CurvesJacobian.Picard.CurveCover
import Belyi.P1.ChartCoord
import Belyi.P1.ChartTransition

/-!
# The two affine charts of a curve attached to a rational function

Let `X` be an integral scheme over a field `k` whose local rings are valuation rings, and let
`π : X ⟶ Y` be a finite morphism. If `ι : Spec A ⟶ Y` is an open immersion such that the generic
point `Spec K(X) ⟶ X ⟶ Y` factors as `Spec e ≫ ι` for a ring map `e : A ⟶ K(X)` with image
in `k[s] = Algebra.adjoin k {s}` and containing `s`, then the affine open `U = π⁻¹(ι(Spec A))`
has ring of functions the integral closure of `k[s]` in `K(X)`:
`CurvesJacobian.mem_range_germToFunctionField_iff`
(`z ∈ Γ(U) ⊆ K(X)` iff `z` is integral over `k[s]`).

For a curve `X` over a perfect field `k` and a transcendental `τ ∈ K(X)`, the morphism
`π = homOfFunctionField τ : X ⟶ ℙ¹` is finite, and the two standard charts `D₊(X₁)` (affine
coordinate `X₀/X₁ ↦ τ`) and `D₊(X₀)` (affine coordinate `X₁/X₀ ↦ τ⁻¹`) give the affine opens

* `CurvesJacobian.chartOne k X τ = π⁻¹ D₊(X₁)`, with `Γ` the integral closure of `k[τ]`
  (`mem_range_germ_chartOne_iff`),
* `CurvesJacobian.chartZero k X τ = π⁻¹ D₊(X₀)`, with `Γ` the integral closure of `k[τ⁻¹]`
  (`mem_range_germ_chartZero_iff`),

covering `X` (`chartOne_sup_chartZero`). These are the charts `U, U'` of pi1's étale van Kampen
theorem in Galois form (`Pi1.Orbifold.GaloisData.ker_chartHomX`).
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi

universe u

noncomputable section

namespace CurvesJacobian

section Lemmas

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsCurveOver k X]

include k in
/-- A curve is locally Noetherian (it is of finite type over a field). -/
theorem IsCurveOver.isLocallyNoetherian : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))

include k in
/-- The stalks of a curve over a perfect field are integrally closed (valuation rings). -/
theorem IsCurveOver.isIntegrallyClosed_stalk [PerfectField k] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  classical
  haveI := IsCurveOver.isIntegral k X
  haveI := valuationRing_stalk_of_isCurveOver k X x
  letI := IsBezout.toGCDDomain (X.presheaf.stalk x)
  infer_instance

end Lemmas

/-- A nonempty open subscheme of an integral scheme is connected. -/
lemma connectedSpace_opens_of_isIntegral {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U] : ConnectedSpace U :=
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  inferInstance

/-- An open immersion with nonempty source into an integral scheme has dense range. -/
lemma denseRange_of_isOpenImmersion {X Y : Scheme.{u}} [IsIntegral X] (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y] : DenseRange j.base :=
  j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

section Generic

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsIntegral X] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))

/-- The scalars `k` lie in every stalk `𝒪_{X,x} ⊆ K(X)`. -/
lemma algebraMap_mem_stalkValuationSubring (x : X) (c : k) :
    algebraMap k X.functionField c ∈ stalkValuationSubring hX x :=
  ⟨_, algebraMap_stalk_functionField_germ k X x c⟩

include hX in
/-- **The ring of functions of a chart.** See the module docstring. -/
theorem mem_range_germToFunctionField_iff {Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    {A : CommRingCat.{u}} (ι : Spec A ⟶ Y) [IsOpenImmersion ι] (e : A ⟶ X.functionField)
    (he : X.fromSpecStalk (genericPoint X) ≫ π = Spec.map e ≫ ι) (s : X.functionField)
    (hse : ∀ a, e a ∈ Algebra.adjoin k {s}) (hs : s ∈ Set.range e)
    [Nonempty (π ⁻¹ᵁ ι.opensRange)] (z : X.functionField) :
    z ∈ Set.range (X.germToFunctionField (π ⁻¹ᵁ ι.opensRange)) ↔
      IsIntegral (Algebra.adjoin k {s}) z := by
  set U := π ⁻¹ᵁ ι.opensRange with hUdef
  have hU : IsAffineOpen U := (isAffineOpen_opensRange ι).preimage π
  have hr : Set.range (hU.fromSpec ≫ π).base ⊆ Set.range ι.base := by
    rintro _ ⟨y, rfl⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    exact hy
  set ρ := IsOpenImmersion.lift ι (hU.fromSpec ≫ π) hr with hρ
  set φ : A ⟶ Γ(X, U) := Spec.preimage ρ with hφdef
  have hφ : Spec.map φ = ρ := Spec.map_preimage ρ
  have hgen : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  have key1 : φ ≫ X.germToFunctionField U = e := by
    rw [← Spec.map_inj, Spec.map_comp, hφ, ← cancel_mono ι, Category.assoc,
      IsOpenImmersion.lift_fac, ← he, ← hU.fromSpecStalk_eq_fromSpecStalk hgen]
    rfl
  have key2 : φ.hom.Finite := by
    have hρ' : ρ = hU.isoSpec.inv ≫ (π ∣_ ι.opensRange) ≫ ι.isoOpensRange.inv := by
      rw [← cancel_mono ι, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
        IsAffineOpen.isoSpec_inv_ι]
    have : IsFinite ρ := by rw [hρ']; infer_instance
    rw [← hφ] at this
    exact (IsFinite.SpecMap_iff φ).mp this
  constructor
  · rintro ⟨s', rfl⟩
    obtain ⟨p, hpm, hp⟩ := key2.to_isIntegral s'
    let g : A →+* Algebra.adjoin k {s} := e.hom.codRestrict (Algebra.adjoin k {s}).toSubring hse
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (Algebra.adjoin k {s}) X.functionField).comp g = e.hom := rfl
    rw [hcomp, ← key1, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, hp, map_zero]
  · intro hz
    obtain ⟨a, ha⟩ := exists_section_of_forall_mem_stalk U z fun x hx => by
      have hle : ∀ y ∈ Algebra.adjoin k {s}, y ∈ stalkValuationSubring hX x := by
        intro y hy
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          obtain ⟨c, rfl⟩ := hs
          rw [← key1, CommRingCat.comp_apply,
            ← X.algebraMap_germ_eq_germToFunctionField hx]
          exact ⟨_, rfl⟩
        | algebraMap c => exact algebraMap_mem_stalkValuationSubring k hX x c
        | add y w _ _ hy hw => exact add_mem hy hw
        | mul y w _ _ hy hw => exact mul_mem hy hw
      obtain ⟨p, hpm, hp⟩ := hz
      let g : Algebra.adjoin k {s} →+* stalkValuationSubring hX x :=
        (Subring.inclusion (fun y hy => hle y hy) :
          (Algebra.adjoin k {s}).toSubring →+* (stalkValuationSubring hX x).toSubring)
      have hint : IsIntegral (stalkValuationSubring hX x) z := by
        refine ⟨p.map g, hpm.map g, ?_⟩
        rw [Polynomial.eval₂_map]
        exact hp
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      rw [← hw]
      exact w.2
    exact ⟨a, ha⟩

end Generic

section Evaluation

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

lemma aeval_mem_adjoin (v : Fin 2 → K) (s : K) (hv : ∀ i, v i ∈ Algebra.adjoin k {s})
    (a : MvPolynomial (Fin 2) k) : aeval v a ∈ Algebra.adjoin k {s} := by
  have h : Algebra.adjoin k (Set.range v) ≤ Algebra.adjoin k {s} :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hv i)
  apply h
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨a, rfl⟩

/-- The chart evaluation `X₀/X₁ ↦ τ` takes values in `k[τ]`. -/
lemma awayEval_mem_adjoin (τ : K)
    (a : Away (P1Grading k) (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)) :
    P1.awayEval k τ a ∈ Algebra.adjoin k {τ} := by
  obtain ⟨n, b, hb, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (P1Grading k) (P1.X_mem_P1Grading k 1) a
  rw [P1.awayEval_mk]
  refine aeval_mem_adjoin k _ τ (fun i => ?_) b
  fin_cases i
  · exact Algebra.subset_adjoin rfl
  · exact one_mem _

/-- The chart evaluation `X₁/X₀ ↦ s` takes values in `k[s]`. -/
lemma awayEval₀_mem_adjoin (s : K)
    (a : Away (P1Grading k) (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)) :
    P1.awayEval₀ k s a ∈ Algebra.adjoin k {s} := by
  obtain ⟨n, b, hb, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (P1Grading k) (P1.X_mem_P1Grading k 0) a
  rw [P1.awayEval₀_mk]
  refine aeval_mem_adjoin k _ s (fun i => ?_) b
  fin_cases i
  · exact one_mem _
  · exact Algebra.subset_adjoin rfl

lemma mem_range_awayEval (τ : K) : τ ∈ Set.range (P1.awayEval k τ) :=
  ⟨P1.affineCoord k, P1.awayEval_affineCoord k τ⟩

lemma mem_range_awayEval₀ (s : K) : s ∈ Set.range (P1.awayEval₀ k s) :=
  ⟨P1.affineCoord0 k, P1.awayEval0_affineCoord k s⟩

end Evaluation

section Curve

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- The morphism `X ⟶ ℙ¹` attached to a rational function `τ` (belyi's
`homOfFunctionField`, with the valuation-ring hypothesis discharged for curves). -/
abbrev toP1 (τ : X.functionField) : X ⟶ P1 k :=
  homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X) τ

omit [PerfectField k] [IsCurveOver k X] in
/-- The rational map of a morphism restricts to the morphism on the generic point. -/
lemma fromFunctionField_toRationalMap {Y : Scheme.{u}} (f : X ⟶ Y) :
    f.toRationalMap.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ f := by
  change Scheme.PartialMap.fromFunctionField f.toPartialMap = _
  simp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem,
    Scheme.Hom.toPartialMap]
  rw [← Category.assoc]
  congr 1
  rw [Scheme.topIso_hom]
  exact Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

omit [PerfectField k] [IsCurveOver k X] in
lemma fromFunctionField_ratMapOfFunctionField (τ : X.functionField) :
    (ratMapOfFunctionField k X τ).fromFunctionField = functionFieldPoint k X τ :=
  congrArg Subtype.val ((Scheme.RationalMap.equivFunctionFieldOver
    (S := Spec (CommRingCat.of k)) (X := X) (Y := P1 k)).symm_apply_apply
      ⟨functionFieldPoint k X τ, inferInstance⟩)

/-- The generic point of `X` is mapped by `toP1 τ` to the point of `ℙ¹` with coordinate `τ`. -/
lemma fromSpecStalk_comp_toP1 (τ : X.functionField) :
    X.fromSpecStalk (genericPoint X) ≫ toP1 k X τ = functionFieldPoint k X τ := by
  rw [← fromFunctionField_toRationalMap, toRationalMap_homOfFunctionField,
    fromFunctionField_ratMapOfFunctionField]

/-- The chart `D₊(X₁) ⊆ ℙ¹`, as an open immersion `Spec k[X₀/X₁] ⟶ ℙ¹`. -/
def chartι₁ : Spec (CommRingCat.of (HomogeneousLocalization.Away (P1Grading k)
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) k))) ⟶ P1 k :=
  Proj.awayι (P1Grading k) (MvPolynomial.X 1) (P1.X_mem_P1Grading k 1) one_pos

/-- The chart `D₊(X₀) ⊆ ℙ¹`, as an open immersion `Spec k[X₁/X₀] ⟶ ℙ¹`. -/
def chartι₀ : Spec (CommRingCat.of (HomogeneousLocalization.Away (P1Grading k)
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) k))) ⟶ P1 k :=
  Proj.awayι (P1Grading k) (MvPolynomial.X 0) (P1.X_mem_P1Grading k 0) one_pos

instance : IsOpenImmersion (chartι₁ k) := by
  unfold chartι₁ P1
  infer_instance

instance : IsOpenImmersion (chartι₀ k) := by
  unfold chartι₀ P1
  infer_instance

/-- The chart `π⁻¹ D₊(X₁)` (where `τ` is regular). -/
abbrev chartOne (τ : X.functionField) : X.Opens :=
  toP1 k X τ ⁻¹ᵁ (chartι₁ k).opensRange

/-- The chart `π⁻¹ D₊(X₀)` (where `τ⁻¹` is regular). -/
abbrev chartZero (τ : X.functionField) : X.Opens :=
  toP1 k X τ ⁻¹ᵁ (chartι₀ k).opensRange

variable {k X}

lemma isFinite_toP1 {τ : X.functionField} (hτ : Transcendental k τ) : IsFinite (toP1 k X τ) :=
  isFinite_homOfFunctionField_of_isCurveOver k X hτ

lemma fromSpecStalk_comp_toP1_one (τ : X.functionField) :
    X.fromSpecStalk (genericPoint X) ≫ toP1 k X τ =
      Spec.map (CommRingCat.ofHom (P1.awayEval k τ)) ≫ chartι₁ k :=
  fromSpecStalk_comp_toP1 k X τ

lemma fromSpecStalk_comp_toP1_zero {τ : X.functionField} (hτ : τ ≠ 0) :
    X.fromSpecStalk (genericPoint X) ≫ toP1 k X τ =
      Spec.map (CommRingCat.ofHom (P1.awayEval₀ k τ⁻¹)) ≫ chartι₀ k :=
  (fromSpecStalk_comp_toP1 k X τ).trans (P1.point_eq_point₀ (k := k) τ τ⁻¹ (mul_inv_cancel₀ hτ))

lemma genericPoint_mem_of_fromSpecStalk_comp {Y : Scheme.{u}} (f : X ⟶ Y) {A : CommRingCat.{u}}
    (ι : Spec A ⟶ Y) [IsOpenImmersion ι] (e : A ⟶ X.functionField)
    (he : X.fromSpecStalk (genericPoint X) ≫ f = Spec.map e ≫ ι) :
    genericPoint X ∈ f ⁻¹ᵁ ι.opensRange := by
  have hx : (X.fromSpecStalk (genericPoint X)).base (IsLocalRing.closedPoint _) =
      genericPoint X := Scheme.fromSpecStalk_closedPoint
  change f.base (genericPoint X) ∈ Set.range ι.base
  rw [← hx]
  change (X.fromSpecStalk (genericPoint X) ≫ f).base _ ∈ _
  rw [he]
  exact ⟨_, rfl⟩

lemma genericPoint_mem_chartOne (τ : X.functionField) : genericPoint X ∈ chartOne k X τ :=
  genericPoint_mem_of_fromSpecStalk_comp _ _ _ (fromSpecStalk_comp_toP1_one (k := k) τ)

instance (τ : X.functionField) : Nonempty (chartOne k X τ) :=
  ⟨⟨_, genericPoint_mem_chartOne τ⟩⟩

lemma genericPoint_mem_chartZero {τ : X.functionField} (hτ : τ ≠ 0) :
    genericPoint X ∈ chartZero k X τ :=
  genericPoint_mem_of_fromSpecStalk_comp _ _ _ (fromSpecStalk_comp_toP1_zero (k := k) hτ)

lemma isAffineOpen_chartOne {τ : X.functionField} (hτ : Transcendental k τ) :
    IsAffineOpen (chartOne k X τ) :=
  haveI := isFinite_toP1 hτ
  (isAffineOpen_opensRange (chartι₁ k)).preimage (toP1 k X τ)

lemma isAffineOpen_chartZero {τ : X.functionField} (hτ : Transcendental k τ) :
    IsAffineOpen (chartZero k X τ) :=
  haveI := isFinite_toP1 hτ
  (isAffineOpen_opensRange (chartι₀ k)).preimage (toP1 k X τ)

/-- The two charts cover `X`. -/
lemma chartOne_sup_chartZero (τ : X.functionField) : chartOne k X τ ⊔ chartZero k X τ = ⊤ := by
  have hcov : ∀ x : P1 k, x ∈ ((P1.coordCover k).openCover.f (1 : Fin 2)).opensRange ∨
      x ∈ ((P1.coordCover k).openCover.f (0 : Fin 2)).opensRange := by
    intro x
    obtain ⟨i, y, rfl⟩ := (P1.coordCover k).openCover.exists_eq x
    have hi : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hi i with rfl | rfl
    · exact Or.inr ⟨y, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
  ext x
  simp only [Opens.coe_sup, Set.mem_union, SetLike.mem_coe, Opens.coe_top, Set.mem_univ,
    iff_true]
  unfold chartOne chartZero
  exact hcov (toP1 k X τ x)

/-- **`Γ(π⁻¹ D₊(X₁))` is the integral closure of `k[τ]` in `K(X)`.** -/
theorem mem_range_germ_chartOne_iff {τ : X.functionField} (hτ : Transcendental k τ)
    (z : X.functionField) :
    z ∈ Set.range (X.germToFunctionField (chartOne k X τ)) ↔
      IsIntegral (Algebra.adjoin k {τ}) z :=
  haveI := isFinite_toP1 hτ
  mem_range_germToFunctionField_iff k (valuationRing_stalk_of_isCurveOver k X) (toP1 k X τ) _
    _ (fromSpecStalk_comp_toP1_one τ) τ (awayEval_mem_adjoin k τ) (mem_range_awayEval k τ) z

/-- **`Γ(π⁻¹ D₊(X₀))` is the integral closure of `k[τ⁻¹]` in `K(X)`.** -/
theorem mem_range_germ_chartZero_iff {τ : X.functionField} (hτ : Transcendental k τ)
    [Nonempty (chartZero k X τ)] (z : X.functionField) :
    z ∈ Set.range (X.germToFunctionField (chartZero k X τ)) ↔
      IsIntegral (Algebra.adjoin k {τ⁻¹}) z :=
  haveI := isFinite_toP1 hτ
  mem_range_germToFunctionField_iff k (valuationRing_stalk_of_isCurveOver k X) (toP1 k X τ) _
    _ (fromSpecStalk_comp_toP1_zero (by rintro rfl; exact hτ isAlgebraic_zero)) τ⁻¹
    (awayEval₀_mem_adjoin k τ⁻¹)
    (mem_range_awayEval₀ k τ⁻¹) z

end Curve

end CurvesJacobian

end
