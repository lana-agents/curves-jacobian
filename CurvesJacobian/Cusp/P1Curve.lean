/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.RingHom.StandardSmooth
import Belyi.P1.BaseChangeIso
import Belyi.P1.ChartCoord
import Belyi.P1.Curve
import Belyi.BelyiCoverRestrict
import CurvesJacobian.Cusp.CuspDegreeEq

/-!
# The projective line is a curve with at least three cusps on `ℙ¹ ∖ {0, 1, ∞}`

* `CurvesJacobian.Cusp.isCurveOver_P1`: belyi's `ℙ¹_k` is a smooth proper geometrically integral
  curve over `k` (belyi's `IsCurveOver`), for every field `k`.
* `CurvesJacobian.Cusp.three_le_cuspDegree_puncturedLine`: `3 ≤ r(ℙ¹ ∖ {0, 1, ∞})`.

**Smoothness.** `SmoothOfRelativeDimension 1` is local on the source; on the two coordinate charts
`D₊(Xᵢ)` the structure morphism is `Spec` of the chart algebra map `k → (k[X₀,X₁]_{Xᵢ})₀`, and
the chart ring is `k[T]` (`Belyi.P1.awayChartEquivZero/One`), which is standard smooth of
relative dimension one via the presentation `k[X] ⧸ (∅)` with no relations.

**Geometric integrality.** For every field `K / k` the base change of `ℙ¹_k` is `ℙ¹_K`
(`Belyi.P1.isPullback_mapOfAlgebra`), which is integral.

**Cusps.** The three marked points are distinct closed points, so their residue fields are
finite over `k` and each contributes a degree `≥ 1`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi Belyi.Anabelian

open scoped Belyi.P1

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace CurvesJacobian.Cusp

variable (k : Type u) [Field k]

/-- The polynomial ring `k[T]` is standard smooth of relative dimension one over `k`. -/
lemma isStandardSmoothOfRelativeDimension_polynomial :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) := by
  let v : Empty → MvPolynomial Unit k := Empty.elim
  let P₀ := Algebra.PreSubmersivePresentation.naive (R := k) (v := v)
    (Empty.elim : Empty → Unit) (Function.injective_of_subsingleton _)
  let P : Algebra.SubmersivePresentation k (MvPolynomial Unit k ⧸ Ideal.span (Set.range v))
      Unit Empty :=
    { P₀ with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty,
          map_one]
        exact isUnit_one }
  have hv : Ideal.span (Set.range v) = ⊥ := by simp [v]
  let e : (MvPolynomial Unit k ⧸ Ideal.span (Set.range v)) ≃ₐ[k] Polynomial k :=
    (Ideal.quotientEquivAlgOfEq k hv).trans
      ((AlgEquiv.quotientBot k _).trans (MvPolynomial.uniqueAlgEquiv k Unit))
  exact (P.ofAlgEquiv e).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

/-- The chart algebra map `k → (k[X₀,X₁]_{X₀})₀` is standard smooth of relative dimension one. -/
lemma isStandardSmoothOfRelativeDimension_chartAlgHom_zero :
    (P1.chartAlgHom k 0).IsStandardSmoothOfRelativeDimension 1 := by
  haveI := isStandardSmoothOfRelativeDimension_polynomial k
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (P1.awayChartEquivZero k).symm

/-- The chart algebra map `k → (k[X₀,X₁]_{X₁})₀` is standard smooth of relative dimension one. -/
lemma isStandardSmoothOfRelativeDimension_chartAlgHom_one :
    (P1.chartAlgHom k 1).IsStandardSmoothOfRelativeDimension 1 := by
  haveI := isStandardSmoothOfRelativeDimension_polynomial k
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (P1.awayChartEquivOne k).symm

/-- The chart algebra maps `k → (k[X₀,X₁]_{Xᵢ})₀` of `ℙ¹` are standard smooth of relative
dimension one. -/
lemma isStandardSmoothOfRelativeDimension_chartAlgHom (i : Fin 2) :
    (P1.chartAlgHom k i).IsStandardSmoothOfRelativeDimension 1 := by
  fin_cases i
  exacts [isStandardSmoothOfRelativeDimension_chartAlgHom_zero k,
    isStandardSmoothOfRelativeDimension_chartAlgHom_one k]

/-- The structure morphism of `ℙ¹` restricted to the chart `D₊(Xᵢ)` is smooth of relative
dimension one. -/
lemma smoothOfRelativeDimension_awayι_comp_structMap (i : Fin 2) :
    SmoothOfRelativeDimension 1 (Proj.awayι (P1Grading k) (MvPolynomial.X i)
      (P1.X_mem_P1Grading k i) one_pos ≫ P1.structMap k) := by
  rw [P1.awayι_comp_structMap, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    (isStandardSmoothOfRelativeDimension_chartAlgHom k i)

/-- `ℙ¹` is smooth of relative dimension one over `k`. -/
instance smoothOfRelativeDimension_P1 :
    SmoothOfRelativeDimension 1 (P1 k ↘ Spec (CommRingCat.of k)) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension 1)
    (P1.coordCover k).openCover]
  exact fun i ↦ smoothOfRelativeDimension_awayι_comp_structMap k i

/-- `ℙ¹` is geometrically integral over `k`: every base change to a field `K` is `ℙ¹_K`. -/
instance geometricallyIntegral_P1 :
    GeometricallyIntegral (P1 k ↘ Spec (CommRingCat.of k)) := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  have e : P1 K ≅ Y := IsPullback.isoIsPullback _ _ (P1.isPullback_mapOfAlgebra k K) h
  exact IsIntegral.of_isIso e.hom

/-- ℙ¹ is a smooth proper geometrically integral curve. -/
instance isCurveOver_P1 : IsCurveOver k (P1 k) :=
  { toSmoothOfRelativeDimension := smoothOfRelativeDimension_P1 k
    toIsProper := inferInstance
    toGeometricallyIntegral := geometricallyIntegral_P1 k }

/-- Each marked point of `ℙ¹` has degree at least one. -/
lemma one_le_pointDegree_of_mem_markedPoints {x : P1 k} (hx : x ∈ markedPoints k) :
    1 ≤ Anabelian.pointDegree k (P1 k) x := by
  letI := Anabelian.residueFieldAlgebra k (P1 k) x
  haveI := finite_residueField k (X := P1 k) (isClosed_singleton_markedPoint k hx)
  exact Module.finrank_pos

/-- The three marked points 0, 1, ∞ give `3 ≤ r(ℙ¹ ∖ {0,1,∞})`. -/
theorem three_le_cuspDegree_puncturedLine :
    3 ≤ Anabelian.cuspDegree k (P1 k) (puncturedLine k) := by
  have hc : ((puncturedLine k : Set (P1 k)))ᶜ = markedPoints k := by simp
  unfold Anabelian.cuspDegree
  rw [hc, markedPoints, finsum_mem_insert _ (by simp [P1.zero_ne_one k, P1.zero_ne_infty k])
    (Set.toFinite _), finsum_mem_insert _ (by simp [P1.one_ne_infty k]) (Set.toFinite _),
    finsum_mem_singleton]
  have h₀ := one_le_pointDegree_of_mem_markedPoints k (zero_mem_markedPoints k)
  have h₁ := one_le_pointDegree_of_mem_markedPoints k (one_mem_markedPoints k)
  have h₂ := one_le_pointDegree_of_mem_markedPoints k (infty_mem_markedPoints k)
  omega

end CurvesJacobian.Cusp
