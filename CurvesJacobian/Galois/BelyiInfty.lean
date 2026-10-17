/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.ChartOfOpen
import Belyi.Marked

/-!
# Belyi maps with a prescribed fibre over `∞`

Let `X` be a curve over an algebraically closed field `k` of characteristic zero that is algebraic
over `ℚ`, and let `D` be a nonempty finite set of closed points of `X`. Then there is a Belyi map
`f : X ⟶ ℙ¹_k` (finite, branched only over `{0, 1, ∞}`) with **`f⁻¹(∞) = D` exactly**
(`CurvesJacobian.exists_isBelyiMap_preimage_infty_eq`).

Construction: a rational function `τ` with poles exactly at `D` (Riemann–Roch,
`CurvesJacobian.exists_chartOne_eq` applied to `U = X ∖ D`) gives `f₀ = toP1 τ` with
`f₀⁻¹(D₊(X₁)) = X ∖ D`, i.e. `f₀⁻¹(∞) = D`; then `f = f₀ ≫ polynomialSelfMap ĝ` for belyi's
reduction polynomial `ĝ` (B6∘B7, `Belyi.exists_aeval_mem_and_critVal_mem_zeroOne`) fed with the
affine branch coordinates of `f₀`, exactly as in the forward direction of Belyi's theorem
(`Belyi.exists_isBelyiMap_marked_isOver_of_isCurveOver`). A polynomial self-map fixes `∞`
(`Belyi.P1.polynomialSelfMap_infty`) and maps affine points to affine points
(`Belyi.P1.polynomialSelfMap_point`), so `f⁻¹(∞) = f₀⁻¹(∞) = D`.

This is the Belyi map used for the topological computation `π₁((X ∖ D)^an) ≅ Π_{g,r}` (r ≥ 1):
`X ∖ D = f⁻¹(𝔸¹)` is then a branched cover of `𝔸¹` unramified over `𝔸¹ ∖ {0,1}`.
-/

open CategoryTheory AlgebraicGeometry Belyi MvPolynomial

universe u

noncomputable section

namespace CurvesJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

section P1

variable (k : Type u) [Field k]

/-- **`D₊(X₁) = ℙ¹ ∖ {∞}`.** -/
lemma mem_range_awayι_one_iff (y : P1 k) :
    y ∈ Set.range (Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos).base ↔
      y ≠ P1.infty k := by
  have hrange : y ∈ Set.range
      (Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos).base ↔
      y ∈ Proj.basicOpen (P1Grading k) (X 1) := by
    rw [← Proj.opensRange_awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos]
    rfl
  rw [hrange]
  constructor
  · rintro hy rfl
    apply hy
    change (X 1 : MvPolynomial (Fin 2) k) ∈ (P1.infty k).asHomogeneousIdeal
    rw [← HomogeneousIdeal.mem_iff, P1.infty, P1.mkPoint_asIdeal]
    exact Ideal.subset_span rfl
  · intro hne h
    exact hne (P1.eq_infty_of_X1_mem k (HomogeneousIdeal.mem_iff.mpr h))

/-- Points with an affine coordinate are not `∞`. -/
lemma point_base_ne_infty {R : Type u} [CommRing R] [Algebra k R] (t : R)
    (z : Spec (CommRingCat.of R)) : (P1.point k t).base z ≠ P1.infty k := by
  rw [← mem_range_awayι_one_iff, P1.point, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

variable [IsAlgClosed k]

/-- A polynomial self-map of `ℙ¹` sends no point other than `∞` to `∞`. -/
lemma polynomialSelfMap_eq_infty_iff (g : Polynomial k) (hd : 0 < g.natDegree) (y : P1 k) :
    P1.polynomialSelfMap k g hd y = P1.infty k ↔ y = P1.infty k := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ P1.polynomialSelfMap_infty k g hd⟩
  by_contra hy
  by_cases hgen : y = _root_.genericPoint (P1 k)
  · have hs : Transcendental k (RatFunc.X : RatFunc k) := by
      rw [← RatFunc.algebraMap_X]
      exact (transcendental_algebraMap_iff (RatFunc.algebraMap_injective k)).2
        (Polynomial.transcendental_X k)
    have hgen' : _root_.genericPoint (P1 k) =
        P1.point k (RatFunc.X : RatFunc k) (IsLocalRing.closedPoint (RatFunc k)) :=
      (genericPoint_spec (P1 k)).eq (P1.closure_point_eq_univ k hs)
    rw [hgen, hgen', ← Scheme.Hom.comp_apply, P1.point_comp_polynomialSelfMap] at h
    exact point_base_ne_infty k _ _ h
  · rcases P1.exists_eq_point_or_eq_infty_of_ne_genericPoint k y hgen with ⟨a, rfl⟩ | h'
    · rw [P1.polynomialSelfMap_point_closedPoint] at h
      exact point_base_ne_infty k _ _ h
    · exact hy h'

end P1

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

omit [IsAlgClosed k] in
/-- **`(toP1 τ)⁻¹(∞)` is the complement of the chart `chartOne τ`.** -/
lemma toP1_eq_infty_iff (τ : X.functionField) (x : X) :
    toP1 k X τ x = P1.infty k ↔ x ∉ chartOne k X τ := by
  rw [← not_iff_not, not_not]
  exact (mem_range_awayι_one_iff k _).symm.trans Iff.rfl

/-- **Belyi maps with `f⁻¹(∞) = D`.** For a curve `X` over `k = ℚ̄` (alg. closed, char 0, algebraic
over `ℚ`) and a nonempty finite set `D` of closed points of `X`, there is a Belyi map
`f : X ⟶ ℙ¹_k` over `k` whose fibre over `∞` is exactly `D`. -/
theorem exists_isBelyiMap_preimage_infty_eq [Algebra.IsAlgebraic ℚ k] (D : Set X)
    (hDfin : D.Finite) (hDne : D.Nonempty) (hD : ∀ x ∈ D, x ≠ genericPoint X) :
    ∃ f : X ⟶ P1 k, IsBelyiMap k f ∧ (∀ x : X, f.base x = P1.infty k ↔ x ∈ D) ∧
      f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k) := by
  classical
  -- `U := X ∖ D` is an open with finite nonempty complement.
  have hDcl : IsClosed D := by
    have := hDfin.isClosed_biUnion (fun x hx ↦ isClosed_closedPoint k X ⟨x, hD x hx⟩)
    simpa using this
  let U : X.Opens := ⟨Dᶜ, hDcl.isOpen_compl⟩
  haveI : Nonempty U := ⟨⟨genericPoint X, fun h ↦ hD _ h rfl⟩⟩
  have hUc : (U : Set X)ᶜ.Finite := by simpa [U] using hDfin
  have hUne : U ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hDne
    intro h
    have hxU : x ∈ (U : Set X) := by rw [h]; trivial
    exact hxU hx
  obtain ⟨τ, hτ, hUτ⟩ := exists_chartOne_eq k U hUc hUne
  -- `f₀ = toP1 τ` is finite surjective with `f₀⁻¹(∞) = D`.
  set f₀ := toP1 k X τ with hf₀
  haveI : IsFinite f₀ := isFinite_toP1 hτ
  have hf₀surj : Function.Surjective f₀.base :=
    (isFinite_and_surjective_homOfFunctionField_of_isCurveOver k X hτ).2
  haveI : IsDominant f₀ := ⟨hf₀surj.denseRange⟩
  haveI : IsNoetherian (P1 k) := isNoetherian_of_over (P1 k) (Spec (CommRingCat.of k))
  haveI : LocallyOfFinitePresentation f₀ := inferInstance
  haveI : IsNoetherian X := isNoetherian_of_over X (Spec (CommRingCat.of k))
  have hf₀D : ∀ x : X, f₀.base x = P1.infty k ↔ x ∈ D := by
    intro x
    rw [toP1_eq_infty_iff, ← hUτ]
    change x ∉ Dᶜ ↔ x ∈ D
    simp
  have hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    fun x => krullDimLE_one_stalk_of_isCurveOver k X x
  -- B6∘B7 applied to the affine branch coordinates of `f₀`.
  obtain ⟨g, hgne, hgS, hgcrit⟩ :=
    exists_aeval_mem_and_critVal_mem_zeroOne (K := k) (P1.branchFinset k f₀ hdim)
  have hinj : Function.Injective (algebraMap ℚ k) := (algebraMap ℚ k).injective
  have hd : 0 < (g.map (algebraMap ℚ k)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hinj]
    exact Nat.pos_of_ne_zero hgne
  refine ⟨f₀ ≫ P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd, ?_, ?_, ?_⟩
  · refine P1.isBelyiMap_comp_polynomialSelfMap k (g.map (algebraMap ℚ k)) hd f₀ ?_ ?_
    · refine P1.polynomialSelfMap_image_branch_subset_markedPoints k f₀ hdim
        (g.map (algebraMap ℚ k)) hd ?_
      intro s hs
      rw [Polynomial.aeval_map_algebraMap]
      exact hgS s hs
    · exact branch_map_polynomialSelfMap_subset_markedPoints hgne hgcrit hd
  · intro x
    rw [Scheme.Hom.comp_apply, polynomialSelfMap_eq_infty_iff, hf₀D]
  · rw [Category.assoc, P1.structMap_eq, P1.polynomialSelfMap_structMap, ← P1.structMap_eq]
    exact (Scheme.Hom.isOver_iff (S := Spec (CommRingCat.of k))).mp inferInstance

end CurvesJacobian
