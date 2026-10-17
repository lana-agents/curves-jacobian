/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.CurveCharts
import CurvesJacobian.Scheme.CurvePic

/-!
# Every proper open subset of a curve is a chart `π⁻¹ D₊(X₁)`

Let `X` be a curve over an algebraically closed (more generally perfect) field `k`. For a rational
function `τ` and `π = toP1 τ : X ⟶ ℙ¹`:

* `CurvesJacobian.mem_chartOne_iff`: `x ∈ π⁻¹ D₊(X₁)` iff `τ ∈ 𝒪_{X,x}` (`τ` transcendental).
  The direction `⇐` uses the uniqueness part of the valuative criterion for the separated
  scheme `ℙ¹`: the morphisms `Spec 𝒪_{X,x} ⟶ X ⟶ ℙ¹` and `Spec 𝒪_{X,x} ⟶ D₊(X₁) ⟶ ℙ¹`
  (coordinate `τ`) agree on the generic point.
* `CurvesJacobian.exists_not_mem_place`: for every place `P` of a function field `K/k` there is
  `g ∈ K` with a pole exactly at `P` (Riemann–Roch: `ℓ(nP) > ℓ((n-1)P)` for `n ≫ 0`), and
  `CurvesJacobian.exists_poles_eq`: for a finite set `Z` of places there is `f` with poles
  exactly at `Z` (sum of such `g`).
* `CurvesJacobian.exists_chartOne_eq`: an open `U ≠ X` with finite complement is
  `π⁻¹ D₊(X₁)` for a transcendental `τ` (with poles exactly at `X ∖ U`); in particular it is
  affine with ring of functions the integral closure of `k[τ]` in `K(X)`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian

section Places

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

/-- **A function with a pole exactly at `P`** (Riemann–Roch). -/
theorem exists_not_mem_place (P : Place k K) :
    ∃ g : K, g ∉ P.1 ∧ ∀ Q : Place k K, Q ≠ P → g ∈ Q.1 := by
  set N : ℕ := 2 * (genus k K).natAbs + 2
  set A : Divisor k K := Finsupp.single P (N : ℤ)
  set A' : Divisor k K := Finsupp.single P ((N : ℤ) - 1)
  have hdeg : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hg : genus k K ≤ (genus k K).natAbs := Int.le_natAbs
  have hN : (N : ℤ) = 2 * ((genus k K).natAbs : ℤ) + 2 := by push_cast [N]; ring
  have hA : 2 * genus k K - 2 < A.deg := by
    rw [Divisor.deg_single]
    have := le_mul_of_one_le_right (show (0 : ℤ) ≤ N by positivity) hdeg
    omega
  have hA' : 2 * genus k K - 2 < A'.deg := by
    rw [Divisor.deg_single]
    have := le_mul_of_one_le_right (show (0 : ℤ) ≤ N - 1 by omega) hdeg
    omega
  have hlt : Divisor.ell A' < Divisor.ell A := by
    have h1 := ell_eq_of_deg_gt hA
    have h2 := ell_eq_of_deg_gt hA'
    rw [Divisor.deg_single] at h1 h2
    have : (Divisor.ell A' : ℤ) < Divisor.ell A := by nlinarith
    exact_mod_cast this
  have hle : A' ≤ A := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ; simp [A, A']
    · simp [A, A', Ne.symm hQ]
  obtain ⟨f, hfA, hfA'⟩ : ∃ f ∈ Divisor.L A, f ∉ Divisor.L A' := by
    by_contra h
    push Not at h
    have : Divisor.L A ≤ Divisor.L A' := h
    exact absurd (Submodule.finrank_mono this) (not_le.2 hlt)
  have hf0 : f ≠ 0 := fun h ↦ hfA' (h ▸ (Divisor.L A').zero_mem)
  have hfA2 := (Divisor.mem_L.1 hfA).resolve_left hf0
  have hreg : ∀ Q : Place k K, Q ≠ P → f ∈ Q.1 := by
    intro Q hQ
    have := hfA2 Q
    simp only [A, Finsupp.single_apply, Ne.symm hQ, if_false, neg_zero] at this
    exact (Place.mem_iff_ord_nonneg Q).2 (Or.inr this)
  refine ⟨f, fun hfP ↦ hfA' (Divisor.mem_L.2 (Or.inr fun Q ↦ ?_)), hreg⟩
  by_cases hQ : Q = P
  · rw [hQ]
    have h0 := (Place.mem_iff_ord_nonneg P).1 hfP
    rcases h0 with h0 | h0
    · exact absurd h0 hf0
    · simp only [A', Finsupp.single_eq_same]
      have : (1 : ℤ) ≤ N := by omega
      omega
  · have := hfA2 Q
    simpa [A, A', Finsupp.single_apply, Ne.symm hQ] using this

/-- **A function with poles exactly at a finite set `Z` of places.** -/
theorem exists_poles_eq (Z : Finset (Place k K)) :
    ∃ f : K, ∀ Q : Place k K, f ∈ Q.1 ↔ Q ∉ Z := by
  classical
  choose g hgP hgQ using fun P : Place k K ↦ exists_not_mem_place P
  refine ⟨∑ z ∈ Z, g z, fun Q ↦ ⟨fun hQ hQZ ↦ ?_, fun hQZ ↦ ?_⟩⟩
  · rw [← Finset.add_sum_erase Z g hQZ] at hQ
    have hrest : ∑ z ∈ Z.erase Q, g z ∈ Q.1 :=
      Q.1.sum_mem fun z hz ↦ hgQ z Q (Finset.ne_of_mem_erase hz).symm
    exact hgP Q (by simpa using Q.1.sub_mem hQ hrest)
  · exact Q.1.sum_mem fun z hz ↦ hgQ z Q fun h ↦ hQZ (h ▸ hz)

end Places

section Curve

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

variable (k) in
/-- `𝒪_{X,x}` as a valuation subring of `K(X)` on a curve. -/
abbrev stalkVS (x : X) : ValuationSubring X.functionField :=
  stalkValuationSubring (valuationRing_stalk_of_isCurveOver k X) x

variable (k) in
/-- **`x ∈ π⁻¹ D₊(X₁)` iff `τ` is regular at `x`.** -/
theorem mem_chartOne_iff {τ : X.functionField} (hτ : Transcendental k τ) (x : X) :
    x ∈ chartOne k X τ ↔ τ ∈ stalkVS k x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (mem_range_germ_chartOne_iff hτ τ).2
      (isIntegral_algebraMap (x := (⟨τ, Algebra.self_mem_adjoin_singleton k τ⟩ :
        Algebra.adjoin k {τ})))
    exact ⟨X.presheaf.germ _ x hx a, by rw [Scheme.algebraMap_germ_eq_germToFunctionField, ha]⟩
  · intro hτx
    have hX := valuationRing_stalk_of_isCurveOver k X
    set O := stalkVS k x
    have hadjO : ∀ z ∈ Algebra.adjoin k {τ}, z ∈ O := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem y hy => obtain rfl := Set.mem_singleton_iff.mp hy; exact hτx
      | algebraMap c => exact algebraMap_mem_stalkValuationSubring k _ x c
      | add y z _ _ hy hz => exact add_mem hy hz
      | mul y z _ _ hy hz => exact mul_mem hy hz
    let φ : HomogeneousLocalization.Away (P1Grading k) (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
        →+* O :=
      (P1.awayEval k τ).codRestrict O.toSubring fun a ↦ hadjO _ (awayEval_mem_adjoin k τ a)
    let g₁ : Spec (CommRingCat.of O) ⟶ P1 k :=
      Spec.map (stalkToValuationSubring hX x rfl) ≫ X.fromSpecStalk x ≫ toP1 k X τ
    let g₂ : Spec (CommRingCat.of O) ⟶ P1 k := Spec.map (CommRingCat.ofHom φ) ≫ chartι₁ k
    have hgen₂ : Spec.map (CommRingCat.ofHom (algebraMap O X.functionField)) ≫ g₂ =
        genericSpec X ≫ toP1 k X τ := by
      rw [genericSpec, fromSpecStalk_comp_toP1_one, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hgen₁ : Spec.map (CommRingCat.ofHom (algebraMap O X.functionField)) ≫ g₁ =
        genericSpec X ≫ toP1 k X τ :=
      SpecMap_stalkToValuationSubring_fromSpecStalk_assoc hX x rfl _
    haveI : (P1 k).IsSeparated := isSeparated_P1 k
    let S : ValuativeCommSq (terminal.from (P1 k)) :=
      { R := O, K := X.functionField, i₁ := genericSpec X ≫ toP1 k X τ,
        i₂ := terminal.from _, commSq := ⟨terminal.hom_ext _ _⟩ }
    have hU := IsSeparated.valuativeCriterion (terminal.from (P1 k)) S
    let l₁ : S.commSq.LiftStruct :=
      { l := g₁, fac_left := hgen₁, fac_right := terminal.hom_ext _ _ }
    let l₂ : S.commSq.LiftStruct :=
      { l := g₂, fac_left := hgen₂, fac_right := terminal.hom_ext _ _ }
    have hl : g₁ = g₂ := congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
    have hx1 := stalkToValuationSubring_closedPoint hX x (O := O) rfl
    have e1 : toP1 k X τ x = g₂ (IsLocalRing.closedPoint O) := by
      rw [← hl, ← hx1]
      simp only [g₁, Scheme.Hom.comp_apply]
    change toP1 k X τ x ∈ Set.range (chartι₁ k)
    rw [e1]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

variable (k) in
/-- **An open `U ≠ X` with finite complement is a chart** `π⁻¹ D₊(X₁)` of a transcendental
rational function (with poles exactly at `X ∖ U`). -/
theorem exists_chartOne_eq (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ.Finite)
    (hne : U ≠ ⊤) : ∃ τ : X.functionField, Transcendental k τ ∧ U = chartOne k X τ := by
  classical
  have hgen : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  -- the removed points, as closed points
  have hZ : {x : ClosedPoint X | x.1 ∉ U}.Finite :=
    hU.preimage (Subtype.val_injective.injOn)
  set Z : Finset (ClosedPoint X) := hZ.toFinset
  have hmemZ : ∀ x : ClosedPoint X, x ∈ Z ↔ x.1 ∉ U := fun x ↦ by simp [Z]
  obtain ⟨f, hf⟩ := exists_poles_eq (k := k) (K := X.functionField)
    (Z.map (curvePlaceEquiv k X).toEmbedding)
  have hfx : ∀ x : ClosedPoint X, f ∈ stalkVS k x.1 ↔ x.1 ∈ U := by
    intro x
    have := hf (curvePlaceEquiv k X x)
    rw [curvePlaceEquiv_apply] at this
    rw [this, Finset.mem_map_equiv, Equiv.symm_apply_apply, hmemZ, not_not]
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ U := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun y _ ↦ h y)
  have hyg : y ≠ genericPoint X := fun h ↦ hy (h ▸ hgen)
  have hτ : Transcendental k f := by
    intro halg
    have := (Place.isAlgebraic_iff_forall_mem.1 halg) (curvePlaceEquiv k X ⟨y, hyg⟩)
    rw [curvePlaceEquiv_apply] at this
    exact hy ((hfx ⟨y, hyg⟩).1 this)
  refine ⟨f, hτ, ?_⟩
  ext x
  change x ∈ U ↔ x ∈ chartOne k X f
  rw [mem_chartOne_iff k hτ]
  by_cases hx : x = genericPoint X
  · subst hx
    refine ⟨fun _ ↦ ?_, fun _ ↦ hgen⟩
    rw [stalkVS, stalkValuationSubring_genericPoint]
    exact ValuationSubring.mem_top _
  · exact (hfx ⟨x, hx⟩).symm

end Curve

end CurvesJacobian
