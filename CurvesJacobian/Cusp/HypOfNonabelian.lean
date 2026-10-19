/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.SurfaceGroupAnyPoint
import CurvesJacobian.Cusp.CuspDegreeEq
import CurvesJacobian.Cusp.GenusBaseChange
import CurvesJacobian.Cusp.GenusLocAnEq

/-!
# Hyperbolicity from a non-commutative geometric fundamental group

The non-hyperbolic types `(g, r)` with `r ≥ 1` are `(0, 1)` and `(0, 2)` (`𝔸¹` and `𝔾_m`), and
for them `Π̂_{g,r}` is trivial resp. `ℤ̂`, in particular commutative. Hence:

* `CurvesJacobian.Cusp.commute_of_not_isHyperbolic`: if `(g, r)` is not hyperbolic and `r ≥ 1`,
  then the profinite completion of `Π_{g,r}` is commutative (`Π_{0,r+1}` is free on `r ≤ 1`
  generators, and the completion of a commutative group is commutative: the image of `G` is
  dense and the commutator condition is closed);
* `CurvesJacobian.Cusp.isHyperbolic_of_not_commute`: for a curve `X` over an algebraically
  closed field `k` of characteristic zero and `U ⊆ X` open with finite nonempty complement, if
  `π₁ᵉᵗ(U, ξ)` is not commutative then `(g(X), #(X ∖ U))` is hyperbolic;
* `CurvesJacobian.Cusp.two_lt_of_not_commute_baseChange`: over a field `K` of characteristic
  zero with algebraically closed `Ω ⊇ K`, if `π₁ᵉᵗ(U_Ω, ξ)` is not commutative then
  `2 < 2 g(X̄) + Σ_{c ∉ U} [κ(c) : K]`, with `g` the Riemann–Roch genus `curveGenus`
  (`CurvesJacobian.Cusp.curveGenus_baseChange`, `CurvesJacobian.Cusp.card_compl_eq_cuspDegree`);
* `CurvesJacobian.Cusp.two_lt_locAn_of_not_commute_baseChange`: the same with the genus
  `Belyi.Anabelian.curveGenus = dim H⁰(X̄, Ω¹)` of `Belyi.Anabelian.HypCurve.hyperbolic`
  (the two genera agree, `CurvesJacobian.Cusp.locAn_curveGenus_eq`).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi Pi1.Profinite ProfiniteGrp.ProfiniteCompletion

universe u

namespace CurvesJacobian.Cusp

/-! ### Group theory -/

/-- A free group on at most one generator is commutative. -/
lemma freeGroup_mul_comm_of_subsingleton {α : Type*} [Subsingleton α] (x y : FreeGroup α) :
    x * y = y * x := by
  obtain ⟨c, hc⟩ : ∃ c : FreeGroup α, Set.range (FreeGroup.of (α := α)) ⊆ {c} := by
    rcases isEmpty_or_nonempty α with h | h
    · exact ⟨1, by simp [Set.range_eq_empty]⟩
    · obtain ⟨a⟩ := h
      refine ⟨FreeGroup.of a, ?_⟩
      rintro _ ⟨b, rfl⟩
      rw [Subsingleton.elim b a]
      rfl
  have hle : (⊤ : Subgroup (FreeGroup α)) ≤ Subgroup.zpowers c := by
    rw [← FreeGroup.closure_range_of, Subgroup.closure_le]
    exact hc.trans (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers c))
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hle (Subgroup.mem_top x))
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hle (Subgroup.mem_top y))
  exact (Commute.zpow_zpow_self c m n).eq

/-- **The profinite completion of a commutative group is commutative**: the image of `G` is
dense and `{(x, y) | x y = y x}` is closed. -/
lemma completion_mul_comm {G : Type u} [Group G] (h : ∀ x y : G, x * y = y * x)
    (x y : completion (GrpCat.of G)) : x * y = y * x :=
  (denseRange (GrpCat.of G)).induction_on₂ (p := fun x y ↦ x * y = y * x)
    (isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst))
    (fun a b ↦ by
      change etaFn (GrpCat.of G) (a * b) = etaFn (GrpCat.of G) (b * a)
      rw [h a b])
    x y

lemma subsingleton_surfaceGen_zero {r : ℕ} (hr : r ≤ 1) : Subsingleton (Pi1.SurfaceGen 0 r) :=
  ⟨fun a b ↦ by
    cases a with
    | a i => exact i.elim0
    | b i => exact i.elim0
    | c i =>
      cases b with
      | a j => exact j.elim0
      | b j => exact j.elim0
      | c j => exact congrArg _ (Fin.ext (by have := i.2; have := j.2; omega))⟩

/-- **`Π̂_{g,r}` is commutative for non-hyperbolic `(g, r)` with `r ≥ 1`**, i.e. for `(0, 1)`
(trivial) and `(0, 2)` (`ℤ̂`). -/
theorem commute_of_not_isHyperbolic {g r : ℕ} (hr : 0 < r)
    (h : ¬ Pi1.SurfaceGroup.IsHyperbolic g r)
    (x y : completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g r)))) : x * y = y * x := by
  unfold Pi1.SurfaceGroup.IsHyperbolic at h
  obtain rfl : g = 0 := by omega
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  haveI := subsingleton_surfaceGen_zero (r := r) (by omega)
  refine completion_mul_comm (fun a b ↦ ?_) x y
  apply ULift.ext
  apply (Pi1.SurfaceGroup.freeEquiv (g := 0) (r := r)).injective
  rw [ULift.mul_down, ULift.mul_down, map_mul, map_mul]
  exact freeGroup_mul_comm_of_subsingleton _ _

/-! ### Curves over an algebraically closed field -/

section Geometric

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **A punctured curve with non-commutative `π₁ᵉᵗ` is hyperbolic.** For a curve `X` over an
algebraically closed field `k` of characteristic zero and `U ⊆ X` open with finite nonempty
complement, if `π₁ᵉᵗ(U, ξ)` is not commutative then `2 < 2 g(X) + #(X ∖ U)`. -/
theorem isHyperbolic_of_not_commute (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ U.toScheme)
    (h : ∃ a b : π₁ᵉᵗ(ξ), a * b ≠ b * a) :
    Pi1.SurfaceGroup.IsHyperbolic (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X)) := by
  by_contra hnh
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup (k := k) U hUfin hUne ξ
  have hr : 0 < Nat.card ((U : Set X)ᶜ : Set X) :=
    haveI := hUfin.to_subtype
    Nat.card_pos_iff.2 ⟨hUne.to_subtype, inferInstance⟩
  obtain ⟨a, b, hab⟩ := h
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact commute_of_not_isHyperbolic hr hnh _ _

end Geometric

/-! ### Curves over a field of characteristic zero -/

section Arithmetic

variable (K : Type u) [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsCurveOver K X]

/-- **Hyperbolicity over `K` from a non-commutative geometric `π₁ᵉᵗ`.** For a curve `X̄` over a
field `K` of characteristic zero, `Ω ⊇ K` algebraically closed and `U ⊆ X̄` a nonempty open with
nonempty complement, if `π₁ᵉᵗ(U_Ω, ξ)` is not commutative then
`2 < 2 g(X̄) + Σ_{c ∉ U} [κ(c) : K]`, `g` the (Riemann–Roch) genus `curveGenus`. -/
theorem two_lt_of_not_commute_baseChange (U : X.Opens) (hU : (U : Set X).Nonempty)
    (hc : (U : Set X)ᶜ.Nonempty)
    (ξ : Spec (.of Ω) ⟶ (baseChangeOpen K Ω U).toScheme)
    (h : ∃ a b : π₁ᵉᵗ(ξ), a * b ≠ b * a) :
    haveI := IsCurveOver.isIntegral K X
    2 < 2 * (curveGenus K X).toNat + Anabelian.cuspDegree K X U := by
  haveI := IsCurveOver.isIntegral K X
  haveI := IsCurveOver.isIntegral Ω (baseChange K Ω X)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : Nonempty (baseChangeOpen K Ω U) := (nonempty_baseChangeOpen K Ω hU).to_subtype
  have hhyp := isHyperbolic_of_not_commute (k := Ω) (X := baseChange K Ω X)
    (baseChangeOpen K Ω U) (compl_finite_baseChangeOpen K Ω hU)
    (compl_nonempty_baseChangeOpen K Ω hc) ξ h
  rw [card_compl_eq_cuspDegree_of_isCurveOver K Ω U hU, curveGenus_baseChange K Ω X] at hhyp
  exact hhyp

/-- **The hyperbolicity condition of `Belyi.Anabelian.HypCurve` from a non-commutative
geometric `π₁ᵉᵗ`**, for the genus `dim H⁰(X̄, Ω¹)` (positive whenever the Riemann–Roch genus is,
`CurvesJacobian.Cusp.locAn_curveGenus_pos`). -/
theorem two_lt_locAn_of_not_commute_baseChange (U : X.Opens) (hU : (U : Set X).Nonempty)
    (hc : (U : Set X)ᶜ.Nonempty)
    (ξ : Spec (.of Ω) ⟶ (baseChangeOpen K Ω U).toScheme)
    (h : ∃ a b : π₁ᵉᵗ(ξ), a * b ≠ b * a) :
    haveI := IsCurveOver.isIntegral K X
    2 < 2 * Anabelian.curveGenus K X + Anabelian.cuspDegree K X U := by
  haveI := IsCurveOver.isIntegral K X
  have hg := locAn_curveGenus_pos K X
  have h1 := two_lt_of_not_commute_baseChange K Ω U hU hc ξ h
  have h2 : 0 < Anabelian.cuspDegree K X U := by
    rw [← card_compl_eq_cuspDegree_of_isCurveOver K Ω U hU]
    haveI := (compl_finite_baseChangeOpen K Ω hU).to_subtype
    exact Nat.card_pos_iff.2 ⟨(compl_nonempty_baseChangeOpen K Ω hc).to_subtype, inferInstance⟩
  rcases Nat.eq_zero_or_pos (curveGenus K X).toNat with h0 | h0
  · omega
  · have := hg h0
    omega

end Arithmetic

end CurvesJacobian.Cusp
