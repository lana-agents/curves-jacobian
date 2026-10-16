/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Place
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Inertia fixes Kummer roots of functions with order divisible by `n`

Let `k` be an algebraically closed field, `K/k` a function field of one variable, `Ω/K` a field
extension, `P` a place of `K/k` and `W` a valuation subring of `Ω` lying over `P`. An
automorphism `σ` of `Ω/K` is *inertial at `W`* (`CurvesJacobian.IsInertial`) if it maps `W` into
itself and acts trivially on the residue field of `W` (`σ x - x ∈ 𝔪_W` for `x ∈ W`).

* `CurvesJacobian.inertial_fixes_kummerRoot`: if `n` is invertible in `k`, `yⁿ = f` in `Ω` and
  `n ∣ ord_P f`, then every `σ` inertial at `W` fixes `y`.

This is the "unramified" half of the Kummer criterion `K(f^{1/n})/K` unramified at `P` iff
`n ∣ ord_P f` (cf. Milne, *Abelian Varieties*, III.9.2). Proof: write `f = πⁿᵐ u` with `u` a
`P`-unit, so `z = y/πᵐ` is a `W`-unit with `zⁿ = u`; then `σ z = ζ z` with `ζ ∈ μₙ ⊆ k`, and
`ζ ≡ 1 mod 𝔪_W` forces `ζ = 1` because distinct elements of `k` stay distinct in the residue
field.
-/

open WeilCurves.FunctionField

namespace CurvesJacobian

variable {k K Ω : Type*} [Field k] [Field K] [Algebra k K] [Field Ω] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower k K Ω]

/-- `σ` is inertial at the valuation subring `W`: it preserves `W` and acts trivially on its
residue field. -/
def IsInertial (W : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x ∈ W, σ x ∈ W ∧ W.valuation (σ x - x) < 1

/-- `W` lies over the place `P`. -/
def LiesOverPlace (W : ValuationSubring Ω) (P : Place k K) : Prop :=
  ∀ x : K, algebraMap K Ω x ∈ W ↔ x ∈ P.1

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- In a valuation ring, an `n`-th root of a unit is a unit. -/
lemma valuation_eq_one_of_pow {W : ValuationSubring Ω} {z : Ω} {n : ℕ} (hn : n ≠ 0)
    (hz : W.valuation (z ^ n) = 1) : W.valuation z = 1 := by
  rw [map_pow] at hz
  rcases lt_trichotomy (W.valuation z) 1 with h | h | h
  · exact absurd hz (pow_lt_one₀ zero_le h hn).ne
  · exact h
  · exact absurd hz (one_lt_pow₀ h hn).ne'

omit [IsScalarTower k K Ω] in
/-- Over an algebraically closed `k`, every element of `Ω` algebraic over `k` is in `k`. -/
lemma exists_algebraMap_eq_of_isAlgebraic [IsAlgClosed k] {x : Ω} (hx : IsAlgebraic k x) :
    ∃ c : k, algebraMap k Ω c = x := by
  have hint := hx.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff (A := k) (x := x)).1
    (Polynomial.natDegree_eq_of_degree_eq_some hdeg)
  exact ⟨c, hc⟩

variable [IsAlgClosed k] [PerfectField k] [WeilCurves.FunctionField.IsFunctionField k K]

/-- **Inertia fixes Kummer roots of functions whose order is divisible by `n`.** -/
theorem inertial_fixes_kummerRoot {n : ℕ} (hn : (n : k) ≠ 0) {P : Place k K}
    {W : ValuationSubring Ω} (hW : LiesOverPlace W P) {f : K} (hf : f ≠ 0) {y : Ω}
    (hy : y ^ n = algebraMap K Ω f) (hdiv : (n : ℤ) ∣ P.ord f) {σ : Ω ≃ₐ[K] Ω}
    (hσ : IsInertial W σ) : σ y = y := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0, eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hy
    exact hf hy
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  obtain ⟨m, hm⟩ := hdiv
  -- the `P`-unit `u = f / π^(n m)`
  set u : K := f / π ^ ((n : ℤ) * m) with hu_def
  have hu0 : u ≠ 0 := div_ne_zero hf (zpow_ne_zero _ hπ0)
  have hord : P.ord u = 0 := by
    rw [hu_def, P.ord_div hf (zpow_ne_zero _ hπ0), P.ord_zpow, hπ, hm]
    ring
  obtain ⟨huP, huP'⟩ := (P.ord_eq_zero_iff hu0).1 hord
  -- `z = y / π^m` is a `W`-unit with `zⁿ = u`
  set z : Ω := y / (algebraMap K Ω π) ^ m with hz_def
  have hπΩ : algebraMap K Ω π ≠ 0 := (map_ne_zero_iff _ (algebraMap K Ω).injective).2 hπ0
  have hzn : z ^ n = algebraMap K Ω u := by
    rw [hz_def, div_pow, hy, hu_def, map_div₀, map_zpow₀, ← zpow_natCast, ← zpow_mul,
      mul_comm (m : ℤ)]
  have hvu : W.valuation (algebraMap K Ω u) = 1 := by
    have h1 : W.valuation (algebraMap K Ω u) ≤ 1 := (W.valuation_le_one_iff _).2 ((hW u).2 huP)
    have h2 : W.valuation (algebraMap K Ω u)⁻¹ ≤ 1 := by
      rw [← map_inv₀]; exact (W.valuation_le_one_iff _).2 ((hW u⁻¹).2 huP')
    rw [map_inv₀] at h2
    have hne : W.valuation (algebraMap K Ω u) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact (map_ne_zero_iff _ (algebraMap K Ω).injective).2 hu0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)
  have hvz : W.valuation z = 1 := valuation_eq_one_of_pow hn0 (by rw [hzn]; exact hvu)
  have hzW : z ∈ W := (W.valuation_le_one_iff _).1 hvz.le
  -- `σ y = ζ y` with `ζⁿ = 1`
  set ζ : Ω := σ y / y with hζ_def
  have hσy : σ y = ζ * y := by rw [hζ_def, div_mul_cancel₀ _ hy0]
  have hζn : ζ ^ n = 1 := by
    rw [hζ_def, div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self]
    rw [← hy]; exact pow_ne_zero _ hy0
  have hσz : σ z = ζ * z := by
    rw [hz_def, map_div₀, map_zpow₀, AlgEquiv.commutes, hσy, mul_div_assoc]
  -- `ζ` is a constant
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (k := k)
    (⟨Polynomial.X ^ n - 1, Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn0) 1,
      by simp [hζn]⟩ : IsAlgebraic k ζ)
  -- inertia: `v((ζ - 1) z) < 1`
  have hin := (hσ z hzW).2
  rw [hσz, ← sub_one_mul, map_mul, hvz, mul_one] at hin
  by_contra hne
  have hζ1 : ζ ≠ 1 := by
    intro h; apply hne; rw [hσy, h, one_mul]
  have hc1 : c - 1 ≠ 0 := by
    intro h; apply hζ1; rw [← hc, sub_eq_zero.1 h, map_one]
  -- constants are `W`-units
  have hk : ∀ d : k, algebraMap k Ω d ∈ W := fun d ↦ by
    rw [IsScalarTower.algebraMap_apply k K Ω]
    exact (hW _).2 (P.algebraMap_mem d)
  have hv1 : W.valuation (ζ - 1) = 1 := by
    have e1 : ζ - 1 = algebraMap k Ω (c - 1) := by rw [map_sub, hc, map_one]
    have e2 : (ζ - 1)⁻¹ = algebraMap k Ω (c - 1)⁻¹ := by rw [e1, map_inv₀]
    have h1 := (W.valuation_le_one_iff _).2 (e1 ▸ hk (c - 1))
    have h2 := (W.valuation_le_one_iff _).2 (e2 ▸ hk (c - 1)⁻¹)
    rw [map_inv₀] at h2
    have hne' : W.valuation (ζ - 1) ≠ 0 := by
      rw [Valuation.ne_zero_iff, e1]
      exact (map_ne_zero_iff _ (algebraMap k Ω).injective).2 hc1
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne')).1 h2)
  rw [hv1] at hin
  exact lt_irrefl _ hin

end CurvesJacobian
