/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.FunctionField.DivisorEval

/-!
# A divisor of degree `g − 1` with `ℓ = 0` (JAC J2: the theta divisor is a divisor)

For a function field `K` over an algebraically closed field `κ` of genus `g`:

* `ell_zero_eq_one`: `ℓ(0) = 1`;
* **`exists_ell_sub_single`**: if `ℓ(A) ≠ 0`, removing a suitable place drops `ℓ` by exactly one
  (any place outside the supports of `A` and of `div f`, `0 ≠ f ∈ L(A)`);
* `exists_effective_ell_sub`: for `m ≤ ℓ(A)` there is an effective `E` of degree `m` with
  `ℓ(A − E) = ℓ(A) − m`;
* **`exists_deg_eq_genus_sub_one_ell_eq_zero`**: there is a divisor `D` of degree `g − 1` with
  `ℓ(D) = 0`. Construction: `E = P₁ + ⋯ + P_g` with `ℓ(W − E) = 0` (from `ℓ(W) = g`), so
  `ℓ(E) = 1` by Riemann–Roch (Stichtenoth §1.5, weil-curves `riemannRoch`), then `D = E − Q`
  with `ℓ(E − Q) = 0`.

This is the point of `J` off the theta divisor `Θ = V(Fit₀ R¹p_*(𝒫 ⊗ κ))`: at the point
`[D] ⊗ κ⁻¹` the fibre `H¹ = H⁰ = 0`, so the local equation `det δ` of `Θ` is a unit there and `Θ`
is an effective Cartier divisor on the integral scheme `J`.
-/

open WeilCurves.FunctionField WeilCurves.FunctionField.Divisor

namespace CurvesJacobian.FunctionField

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

lemma deg_single_one (P : Place κ K) : deg (Finsupp.single P (1 : ℤ) : Divisor κ K) = 1 := by
  rw [deg_single, Place.deg_eq_one]
  simp

/-- `ℓ(A + P) ≤ ℓ(A) + 1`. -/
lemma ell_add_single_le (A : Divisor κ K) (P : Place κ K) :
    ell (A + Finsupp.single P 1) ≤ ell A + 1 := by
  have := (step A P).2
  rwa [Place.deg_eq_one] at this

variable (κ K) in
/-- `ℓ(0) = 1` over an algebraically closed field. -/
theorem ell_zero_eq_one : ell (0 : Divisor κ K) = 1 := by
  have := infinite_place κ K
  obtain ⟨P⟩ := (inferInstance : Nonempty (Place κ K))
  have h1 := ell_add_single_le (-Finsupp.single P 1) P
  rw [neg_add_cancel, ell_eq_zero_of_deg_neg (A := -Finsupp.single P 1)
    (by rw [deg_neg, deg_single_one]; omega)] at h1
  have h2 := ell_zero_pos (k := κ) (K := K)
  omega

/-- **Removing a general place drops `ℓ` by one.** -/
theorem exists_ell_sub_single (A : Divisor κ K) (h : ell A ≠ 0) :
    ∃ P : Place κ K, ell (A - Finsupp.single P 1) + 1 = ell A := by
  classical
  obtain ⟨f, hfL, hf0⟩ := exists_ne_zero_mem_L h
  have := infinite_place κ K
  obtain ⟨P, hP⟩ := Infinite.exists_notMem_finset (A.support ∪ (div κ f).support)
  rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff,
    div_apply] at hP
  refine ⟨P, ?_⟩
  have hle : L (A - Finsupp.single P 1) ≤ L A :=
    L_mono (sub_le_self _ (Finsupp.single_nonneg.mpr zero_le_one))
  have hlt : L (A - Finsupp.single P 1) < L A := by
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have hf' : f ∈ L (A - Finsupp.single P 1) := heq ▸ hfL
    rw [mem_L_of_ne_zero hf0] at hf'
    have := hf' P
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_eq_same, div_apply, hP.1, hP.2] at this
    omega
  have h1 : ell (A - Finsupp.single P 1) < ell A := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := ell_add_single_le (A - Finsupp.single P 1) P
  rw [sub_add_cancel] at h2
  omega

/-- For `m ≤ ℓ(A)` there is an effective divisor `E` of degree `m` with `ℓ(A − E) = ℓ(A) − m`. -/
theorem exists_effective_ell_sub (A : Divisor κ K) :
    ∀ m : ℕ, m ≤ ell A → ∃ E : Divisor κ K, 0 ≤ E ∧ deg E = m ∧ ell (A - E) + m = ell A
  | 0, _ => ⟨0, le_rfl, by simp, by simp⟩
  | m + 1, hm => by
    obtain ⟨E, hE, hdeg, hell⟩ := exists_effective_ell_sub A m (by omega)
    obtain ⟨P, hP⟩ := exists_ell_sub_single (A - E) (by omega)
    refine ⟨E + Finsupp.single P 1, add_nonneg hE (Finsupp.single_nonneg.mpr zero_le_one), ?_, ?_⟩
    · rw [deg_add, hdeg, deg_single_one]
      push_cast
      ring
    · rw [sub_add_eq_sub_sub]
      omega

variable (κ K) in
/-- **A divisor of degree `g − 1` with `ℓ(D) = 0`.** -/
theorem exists_deg_eq_genus_sub_one_ell_eq_zero :
    ∃ D : Divisor κ K, deg D = genus κ K - 1 ∧ ell D = 0 := by
  have hW : (ell (canonical κ K) : ℤ) = genus κ K := by
    rw [ell_canonical, ell_zero_eq_one]
    push_cast
    ring
  obtain ⟨E, -, hdeg, hell⟩ := exists_effective_ell_sub (canonical κ K) (ell (canonical κ K)) le_rfl
  have h0 : ell (canonical κ K - E) = 0 := by omega
  have hRR := riemannRoch E
  rw [h0, hdeg, hW] at hRR
  have hE1 : ell E = 1 := by omega
  obtain ⟨Q, hQ⟩ := exists_ell_sub_single E (by omega)
  refine ⟨E - Finsupp.single Q 1, ?_, by omega⟩
  rw [deg_sub, hdeg, deg_single_one, hW]

end CurvesJacobian.FunctionField
