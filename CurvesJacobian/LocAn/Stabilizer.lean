/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.FixedPlaceOrder
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Stabilisers of places: cyclicity and the genus-zero case

Let `K/κ` be a function field of one variable over an algebraically closed field `κ` of
characteristic `0`.

* **`CurvesJacobian.LocAn.exists_eq_pow_of_commute`**: let `ι, τ ∈ Aut_κ(K)` commute and fix a
  place `P`, `ι` of order `e`, `τ^m = 1` with `m ∣ e`. Then `τ` is a power of `ι`. (The derivative
  `u(ι, P)` is a primitive `e`-th root of unity, `u(τ, P)^e = 1`, so `u(τ, P) = u(ι^a, P)` and
  `τ = ι^a` by `eq_of_derivAt_eq`.) This is the step (G3) of the MR7 uniqueness route: an
  automorphism of finite order commuting with a cyclic inertia group of order divisible by its
  order lies in that inertia group.
* **`CurvesJacobian.LocAn.eq_one_of_genus_eq_zero`**: on a curve of genus `0`, an automorphism
  fixing three distinct places is the identity (`L(P) = κ ⊕ κ s` with `s : X ≅ ℙ¹`, `σ s = v s + b`,
  and two further fixed values force `v = 1`, `b = 0`). This is (F3).
-/

open WeilCurves.FunctionField WeilCurves.FunctionField.Divisor Module
open scoped IntermediateField

namespace CurvesJacobian.LocAn

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [CharZero κ] [Field K] [Algebra κ K]
  [IsFunctionField κ K]

/-- **An automorphism of order dividing `e` commuting with an automorphism `ι` of order `e`, both
fixing a place, is a power of `ι`.** -/
theorem exists_eq_pow_of_commute {ι τ : K ≃ₐ[κ] K} {P : Place κ K} (hι : Fixes ι P)
    (hτ : Fixes τ P) (hcomm : Commute ι τ) {e m : ℕ} (he : 0 < e) (hιe : orderOf ι = e)
    (hm : 0 < m) (hτm : τ ^ m = 1) (hme : m ∣ e) : ∃ a : ℕ, τ = ι ^ a := by
  haveI : NeZero e := ⟨he.ne'⟩
  have hιe' : ι ^ e = 1 := by rw [← hιe]; exact pow_orderOf_eq_one ι
  have hprim : IsPrimitiveRoot (derivAt ι P) e := by
    refine ⟨?_, fun l hl ↦ ?_⟩
    · rw [← derivAt_pow hι, hιe', derivAt_one]
    · rw [← derivAt_pow hι] at hl
      have hpow : (ι ^ l) ^ e = 1 := by rw [← pow_mul, mul_comm, pow_mul, hιe', one_pow]
      have := eq_one_of_fixes_of_derivAt_eq_one (hι.pow l) hl he hpow
      rw [← hιe]
      exact orderOf_dvd_of_pow_eq_one this
  have hτe : derivAt τ P ^ e = 1 := by
    obtain ⟨c, rfl⟩ := hme
    rw [pow_mul, ← derivAt_pow hτ, hτm, derivAt_one, one_pow]
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hτe
  refine ⟨i, (eq_of_derivAt_eq (hι.pow i) hτ (hcomm.pow_left i) he hm ?_ hτm ?_).symm⟩
  · rw [← pow_mul, mul_comm, pow_mul, hιe', one_pow]
  · rw [derivAt_pow hι, hi]

/-- **On a curve of genus `0`, an automorphism fixing three distinct places is the identity.** -/
theorem eq_one_of_genus_eq_zero (hg : genus κ K = 0) {σ : K ≃ₐ[κ] K} {P Q₁ Q₂ : Place κ K}
    (h₁ : Q₁ ≠ P) (h₂ : Q₂ ≠ P) (h₁₂ : Q₁ ≠ Q₂) (hP : Fixes σ P) (hQ₁ : Fixes σ Q₁)
    (hQ₂ : Fixes σ Q₂) : σ = 1 := by
  classical
  -- `ℓ(P) = 2`
  have hell : 2 ≤ ell (Finsupp.single P 1 : Divisor κ K) := by
    have hRR := riemannRoch (Finsupp.single P 1 : Divisor κ K)
    have hdeg : Divisor.deg (Finsupp.single P 1 : Divisor κ K) = 1 := by
      simp only [Divisor.deg_single, Place.deg_eq_one, Nat.cast_one, mul_one]
    have hW : ell (canonical κ K - Finsupp.single P 1) = 0 := by
      apply ell_eq_zero_of_deg_neg
      rw [Divisor.deg_sub, deg_canonical, hdeg, hg]
      norm_num
    rw [hW, hdeg, hg] at hRR
    omega
  obtain ⟨s, hsL, hs, v, b, hv, hσs⟩ := exists_eigen_mod_const zero_le_one hell hP
  have hst : Transcendental κ s := transcendental_of_notMem_range hs
  -- the only pole of `s` is a simple pole at `P`
  have hpole : ∀ Q : Place κ K, Q ≠ P → 0 ≤ Q.ord s := by
    intro Q hQ
    rcases mem_L.1 hsL with h0 | h
    · exact absurd (h0 ▸ (isAlgebraic_zero : IsAlgebraic κ (0 : K))) hst
    · have := h Q
      rwa [Finsupp.single_apply, if_neg (Ne.symm hQ), neg_zero] at this
  have hfin : finrank κ⟮s⟯ K = 1 := by
    have hsum := Place.sum_ord_mul_deg_poles s hst
    obtain ⟨Q0, hQ0⟩ := Place.exists_ord_neg hst
    have hQ0P : Q0 = P := by
      by_contra hne
      have := hpole Q0 hne
      omega
    subst hQ0P
    have hPs : -1 ≤ Q0.ord s := by
      rcases mem_L.1 hsL with h0 | h
      · exact absurd (h0 ▸ (isAlgebraic_zero : IsAlgebraic κ (0 : K))) hst
      · simpa using h Q0
    have hZi : (Place.finite_setOf_ord_neg (k := κ) s).toFinset = {Q0} := by
      ext Q
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
      constructor
      · intro hQ
        by_contra hne
        have := hpole Q hne
        omega
      · rintro rfl; exact hQ0
    rw [hZi, Finset.sum_singleton, Place.deg_eq_one] at hsum
    push_cast at hsum
    have : Q0.ord s = -1 := by omega
    rw [this] at hsum
    have h1 : (finrank κ⟮s⟯ K : ℤ) = 1 := by rw [← hsum]; norm_num
    exact_mod_cast h1
  -- the values of `s` at `Q₁, Q₂`
  have hmem : ∀ Q : Place κ K, Q ≠ P → s ∈ Q.1 := fun Q hQ ↦ Q.mem_of_ord_nonneg (hpole Q hQ)
  have hval : ∀ Q : Place κ K, Q ≠ P → 0 < Q.ord (s - algebraMap κ K (Place.val Q s)) := by
    intro Q hQ
    have h := (Place.val_eq_iff Q (hmem Q hQ) (Place.val Q s)).1 rfl
    rcases h with h0 | h
    · exact absurd (by
        have : s = algebraMap κ K (Place.val Q s) := sub_eq_zero.1 h0
        exact ⟨_, this.symm⟩) hs
    · exact h
  -- `σ` fixes `Q` ⇒ `(v - 1) s(Q) + b = 0`
  have hrel : ∀ Q : Place κ K, Q ≠ P → Fixes σ Q →
      (v - 1) * Place.val Q s + b = 0 := by
    intro Q hQ hσQ
    set a := Place.val Q s
    have hpos := hval Q hQ
    have h1 : 0 < Q.ord (σ (s - algebraMap κ K a)) := by rw [hσQ.ord_apply]; exact hpos
    rw [map_sub, AlgEquiv.commutes, hσs] at h1
    have hmemQ : algebraMap κ K v * s + algebraMap κ K b - algebraMap κ K a ∈ Q.1 :=
      sub_mem (add_mem (mul_mem (Q.algebraMap_mem v) (hmem Q hQ)) (Q.algebraMap_mem b))
        (Q.algebraMap_mem a)
    have h0 : Place.val Q (algebraMap κ K v * s + algebraMap κ K b - algebraMap κ K a) = 0 :=
      (Place.val_eq_zero_iff Q hmemQ).2 (Or.inr h1)
    rw [Place.val_sub Q (add_mem (mul_mem (Q.algebraMap_mem v) (hmem Q hQ)) (Q.algebraMap_mem b))
      (Q.algebraMap_mem a), Place.val_add Q (mul_mem (Q.algebraMap_mem v) (hmem Q hQ))
      (Q.algebraMap_mem b), Place.val_mul Q (Q.algebraMap_mem v) (hmem Q hQ),
      Place.val_algebraMap, Place.val_algebraMap, Place.val_algebraMap] at h0
    linear_combination h0
  -- distinct places have distinct values (`s` has degree one)
  have hne : Place.val Q₁ s ≠ Place.val Q₂ s := by
    intro heq
    have hst' := transcendental_sub_algebraMap hst (Place.val Q₁ s)
    have hsum := Place.sum_ord_mul_deg_zeros (s - algebraMap κ K (Place.val Q₁ s)) hst'
    rw [adjoin_sub_algebraMap_eq, hfin] at hsum
    set Z := (Place.finite_setOf_ord_pos (k := κ) (s - algebraMap κ K (Place.val Q₁ s))).toFinset
    have hq1 : Q₁ ∈ Z := by simpa [Z] using hval Q₁ h₁
    have hq2 : Q₂ ∈ Z := by
      have : 0 < Q₂.ord (s - algebraMap κ K (Place.val Q₁ s)) := by rw [heq]; exact hval Q₂ h₂
      simpa [Z] using this
    have hsub : ({Q₁, Q₂} : Finset (Place κ K)) ⊆ Z := by
      intro Q hQ; simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with rfl | rfl <;> assumption
    have hge : ∑ Q ∈ ({Q₁, Q₂} : Finset (Place κ K)),
        Q.ord (s - algebraMap κ K (Place.val Q₁ s)) * (Q.deg : ℤ) ≤
        ∑ Q ∈ Z, Q.ord (s - algebraMap κ K (Place.val Q₁ s)) * (Q.deg : ℤ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro Q hQ _
      have : 0 < Q.ord (s - algebraMap κ K (Place.val Q₁ s)) := by simpa [Z] using hQ
      rw [Place.deg_eq_one]; push_cast; omega
    rw [hsum, Finset.sum_pair h₁₂, Place.deg_eq_one, Place.deg_eq_one] at hge
    have hp1 : 0 < Q₁.ord (s - algebraMap κ K (Place.val Q₁ s)) := hval Q₁ h₁
    have hp2 : 0 < Q₂.ord (s - algebraMap κ K (Place.val Q₁ s)) := by rw [heq]; exact hval Q₂ h₂
    push_cast at hge
    omega
  have hv1 : v = 1 := by
    have e1 := hrel Q₁ h₁ hQ₁
    have e2 := hrel Q₂ h₂ hQ₂
    have : (v - 1) * (Place.val Q₁ s - Place.val Q₂ s) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd (sub_eq_zero.1 h) hne
  have hb : b = 0 := by
    have e1 := hrel Q₁ h₁ hQ₁
    rw [hv1, sub_self, zero_mul, zero_add] at e1
    exact e1
  have hσs' : σ s = s := by rw [hσs, hv1, hb, map_one, map_zero, one_mul, add_zero]
  -- `K = κ(s)`
  have htop : κ⟮s⟯ = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.1 hfin
  set H : Subgroup (K ≃ₐ[κ] K) := Subgroup.zpowers σ
  have hsH : s ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
    clear hτ
    have hinv : σ⁻¹ s = s := by
      conv_lhs => rw [← hσs']
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσs', ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]
  have hle : κ⟮s⟯ ≤ IntermediateField.fixedField H := IntermediateField.adjoin_simple_le_iff.2 hsH
  ext y
  have hy : y ∈ IntermediateField.fixedField H := hle (htop ▸ IntermediateField.mem_top)
  exact (IntermediateField.mem_fixedField_iff H y).1 hy σ (Subgroup.mem_zpowers σ)

end CurvesJacobian.LocAn
