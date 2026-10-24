/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The cyclotomic character of a number field has no finite exponent on open subgroups (B3)

Let `K` be a number field, `Ω` an algebraic closure of `K` and `l` an odd prime. For a finite
extension `K ⊆ L ⊆ Ω` and `N > 0`, some `σ ∈ Gal(Ω/L)` and some level `k` satisfy
`χ_{l^k}(σ)^N ≠ 1` (`CurvesJacobian.CuspChar.exists_cycChar_pow_ne_one`). Otherwise every
`σ ∈ Gal(Ω/L)` would map a primitive `l^k`-th root of unity `ζ` into `{ζ^a : a^N = 1}`, a set of
at most `N` elements (`(ℤ/l^k)ˣ` is cyclic); the polynomial `∏_{a^N = 1} (X - ζ^a)` would be
defined over `L`, so `[L(ζ) : L] ≤ N`, contradicting `[ℚ(ζ) : ℚ] = φ(l^k) → ∞`.

This is the input "χ_l has infinite image on every open subgroup of `G_K`" of step B of
[AbsTopI] Lemma 4.5 (v) (`MR3-plan.md`).
-/

namespace CurvesJacobian.CuspChar

open Polynomial

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [CharZero Ω]

lemma natCard_rootsOfUnity_pow (l k : ℕ) [NeZero l] :
    Nat.card {x // x ∈ rootsOfUnity (l ^ k) Ω} = l ^ k := by
  haveI : NeZero ((l ^ k : ℕ) : Ω) := ⟨by exact_mod_cast pow_ne_zero k (NeZero.ne l)⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ k)

/-- The mod-`l^k` cyclotomic character of `Gal(Ω/K)`. -/
noncomputable def cycChar (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    [CharZero Ω] (l k : ℕ) [NeZero l] : (Ω ≃ₐ[K] Ω) →* (ZMod (l ^ k))ˣ :=
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero k (NeZero.ne l)⟩
  (modularCyclotomicCharacter Ω (natCard_rootsOfUnity_pow (Ω := Ω) l k)).comp
    (MulSemiringAction.toRingAut (Ω ≃ₐ[K] Ω) Ω)

lemma cycChar_spec (l k : ℕ) [NeZero l] (σ : Ω ≃ₐ[K] Ω) {t : Ωˣ}
    (ht : t ∈ rootsOfUnity (l ^ k) Ω) :
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero k (NeZero.ne l)⟩
    σ (t : Ω) = (t : Ω) ^ ((cycChar K Ω l k σ : ZMod (l ^ k))).val := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero k (NeZero.ne l)⟩
  exact modularCyclotomicCharacter.spec Ω _ (MulSemiringAction.toRingAut (Ω ≃ₐ[K] Ω) Ω σ) ht

/-- In `(ℤ/l^k)ˣ` (`l` an odd prime) at most `N` elements satisfy `a^N = 1`. -/
lemma card_pow_eq_one_le_units {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (k : ℕ) [NeZero (l ^ k)]
    {N : ℕ} (hN : 0 < N) :
    (Finset.univ.filter fun a : (ZMod (l ^ k))ˣ ↦ a ^ N = 1).card ≤ N := by
  classical
  haveI := ZMod.isCyclic_units_of_prime_pow l hl hl2 k
  convert IsCyclic.card_pow_eq_one_le (α := (ZMod (l ^ k))ˣ) hN

section Exponent

variable [Algebra.IsAlgebraic K Ω]

/-- **The cyclotomic character has no finite exponent on `Gal(Ω/L)`** for `L/K` finite, `K` a
number field and `l` an odd prime. -/
theorem exists_cycChar_pow_ne_one [NumberField K] {l : ℕ} [hl : Fact l.Prime] (hl2 : l ≠ 2)
    (L : IntermediateField K Ω) [FiniteDimensional K L] {N : ℕ} (hN : 0 < N) :
    ∃ k, ∃ σ ∈ L.fixingSubgroup, cycChar K Ω l k σ ^ N ≠ 1 := by
  classical
  by_contra H
  push Not at H
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K Ω := isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  set d := Module.finrank ℚ L
  set k := N * d + 1
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero k hl.out.ne_zero⟩
  have h1k : 1 < l ^ k := Nat.one_lt_pow (Nat.succ_ne_zero _) hl.out.one_lt
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
  have hord : orderOf ζ = l ^ k := hζ.eq_orderOf.symm
  have hmod : ∀ m, ζ ^ (m % l ^ k) = ζ ^ m := fun m ↦ by
    rw [← hord]
    exact pow_mod_orderOf ζ m
  set W := Finset.univ.filter fun a : (ZMod (l ^ k))ˣ ↦ a ^ N = 1
  set P : Ω[X] := ∏ a ∈ W, (X - C (ζ ^ (a : ZMod (l ^ k)).val))
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C _
  have hPdeg : P.natDegree = W.card := by
    rw [natDegree_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  -- the action of `σ ∈ Gal(Ω/L)` on the roots of `P`
  have hact : ∀ σ : Ω ≃ₐ[K] Ω, ∀ a : (ZMod (l ^ k))ˣ, σ (ζ ^ (a : ZMod (l ^ k)).val) =
      ζ ^ ((cycChar K Ω l k σ * a : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)).val := by
    intro σ a
    have hz := cycChar_spec (K := K) l k σ hζ.toRootsOfUnity.2
    simp only [IsPrimitiveRoot.val_toRootsOfUnity_coe] at hz
    rw [map_pow, hz, ← pow_mul, Units.val_mul, ZMod.val_mul, hmod]
  have hmapP : ∀ σ ∈ L.fixingSubgroup, P.map (σ : Ω →+* Ω) = P := by
    intro σ hσ
    set c := cycChar K Ω l k σ
    have hc : c ^ N = 1 := H k σ hσ
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    refine Finset.prod_nbij' (fun a ↦ c * a) (fun a ↦ c⁻¹ * a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [mul_pow, hc, ha, one_mul]
    · intro a ha
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [mul_pow, inv_pow, hc, ha, inv_one, one_mul]
    · intro a _
      simp
    · intro a _
      simp
    · intro a _
      congr 2
      exact hact σ a
  have hcoeff : ∀ i, P.coeff i ∈ L := by
    intro i
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have := congrArg (fun Q ↦ Q.coeff i) (hmapP σ hσ)
    simpa [coeff_map] using this
  have hlifts : P ∈ lifts (algebraMap L Ω) :=
    (lifts_iff_coeff_lifts P).2 fun n ↦ ⟨⟨_, hcoeff n⟩, rfl⟩
  obtain ⟨Q, hQmap, hQdeg, hQmon⟩ := lifts_and_natDegree_eq_and_monic hlifts hPmonic
  have hroot : aeval ζ Q = 0 := by
    rw [aeval_def, ← eval_map, hQmap, eval_prod]
    refine Finset.prod_eq_zero (i := 1) (by simp [W]) ?_
    rw [eval_sub, eval_X, eval_C, Units.val_one, ZMod.val_one_eq_one_mod, hmod, pow_one,
      sub_self]
  have hint : IsIntegral L ζ := ⟨Q, hQmon, hroot⟩
  have hdegL : (minpoly L ζ).natDegree ≤ N := by
    refine (natDegree_le_of_dvd (minpoly.dvd L ζ hroot) hQmon.ne_zero).trans ?_
    rw [hQdeg, hPdeg]
    exact card_pow_eq_one_le_units hl.out hl2 k hN
  -- degrees over `ℚ`
  set E := IntermediateField.adjoin L {ζ}
  have hfE : Module.finrank L E = (minpoly L ζ).natDegree := IntermediateField.adjoin.finrank hint
  haveI : FiniteDimensional L E := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ E := Module.Finite.trans L E
  have hrank : Module.finrank ℚ E = d * Module.finrank L E :=
    (Module.finrank_mul_finrank ℚ L E).symm
  have hζE : ζ ∈ E := IntermediateField.mem_adjoin_simple_self L ζ
  have hmin : (minpoly ℚ (⟨ζ, hζE⟩ : E)).natDegree ≤ Module.finrank ℚ E := minpoly.natDegree_le _
  have hminEq : minpoly ℚ (⟨ζ, hζE⟩ : E) = minpoly ℚ ζ :=
    (minpoly.algebraMap_eq (A := ℚ) (algebraMap E Ω).injective ⟨ζ, hζE⟩).symm
  have hcyc : (minpoly ℚ ζ).natDegree = Nat.totient (l ^ k) := by
    rw [← cyclotomic_eq_minpoly_rat hζ (by positivity), natDegree_cyclotomic]
  have htot : Nat.totient (l ^ k) = l ^ (N * d) * (l - 1) := by
    rw [Nat.totient_prime_pow hl.out (Nat.succ_pos _)]
    rfl
  have hlt : N * d < l ^ (N * d) := Nat.lt_pow_self hl.out.one_lt
  have hl1 : 1 ≤ l - 1 := by have := hl.out.two_le; omega
  have hle : Nat.totient (l ^ k) ≤ d * N := by
    rw [← hcyc, ← hminEq]
    refine hmin.trans ?_
    rw [hrank, hfE]
    exact Nat.mul_le_mul_left _ hdegL
  rw [htot] at hle
  nlinarith

end Exponent

end CurvesJacobian.CuspChar
