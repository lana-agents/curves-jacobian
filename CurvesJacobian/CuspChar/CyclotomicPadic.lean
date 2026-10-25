/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Cyclotomic
import LocalClassFieldTheory.PadicField.PowIndexPadic

/-!
# Roots of unity in `p`-adic fields; B3 for `p`-adic fields

For a finite extension `M/ℚ_p` of degree `d` containing a primitive `l^k`-th root of unity
(`l` prime) we show `l^(k-1) ≤ p^d` (`CurvesJacobian.CuspChar.pow_le_of_isPrimitiveRoot_padic`):

* `l ≠ p`: the `l^k`-th roots of unity are units with pairwise distances `1`
  (`∏_{0<i<n} (1 - ζ^i) = n` is a unit), so they reduce to distinct elements of the residue
  field, of cardinality `p^f ≤ p^d`;
* `l = p`, `k ≥ 1`: all `1 - μ` (`μ` primitive) have the same absolute value and
  `∏_μ (1 - μ) = Φ_{p^k}(1) = p`, so `φ(p^k) · v(1 - ζ) = v(p) = e ≤ d` with `v(1 - ζ) ≥ 1`.

Hence the cyclotomic character of `G_K`, `K/ℚ_p` finite, has no finite exponent on open
subgroups (`CurvesJacobian.CuspChar.exists_cycChar_pow_ne_one_padic`, the `p`-adic case of B3 of
[AbsTopI] Lemma 4.5 (v), `MR3-plan.md`).
-/

open Polynomial PadicField

namespace CurvesJacobian.CuspChar

section Local

variable {p : ℕ} [hp : Fact p.Prime] {M : Type*} [Field M] [Algebra ℚ_[p] M]
  [FiniteDimensional ℚ_[p] M]

omit [FiniteDimensional ℚ_[p] M] in
lemma nrm_eq_one_of_pow_eq_one [Algebra.IsAlgebraic ℚ_[p] M] {ζ : M} {n : ℕ} (hn : n ≠ 0)
    (h : ζ ^ n = 1) : nrm p M ζ = 1 := by
  have h1 : nrm p M ζ ^ n = 1 := by rw [← nrm_pow, h, nrm_one]
  exact (pow_eq_one_iff_of_nonneg (nrm_nonneg ζ) hn).1 h1

omit [FiniteDimensional ℚ_[p] M] in
/-- `|1 - x^i| ≤ |1 - x|` for `|x| ≤ 1`. -/
lemma nrm_one_sub_pow_le [Algebra.IsAlgebraic ℚ_[p] M] {x : M} (hx : nrm p M x ≤ 1) (i : ℕ) :
    nrm p M (1 - x ^ i) ≤ nrm p M (1 - x) := by
  have h : 1 - x ^ i = (1 - x) * ∑ j ∈ Finset.range i, x ^ j := by
    rw [mul_comm, ← neg_sub, ← neg_sub x, mul_neg, geom_sum_mul]
  rw [h, nrm_mul]
  refine mul_le_of_le_one_right (nrm_nonneg _) (nrm_sum_le _ _ zero_le_one fun j _ ↦ ?_)
  rw [nrm_pow]
  exact pow_le_one₀ (nrm_nonneg x) hx

/-- **`l ≠ p`**: a primitive `n`-th root of unity with `p ∤ n` in `M` forces `n ≤ #𝓴_M`. -/
lemma le_card_residue_of_isPrimitiveRoot {ζ : M} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hpn : p.Coprime n) : n ≤ Nat.card (𝓴 p M) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hn0 : n ≠ 0 := hn.ne'
  have hζ1 : ∀ i, nrm p M (ζ ^ i) = 1 := fun i ↦ by
    rw [nrm_pow, nrm_eq_one_of_pow_eq_one hn0 hζ.pow_eq_one, one_pow]
  -- `|1 - ζ^i| = 1` for `0 < i < n`
  have hsub : ∀ i, 0 < i → i < n → nrm p M (1 - ζ ^ i) = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hprod := hζ.prod_one_sub_pow_eq_order
    have hnrm : nrm p M (((m + 1 : ℕ) : M)) = 1 := by
      rw [show (((m + 1 : ℕ) : M)) = algebraMap ℚ_[p] M ((m + 1 : ℕ) : ℚ_[p]) by simp,
        nrm_algebraMap]
      exact (Padic.norm_natCast_eq_one_iff (p := p)).2 hpn
    have hle : ∀ j ∈ Finset.range m, nrm p M (1 - ζ ^ (j + 1)) ≤ 1 := fun j _ ↦
      (nrm_sub_le_max _ _).trans (max_le nrm_one.le (hζ1 _).le)
    intro i hi0 hin
    have hj : i - 1 ∈ Finset.range m := Finset.mem_range.2 (by omega)
    refine le_antisymm (hle _ hj |>.trans_eq' (by rw [Nat.sub_add_cancel hi0])) ?_
    have hP : nrm p M (∏ j ∈ Finset.range m, (1 - ζ ^ (j + 1))) = 1 := by
      rw [hprod]; push_cast at hnrm ⊢; exact hnrm
    rw [map_prod, ← Finset.mul_prod_erase _ _ hj, Nat.sub_add_cancel hi0] at hP
    by_contra hlt
    push Not at hlt
    have : (∏ x ∈ (Finset.range m).erase (i - 1), nrm p M (1 - ζ ^ (x + 1))) ≤ 1 :=
      Finset.prod_le_one (fun _ _ ↦ nrm_nonneg _) fun j hj' ↦ hle j (Finset.mem_of_mem_erase hj')
    nlinarith [nrm_nonneg (p := p) (1 - ζ ^ i),
      Finset.prod_nonneg fun j (_ : j ∈ (Finset.range m).erase (i - 1)) ↦
        nrm_nonneg (p := p) (1 - ζ ^ (j + 1))]
  -- the residues of `ζ^i`, `i < n`, are distinct
  let r : Fin n → 𝓴 p M := fun i ↦
    IsLocalRing.residue (𝒪 p M) (Integers.mk (ζ ^ (i : ℕ)) (hζ1 i).le)
  have hr : Function.Injective r := by
    intro i j hij
    by_contra hne
    wlog hlt : (i : ℕ) < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) fun h ↦ hne (Fin.ext h.symm))
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      Integers.mem_maximalIdeal_iff] at hij
    have hd : ((Integers.mk (ζ ^ (i : ℕ)) (hζ1 i).le - Integers.mk (ζ ^ (j : ℕ)) (hζ1 j).le :
        𝒪 p M) : M) = ζ ^ (i : ℕ) * (1 - ζ ^ ((j : ℕ) - i)) := by
      rw [Integers.coe_sub, Integers.coe_mk, Integers.coe_mk, mul_sub, mul_one, ← pow_add,
        Nat.add_sub_cancel' hlt.le]
    rw [hd, nrm_mul, hζ1, one_mul, hsub _ (by omega) (by omega)] at hij
    exact lt_irrefl _ hij
  simpa using Nat.card_le_card_of_injective r hr

/-- **`l = p`**: a primitive `p^(k+1)`-th root of unity in `M` forces `φ(p^(k+1)) ≤ [M : ℚ_p]`. -/
lemma totient_le_finrank_of_isPrimitiveRoot {ζ : M} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Nat.totient (p ^ (k + 1)) ≤ Module.finrank ℚ_[p] M := by
  classical
  set n := p ^ (k + 1)
  have hn0 : n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have h1n : 1 < n := Nat.one_lt_pow (Nat.succ_ne_zero k) hp.out.one_lt
  have hnrmζ : ∀ μ : M, μ ^ n = 1 → nrm p M μ ≤ 1 := fun μ hμ ↦
    (nrm_eq_one_of_pow_eq_one hn0 hμ).le
  -- all `1 - μ`, `μ` primitive, have the same absolute value
  have hsame : ∀ μ ∈ primitiveRoots n M, nrm p M (1 - μ) = nrm p M (1 - ζ) := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots (Nat.pos_of_ne_zero hn0)).1 hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    refine le_antisymm ?_ ?_
    · rw [← hi]; exact nrm_one_sub_pow_le (hnrmζ _ hζ.pow_eq_one) i
    · rw [← hj]; exact nrm_one_sub_pow_le (hnrmζ _ hμ'.pow_eq_one) j
  have hprod : ∏ μ ∈ primitiveRoots n M, (1 - μ) = (p : M) := by
    have h := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [eval_one_cyclotomic_prime_pow k, eval_prod] at h
    simpa using h.symm
  have hcard : (primitiveRoots n M).card = Nat.totient n := hζ.card_primitiveRoots
  have hpow : nrm p M ((1 - ζ) ^ Nat.totient n) = nrm p M (p : M) := by
    rw [← hprod, map_prod, Finset.prod_congr rfl hsame, Finset.prod_const, hcard, nrm_pow]
  have hζ1 : 1 - ζ ≠ 0 := sub_ne_zero.2 (fun h ↦ (hζ.ne_one h1n) h.symm)
  have hp0 : (p : M) ≠ 0 := natCast_p_ne_zero
  have hv := (nrm_eq_iff_v_eq (pow_ne_zero _ hζ1) hp0).1 hpow
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [v_pow hζ1, v_natCast, padicValNat_self, Nat.cast_one, mul_one] at hv
  -- `v(1 - ζ) ≥ 1`
  have hlt : nrm p M (1 - ζ) < 1 := by
    have hpn : nrm p M (p : M) < 1 := by
      rw [show (p : M) = algebraMap ℚ_[p] M (p : ℚ_[p]) by simp, nrm_algebraMap, Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    rw [← hpow, nrm_pow] at hpn
    by_contra hge
    push Not at hge
    exact (one_le_pow₀ hge).not_gt hpn
  have hv1 : 1 ≤ v p (1 - ζ) := (nrm_lt_one_iff_v_pos hζ1).1 hlt
  have hef := e_mul_f (p := p) (K := ℚ_[p]) (L := M)
  have hf := f_pos (p := p) (K := ℚ_[p]) (L := M)
  have : (Nat.totient n : ℤ) ≤ e p ℚ_[p] M := by
    rw [← hv]; nlinarith
  have he : e p ℚ_[p] M ≤ Module.finrank ℚ_[p] M := by
    rw [← hef]; exact Nat.le_mul_of_pos_right _ hf
  omega

/-- **Roots of unity in a `p`-adic field**: if `M/ℚ_p` (finite) contains a primitive `l^k`-th
root of unity (`l` prime), then `l^(k-1) ≤ p^[M : ℚ_p]`. -/
theorem pow_le_of_isPrimitiveRoot_padic {l k : ℕ} (hl : l.Prime) {ζ : M}
    (hζ : IsPrimitiveRoot ζ (l ^ k)) : l ^ (k - 1) ≤ p ^ Module.finrank ℚ_[p] M := by
  set d := Module.finrank ℚ_[p] M
  have hd : d < p ^ d := Nat.lt_pow_self hp.out.one_lt
  by_cases hlp : l = p
  · subst hlp
    rcases k with _ | k
    · exact Nat.one_le_pow _ _ hp.out.pos
    have h := totient_le_finrank_of_isPrimitiveRoot hζ
    rw [Nat.totient_prime_pow_succ hp.out] at h
    have : l ^ k ≤ l ^ k * (l - 1) := Nat.le_mul_of_pos_right _ (by have := hp.out.two_le; omega)
    simp only [Nat.add_sub_cancel]
    omega
  · have hcop : p.Coprime (l ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out hl).2 (Ne.symm hlp))
    have h1 := le_card_residue_of_isPrimitiveRoot hζ hcop
    have hq : Nat.card (𝓴 p M) = p ^ f p ℚ_[p] M := q_eq_pow
    have hef := e_mul_f (p := p) (K := ℚ_[p]) (L := M)
    have he := e_pos (p := p) (K := ℚ_[p]) (L := M)
    have hfd : f p ℚ_[p] M ≤ d := by
      have := Nat.le_mul_of_pos_left (f p ℚ_[p] M) he
      rw [hef] at this
      exact this
    calc l ^ (k - 1) ≤ l ^ k := Nat.pow_le_pow_right hl.pos (Nat.sub_le _ _)
      _ ≤ p ^ f p ℚ_[p] M := hq ▸ h1
      _ ≤ p ^ d := Nat.pow_le_pow_right hp.out.pos hfd

end Local

section Global

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Algebra.IsAlgebraic K Ω]

/-- If the cyclotomic character satisfies `χ_{l^k}^N = 1` on `Gal(Ω/L)` for all `k` (`l` an odd
prime, `N > 0`), then for every `k` a primitive `l^k`-th root of unity has degree `≤ N` over `L`
(the set `{ζ^a : a^N = 1}` of its conjugates has at most `N` elements). -/
theorem exists_primitiveRoot_natDegree_le {l : ℕ} [hl : Fact l.Prime] (hl2 : l ≠ 2)
    (L : IntermediateField K Ω) {N : ℕ} (hN : 0 < N)
    (H : ∀ k, ∀ σ ∈ L.fixingSubgroup, cycChar K Ω l k σ ^ N = 1) (k : ℕ) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ (l ^ k) ∧ IsIntegral L ζ ∧ (minpoly L ζ).natDegree ≤ N := by
  classical
  haveI : CharZero K := (algebraMap K Ω).charZero
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K Ω := isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero k hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
  have hord : orderOf ζ = l ^ k := hζ.eq_orderOf.symm
  have hmod : ∀ m, ζ ^ (m % l ^ k) = ζ ^ m := fun m ↦ by
    rw [← hord]
    exact pow_mod_orderOf ζ m
  set W := Finset.univ.filter fun a : (ZMod (l ^ k))ˣ ↦ a ^ N = 1
  set P : Polynomial Ω := ∏ a ∈ W, (X - C (ζ ^ (a : ZMod (l ^ k)).val))
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C _
  have hPdeg : P.natDegree = W.card := by
    rw [natDegree_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
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
  refine ⟨ζ, hζ, ⟨Q, hQmon, hroot⟩, ?_⟩
  refine (natDegree_le_of_dvd (minpoly.dvd L ζ hroot) hQmon.ne_zero).trans ?_
  rw [hQdeg, hPdeg]
  exact card_pow_eq_one_le_units hl.out hl2 k hN

/-- **B3 for `p`-adic fields: the cyclotomic character has no finite exponent on `Gal(Ω/L)`**
for `L/K` finite, `K/ℚ_p` finite and `l` an odd prime (possibly `l = p`). Otherwise all
`ζ_{l^k}` would have degree `≤ N` over `L`, so `L(ζ_{l^k})/ℚ_p` would have degree
`≤ [L : ℚ_p] N =: D` for all `k`, contradicting `l^(k-1) ≤ p^D`
(`pow_le_of_isPrimitiveRoot_padic`). -/
theorem exists_cycChar_pow_ne_one_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] {l : ℕ} [hl : Fact l.Prime] (hl2 : l ≠ 2)
    (L : IntermediateField K Ω) [FiniteDimensional K L] {N : ℕ} (hN : 0 < N) :
    ∃ k, ∃ σ ∈ L.fixingSubgroup, cycChar K Ω l k σ ^ N ≠ 1 := by
  by_contra H
  push Not at H
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp (algebraMap ℚ_[p] K)).toAlgebra
  haveI : IsScalarTower ℚ_[p] K Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional ℚ_[p] L := Module.Finite.trans K L
  set D := Module.finrank ℚ_[p] L * N
  set k := p ^ D + 1
  obtain ⟨ζ, hζ, hint, hdeg⟩ := exists_primitiveRoot_natDegree_le hl2 L hN H k
  set E := IntermediateField.adjoin L {ζ}
  haveI : IsScalarTower ℚ_[p] L Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional L E := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans L E
  have hfE : Module.finrank L E = (minpoly L ζ).natDegree := IntermediateField.adjoin.finrank hint
  have hrank : Module.finrank ℚ_[p] E = Module.finrank ℚ_[p] L * Module.finrank L E :=
    (Module.finrank_mul_finrank ℚ_[p] L E).symm
  have hζE : ζ ∈ E := IntermediateField.mem_adjoin_simple_self L ζ
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : E) (l ^ k) :=
    hζ.of_map_of_injective (f := algebraMap E Ω) (algebraMap E Ω).injective
  have h1 := pow_le_of_isPrimitiveRoot_padic (p := p) hl.out hζ'
  have hED : Module.finrank ℚ_[p] E ≤ D := by
    rw [hrank, hfE]
    exact Nat.mul_le_mul_left _ hdeg
  have h2 : p ^ Module.finrank ℚ_[p] E ≤ p ^ D := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hED
  have h3 : p ^ D < l ^ (p ^ D) := Nat.lt_pow_self hl.out.one_lt
  simp only [k, Nat.add_sub_cancel] at h1
  omega

end Global

end CurvesJacobian.CuspChar
