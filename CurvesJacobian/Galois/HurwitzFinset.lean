/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Hurwitz.Belyi

/-!
# The genus of a cover of `ℙ¹` branched over a finite set

Let `k` be algebraically closed of characteristic zero, `L` a function field over `k` and
`x ∈ L` transcendental, unramified over `𝔸¹ ∖ S` for a finite `S ⊆ k`: `ord_Q (x - a) ≤ 1` for
every place `Q` of `L` and every `a ∉ S`. With `d = [L : k(x)]`, `c_s = #{Q | ord_Q (x - s) > 0}`
and `c_∞ = #{Q | ord_Q x < 0}`,

  `2 g_L - 2 = d (|S| - 1) - c_∞ - ∑_{s ∈ S} c_s`   (`CurvesJacobian.genus_of_finset`).

This is the general form of weil-curves' `genus_belyi` (`S = {0, 1}`), with the same proof: the
Riemann–Hurwitz formula in characteristic zero (`riemannHurwitz_charZero`) for `L / k(x)`,
`g(k(x)) = 0`, all places of degree one, `e(Q) = ord_Q (x - a)` above `a ∈ k`, `e(Q) = -ord_Q x`
above `∞`, and `∑_{x(Q) = a} e(Q) = d = ∑_{x(Q) = ∞} e(Q)`.
-/

open Module WeilCurves.FunctionField
open scoped IntermediateField

namespace CurvesJacobian

variable {k L : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Field L] [Algebra k L]
  [IsFunctionField k L]

/-- **Riemann–Hurwitz for a cover of `ℙ¹` branched over `S ∪ {∞}`**: if `x ∈ L` is transcendental
and `ord_Q (x - a) ≤ 1` for all places `Q` and all `a ∉ S`, then
`2 g_L - 2 = [L : k(x)] (|S| - 1) - c_∞ - ∑_{s ∈ S} c_s`, with `c_s`, `c_∞` the numbers of places
of `L` over `s` and `∞`. -/
theorem genus_of_finset {x : L} (hx : Transcendental k x) (S : Finset k)
    (hunr : ∀ Q : Place k L, ∀ a : k, a ∉ S → Q.ord (x - algebraMap k L a) ≤ 1) :
    2 * genus k L - 2 = (finrank k⟮x⟯ L : ℤ) * (S.card - 1) -
      {Q : Place k L | Q.ord x < 0}.ncard -
        ∑ s ∈ S, ({Q : Place k L | 0 < Q.ord (x - algebraMap k L s)}.ncard : ℤ) := by
  classical
  set K := k⟮x⟯
  set t : K := IntermediateField.AdjoinSimple.gen k x
  have htx : algebraMap K L t = x := rfl
  have ht : Transcendental k t := by
    rw [← transcendental_algebraMap_iff (algebraMap K L).injective, htx]; exact hx
  have htop : k⟮t⟯ = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  have hK1 : ∀ a : k, finrank k⟮t - algebraMap k K a⟯ K = 1 := fun a ↦ by
    rw [adjoin_sub_algebraMap_eq, IntermediateField.finrank_eq_one_iff_eq_top]; exact htop
  have hK1' : finrank k⟮t⟯ K = 1 := by
    rw [IntermediateField.finrank_eq_one_iff_eq_top]; exact htop
  haveI : FiniteDimensional k⟮t⟯ K := Module.finite_of_finrank_eq_succ hK1'
  haveI : IsFunctionField k K := ⟨⟨t, ht, inferInstance⟩⟩
  haveI : FiniteDimensional K L := finiteDimensional_adjoin hx
  have hgK : genus k K = 0 := genus_eq_zero_of_finrank_eq_one ell_zero_eq_one_of_isAlgClosed ht hK1'
  -- ramification indices above `a ∈ k` and above `∞`
  have hram : ∀ (Q : Place k L) (a : k), 0 < Q.ord (x - algebraMap k L a) →
      ramIndex K Q = Q.ord (x - algebraMap k L a) := by
    intro Q a hQ
    have hxa : x - algebraMap k L a = algebraMap K L (t - algebraMap k K a) := by
      rw [map_sub, htx, ← IsScalarTower.algebraMap_apply]
    rw [hxa, ord_algebraMap_eq_ramIndex_mul] at hQ ⊢
    have he := ramIndex_pos (K := K) Q
    have hpos : 0 < (Q.restrict (K := K)).ord (t - algebraMap k K a) :=
      pos_of_mul_pos_right hQ he.le
    obtain ⟨h1, -⟩ := ord_eq_one_of_finrank_eq_one (transcendental_sub_algebraMap ht a)
      (hK1 a) hpos
    rw [h1, mul_one]
  have hramInf : ∀ Q : Place k L, Q.ord x < 0 → ramIndex K Q = -Q.ord x := by
    intro Q hQ
    have hxi : x⁻¹ = algebraMap K L t⁻¹ := by rw [map_inv₀, htx]
    have hQ' : 0 < Q.ord (algebraMap K L t⁻¹) := by rw [← hxi, Place.ord_inv]; omega
    rw [ord_algebraMap_eq_ramIndex_mul] at hQ'
    have he := ramIndex_pos (K := K) Q
    have hpos := pos_of_mul_pos_right hQ' he.le
    have hinv : finrank k⟮t⁻¹⟯ K = 1 := by rw [adjoin_inv_eq]; exact hK1'
    obtain ⟨h1, -⟩ := ord_eq_one_of_finrank_eq_one (transcendental_inv ht) hinv hpos
    have := congrArg Q.ord hxi
    rw [Place.ord_inv, ord_algebraMap_eq_ramIndex_mul, h1, mul_one] at this
    omega
  -- the finite sets of places over `s ∈ S` and over `∞`
  let Zs : k → Finset (Place k L) := fun s ↦
    (Place.finite_setOf_ord_pos (k := k) (x - algebraMap k L s)).toFinset
  set Zi := (Place.finite_setOf_ord_neg (k := k) x).toFinset
  have hmems : ∀ s Q, Q ∈ Zs s ↔ 0 < Q.ord (x - algebraMap k L s) := fun s Q ↦ by simp [Zs]
  have hmemi : ∀ Q, Q ∈ Zi ↔ Q.ord x < 0 := fun Q ↦ by simp [Zi]
  have hunram : ∀ Q : Place k L, Q ∉ S.biUnion Zs ∪ Zi → ramIndex K Q = 1 := by
    intro Q hQ
    simp only [Finset.mem_union, Finset.mem_biUnion, hmems, hmemi, not_or, not_exists,
      not_and] at hQ
    obtain ⟨hs, hi⟩ := hQ
    have hxQ : x ∈ Q.1 := Q.mem_of_ord_nonneg (by omega)
    obtain ⟨a, ha⟩ := Q.exists_ord_sub_pos hx hxQ
    have haS : a ∉ S := fun h ↦ hs a h ha
    have := hunr Q a haS
    rw [hram Q a ha]
    omega
  have hRH := riemannHurwitz_charZero (K := K) (S.biUnion Zs ∪ Zi) hunram
  rw [hgK] at hRH
  -- disjointness
  have hds : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → Disjoint (Zs s) (Zs s') := by
    intro s _ s' _ hss
    rw [Finset.disjoint_left]
    intro Q h h'
    rw [hmems] at h h'
    have hc : (x - algebraMap k L s) + -(x - algebraMap k L s') = algebraMap k L (s' - s) := by
      rw [map_sub]; ring
    have hne : (x - algebraMap k L s) + -(x - algebraMap k L s') ≠ 0 := by
      rw [hc, map_ne_zero_iff _ (algebraMap k L).injective, sub_ne_zero]
      exact Ne.symm hss
    have := Q.min_le_ord_add hne
    rw [Place.ord_neg, hc, Place.ord_algebraMap_base] at this
    omega
  have hdi : Disjoint (S.biUnion Zs) Zi := by
    rw [Finset.disjoint_left]
    intro Q h hi
    rw [hmemi] at hi
    obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 h
    rw [hmems] at hs
    have hxQ : x ∈ Q.1 := by
      have hmem : x - algebraMap k L s ∈ Q.1 := Q.mem_of_ord_nonneg hs.le
      simpa using add_mem hmem (Q.algebraMap_mem s)
    have := Q.ord_nonneg_of_mem hxQ
    omega
  rw [Finset.sum_union hdi, Finset.sum_biUnion hds] at hRH
  have hdeg : ∀ Q : Place k L, (Q.deg : ℤ) = 1 := fun Q ↦ by rw [Place.deg_eq_one]; rfl
  have hss : ∀ s : k, ∑ Q ∈ Zs s, (ramIndex K Q - 1) * (Q.deg : ℤ) =
      finrank k⟮x⟯ L - (Zs s).card := by
    intro s
    have h := Place.sum_ord_mul_deg_zeros (x - algebraMap k L s)
      (transcendental_sub_algebraMap hx s)
    rw [Finset.sum_congr rfl fun Q hQ ↦ by
      rw [hdeg, mul_one, hram Q s ((hmems s Q).mp hQ)]]
    simp only [hdeg, mul_one] at h
    rw [Finset.sum_sub_distrib, h, adjoin_sub_algebraMap_eq]
    simp [Zs]
  have hsi : ∑ Q ∈ Zi, (ramIndex K Q - 1) * (Q.deg : ℤ) = finrank k⟮x⟯ L - Zi.card := by
    have h := Place.sum_ord_mul_deg_poles x hx
    rw [Finset.sum_congr rfl fun Q hQ ↦ by
      rw [hdeg, mul_one, hramInf Q ((hmemi Q).mp hQ)]]
    simp only [hdeg, mul_one] at h
    rw [Finset.sum_sub_distrib, h]
    simp
  rw [Finset.sum_congr rfl fun s _ ↦ hss s, hsi] at hRH
  have hcs : ∀ s : k, ({Q : Place k L | 0 < Q.ord (x - algebraMap k L s)}.ncard : ℤ) =
      (Zs s).card := fun s ↦ by
    rw [Set.ncard_eq_toFinset_card _ (Place.finite_setOf_ord_pos _)]
  have hci : {Q : Place k L | Q.ord x < 0}.ncard = Zi.card := Set.ncard_eq_toFinset_card _ _
  rw [Finset.sum_congr rfl fun s _ ↦ hcs s, hci, hRH, Finset.sum_sub_distrib]
  change (finrank K L : ℤ) * (2 * 0 - 2) + _ = _
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

end CurvesJacobian
