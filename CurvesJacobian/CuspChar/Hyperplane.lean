/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Coset.Card

/-!
# Hyperplane counting over `𝔽_p` (step G2 of [AbsTopI] Lemma 4.5 (v))

Let `V` be a finite `𝔽_p`-vector space (in the application: the continuous characters
`H → ℤ/p` of an open subgroup `H` of a geometric fundamental group) and `f : Y → V^*` a finite
family of linear forms (in the application: evaluation at a generator of the inertia group of
each cusp of `H`). The **ramification count** `N(ξ) = #{y | f y ξ ≠ 0}` is the number of cusps
ramified in the cyclic cover cut out by `ξ`.

Main result (`CurvesJacobian.CuspChar.card_mem_span_eq`): the function `N` determines, for every
nonzero form `f_B`, the number of `y` with `f y` a nonzero multiple of `f_B`. Precisely, if a
linear isomorphism `T : V' ≃ V` intertwines the ramification counts of two families `f`, `f'`,
then `#{y | f y ≠ 0 ∧ f y ∈ 𝔽_p f_B} = #{y' | f' y' ≠ 0 ∧ f' y' ∈ 𝔽_p (f_B ∘ T)}`.

The proof sums `N` over `V` and over the hyperplane `ker f_B`: a nonzero form takes every value
equally often, so `p · Σ_V N = (p - 1) · #V · #{f y ≠ 0}` and
`p · Σ_{ker f_B} N = (p - 1) · #ker f_B · #{f y ∉ 𝔽_p f_B}`.
-/

namespace CurvesJacobian.CuspChar

open Module

variable {p : ℕ} [hp : Fact p.Prime]

section Fibre

variable {W : Type*} [AddCommGroup W] [Module (ZMod p) W] [Finite W]

omit [Finite W] in
/-- A nonzero linear form on an `𝔽_p`-space is surjective. -/
lemma surjective_of_ne_zero {h : W →ₗ[ZMod p] ZMod p} (hh : h ≠ 0) : Function.Surjective h := by
  obtain ⟨w, hw⟩ : ∃ w, h w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hh (LinearMap.ext hc)
  intro c
  refine ⟨(c / h w) • w, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hw]

omit [Finite W] in
/-- `#W = p · #ker h` for a nonzero linear form `h`. -/
lemma card_eq_mul_card_ker {h : W →ₗ[ZMod p] ZMod p} (hh : h ≠ 0) :
    Nat.card W = p * Nat.card {w // h w = 0} := by
  have hsurj := surjective_of_ne_zero hh
  have e : (W ⧸ (LinearMap.ker h).toAddSubgroup) ≃ ZMod p :=
    (QuotientAddGroup.quotientKerEquivOfSurjective h.toAddMonoidHom hsurj).toEquiv
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (LinearMap.ker h).toAddSubgroup
  rw [Nat.card_congr e, Nat.card_zmod] at h1
  rw [h1]
  rfl

/-- `p · #{h ≠ 0} = (p - 1) · #W` for a nonzero linear form `h`. -/
lemma card_ne_zero_mul {h : W →ₗ[ZMod p] ZMod p} (hh : h ≠ 0) :
    p * Nat.card {w // h w ≠ 0} = (p - 1) * Nat.card W := by
  classical
  have := Fintype.ofFinite W
  have hc := card_eq_mul_card_ker hh
  have hsplit : Nat.card {w // h w ≠ 0} + Nat.card {w // h w = 0} = Nat.card W := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Nat.sub_add_cancel (Fintype.card_subtype_le _)]
  have hne : Nat.card {w // h w ≠ 0} = (p - 1) * Nat.card {w // h w = 0} := by
    rw [Nat.sub_mul, one_mul, ← hc]
    omega
  rw [hne, hc]
  ring

end Fibre

section Count

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {Y : Type*} [Fintype Y]

open Classical in
/-- The ramification count `N(ξ) = #{y | f y ξ ≠ 0}`. -/
noncomputable def ramCount (f : Y → Dual (ZMod p) V) (ξ : V) : ℕ :=
  (Finset.univ.filter fun y ↦ f y ξ ≠ 0).card

open Classical in
/-- `p · Σ_V N = (p - 1) · #V · #{y | f y ≠ 0}`. -/
lemma mul_sum_ramCount [Fintype V] (f : Y → Dual (ZMod p) V) :
    p * ∑ ξ, ramCount f ξ =
      (p - 1) * Nat.card V * (Finset.univ.filter fun y ↦ f y ≠ 0).card := by
  have hswap : ∑ ξ, ramCount f ξ = ∑ y, Nat.card {ξ : V // f y ξ ≠ 0} := by
    simp only [ramCount, Finset.card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hy : f y = 0
  · simp [hy]
  · rw [card_ne_zero_mul hy, if_pos hy]
    ring

omit [Finite V] in
lemma restrict_ne_zero {fB g : Dual (ZMod p) V}
    (hg : g ∉ Submodule.span (ZMod p) {fB}) : g.comp (LinearMap.ker fB).subtype ≠ 0 := by
  intro h0
  apply hg
  have hker : ∀ v, fB v = 0 → g v = 0 := fun v hv ↦ by
    simpa using LinearMap.congr_fun h0 ⟨v, LinearMap.mem_ker.2 hv⟩
  by_cases hB : fB = 0
  · have : g = 0 := LinearMap.ext fun v ↦ hker v (by simp [hB])
    simp [this]
  obtain ⟨w, hw⟩ := surjective_of_ne_zero hB 1
  refine Submodule.mem_span_singleton.2 ⟨g w, LinearMap.ext fun v ↦ ?_⟩
  have h1 : fB (v - fB v • w) = 0 := by simp [hw]
  have h2 := hker _ h1
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h2
  simp [h2, mul_comm]

/-- `p · #{f_B = 0, g ≠ 0} = (p - 1) · #{f_B = 0}` if `g ∉ 𝔽_p f_B`. -/
lemma card_ker_ne_zero_mul {fB g : Dual (ZMod p) V}
    (hg : g ∉ Submodule.span (ZMod p) {fB}) :
    p * Nat.card {ξ : V // fB ξ = 0 ∧ g ξ ≠ 0} = (p - 1) * Nat.card {ξ : V // fB ξ = 0} := by
  have h := card_ne_zero_mul (restrict_ne_zero hg)
  have e1 : {w : LinearMap.ker fB // (g.comp (LinearMap.ker fB).subtype) w ≠ 0} ≃
      {ξ : V // fB ξ = 0 ∧ g ξ ≠ 0} :=
    { toFun := fun w ↦ ⟨w.1.1, LinearMap.mem_ker.1 w.1.2, w.2⟩
      invFun := fun ξ ↦ ⟨⟨ξ.1, LinearMap.mem_ker.2 ξ.2.1⟩, ξ.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have e2 : LinearMap.ker fB ≃ {ξ : V // fB ξ = 0} :=
    { toFun := fun w ↦ ⟨w.1, LinearMap.mem_ker.1 w.2⟩
      invFun := fun ξ ↦ ⟨ξ.1, LinearMap.mem_ker.2 ξ.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rwa [Nat.card_congr e1, Nat.card_congr e2] at h

open Classical in
/-- `p · Σ_{ker f_B} N = (p - 1) · #ker f_B · #{y | f y ∉ 𝔽_p f_B}`. -/
lemma mul_sum_ramCount_ker [Fintype V] (f : Y → Dual (ZMod p) V) (fB : Dual (ZMod p) V) :
    p * ∑ ξ ∈ Finset.univ.filter (fun ξ ↦ fB ξ = 0), ramCount f ξ =
      (p - 1) * Nat.card {ξ : V // fB ξ = 0} *
        (Finset.univ.filter fun y ↦ f y ∉ Submodule.span (ZMod p) {fB}).card := by
  have hswap : ∑ ξ ∈ Finset.univ.filter (fun ξ ↦ fB ξ = 0), ramCount f ξ =
      ∑ y, Nat.card {ξ : V // fB ξ = 0 ∧ f y ξ ≠ 0} := by
    simp only [ramCount, Finset.card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ξ _ ↦ ?_
    by_cases h1 : fB ξ = 0 <;> by_cases h2 : f y ξ = 0 <;> simp [h1, h2]
  rw [hswap, Finset.mul_sum, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hy : f y ∈ Submodule.span (ZMod p) {fB}
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
    have : IsEmpty {ξ : V // fB ξ = 0 ∧ f y ξ ≠ 0} := by
      refine ⟨fun ⟨ξ, h1, h2⟩ ↦ h2 ?_⟩
      rw [← hc]
      simp [h1]
    simp [hy]
  · rw [card_ker_ne_zero_mul hy, if_pos hy]
    ring

omit [Finite V] in
open Classical in
/-- `f y ≠ 0 ∧ f y ∈ 𝔽_p f_B` is counted by `#{f y ≠ 0} - #{f y ∉ 𝔽_p f_B}`. -/
lemma card_mem_span_eq_sub (f : Y → Dual (ZMod p) V) (fB : Dual (ZMod p) V) :
    (Finset.univ.filter fun y ↦ f y ≠ 0 ∧ f y ∈ Submodule.span (ZMod p) {fB}).card =
      (Finset.univ.filter fun y ↦ f y ≠ 0).card -
        (Finset.univ.filter fun y ↦ f y ∉ Submodule.span (ZMod p) {fB}).card := by
  have hsub : (Finset.univ.filter fun y ↦ f y ∉ Submodule.span (ZMod p) {fB}) ⊆
      Finset.univ.filter fun y ↦ f y ≠ 0 := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rintro h0
    exact hy (h0 ▸ Submodule.zero_mem _)
  rw [← Finset.card_sdiff_of_subset hsub]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_not]

end Count

section Transport

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  [AddCommGroup V'] [Module (ZMod p) V'] [Finite V']
  {Y Y' : Type*} [Fintype Y] [Fintype Y']

open Classical in
/-- **The ramification counts determine the cusp lines** (G2). If `T : V' ≃ V` intertwines the
ramification counts of `f` and `f'`, then for every form `f_B` the number of `y` with `f y` a
nonzero multiple of `f_B` equals the number of `y'` with `f' y'` a nonzero multiple of
`f_B ∘ T`. -/
theorem card_mem_span_eq (T : V' ≃ₗ[ZMod p] V) (f : Y → Dual (ZMod p) V)
    (f' : Y' → Dual (ZMod p) V') (hN : ∀ ξ', ramCount f (T ξ') = ramCount f' ξ')
    (fB : Dual (ZMod p) V) :
    (Finset.univ.filter fun y ↦ f y ≠ 0 ∧ f y ∈ Submodule.span (ZMod p) {fB}).card =
      (Finset.univ.filter fun y' ↦
        f' y' ≠ 0 ∧ f' y' ∈ Submodule.span (ZMod p) {fB.comp T.toLinearMap}).card := by
  have := Fintype.ofFinite V
  have := Fintype.ofFinite V'
  have hp0 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  -- the totals over `V` agree
  have hA : ∑ ξ, ramCount f ξ = ∑ ξ', ramCount f' ξ' := by
    rw [← Equiv.sum_comp T.toEquiv]
    exact Finset.sum_congr rfl fun ξ' _ ↦ hN ξ'
  have hcardV : Nat.card V = Nat.card V' := (Nat.card_congr T.toEquiv).symm
  have ha : (Finset.univ.filter fun y ↦ f y ≠ 0).card =
      (Finset.univ.filter fun y' ↦ f' y' ≠ 0).card := by
    have h1 := mul_sum_ramCount f
    have h2 := mul_sum_ramCount f'
    rw [hA, h2, hcardV] at h1
    have hV : 0 < Nat.card V' := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp0 hV) h1).symm
  -- the sums over the hyperplanes agree
  set fB' := fB.comp T.toLinearMap
  let Tk : {ξ' : V' // fB' ξ' = 0} ≃ {ξ : V // fB ξ = 0} :=
    { toFun := fun ξ' ↦ ⟨T ξ', ξ'.2⟩
      invFun := fun ξ ↦ ⟨T.symm ξ, show fB (T (T.symm ξ)) = 0 by rw [T.apply_symm_apply]; exact ξ.2⟩
      left_inv := fun ξ' ↦ by ext; simp
      right_inv := fun ξ ↦ by ext; simp }
  have hB : ∑ ξ ∈ Finset.univ.filter (fun ξ ↦ fB ξ = 0), ramCount f ξ =
      ∑ ξ' ∈ Finset.univ.filter (fun ξ' ↦ fB' ξ' = 0), ramCount f' ξ' := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp T.toEquiv]
    refine Finset.sum_congr rfl fun ξ' _ ↦ ?_
    simp only [LinearEquiv.coe_toEquiv, fB', LinearMap.comp_apply, LinearEquiv.coe_coe, hN]
  have hcardK : Nat.card {ξ : V // fB ξ = 0} = Nat.card {ξ' : V' // fB' ξ' = 0} :=
    (Nat.card_congr Tk).symm
  have hb : (Finset.univ.filter fun y ↦ f y ∉ Submodule.span (ZMod p) {fB}).card =
      (Finset.univ.filter fun y' ↦ f' y' ∉ Submodule.span (ZMod p) {fB'}).card := by
    have h1 := mul_sum_ramCount_ker f fB
    have h2 := mul_sum_ramCount_ker f' fB'
    rw [hB, h2, hcardK] at h1
    have : Nonempty {ξ' : V' // fB' ξ' = 0} := ⟨⟨0, map_zero _⟩⟩
    have hK : 0 < Nat.card {ξ' : V' // fB' ξ' = 0} := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp0 hK) h1).symm
  rw [card_mem_span_eq_sub, card_mem_span_eq_sub, ha, hb]

end Transport

end CurvesJacobian.CuspChar
