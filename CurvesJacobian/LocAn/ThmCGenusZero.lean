/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThmCUnitCoord

/-!
# [LocAn] Theorem C in genus `0` with two rational cusps (MR7 S3(a), step 4 over `k`)

For a curve of genus `0` the Jacobian argument of `LocAn/ThmC.lean` is empty; Kummer classes of
units replace it (`LocAn/ThmCUnits.lean`, `LocAn/ThmCUnitCoord.lean`). If `X` has genus `0` over
`k` and `U` has two distinct `k`-rational cusps `P, Q`, Riemann–Roch gives a coordinate `w` with
`F = k(w)` and `div w = Q − P`; `w` is a unit of `U`, so `Δ_U`-conjugate sections of rational
points of `U` give the same point.

## Main results

* `WeilCurves.FunctionField.ell_zero_eq_one_of_genus_eq_zero`: `ℓ(0) = 1` in genus `0`;
* `WeilCurves.FunctionField.exists_adjoin_eq_top_of_genus_eq_zero`: genus `0` and a place `P` of
  degree `1` give `K = k(w)` with a single simple pole at `P`;
* `WeilCurves.FunctionField.exists_adjoin_eq_top_div_of_genus_eq_zero`: with a second place `Q`
  of degree `1`, `w` can be taken with `div w = Q − P`;
* `CurvesJacobian.LocAn.mem_units_of_ord'`: functions without zeros or poles over `U` are units;
* **`CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj_genus_zero`**: Theorem C (profinite)
  in genus `0` with two `k`-rational cusps, `k` Kummer-faithful for `𝔾_m`.

The general genus-`0` case (cusps not rational) needs a finite extension `k'/k` making two cusps
rational and the Galois model over `k'` (MR7 plan S3(c)).
-/


open scoped IntermediateField

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

/-- In genus `0`, `ℓ(0) = 1`. -/
theorem ell_zero_eq_one_of_genus_eq_zero (hg : genus k K = 0) :
    Divisor.ell (0 : Divisor k K) = 1 := by
  have h1 := ell_canonical (k := k) (K := K)
  have h2 : Divisor.ell (canonical k K) = 0 :=
    Divisor.ell_eq_zero_of_deg_neg (by rw [deg_canonical, hg]; norm_num)
  rw [h2, hg] at h1
  omega

/-- **A genus-`0` function field with a place of degree `1` is rational**: `K = k(w)` for a
function `w` whose only pole is a simple pole at `P`. -/
theorem exists_adjoin_eq_top_of_genus_eq_zero (hg : genus k K = 0) {P : Place k K}
    (hP : P.deg = 1) : ∃ w : K, k⟮w⟯ = ⊤ ∧ P.ord w = -1 ∧ ∀ Q : Place k K, Q ≠ P → 0 ≤ Q.ord w := by
  classical
  set A : Divisor k K := Finsupp.single P 1
  have hA : (Divisor.ell A : ℤ) = 2 := by
    rw [ell_eq_of_deg_gt (by rw [Divisor.deg_single, hP, hg]; norm_num), Divisor.deg_single, hP,
      hg]
    norm_num
  have h0 := ell_zero_eq_one_of_genus_eq_zero hg
  have hle : Divisor.L (0 : Divisor k K) ≤ Divisor.L A :=
    Divisor.L_mono (Finsupp.single_nonneg.2 zero_le_one)
  have hne : Divisor.L (0 : Divisor k K) ≠ Divisor.L A := by
    intro h
    have : Divisor.ell (0 : Divisor k K) = Divisor.ell A := by rw [Divisor.ell, Divisor.ell, h]
    omega
  obtain ⟨w, hwA, hw0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hwne : w ≠ 0 := fun h ↦ hw0 (h ▸ (Divisor.L 0).zero_mem)
  have ht : Transcendental k w := fun h ↦ hw0 (Divisor.mem_L_zero.2 h)
  have hord : ∀ Q : Place k K, -A Q ≤ Q.ord w := (Divisor.mem_L.1 hwA).resolve_left hwne
  have hQ : ∀ Q : Place k K, Q ≠ P → 0 ≤ Q.ord w := fun Q hQ ↦ by
    have := hord Q
    change -(Finsupp.single P (1 : ℤ)) Q ≤ _ at this
    rwa [Finsupp.single_apply, if_neg (Ne.symm hQ), neg_zero] at this
  have hPge : -1 ≤ P.ord w := by
    have := hord P
    change -(Finsupp.single P (1 : ℤ)) P ≤ _ at this
    rwa [Finsupp.single_eq_same] at this
  have hsum := Place.sum_ord_mul_deg_poles w ht
  have hsub : (Place.finite_setOf_ord_neg (k := k) w).toFinset ⊆ {P} := fun Q hQm ↦ by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hQm
    rw [Finset.mem_singleton]
    by_contra hne
    exact absurd (hQ Q hne) (not_le.2 hQm)
  have := finiteDimensional_adjoin ht
  have hpos : 0 < Module.finrank k⟮w⟯ K := Module.finrank_pos
  rcases Finset.subset_singleton_iff.1 hsub with h | h
  · rw [h, Finset.sum_empty] at hsum
    omega
  rw [h, Finset.sum_singleton, hP] at hsum
  have hPw : P.ord w = -1 := by omega
  refine ⟨w, ?_, hPw, hQ⟩
  have h1 : Module.finrank k⟮w⟯ K = 1 := by
    rw [hPw] at hsum
    omega
  have hbot : (⊤ : IntermediateField k⟮w⟯ K) = ⊥ :=
    IntermediateField.finrank_eq_one_iff.1 (by rw [IntermediateField.finrank_top', h1])
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (⊥ : IntermediateField k⟮w⟯ K) := hbot ▸ IntermediateField.mem_top
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact y.2

/-- At a place of degree `1`, every `f ∈ 𝒪_P` has a value `a ∈ k`: `f − a ∈ 𝔪_P`. -/
theorem Place.exists_sub_mem_maximalIdeal {P : Place k K} (hP : P.deg = 1) (f : P.1) :
    ∃ a : k, P.residue f = algebraMap k P.ResidueField a := by
  have h := (Subalgebra.bot_eq_top_iff_finrank_eq_one (F := k) (E := P.ResidueField)).2 hP
  have hx : P.residue f ∈ (⊥ : Subalgebra k P.ResidueField) := h ▸ Algebra.mem_top
  obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hx
  exact ⟨a, ha.symm⟩

/-- **Genus `0` with two places of degree `1`**: there is `w` with `K = k(w)`, `div w = Q − P`
(a simple zero at `Q`, a simple pole at `P`, no other zeros or poles). -/
theorem exists_adjoin_eq_top_div_of_genus_eq_zero (hg : genus k K = 0) {P Q : Place k K}
    (hPQ : P ≠ Q) (hP : P.deg = 1) (hQ : Q.deg = 1) :
    ∃ w : K, k⟮w⟯ = ⊤ ∧ ∀ R : Place k K, R ≠ P → R ≠ Q → R.ord w = 0 := by
  classical
  obtain ⟨w₀, htop, hPw, hR⟩ := exists_adjoin_eq_top_of_genus_eq_zero hg hP
  have hw₀Q : w₀ ∈ Q.1 := Q.mem_of_ord_nonneg (hR Q (Ne.symm hPQ))
  obtain ⟨a, ha⟩ := Place.exists_sub_mem_maximalIdeal hQ ⟨w₀, hw₀Q⟩
  set w := w₀ - algebraMap k K a with hw
  have hadj : k⟮w⟯ = ⊤ := by
    rw [eq_top_iff, ← htop, IntermediateField.adjoin_simple_le_iff]
    have : w₀ = w + algebraMap k K a := by rw [hw]; ring
    rw [this]
    exact add_mem (IntermediateField.mem_adjoin_simple_self k w)
      (IntermediateField.algebraMap_mem _ a)
  have ht : Transcendental k w := by
    intro h
    have := (Place.isAlgebraic_iff_forall_ord_eq_zero.1 h) P
    have hPw' : P.ord w = -1 := by
      by_cases ha0 : a = 0
      · rw [hw, ha0, map_zero, sub_zero, hPw]
      have hc0 : -algebraMap k K a ≠ 0 := neg_ne_zero.2 ((map_ne_zero _).2 ha0)
      have hw₀0 : w₀ ≠ 0 := fun h0 ↦ by rw [h0, P.ord_zero] at hPw; omega
      have hlt : P.ord w₀ < P.ord (-algebraMap k K a) := by
        rw [P.ord_neg, P.ord_algebraMap_base, hPw]; omega
      rw [hw, sub_eq_add_neg, P.ord_add_eq_of_lt hw₀0 hc0 hlt, hPw]
    omega
  have hw0 : w ≠ 0 := fun h ↦ ht (h ▸ isAlgebraic_zero)
  have hwQ : w ∈ Q.1 := sub_mem hw₀Q (Q.algebraMap_mem a)
  have hQpos : 0 < Q.ord w := by
    refine (Q.ord_pos_iff_mem_maximalIdeal (a := ⟨w, hwQ⟩) hw0).2 ?_
    rw [← Place.residue_eq_zero_iff]
    have : (⟨w, hwQ⟩ : Q.1) = ⟨w₀, hw₀Q⟩ - ⟨algebraMap k K a, Q.algebraMap_mem a⟩ := rfl
    rw [this, map_sub, ha, Place.residue_mk_algebraMap, sub_self]
  have hnn : ∀ R : Place k K, R ≠ P → 0 ≤ R.ord w := fun R hRP ↦
    R.ord_nonneg_of_mem (sub_mem (R.mem_of_ord_nonneg (hR R hRP)) (R.algebraMap_mem a))
  have hfin : Module.finrank k⟮w⟯ K = 1 := by
    have := finiteDimensional_adjoin ht
    have h1 : Module.finrank k⟮w⟯ K = Module.finrank (⊤ : IntermediateField k K) K := by
      rw [hadj]
    rw [h1, IntermediateField.finrank_top]
  have hsum := Place.sum_ord_mul_deg_zeros w ht
  rw [hfin] at hsum
  refine ⟨w, hadj, fun R hRP hRQ ↦ ?_⟩
  refine le_antisymm ?_ (hnn R hRP)
  by_contra hpos
  push Not at hpos
  have hQm : Q ∈ (Place.finite_setOf_ord_pos (k := k) w).toFinset := by
    simpa using hQpos
  have hRm : R ∈ (Place.finite_setOf_ord_pos (k := k) w).toFinset := by
    simpa using hpos
  have hle : Q.ord w * (Q.deg : ℤ) + R.ord w * (R.deg : ℤ) ≤
      ∑ S ∈ (Place.finite_setOf_ord_pos (k := k) w).toFinset, S.ord w * (S.deg : ℤ) := by
    rw [← Finset.sum_pair (f := fun S : Place k K ↦ S.ord w * (S.deg : ℤ)) (Ne.symm hRQ)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun S hS _ ↦ ?_
    · intro S hS
      rcases Finset.mem_insert.1 hS with rfl | hS
      · exact hQm
      · rw [Finset.mem_singleton.1 hS]; exact hRm
    · have : 0 < S.ord w := by simpa using hS
      positivity
  have hRd := R.deg_pos
  rw [hsum, hQ] at hle
  nlinarith

end WeilCurves.FunctionField

namespace CurvesJacobian.LocAn

open KummerTheory Curve AffOrbicurve IsLocalRing CurvesJacobian.Kummer WeilCurves.FunctionField
open IntermediateField.algebraAdjoinAdjoin

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] in
/-- **An element of `F` lying in every place over `U` is integral over `k[t]`** (the integral
closure of `k[t]` in `F` is the intersection of the valuation rings containing it; the same
argument as iut's `Thm19.isIntegral_of_forall_place`). -/
theorem isIntegral_of_forall_place' (x : F D)
    (hx : ∀ P : Place k (F D), tF D ∈ P.1 → x ∈ P.1) : IsIntegral (A₀ k t) x := by
  have hC := Subring.eq_iInf_of_isIntegrallyClosedIn
    (R := (integralClosure (A₀ k t) (F D)).toSubring) (K := F D)
  have : x ∈ (integralClosure (A₀ k t) (F D)).toSubring := by
    rw [hC, Subring.mem_iInf]
    intro V
    by_cases hV : V.1 = ⊤
    · rw [hV]
      exact ValuationSubring.mem_top x
    · have hk : ∀ c : k, algebraMap k (F D) c ∈ V.1 := fun c => V.2 (by
        change IsIntegral (A₀ k t) (algebraMap k (F D) c)
        rw [IsScalarTower.algebraMap_apply k (A₀ k t) (F D)]
        exact isIntegral_algebraMap)
      have ht : tF D ∈ V.1 := V.2 (by
        change IsIntegral (A₀ k t) (tF D)
        have e : tF D = algebraMap (A₀ k t) (F D)
            ⟨t, Algebra.subset_adjoin (Set.mem_singleton t)⟩ := rfl
        rw [e]
        exact isIntegral_algebraMap)
      exact hx ⟨V.1, hV, hk⟩ ht
  exact this

omit [IsAlgClosed Ω] in
/-- A nonzero element of `F` without zeros or poles over `U` is a unit of `U`. -/
theorem mem_units_of_ord' (g : F D) (hg : g ≠ 0)
    (hord : ∀ P : Place k (F D), tF D ∈ P.1 → P.ord g = 0) : Units.mk0 g hg ∈ units D :=
  ⟨isIntegral_of_forall_place' g fun P hP => ((P.ord_eq_zero_iff hg).1 (hord P hP)).1,
    isIntegral_of_forall_place' _ fun P hP => ((P.ord_eq_zero_iff hg).1 (hord P hP)).2⟩

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) in genus `0` with two `k`-rational cusps** (MR7 S3(a)): if `X`
has genus `0` over `k`, `U` has two distinct cusps `P, Q` of degree `1`, `k` is Kummer-faithful
for `𝔾_m`, and two rational points `x, y` of `U` have `Δ_U`-conjugate sections, then `x = y`.
(Riemann–Roch gives `F = k(w)` with `div w = Q − P`, a unit of `U`.) -/
theorem placeOfF_eq_of_ratSectionGk_conj_genus_zero (hkf : IsKummerFaithfulGm k)
    (hHL : D.HL = D.H) {x y : RatPoint D} (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D}
    (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹)
    (hg : genus k (F D) = 0) {P Q : Place k (F D)} (hPQ : P ≠ Q) (hP : P.deg = 1)
    (hQ : Q.deg = 1) (hPc : tF D ∉ P.1) (hQc : tF D ∉ Q.1) :
    placeOfF x = placeOfF y := by
  obtain ⟨w, hadj, hord⟩ := exists_adjoin_eq_top_div_of_genus_eq_zero hg hPQ hP hQ
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [IntermediateField.adjoin_zero] at hadj
    have htF : (tF D) ∈ (⊥ : IntermediateField k (F D)) := by rw [hadj]; trivial
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 htF
    have hct : algebraMap k Ω c = t := congrArg Subtype.val hc
    exact D.transcendental (hct ▸ isAlgebraic_algebraMap c)
  have hu := mem_units_of_ord' w hw0 fun R hR ↦
    hord R (fun e ↦ hPc (e ▸ hR)) (fun e ↦ hQc (e ▸ hR))
  exact placeOfF_eq_of_ratSectionGk_conj_unitCoord hkf hHL hx hy hδ h ⟨_, hu⟩ hadj

end CurvesJacobian.LocAn
