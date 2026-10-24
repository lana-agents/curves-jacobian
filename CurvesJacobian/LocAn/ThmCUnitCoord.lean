/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThmCUnits

/-!
# [LocAn] Theorem C for curves with a unit coordinate (MR7 S3(a), step 3)

`LocAn/ThmCUnits.lean` shows that `Δ_U`-conjugate sections of two rational points `x, y` of `U`
give `w(x) = w(y)` for every unit `w` of `U`, over a field `k` that is Kummer-faithful for `𝔾_m`.
If the function field is `F = k(w)` for one such unit (for instance `U ⊆ ℙ¹ ∖ {0, ∞}` with
coordinate `w`: the genus-`0` case with two rational cusps), this separates the points: the
place of `k(w)` at which `w − a` vanishes is unique.

## Main results

* `WeilCurves.FunctionField.Place.ord_aeval`: `ord_P r(w) = mult_a(r) · ord_P(w − a)` when
  `ord_P(w − a) > 0`;
* `WeilCurves.FunctionField.Place.eq_of_adjoin_eq_top`: places of `k(w)` with
  `ord(w − a) > 0` are equal;
* `CurvesJacobian.LocAn.ord_placeOfF_pos`, `CurvesJacobian.LocAn.exists_unit_residue`;
* **`CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj_unitCoord`**: Theorem C for
  `F = k(w)`, `w` a unit of `U`.

The general genus-`0` case (no two rational cusps) needs a finite extension of `k` making two
cusps rational (MR7 plan S3(a) step 4, S3(c)).
-/

open Polynomial
open scoped IntermediateField

namespace WeilCurves.FunctionField.Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Polynomials in `w ∈ P` with coefficients in `k` lie in `P`. -/
theorem aeval_mem (P : Place k K) {w : K} (hw : w ∈ P.1) (q : k[X]) : aeval w q ∈ P.1 := by
  induction q using Polynomial.induction_on with
  | C c => rw [aeval_C]; exact P.algebraMap_mem c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c _ =>
    rw [map_mul, map_pow, aeval_X, aeval_C]
    exact mul_mem (P.algebraMap_mem c) (pow_mem hw _)

variable [PerfectField k] [IsFunctionField k K]

/-- If `0 < ord_P (w − a)`, a polynomial `q` with `q(a) ≠ 0` has `ord_P q(w) = 0`. -/
theorem ord_aeval_eq_zero (P : Place k K) {w : K} {a : k}
    (hpos : 0 < P.ord (w - algebraMap k K a)) {q : k[X]} (hq : q.eval a ≠ 0) :
    P.ord (aeval w q) = 0 := by
  have hwa : w - algebraMap k K a ≠ 0 := fun h ↦ by
    rw [h, P.ord_zero] at hpos; exact lt_irrefl _ hpos
  have hwP : w ∈ P.1 := by
    have h1 : w - algebraMap k K a ∈ P.1 := P.mem_of_ord_nonneg hpos.le
    simpa using add_mem h1 (P.algebraMap_mem a)
  have hroot : IsRoot (q - C (q.eval a)) a := by simp
  set g := (q - C (q.eval a)) /ₘ (X - C a)
  have hg : (X - C a) * g = q - C (q.eval a) := mul_divByMonic_eq_iff_isRoot.2 hroot
  have hdec : aeval w q = algebraMap k K (q.eval a) + (w - algebraMap k K a) * aeval w g := by
    have := congrArg (aeval w) hg
    rw [map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C] at this
    rw [this]; ring
  have hc : P.ord (algebraMap k K (q.eval a)) = 0 := P.ord_algebraMap_base _
  have hc0 : algebraMap k K (q.eval a) ≠ 0 := (_root_.map_ne_zero _).2 hq
  by_cases hg0 : (w - algebraMap k K a) * aeval w g = 0
  · rw [hdec, hg0, add_zero, hc]
  · rw [hdec, P.ord_add_eq_of_lt hc0 hg0, hc]
    have hgne : aeval w g ≠ 0 := right_ne_zero_of_mul hg0
    rw [hc, P.ord_mul hwa hgne]
    have := P.ord_nonneg_of_mem (P.aeval_mem hwP g)
    omega

/-- `ord_P r(w) = mult_a(r) · ord_P (w − a)` when `0 < ord_P (w − a)`. -/
theorem ord_aeval (P : Place k K) {w : K} {a : k}
    (hpos : 0 < P.ord (w - algebraMap k K a)) {r : k[X]} (hr : r ≠ 0) (hrw : aeval w r ≠ 0) :
    P.ord (aeval w r) = r.rootMultiplicity a * P.ord (w - algebraMap k K a) := by
  obtain ⟨q, hq, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr a
  have hqa : q.eval a ≠ 0 := fun h ↦ hdvd (dvd_iff_isRoot.2 h)
  set m := r.rootMultiplicity a with hm
  have hrw' := hrw
  rw [hq, map_mul, map_pow, map_sub, aeval_X, aeval_C] at hrw' ⊢
  have h1 : (w - algebraMap k K a) ^ r.rootMultiplicity a ≠ 0 := left_ne_zero_of_mul hrw'
  rw [P.ord_mul h1 (right_ne_zero_of_mul hrw'), P.ord_pow, P.ord_aeval_eq_zero hpos hqa, add_zero]

/-- **Places of a rational function field are determined by the value of the coordinate**: if
`K = k(w)` and `w − a` has positive order at `P` and at `P'`, then `P = P'`. -/
theorem eq_of_adjoin_eq_top {w : K} (hw : k⟮w⟯ = ⊤) {a : k} {P P' : Place k K}
    (hP : 0 < P.ord (w - algebraMap k K a)) (hP' : 0 < P'.ord (w - algebraMap k K a)) :
    P = P' := by
  have key : ∀ Q : Place k K, 0 < Q.ord (w - algebraMap k K a) → ∀ (r s : k[X]),
      aeval w r ≠ 0 → aeval w s ≠ 0 →
      (aeval w r / aeval w s ∈ Q.1 ↔ s.rootMultiplicity a ≤ r.rootMultiplicity a) := by
    intro Q hQ r s hr hs
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    rw [Q.mem_iff_ord_nonneg, Q.ord_div hr hs, Q.ord_aeval hQ hr0 hr, Q.ord_aeval hQ hs0 hs]
    constructor
    · rintro (h | h)
      · exact absurd h (div_ne_zero hr hs)
      · by_contra hlt
        push Not at hlt
        have : (r.rootMultiplicity a : ℤ) < s.rootMultiplicity a := by exact_mod_cast hlt
        nlinarith
    · intro hle
      right
      have : (s.rootMultiplicity a : ℤ) ≤ r.rootMultiplicity a := by exact_mod_cast hle
      nlinarith
  apply Place.ext
  ext f
  have hf : f ∈ k⟮w⟯ := by rw [hw]; trivial
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (F := k) f).1 hf
  by_cases hr : aeval w r = 0
  · simp [hr]
  by_cases hs : aeval w s = 0
  · simp [hs]
  rw [key P hP r s hr hs, key P' hP' r s hr hs]

end WeilCurves.FunctionField.Place

namespace CurvesJacobian.LocAn

open KummerTheory Curve AffOrbicurve IsLocalRing CurvesJacobian.Kummer WeilCurves.FunctionField

universe u

section General

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

/-- At a rational point `x`, if `f ≠ 0` in `F` lies in `x.A` with residue `0`, then
`ord_x f > 0`. -/
theorem ord_placeOfF_pos {x : RatPoint D} {f : F D} (hf0 : f ≠ 0) (hf : (f : Ω) ∈ x.A)
    (h0 : residue x.A ⟨_, hf⟩ = 0) : 0 < (placeOfF x).ord f := by
  have hnn : 0 ≤ (placeOfF x).ord f := (placeOfF x).ord_nonneg_of_mem (mem_placeOfF.2 hf)
  refine lt_of_le_of_ne hnn fun h ↦ ?_
  have hinv : ((f⁻¹ : F D) : Ω) ∈ x.A :=
    mem_placeOfF.1 (((placeOfF x).ord_eq_zero_iff hf0).1 h.symm).2
  have hm : (⟨_, hf⟩ : x.A) ∈ maximalIdeal x.A := (residue_eq_zero_iff _).1 h0
  have hunit : IsUnit (⟨_, hf⟩ : x.A) := isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by
    change (f : Ω) * ((f⁻¹ : F D) : Ω) = 1
    rw [IntermediateField.coe_inv, mul_inv_cancel₀ (by exact_mod_cast hf0)])⟩
  exact (mem_maximalIdeal _).1 hm hunit

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- The value of a unit of `U` at a rational point of `U` is a unit of `k`. -/
theorem exists_unit_residue (x : RatPoint D) (hx : t ∈ x.A) (w : units D) :
    ∃ (a : kˣ) (hw : (((w : (F D)ˣ) : F D) : Ω) ∈ x.A),
      residue x.A ⟨_, hw⟩ = algebraMap k (ResidueField x.A) a := by
  obtain ⟨hw, hw'⟩ := units_mem (D := D) ⟨x.hk, hx⟩ w.2
  obtain ⟨a, ha⟩ := x.hrat _ hw
  have hunit : IsUnit (⟨_, hw⟩ : x.A) := isUnit_iff_exists_inv.2 ⟨⟨_, hw'⟩, Subtype.ext (by
    change ((((w : (F D)ˣ) : F D) : Ω) * ((((w : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω)) = 1
    rw [← IntermediateField.coe_mul, Units.mul_inv]
    rfl)⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, residue_eq_zero_iff] at ha
    exact (mem_maximalIdeal _).1 ha hunit
  exact ⟨Units.mk0 a ha0, hw, ha⟩

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for `U ⊆ 𝔸¹ ∖ {0}` with a unit coordinate** (MR7 S3(a), step 3):
if `F = k(w)` for a unit `w` of `U` (e.g. `U ⊆ ℙ¹ ∖ {0, ∞}`, `w` the coordinate), `k` is
Kummer-faithful for `𝔾_m`, and two rational points `x, y` of `U` have `Δ_U`-conjugate sections,
then `x = y` as places of `F`. -/
theorem placeOfF_eq_of_ratSectionGk_conj_unitCoord (hkf : IsKummerFaithfulGm k) (hHL : D.HL = D.H)
    {x y : RatPoint D} (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D} (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹)
    (w : units D) (hgen : k⟮((w : (F D)ˣ) : F D)⟯ = ⊤) :
    placeOfF x = placeOfF y := by
  obtain ⟨a, hwx, ha⟩ := exists_unit_residue x hx w
  obtain ⟨b, hwy, hb⟩ := exists_unit_residue y hy w
  have hab : a = b := eq_of_ratSectionGk_conj_units hkf hHL hx hy hδ h w a b hwx
    (units_mem (D := D) ⟨x.hk, hx⟩ w.2).2 ha hwy (units_mem (D := D) ⟨y.hk, hy⟩ w.2).2 hb
  subst hab
  set f : F D := ((w : (F D)ˣ) : F D) - algebraMap k (F D) a with hf
  have hf0 : f ≠ 0 := by
    intro h0
    rw [hf, sub_eq_zero] at h0
    rw [h0, IntermediateField.adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ _)]
      at hgen
    have htF : t ∈ F D :=
      (F D).algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
    have hmem : (⟨t, htF⟩ : F D) ∈ (⊥ : IntermediateField k (F D)) := by
      rw [hgen]; trivial
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
    have hct : algebraMap k Ω c = t := congrArg Subtype.val hc
    exact D.transcendental (hct ▸ isAlgebraic_algebraMap c)
  have key : ∀ (z : RatPoint D) (hwz : (((w : (F D)ˣ) : F D) : Ω) ∈ z.A),
      residue z.A ⟨_, hwz⟩ = algebraMap k (ResidueField z.A) a →
      0 < (placeOfF z).ord f := by
    intro z hwz hz
    have hfz : (f : Ω) ∈ z.A := by
      have hfe : (f : Ω) = (((w : (F D)ˣ) : F D) : Ω) - algebraMap k Ω a := rfl
      rw [hfe]
      exact sub_mem hwz (z.hk a)
    refine ord_placeOfF_pos hf0 hfz ?_
    have : residue z.A ⟨_, hfz⟩ = residue z.A ⟨_, hwz⟩ - residue z.A ⟨_, z.hk a⟩ := by
      rw [← map_sub]; rfl
    rw [this, hz, RatPoint.hkres, sub_self]
  exact Place.eq_of_adjoin_eq_top hgen (key x hwx ha) (key y hwy hb)

end General

end CurvesJacobian.LocAn
