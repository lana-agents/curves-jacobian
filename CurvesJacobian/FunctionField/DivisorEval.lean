/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Hurwitz.Belyi
import WeilCurves.Hurwitz.Lift

/-!
# Values of functions at places and at divisors

Let `K/κ` be a function field of one variable over an algebraically closed field `κ`. Every place
`P` has residue field `κ` (`WeilCurves.FunctionField.Place.deg_eq_one`), so a function `f ∈ 𝒪_P`
has a value `f(P) ∈ κ`; for a divisor `D` whose support avoids the zeros and poles of `f` one
puts `f(D) = ∏_P f(P)^{D(P)}` (Sutherland, *Elliptic curves* (MIT 18.783, 2019), Lecture 24,
Def. 24.18).

* `CurvesJacobian.Place.val P f`: the value `f(P) ∈ κ` (`0` if `f ∉ 𝒪_P`), with `val_mul`,
  `val_algebraMap`, `val_ne_zero` (units), `val_inv`, `val_eq_iff` (`f(P) = c` iff
  `ord_P (f - c) > 0`).
* `CurvesJacobian.evalDiv f D = f(D)`, with `evalDiv_add`, `evalDiv_neg`, `evalDiv_sub`,
  `evalDiv_nsmul`, `evalDiv_mul`, `evalDiv_inv`, `evalDiv_pow`, `evalDiv_algebraMap`
  (`c(D) = c^{deg D}`), `evalDiv_ne_zero`.
* `CurvesJacobian.exists_ord_eq_neg` (**moving lemma**): for a divisor `D` and a finite set `S`
  of places there is `h ≠ 0` with `ord_P h = -D(P)` on `S`, so `D + div h` avoids `S`
  (`exists_add_div_avoid`); from weil-curves' approximation theorem `exists_approx`.
-/

open WeilCurves.FunctionField

namespace CurvesJacobian

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

namespace Place

/-- The residue field of a place is `κ` (`κ` algebraically closed). -/
noncomputable def resEquiv (P : Place κ K) : κ ≃ₐ[κ] P.ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId κ P.ResidueField)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ) (K := P.ResidueField))

open Classical in
/-- The value `f(P) ∈ κ` of a function `f` regular at `P` (junk value `0` otherwise). -/
noncomputable def val (P : Place κ K) (f : K) : κ :=
  if h : f ∈ P.1 then (resEquiv P).symm (P.residue ⟨f, h⟩) else 0

variable (P : Place κ K) {f g : K}

lemma val_of_mem (h : f ∈ P.1) : val P f = (resEquiv P).symm (P.residue ⟨f, h⟩) := by
  rw [val, dif_pos h]

lemma val_of_notMem (h : f ∉ P.1) : val P f = 0 := by
  rw [val, dif_neg h]

lemma algebraMap_val (h : f ∈ P.1) :
    algebraMap κ P.ResidueField (val P f) = P.residue ⟨f, h⟩ := by
  rw [val_of_mem P h]
  exact (resEquiv P).apply_symm_apply _

lemma val_eq_of_residue (h : f ∈ P.1) {c : κ}
    (hc : P.residue ⟨f, h⟩ = algebraMap κ P.ResidueField c) : val P f = c := by
  apply (resEquiv P).injective
  rw [val_of_mem P h, AlgEquiv.apply_symm_apply, hc]
  rfl

@[simp]
lemma val_algebraMap (c : κ) : val P (algebraMap κ K c) = c :=
  val_eq_of_residue P (P.algebraMap_mem c) (Place.residue_mk_algebraMap P c)

@[simp]
lemma val_one : val P (1 : K) = 1 := by
  simpa using val_algebraMap P (1 : κ)

@[simp]
lemma val_zero : val P (0 : K) = 0 := by
  simpa using val_algebraMap P (0 : κ)

lemma val_mul (hf : f ∈ P.1) (hg : g ∈ P.1) : val P (f * g) = val P f * val P g := by
  refine val_eq_of_residue P (mul_mem hf hg) ?_
  rw [map_mul, algebraMap_val P hf, algebraMap_val P hg, ← map_mul]
  rfl

lemma val_add (hf : f ∈ P.1) (hg : g ∈ P.1) : val P (f + g) = val P f + val P g := by
  refine val_eq_of_residue P (add_mem hf hg) ?_
  rw [map_add, algebraMap_val P hf, algebraMap_val P hg, ← map_add]
  rfl

lemma val_sub (hf : f ∈ P.1) (hg : g ∈ P.1) : val P (f - g) = val P f - val P g := by
  refine val_eq_of_residue P (sub_mem hf hg) ?_
  rw [map_sub, algebraMap_val P hf, algebraMap_val P hg, ← map_sub]
  rfl

lemma val_pow (hf : f ∈ P.1) (n : ℕ) : val P (f ^ n) = val P f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, val_mul P (pow_mem hf n) hf, ih, pow_succ]

/-- `f(P) = 0` iff `f` vanishes at `P` (for `f ∈ 𝒪_P`). -/
lemma val_eq_zero_iff (hf : f ∈ P.1) : val P f = 0 ↔ f = 0 ∨ 0 < P.ord f := by
  rw [val_of_mem P hf, AlgEquiv.symm_apply_eq, map_zero, Place.residue_eq_zero_iff]
  constructor
  · intro h
    by_cases h0 : f = 0
    · exact Or.inl h0
    · exact Or.inr ((P.ord_pos_iff).mpr ⟨h0, (ValuationSubring.coe_mem_nonunits_iff).mpr h⟩)
  · rintro (h0 | hpos)
    · subst h0; exact Ideal.zero_mem _
    · exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f, hf⟩)).mp ((P.ord_pos_iff).mp hpos).2

/-- A function without zero or pole at `P` has a nonzero value there. -/
lemma val_ne_zero (hf : f ≠ 0) (h : P.ord f = 0) : val P f ≠ 0 := by
  have hmem : f ∈ P.1 := P.mem_of_ord_nonneg h.ge
  rw [Ne, val_eq_zero_iff P hmem]
  rintro (h0 | hpos)
  · exact hf h0
  · omega

lemma mem_of_ord_eq_zero (h : P.ord f = 0) : f ∈ P.1 := P.mem_of_ord_nonneg h.ge

lemma val_inv (hf : f ≠ 0) (h : P.ord f = 0) : val P f⁻¹ = (val P f)⁻¹ := by
  have h' : P.ord f⁻¹ = 0 := by rw [Place.ord_inv, h, neg_zero]
  have h1 := val_mul P (mem_of_ord_eq_zero P h) (mem_of_ord_eq_zero P h')
  rw [mul_inv_cancel₀ hf, val_one] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

lemma val_div (hg : g ≠ 0) (hf0 : P.ord f = 0) (hg0 : P.ord g = 0) :
    val P (f / g) = val P f / val P g := by
  have h' : P.ord g⁻¹ = 0 := by rw [Place.ord_inv, hg0, neg_zero]
  rw [div_eq_mul_inv, val_mul P (mem_of_ord_eq_zero P hf0) (mem_of_ord_eq_zero P h'),
    val_inv P hg hg0, div_eq_mul_inv]

/-- `f(P) = c` iff `f - c` vanishes at `P`. -/
lemma val_eq_iff (hf : f ∈ P.1) (c : κ) :
    val P f = c ↔ f - algebraMap κ K c = 0 ∨ 0 < P.ord (f - algebraMap κ K c) := by
  have hc := P.algebraMap_mem c
  rw [← val_eq_zero_iff P (sub_mem hf hc), val_sub P hf hc, val_algebraMap, sub_eq_zero]

end Place

open Classical in
/-- **The value `f(D) = ∏_P f(P)^{D(P)}` of a function at a divisor** (Sutherland, Lecture 24,
Def. 24.18). Meaningful when the support of `D` avoids the zeros and poles of `f`. -/
noncomputable def evalDiv (f : K) (D : Divisor κ K) : κ :=
  D.prod fun P n ↦ Place.val P f ^ n

/-- `f` has neither zeros nor poles on the support of `D`. -/
def Avoids (f : K) (D : Divisor κ K) : Prop :=
  f ≠ 0 ∧ ∀ P, D P ≠ 0 → P.ord f = 0

lemma Avoids.val_ne_zero {f : K} {D : Divisor κ K} (h : Avoids f D) {P : Place κ K}
    (hP : D P ≠ 0) : Place.val P f ≠ 0 :=
  Place.val_ne_zero P h.1 (h.2 P hP)

@[simp]
lemma evalDiv_zero (f : K) : evalDiv f (0 : Divisor κ K) = 1 := by
  simp [evalDiv]

lemma evalDiv_single (f : K) (P : Place κ K) (n : ℤ) :
    evalDiv f (Finsupp.single P n) = Place.val P f ^ n := by
  rw [evalDiv, Finsupp.prod_single_index (zpow_zero _)]

lemma evalDiv_add {f : K} {D E : Divisor κ K} (hD : Avoids f D) (hE : Avoids f E) :
    evalDiv f (D + E) = evalDiv f D * evalDiv f E := by
  classical
  refine Finsupp.prod_add_index (fun _ _ ↦ zpow_zero _) fun P hP b₁ b₂ ↦ ?_
  have hne : Place.val P f ≠ 0 := by
    rcases Finset.mem_union.mp hP with h | h
    · exact hD.val_ne_zero (Finsupp.mem_support_iff.mp h)
    · exact hE.val_ne_zero (Finsupp.mem_support_iff.mp h)
  exact zpow_add₀ hne b₁ b₂

lemma Avoids.neg {f : K} {D : Divisor κ K} (h : Avoids f D) : Avoids f (-D) :=
  ⟨h.1, fun P hP ↦ h.2 P (by simpa using hP)⟩

lemma Avoids.add {f : K} {D E : Divisor κ K} (hD : Avoids f D) (hE : Avoids f E) :
    Avoids f (D + E) := by
  refine ⟨hD.1, fun P hP ↦ ?_⟩
  by_cases h : D P = 0
  · exact hE.2 P (by simpa [h] using hP)
  · exact hD.2 P h

lemma Avoids.sub {f : K} {D E : Divisor κ K} (hD : Avoids f D) (hE : Avoids f E) :
    Avoids f (D - E) := by
  rw [sub_eq_add_neg]; exact hD.add hE.neg

lemma Avoids.zsmul {f : K} {D : Divisor κ K} (h : Avoids f D) (n : ℤ) : Avoids f (n • D) :=
  ⟨h.1, fun P hP ↦ h.2 P fun h0 ↦ hP (by simp [h0])⟩

lemma Avoids.nsmul {f : K} {D : Divisor κ K} (h : Avoids f D) (n : ℕ) : Avoids f (n • D) :=
  ⟨h.1, fun P hP ↦ h.2 P fun h0 ↦ hP (by simp [h0])⟩

lemma Avoids.mul {f g : K} {D : Divisor κ K} (hf : Avoids f D) (hg : Avoids g D) :
    Avoids (f * g) D :=
  ⟨mul_ne_zero hf.1 hg.1, fun P hP ↦ by rw [Place.ord_mul P hf.1 hg.1, hf.2 P hP, hg.2 P hP,
    add_zero]⟩

lemma Avoids.inv {f : K} {D : Divisor κ K} (hf : Avoids f D) : Avoids f⁻¹ D :=
  ⟨inv_ne_zero hf.1, fun P hP ↦ by rw [Place.ord_inv, hf.2 P hP, neg_zero]⟩

lemma Avoids.div {f g : K} {D : Divisor κ K} (hf : Avoids f D) (hg : Avoids g D) :
    Avoids (f / g) D := by
  rw [div_eq_mul_inv]; exact hf.mul hg.inv

lemma Avoids.pow {f : K} {D : Divisor κ K} (hf : Avoids f D) (n : ℕ) : Avoids (f ^ n) D :=
  ⟨pow_ne_zero n hf.1, fun P hP ↦ by rw [Place.ord_pow, hf.2 P hP, mul_zero]⟩

lemma avoids_algebraMap {c : κ} (hc : c ≠ 0) (D : Divisor κ K) : Avoids (algebraMap κ K c) D :=
  ⟨(map_ne_zero _).mpr hc, fun P _ ↦ P.ord_algebraMap_base c⟩

/-- `f` avoids `D` iff it avoids each place of the support. -/
lemma avoids_iff {f : K} {D : Divisor κ K} (hf : f ≠ 0) :
    Avoids f D ↔ ∀ P ∈ D.support, P.ord f = 0 :=
  ⟨fun h P hP ↦ h.2 P (Finsupp.mem_support_iff.mp hP),
    fun h ↦ ⟨hf, fun P hP ↦ h P (Finsupp.mem_support_iff.mpr hP)⟩⟩

lemma evalDiv_neg {f : K} {D : Divisor κ K} (hD : Avoids f D) :
    evalDiv f (-D) = (evalDiv f D)⁻¹ := by
  have h := evalDiv_add hD hD.neg
  rw [add_neg_cancel, evalDiv_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma evalDiv_sub {f : K} {D E : Divisor κ K} (hD : Avoids f D) (hE : Avoids f E) :
    evalDiv f (D - E) = evalDiv f D / evalDiv f E := by
  rw [sub_eq_add_neg, evalDiv_add hD hE.neg, evalDiv_neg hE, div_eq_mul_inv]

lemma evalDiv_nsmul {f : K} {D : Divisor κ K} (hD : Avoids f D) (n : ℕ) :
    evalDiv f (n • D) = evalDiv f D ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, evalDiv_add (hD.nsmul n) hD, ih, pow_succ]

lemma evalDiv_zsmul {f : K} {D : Divisor κ K} (hD : Avoids f D) (n : ℤ) :
    evalDiv f (n • D) = evalDiv f D ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [natCast_zsmul, evalDiv_nsmul hD, zpow_natCast]
  · rw [neg_smul, evalDiv_neg (hD.zsmul _), natCast_zsmul, evalDiv_nsmul hD, zpow_neg,
      zpow_natCast]

lemma evalDiv_mul {f g : K} {D : Divisor κ K} (hf : Avoids f D) (hg : Avoids g D) :
    evalDiv (f * g) D = evalDiv f D * evalDiv g D := by
  classical
  rw [evalDiv, evalDiv, evalDiv, ← Finsupp.prod_mul]
  refine Finset.prod_congr rfl fun P hP ↦ ?_
  have hP' := Finsupp.mem_support_iff.mp hP
  dsimp only
  rw [Place.val_mul P (Place.mem_of_ord_eq_zero P (hf.2 P hP'))
    (Place.mem_of_ord_eq_zero P (hg.2 P hP')), mul_zpow]

lemma evalDiv_inv {f : K} {D : Divisor κ K} (hf : Avoids f D) :
    evalDiv f⁻¹ D = (evalDiv f D)⁻¹ := by
  have h := evalDiv_mul hf hf.inv
  rw [mul_inv_cancel₀ hf.1] at h
  have h1 : evalDiv (1 : K) D = 1 := by
    classical
    rw [evalDiv]
    exact Finset.prod_eq_one fun P _ ↦ by dsimp only; rw [Place.val_one, one_zpow]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma evalDiv_div {f g : K} {D : Divisor κ K} (hf : Avoids f D) (hg : Avoids g D) :
    evalDiv (f / g) D = evalDiv f D / evalDiv g D := by
  rw [div_eq_mul_inv, evalDiv_mul hf hg.inv, evalDiv_inv hg, div_eq_mul_inv]

lemma evalDiv_pow {f : K} {D : Divisor κ K} (hf : Avoids f D) (n : ℕ) :
    evalDiv (f ^ n) D = evalDiv f D ^ n := by
  induction n with
  | zero =>
    classical
    rw [pow_zero, pow_zero, evalDiv]
    exact Finset.prod_eq_one fun P _ ↦ by dsimp only; rw [Place.val_one, one_zpow]
  | succ n ih => rw [pow_succ, evalDiv_mul (hf.pow n) hf, ih, pow_succ]

/-- `c(D) = c^{deg D}` for a constant `c ≠ 0`. -/
lemma evalDiv_algebraMap {c : κ} (hc : c ≠ 0) (D : Divisor κ K) :
    evalDiv (algebraMap κ K c) D = c ^ D.deg := by
  classical
  rw [evalDiv, Divisor.deg, Finsupp.prod, Finsupp.sum]
  simp only [Place.val_algebraMap, Place.deg_eq_one, Nat.cast_one, mul_one]
  induction D.support using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hc, ih]

lemma evalDiv_ne_zero {f : K} {D : Divisor κ K} (hf : Avoids f D) : evalDiv f D ≠ 0 := by
  classical
  rw [evalDiv, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun P hP ↦
    zpow_ne_zero _ (hf.val_ne_zero (Finsupp.mem_support_iff.mp hP))

/-- `f(D)` only depends on the values of `f` on the support of `D`. -/
lemma evalDiv_congr {f g : K} {D : Divisor κ K}
    (h : ∀ P, D P ≠ 0 → Place.val P f = Place.val P g) : evalDiv f D = evalDiv g D := by
  classical
  rw [evalDiv, evalDiv]
  exact Finset.prod_congr rfl fun P hP ↦ by dsimp only; rw [h P (Finsupp.mem_support_iff.mp hP)]

/-! ### Moving lemma -/

variable (κ K) in
/-- There are infinitely many places (`κ` is infinite; the zeros of `t - a`, `a ∈ κ`, are
distinct). -/
theorem infinite_place : Infinite (Place κ K) := by
  obtain ⟨t, ht⟩ := exists_transcendental κ K
  have htr : ∀ a : κ, Transcendental κ (t - algebraMap κ K a) := fun a h ↦
    ht (by simpa using (h.add (isAlgebraic_algebraMap (R := κ) (A := K) a)))
  choose P hP using fun a : κ ↦ Place.exists_ord_pos (htr a)
  refine Infinite.of_injective P fun a b hab ↦ ?_
  by_contra hne
  have hb := hP b
  rw [← hab] at hb
  have hsub : (t - algebraMap κ K b) - (t - algebraMap κ K a) = algebraMap κ K (a - b) := by
    rw [map_sub]; ring
  have hc : algebraMap κ K (a - b) ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hne)
  have h1 := (P a).min_le_ord_add (f := t - algebraMap κ K b) (g := -(t - algebraMap κ K a))
    (by rw [← sub_eq_add_neg, hsub]; exact hc)
  rw [← sub_eq_add_neg, hsub, (P a).ord_algebraMap_base, Place.ord_neg] at h1
  have := hP a
  omega

/-- **Prescribed orders at finitely many places**: for `n : Place → ℤ` and a finite set `S` there
is `h ≠ 0` with `ord_P h = n P` for `P ∈ S` (approximation theorem `exists_approx`). -/
theorem exists_ord_eq (S : Finset (Place κ K)) (n : Place κ K → ℤ) :
    ∃ h : K, h ≠ 0 ∧ ∀ P ∈ S, P.ord h = n P := by
  classical
  have := infinite_place κ K
  obtain ⟨Q₀, hQ₀⟩ := Infinite.exists_notMem_finset S
  choose π hπ using fun Q : Place κ K ↦ Q.exists_ord_eq_one
  have hπ0 : ∀ Q, π Q ≠ 0 := fun Q h ↦ by have := hπ Q; rw [h, Place.ord_zero] at this; omega
  set A : Divisor κ K := ∑ Q ∈ S, Finsupp.single Q (-(n Q + 1))
  have hA : ∀ Q ∈ S, A Q = -(n Q + 1) := by
    intro Q hQ
    simp only [A, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq', if_pos hQ]
  obtain ⟨x, hx⟩ := exists_approx A S Q₀ hQ₀ fun Q ↦ π Q ^ n Q
  have hα : ∀ Q, Q.ord (π Q ^ n Q) = n Q := fun Q ↦ by rw [Place.ord_zpow, hπ Q, mul_one]
  have hα0 : ∀ Q, π Q ^ n Q ≠ 0 := fun Q ↦ zpow_ne_zero _ (hπ0 Q)
  have key : ∀ Q ∈ S, x ≠ 0 → Q.ord x = n Q := by
    intro Q hQ hx0
    rcases hx Q hQ with h | h
    · rw [← sub_eq_zero.mp h, hα]
    · by_cases hne : π Q ^ n Q - x = 0
      · rw [← sub_eq_zero.mp hne, hα]
      rw [hA Q hQ, neg_neg] at h
      have hxe : x = π Q ^ n Q + -(π Q ^ n Q - x) := by ring
      rw [hxe, Q.ord_add_eq_of_lt (hα0 Q) (neg_ne_zero.mpr hne) (by rw [Place.ord_neg, hα]; omega),
        hα]
  by_cases hx0 : x = 0
  · by_cases hS : S = ∅
    · exact ⟨1, one_ne_zero, by simp [hS]⟩
    · exfalso
      obtain ⟨Q, hQ⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rcases hx Q hQ with h | h
      · rw [hx0, sub_zero] at h; exact hα0 Q h
      · rw [hx0, sub_zero, hA Q hQ, neg_neg, hα] at h; omega
  · exact ⟨x, hx0, fun Q hQ ↦ key Q hQ hx0⟩

/-- **Moving lemma**: every divisor is linearly equivalent to one avoiding a finite set `S`. -/
theorem exists_add_div_avoid (D : Divisor κ K) (S : Finset (Place κ K)) :
    ∃ h : K, h ≠ 0 ∧ ∀ P ∈ S, (D + Divisor.div κ h) P = 0 := by
  obtain ⟨h, h0, hh⟩ := exists_ord_eq S fun P ↦ -D P
  refine ⟨h, h0, fun P hP ↦ ?_⟩
  rw [Finsupp.add_apply, Divisor.div_apply, hh P hP, add_neg_cancel]

end CurvesJacobian
