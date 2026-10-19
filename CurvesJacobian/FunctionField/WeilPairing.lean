/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.FunctionField.WeilReciprocity
import CurvesJacobian.FunctionField.KummerPic

/-!
# The Weil pairing on the `n`-torsion of the divisor class group

Let `K/κ` be a function field of one variable over an algebraically closed field `κ` and
`n ≥ 1`. For `n`-torsion classes `a, b ∈ Pic(K)[n]` choose representatives `D`, `E` with disjoint
supports and functions `f`, `g` with `n D = div f`, `n E = div g`; the **Weil pairing** is

  `e_n(a, b) = f(E) / g(D) ∈ μ_n(κ)`

(Sutherland, *Elliptic curves* (MIT 18.783, 2019), Lecture 24, Def. 24.19, Lemma 24.21,
Thm. 24.22). It is well defined by Weil reciprocity (`CurvesJacobian.weil_reciprocity`).

* `CurvesJacobian.TorsRep n a`: a representative `D` of `a` together with `f`, `n D = div f`;
  `TorsRep.exists`, `TorsRep.exists_avoid` (moving lemma).
* `CurvesJacobian.pairVal D E f g = f(E) / g(D)` and its invariance
  (`pairVal_eq_of_rep`): independent of the representatives with disjoint supports.
* **`CurvesJacobian.weilPairing n a b`** and `weilPairing_eq` (computed by any disjoint
  representatives), `weilPairing_pow` (`e_n(a, b)^n = 1`), `weilPairing_ne_zero`,
  `weilPairing_add_left`, `weilPairing_add_right` (bilinear), `weilPairing_swap`
  (`e_n(a, b) e_n(b, a) = 1`), `weilPairing_mul` (compatibility across levels:
  `e_{nm}(a, b) = e_n(m a, b)` for `a ∈ Pic[nm]`, `b ∈ Pic[n]`).
-/

open WeilCurves.FunctionField

namespace CurvesJacobian

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

/-! ### Preliminaries -/

/-- A function without zeros and poles is a constant. -/
lemma exists_eq_algebraMap_of_div_eq_zero {u : K} (hu : Divisor.div κ u = 0) :
    ∃ c : κ, u = algebraMap κ K c := by
  have halg : IsAlgebraic κ u := (Place.isAlgebraic_iff_forall_ord_eq_zero).mpr fun P ↦ by
    have := congrArg (fun D : Divisor κ K ↦ D P) hu
    simpa using this
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ)
    (K := integralClosure κ K)).2 ⟨u, halg.isIntegral⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Two functions with the same divisor differ by a nonzero constant. -/
lemma exists_eq_const_mul_of_div_eq {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Divisor.div κ u = Divisor.div κ v) : ∃ c : κ, c ≠ 0 ∧ u = algebraMap κ K c * v := by
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_div_eq_zero (u := u / v) (by
    rw [Divisor.div_div (k := κ) hu hv, h, sub_self])
  refine ⟨c, fun h0 ↦ ?_, ?_⟩
  · rw [h0, map_zero, div_eq_zero_iff] at hc
    exact hc.elim hu hv
  · rw [← hc, div_mul_cancel₀ u hv]

/-- Supports are disjoint. -/
def DisjSupp (D E : Divisor κ K) : Prop := ∀ P, D P = 0 ∨ E P = 0

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma DisjSupp.symm {D E : Divisor κ K} (h : DisjSupp D E) : DisjSupp E D :=
  fun P ↦ (h P).symm

variable {n : ℕ}

/-- If `n D = div f` (`n ≠ 0`) and `E` is disjoint from `D`, then `f` avoids `E`. -/
lemma avoids_of_disjSupp {D E : Divisor κ K} {f : K} (hf : f ≠ 0)
    (hD : n • D = Divisor.div κ f) (h : DisjSupp D E) : Avoids f E := by
  refine ⟨hf, fun P hP ↦ ?_⟩
  have h1 := congrArg (fun F : Divisor κ K ↦ F P) hD
  simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply] at h1
  rw [← h1, ((h P).resolve_right hP), mul_zero]

lemma deg_eq_zero_of_nsmul_eq_div (hn : n ≠ 0) {D : Divisor κ K} {f : K}
    (hD : n • D = Divisor.div κ f) : D.deg = 0 := by
  have h := congrArg Divisor.deg hD
  rw [Divisor.deg_nsmul, Divisor.deg_div] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

/-! ### Representatives of torsion classes -/

/-- A representative `D` of a divisor class `a` with `n D = div f`. -/
structure TorsRep (n : ℕ) (a : Pic κ K) where
  /-- The divisor. -/
  D : Divisor κ K
  /-- The function with `n D = div f`. -/
  f : K
  f_ne : f ≠ 0
  mk_eq : (QuotientAddGroup.mk D : Pic κ K) = a
  nsmul_eq : n • D = Divisor.div κ f

/-- Every `n`-torsion class has a representative. -/
lemma TorsRep.exists {a : Pic κ K} (ha : n • a = 0) : Nonempty (TorsRep n a) := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at ha
  obtain ⟨f, hf, hfD⟩ := mem_principal.mp ha
  exact ⟨⟨D, f, hf, rfl, hfD.symm⟩⟩

/-- Moving a representative by `div h`. -/
noncomputable def TorsRep.move {a : Pic κ K} (r : TorsRep n a) {h : K} (hh : h ≠ 0) :
    TorsRep n a where
  D := r.D + Divisor.div κ h
  f := r.f * h ^ n
  f_ne := mul_ne_zero r.f_ne (pow_ne_zero n hh)
  mk_eq := by
    rw [QuotientAddGroup.mk_add, r.mk_eq, (QuotientAddGroup.eq_zero_iff _).mpr
      (div_mem_principal hh), add_zero]
  nsmul_eq := by rw [smul_add, r.nsmul_eq, Divisor.div_mul r.f_ne (pow_ne_zero n hh),
    Divisor.div_pow]

/-- **Moving lemma** for representatives: some representative avoids a finite set `S`. -/
lemma TorsRep.exists_avoid {a : Pic κ K} (ha : n • a = 0) (S : Finset (Place κ K)) :
    ∃ r : TorsRep n a, ∀ P ∈ S, r.D P = 0 := by
  obtain ⟨r⟩ := TorsRep.exists ha
  obtain ⟨h, hh, hS⟩ := exists_add_div_avoid r.D S
  exact ⟨r.move hh, hS⟩

/-- A representative disjoint from a given divisor. -/
lemma TorsRep.exists_disj {a : Pic κ K} (ha : n • a = 0) (E : Divisor κ K) :
    ∃ r : TorsRep n a, DisjSupp r.D E := by
  classical
  obtain ⟨r, hr⟩ := TorsRep.exists_avoid ha E.support
  refine ⟨r, fun P ↦ ?_⟩
  by_cases hP : P ∈ E.support
  · exact Or.inl (hr P hP)
  · exact Or.inr (Finsupp.notMem_support_iff.mp hP)

/-! ### The value `f(E) / g(D)` -/

/-- `f(E) / g(D)`. -/
noncomputable def pairVal (D E : Divisor κ K) (f g : K) : κ := evalDiv f E / evalDiv g D

lemma pairVal_swap (D E : Divisor κ K) (f g : K) : pairVal E D g f = (pairVal D E f g)⁻¹ := by
  rw [pairVal, pairVal, inv_div]

variable [NeZero n]

/-- **Invariance in the second argument**: moving `E` within its class (keeping disjointness)
does not change `f(E)/g(D)` (Sutherland, Lemma 24.21; by Weil reciprocity). -/
lemma pairVal_eq_right {a b : Pic κ K} (r : TorsRep n a) (s s' : TorsRep n b)
    (h : DisjSupp r.D s.D) (h' : DisjSupp r.D s'.D) :
    pairVal r.D s.D r.f s.f = pairVal r.D s'.D r.f s'.f := by
  have hn : n ≠ 0 := NeZero.ne n
  -- `s'.D = s.D + div u`
  have hmk : (QuotientAddGroup.mk (s'.D - s.D) : Pic κ K) = 0 := by
    rw [QuotientAddGroup.mk_sub, s.mk_eq, s'.mk_eq, sub_self]
  obtain ⟨u, hu, hudiv⟩ := mem_principal.mp (QuotientAddGroup.eq_zero_iff _ |>.mp hmk)
  have hE' : s'.D = s.D + Divisor.div κ u := by rw [hudiv]; abel
  -- `s'.f = c · s.f · uⁿ`
  have hdivg : Divisor.div κ s'.f = Divisor.div κ (s.f * u ^ n) := by
    rw [← s'.nsmul_eq, hE', smul_add, s.nsmul_eq, Divisor.div_mul s.f_ne (pow_ne_zero n hu),
      Divisor.div_pow]
  obtain ⟨c, hc, hcg⟩ := exists_eq_const_mul_of_div_eq s'.f_ne
    (mul_ne_zero s.f_ne (pow_ne_zero n hu)) hdivg
  -- avoidance facts
  have hfE : Avoids r.f s.D := avoids_of_disjSupp r.f_ne r.nsmul_eq h
  have hgD : Avoids s.f r.D := avoids_of_disjSupp s.f_ne s.nsmul_eq h.symm
  have hfu : Avoids r.f (Divisor.div κ u) := by
    refine ⟨r.f_ne, fun P hP ↦ ?_⟩
    have h1 : (Divisor.div κ u) P = s'.D P - s.D P := by rw [hE']; simp
    have hrP : r.D P = 0 := by
      rcases h P with h2 | h2
      · exact h2
      rcases h' P with h3 | h3
      · exact h3
      exact absurd (by rw [h1, h2, h3, sub_zero]) hP
    have h4 := congrArg (fun F : Divisor κ K ↦ F P) r.nsmul_eq
    simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply] at h4
    rw [← h4, hrP, mul_zero]
  have huD : Avoids u r.D := by
    refine ⟨hu, fun P hP ↦ ?_⟩
    have h1 : (Divisor.div κ u) P = s'.D P - s.D P := by rw [hE']; simp
    rw [← Divisor.div_apply (k := κ), h1, (h P).resolve_left hP, (h' P).resolve_left hP,
      sub_zero]
  have hrec := weil_reciprocity r.f_ne hu fun P ↦ by
    by_cases hP : r.D P = 0
    · left
      have h4 := congrArg (fun F : Divisor κ K ↦ F P) r.nsmul_eq
      simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply] at h4
      rw [← h4, hP, mul_zero]
    · exact Or.inr (huD.2 P hP)
  have hdegD : r.D.deg = 0 := deg_eq_zero_of_nsmul_eq_div hn r.nsmul_eq
  rw [pairVal, pairVal, hE', hcg, evalDiv_add hfE hfu,
    evalDiv_mul (avoids_algebraMap hc _) (hgD.mul (huD.pow n)), evalDiv_mul hgD (huD.pow n),
    evalDiv_algebraMap hc, hdegD, zpow_zero, one_mul, evalDiv_pow huD, ← evalDiv_nsmul huD,
    r.nsmul_eq, hrec]
  have h0 : evalDiv u (Divisor.div κ r.f) ≠ 0 := by
    rw [← r.nsmul_eq]; exact evalDiv_ne_zero (huD.nsmul n)
  have h1 : evalDiv s.f r.D ≠ 0 := evalDiv_ne_zero hgD
  field_simp

/-- Invariance in the first argument. -/
lemma pairVal_eq_left {a b : Pic κ K} (r r' : TorsRep n a) (s : TorsRep n b)
    (h : DisjSupp r.D s.D) (h' : DisjSupp r'.D s.D) :
    pairVal r.D s.D r.f s.f = pairVal r'.D s.D r'.f s.f := by
  rw [← inv_inj, ← pairVal_swap, ← pairVal_swap, pairVal_eq_right s r r' h.symm h'.symm]

/-- **Independence of the representatives.** -/
theorem pairVal_eq_of_rep {a b : Pic κ K} (hb : n • b = 0) (r r' : TorsRep n a)
    (s s' : TorsRep n b) (h : DisjSupp r.D s.D) (h' : DisjSupp r'.D s'.D) :
    pairVal r.D s.D r.f s.f = pairVal r'.D s'.D r'.f s'.f := by
  classical
  obtain ⟨s'', hs''⟩ := TorsRep.exists_avoid hb (r.D.support ∪ r'.D.support)
  have hd : ∀ (F : Divisor κ K), (∀ P ∈ F.support, s''.D P = 0) → DisjSupp F s''.D :=
    fun F hF P ↦ by
      by_cases hP : P ∈ F.support
      · exact Or.inr (hF P hP)
      · exact Or.inl (Finsupp.notMem_support_iff.mp hP)
  have h1 := hd r.D fun P hP ↦ hs'' P (Finset.mem_union_left _ hP)
  have h2 := hd r'.D fun P hP ↦ hs'' P (Finset.mem_union_right _ hP)
  rw [pairVal_eq_right r s s'' h h1, pairVal_eq_left r r' s'' h1 h2,
    pairVal_eq_right r' s'' s' h2 h']

omit [NeZero n] in
/-- A pair of representatives with disjoint supports exists. -/
lemma exists_disj_reps {a b : Pic κ K} (ha : n • a = 0) (hb : n • b = 0) :
    ∃ (r : TorsRep n a) (s : TorsRep n b), DisjSupp r.D s.D := by
  obtain ⟨r⟩ := TorsRep.exists ha
  obtain ⟨s, hs⟩ := TorsRep.exists_disj hb r.D
  exact ⟨r, s, hs.symm⟩

variable (n) in
/-- **The Weil pairing** `e_n : Pic(K)[n] × Pic(K)[n] → μ_n(κ)`, `e_n(a, b) = f(E)/g(D)`
(Sutherland, Lecture 24, Def. 24.19). -/
noncomputable def weilPairing (a b : picTorsion κ K n) : κ :=
  pairVal (exists_disj_reps a.2 b.2).choose.D (exists_disj_reps a.2 b.2).choose_spec.choose.D
    (exists_disj_reps a.2 b.2).choose.f (exists_disj_reps a.2 b.2).choose_spec.choose.f

/-- `e_n(a, b)` is computed by any representatives with disjoint supports. -/
theorem weilPairing_eq (a b : picTorsion κ K n) (r : TorsRep n (a : Pic κ K))
    (s : TorsRep n (b : Pic κ K)) (h : DisjSupp r.D s.D) :
    weilPairing n a b = pairVal r.D s.D r.f s.f :=
  pairVal_eq_of_rep b.2 _ r _ s (exists_disj_reps a.2 b.2).choose_spec.choose_spec h

omit [NeZero n] in
lemma pairVal_pow {a b : Pic κ K} (r : TorsRep n a) (s : TorsRep n b) (h : DisjSupp r.D s.D) :
    pairVal r.D s.D r.f s.f ^ n = 1 := by
  have hfE : Avoids r.f s.D := avoids_of_disjSupp r.f_ne r.nsmul_eq h
  have hgD : Avoids s.f r.D := avoids_of_disjSupp s.f_ne s.nsmul_eq h.symm
  rw [pairVal, div_pow, ← evalDiv_nsmul hfE, ← evalDiv_nsmul hgD, s.nsmul_eq, r.nsmul_eq,
    weil_reciprocity r.f_ne s.f_ne fun P ↦ ?_, div_self]
  · rw [← r.nsmul_eq]; exact evalDiv_ne_zero (hgD.nsmul n)
  · rcases h P with h1 | h1
    · left
      have h4 := congrArg (fun F : Divisor κ K ↦ F P) r.nsmul_eq
      simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply] at h4
      rw [← h4, h1, mul_zero]
    · right
      have h4 := congrArg (fun F : Divisor κ K ↦ F P) s.nsmul_eq
      simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply] at h4
      rw [← h4, h1, mul_zero]

/-- **`e_n(a, b) ∈ μ_n`.** -/
theorem weilPairing_pow (a b : picTorsion κ K n) : weilPairing n a b ^ n = 1 := by
  obtain ⟨r, s, h⟩ := exists_disj_reps a.2 b.2
  rw [weilPairing_eq a b r s h]
  exact pairVal_pow r s h

theorem weilPairing_ne_zero (a b : picTorsion κ K n) : weilPairing n a b ≠ 0 := fun h0 ↦ by
  have := weilPairing_pow a b
  rw [h0, zero_pow (NeZero.ne n)] at this
  exact zero_ne_one this

/-- **Skew symmetry** `e_n(a, b) e_n(b, a) = 1` (Sutherland, Thm. 24.22). -/
theorem weilPairing_swap (a b : picTorsion κ K n) :
    weilPairing n b a = (weilPairing n a b)⁻¹ := by
  obtain ⟨r, s, h⟩ := exists_disj_reps a.2 b.2
  rw [weilPairing_eq a b r s h, weilPairing_eq b a s r h.symm, pairVal_swap]

/-- The sum of two representatives. -/
noncomputable def TorsRep.add {a a' : Pic κ K} (r : TorsRep n a) (r' : TorsRep n a') :
    TorsRep n (a + a') where
  D := r.D + r'.D
  f := r.f * r'.f
  f_ne := mul_ne_zero r.f_ne r'.f_ne
  mk_eq := by rw [QuotientAddGroup.mk_add, r.mk_eq, r'.mk_eq]
  nsmul_eq := by rw [smul_add, r.nsmul_eq, r'.nsmul_eq, Divisor.div_mul r.f_ne r'.f_ne]

/-- **Bilinearity** in the first variable (Sutherland, Thm. 24.22). -/
theorem weilPairing_add_left (a a' b : picTorsion κ K n) :
    weilPairing n (a + a') b = weilPairing n a b * weilPairing n a' b := by
  classical
  obtain ⟨r⟩ := TorsRep.exists a.2
  obtain ⟨r'⟩ := TorsRep.exists a'.2
  obtain ⟨s, hs⟩ := TorsRep.exists_avoid b.2 (r.D.support ∪ r'.D.support)
  have hd : ∀ (F : Divisor κ K), (∀ P ∈ F.support, s.D P = 0) → DisjSupp F s.D :=
    fun F hF P ↦ by
      by_cases hP : P ∈ F.support
      · exact Or.inr (hF P hP)
      · exact Or.inl (Finsupp.notMem_support_iff.mp hP)
  have h1 := hd r.D fun P hP ↦ hs P (Finset.mem_union_left _ hP)
  have h2 := hd r'.D fun P hP ↦ hs P (Finset.mem_union_right _ hP)
  have h12 : DisjSupp (r.add r').D s.D := fun P ↦ by
    rcases h1 P with h | h
    · rcases h2 P with h' | h'
      · left; change r.D P + r'.D P = 0; rw [h, h', add_zero]
      · exact Or.inr h'
    · exact Or.inr h
  rw [weilPairing_eq (a + a') b (r.add r') s h12, weilPairing_eq a b r s h1,
    weilPairing_eq a' b r' s h2]
  have hfE : Avoids r.f s.D := avoids_of_disjSupp r.f_ne r.nsmul_eq h1
  have hfE' : Avoids r'.f s.D := avoids_of_disjSupp r'.f_ne r'.nsmul_eq h2
  have hgD : Avoids s.f r.D := avoids_of_disjSupp s.f_ne s.nsmul_eq h1.symm
  have hgD' : Avoids s.f r'.D := avoids_of_disjSupp s.f_ne s.nsmul_eq h2.symm
  change evalDiv (r.f * r'.f) s.D / evalDiv s.f (r.D + r'.D) = _
  rw [evalDiv_mul hfE hfE', evalDiv_add hgD hgD', pairVal, pairVal, mul_div_mul_comm]

lemma weilPairing_zero_left (b : picTorsion κ K n) : weilPairing n 0 b = 1 := by
  have h := weilPairing_add_left (0 : picTorsion κ K n) 0 b
  rw [add_zero] at h
  exact (mul_eq_left₀ (weilPairing_ne_zero 0 b)).mp h.symm

lemma weilPairing_zero_right (a : picTorsion κ K n) : weilPairing n a 0 = 1 := by
  rw [weilPairing_swap 0 a, weilPairing_zero_left, inv_one]

/-- Bilinearity in the second variable. -/
theorem weilPairing_add_right (a b b' : picTorsion κ K n) :
    weilPairing n a (b + b') = weilPairing n a b * weilPairing n a b' := by
  rw [weilPairing_swap (b + b') a, weilPairing_add_left, mul_inv, ← weilPairing_swap b a,
    ← weilPairing_swap b' a]

/-! ### Compatibility across levels and the alternating property -/

omit [NeZero n] in
lemma mem_picTorsion_mul_right {m : ℕ} {b : Pic κ K} (hb : b ∈ picTorsion κ K n) :
    b ∈ picTorsion κ K (n * m) := by
  change (n * m) • b = 0
  rw [mul_comm, ← smul_smul, (show n • b = 0 from hb), smul_zero]

omit [NeZero n] in
lemma nsmul_mem_picTorsion {m : ℕ} {a : Pic κ K} (ha : a ∈ picTorsion κ K (n * m)) :
    m • a ∈ picTorsion κ K n := by
  change n • m • a = 0
  rw [smul_smul]
  exact ha

/-- A level-`n` representative is a level-`nm` representative (with `f^m`). -/
def TorsRep.toMul {b : Pic κ K} (m : ℕ) (s : TorsRep n b) : TorsRep (n * m) b where
  D := s.D
  f := s.f ^ m
  f_ne := pow_ne_zero m s.f_ne
  mk_eq := s.mk_eq
  nsmul_eq := by rw [mul_comm, ← smul_smul, s.nsmul_eq, Divisor.div_pow]

/-- A level-`nm` representative of `a` gives a level-`n` representative of `m a`. -/
noncomputable def TorsRep.ofMul {a : Pic κ K} (m : ℕ) (r : TorsRep (n * m) a) :
    TorsRep n (m • a) where
  D := m • r.D
  f := r.f
  f_ne := r.f_ne
  mk_eq := by rw [QuotientAddGroup.mk_nsmul, r.mk_eq]
  nsmul_eq := by rw [smul_smul]; exact r.nsmul_eq

/-- **Compatibility across levels**: `e_{nm}(a, b) = e_n(m a, b)` for `a ∈ Pic[nm]`,
`b ∈ Pic[n]` (cf. Milne, *Abelian Varieties*, Lemma 13.1). -/
theorem weilPairing_mul {m : ℕ} [NeZero (n * m)] (a : picTorsion κ K (n * m))
    (b : picTorsion κ K n) :
    weilPairing (n * m) a ⟨b, mem_picTorsion_mul_right b.2⟩ =
      weilPairing n ⟨m • (a : Pic κ K), nsmul_mem_picTorsion a.2⟩ b := by
  obtain ⟨r⟩ := TorsRep.exists a.2
  obtain ⟨s, hs⟩ := TorsRep.exists_disj b.2 r.D
  have h := hs.symm
  have h' : DisjSupp (r.ofMul m).D s.D := fun P ↦ by
    rcases h P with h1 | h1
    · left; change m • r.D P = 0; rw [h1, smul_zero]
    · exact Or.inr h1
  rw [weilPairing_eq a ⟨b, _⟩ r (s.toMul m) h,
    weilPairing_eq ⟨m • (a : Pic κ K), _⟩ b (r.ofMul m) s h']
  have hgD : Avoids s.f r.D := avoids_of_disjSupp s.f_ne s.nsmul_eq h.symm
  change evalDiv r.f s.D / evalDiv (s.f ^ m) r.D = evalDiv r.f s.D / evalDiv s.f (m • r.D)
  rw [evalDiv_pow hgD, evalDiv_nsmul hgD]

/-- `e_n(a, a)² = 1`. -/
lemma weilPairing_self_sq (a : picTorsion κ K n) : weilPairing n a a ^ 2 = 1 := by
  have h := weilPairing_swap a a
  have h0 := weilPairing_ne_zero a a
  rw [sq]
  nth_rw 1 [h]
  exact inv_mul_cancel₀ h0

/-- **The Weil pairing is alternating**, `e_n(a, a) = 1`, provided `a` is divisible by `2` in
`Pic[2n]` (true when `#Pic[d] = d^{2g}` for all `d`, `CurvesJacobian.mulTorsion_surjective`). -/
theorem weilPairing_self (a : picTorsion κ K n)
    (h2 : ∃ a' : picTorsion κ K (n * 2), 2 • (a' : Pic κ K) = a) : weilPairing n a a = 1 := by
  obtain ⟨a', ha'⟩ := h2
  have hb : (⟨a, mem_picTorsion_mul_right a.2⟩ : picTorsion κ K (n * 2)) = a' + a' := by
    apply Subtype.ext
    change (a : Pic κ K) = a' + a'
    rw [← ha', two_nsmul]
  have key := weilPairing_mul (m := 2) a' a
  have ha : (⟨2 • (a' : Pic κ K), nsmul_mem_picTorsion a'.2⟩ : picTorsion κ K n) = a :=
    Subtype.ext ha'
  rw [ha, hb, weilPairing_add_right, ← sq, weilPairing_self_sq] at key
  exact key.symm

end CurvesJacobian
