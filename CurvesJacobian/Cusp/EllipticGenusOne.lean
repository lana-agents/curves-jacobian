/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiPi1
import CurvesJacobian.Cusp.GenusLocAnEq
import CurvesJacobian.Cusp.GenusBaseChange
import CurvesJacobian.Scheme.PointDegree

/-!
# `Ē` has genus one and `E ∖ {O}` has exactly one cusp

Let `E` be an elliptic curve over a field `K` of characteristic zero, `Ē = curveE E` its smooth
projective model and `X = E ∖ {O} = XE E`. We prove

* `CurvesJacobian.Cusp.curveGenus_curveE₂`: `g(Ē) = 1` (Riemann–Roch genus of `K(Ē)`), hence
  `CurvesJacobian.Cusp.curveGenus_baseChange_curveE`: `g(Ē_Ω) = 1` for every algebraically closed
  `Ω ⊇ K`;
* `CurvesJacobian.Cusp.cuspDegree_XE₂`: `Σ_{c ∉ X} [κ(c) : K] = 1`, hence
  `CurvesJacobian.Cusp.card_compl_baseChangeOpen_XE`: `X_Ω ⊆ Ē_Ω` has exactly one cusp.

These are the hypotheses `hg`, `hr` of `CurvesJacobian.Cusp.dupPiU_inf_Delta`.

**Genus.** Work in a function field `F / k` with `x, y ∈ F` satisfying a Weierstrass equation,
`x` transcendental and `[F : k(x)] = 2`. At a place `P` with `x ∈ 𝒪_P` also `y ∈ 𝒪_P`
(`CurvesJacobian.Cusp.mem_of_weq₂`); at a pole of `x`, `2 ord_P y = 3 ord_P x`
(`CurvesJacobian.Cusp.two_mul_ord_eq_of_weq₂`). Hence for `D = n (x)_∞` the `2n` functions
`x^i` (`i ≤ n`) and `x^i y` (`i ≤ n - 2`) lie in `L(D)`, and they are linearly independent
(at a pole of `x` the orders of `A(x)` and `B(x) y` have different parities). Riemann–Roch for
`deg D = 2n > 2g - 2` gives `2n ≤ ℓ(D) = 2n + 1 - g`, so `g ≤ 1`
(`CurvesJacobian.Cusp.genus_le_one_of_weq₂`); `g ≥ 1` is `one_le_curveGenus_curveE`.

**Cusp.** `deg (x)_∞ = 2` and every pole of `x` has even order `≥ 2`, so `x` has a unique pole
`P_∞`, of degree one (`CurvesJacobian.Cusp.exists_unique_pole_of_weq₂`). A place whose point
lies in `X` contains `x` (`x ∈ Γ(X)`); conversely if `x ∈ 𝒪_P` for a place `P` outside `X` then
every function regular outside `X` lies in `𝒪_P` (`Γ(X)` is the integral closure of `K[x]`,
`mem_range_germ_XE_iff`), so `L(2P) ⊆ L(0)`, contradicting Riemann–Roch `ℓ(2P) = 2 deg P ≥ 2`.
Hence `Ē ∖ X = {P_∞}`.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi WeilCurves.FunctionField Module
open WeierstrassCurve.Affine.CoordinateRing
open scoped IntermediateField

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Order estimates at a place -/

section OrdGe

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k] [IsFunctionField k F]

/-- `f = 0` or `c ≤ ord_P f`. -/
def OrdGe₂ (P : Place k F) (c : ℤ) (f : F) : Prop := f = 0 ∨ c ≤ P.ord f

variable {P : Place k F}

lemma ordGe₂_mono {c c' : ℤ} {f : F} (h : c' ≤ c) (hf : OrdGe₂ P c f) : OrdGe₂ P c' f :=
  hf.imp_right h.trans

lemma ordGe₂_add {c : ℤ} {f g : F} (hf : OrdGe₂ P c f) (hg : OrdGe₂ P c g) :
    OrdGe₂ P c (f + g) := by
  by_cases h : f + g = 0
  · exact Or.inl h
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_add]; exact hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [add_zero]; exact hf
  exact Or.inr ((le_min (hf.resolve_left hf0) (hg.resolve_left hg0)).trans (P.min_le_ord_add h))

lemma ordGe₂_mul {c d e : ℤ} {f g : F} (hf : OrdGe₂ P c f) (hg : OrdGe₂ P d g)
    (he : e ≤ c + d) : OrdGe₂ P e (f * g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Or.inl (zero_mul g)
  rcases eq_or_ne g 0 with rfl | hg0
  · exact Or.inl (mul_zero f)
  refine Or.inr ?_
  rw [P.ord_mul hf0 hg0]
  have := hf.resolve_left hf0
  have := hg.resolve_left hg0
  omega

lemma ordGe₂_ord (f : F) : OrdGe₂ P (P.ord f) f := Or.inr le_rfl

lemma ordGe₂_algebraMap (c : k) : OrdGe₂ P 0 (algebraMap k F c) :=
  Or.inr (P.ord_algebraMap_base c).ge

lemma ordGe₂_zero_iff {f : F} : OrdGe₂ P 0 f ↔ f ∈ P.1 := P.mem_iff_ord_nonneg.symm

lemma ordGe₂_pow {a : ℤ} {x : F} (hx : OrdGe₂ P a x) (n : ℕ) : OrdGe₂ P (n * a) (x ^ n) := by
  induction n with
  | zero => exact Or.inr (by rw [pow_zero, P.ord_one]; simp)
  | succ n ih =>
    rw [pow_succ]
    exact ordGe₂_mul ih hx (by push_cast; linarith)

lemma ordGe₂_sum {ι : Type*} (s : Finset ι) {c : ℤ} {f : ι → F}
    (hf : ∀ i ∈ s, OrdGe₂ P c (f i)) : OrdGe₂ P c (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl Finset.sum_empty
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ordGe₂_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- `ord_P (A(x)) ≥ m · a` if `ord_P x ≥ a`, `a ≤ 0` and `deg A ≤ m`. -/
lemma ordGe₂_aeval {a : ℤ} (ha : a ≤ 0) {x : F} (hx : OrdGe₂ P a x) {m : ℕ} (A : k[X])
    (hA : A.natDegree ≤ m) : OrdGe₂ P (m * a) (aeval x A) := by
  rw [aeval_eq_sum_range]
  refine ordGe₂_sum _ fun i hi ↦ ?_
  have hi' : (i : ℤ) ≤ m := by
    have := Finset.mem_range.1 hi
    exact_mod_cast (by omega : i ≤ m)
  rw [Algebra.smul_def]
  refine ordGe₂_mul (ordGe₂_algebraMap _) (ordGe₂_pow hx i) ?_
  nlinarith

lemma aeval_mem₂ {x : F} (hx : x ∈ P.1) (A : k[X]) : aeval x A ∈ P.1 :=
  ordGe₂_zero_iff.1 (ordGe₂_mono (by simp) (ordGe₂_aeval le_rfl (ordGe₂_zero_iff.2 hx) A le_rfl))

lemma ordGe₂_of_mem {c : ℤ} {f : F} (hf : f ∈ P.1) (hc : c ≤ 0) : OrdGe₂ P c f :=
  ordGe₂_mono hc (ordGe₂_zero_iff.2 hf)

/-- `ord_P (u + v) = ord_P u` if `ord_P u < c ≤ ord_P v`. -/
lemma ord_add_eq_of_ordGe₂ {c : ℤ} {u v : F} (hv : OrdGe₂ P c v) (hu0 : u ≠ 0)
    (hu : P.ord u < c) : P.ord (u + v) = P.ord u := by
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [add_zero]
  exact P.ord_add_eq_of_lt hu0 hv0 (hu.trans_le (hv.resolve_left hv0))

/-- **At a pole of `x`, `ord_P (A(x)) = deg A · ord_P x`.** -/
lemma ord_aeval_eq₂ {x : F} (hx0 : x ≠ 0) (ha : P.ord x < 0) {A : k[X]} (hA : A ≠ 0) :
    P.ord (aeval x A) = A.natDegree * P.ord x := by
  have hlc : algebraMap k F A.leadingCoeff ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap k F).injective).2 (leadingCoeff_ne_zero.2 hA)
  have hv0 : algebraMap k F A.leadingCoeff * x ^ A.natDegree ≠ 0 :=
    mul_ne_zero hlc (pow_ne_zero _ hx0)
  have hv : P.ord (algebraMap k F A.leadingCoeff * x ^ A.natDegree) = A.natDegree * P.ord x := by
    rw [P.ord_mul hlc (pow_ne_zero _ hx0), P.ord_algebraMap_base, P.ord_pow, zero_add]
  have hsplit : aeval x A =
      algebraMap k F A.leadingCoeff * x ^ A.natDegree + aeval x A.eraseLead := by
    conv_lhs => rw [← A.eraseLead_add_C_mul_X_pow]
    rw [map_add, map_mul, aeval_C, map_pow, aeval_X, add_comm]
  rcases A.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | h0
  · have hu := ordGe₂_aeval (P := P) ha.le (ordGe₂_ord x) A.eraseLead
      (m := A.natDegree - 1) (by omega)
    rcases eq_or_ne (aeval x A.eraseLead) 0 with hz | hz
    · rw [hsplit, hz, add_zero, hv]
    · have h1 := hu.resolve_left hz
      have h2 : ((A.natDegree - 1 : ℕ) : ℤ) = A.natDegree - 1 := by
        have : 1 ≤ A.natDegree := by omega
        push_cast [this]
        ring
      rw [h2] at h1
      rw [hsplit, P.ord_add_eq_of_lt hv0 hz (by rw [hv]; nlinarith), hv]
  · rw [hsplit, h0, map_zero, add_zero, hv]

end OrdGe

/-! ### Weierstrass functions in a function field -/

section Weierstrass

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k] [IsFunctionField k F]
  (W : WeierstrassCurve k) {x y : F}

/-- The Weierstrass equation for `x, y ∈ F`. -/
abbrev WEq₂ (W : WeierstrassCurve k) (x y : F) : Prop :=
  y ^ 2 + algebraMap k F W.a₁ * x * y + algebraMap k F W.a₃ * y =
    x ^ 3 + algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x + algebraMap k F W.a₆

omit [PerfectField k] [IsFunctionField k F] in
lemma weq₂_factor (h : WEq₂ W x y) :
    y * (y + (algebraMap k F W.a₁ * x + algebraMap k F W.a₃)) =
      x ^ 3 + (algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x + algebraMap k F W.a₆) := by
  linear_combination h


/-- **`y` is integral where `x` is.** -/
lemma mem_of_weq₂ (h : WEq₂ W x y) {P : Place k F} (hx : x ∈ P.1) : y ∈ P.1 := by
  by_contra hy
  have hb : P.ord y < 0 := P.ord_neg_iff.2 hy
  have hy0 : y ≠ 0 := fun h0 ↦ hy (by rw [h0]; exact zero_mem _)
  have hu : algebraMap k F W.a₁ * x + algebraMap k F W.a₃ ∈ P.1 :=
    add_mem (mul_mem (P.algebraMap_mem _) hx) (P.algebraMap_mem _)
  have hyu := ord_add_eq_of_ordGe₂ (ordGe₂_zero_iff.2 hu) hy0 hb
  have hyu0 : y + (algebraMap k F W.a₁ * x + algebraMap k F W.a₃) ≠ 0 := by
    intro h0
    rw [h0, P.ord_zero] at hyu
    omega
  have hR : x ^ 3 + (algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x +
      algebraMap k F W.a₆) ∈ P.1 :=
    add_mem (pow_mem hx 3) (add_mem (add_mem (mul_mem (P.algebraMap_mem _) (pow_mem hx 2))
      (mul_mem (P.algebraMap_mem _) hx)) (P.algebraMap_mem _))
  rw [← weq₂_factor W h] at hR
  have h1 := P.ord_nonneg_of_mem hR
  rw [P.ord_mul hy0 hyu0, hyu] at h1
  omega

/-- **At a pole of `x`: `2 ord_P y = 3 ord_P x`.** -/
lemma two_mul_ord_eq_of_weq₂ (h : WEq₂ W x y) {P : Place k F} (hx : x ∉ P.1) :
    2 * P.ord y = 3 * P.ord x := by
  have ha : P.ord x < 0 := P.ord_neg_iff.2 hx
  have hx0 : x ≠ 0 := fun h0 ↦ hx (by rw [h0]; exact zero_mem _)
  have hx' : OrdGe₂ P (P.ord x) x := ordGe₂_ord x
  have hr : OrdGe₂ P (2 * P.ord x)
      (algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x + algebraMap k F W.a₆) :=
    ordGe₂_add (ordGe₂_add
      (ordGe₂_mul (ordGe₂_algebraMap _) (ordGe₂_pow hx' 2) (by push_cast; omega))
      (ordGe₂_mul (ordGe₂_algebraMap _) hx' (by omega)))
      (ordGe₂_mono (by omega) (ordGe₂_algebraMap _))
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero _ hx0
  have hR : P.ord (x ^ 3 + (algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x +
      algebraMap k F W.a₆)) = 3 * P.ord x := by
    rw [ord_add_eq_of_ordGe₂ hr hx3 (by rw [P.ord_pow]; push_cast; omega), P.ord_pow]
    norm_num
  have hL := weq₂_factor W h
  have hR0 : x ^ 3 + (algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x +
      algebraMap k F W.a₆) ≠ 0 := by
    intro h0
    rw [h0, P.ord_zero] at hR
    omega
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hL
    exact hR0 hL.symm
  have hyu0 : y + (algebraMap k F W.a₁ * x + algebraMap k F W.a₃) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hL
    exact hR0 hL.symm
  have hord := congrArg P.ord hL
  rw [P.ord_mul hy0 hyu0, hR] at hord
  have hu : OrdGe₂ P (P.ord x) (algebraMap k F W.a₁ * x + algebraMap k F W.a₃) :=
    ordGe₂_add (ordGe₂_mul (ordGe₂_algebraMap _) hx' (by omega))
      (ordGe₂_mono ha.le (ordGe₂_algebraMap _))
  by_cases hb : P.ord y < P.ord x
  · rw [ord_add_eq_of_ordGe₂ hu hy0 hb] at hord
    omega
  · have h1 : OrdGe₂ P (P.ord x) (y + (algebraMap k F W.a₁ * x + algebraMap k F W.a₃)) :=
      ordGe₂_add (Or.inr (by omega)) hu
    have := h1.resolve_left hyu0
    omega

/-- **`A(x) + B(x) y = 0` forces `A = B = 0`**: at a pole of `x` the orders of `A(x)` and
`B(x) y` have different parities. -/
lemma eq_zero_of_aeval_add_mul₂ (h : WEq₂ W x y) (hx : Transcendental k x) {P : Place k F}
    (hP : P.ord x < 0) {A B : k[X]} (hAB : aeval x A + aeval x B * y = 0) : A = 0 ∧ B = 0 := by
  have hx0 : x ≠ 0 := ne_zero_of_transcendental hx
  have hyx := two_mul_ord_eq_of_weq₂ W h (P.ord_neg_iff.1 hP)
  have hne : ∀ C : k[X], C ≠ 0 → aeval x C ≠ 0 := fun C hC h0 ↦ hx ⟨C, hC, h0⟩
  by_cases hB : B = 0
  · rw [hB, map_zero, zero_mul, add_zero] at hAB
    exact ⟨by_contra fun hA ↦ hne A hA hAB, hB⟩
  exfalso
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, P.ord_zero] at hyx
    omega
  have hBy : aeval x B * y ≠ 0 := mul_ne_zero (hne B hB) hy0
  have hA : A ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_add] at hAB
    exact hBy hAB
  have h1 : aeval x A = -(aeval x B * y) := eq_neg_of_add_eq_zero_left hAB
  have h2 := congrArg P.ord h1
  rw [P.ord_neg, P.ord_mul (hne B hB) hy0, ord_aeval_eq₂ hx0 hP hA, ord_aeval_eq₂ hx0 hP hB] at h2
  have h3 : P.ord x * (2 * A.natDegree - 2 * B.natDegree - 3) = 0 := by
    linear_combination 2 * h2 + hyx
  rcases mul_eq_zero.1 h3 with h4 | h4
  · omega
  · omega

omit [PerfectField k] [IsFunctionField k F] in
lemma natDegree_le_of_mem_degreeLT₂ {p : k[X]} {m : ℕ} (hp : p ∈ degreeLT k (m + 1)) :
    p.natDegree ≤ m := by
  rcases eq_or_ne p 0 with rfl | h0
  · simp
  · have := (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
    omega

variable (k) in
/-- `(A, B) ↦ A(x) + B(x) y` on `k[X]_{< n + 1} × k[X]_{< n - 1}`. -/
def weqMap₂ (x y : F) (n : ℕ) : degreeLT k (n + 1) × degreeLT k (n - 1) →ₗ[k] F :=
  LinearMap.coprod ((aeval x).toLinearMap ∘ₗ (degreeLT k (n + 1)).subtype)
    (LinearMap.mulRight k y ∘ₗ (aeval x).toLinearMap ∘ₗ (degreeLT k (n - 1)).subtype)

omit [PerfectField k] [IsFunctionField k F] in
lemma weqMap₂_apply (x y : F) (n : ℕ) (p : degreeLT k (n + 1) × degreeLT k (n - 1)) :
    weqMap₂ k x y n p = aeval x (p.1 : k[X]) + aeval x (p.2 : k[X]) * y :=
  rfl

/-- **A function field with a Weierstrass pair `(x, y)`, `[F : k(x)] = 2`, has genus `≤ 1`.** -/
theorem genus_le_one_of_weq₂ (h : WEq₂ W x y) (hx : Transcendental k x)
    (h2 : finrank k⟮x⟯ F = 2) : genus k F ≤ 1 := by
  obtain ⟨P₀, hP₀⟩ := Place.exists_ord_neg hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (genus k F).toNat + 1 := ⟨_, rfl⟩
  have hg := Int.self_le_toNat (genus k F)
  have hdeg : (n • Divisor.polarDivisor k x).deg = 2 * n := by
    rw [Divisor.deg_nsmul, Divisor.deg_polarDivisor hx, h2]
    push_cast
    ring
  have hell := ell_eq_of_deg_gt (A := n • Divisor.polarDivisor k x) (by rw [hdeg]; omega)
  have hDv : ∀ P : Place k F, (n • Divisor.polarDivisor k x) P = n * max 0 (-P.ord x) :=
    fun P ↦ by rw [Finsupp.smul_apply, Divisor.polarDivisor_apply, nsmul_eq_mul]
  have hmem : ∀ f : F, (∀ P : Place k F, OrdGe₂ P (-(n * max 0 (-P.ord x))) f) →
      f ∈ Divisor.L (n • Divisor.polarDivisor k x) := by
    intro f hf
    refine Divisor.mem_L.2 ?_
    by_cases h0 : f = 0
    · exact Or.inl h0
    · exact Or.inr fun P ↦ by rw [hDv P]; exact (hf P).resolve_left h0
  have hA : ∀ A : k[X], A.natDegree ≤ n → aeval x A ∈ Divisor.L (n • Divisor.polarDivisor k x) := by
    intro A hA
    refine hmem _ fun P ↦ ?_
    by_cases hxP : x ∈ P.1
    · exact ordGe₂_of_mem (aeval_mem₂ hxP A)
        (neg_nonpos.2 (mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)))
    · have ha := P.ord_neg_iff.2 hxP
      refine ordGe₂_mono (le_of_eq ?_) (ordGe₂_aeval ha.le (ordGe₂_ord x) A hA)
      rw [max_eq_right (by omega)]
      ring
  have hB : ∀ B : k[X], B.natDegree + 2 ≤ n →
      aeval x B * y ∈ Divisor.L (n • Divisor.polarDivisor k x) := by
    intro B hB
    refine hmem _ fun P ↦ ?_
    by_cases hxP : x ∈ P.1
    · exact ordGe₂_of_mem (mul_mem (aeval_mem₂ hxP B) (mem_of_weq₂ W h hxP))
        (neg_nonpos.2 (mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)))
    · have ha := P.ord_neg_iff.2 hxP
      have hyx := two_mul_ord_eq_of_weq₂ W h hxP
      refine ordGe₂_mul (ordGe₂_aeval ha.le (ordGe₂_ord x) B le_rfl) (ordGe₂_ord y) ?_
      rw [max_eq_right (by omega)]
      have h3 : (0 : ℤ) ≤ n - (B.natDegree + 2) := by omega
      nlinarith [mul_nonneg h3 (by omega : (0 : ℤ) ≤ -P.ord x)]
  have hrange : ∀ p, weqMap₂ k x y n p ∈ Divisor.L (n • Divisor.polarDivisor k x) := by
    intro p
    rw [weqMap₂_apply]
    refine add_mem (hA _ (natDegree_le_of_mem_degreeLT₂ p.1.2)) ?_
    rcases eq_or_ne (p.2 : k[X]) 0 with h0 | h0
    · rw [h0, map_zero, zero_mul]
      exact zero_mem _
    · refine hB _ ?_
      have := (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 p.2.2)
      omega
  have hinj : Function.Injective (weqMap₂ k x y n) := by
    refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
    rw [weqMap₂_apply] at hp
    obtain ⟨h1, h2⟩ := eq_zero_of_aeval_add_mul₂ W h hx hP₀ hp
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (weqMap₂ k x y n).codRestrict _ hrange)
    (fun a b hab ↦ hinj (congrArg Subtype.val hab))
  rw [Module.finrank_prod, (degreeLTEquiv k _).finrank_eq, (degreeLTEquiv k _).finrank_eq,
    Module.finrank_fin_fun, Module.finrank_fin_fun] at hle
  have hle' : n + 1 + (n - 1) ≤ Divisor.ell (n • Divisor.polarDivisor k x) := hle
  rw [hdeg] at hell
  omega

/-- **`x` has a unique pole, and it has degree one.** -/
theorem exists_unique_pole_of_weq₂ (h : WEq₂ W x y) (hx : Transcendental k x)
    (h2 : finrank k⟮x⟯ F = 2) :
    ∃ P : Place k F, x ∉ P.1 ∧ P.deg = 1 ∧ ∀ Q : Place k F, x ∉ Q.1 → Q = P := by
  have hdeg : (Divisor.polarDivisor k x).deg = 2 := by
    simp [Divisor.deg_polarDivisor hx, h2]
  have hnn : ∀ R : Place k F, 0 ≤ Divisor.polarDivisor k x R := fun R ↦ by
    rw [Divisor.polarDivisor_apply]
    exact le_max_left _ _
  have hpole : ∀ Q : Place k F, x ∉ Q.1 → 2 ≤ Divisor.polarDivisor k x Q := by
    intro Q hQ
    have h1 := two_mul_ord_eq_of_weq₂ W h hQ
    have h3 := Q.ord_neg_iff.2 hQ
    rw [Divisor.polarDivisor_apply, max_eq_right (by omega)]
    omega
  have hle1 : ∀ Q : Place k F, x ∉ Q.1 → Q.deg = 1 := by
    intro Q hQ
    have hle : Finsupp.single Q 2 ≤ Divisor.polarDivisor k x := by
      refine Finsupp.le_def.2 fun R ↦ ?_
      rw [Finsupp.single_apply]
      split_ifs with hQR
      · rw [← hQR]
        exact hpole _ hQ
      · exact hnn R
    have h3 := Divisor.deg_mono hle
    rw [Divisor.deg_single, hdeg] at h3
    have := Q.deg_pos
    omega
  obtain ⟨P, hP⟩ := Place.exists_ord_neg hx
  have hxP : x ∉ P.1 := P.ord_neg_iff.1 hP
  refine ⟨P, hxP, hle1 P hxP, fun Q hQ ↦ ?_⟩
  by_contra hQP
  have hle : Finsupp.single P 2 + Finsupp.single Q 2 ≤ Divisor.polarDivisor k x := by
    refine Finsupp.le_def.2 fun R ↦ ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hPR : P = R
    · rw [if_pos hPR, if_neg (fun h' ↦ hQP (h'.trans hPR.symm))]
      have := hpole R (hPR ▸ hxP)
      omega
    · by_cases hQR : Q = R
      · rw [if_neg hPR, if_pos hQR]
        have := hpole R (hQR ▸ hQ)
        omega
      · rw [if_neg hPR, if_neg hQR]
        have := hnn R
        omega
  have h3 := Divisor.deg_mono hle
  rw [Divisor.deg_add, Divisor.deg_single, Divisor.deg_single, hdeg] at h3
  have := P.deg_pos
  have := Q.deg_pos
  omega

omit [PerfectField k] [IsFunctionField k F] in
/-- An element integral over `k[x] ⊆ 𝒪_P` lies in `𝒪_P`. -/
lemma mem_of_isIntegral_adjoin₂ {P : Place k F} {z : F} (hx : x ∈ P.1)
    (hz : IsIntegral (Algebra.adjoin k {x}) z) : z ∈ P.1 := by
  have hle : (Algebra.adjoin k {x}).toSubring ≤ P.1.toSubring := by
    intro w hw
    change w ∈ Algebra.adjoin k {x} at hw
    induction hw using Algebra.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hx
    | algebraMap c => exact P.algebraMap_mem c
    | add w v _ _ hw hv => exact add_mem hw hv
    | mul w v _ _ hw hv => exact mul_mem hw hv
  obtain ⟨p, hpm, hp⟩ := hz
  have hc : (algebraMap P.1 F).comp (Subring.inclusion hle) =
      algebraMap (Algebra.adjoin k {x}) F := RingHom.ext fun _ ↦ rfl
  have hint : IsIntegral P.1 z :=
    ⟨p.map (Subring.inclusion hle), hpm.map _, by rw [eval₂_map, hc]; exact hp⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hw]
  exact w.2

end Weierstrass

/-! ### The elliptic curve `Ē` -/

section Curve

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **`[K(Ē) : K(x)] = 2`.** -/
theorem finrank_adjoin_xN₂ : finrank K⟮xN E⟯ (curveE E).functionField = 2 := by
  have hφ : (funFieldAlgEquivE E : (curveE E).functionField →ₐ[K] E.toAffine.FunctionField)
      (xN E) = genX E.toAffine := funFieldEquivE_xN E
  have hmap : (IntermediateField.adjoin K {xN E}).map
      (funFieldAlgEquivE E : (curveE E).functionField →ₐ[K] E.toAffine.FunctionField) =
      ratFuncRange E.toAffine := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hφ, ratFuncRange_eq_adjoin]
  rw [← finrank_ratFuncRange (W := E.toAffine)]
  exact Algebra.finrank_eq_of_equiv_equiv
    ((IntermediateField.equivMap _ (funFieldAlgEquivE E :
      (curveE E).functionField →ₐ[K] E.toAffine.FunctionField)).trans
        (IntermediateField.equivOfEq hmap)).toRingEquiv
    (funFieldEquivE E) (RingHom.ext fun _ ↦ rfl)

/-- **`Ē` has genus one** (Riemann–Roch genus of `K(Ē)`). -/
theorem curveGenus_curveE₂ :
    haveI := IsCurveOver.isIntegral K (curveE E)
    curveGenus K (curveE E) = 1 := by
  haveI := IsCurveOver.isIntegral K (curveE E)
  have h1 := locAn_curveGenus_eq K (curveE E)
  have h2 := one_le_curveGenus_curveE E
  have h3 : curveGenus K (curveE E) ≤ 1 :=
    genus_le_one_of_weq₂ E (wEq_curveE E) (transcendental_xN E) (finrank_adjoin_xN₂ E)
  omega

/-- **`Ē_Ω` has genus one** for every algebraically closed `Ω ⊇ K` (hypothesis `hg` of
`CurvesJacobian.Cusp.dupPiU_inf_Delta`). -/
theorem curveGenus_baseChange_curveE (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    haveI := IsCurveOver.isIntegral Ω (baseChange K Ω (curveE E))
    (curveGenus Ω (baseChange K Ω (curveE E))).toNat = 1 := by
  haveI := IsCurveOver.isIntegral K (curveE E)
  haveI := IsCurveOver.isIntegral Ω (baseChange K Ω (curveE E))
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have h := curveGenus_baseChange K Ω (curveE E)
  rw [curveGenus_curveE₂ E] at h
  rw [h]
  rfl

omit [E.IsElliptic] in
lemma nonempty_XE₂ : Nonempty (XE E) := ((VE_nonempty E).mono (VE_le_XE E)).to_subtype

/-- A place whose point lies in `E ∖ {O}` contains `x`. -/
lemma xN_mem_of_mem_XE₂ (Q : Place K (curveE E).functionField)
    (hQ : pointOfPlace K (curveE E) Q ∈ XE E) : xN E ∈ Q.1 := by
  haveI := nonempty_XE₂ E
  have h : xN E ∈ regularOutside K (placesOutside K (curveE E) (XE E)) :=
    (mem_regularOutside_iff K (curveE E) (XE E) (mem_placesOutside K (curveE E) (XE E)) _).2
      ⟨xX E, germ_xX E⟩
  exact h Q fun hQ' ↦ (mem_placesOutside K (curveE E) (XE E) Q).1 hQ' hQ

/-- **A place whose point is not in `E ∖ {O}` is a pole of `x`.** -/
lemma xN_not_mem_of_not_mem_XE₂ (Q : Place K (curveE E).functionField)
    (hQ : pointOfPlace K (curveE E) Q ∉ XE E) : xN E ∉ Q.1 := by
  haveI := nonempty_XE₂ E
  intro hxQ
  have hQS : Q ∈ placesOutside K (curveE E) (XE E) :=
    (mem_placesOutside K (curveE E) (XE E) Q).2 hQ
  have hle : Divisor.L (2 • Finsupp.single Q 1 : Divisor K (curveE E).functionField) ≤
      Divisor.L 0 := by
    intro f hf
    rcases Divisor.mem_L.1 hf with rfl | hf'
    · exact zero_mem _
    have hreg : ∀ P : Place K (curveE E).functionField, P ≠ Q → f ∈ P.1 := by
      intro P hPQ
      refine P.mem_of_ord_nonneg ?_
      have := hf' P
      rwa [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hPQ), smul_zero,
        neg_zero] at this
    have hsec : f ∈ regularOutside K (placesOutside K (curveE E) (XE E)) :=
      fun P hP ↦ hreg P fun h ↦ hP (h ▸ hQS)
    obtain ⟨a, ha⟩ := (mem_regularOutside_iff K (curveE E) (XE E)
      (mem_placesOutside K (curveE E) (XE E)) f).1 hsec
    have hfQ : f ∈ Q.1 := mem_of_isIntegral_adjoin₂ hxQ ((mem_range_germ_XE_iff E f).1 ⟨a, ha⟩)
    refine Divisor.mem_L.2 (Or.inr fun P ↦ ?_)
    rw [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
    by_cases hPQ : P = Q
    · rw [hPQ]
      exact Q.ord_nonneg_of_mem hfQ
    · exact P.ord_nonneg_of_mem (hreg P hPQ)
  have h1 : Divisor.ell (2 • Finsupp.single Q 1 : Divisor K (curveE E).functionField) ≤
      Divisor.ell (0 : Divisor K (curveE E).functionField) := Submodule.finrank_mono hle
  rw [ell_zero_eq_one K (curveE E)] at h1
  have hg : genus K (curveE E).functionField = 1 := curveGenus_curveE₂ E
  have hdeg : (2 • Finsupp.single Q 1 : Divisor K (curveE E).functionField).deg = 2 * Q.deg := by
    rw [Divisor.deg_nsmul, Divisor.deg_single]
    push_cast
    ring
  have hQd := Q.deg_pos
  have h2 := ell_eq_of_deg_gt (A := (2 • Finsupp.single Q 1 : Divisor K (curveE E).functionField))
    (by rw [hdeg, hg]; omega)
  rw [hdeg, hg] at h2
  omega

/-- **`E ∖ {O}` has exactly one cusp, of degree one**: `Σ_{c ∉ X} [κ(c) : K] = 1`. -/
theorem cuspDegree_XE₂ : Anabelian.cuspDegree K (curveE E) (XE E) = 1 := by
  haveI := nonempty_XE₂ E
  obtain ⟨P, hxP, hdeg, huniq⟩ := exists_unique_pole_of_weq₂ E (wEq_curveE E)
    (transcendental_xN E) (finrank_adjoin_xN₂ E)
  have hset : ((XE E : Set (curveE E))ᶜ) = {pointOfPlace K (curveE E) P} := by
    ext c
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · intro hc
      have hcg : c ≠ genericPoint (curveE E) := fun h ↦ hc (h ▸ genericPoint_mem_of_nonempty _)
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = curvePlaceEquiv K (curveE E) ⟨c, hcg⟩ := ⟨_, rfl⟩
      have hQc : pointOfPlace K (curveE E) Q = c := by
        rw [hQ, pointOfPlace, Equiv.symm_apply_apply]
      rw [← hQc, huniq Q (xN_not_mem_of_not_mem_XE₂ E Q (hQc ▸ hc))]
    · rintro rfl hP
      exact hxP (xN_mem_of_mem_XE₂ E P hP)
  unfold Anabelian.cuspDegree
  rw [hset, finsum_mem_singleton]
  have h := pointDegree_eq_finrank K (curveE E) ((curvePlaceEquiv K (curveE E)).symm P)
  rw [pointDegree, Equiv.apply_symm_apply, hdeg] at h
  exact h.symm

/-- **`X_Ω = (E ∖ {O})_Ω` has exactly one cusp** for every algebraically closed `Ω ⊇ K`
(hypothesis `hr` of `CurvesJacobian.Cusp.dupPiU_inf_Delta`). -/
theorem card_compl_baseChangeOpen_XE (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    Nat.card ((baseChangeOpen K Ω (XE E) : Set (baseChange K Ω (curveE E)))ᶜ : Set _) = 1 := by
  rw [card_compl_eq_cuspDegree_of_isCurveOver K Ω (XE E) ((VE_nonempty E).mono (VE_le_XE E)),
    cuspDegree_XE₂ E]

end Curve

end CurvesJacobian.Cusp
