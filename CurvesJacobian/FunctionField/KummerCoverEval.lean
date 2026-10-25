/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.BigOperators.Intervals
import CurvesJacobian.FunctionField.KummerCover
import CurvesJacobian.FunctionField.WeilReciprocity

/-!
# Values of functions on a cyclic Kummer cover and Weil reciprocity

Setting of `CurvesJacobian/FunctionField/KummerCover.lean`: `L = K(α)`, `αⁿ = f`, `div f = n D`,
`σ α = ζ α`. This file proves:

* `val_algebraMap_restrict`: `x(Q) = x(Q|_K)` for `x ∈ K`; `val_placeMap'`, `evalDiv_divMap`
  (`φ(g_* C) = (g⁻¹ φ)(C)`);
* `prod_val_placeMap`: `∏_g φ(g Q) = (N φ)(Q|_K)`, and **`evalDiv_conormOf`**:
  `φ(Con B) = (N φ)(B)` if `φ` has no zeros or poles above the support of `B`;
* `norm_eq_prod` (`N γ = ∏_{j < n} σ^j γ`), `div_alpha` (`div α = Con D`), `ord_alpha`;
* `sigma_eq_of_apply` (`g α = ζ α → g = σ`), the change of data `(f hⁿ, D + div h, α h)`
  (`shift_hf0`, `shift_hfD`, `shift_hord`, `shift_hα`, `shift_hgen`, `sigma_shift`);
* `div_normF`: the divisor of `F = ∏_{i < n} ∏_{j < i} σ^j γ`;
* **`evalDiv_div_evalDiv`**: if `N γ = f_b`, `div f_b = n D_b`,
  `div γ = C - σ_* C + Con D_b` and the supports are disjoint, then
  `f(D_b) / f_b(D) = ζ^{-deg C}` (Weil reciprocity on `L` for `α` and `γ`).
-/

open WeilCurves.FunctionField Module

set_option linter.unusedSectionVars false

namespace CurvesJacobian.KummerCover

variable {κ K L : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Field L]
  [Algebra κ K] [Algebra κ L] [Algebra K L] [IsScalarTower κ K L] [IsFunctionField κ K]
  [IsFunctionField κ L] [FiniteDimensional K L]
  {n : ℕ} [NeZero n] {ζ : κ} (hζ : IsPrimitiveRoot ζ n)
  {f : K} (hf0 : f ≠ 0) {D : Divisor κ K} (hfD : Divisor.div κ f = n • D)
  (hord : ∀ d : ℕ, 0 < d → d < n → d ∣ n → ∀ h : K, h ≠ 0 → Divisor.div κ h ≠ d • D)
  {α : L} (hα : α ^ n = algebraMap K L f) (hgen : IntermediateField.adjoin K {α} = ⊤)

set_option hygiene false in
/-- The generator `σ` of `Gal(L/K)`, `σ α = ζ α`. -/
local notation "𝔰" => sigma hζ hf0 hfD hord hα hgen

/-! ### Values at places -/

/-- Values are compatible with restriction: `x(Q) = x(Q|_K)` for `x ∈ K`. -/
theorem val_algebraMap_restrict (Q : Place κ L) (x : K) :
    Place.val Q (algebraMap K L x) = Place.val (Q.restrict (K := K)) x := by
  by_cases hx : x ∈ (Q.restrict (K := K)).1
  · have hxQ : algebraMap K L x ∈ Q.1 := Place.mem_restrict.mp hx
    rw [Place.val_eq_iff Q hxQ]
    have h := (Place.val_eq_iff _ hx (Place.val (Q.restrict (K := K)) x)).mp rfl
    rw [IsScalarTower.algebraMap_apply κ K L, ← map_sub,
      map_eq_zero_iff _ (algebraMap K L).injective, ord_algebraMap_eq_ramIndex_mul]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (mul_pos (ramIndex_pos _) h)
  · rw [Place.val_of_notMem _ hx,
      Place.val_of_notMem _ fun h ↦ hx (Place.mem_restrict.mpr h)]

lemma val_prod (Q : Place κ L) {ι : Type*} (s : Finset ι) (x : ι → L)
    (hx : ∀ i ∈ s, x i ∈ Q.1) : Place.val Q (∏ i ∈ s, x i) = ∏ i ∈ s, Place.val Q (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.val_one]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, x i ∈ Q.1 := fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Place.val_mul Q (hx a (Finset.mem_insert_self a s)) (prod_mem hs), ih hs]

/-- `x(g Q) = (g⁻¹ x)(Q)`. -/
lemma val_placeMap' (g : L ≃ₐ[K] L) (Q : Place κ L) (x : L) :
    Place.val (placeMap g Q) x = Place.val Q (g.symm x) := by
  have := val_placeMap g Q (g.symm x)
  rwa [AlgEquiv.apply_symm_apply] at this

/-- `φ(g_* C) = (g⁻¹ φ)(C)`. -/
theorem evalDiv_divMap (g : L ≃ₐ[K] L) (x : L) (C : Divisor κ L) :
    evalDiv x (divMap g C) = evalDiv (g.symm x) C := by
  rw [evalDiv, evalDiv]
  change (Finsupp.equivMapDomain (placeEquiv g) C).prod _ = _
  rw [Finsupp.prod_equivMapDomain]
  simp only [placeEquiv, Equiv.coe_fn_mk, val_placeMap']

lemma algEquiv_algebraMap (g : L ≃ₐ[K] L) (c : κ) : g (algebraMap κ L c) = algebraMap κ L c := by
  rw [IsScalarTower.algebraMap_apply κ K L, AlgEquiv.commutes]

include hζ hf0 hfD hord hα hgen in
/-- **`N γ = ∏_{j < n} σ^j γ`**. -/
theorem norm_eq_prod (γ : L) :
    algebraMap K L (Algebra.norm K γ) = ∏ j ∈ Finset.range n, (𝔰 ^ j) γ := by
  haveI := isGalois hζ hf0 hfD hord hα hgen
  rw [Algebra.norm_eq_prod_automorphisms]
  exact (prod_range_sigma_pow hζ hf0 hfD hord hα hgen fun g ↦ g γ).symm

include hζ hf0 hfD hord hα hgen in
/-- `∏_g φ(g Q) = (N φ)(Q|_K)` if `φ` is a unit at all `g Q`. -/
theorem prod_val_placeMap {φ : L} (Q : Place κ L)
    (h : ∀ g : L ≃ₐ[K] L, (placeMap g Q).ord φ = 0) :
    ∏ g : L ≃ₐ[K] L, Place.val (placeMap g Q) φ =
      Place.val (Q.restrict (K := K)) (Algebra.norm K φ) := by
  haveI := isGalois hζ hf0 hfD hord hα hgen
  simp only [val_placeMap']
  rw [← val_algebraMap_restrict, Algebra.norm_eq_prod_automorphisms, val_prod]
  · exact Fintype.prod_equiv (Equiv.inv _) _ _ fun g ↦ rfl
  · intro g _
    apply Place.mem_of_ord_eq_zero
    have := ord_placeMap g (placeMap g⁻¹ Q) φ
    rw [placeMap_placeMap_inv] at this
    rw [this]
    exact h g⁻¹

include hζ hf0 hfD hord hα hgen in
/-- **`φ(Con B) = (N φ)(B)`** if `φ` has neither zeros nor poles above the support of `B`. -/
theorem evalDiv_conormOf {φ : L} (B : Divisor κ K)
    (h : ∀ Q : Place κ L, B (Q.restrict (K := K)) ≠ 0 → Q.ord φ = 0) :
    evalDiv φ (conormOf L B) = evalDiv (Algebra.norm K φ) B := by
  classical
  choose s hs using fun P : Place κ K ↦ exists_restrict_eq (L := L) P
  set fib : Place κ K → Finset (Place κ L) := fun P ↦
    Finset.univ.image fun g : L ≃ₐ[K] L ↦ placeMap g (s P)
  have hfib : ∀ P Q, Q ∈ fib P ↔ Q.restrict (K := K) = P := by
    intro P Q
    simp only [fib, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨g, rfl⟩
      rw [restrict_placeMap, hs]
    · intro hQ
      obtain ⟨g, hg⟩ := exists_eq_placeMap' hζ hf0 hfD hord hα hgen (Q := s P) (Q' := Q)
        (by rw [hQ, hs])
      exact ⟨g, hg.symm⟩
  have hsupp : (conormOf L B).support ⊆ B.support.biUnion fib := by
    intro Q hQ
    rw [Finsupp.mem_support_iff, conormOf_apply] at hQ
    rw [Finset.mem_biUnion]
    exact ⟨Q.restrict (K := K), Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hQ),
      (hfib _ Q).mpr rfl⟩
  rw [evalDiv, evalDiv, Finsupp.prod_of_support_subset _ hsupp _ fun _ _ ↦ zpow_zero _,
    Finset.prod_biUnion, Finsupp.prod]
  · refine Finset.prod_congr rfl fun P hP ↦ ?_
    rw [Finset.prod_image fun g _ g' _ hgg' ↦
      placeMap_injective hζ hf0 hfD hord hα hgen (s P) hgg']
    simp only [conormOf_apply, ramIndex_eq_one hζ hf0 hfD hord hα hgen, restrict_placeMap, hs,
      one_mul]
    rw [Finset.prod_zpow, prod_val_placeMap hζ hf0 hfD hord hα hgen, hs]
    intro g
    exact h _ (by rw [restrict_placeMap, hs]; exact Finsupp.mem_support_iff.mp hP)
  · intro P _ P' _ hPP'
    rw [Function.onFun, Finset.disjoint_left]
    intro Q hQ hQ'
    exact hPP' (((hfib P Q).mp hQ).symm.trans ((hfib P' Q).mp hQ'))

/-! ### The divisor of `α` and the generator `σ` -/

include hfD hα in
/-- **`div α = Con D`**. -/
theorem div_alpha : Divisor.div κ α = conormOf L D := by
  refine nsmul_cancel (NeZero.ne n) ?_
  rw [← Divisor.div_pow, hα, div_algebraMap, hfD]
  ext Q
  simp only [conormOf_apply, Finsupp.smul_apply, nsmul_eq_mul]
  ring

include hζ hf0 hfD hord hα hgen in
/-- `ord_Q α = D(Q|_K)`. -/
theorem ord_alpha (Q : Place κ L) : Q.ord α = D (Q.restrict (K := K)) := by
  have := DFunLike.congr_fun (div_alpha hfD hα) Q
  rwa [Divisor.div_apply, conormOf_apply, ramIndex_eq_one hζ hf0 hfD hord hα hgen, one_mul]
    at this

/-- `σ⁻¹ α = ζ⁻¹ α`. -/
theorem sigma_symm_apply : (𝔰).symm α = algebraMap κ L ζ⁻¹ * α := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  rw [AlgEquiv.symm_apply_eq, map_mul, algEquiv_algebraMap, sigma_apply, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hζ0, map_one, one_mul]

/-- **`σ` is the only automorphism with `σ α = ζ α`**. -/
theorem sigma_eq_of_apply {g : L ≃ₐ[K] L} (hg : g α = algebraMap κ L ζ * α) : g = 𝔰 := by
  have hα0 := ne_zero hf0 hα
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have h1 : (g * (𝔰)⁻¹) α = α := by
    rw [AlgEquiv.mul_apply]
    change g ((𝔰).symm α) = α
    rw [sigma_symm_apply, map_mul, algEquiv_algebraMap, hg, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hζ0, map_one, one_mul]
  obtain ⟨k, -, hk⟩ := exists_eq_sigma_pow hζ hf0 hfD hord hα hgen (g * (𝔰)⁻¹)
  rw [hk, sigma_pow_apply] at h1
  have h2 : ζ ^ k = 1 := by
    have h3 : (algebraMap κ L (ζ ^ k) - 1) * α = 0 := by
      rw [map_pow, sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · rw [sub_eq_zero, ← map_one (algebraMap κ L)] at h
      exact (algebraMap κ L).injective h
    · exact absurd h hα0
  rw [(sigma_pow_eq_one_iff hζ hf0 hfD hord hα hgen).mpr ((hζ.pow_eq_one_iff_dvd k).mp h2)] at hk
  exact mul_inv_eq_one.mp hk

/-! ### Changing the Kummer generator by an `n`-th power -/

include hf0 in
theorem shift_hf0 {h : K} (hh : h ≠ 0) : f * h ^ n ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ hh)

include hf0 hfD in
theorem shift_hfD {h : K} (hh : h ≠ 0) :
    Divisor.div κ (f * h ^ n) = n • (D + Divisor.div κ h) := by
  rw [Divisor.div_mul hf0 (pow_ne_zero _ hh), Divisor.div_pow, hfD, smul_add]

include hord in
theorem shift_hord {h : K} (hh : h ≠ 0) :
    ∀ d : ℕ, 0 < d → d < n → d ∣ n → ∀ h' : K, h' ≠ 0 →
      Divisor.div κ h' ≠ d • (D + Divisor.div κ h) := by
  intro d hd hdn hdvd h' hh' heq
  refine hord d hd hdn hdvd (h' / h ^ d) (div_ne_zero hh' (pow_ne_zero _ hh)) ?_
  rw [Divisor.div_div hh' (pow_ne_zero _ hh), heq, Divisor.div_pow, smul_add, add_sub_cancel_right]

include hα in
theorem shift_hα (h : K) : (α * algebraMap K L h) ^ n = algebraMap K L (f * h ^ n) := by
  rw [mul_pow, hα, map_mul, map_pow]

include hgen in
theorem shift_hgen {h : K} (hh : h ≠ 0) :
    IntermediateField.adjoin K {α * algebraMap K L h} = ⊤ := by
  rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
  have e : α * algebraMap K L h * algebraMap K L h⁻¹ = α := by
    rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hh, map_one, mul_one]
  have hmem : α * algebraMap K L h * algebraMap K L h⁻¹ ∈
      IntermediateField.adjoin K {α * algebraMap K L h} :=
    mul_mem (IntermediateField.mem_adjoin_simple_self K _)
      (IntermediateField.algebraMap_mem _ _)
  rwa [e] at hmem

/-- **The generator `σ` does not change** when `(f, D, α)` is replaced by
`(f hⁿ, D + div h, α h)`. -/
theorem sigma_shift {h : K} (hh : h ≠ 0) :
    sigma hζ (shift_hf0 hf0 hh) (shift_hfD hf0 hfD hh) (shift_hord hord hh) (shift_hα hα h)
      (shift_hgen hgen hh) = 𝔰 := by
  symm
  apply sigma_eq_of_apply
  rw [map_mul, AlgEquiv.commutes, sigma_apply, mul_assoc]

/-! ### The divisor of the norm representative -/

include hζ hf0 hfD hord hα hgen in
/-- With `ρ_i = ∏_{j < i} σ^j γ`: `div ∏_{i < n} ρ_i = n C + Con(-π_* C + (n(n-1)/2) D_b)`. -/
theorem div_normF {γ : L} (hγ0 : γ ≠ 0) {C : Divisor κ L} {Db : Divisor κ K}
    (hC : Divisor.div κ γ = C - divMap 𝔰 C + conormOf L Db) :
    Divisor.div κ (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, (𝔰 ^ j) γ) =
      n • C + conormOf L (-(normDiv K C) + (n * (n - 1) / 2 : ℕ) • Db) := by
  have hj : ∀ j : ℕ, Divisor.div κ ((𝔰 ^ j) γ) =
      divMap (𝔰 ^ j) C - divMap (𝔰 ^ (j + 1)) C + conormOf L Db := by
    intro j
    rw [← divMap_div, hC, map_add, map_sub, divMap_conormOf, ← divMap_mul, ← pow_succ]
  have hρ : ∀ i : ℕ, Divisor.div κ (∏ j ∈ Finset.range i, (𝔰 ^ j) γ) =
      C - divMap (𝔰 ^ i) C + i • conormOf L Db := by
    intro i
    rw [div_prod _ _ fun j _ ↦ (_root_.map_ne_zero _).2 hγ0]
    induction i with
    | zero => simp [divMap_one]
    | succ i ih =>
      rw [Finset.sum_range_succ, ih, hj, succ_nsmul]
      abel
  rw [div_prod _ _ fun i _ ↦ Finset.prod_ne_zero_iff.mpr fun j _ ↦ (_root_.map_ne_zero _).2 hγ0]
  simp only [hρ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    sum_divMap_sigma_pow hζ hf0 hfD hord hα hgen, ← Finset.sum_smul, Finset.sum_range_id]
  have e : conormOf L (-(normDiv K C) + (n * (n - 1) / 2 : ℕ) • Db) =
      -conormOf L (normDiv K C) + (n * (n - 1) / 2 : ℕ) • conormOf L Db := by
    ext Q
    simp only [conormOf_apply, Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply,
      nsmul_eq_mul]
    ring
  rw [e]
  abel

/-! ### Weil reciprocity on the cover -/

variable {fb : K} (hfb0 : fb ≠ 0) {Db : Divisor κ K} (hfbD : Divisor.div κ fb = n • Db)
  {γ : L} (hγN : Algebra.norm K γ = fb) {C : Divisor κ L}
  (hC : Divisor.div κ γ = C - divMap 𝔰 C + conormOf L Db)
  (hDisj : ∀ P, D P = 0 ∨ Db P = 0) (hDC : ∀ Q ∈ C.support, D (Q.restrict (K := K)) = 0)

include hfb0 hfbD hγN hC hDisj hDC in
/-- **`f(D_b) / f_b(D) = ζ^{-deg C}`** (S5): Weil reciprocity `α(div γ) = γ(div α)` on `L`, with
`α(C - σ_* C) = ζ^{deg C}`, `α(Con D_b) = (N α)(D_b) = f(D_b)` and
`γ(Con D) = (N γ)(D) = f_b(D)`. -/
theorem evalDiv_div_evalDiv : evalDiv f Db / evalDiv fb D = ζ ^ (-C.deg) := by
  have hα0 := ne_zero hf0 hα
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have hγ0 : γ ≠ 0 := Algebra.norm_ne_zero_iff.mp (hγN ▸ hfb0)
  have hordα := ord_alpha hζ hf0 hfD hord hα hgen
  have hC0 : ∀ Q : Place κ L, D (Q.restrict (K := K)) ≠ 0 → C Q = 0 := fun Q hQ ↦ by
    by_contra h
    exact hQ (hDC Q (Finsupp.mem_support_iff.mpr h))
  have hγD : ∀ Q : Place κ L, D (Q.restrict (K := K)) ≠ 0 → Q.ord γ = 0 := by
    intro Q hQ
    have := DFunLike.congr_fun hC Q
    rw [Divisor.div_apply] at this
    rw [this, Finsupp.add_apply, Finsupp.sub_apply, divMap_apply, conormOf_apply, hC0 Q hQ,
      hC0 _ (by rwa [restrict_placeMap]), (hDisj _).resolve_left hQ]
    simp
  have hDb : Db.deg = 0 := by
    have := Divisor.deg_div (k := κ) fb
    rw [hfbD, Divisor.deg_nsmul] at this
    exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast NeZero.ne n)
  have hαC : Avoids α C :=
    ⟨hα0, fun Q hQ ↦ by rw [hordα]; exact hDC Q (Finsupp.mem_support_iff.mpr hQ)⟩
  have hασC : Avoids α (divMap 𝔰 C) := ⟨hα0, fun Q hQ ↦ by
    rw [divMap_apply] at hQ
    rw [hordα, ← restrict_placeMap (𝔰)⁻¹ Q]
    exact hDC _ (Finsupp.mem_support_iff.mpr hQ)⟩
  have hαDb : ∀ Q : Place κ L, Db (Q.restrict (K := K)) ≠ 0 → Q.ord α = 0 := fun Q hQ ↦ by
    rw [hordα]
    exact (hDisj _).resolve_right hQ
  have hαCon : Avoids α (conormOf L Db) := ⟨hα0, fun Q hQ ↦ hαDb Q (by
    rw [conormOf_apply] at hQ
    exact right_ne_zero_of_mul hQ)⟩
  have hfDb : Avoids f Db := ⟨hf0, fun P hP ↦ by
    have := DFunLike.congr_fun hfD P
    rw [Divisor.div_apply, Finsupp.smul_apply, (hDisj P).resolve_right hP, smul_zero] at this
    exact this⟩
  -- the norm of `α`
  set c : κ := ∏ j ∈ Finset.range n, ζ ^ j
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ hζ0
  have hNα : Algebra.norm K α = algebraMap κ K c * f := by
    apply (algebraMap K L).injective
    rw [norm_eq_prod hζ hf0 hfD hord hα hgen]
    simp only [sigma_pow_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hα, map_mul,
      ← IsScalarTower.algebraMap_apply, map_prod]
    simp only [map_pow]
  have hWR := weil_reciprocity hα0 hγ0 fun Q ↦ by
    by_cases hQ : D (Q.restrict (K := K)) = 0
    · exact Or.inl (by rw [hordα, hQ])
    · exact Or.inr (hγD Q hQ)
  rw [hC, div_alpha hfD hα, evalDiv_add (hαC.sub hασC) hαCon, evalDiv_sub hαC hασC,
    evalDiv_divMap, sigma_symm_apply, evalDiv_mul (avoids_algebraMap (inv_ne_zero hζ0) C) hαC,
    evalDiv_algebraMap (inv_ne_zero hζ0), evalDiv_conormOf hζ hf0 hfD hord hα hgen Db hαDb,
    evalDiv_conormOf hζ hf0 hfD hord hα hgen D hγD, hγN, hNα,
    evalDiv_mul (avoids_algebraMap hc0 Db) hfDb, evalDiv_algebraMap hc0, hDb, zpow_zero,
    one_mul] at hWR
  have ha := evalDiv_ne_zero hαC
  have hb := evalDiv_ne_zero hfDb
  have hz : ζ ^ C.deg ≠ 0 := zpow_ne_zero _ hζ0
  rw [← hWR, inv_zpow, zpow_neg]
  field_simp

end CurvesJacobian.KummerCover
