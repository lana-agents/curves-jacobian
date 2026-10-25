/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Norm.Transitivity
import WeilCurves.Hurwitz.Belyi
import CurvesJacobian.LocAn.PlaceAut

/-!
# Cyclic Kummer covers of function fields

Let `K / κ` be a function field of one variable over an algebraically closed field `κ`, `n ≥ 1`,
`ζ ∈ κ` a primitive `n`-th root of unity, `f ∈ K×` with `div f = n D`, such that `d D` is not
principal for any proper divisor `d` of `n` (`hord`), and `L = K(α)` with `αⁿ = f` (a finite
extension of `K`; `IsFunctionField κ L` is an instance argument, it follows from
`WeilCurves.FunctionField.IsFunctionField.of_finite`). This file proves that `L / K` is a cyclic
unramified cover of degree `n` and describes its places and divisors:

* `CurvesJacobian.KummerCover.finrank_eq`: `[L : K] = n` (if `d = [L : K] < n`, then
  `g = N(α)` satisfies `gⁿ = f^d`, so `div g = d D`, and Bézout gives `h ∈ K` with
  `div h = gcd(d, n) D`);
* `sigma` (`σ α = ζ α`, `sigma_apply`, `sigma_pow_apply`), `isGalois`, `exists_eq_sigma_pow`,
  `sigma_pow_eq_one_iff`: `Gal(L/K) = ⟨σ⟩ ≅ ℤ/n` (via Mathlib's `autEquivZmod`);
* `placeMap g Q` (`= CurvesJacobian.LocAn.placeMap` of `g` viewed as a `κ`-automorphism, i.e.
  the place with valuation ring `g(𝒪_Q)`), `ord_placeMap`, `val_placeMap`, `restrict_placeMap`,
  `divMap g` (`(g_* C)(Q) = C(g⁻¹ Q)`, so `g_* [Q] = [g Q]`), `divMap_div`, `divMap_conormOf`;
* `placeMap_sigma_pow_eq_iff`: `σ^j Q = Q ↔ n ∣ j` (the residue field of `Q` is `κ`, and `σ^j`
  multiplies the unit `α / π^{D(P)}` by `ζ^j`);
* **`ramIndex_eq_one`** (`L / K` is unramified) and `exists_eq_placeMap` (the places above
  `Q|_K` are the `σ^j Q`, `j < n`), from `∑_{Q'|P} e(Q'|P) = n`;
* `div_algebraMap` (`div x = Con (div x)` for `x ∈ K`), `normDiv` (`π_*`), `deg_normDiv`,
  `normDiv_conormOf` (`π_* Con B = n B`), `sum_divMap_sigma_pow` (`∑_j σ^j_* C = Con π_* C`);
* **`exists_div_eq`**: if `div N_{L/K}(γ) = n B`, then `div γ = C - σ_* C + Con B` for some
  divisor `C` of `L`.
-/

open Polynomial WeilCurves.FunctionField Module

set_option linter.unusedSectionVars false

namespace CurvesJacobian.KummerCover

variable {κ K L : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Field L]
  [Algebra κ K] [Algebra κ L] [Algebra K L] [IsScalarTower κ K L] [IsFunctionField κ K]
  [IsFunctionField κ L] [FiniteDimensional K L]
  {n : ℕ} [NeZero n] {ζ : κ} (hζ : IsPrimitiveRoot ζ n)
  {f : K} (hf0 : f ≠ 0) {D : Divisor κ K} (hfD : Divisor.div κ f = n • D)
  (hord : ∀ d : ℕ, 0 < d → d < n → d ∣ n → ∀ h : K, h ≠ 0 → Divisor.div κ h ≠ d • D)
  {α : L} (hα : α ^ n = algebraMap K L f) (hgen : IntermediateField.adjoin K {α} = ⊤)

omit [IsAlgClosed κ] [IsFunctionField κ K] [IsFunctionField κ L] [FiniteDimensional K L] in
/-- Divisors are torsion-free. -/
lemma nsmul_cancel {m : ℕ} (hm : m ≠ 0) {X Y : Divisor κ K} (h : m • X = m • Y) : X = Y := by
  ext P
  have := DFunLike.congr_fun h P
  simp only [Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hm) this

omit [FiniteDimensional K L] in
include hα hf0 in
lemma ne_zero : α ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n), eq_comm, map_eq_zero_iff _ (algebraMap K L).injective] at hα
  exact hf0 hα

omit [Algebra κ L] [IsScalarTower κ K L] [IsFunctionField κ L] in
include hf0 hfD hord hα hgen in
/-- **`[L : K] = n`**. -/
theorem finrank_eq : finrank K L = n := by
  have hint : IsIntegral K α := IsIntegral.of_finite K α
  have hα0 := ne_zero hf0 hα
  have hle : finrank K L ≤ n := by
    have h1 : finrank K (IntermediateField.adjoin K {α}) = (minpoly K α).natDegree :=
      IntermediateField.adjoin.finrank hint
    rw [hgen, IntermediateField.finrank_top'] at h1
    rw [h1]
    have hne : (X ^ n - C f : K[X]) ≠ 0 := X_pow_sub_C_ne_zero (NeZero.pos n) f
    have := natDegree_le_of_dvd (minpoly.dvd K α (by simp [hα])) hne
    rwa [natDegree_X_pow_sub_C] at this
  set d := finrank K L with hd
  have hdpos : 0 < d := finrank_pos
  set g := Algebra.norm K α
  have hg0 : g ≠ 0 := Algebra.norm_ne_zero_iff.mpr hα0
  have hg : g ^ n = f ^ d := by
    rw [← map_pow, hα, Algebra.norm_algebraMap]
  have hdivg : Divisor.div κ g = d • D := by
    refine nsmul_cancel (NeZero.ne n) ?_
    rw [← Divisor.div_pow, hg, Divisor.div_pow, hfD, smul_comm]
  by_contra hne
  have hlt : d < n := lt_of_le_of_ne hle hne
  set m := Nat.gcd d n
  have hm := Nat.gcd_eq_gcd_ab d n
  have hmpos : 0 < m := Nat.gcd_pos_of_pos_left n hdpos
  have hmd : m ≤ d := Nat.le_of_dvd hdpos (Nat.gcd_dvd_left d n)
  set h := g ^ (Nat.gcdA d n) * f ^ (Nat.gcdB d n)
  have hh0 : h ≠ 0 := mul_ne_zero (zpow_ne_zero _ hg0) (zpow_ne_zero _ hf0)
  refine hord m hmpos (by omega) (Nat.gcd_dvd_right d n) h hh0 ?_
  ext P
  have h1 := DFunLike.congr_fun hdivg P
  have h2 := DFunLike.congr_fun hfD P
  simp only [Divisor.div_apply, Finsupp.smul_apply, nsmul_eq_mul] at h1 h2 ⊢
  rw [P.ord_mul (zpow_ne_zero _ hg0) (zpow_ne_zero _ hf0), Place.ord_zpow, Place.ord_zpow,
    h1, h2, hm]
  ring


/-! ### The Galois group -/

omit [Algebra κ L] [IsScalarTower κ K L] [IsFunctionField κ L] in
include hf0 hfD hord hα hgen in
lemma irreducible_X_pow_sub_C : Irreducible (X ^ n - C f) := by
  have hfr := finrank_eq hf0 hfD hord hα hgen
  have := irreducible_X_pow_sub_C_of_root_adjoin_eq_top (a := f) (α := α)
    (by rw [hfr]; exact hα) hgen
  rwa [hfr] at this

omit [Algebra κ L] [IsScalarTower κ K L] [IsFunctionField κ L] in
include hζ hf0 hfD hord hα hgen in
lemma isSplittingField : IsSplittingField K L (X ^ n - C f) := by
  have hfr := finrank_eq hf0 hfD hord hα hgen
  have hK : (primitiveRoots (finrank K L) K).Nonempty :=
    ⟨algebraMap κ K ζ, (mem_primitiveRoots finrank_pos).mpr
      (by rw [hfr]; exact hζ.map_of_injective (algebraMap κ K).injective)⟩
  have := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK (a := f)
    (by rw [hfr]; exact hα) hgen
  rwa [hfr] at this

/-- `Gal(L/K) ≃ ℤ/n` (Mathlib's `autEquivZmod`, for the primitive root `ζ`). -/
noncomputable def autEquiv : (L ≃ₐ[K] L) ≃* Multiplicative (ZMod n) :=
  haveI := isSplittingField hζ hf0 hfD hord hα hgen
  autEquivZmod (irreducible_X_pow_sub_C hf0 hfD hord hα hgen) L
    (hζ.map_of_injective (algebraMap κ K).injective)

lemma autEquiv_symm_apply (j : ℕ) :
    (autEquiv hζ hf0 hfD hord hα hgen).symm (Multiplicative.ofAdd (j : ZMod n)) α =
      algebraMap κ L ζ ^ j * α := by
  haveI := isSplittingField hζ hf0 hfD hord hα hgen
  rw [autEquiv, autEquivZmod_symm_apply_natCast _ L hα, Algebra.smul_def, map_pow,
    ← IsScalarTower.algebraMap_apply]

/-- The generator `σ` of `Gal(L/K)` with `σ α = ζ α`. -/
noncomputable def sigma : L ≃ₐ[K] L :=
  (autEquiv hζ hf0 hfD hord hα hgen).symm (Multiplicative.ofAdd 1)

lemma sigma_pow_eq (j : ℕ) : sigma hζ hf0 hfD hord hα hgen ^ j =
    (autEquiv hζ hf0 hfD hord hα hgen).symm (Multiplicative.ofAdd (j : ZMod n)) := by
  rw [sigma, ← map_pow, ← ofAdd_nsmul, nsmul_one]

/-- `σ^j α = ζ^j α`. -/
lemma sigma_pow_apply (j : ℕ) :
    (sigma hζ hf0 hfD hord hα hgen ^ j) α = algebraMap κ L ζ ^ j * α := by
  rw [sigma_pow_eq, autEquiv_symm_apply]

/-- `σ α = ζ α`. -/
lemma sigma_apply : sigma hζ hf0 hfD hord hα hgen α = algebraMap κ L ζ * α := by
  simpa using sigma_pow_apply hζ hf0 hfD hord hα hgen 1

include hζ hf0 hfD hord hα hgen in
/-- `L / K` is Galois. -/
theorem isGalois : IsGalois K L := by
  haveI := isSplittingField hζ hf0 hfD hord hα hgen
  exact isGalois_of_isSplittingField_X_pow_sub_C
    ⟨_, (mem_primitiveRoots (NeZero.pos n)).mpr (hζ.map_of_injective (algebraMap κ K).injective)⟩
    (irreducible_X_pow_sub_C hf0 hfD hord hα hgen) L

/-- Every `g ∈ Gal(L/K)` is a power `σ^j`, `j < n`. -/
theorem exists_eq_sigma_pow (g : L ≃ₐ[K] L) : ∃ j < n, g = sigma hζ hf0 hfD hord hα hgen ^ j := by
  refine ⟨(Multiplicative.toAdd (autEquiv hζ hf0 hfD hord hα hgen g)).val, ZMod.val_lt _, ?_⟩
  rw [sigma_pow_eq, ZMod.natCast_zmod_val, ofAdd_toAdd, MulEquiv.symm_apply_apply]

/-- `σ` has order `n`. -/
theorem sigma_pow_eq_one_iff {j : ℕ} : sigma hζ hf0 hfD hord hα hgen ^ j = 1 ↔ n ∣ j := by
  rw [sigma_pow_eq, MulEquiv.map_eq_one_iff, ofAdd_eq_one, ZMod.natCast_eq_zero_iff]


set_option hygiene false in
/-- The generator `σ` of `Gal(L/K)`, `σ α = ζ α`. -/
local notation "𝔰" => sigma hζ hf0 hfD hord hα hgen

lemma injOn_sigma_pow : Set.InjOn (fun j : ℕ ↦ 𝔰 ^ j) (Finset.range n) := by
  have key : ∀ i j : ℕ, i ≤ j → j < n → 𝔰 ^ i = 𝔰 ^ j → i = j := by
    intro i j hij hj h
    have h1 : 𝔰 ^ (j - i) = 1 := by
      rw [← Nat.sub_add_cancel hij, pow_add] at h
      exact (mul_eq_right.mp h.symm)
    rw [sigma_pow_eq_one_iff] at h1
    have := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    omega
  intro i hi j hj h
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases le_total i j with hij | hij
  · exact key i j hij hj h
  · exact (key j i hij hi h.symm).symm

lemma image_sigma_pow [DecidableEq (L ≃ₐ[K] L)] :
    (Finset.range n).image (fun j : ℕ ↦ 𝔰 ^ j) = Finset.univ := by
  ext g
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
  obtain ⟨j, hj, rfl⟩ := exists_eq_sigma_pow hζ hf0 hfD hord hα hgen g
  exact ⟨j, hj, rfl⟩

lemma sum_range_sigma_pow {M : Type*} [AddCommMonoid M] (F : (L ≃ₐ[K] L) → M) :
    ∑ j ∈ Finset.range n, F (𝔰 ^ j) = ∑ g, F g := by
  classical
  rw [← image_sigma_pow hζ hf0 hfD hord hα hgen,
    Finset.sum_image (injOn_sigma_pow hζ hf0 hfD hord hα hgen)]

lemma prod_range_sigma_pow {M : Type*} [CommMonoid M] (F : (L ≃ₐ[K] L) → M) :
    ∏ j ∈ Finset.range n, F (𝔰 ^ j) = ∏ g, F g := by
  classical
  rw [← image_sigma_pow hζ hf0 hfD hord hα hgen,
    Finset.prod_image (injOn_sigma_pow hζ hf0 hfD hord hα hgen)]

include hζ hf0 hfD hord hα hgen in
lemma card_aut : Fintype.card (L ≃ₐ[K] L) = n := by
  haveI := isGalois hζ hf0 hfD hord hα hgen
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, finrank_eq hf0 hfD hord hα hgen]

/-! ### The action on places and divisors -/

/-- The place `g(Q)` (valuation ring `g(𝒪_Q)`) for `g ∈ Aut(L/K)`: this is
`CurvesJacobian.LocAn.placeMap` (`LocAn/PlaceAut.lean`) of `g` as a `κ`-automorphism. -/
def placeMap (g : L ≃ₐ[K] L) (Q : Place κ L) : Place κ L :=
  LocAn.placeMap (g.restrictScalars κ) Q

omit [IsAlgClosed κ] [IsFunctionField κ K] [IsFunctionField κ L] [FiniteDimensional K L]
  [NeZero n] in
lemma mem_placeMap {g : L ≃ₐ[K] L} {Q : Place κ L} {x : L} :
    x ∈ (placeMap g Q).1 ↔ g.symm x ∈ Q.1 :=
  LocAn.mem_placeMap

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma placeMap_mul (g h : L ≃ₐ[K] L) (Q : Place κ L) :
    placeMap (g * h) Q = placeMap g (placeMap h Q) := by
  ext x
  simp only [mem_placeMap]
  rfl

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma placeMap_one (Q : Place κ L) : placeMap (1 : L ≃ₐ[K] L) Q = Q := by
  ext x
  simp only [mem_placeMap]
  rfl

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma placeMap_inv_placeMap (g : L ≃ₐ[K] L) (Q : Place κ L) :
    placeMap g⁻¹ (placeMap g Q) = Q := by
  rw [← placeMap_mul, inv_mul_cancel, placeMap_one]

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma placeMap_placeMap_inv (g : L ≃ₐ[K] L) (Q : Place κ L) :
    placeMap g (placeMap g⁻¹ Q) = Q := by
  rw [← placeMap_mul, mul_inv_cancel, placeMap_one]

/-- `placeMap g` as a permutation of the places of `L`. -/
def placeEquiv (g : L ≃ₐ[K] L) : Place κ L ≃ Place κ L where
  toFun := placeMap g
  invFun := placeMap g⁻¹
  left_inv := placeMap_inv_placeMap g
  right_inv := placeMap_placeMap_inv g

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
/-- **`ord_{gQ}(g x) = ord_Q x`**. -/
theorem ord_placeMap (g : L ≃ₐ[K] L) (Q : Place κ L) (x : L) :
    (placeMap g Q).ord (g x) = Q.ord x :=
  ord_placeTr (g.restrictScalars κ).toRingEquiv (RingEquiv.refl κ)
    (fun c ↦ (g.restrictScalars κ).commutes c) Q x

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
/-- `(g x)(gQ) = x(Q)`. -/
theorem val_placeMap (g : L ≃ₐ[K] L) (Q : Place κ L) (x : L) :
    Place.val (placeMap g Q) (g x) = Place.val Q x :=
  val_placeTr (g.restrictScalars κ).toRingEquiv (RingEquiv.refl κ)
    (fun c ↦ (g.restrictScalars κ).commutes c) Q x

omit [IsFunctionField κ K] [NeZero n] in
/-- `g Q` lies over the same place of `K` as `Q`. -/
theorem restrict_placeMap (g : L ≃ₐ[K] L) (Q : Place κ L) :
    (placeMap g Q).restrict (K := K) = Q.restrict := by
  ext x
  rw [Place.mem_restrict, Place.mem_restrict, mem_placeMap, AlgEquiv.commutes]

omit [NeZero n] in
theorem ramIndex_placeMap (g : L ≃ₐ[K] L) (Q : Place κ L) :
    ramIndex K (placeMap g Q) = ramIndex K Q := by
  have := ord_placeMap g Q (algebraMap K L (unifier (Q.restrict (K := K))))
  rw [AlgEquiv.commutes] at this
  simp only [ramIndex, restrict_placeMap]
  exact this

/-- The action on divisors: `(g_* C)(Q) = C(g⁻¹ Q)`, so `g_* [Q] = [g Q]` (`divMap_single`). -/
noncomputable def divMap (g : L ≃ₐ[K] L) : Divisor κ L →+ Divisor κ L :=
  (Finsupp.domCongr (placeEquiv g)).toAddMonoidHom

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma divMap_apply (g : L ≃ₐ[K] L) (C : Divisor κ L) (Q : Place κ L) :
    divMap g C Q = C (placeMap g⁻¹ Q) := rfl

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma divMap_single (g : L ≃ₐ[K] L) (Q : Place κ L) (m : ℤ) :
    divMap g (Finsupp.single Q m) = Finsupp.single (placeMap g Q) m := by
  simp only [divMap, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single]
  rfl

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma divMap_mul (g h : L ≃ₐ[K] L) (C : Divisor κ L) :
    divMap (g * h) C = divMap g (divMap h C) := by
  ext Q
  simp only [divMap_apply, mul_inv_rev, placeMap_mul]

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma divMap_one (C : Divisor κ L) : divMap (1 : L ≃ₐ[K] L) C = C := by
  ext Q
  simp only [divMap_apply, inv_one, placeMap_one]

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
/-- **`g_* div x = div (g x)`**. -/
theorem divMap_div (g : L ≃ₐ[K] L) (x : L) :
    divMap g (Divisor.div κ x) = Divisor.div κ (g x) := by
  ext Q
  rw [divMap_apply, Divisor.div_apply, Divisor.div_apply]
  have := ord_placeMap g (placeMap g⁻¹ Q) x
  rw [placeMap_placeMap_inv] at this
  exact this.symm

omit [NeZero n] in
/-- **`g_* Con B = Con B`**. -/
theorem divMap_conormOf (g : L ≃ₐ[K] L) (B : Divisor κ K) :
    divMap g (conormOf L B) = conormOf L B := by
  ext Q
  rw [divMap_apply, conormOf_apply, conormOf_apply, ramIndex_placeMap, restrict_placeMap]

omit [NeZero n] in
/-- **`div x = Con (div x)`** for `x ∈ K`. -/
theorem div_algebraMap (x : K) :
    Divisor.div κ (algebraMap K L x) = conormOf L (Divisor.div κ x) := by
  ext Q
  rw [Divisor.div_apply, conormOf_apply, Divisor.div_apply, ord_algebraMap_eq_ramIndex_mul]

/-! ### Decomposition of places -/

/-- **`σ^j` fixes a place iff `n ∣ j`**: the action of `Gal(L/K)` on the places is free. -/
theorem placeMap_sigma_pow_eq_iff {j : ℕ} (Q : Place κ L) :
    placeMap (𝔰 ^ j) Q = Q ↔ n ∣ j := by
  refine ⟨fun hQ ↦ ?_, fun h ↦ ?_⟩
  · set P := Q.restrict (K := K)
    set π := unifier P
    have hπ1 : P.ord π = 1 := ord_unifier P
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, Place.ord_zero] at hπ1
      exact zero_ne_one hπ1
    have hα0 := ne_zero hf0 hα
    have hordα : Q.ord α = ramIndex K Q * D P := by
      have h1 : (n : ℤ) * Q.ord α = n * (ramIndex K Q * D P) := by
        rw [← Place.ord_pow, hα, ord_algebraMap_eq_ramIndex_mul]
        have := DFunLike.congr_fun hfD P
        rw [Divisor.div_apply, Finsupp.smul_apply, nsmul_eq_mul] at this
        rw [this]
        ring
      exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne n) h1
    have hden : algebraMap K L π ^ D P ≠ 0 := zpow_ne_zero _ ((_root_.map_ne_zero _).2 hπ0)
    set u := α / algebraMap K L π ^ D P
    have hu0 : u ≠ 0 := div_ne_zero hα0 hden
    have hordu : Q.ord u = 0 := by
      rw [Q.ord_div hα0 hden, Place.ord_zpow, ord_algebraMap_eq_ramIndex_mul, hπ1, hordα]
      ring
    have hτu : (𝔰 ^ j) u = algebraMap κ L (ζ ^ j) * u := by
      simp only [u, map_div₀, map_zpow₀, AlgEquiv.commutes, sigma_pow_apply, map_pow]
      ring
    have hval := val_placeMap (𝔰 ^ j) Q u
    rw [hQ, hτu, Place.val_mul Q (Q.algebraMap_mem _) (Place.mem_of_ord_eq_zero Q hordu),
      Place.val_algebraMap] at hval
    have hv0 := Place.val_ne_zero Q hu0 hordu
    have h1 : ζ ^ j = 1 := mul_right_cancel₀ hv0 (hval.trans (one_mul _).symm)
    exact (hζ.pow_eq_one_iff_dvd j).mp h1
  · rw [(sigma_pow_eq_one_iff hζ hf0 hfD hord hα hgen).mpr h, placeMap_one]

include hζ hf0 hfD hord hα hgen in
/-- The action of `Gal(L/K)` on the places of `L` is free. -/
theorem placeMap_injective (Q : Place κ L) :
    Function.Injective (fun g : L ≃ₐ[K] L ↦ placeMap g Q) := by
  intro g h hgh
  simp only at hgh
  obtain ⟨j, -, hj⟩ := exists_eq_sigma_pow hζ hf0 hfD hord hα hgen (h⁻¹ * g)
  have h1 : placeMap (h⁻¹ * g) Q = Q := by
    rw [placeMap_mul, hgh, placeMap_inv_placeMap]
  rw [hj, placeMap_sigma_pow_eq_iff, ← sigma_pow_eq_one_iff hζ hf0 hfD hord hα hgen] at h1
  rw [h1] at hj
  exact (inv_mul_eq_one.mp hj).symm

omit [NeZero n] in
/-- Every place of `K` has a place of `L` above it. -/
theorem exists_restrict_eq (P : Place κ K) : ∃ Q : Place κ L, Q.restrict (K := K) = P := by
  classical
  by_contra h
  simp only [not_exists] at h
  have hA : conormOf L (Finsupp.single P (1 : ℤ)) = 0 := by
    ext Q
    rw [conormOf_apply, Finsupp.single_apply, if_neg (Ne.symm (h Q)), mul_zero,
      Finsupp.coe_zero, Pi.zero_apply]
  have := deg_conormOf_single (L := L) P
  rw [hA, Divisor.deg_zero, Place.deg_eq_one] at this
  have hpos : 0 < finrank K L := finrank_pos
  push_cast at this
  omega

include hf0 hfD hord hα hgen in
/-- `∑_{Q ∈ T} e(Q|P) ≤ n` for a finite set `T` of places above `P`. -/
lemma sum_ramIndex_le (P : Place κ K) (T : Finset (Place κ L))
    (hT : ∀ Q ∈ T, Q.restrict (K := K) = P) : ∑ Q ∈ T, ramIndex K Q ≤ n := by
  classical
  set A := conormOf L (Finsupp.single P (1 : ℤ))
  have hdeg := deg_conormOf_single (L := L) P
  rw [Place.deg_eq_one, finrank_eq hf0 hfD hord hα hgen,
    Divisor.deg_eq_sum_of_support_subset A (Finset.subset_union_left (s₂ := T))] at hdeg
  have hA : ∀ Q, 0 ≤ A Q * ((Place.deg Q : ℕ) : ℤ) := fun Q ↦ by
    rw [conormOf_apply, Place.deg_eq_one, Finsupp.single_apply]
    have := ramIndex_pos (K := K) Q
    split_ifs <;> positivity
  have h1 : ∑ Q ∈ T, ramIndex K Q = ∑ Q ∈ T, A Q * ((Place.deg Q : ℕ) : ℤ) :=
    Finset.sum_congr rfl fun Q hQ ↦ by
      rw [conormOf_apply, hT Q hQ, Finsupp.single_eq_same, Place.deg_eq_one]
      simp
  rw [h1]
  calc _ ≤ ∑ Q ∈ A.support ∪ T, A Q * ((Place.deg Q : ℕ) : ℤ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun Q _ _ ↦ hA Q
    _ = n := by rw [hdeg]; simp

include hζ hf0 hfD hord hα hgen in
/-- **`L / K` is unramified**: `e(Q|P) = 1` for every place `Q` of `L`. -/
theorem ramIndex_eq_one (Q : Place κ L) : ramIndex K Q = 1 := by
  classical
  have h := sum_ramIndex_le hf0 hfD hord hα hgen (Q.restrict (K := K))
    (Finset.univ.image fun g : L ≃ₐ[K] L ↦ placeMap g Q) (by
      intro Q' hQ'
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hQ'
      exact restrict_placeMap g Q)
  rw [Finset.sum_image fun g _ h _ hgh ↦ placeMap_injective hζ hf0 hfD hord hα hgen Q hgh] at h
  simp only [ramIndex_placeMap, Finset.sum_const, Finset.card_univ,
    card_aut hζ hf0 hfD hord hα hgen, nsmul_eq_mul] at h
  have hpos := ramIndex_pos (K := K) Q
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  nlinarith

include hζ hf0 hfD hord hα hgen in
/-- The places above `Q|_K` form one `Gal(L/K)`-orbit. -/
theorem exists_eq_placeMap' {Q Q' : Place κ L}
    (h : Q'.restrict (K := K) = Q.restrict) : ∃ g : L ≃ₐ[K] L, Q' = placeMap g Q := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  set S := Finset.univ.image fun g : L ≃ₐ[K] L ↦ placeMap g Q
  have hQ' : Q' ∉ S := by
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun g hg ↦ hne g hg.symm
  have h1 := sum_ramIndex_le hf0 hfD hord hα hgen (Q.restrict (K := K)) (insert Q' S) (by
    intro Q'' hQ''
    rcases Finset.mem_insert.mp hQ'' with rfl | hQ''
    · exact h
    · obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hQ''
      exact restrict_placeMap g Q)
  rw [Finset.sum_insert hQ',
    Finset.sum_image fun g _ h _ hgh ↦ placeMap_injective hζ hf0 hfD hord hα hgen Q hgh] at h1
  simp only [ramIndex_eq_one hζ hf0 hfD hord hα hgen, Finset.sum_const, Finset.card_univ,
    card_aut hζ hf0 hfD hord hα hgen, nsmul_eq_mul, mul_one] at h1
  omega

/-- **The places above `Q|_K` are the `σ^j Q`, `j < n`** (and these are distinct,
`placeMap_sigma_pow_eq_iff`). -/
theorem exists_eq_placeMap {Q Q' : Place κ L} (h : Q'.restrict (K := K) = Q.restrict) :
    ∃ j < n, Q' = placeMap (𝔰 ^ j) Q := by
  obtain ⟨g, rfl⟩ := exists_eq_placeMap' hζ hf0 hfD hord hα hgen h
  obtain ⟨j, hj, rfl⟩ := exists_eq_sigma_pow hζ hf0 hfD hord hα hgen g
  exact ⟨j, hj, rfl⟩

/-! ### Norms of divisors -/

variable (K) in
/-- The norm (push-forward) `π_* C = ∑_Q C(Q) · Q|_K` of a divisor of `L`. -/
noncomputable def normDiv : Divisor κ L →+ Divisor κ K :=
  Finsupp.mapDomain.addMonoidHom fun Q : Place κ L ↦ Q.restrict (K := K)

omit [IsAlgClosed κ] [IsFunctionField κ K] [IsFunctionField κ L] [NeZero n] in
lemma normDiv_single (Q : Place κ L) (m : ℤ) :
    normDiv K (Finsupp.single Q m) = Finsupp.single (Q.restrict (K := K)) m :=
  Finsupp.mapDomain_single

omit [NeZero n] in
/-- **`deg π_* C = deg C`** (all places have degree one). -/
theorem deg_normDiv (C : Divisor κ L) : (normDiv K C).deg = C.deg := by
  have : Divisor.degHom.comp (normDiv K) = (Divisor.degHom : Divisor κ L →+ ℤ) :=
    Finsupp.addHom_ext fun Q m ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, normDiv_single,
        Divisor.degHom_apply, Divisor.deg_single, Place.deg_eq_one]
  exact DFunLike.congr_fun this C

include hζ hf0 hfD hord hα hgen in
/-- `(π_* C)(Q|_K) = ∑_{g ∈ Gal(L/K)} C(g Q)`. -/
theorem normDiv_apply_restrict (C : Divisor κ L) (Q : Place κ L) :
    normDiv K C (Q.restrict (K := K)) = ∑ g : L ≃ₐ[K] L, C (placeMap g Q) := by
  classical
  induction C using Finsupp.induction_linear with
  | zero => simp
  | add C₁ C₂ h₁ h₂ =>
    simp only [map_add, Finsupp.coe_add, Pi.add_apply, h₁, h₂, Finset.sum_add_distrib]
  | single Q' m =>
    rw [normDiv_single, Finsupp.single_apply]
    simp only [Finsupp.single_apply]
    split_ifs with h
    · obtain ⟨g₀, rfl⟩ := exists_eq_placeMap' hζ hf0 hfD hord hα hgen h
      rw [Finset.sum_eq_single g₀]
      · simp
      · intro g _ hg
        rw [if_neg]
        exact fun h' ↦ hg (placeMap_injective hζ hf0 hfD hord hα hgen Q h').symm
      · simp
    · symm
      refine Finset.sum_eq_zero fun g _ ↦ if_neg fun h' ↦ h ?_
      rw [h', restrict_placeMap]

include hζ hf0 hfD hord hα hgen in
/-- **`π_* Con B = n B`**. -/
theorem normDiv_conormOf (B : Divisor κ K) : normDiv K (conormOf L B) = n • B := by
  ext P
  obtain ⟨Q, rfl⟩ := exists_restrict_eq (L := L) P
  rw [normDiv_apply_restrict hζ hf0 hfD hord hα hgen]
  simp only [conormOf_apply, ramIndex_eq_one hζ hf0 hfD hord hα hgen, restrict_placeMap, one_mul,
    Finset.sum_const, Finset.card_univ, card_aut hζ hf0 hfD hord hα hgen, Finsupp.smul_apply]

/-- **`∑_{j < n} σ^j_* C = Con π_* C`**. -/
theorem sum_divMap_sigma_pow (C : Divisor κ L) :
    ∑ j ∈ Finset.range n, divMap (𝔰 ^ j) C = conormOf L (normDiv K C) := by
  ext Q
  rw [Finsupp.finsetSum_apply, conormOf_apply, ramIndex_eq_one hζ hf0 hfD hord hα hgen, one_mul,
    normDiv_apply_restrict hζ hf0 hfD hord hα hgen]
  simp only [divMap_apply]
  exact (sum_range_sigma_pow hζ hf0 hfD hord hα hgen fun g ↦ C (placeMap g⁻¹ Q)).trans
    (Fintype.sum_equiv (Equiv.inv _) _ _ fun g ↦ rfl)

/-! ### Divisors with norm `n B` -/

omit [IsFunctionField κ K] [FiniteDimensional K L] [NeZero n] in
lemma div_prod {ι : Type*} (s : Finset ι) (x : ι → L) (hx : ∀ i ∈ s, x i ≠ 0) :
    Divisor.div κ (∏ i ∈ s, x i) = ∑ i ∈ s, Divisor.div κ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Divisor.div_one]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, x i ≠ 0 := fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Divisor.div_mul (hx a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

/-- A divisor `E` with `π_* E = 0` is of the form `C - σ_* C`. -/
theorem exists_sub_divMap_eq {E : Divisor κ L} (hE : normDiv K E = 0) :
    ∃ C : Divisor κ L, C - divMap 𝔰 C = E := by
  classical
  set V := (AddMonoidHom.id (Divisor κ L) - divMap 𝔰).range
  have hV : ∀ C, C - divMap 𝔰 C ∈ V := fun C ↦ ⟨C, rfl⟩
  choose s hs using fun P : Place κ K ↦ exists_restrict_eq (L := L) P
  have step0 : ∀ (Q₀ : Place κ L) (m : ℤ) (j : ℕ),
      Finsupp.single (placeMap (𝔰 ^ j) Q₀) m - Finsupp.single Q₀ m ∈ V := by
    intro Q₀ m j
    induction j with
    | zero => rw [pow_zero, placeMap_one, sub_self]; exact zero_mem V
    | succ j ih =>
      have e : Finsupp.single (placeMap (𝔰 ^ (j + 1)) Q₀) m - Finsupp.single Q₀ m =
          (Finsupp.single (placeMap (𝔰 ^ j) Q₀) m - Finsupp.single Q₀ m) -
          (Finsupp.single (placeMap (𝔰 ^ j) Q₀) m -
            divMap 𝔰 (Finsupp.single (placeMap (𝔰 ^ j) Q₀) m)) := by
        rw [divMap_single, ← placeMap_mul, ← pow_succ']
        abel
      rw [e]
      exact sub_mem ih (hV _)
  have step1 : ∀ (Q : Place κ L) (m : ℤ),
      Finsupp.single Q m - Finsupp.single (s (Q.restrict (K := K))) m ∈ V := by
    intro Q m
    obtain ⟨j, -, hj⟩ := exists_eq_placeMap hζ hf0 hfD hord hα hgen
      (Q := s (Q.restrict (K := K))) (Q' := Q) (hs _).symm
    have := step0 (s (Q.restrict (K := K))) m j
    rwa [← hj] at this
  have step2 : ∀ F : Divisor κ L,
      F - Finsupp.mapDomain (fun Q ↦ s (Q.restrict (K := K))) F ∈ V := by
    intro F
    induction F using Finsupp.induction_linear with
    | zero => simp
    | add F₁ F₂ h₁ h₂ =>
      rw [Finsupp.mapDomain_add]
      convert add_mem h₁ h₂ using 1
      abel
    | single Q m =>
      rw [Finsupp.mapDomain_single]
      exact step1 Q m
  have h3 : Finsupp.mapDomain (fun Q ↦ s (Q.restrict (K := K))) E = 0 := by
    have : (fun Q : Place κ L ↦ s (Q.restrict (K := K))) = s ∘ fun Q ↦ Q.restrict (K := K) := rfl
    rw [this, Finsupp.mapDomain_comp]
    change Finsupp.mapDomain s (normDiv K E) = 0
    rw [hE, Finsupp.mapDomain_zero]
  have := step2 E
  rw [h3, sub_zero] at this
  obtain ⟨C, hC⟩ := this
  exact ⟨C, by simpa using hC⟩

/-- **Divisors of functions whose norm is an `n`-th multiple**: if `div (N γ) = n B`, then
`div γ = C - σ_* C + Con B` for some divisor `C` of `L` (with `(σ_* C)(Q) = C(σ⁻¹ Q)`). -/
theorem exists_div_eq {γ : L} (hγ : γ ≠ 0) {B : Divisor κ K}
    (hB : Divisor.div κ (Algebra.norm K γ) = n • B) :
    ∃ C : Divisor κ L, Divisor.div κ γ = C - divMap 𝔰 C + conormOf L B := by
  haveI := isGalois hζ hf0 hfD hord hα hgen
  have hprod : ∏ j ∈ Finset.range n, (𝔰 ^ j) γ = algebraMap K L (Algebra.norm K γ) := by
    rw [Algebra.norm_eq_prod_automorphisms]
    exact prod_range_sigma_pow hζ hf0 hfD hord hα hgen fun g ↦ g γ
  have h1 : ∑ j ∈ Finset.range n, divMap (𝔰 ^ j) (Divisor.div κ γ) = n • conormOf L B := by
    simp only [divMap_div]
    rw [← div_prod (Finset.range n) (fun j ↦ (𝔰 ^ j) γ)
      fun j _ ↦ (_root_.map_ne_zero _).2 hγ, hprod, div_algebraMap, hB]
    ext Q
    simp only [conormOf_apply, Finsupp.smul_apply, nsmul_eq_mul]
    ring
  have h2 : ∑ j ∈ Finset.range n, divMap (𝔰 ^ j) (conormOf L B) = n • conormOf L B := by
    simp only [divMap_conormOf, Finset.sum_const, Finset.card_range]
  have hN : ∑ j ∈ Finset.range n, divMap (𝔰 ^ j) (Divisor.div κ γ - conormOf L B) = 0 := by
    simp only [map_sub, Finset.sum_sub_distrib, h1, h2, sub_self]
  have hE : normDiv K (Divisor.div κ γ - conormOf L B) = 0 := by
    refine nsmul_cancel (NeZero.ne n) ?_
    rw [← normDiv_conormOf hζ hf0 hfD hord hα hgen,
      ← sum_divMap_sigma_pow hζ hf0 hfD hord hα hgen, hN, map_zero, smul_zero]
  obtain ⟨C, hC⟩ := exists_sub_divMap_eq hζ hf0 hfD hord hα hgen hE
  exact ⟨C, by rw [hC]; abel⟩

end CurvesJacobian.KummerCover
