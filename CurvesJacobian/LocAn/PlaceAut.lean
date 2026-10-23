/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.FunctionField.WeilPairingTransport

/-!
# Automorphisms of a function field fixing a place: the derivative at the place

Let `K/κ` be a function field of one variable over an algebraically closed field `κ` and
`σ ∈ Aut_κ(K)` an automorphism fixing a place `P` (`CurvesJacobian.LocAn.Fixes σ P`: the
transported place `σ(P)` is `P`). For a uniformiser `π` at `P`, `σ π / π` is a unit at `P`; its
value

  `u(σ, P) = (σ π / π)(P) ∈ κˣ`   (`CurvesJacobian.LocAn.derivAt`)

is the action of `σ` on the cotangent space `𝔪_P / 𝔪_P²` (the "derivative" of the automorphism
of the curve at the fixed point `P`). This file proves:

* `CurvesJacobian.LocAn.val_div_apply_of_fixes`: for every `f ≠ 0`,
  `(σ f / f)(P) = u(σ, P) ^ ord_P f` (independence of the uniformiser);
* `CurvesJacobian.LocAn.derivAt_mul`: `u(σ τ, P) = u(σ, P) u(τ, P)`, and `derivAt_one`,
  `derivAt_pow`;
* `CurvesJacobian.LocAn.ord_lt_ord_apply_sub`: if `u(σ, P) = 1`, then `σ f - f` (if nonzero) has
  larger order at `P` than `f`;
* **`CurvesJacobian.LocAn.eq_one_of_fixes_of_derivAt_eq_one`**: in characteristic `0`, an
  automorphism of **finite order** fixing `P` with `u(σ, P) = 1` is the identity. (If
  `g = σ f - f ≠ 0`, then `0 = σ^m f - f = ∑_{i < m} σ^i g = m g + (terms of larger order at P)`.)
* **`CurvesJacobian.LocAn.eq_of_derivAt_eq`**: two commuting automorphisms of finite order fixing
  `P` with the same derivative at `P` are equal. So a finite abelian group of automorphisms fixing
  `P` embeds into `κˣ` (the classical fact that the stabiliser of a point is cyclic in
  characteristic `0`).

These are the function-field inputs (F1) of the uniqueness half of the relative Grothendieck
conjecture for affine hyperbolic curves (MR7 plan, "S2 route"): an automorphism of a curve whose
action on `π₁` is inner fixes the cusps, and the derivative at a cusp is controlled by the cuspidal
inertia.
-/

open WeilCurves.FunctionField

namespace CurvesJacobian.LocAn

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

/-- The transport of places along a `κ`-automorphism `σ` of `K` (`σ(P)` has valuation ring
`σ(𝒪_P)`). -/
def placeMap (σ : K ≃ₐ[κ] K) (P : Place κ K) : Place κ K :=
  placeTr σ.toRingEquiv (RingEquiv.refl κ) (fun c ↦ σ.commutes c) P

/-- `σ` **fixes the place** `P`: `σ(𝒪_P) = 𝒪_P`. -/
def Fixes (σ : K ≃ₐ[κ] K) (P : Place κ K) : Prop :=
  placeMap σ P = P

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma mem_placeMap {σ : K ≃ₐ[κ] K} {P : Place κ K} {x : K} :
    x ∈ (placeMap σ P).1 ↔ σ.symm x ∈ P.1 :=
  mem_placeTr _ _ _

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma fixes_iff {σ : K ≃ₐ[κ] K} {P : Place κ K} : Fixes σ P ↔ ∀ x, σ x ∈ P.1 ↔ x ∈ P.1 := by
  constructor
  · intro h x
    have := (mem_placeMap (σ := σ) (P := P) (x := σ x))
    rw [h, AlgEquiv.symm_apply_apply] at this
    exact this
  · intro h
    refine Place.ext (SetLike.ext fun x ↦ ?_)
    rw [mem_placeMap, ← h, AlgEquiv.apply_symm_apply]

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma Fixes.one (P : Place κ K) : Fixes (1 : K ≃ₐ[κ] K) P :=
  fixes_iff.2 fun _ ↦ Iff.rfl

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma Fixes.mul {σ τ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) (hτ : Fixes τ P) :
    Fixes (σ * τ) P :=
  fixes_iff.2 fun x ↦ by
    rw [AlgEquiv.mul_apply, fixes_iff.1 hσ, fixes_iff.1 hτ]

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma Fixes.pow {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) (n : ℕ) :
    Fixes (σ ^ n) P := by
  induction n with
  | zero => exact Fixes.one P
  | succ n ih => rw [pow_succ]; exact ih.mul hσ

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma Fixes.inv {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) : Fixes σ⁻¹ P :=
  fixes_iff.2 fun x ↦ by
    rw [← fixes_iff.1 hσ (σ⁻¹ x), ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

section Order

/-- `ord_P (σ x) = ord_P x` for `σ` fixing `P`. -/
lemma Fixes.ord_apply {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) (x : K) :
    P.ord (σ x) = P.ord x := by
  have := ord_placeTr σ.toRingEquiv (RingEquiv.refl κ) (fun c ↦ σ.commutes c) P x
  change (placeMap σ P).ord (σ x) = P.ord x at this
  rwa [h] at this

/-- `(σ x)(P) = x(P)` for `σ` fixing `P`. -/
lemma Fixes.val_apply {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) (x : K) :
    Place.val P (σ x) = Place.val P x := by
  have := val_placeTr σ.toRingEquiv (RingEquiv.refl κ) (fun c ↦ σ.commutes c) P x
  change Place.val (placeMap σ P) (σ x) = Place.val P x at this
  rwa [h] at this

/-- A chosen uniformiser at `P`. -/
noncomputable def unif (P : Place κ K) : K := Classical.choose P.exists_ord_eq_one

lemma ord_unif (P : Place κ K) : P.ord (unif P) = 1 := Classical.choose_spec P.exists_ord_eq_one

lemma unif_ne_zero (P : Place κ K) : unif P ≠ 0 := by
  intro h
  have := ord_unif P
  rw [h, Place.ord_zero] at this
  exact zero_ne_one this

/-- **The derivative of `σ` at the fixed place `P`**: `u(σ, P) = (σ π / π)(P)` for the chosen
uniformiser `π` (independent of the choice, `val_div_apply_of_fixes`). -/
noncomputable def derivAt (σ : K ≃ₐ[κ] K) (P : Place κ K) : κ :=
  Place.val P (σ (unif P) / unif P)

lemma Fixes.ord_div_apply {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) {f : K} (hf : f ≠ 0) :
    P.ord (σ f / f) = 0 := by
  have hσf : σ f ≠ 0 := (map_ne_zero_iff σ σ.injective).2 hf
  rw [P.ord_div hσf hf, h.ord_apply, sub_self]

lemma Fixes.val_div_apply_mul {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) {f g : K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    Place.val P (σ (f * g) / (f * g)) = Place.val P (σ f / f) * Place.val P (σ g / g) := by
  have e : σ (f * g) / (f * g) = (σ f / f) * (σ g / g) := by
    rw [map_mul]; field_simp
  rw [e, Place.val_mul P (Place.mem_of_ord_eq_zero P (h.ord_div_apply hf))
    (Place.mem_of_ord_eq_zero P (h.ord_div_apply hg))]

lemma Fixes.val_div_apply_ne_zero {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) {f : K}
    (hf : f ≠ 0) : Place.val P (σ f / f) ≠ 0 :=
  Place.val_ne_zero P (div_ne_zero ((map_ne_zero_iff σ σ.injective).2 hf) hf)
    (h.ord_div_apply hf)

/-- On units at `P`, `(σ w / w)(P) = 1`. -/
lemma Fixes.val_div_apply_of_ord_eq_zero {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) {w : K}
    (hw : w ≠ 0) (hw0 : P.ord w = 0) : Place.val P (σ w / w) = 1 := by
  have hσw : σ w ≠ 0 := (map_ne_zero_iff σ σ.injective).2 hw
  rw [Place.val_div P hw (by rw [h.ord_apply]; exact hw0) hw0, h.val_apply,
    div_self (Place.val_ne_zero P hw hw0)]

lemma Fixes.val_div_apply_inv {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) {f : K}
    (hf : f ≠ 0) : Place.val P (σ f⁻¹ / f⁻¹) = (Place.val P (σ f / f))⁻¹ := by
  have e : σ f⁻¹ / f⁻¹ = (σ f / f)⁻¹ := by
    rw [map_inv₀]; field_simp
  have hσf : σ f ≠ 0 := (map_ne_zero_iff σ σ.injective).2 hf
  rw [e, Place.val_inv P (div_ne_zero hσf hf) (h.ord_div_apply hf)]

/-- **`(σ f / f)(P) = u(σ, P) ^ ord_P f`**. -/
theorem Fixes.val_div_apply {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) {f : K}
    (hf : f ≠ 0) : Place.val P (σ f / f) = derivAt σ P ^ P.ord f := by
  set π := unif P
  have hπ : π ≠ 0 := unif_ne_zero P
  -- powers of `π`
  have hpow : ∀ n : ℕ, Place.val P (σ (π ^ n) / π ^ n) = derivAt σ P ^ n := by
    intro n
    induction n with
    | zero => simp [Place.val_one]
    | succ n ih =>
      rw [pow_succ, h.val_div_apply_mul (pow_ne_zero n hπ) hπ, ih, pow_succ]
      rfl
  have hzpow : ∀ n : ℤ, Place.val P (σ (π ^ n) / π ^ n) = derivAt σ P ^ n := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast, zpow_natCast, hpow]
    · rw [zpow_neg, zpow_natCast, h.val_div_apply_inv (pow_ne_zero m hπ), hpow, zpow_neg,
        zpow_natCast]
  set n := P.ord f
  have hw : f / π ^ n ≠ 0 := div_ne_zero hf (zpow_ne_zero n hπ)
  have hw0 : P.ord (f / π ^ n) = 0 := by
    rw [P.ord_div hf (zpow_ne_zero n hπ), Place.ord_zpow, ord_unif, mul_one, sub_self]
  have e : f = (f / π ^ n) * π ^ n := by field_simp
  rw [e, h.val_div_apply_mul hw (zpow_ne_zero n hπ), h.val_div_apply_of_ord_eq_zero hw hw0,
    one_mul, hzpow]

lemma Fixes.derivAt_ne_zero {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) :
    derivAt σ P ≠ 0 :=
  h.val_div_apply_ne_zero (unif_ne_zero P)

/-- `u(σ, P)` can be computed with any uniformiser. -/
lemma Fixes.derivAt_eq {σ : K ≃ₐ[κ] K} {P : Place κ K} (h : Fixes σ P) {π : K}
    (hπ : P.ord π = 1) : derivAt σ P = Place.val P (σ π / π) := by
  have hπ0 : π ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hπ; exact zero_ne_one hπ
  rw [h.val_div_apply hπ0, hπ, zpow_one]

lemma derivAt_one (P : Place κ K) : derivAt (1 : K ≃ₐ[κ] K) P = 1 := by
  rw [derivAt, AlgEquiv.one_apply, div_self (unif_ne_zero P), Place.val_one]

/-- **The derivative is multiplicative**: `u(σ τ, P) = u(σ, P) u(τ, P)`. -/
theorem derivAt_mul {σ τ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) (hτ : Fixes τ P) :
    derivAt (σ * τ) P = derivAt σ P * derivAt τ P := by
  set π := unif P
  have hπ : π ≠ 0 := unif_ne_zero P
  have hτπ : τ π ≠ 0 := (map_ne_zero_iff τ τ.injective).2 hπ
  have hσπ : σ π ≠ 0 := (map_ne_zero_iff σ σ.injective).2 hπ
  have e : (σ * τ) π / π = σ (τ π / π) * (σ π / π) := by
    rw [AlgEquiv.mul_apply, map_div₀]; field_simp
  have h1 : P.ord (σ (τ π / π)) = 0 := by rw [hσ.ord_apply, hτ.ord_div_apply hπ]
  rw [derivAt, e, Place.val_mul P (Place.mem_of_ord_eq_zero P h1)
    (Place.mem_of_ord_eq_zero P (hσ.ord_div_apply hπ)), hσ.val_apply, mul_comm]
  rfl

lemma derivAt_pow {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) (n : ℕ) :
    derivAt (σ ^ n) P = derivAt σ P ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, derivAt_one]
  | succ n ih => rw [pow_succ, derivAt_mul (hσ.pow n) hσ, ih, pow_succ]

lemma derivAt_inv {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) :
    derivAt σ⁻¹ P = (derivAt σ P)⁻¹ := by
  have h := derivAt_mul hσ hσ.inv
  rw [mul_inv_cancel, derivAt_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- If `u(σ, P) = 1`, then `σ f - f` (when nonzero) has larger order at `P` than `f`. -/
theorem ord_lt_ord_apply_sub {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P)
    (hu : derivAt σ P = 1) {f : K} (hf : f ≠ 0) (hσf : σ f - f ≠ 0) :
    P.ord f < P.ord (σ f - f) := by
  have hmem : σ f / f ∈ P.1 := Place.mem_of_ord_eq_zero P (hσ.ord_div_apply hf)
  have hv : Place.val P (σ f / f) = 1 := by
    rw [hσ.val_div_apply hf, hu, one_zpow]
  have hne : σ f / f - 1 ≠ 0 := by
    intro h0
    apply hσf
    rw [sub_eq_zero, div_eq_one_iff_eq hf] at h0
    rw [h0, sub_self]
  have hpos : 0 < P.ord (σ f / f - 1) := by
    have := (Place.val_eq_iff P hmem 1).1 hv
    rw [map_one] at this
    exact this.resolve_left hne
  have e : σ f - f = f * (σ f / f - 1) := by field_simp
  rw [e, P.ord_mul hf hne]
  omega

end Order

section CharZero

variable [CharZero κ]

/-- Elements `x` that are `0` or of larger order at `P` than `g`. -/
def NearOrd (P : Place κ K) (g x : K) : Prop := x = 0 ∨ P.ord g < P.ord x

omit [IsAlgClosed κ] in
lemma NearOrd.add {P : Place κ K} {g x y : K} (hx : NearOrd P g x) (hy : NearOrd P g y) :
    NearOrd P g (x + y) := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · simp at hxy
    · simpa using hy
  rcases hy with rfl | hy
  · simpa using hx
  exact lt_of_lt_of_le (lt_min hx hy) (P.min_le_ord_add hxy)

lemma NearOrd.map {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) {g x : K}
    (hx : NearOrd P g x) : NearOrd P g (σ x) := by
  rcases hx with rfl | hx
  · exact Or.inl (map_zero σ)
  · exact Or.inr (by rw [hσ.ord_apply]; exact hx)

/-- **An automorphism of finite order fixing a place with derivative `1` there is the
identity** (characteristic `0`). -/
theorem eq_one_of_fixes_of_derivAt_eq_one {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P)
    (hu : derivAt σ P = 1) {m : ℕ} (hm : 0 < m) (hσm : σ ^ m = 1) : σ = 1 := by
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f, σ f ≠ f := by
    by_contra h
    push Not at h
    exact hne (AlgEquiv.ext h)
  set g := σ f - f with hg_def
  clear_value g
  have hg : g ≠ 0 := by rw [hg_def]; exact sub_ne_zero.2 hf
  -- `σ^i g - g` is near `g` for all `i`
  have hnear1 : NearOrd P g (σ g - g) := by
    by_cases h0 : σ g - g = 0
    · exact Or.inl h0
    · exact Or.inr (ord_lt_ord_apply_sub hσ hu hg h0)
  have hneari : ∀ i : ℕ, NearOrd P g ((σ ^ i) g - g) := by
    intro i
    induction i with
    | zero => exact Or.inl (by simp)
    | succ i ih =>
      have e : (σ ^ (i + 1)) g - g = σ ((σ ^ i) g - g) + (σ g - g) := by
        rw [pow_succ', AlgEquiv.mul_apply, map_sub σ]; ring
      rw [e]
      exact NearOrd.add (NearOrd.map hσ ih) hnear1
  -- the telescoping sum
  have htel : ∀ n : ℕ, (σ ^ n) f - f = ∑ i ∈ Finset.range n, (σ ^ i) g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, hg_def, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
      ring
  have hsplit : ∀ n : ℕ, ∑ i ∈ Finset.range n, (σ ^ i) g =
      (n : K) * g + ∑ i ∈ Finset.range n, ((σ ^ i) g - g) := by
    intro n
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hrest : ∀ n : ℕ, NearOrd P g (∑ i ∈ Finset.range n, ((σ ^ i) g - g)) := by
    intro n
    induction n with
    | zero => exact Or.inl (by simp)
    | succ n ihn => rw [Finset.sum_range_succ]; exact NearOrd.add ihn (hneari _)
  have hzero : (m : K) * g + ∑ i ∈ Finset.range m, ((σ ^ i) g - g) = 0 := by
    rw [← hsplit, ← htel, hσm, AlgEquiv.one_apply, sub_self]
  have hmK : (m : K) ≠ 0 := by
    rw [← map_natCast (algebraMap κ K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm.ne')
  have hmg : (m : K) * g ≠ 0 := mul_ne_zero hmK hg
  have hord : P.ord ((m : K) * g) = P.ord g := by
    rw [P.ord_mul hmK hg, Place.ord_natCast, zero_add]
  rcases hrest m with h0 | hlt
  · rw [h0, add_zero] at hzero
    exact hmg hzero
  · rw [eq_neg_of_add_eq_zero_right hzero, Place.ord_neg, hord] at hlt
    exact lt_irrefl _ hlt

/-- **Two commuting automorphisms of finite order fixing `P` with the same derivative at `P` are
equal** (characteristic `0`): the derivative embeds every finite abelian group of automorphisms
fixing `P` into `κˣ`. -/
theorem eq_of_derivAt_eq {σ τ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) (hτ : Fixes τ P)
    (hcomm : Commute σ τ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hσm : σ ^ m = 1) (hτn : τ ^ n = 1)
    (hu : derivAt σ P = derivAt τ P) : σ = τ := by
  have hfix : Fixes (σ * τ⁻¹) P := hσ.mul hτ.inv
  have hu1 : derivAt (σ * τ⁻¹) P = 1 := by
    rw [derivAt_mul hσ hτ.inv, derivAt_inv hτ, hu, mul_inv_cancel₀ hτ.derivAt_ne_zero]
  have hord : (σ * τ⁻¹) ^ (m * n) = 1 := by
    rw [(hcomm.inv_right).mul_pow, pow_mul, hσm, one_pow, one_mul, inv_pow, mul_comm, pow_mul,
      hτn, one_pow, inv_one]
  have := eq_one_of_fixes_of_derivAt_eq_one hfix hu1 (Nat.mul_pos hm hn) hord
  exact mul_inv_eq_one.1 this

end CharZero

end CurvesJacobian.LocAn
