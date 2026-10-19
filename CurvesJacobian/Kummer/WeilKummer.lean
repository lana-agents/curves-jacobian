/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.WeilPairingGalois

/-!
# Kummer characters and the Weil pairing at rational points

Let `K/κ` be a function field over an algebraically closed field `κ`, `Ω ⊇ K` a field and
`x, y` two places of `K`. Fix places `W_x`, `W_y` of `Ω` over `x`, `y` with residue fields `κ`
(`CurvesJacobian.OmegaPlace`). This file proves the **Kummer–Weil identity**
(`CurvesJacobian.exists_kummer_weil`): there is a class `z` with `n z = [x − y]` such that for
every semilinear automorphism `σ` of `K` fixing `x` and `y`, all lifts `τ_x, τ_y` of `σ` to `Ω`
stabilising `W_x`, resp. `W_y`, every `a ∈ Pic(K)[n]` (`n D = div f`) and every `α ∈ Ω` with
`αⁿ = f`,

  `τ_x τ_y⁻¹ (α) / α = e_n(a, σ z − z)`.

This is the identity `χ_a(t_x t_y⁻¹) = e_n(a, σ z − z)` relating the Kummer characters of
`J[n]` with the cocycle of the `n`-division points of `[x − y]` (input of [AbsTopIII]
Prop. 1.6(ii), MR5 J4).

Proof. For `n Z = x − y + div h` put `c_Z(f) = f(Z) / h(D)`; by Weil reciprocity
`c_Z(f)ⁿ = f(x)/f(y)`, so `ρ_Z(a) = (α(W_x)/α(W_y)) / c_Z(f) ∈ μ_n` is a character of `Pic(K)[n]`
(`rhoZ`), hence `ρ_Z = e_n(·, w)` by perfectness, and replacing `Z` by `Z + E_w` makes it trivial.
Then `τ_x τ_y⁻¹(α)/α = σ(R(τ_y⁻¹ α))/R(α)` with `R(β) = β(W_x)/β(W_y)` (residues), which is
`c_{σZ}(f)/c_Z(f) = e_n(a, [σ Z − Z])`.

For the Galois model `F k̄ ⊆ Ω` of a curve with a `k`-point the hypotheses (divisibility of
`[x − y]`, perfectness of `e_n`) are `exists_nsmul_eq_sub_baseChange` and
`CurvesJacobian.Kummer.weilDual_bijective_baseChange`.
-/

open WeilCurves.FunctionField CurvesJacobian.Kummer AlgebraicGeometry Belyi KummerTheory Curve
open AffOrbicurve CurvesJacobian.Cusp CategoryTheory

namespace CurvesJacobian

set_option linter.unusedSectionVars false

variable {κ K Ω : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]
  [Field Ω] [Algebra K Ω]

variable (K Ω) in
/-- `κ → K → Ω`. -/
abbrev κΩ : κ →+* Ω := (algebraMap K Ω).comp (algebraMap κ K)

/-- A place of `Ω` over the place `P` of `K`, with residue field `κ`. -/
structure OmegaPlace (P : Place κ K) where
  /-- The valuation ring. -/
  W : ValuationSubring Ω
  liesOver : ∀ g : K, algebraMap K Ω g ∈ W ↔ g ∈ P.1
  bijective : Function.Bijective fun c : κ ↦
    IsLocalRing.residue W ⟨algebraMap K Ω (algebraMap κ K c),
      (liesOver _).mpr (P.algebraMap_mem c)⟩

namespace OmegaPlace

variable {P : Place κ K} (A : OmegaPlace (Ω := Ω) P)


lemma algebraMap_mem (c : κ) : κΩ K Ω c ∈ A.W :=
  (A.liesOver _).mpr (P.algebraMap_mem c)

/-- `κ ≃ 𝒪_W / 𝔪_W`. -/
noncomputable def resEquiv : κ ≃+* IsLocalRing.ResidueField A.W :=
  RingEquiv.ofBijective ((IsLocalRing.residue A.W).comp
    ((κΩ K Ω).codRestrict A.W.toSubring A.algebraMap_mem)) A.bijective

/-- The residue map `𝒪_W → κ`. -/
noncomputable def resHom : A.W →+* κ := A.resEquiv.symm.toRingHom.comp (IsLocalRing.residue A.W)

open Classical in
/-- The residue `β(W) ∈ κ` of `β ∈ 𝒪_W` (junk `0` otherwise). -/
noncomputable def res (β : Ω) : κ := if h : β ∈ A.W then A.resHom ⟨β, h⟩ else 0

lemma res_of_mem {β : Ω} (h : β ∈ A.W) : A.res β = A.resHom ⟨β, h⟩ := by
  rw [res, dif_pos h]

lemma res_of_notMem {β : Ω} (h : β ∉ A.W) : A.res β = 0 := by
  rw [res, dif_neg h]

lemma resHom_algebraMap (c : κ) : A.resHom ⟨κΩ K Ω c, A.algebraMap_mem c⟩ = c := by
  change A.resEquiv.symm (A.resEquiv c) = c
  exact A.resEquiv.symm_apply_apply c

@[simp]
lemma res_algebraMap (c : κ) : A.res (κΩ K Ω c) = c := by
  rw [res_of_mem A (A.algebraMap_mem c), resHom_algebraMap]

lemma res_mul {β β' : Ω} (h : β ∈ A.W) (h' : β' ∈ A.W) :
    A.res (β * β') = A.res β * A.res β' := by
  rw [res_of_mem A (mul_mem h h'), res_of_mem A h, res_of_mem A h', ← map_mul]
  rfl

lemma res_one : A.res 1 = 1 := by
  simpa using A.res_algebraMap 1

/-- `β(W) = c` iff `β - c ∈ 𝔪_W`. -/
lemma res_eq_iff {β : Ω} (h : β ∈ A.W) (c : κ) :
    A.res β = c ↔ β - κΩ K Ω c = 0 ∨ (β - κΩ K Ω c)⁻¹ ∉ A.W := by
  have hm : β - κΩ K Ω c ∈ A.W := sub_mem h (A.algebraMap_mem c)
  rw [← ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.valuation_lt_one_iff A.W ⟨_, hm⟩, ← IsLocalRing.residue_eq_zero_iff]
  have : IsLocalRing.residue A.W ⟨_, hm⟩ = IsLocalRing.residue A.W ⟨β, h⟩ -
      IsLocalRing.residue A.W ⟨κΩ K Ω c, A.algebraMap_mem c⟩ := by
    rw [← map_sub]; rfl
  rw [this, sub_eq_zero, res_of_mem A h, resHom, RingEquiv.toRingHom_eq_coe, RingHom.comp_apply,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  rfl

lemma res_ne_zero {β : Ω} (h0 : β ≠ 0) (h : β ∈ A.W) (h' : β⁻¹ ∈ A.W) : A.res β ≠ 0 := by
  intro hr
  have := A.res_mul h h'
  rw [mul_inv_cancel₀ h0, A.res_one, hr, zero_mul] at this
  exact one_ne_zero this

/-- Values of functions of `K`: `g(W) = g(P)`. -/
lemma res_algebraMap_K {g : K} (hg : g ∈ P.1) : A.res (algebraMap K Ω g) = Place.val P g := by
  rw [res_eq_iff A ((A.liesOver g).mpr hg)]
  rcases (Place.val_eq_iff P hg (Place.val P g)).mp rfl with h0 | hpos
  · left
    change algebraMap K Ω g - algebraMap K Ω (algebraMap κ K _) = 0
    rw [← map_sub, h0, map_zero]
  · right
    change (algebraMap K Ω g - algebraMap K Ω (algebraMap κ K _))⁻¹ ∉ A.W
    rw [← map_sub, ← map_inv₀, A.liesOver]
    intro hinv
    have := P.ord_nonneg_of_mem hinv
    rw [Place.ord_inv] at this
    omega

/-- **Decomposition automorphisms act on residues through the constants**: if `τ` stabilises
`W` and acts on `κ` by `σ`, then `(τ β)(W) = σ(β(W))`. -/
lemma res_map (τ : Ω ≃+* Ω) (σ : κ ≃+* κ) (hτW : ∀ β, τ β ∈ A.W ↔ β ∈ A.W)
    (hτκ : ∀ c, τ (κΩ K Ω c) = κΩ K Ω (σ c)) (β : Ω) : A.res (τ β) = σ (A.res β) := by
  by_cases h : β ∈ A.W
  · have h1 := (res_eq_iff A h (A.res β)).mp rfl
    refine (res_eq_iff A ((hτW β).mpr h) _).mpr ?_
    rw [← hτκ, ← map_sub]
    rcases h1 with h1 | h1
    · left; rw [h1, map_zero]
    · right
      rw [← map_inv₀, hτW]
      exact h1
  · rw [res_of_notMem A h, res_of_notMem A (by rwa [hτW]), map_zero]

end OmegaPlace

/-! ### Kummer roots at places of `Ω` -/

section Roots

lemma OmegaPlace.mem_of_pow_eq {P : Place κ K} (A : OmegaPlace (Ω := Ω) P) {β : Ω} {g : K}
    {n : ℕ} (hn : n ≠ 0) (hβ : β ^ n = algebraMap K Ω g) (hg : g ≠ 0) (hord : P.ord g = 0) :
    β ∈ A.W ∧ β⁻¹ ∈ A.W := by
  obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff hg).1 hord
  have hg1 : algebraMap K Ω g ∈ A.W := (A.liesOver g).mpr h1
  have hg2 : (algebraMap K Ω g)⁻¹ ∈ A.W := by rw [← map_inv₀]; exact (A.liesOver _).mpr h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero m), eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective]
      at hβ
    exact hg hβ
  rcases A.W.mem_or_inv_mem β with h | h
  · refine ⟨h, ?_⟩
    have : β⁻¹ = (algebraMap K Ω g)⁻¹ * β ^ m := by
      rw [← hβ, pow_succ]; field_simp
    rw [this]; exact mul_mem hg2 (pow_mem h m)
  · refine ⟨?_, h⟩
    have : β = algebraMap K Ω g * β⁻¹ ^ m := by
      rw [← hβ, pow_succ, inv_pow]; field_simp
    rw [this]; exact mul_mem hg1 (pow_mem h m)

variable [IsAlgClosed Ω]

/-- An `n`-th root (in `Ω`) of a constant is a constant. -/
lemma mem_range_κΩ_of_pow_eq {n : ℕ} (hn : n ≠ 0) {γ : Ω} {c : κ} (hγ : γ ^ n = κΩ K Ω c) :
    γ ∈ (κΩ (κ := κ) K Ω).range := by
  have hf0 : (Polynomial.X ^ n - Polynomial.C c : Polynomial κ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) c
  refine (IsAlgClosed.splits _).mem_range_of_isRoot hf0 ?_
  simp [Polynomial.IsRoot, hγ]

end Roots

/-! ### The character `ρ_Z` -/

section Rho

variable {n : ℕ} {x y : Place κ K}

variable (n x y) in
/-- A divisor `Z` with `n Z = x − y + div h`. -/
structure DivPt where
  /-- The divisor. -/
  Z : Divisor κ K
  /-- The function. -/
  h : K
  h_ne : h ≠ 0
  nsmul_eq : n • Z = Finsupp.single x 1 - Finsupp.single y 1 + Divisor.div κ h

namespace DivPt

variable (p : DivPt n x y)

open Classical in
/-- The places to avoid: `x`, `y` and the supports of `Z` and `div h`. -/
noncomputable def S : Finset (Place κ K) :=
  insert x (insert y (p.Z.support ∪ (Divisor.div κ p.h).support))

lemma x_mem_S : x ∈ p.S := by classical simp [S]
lemma y_mem_S : y ∈ p.S := by classical simp [S]
lemma mem_S_of_Z {P : Place κ K} (hP : p.Z P ≠ 0) : P ∈ p.S := by
  classical simp [S, Finsupp.mem_support_iff, hP]
lemma mem_S_of_h {P : Place κ K} (hP : P.ord p.h ≠ 0) : P ∈ p.S := by
  classical simp [S, Finsupp.mem_support_iff, Divisor.div_apply, hP]

lemma deg_Z (hn : n ≠ 0) : p.Z.deg = 0 := by
  have h := congrArg Divisor.deg p.nsmul_eq
  rw [Divisor.deg_nsmul, Divisor.deg_add, Divisor.deg_sub, Divisor.deg_single, Divisor.deg_single,
    Divisor.deg_div, Place.deg_eq_one, Place.deg_eq_one] at h
  simp only [Nat.cast_one, mul_one, sub_self, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

/-- `c_Z(f) = f(Z) / h(D)`. -/
noncomputable def c (D : Divisor κ K) (f : K) : κ := evalDiv f p.Z / evalDiv p.h D

end DivPt

variable [IsAlgClosed Ω] (Ax : OmegaPlace (Ω := Ω) x) (Ay : OmegaPlace (Ω := Ω) y)

/-- `R(β) = β(W_x) / β(W_y)`. -/
noncomputable def resRatio (β : Ω) : κ := Ax.res β / Ay.res β

omit [IsAlgClosed Ω] in
lemma TorsRep.ord_f {a : Pic κ K} (r : TorsRep n a) (P : Place κ K) :
    P.ord r.f = n * r.D P := by
  have h4 := congrArg (fun E : Divisor κ K ↦ E P) r.nsmul_eq
  simp only [Finsupp.smul_apply, nsmul_eq_mul, Divisor.div_apply] at h4
  exact h4.symm

lemma resRatio_mul {β β' : Ω} (hx : β ∈ Ax.W) (hx' : β' ∈ Ax.W) (hy : β ∈ Ay.W)
    (hy' : β' ∈ Ay.W) :
    resRatio Ax Ay (β * β') = resRatio Ax Ay β * resRatio Ax Ay β' := by
  rw [resRatio, resRatio, resRatio, Ax.res_mul hx hx', Ay.res_mul hy hy', mul_div_mul_comm]

lemma resRatio_κ {c : κ} (hc : c ≠ 0) : resRatio Ax Ay (κΩ K Ω c) = 1 := by
  rw [resRatio, Ax.res_algebraMap, Ay.res_algebraMap, div_self hc]

lemma resRatio_K {u : K} (hx : u ∈ x.1) (hy : u ∈ y.1) :
    resRatio Ax Ay (algebraMap K Ω u) = Place.val x u / Place.val y u := by
  rw [resRatio, Ax.res_algebraMap_K hx, Ay.res_algebraMap_K hy]

variable [NeZero n]

/-- Kummer roots of functions without zero or pole at `x` and `y` are units at `W_x`, `W_y`. -/
lemma mem_W_of_root {a : Pic κ K} (r : TorsRep n a) (hrx : r.D x = 0) (hry : r.D y = 0)
    {β : Ω} (hβ : β ^ n = algebraMap K Ω r.f) :
    (β ∈ Ax.W ∧ β⁻¹ ∈ Ax.W) ∧ (β ∈ Ay.W ∧ β⁻¹ ∈ Ay.W) :=
  ⟨Ax.mem_of_pow_eq (NeZero.ne n) hβ r.f_ne (by rw [TorsRep.ord_f, hrx, mul_zero]),
    Ay.mem_of_pow_eq (NeZero.ne n) hβ r.f_ne (by rw [TorsRep.ord_f, hry, mul_zero])⟩

variable (p : DivPt n x y)

/-- **Invariance of `R(β) / c_Z(f)`** under change of the representative (avoiding `x`, `y`,
`Z` and `div h`) and of the Kummer root (Weil reciprocity). -/
theorem resRatio_div_c_eq {a : Pic κ K} (r r' : TorsRep n a) (hr : ∀ P ∈ p.S, r.D P = 0)
    (hr' : ∀ P ∈ p.S, r'.D P = 0) {β β' : Ω} (hβ : β ^ n = algebraMap K Ω r.f)
    (hβ' : β' ^ n = algebraMap K Ω r'.f) :
    resRatio Ax Ay β / p.c r.D r.f = resRatio Ax Ay β' / p.c r'.D r'.f := by
  have hn : n ≠ 0 := NeZero.ne n
  -- `r'.D = r.D + div u`
  have hmk : (QuotientAddGroup.mk (r'.D - r.D) : Pic κ K) = 0 := by
    rw [QuotientAddGroup.mk_sub, r.mk_eq, r'.mk_eq, sub_self]
  obtain ⟨u, hu, hudiv⟩ := mem_principal.mp ((QuotientAddGroup.eq_zero_iff _).mp hmk)
  have hordu : ∀ P, P.ord u = r'.D P - r.D P := fun P ↦ by
    rw [← Divisor.div_apply (k := κ), hudiv]; rfl
  -- `r'.f = c' · r.f · uⁿ`
  have hdivf : Divisor.div κ r'.f = Divisor.div κ (r.f * u ^ n) := by
    rw [← r'.nsmul_eq, Divisor.div_mul r.f_ne (pow_ne_zero n hu), Divisor.div_pow, hudiv,
      ← r.nsmul_eq, smul_sub]; abel
  obtain ⟨c', hc', hfc⟩ := exists_eq_const_mul_of_div_eq r'.f_ne
    (mul_ne_zero r.f_ne (pow_ne_zero n hu)) hdivf
  -- `β' = γ · β · u` with `γ` constant
  obtain ⟨⟨hβx, hβx'⟩, ⟨hβy, hβy'⟩⟩ := mem_W_of_root Ax Ay r (hr x p.x_mem_S) (hr y p.y_mem_S) hβ
  have hβ0 : β ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hβ
    exact r.f_ne hβ
  have hu0 : algebraMap K Ω u ≠ 0 := (map_ne_zero _).mpr hu
  obtain ⟨γ, hγ⟩ : β' / (β * algebraMap K Ω u) ∈ (κΩ (κ := κ) K Ω).range := by
    refine mem_range_κΩ_of_pow_eq hn (c := c') ?_
    have hf0 : algebraMap K Ω r.f ≠ 0 := (map_ne_zero _).mpr r.f_ne
    have hun : algebraMap K Ω (u ^ n) ≠ 0 := (map_ne_zero _).mpr (pow_ne_zero n hu)
    rw [div_pow, mul_pow, hβ, hβ', hfc, ← map_pow, map_mul, map_mul,
      mul_div_cancel_right₀ _ (mul_ne_zero hf0 hun)]
    rfl
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, div_eq_zero_iff] at hγ
    rcases hγ with h | h
    · rw [h, zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hβ'
      exact r'.f_ne hβ'
    · exact mul_ne_zero hβ0 hu0 h
  have hβ'eq : β' = κΩ K Ω γ * (β * algebraMap K Ω u) := by
    rw [hγ, div_mul_cancel₀ _ (mul_ne_zero hβ0 hu0)]
  -- memberships of `u`
  have hux : u ∈ x.1 ∧ u⁻¹ ∈ x.1 := (x.ord_eq_zero_iff hu).1 (by
    rw [hordu, hr x p.x_mem_S, hr' x p.x_mem_S, sub_zero])
  have huy : u ∈ y.1 ∧ u⁻¹ ∈ y.1 := (y.ord_eq_zero_iff hu).1 (by
    rw [hordu, hr y p.y_mem_S, hr' y p.y_mem_S, sub_zero])
  have hκx : κΩ K Ω γ ∈ Ax.W := Ax.algebraMap_mem γ
  have hκy : κΩ K Ω γ ∈ Ay.W := Ay.algebraMap_mem γ
  have hux' : algebraMap K Ω u ∈ Ax.W := (Ax.liesOver u).mpr hux.1
  have huy' : algebraMap K Ω u ∈ Ay.W := (Ay.liesOver u).mpr huy.1
  have hR : resRatio Ax Ay β' = resRatio Ax Ay β * (Place.val x u / Place.val y u) := by
    rw [hβ'eq, resRatio_mul Ax Ay hκx (mul_mem hβx hux') hκy (mul_mem hβy huy'),
      resRatio_κ Ax Ay hγ0, one_mul, resRatio_mul Ax Ay hβx hux' hβy huy', resRatio_K Ax Ay hux.1
      huy.1]
  -- `c_Z(r'.f) = c_Z(r.f) · u(x)/u(y)`
  have hZ : ∀ P, p.Z P ≠ 0 → r.D P = 0 ∧ r'.D P = 0 := fun P hP ↦
    ⟨hr P (p.mem_S_of_Z hP), hr' P (p.mem_S_of_Z hP)⟩
  have hfZ : Avoids r.f p.Z := ⟨r.f_ne, fun P hP ↦ by rw [TorsRep.ord_f, (hZ P hP).1, mul_zero]⟩
  have huZ : Avoids u p.Z := ⟨hu, fun P hP ↦ by rw [hordu, (hZ P hP).1, (hZ P hP).2, sub_zero]⟩
  have hhD : Avoids p.h r.D := ⟨p.h_ne, fun P hP ↦ by
    by_contra hc; exact hP (hr P (p.mem_S_of_h hc))⟩
  have hhu : Avoids p.h (Divisor.div κ u) := ⟨p.h_ne, fun P hP ↦ by
    by_contra hc
    rw [Divisor.div_apply, hordu, hr P (p.mem_S_of_h hc), hr' P (p.mem_S_of_h hc), sub_zero]
      at hP
    exact hP rfl⟩
  have hrec := weil_reciprocity (κ := κ) hu p.h_ne fun P ↦ by
    by_cases hP : P.ord p.h = 0
    · exact Or.inr hP
    · left; rw [hordu, hr P (p.mem_S_of_h hP), hr' P (p.mem_S_of_h hP), sub_zero]
  have hsx : Avoids u (Finsupp.single x 1) := ⟨hu, fun P hP ↦ by
    by_cases h : x = P
    · subst h; exact (x.ord_eq_zero_iff hu).2 hux
    · rw [Finsupp.single_apply, if_neg h] at hP; exact absurd rfl hP⟩
  have hsy : Avoids u (Finsupp.single y 1) := ⟨hu, fun P hP ↦ by
    by_cases h : y = P
    · subst h; exact (y.ord_eq_zero_iff hu).2 huy
    · rw [Finsupp.single_apply, if_neg h] at hP; exact absurd rfl hP⟩
  have huh : Avoids u (Divisor.div κ p.h) := ⟨hu, fun P hP ↦ by
    by_contra hc
    rw [hordu, sub_eq_zero] at hc
    exact hP (by rw [Divisor.div_apply]; by_contra hc'; exact hc (by
      rw [hr P (p.mem_S_of_h hc'), hr' P (p.mem_S_of_h hc')]))⟩
  have hnZ : evalDiv u p.Z ^ n = Place.val x u / Place.val y u * evalDiv u (Divisor.div κ p.h) := by
    rw [← evalDiv_nsmul huZ, p.nsmul_eq, evalDiv_add (hsx.sub hsy) huh, evalDiv_sub hsx hsy,
      evalDiv_single, evalDiv_single, zpow_one, zpow_one]
  have hdegZ := p.deg_Z hn
  have hc'Z : evalDiv r'.f p.Z = evalDiv r.f p.Z * evalDiv u p.Z ^ n := by
    rw [hfc, evalDiv_mul (avoids_algebraMap hc' _) (hfZ.mul (huZ.pow n)),
      evalDiv_algebraMap hc', hdegZ, zpow_zero, one_mul, evalDiv_mul hfZ (huZ.pow n),
      evalDiv_pow huZ]
  have hD' : r'.D = r.D + Divisor.div κ u := by rw [hudiv]; abel
  have hcr' : p.c r'.D r'.f = p.c r.D r.f * (Place.val x u / Place.val y u) := by
    rw [DivPt.c, DivPt.c, hc'Z, hnZ, hD', evalDiv_add hhD hhu, hrec]
    have h1 : evalDiv p.h r.D ≠ 0 := evalDiv_ne_zero hhD
    have h2 : evalDiv p.h (Divisor.div κ u) ≠ 0 := evalDiv_ne_zero hhu
    have hv2 : Place.val y u ≠ 0 := Place.val_ne_zero y hu ((y.ord_eq_zero_iff hu).2 huy)
    field_simp
  rw [hR, hcr']
  have hv1 : Place.val x u ≠ 0 := Place.val_ne_zero x hu ((x.ord_eq_zero_iff hu).2 hux)
  have hv2 : Place.val y u ≠ 0 := Place.val_ne_zero y hu ((y.ord_eq_zero_iff hu).2 huy)
  field_simp

lemma exists_good_rep (S : Finset (Place κ K)) (a : picTorsion κ K n) :
    ∃ r : TorsRep n (a : Pic κ K), ∀ P ∈ S, r.D P = 0 :=
  TorsRep.exists_avoid a.2 S

lemma exists_root {a : Pic κ K} (r : TorsRep n a) : ∃ β : Ω, β ^ n = algebraMap K Ω r.f :=
  IsAlgClosed.exists_pow_nat_eq _ (Nat.pos_of_ne_zero (NeZero.ne n))

lemma resRatio_ne_zero {a : Pic κ K} (r : TorsRep n a) (hrx : r.D x = 0) (hry : r.D y = 0)
    {β : Ω} (hβ : β ^ n = algebraMap K Ω r.f) : resRatio Ax Ay β ≠ 0 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := mem_W_of_root Ax Ay r hrx hry hβ
  have hβ0 : β ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow (NeZero.ne n), eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hβ
    exact r.f_ne hβ
  exact div_ne_zero (Ax.res_ne_zero hβ0 h1 h2) (Ay.res_ne_zero hβ0 h3 h4)

lemma avoids_f_Z {a : Pic κ K} (r : TorsRep n a) (hr : ∀ P ∈ p.S, r.D P = 0) : Avoids r.f p.Z :=
  ⟨r.f_ne, fun P hP ↦ by rw [TorsRep.ord_f, hr P (p.mem_S_of_Z hP), mul_zero]⟩

lemma avoids_h_D {a : Pic κ K} (r : TorsRep n a) (hr : ∀ P ∈ p.S, r.D P = 0) :
    Avoids p.h r.D :=
  ⟨p.h_ne, fun P hP ↦ by by_contra hc; exact hP (hr P (p.mem_S_of_h hc))⟩

lemma c_ne_zero {a : Pic κ K} (r : TorsRep n a) (hr : ∀ P ∈ p.S, r.D P = 0) :
    p.c r.D r.f ≠ 0 :=
  div_ne_zero (evalDiv_ne_zero (avoids_f_Z p r hr)) (evalDiv_ne_zero (avoids_h_D p r hr))

/-- The value `ρ_Z(a) = R(β) / c_Z(f)` for a chosen good representative and root. -/
noncomputable def rhoVal (a : picTorsion κ K n) : κ :=
  resRatio Ax Ay (exists_root (Ω := Ω) (exists_good_rep p.S a).choose).choose /
    p.c (exists_good_rep p.S a).choose.D (exists_good_rep p.S a).choose.f

/-- `ρ_Z(a)` is computed by any good representative and root. -/
lemma rhoVal_eq (a : picTorsion κ K n) (r : TorsRep n (a : Pic κ K))
    (hr : ∀ P ∈ p.S, r.D P = 0) {β : Ω} (hβ : β ^ n = algebraMap K Ω r.f) :
    rhoVal Ax Ay p a = resRatio Ax Ay β / p.c r.D r.f :=
  resRatio_div_c_eq Ax Ay p _ r (exists_good_rep p.S a).choose_spec hr
    (exists_root (exists_good_rep p.S a).choose).choose_spec hβ

lemma rhoVal_ne_zero (a : picTorsion κ K n) : rhoVal Ax Ay p a ≠ 0 :=
  div_ne_zero (resRatio_ne_zero Ax Ay _ ((exists_good_rep p.S a).choose_spec x p.x_mem_S)
    ((exists_good_rep p.S a).choose_spec y p.y_mem_S)
    (exists_root (Ω := Ω) (exists_good_rep p.S a).choose).choose_spec)
    (c_ne_zero p _ (exists_good_rep p.S a).choose_spec)

lemma rhoVal_add (a b : picTorsion κ K n) :
    rhoVal Ax Ay p (a + b) = rhoVal Ax Ay p a * rhoVal Ax Ay p b := by
  obtain ⟨r, hr⟩ := exists_good_rep p.S a
  obtain ⟨s, hs⟩ := exists_good_rep p.S b
  obtain ⟨β, hβ⟩ := exists_root (Ω := Ω) r
  obtain ⟨β', hβ'⟩ := exists_root (Ω := Ω) s
  have hrs : ∀ P ∈ p.S, (r.add s).D P = 0 := fun P hP ↦ by
    change r.D P + s.D P = 0; rw [hr P hP, hs P hP, add_zero]
  have hββ' : (β * β') ^ n = algebraMap K Ω (r.add s).f := by
    rw [mul_pow, hβ, hβ', ← map_mul]; rfl
  rw [rhoVal_eq Ax Ay p (a + b) (r.add s) hrs hββ', rhoVal_eq Ax Ay p a r hr hβ,
    rhoVal_eq Ax Ay p b s hs hβ']
  obtain ⟨⟨h1, -⟩, ⟨h3, -⟩⟩ := mem_W_of_root Ax Ay r (hr x p.x_mem_S) (hr y p.y_mem_S) hβ
  obtain ⟨⟨h1', -⟩, ⟨h3', -⟩⟩ := mem_W_of_root Ax Ay s (hs x p.x_mem_S) (hs y p.y_mem_S) hβ'
  rw [resRatio_mul Ax Ay h1 h1' h3 h3']
  have hc : p.c (r.add s).D (r.add s).f = p.c r.D r.f * p.c s.D s.f := by
    change evalDiv (r.f * s.f) p.Z / evalDiv p.h (r.D + s.D) = _
    rw [evalDiv_mul (avoids_f_Z p r hr) (avoids_f_Z p s hs),
      evalDiv_add (avoids_h_D p r hr) (avoids_h_D p s hs), DivPt.c, DivPt.c, mul_div_mul_comm]
  rw [hc, mul_div_mul_comm]

/-- **The character `ρ_Z : Pic(K)[n] → κˣ`**. -/
noncomputable def rho : Multiplicative (picTorsion κ K n) →* κˣ where
  toFun a := Units.mk0 (rhoVal Ax Ay p (Multiplicative.toAdd a)) (rhoVal_ne_zero Ax Ay p _)
  map_one' := by
    apply Units.ext
    have h := rhoVal_add Ax Ay p 0 0
    rw [add_zero] at h
    exact (mul_eq_left₀ (rhoVal_ne_zero Ax Ay p 0)).mp h.symm
  map_mul' a b := Units.ext (rhoVal_add Ax Ay p _ _)

omit [IsAlgClosed Ω] in
lemma exists_divPt (hdiv : ∃ z : Pic κ K, n • z =
      QuotientAddGroup.mk (Finsupp.single x 1 - Finsupp.single y 1)) :
    Nonempty (DivPt n x y) := by
  obtain ⟨z, hz⟩ := hdiv
  obtain ⟨Z, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [← QuotientAddGroup.mk_nsmul, eq_comm, ← sub_eq_zero, ← QuotientAddGroup.mk_sub,
    QuotientAddGroup.eq_zero_iff] at hz
  obtain ⟨h, h0, hh⟩ := mem_principal.mp (neg_mem hz)
  exact ⟨⟨Z, h, h0, by rw [hh]; abel⟩⟩

variable [CharZero κ] in
/-- **Normalisation of `Z`** (perfectness): there are `Z` and a finite set `T ⊇ S_Z` such that
`R(β) = c_Z(f)` for every representative avoiding `T` and every Kummer root `β`. -/
theorem exists_divPt_resRatio_eq
    (hdiv : ∃ z : Pic κ K, n • z = QuotientAddGroup.mk (Finsupp.single x 1 - Finsupp.single y 1))
    (hperf : Function.Bijective (weilDual (κ := κ) (K := K) (n := n))) :
    ∃ (p : DivPt n x y) (T : Finset (Place κ K)), p.S ⊆ T ∧
      ∀ (a : picTorsion κ K n) (r : TorsRep n (a : Pic κ K)), (∀ P ∈ T, r.D P = 0) →
        ∀ β : Ω, β ^ n = algebraMap K Ω r.f → resRatio Ax Ay β = p.c r.D r.f := by
  classical
  obtain ⟨p₀⟩ := exists_divPt hdiv
  obtain ⟨w, hw⟩ := hperf.2 (rho Ax Ay p₀)
  obtain ⟨E, hE⟩ := TorsRep.exists_avoid w.2 p₀.S
  let p : DivPt n x y :=
    ⟨p₀.Z + E.D, p₀.h * E.f, mul_ne_zero p₀.h_ne E.f_ne, by
      rw [smul_add, p₀.nsmul_eq, E.nsmul_eq, Divisor.div_mul p₀.h_ne E.f_ne]; abel⟩
  refine ⟨p, p₀.S ∪ p.S ∪ E.D.support, fun P hP ↦ Finset.mem_union_left _
    (Finset.mem_union_right _ hP), fun a r hr β hβ ↦ ?_⟩
  have hr₀ : ∀ P ∈ p₀.S, r.D P = 0 := fun P hP ↦
    hr P (Finset.mem_union_left _ (Finset.mem_union_left _ hP))
  have hrE : DisjSupp r.D E.D := fun P ↦ by
    by_cases hP : E.D P = 0
    · exact Or.inr hP
    · exact Or.inl (hr P (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hP)))
  have hχ : rhoVal Ax Ay p₀ a = weilPairing n a w := by
    have := congrArg (fun χ ↦ ((χ (Multiplicative.ofAdd a) : κˣ) : κ)) hw
    exact this.symm
  rw [rhoVal_eq Ax Ay p₀ a r hr₀ hβ, weilPairing_eq a w r E hrE, pairVal] at hχ
  have hfE : Avoids r.f E.D := avoids_of_disjSupp r.f_ne r.nsmul_eq hrE
  have hED : Avoids E.f r.D := avoids_of_disjSupp E.f_ne E.nsmul_eq hrE.symm
  have hc : p.c r.D r.f = p₀.c r.D r.f * (evalDiv r.f E.D / evalDiv E.f r.D) := by
    change evalDiv r.f (p₀.Z + E.D) / evalDiv (p₀.h * E.f) r.D = _
    rw [evalDiv_add (avoids_f_Z p₀ r hr₀) hfE, evalDiv_mul (avoids_h_D p₀ r hr₀) hED, DivPt.c,
      mul_div_mul_comm]
  rw [hc, ← hχ]
  have h1 := c_ne_zero p₀ r hr₀
  field_simp

omit [NeZero n] in
/-- Two Kummer roots of representatives of the same class differ by `γ · u`, `γ ∈ κ`, `u ∈ K`. -/
lemma exists_root_eq {a : Pic κ K} (r r' : TorsRep n a) (hn : n ≠ 0) {β β' : Ω}
    (hβ : β ^ n = algebraMap K Ω r.f) (hβ' : β' ^ n = algebraMap K Ω r'.f) :
    ∃ (γ : κ) (u : K), u ≠ 0 ∧ β' = κΩ K Ω γ * (β * algebraMap K Ω u) := by
  have hmk : (QuotientAddGroup.mk (r'.D - r.D) : Pic κ K) = 0 := by
    rw [QuotientAddGroup.mk_sub, r.mk_eq, r'.mk_eq, sub_self]
  obtain ⟨u, hu, hudiv⟩ := mem_principal.mp ((QuotientAddGroup.eq_zero_iff _).mp hmk)
  have hdivf : Divisor.div κ r'.f = Divisor.div κ (r.f * u ^ n) := by
    rw [← r'.nsmul_eq, Divisor.div_mul r.f_ne (pow_ne_zero n hu), Divisor.div_pow, hudiv,
      ← r.nsmul_eq, smul_sub]; abel
  obtain ⟨c', _, hfc⟩ := exists_eq_const_mul_of_div_eq r'.f_ne
    (mul_ne_zero r.f_ne (pow_ne_zero n hu)) hdivf
  have hβ0 : β ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hβ
    exact r.f_ne hβ
  have hu0 : algebraMap K Ω u ≠ 0 := (map_ne_zero _).mpr hu
  obtain ⟨γ, hγ⟩ : β' / (β * algebraMap K Ω u) ∈ (κΩ (κ := κ) K Ω).range := by
    refine mem_range_κΩ_of_pow_eq hn (c := c') ?_
    have hf0 : algebraMap K Ω r.f ≠ 0 := (map_ne_zero _).mpr r.f_ne
    have hun : algebraMap K Ω (u ^ n) ≠ 0 := (map_ne_zero _).mpr (pow_ne_zero n hu)
    rw [div_pow, mul_pow, hβ, hβ', hfc, ← map_pow, map_mul, map_mul,
      mul_div_cancel_right₀ _ (mul_ne_zero hf0 hun)]
    rfl
  exact ⟨γ, u, hu, by rw [hγ, div_mul_cancel₀ _ (mul_ne_zero hβ0 hu0)]⟩

omit [NeZero n] in
/-- The Kummer character `δ(β)/β` (`δ` fixing `K`) only depends on the class. -/
lemma kummer_ratio_eq {a : Pic κ K} (r r' : TorsRep n a) (hn : n ≠ 0) {β β' : Ω}
    (hβ : β ^ n = algebraMap K Ω r.f) (hβ' : β' ^ n = algebraMap K Ω r'.f) (δ : Ω ≃+* Ω)
    (hδ : ∀ g : K, δ (algebraMap K Ω g) = algebraMap K Ω g) : δ β' / β' = δ β / β := by
  obtain ⟨γ, u, hu, rfl⟩ := exists_root_eq r r' hn hβ hβ'
  have hβ0 : β ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hβ
    exact r.f_ne hβ
  have hγ0 : κΩ K Ω γ ≠ 0 := by
    rintro h0
    rw [h0, zero_mul, zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hβ'
    exact r'.f_ne hβ'
  have hu0 : algebraMap K Ω u ≠ 0 := (map_ne_zero _).mpr hu
  rw [map_mul, map_mul, hδ u]
  change δ (algebraMap K Ω (algebraMap κ K γ)) * _ / _ = _
  rw [hδ]
  change κΩ K Ω γ * (δ β * algebraMap K Ω u) / (κΩ K Ω γ * (β * algebraMap K Ω u)) = δ β / β
  field_simp

end Rho

/-! ### The Kummer–Weil identity -/

section Identity

variable [IsAlgClosed Ω] {n : ℕ} [NeZero n] {x y : Place κ K}
  (Ax : OmegaPlace (Ω := Ω) x) (Ay : OmegaPlace (Ω := Ω) y)

omit [IsAlgClosed Ω] [NeZero n] in
lemma divTr_single' {κ' K' : Type*} [Field κ'] [Field K'] [Algebra κ' K'] (φ : K ≃+* K')
    (ψ : κ ≃+* κ') (hφ : ∀ c : κ, φ (algebraMap κ K c) = algebraMap κ' K' (ψ c))
    [IsFunctionField κ' K'] (Q : Place κ K) (m : ℤ) :
    divTr φ ψ hφ (Finsupp.single Q m) = Finsupp.single (placeTr φ ψ hφ Q) m :=
  Finsupp.equivMapDomain_single _ _ _

omit [IsAlgClosed Ω] [NeZero n] in
lemma placeTr_symm_placeTr (σ : constAut κ K) (P : Place κ K) :
    placeTr (σ : K ≃+* K).symm (constRes σ).symm (symm_tr _ _ (constRes_spec σ))
      (placeTr (σ : K ≃+* K) (constRes σ) (constRes_spec σ) P) = P :=
  (placeTrEquiv _ _ (constRes_spec σ)).symm_apply_apply P

omit [IsAlgClosed Ω] [NeZero n] in
lemma divTr_divTr_symm (σ : constAut κ K) (D : Divisor κ K) :
    divTr (σ : K ≃+* K) (constRes σ) (constRes_spec σ)
      (divTr (σ : K ≃+* K).symm (constRes σ).symm (symm_tr _ _ (constRes_spec σ)) D) = D := by
  ext P
  rw [divTr_apply, divTr_apply]
  congr 1
  apply Place.ext
  ext g
  simp [placeTrEquiv, mem_placeTr]

variable [CharZero κ] in
/-- **The Kummer–Weil identity** (see the module docstring): there is `z` with `n z = [x − y]`
such that `τ_x τ_y⁻¹(α)/α = e_n(a, σ z − z)` for all `σ` fixing `x, y`, all lifts `τ_x, τ_y` of `σ`
in the decomposition groups of `W_x`, `W_y`, all `a ∈ Pic(K)[n]` and Kummer roots `α` of `a`. -/
theorem exists_kummer_weil
    (hdiv : ∃ z : Pic κ K, n • z = QuotientAddGroup.mk (Finsupp.single x 1 - Finsupp.single y 1))
    (hperf : Function.Bijective (weilDual (κ := κ) (K := K) (n := n))) :
    ∃ z : Pic κ K, n • z = QuotientAddGroup.mk (Finsupp.single x 1 - Finsupp.single y 1) ∧
      ∀ (σ : constAut κ K), Kummer.placeMap σ x = x → Kummer.placeMap σ y = y →
      ∀ (τx τy : Ω ≃+* Ω),
        (∀ g, τx (algebraMap K Ω g) = algebraMap K Ω ((σ : K ≃+* K) g)) →
        (∀ g, τy (algebraMap K Ω g) = algebraMap K Ω ((σ : K ≃+* K) g)) →
        (∀ β, τx β ∈ Ax.W ↔ β ∈ Ax.W) → (∀ β, τy β ∈ Ay.W ↔ β ∈ Ay.W) →
      ∀ (a : picTorsion κ K n) (r : TorsRep n (a : Pic κ K)) (α : Ω),
        α ^ n = algebraMap K Ω r.f →
        ∃ hz : picMap σ z - z ∈ picTorsion κ K n,
          τx (τy.symm α) / α = κΩ K Ω (weilPairing n a ⟨_, hz⟩) := by
  classical
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨p, T, hpT, hKP⟩ := exists_divPt_resRatio_eq Ax Ay hdiv hperf
  refine ⟨QuotientAddGroup.mk p.Z, ?_, ?_⟩
  · rw [← QuotientAddGroup.mk_nsmul, p.nsmul_eq, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff _).mpr (div_mem_principal p.h_ne), add_zero]
  intro σ hσx hσy τx τy hτx hτy hWx hWy a r α hα
  set φ : K ≃+* K := (σ : K ≃+* K)
  set ψ := constRes σ
  have hφ := constRes_spec σ
  have hpx : placeTr φ ψ hφ x = x := by rw [← placeMap_eq_placeTr]; exact hσx
  have hpy : placeTr φ ψ hφ y = y := by rw [← placeMap_eq_placeTr]; exact hσy
  -- `σ Z`
  set Zσ := divTr φ ψ hφ p.Z with hZσdef
  have hZσ : n • Zσ = Finsupp.single x 1 - Finsupp.single y 1 + Divisor.div κ (φ p.h) := by
    rw [hZσdef, ← map_nsmul, p.nsmul_eq, map_add, map_sub, divTr_single', divTr_single', hpx, hpy,
      ← div_tr]
  have hφh0 : φ p.h ≠ 0 := (map_ne_zero _).mpr p.h_ne
  have hb : n • (Zσ - p.Z) = Divisor.div κ (φ p.h / p.h) := by
    rw [smul_sub, hZσ, p.nsmul_eq, Divisor.div_div hφh0 p.h_ne]; abel
  have hcl : picMap σ (QuotientAddGroup.mk p.Z) - QuotientAddGroup.mk p.Z =
      (QuotientAddGroup.mk (Zσ - p.Z) : Pic κ K) := by
    rw [picMap_eq_picTr, picTr_mk, QuotientAddGroup.mk_sub]
  have hz : picMap σ (QuotientAddGroup.mk p.Z) - QuotientAddGroup.mk p.Z ∈ picTorsion κ K n := by
    change n • (_ : Pic κ K) = 0
    rw [hcl, ← QuotientAddGroup.mk_nsmul, hb, QuotientAddGroup.eq_zero_iff]
    exact div_mem_principal (div_ne_zero hφh0 p.h_ne)
  refine ⟨hz, ?_⟩
  -- a good representative
  obtain ⟨r₁, hr₁⟩ := TorsRep.exists_avoid a.2 (T ∪ T.image (placeTr φ ψ hφ))
  obtain ⟨α₁, hα₁⟩ := exists_root (Ω := Ω) r₁
  have hr₁T : ∀ P ∈ T, r₁.D P = 0 := fun P hP ↦ hr₁ P (Finset.mem_union_left _ hP)
  -- `δ = τ_x τ_y⁻¹` fixes `K`
  have hτy' : ∀ g, τy.symm (algebraMap K Ω g) = algebraMap K Ω (φ.symm g) := fun g ↦ by
    rw [RingEquiv.symm_apply_eq, hτy, RingEquiv.apply_symm_apply]
  have hδ : ∀ g : K, (τy.symm.trans τx) (algebraMap K Ω g) = algebraMap K Ω g := fun g ↦ by
    change τx (τy.symm _) = _
    rw [hτy', hτx, RingEquiv.apply_symm_apply]
  have hred := kummer_ratio_eq r₁ r hn hα₁ hα (τy.symm.trans τx) hδ
  change τx (τy.symm α) / α = τx (τy.symm α₁) / α₁ at hred
  rw [hred]
  -- the conjugate representative `σ⁻¹ r₁`
  set r₁' := r₁.tr φ.symm ψ.symm (symm_tr _ _ hφ)
  have hr₁' : ∀ P ∈ T, r₁'.D P = 0 := fun P hP ↦ by
    change divTr φ.symm ψ.symm _ r₁.D P = 0
    rw [divTr_apply]
    refine hr₁ _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨P, hP, ?_⟩))
    apply Place.ext; ext g; simp [placeTrEquiv, mem_placeTr]
  set α' := τy.symm α₁
  have hα' : α' ^ n = algebraMap K Ω r₁'.f := by
    change (τy.symm α₁) ^ n = algebraMap K Ω (φ.symm r₁.f)
    rw [← map_pow, hα₁, hτy']
  have hT1 := hKP _ r₁ hr₁T α₁ hα₁
  have hT2 := hKP ⟨_, picTr_mem_picTorsion φ.symm ψ.symm (symm_tr _ _ hφ) a.2⟩ r₁' hr₁' α' hα'
  -- `χ = τ_x(α')/α₁ ∈ μ_n ⊆ κ`
  have hα₁0 : α₁ ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K Ω).injective] at hα₁
    exact r₁.f_ne hα₁
  have hχn : (τx α' / α₁) ^ n = κΩ (κ := κ) K Ω 1 := by
    rw [div_pow, ← map_pow, hα', hα₁]
    change τx (algebraMap K Ω (φ.symm r₁.f)) / _ = _
    rw [hτx, RingEquiv.apply_symm_apply, div_self ((map_ne_zero _).mpr r₁.f_ne), map_one]
  obtain ⟨ζ, hζ⟩ := mem_range_κΩ_of_pow_eq hn hχn
  have hτxα' : τx α' = κΩ K Ω ζ * α₁ := by rw [hζ, div_mul_cancel₀ _ hα₁0]
  -- residues
  have hτκ : ∀ (τ : Ω ≃+* Ω), (∀ g, τ (algebraMap K Ω g) = algebraMap K Ω (φ g)) →
      ∀ c, τ (κΩ K Ω c) = κΩ K Ω (ψ c) := fun τ hτ c ↦ by
    change τ (algebraMap K Ω (algebraMap κ K c)) = algebraMap K Ω (algebraMap κ K (ψ c))
    rw [hτ, ← hφ]
  obtain ⟨⟨h1, -⟩, ⟨h3, -⟩⟩ := mem_W_of_root Ax Ay r₁ (hr₁T x (hpT p.x_mem_S))
    (hr₁T y (hpT p.y_mem_S)) hα₁
  obtain ⟨⟨h1', h2'⟩, ⟨h3', h4'⟩⟩ := mem_W_of_root Ax Ay r₁' (hr₁' x (hpT p.x_mem_S))
    (hr₁' y (hpT p.y_mem_S)) hα'
  have hrx : Ax.res (τx α') = ψ (Ax.res α') := Ax.res_map τx ψ hWx (hτκ τx hτx) α'
  have hry : Ay.res α₁ = ψ (Ay.res α') := by
    have := Ay.res_map τy ψ hWy (hτκ τy hτy) α'
    rwa [show τy α' = α₁ from τy.apply_symm_apply α₁] at this
  rw [hτxα', Ax.res_mul (Ax.algebraMap_mem ζ) h1, Ax.res_algebraMap] at hrx
  have hζeq : ζ = ψ (resRatio Ax Ay α') / resRatio Ax Ay α₁ := by
    have hx0 : Ax.res α₁ ≠ 0 := by
      obtain ⟨⟨_, h2⟩, -⟩ := mem_W_of_root Ax Ay r₁ (hr₁T x (hpT p.x_mem_S))
        (hr₁T y (hpT p.y_mem_S)) hα₁
      exact Ax.res_ne_zero hα₁0 h1 h2
    have hy0 : ψ (Ay.res α') ≠ 0 := by
      rw [← hry]
      obtain ⟨-, ⟨_, h4⟩⟩ := mem_W_of_root Ax Ay r₁ (hr₁T x (hpT p.x_mem_S))
        (hr₁T y (hpT p.y_mem_S)) hα₁
      exact Ay.res_ne_zero hα₁0 h3 h4
    rw [resRatio, resRatio, map_div₀, ← hrx, ← hry]
    rw [← hry] at hy0
    field_simp
  -- evaluate
  rw [← hζ]
  congr 1
  set e := placeTrEquiv φ ψ hφ
  have himg : ∀ P, r₁.D P ≠ 0 → e.symm P ∉ T := fun P hP hT ↦ hP (hr₁ P
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hT, e.apply_symm_apply P⟩)))
  have hZT : ∀ P, p.Z P ≠ 0 → P ∈ T := fun P hP ↦ hpT (p.mem_S_of_Z hP)
  have hZσP : ∀ P, r₁.D P ≠ 0 → Zσ P = 0 := fun P hP ↦ by
    rw [hZσdef, divTr_apply]
    by_contra hc
    exact himg P hP (hZT _ hc)
  have hZP : ∀ P, r₁.D P ≠ 0 → p.Z P = 0 := fun P hP ↦ by
    by_contra hc; exact hP (hr₁T P (hZT P hc))
  let s : TorsRep n (picMap σ (QuotientAddGroup.mk p.Z) - QuotientAddGroup.mk p.Z) :=
    ⟨Zσ - p.Z, φ p.h / p.h, div_ne_zero hφh0 p.h_ne, hcl.symm, hb⟩
  have hdisj : DisjSupp r₁.D s.D := fun P ↦ by
    by_cases hP : r₁.D P = 0
    · exact Or.inl hP
    · right; change Zσ P - p.Z P = 0; rw [hZσP P hP, hZP P hP, sub_zero]
  rw [weilPairing_eq a ⟨_, hz⟩ r₁ s hdisj, hζeq, hT1, hT2, pairVal]
  have hfZ : Avoids r₁.f p.Z := avoids_f_Z p r₁ fun P hP ↦ hr₁T P (hpT hP)
  have hfZσ : Avoids r₁.f Zσ := ⟨r₁.f_ne, fun P hP ↦ by
    by_contra hc
    rw [TorsRep.ord_f] at hc
    exact hP (hZσP P fun h0 ↦ hc (by rw [h0, mul_zero]))⟩
  have hhD : Avoids p.h r₁.D := avoids_h_D p r₁ fun P hP ↦ hr₁T P (hpT hP)
  have hφhD : Avoids (φ p.h) r₁.D := ⟨hφh0, fun P hP ↦ by
    have h6 := ord_placeTr φ ψ hφ (e.symm P) p.h
    rw [show placeTr φ ψ hφ (e.symm P) = P from e.apply_symm_apply P] at h6
    rw [h6]
    by_contra hc
    exact himg P hP (hpT (p.mem_S_of_h hc))⟩
  have hs : p.c r₁'.D r₁'.f = ψ.symm (evalDiv r₁.f Zσ / evalDiv (φ p.h) r₁.D) := by
    rw [RingEquiv.eq_symm_apply, DivPt.c, map_div₀, ← evalDiv_tr φ ψ hφ, ← evalDiv_tr φ ψ hφ]
    change evalDiv (φ (φ.symm r₁.f)) Zσ / evalDiv (φ p.h)
      (divTr φ ψ hφ (divTr φ.symm ψ.symm (symm_tr _ _ hφ) r₁.D)) = _
    rw [RingEquiv.apply_symm_apply, divTr_divTr_symm]
  rw [hs, RingEquiv.apply_symm_apply, DivPt.c]
  change _ = evalDiv r₁.f (Zσ - p.Z) / evalDiv (φ p.h / p.h) r₁.D
  rw [evalDiv_sub hfZσ hfZ, evalDiv_div hφhD hhD]
  have h1 := evalDiv_ne_zero hfZ
  have h2 := evalDiv_ne_zero hhD
  have h3 := evalDiv_ne_zero hφhD
  field_simp

end Identity

/-! ### The Galois model of a curve -/

section Curve

universe u

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

attribute [local instance] isFunctionField_F

include σ hσ in
/-- `[x − y]` is `n`-divisible in `Pic(F k̄)` (`J(k̄)` is divisible). With
`weilDual_bijective_baseChange` this provides the hypotheses of `CurvesJacobian.exists_kummer_weil`
(the Kummer–Weil identity) for `J(k̄)[n]` in the Galois model of a curve with a `k`-point. -/
theorem exists_nsmul_eq_sub_baseChange {n : ℕ} (hn : n ≠ 0)
    (x y : Place (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) :
    ∃ z : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))),
      n • z = QuotientAddGroup.mk (Finsupp.single x 1 - Finsupp.single y 1) := by
  have hdeg : (QuotientAddGroup.mk (Finsupp.single x 1 - Finsupp.single y 1) :
      Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) ∈
      (Pic.deg (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))).ker := by
    rw [AddMonoidHom.mem_ker, Pic.deg_mk, Divisor.deg_sub, Divisor.deg_single,
      Divisor.deg_single, Place.deg_eq_one, Place.deg_eq_one, sub_self]
  obtain ⟨w, hw⟩ := exists_nsmul_eq_jacPsi k hτ σ hσ hn ⟨_, hdeg⟩
  exact ⟨w, congrArg Subtype.val hw⟩

end Curve

end CurvesJacobian
