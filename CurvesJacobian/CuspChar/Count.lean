/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sigma

/-!
# Cusp counts of subgroups and of cyclic covers of prime degree (step G1 of [AbsTopI] Lemma 4.5 (v))

Let `S` be a set of subgroups of a group `Δ` ("cusp groups") that is stable under conjugation and
consists of self-normalising subgroups (`N_Δ(I) = I`, [AbsTopI] Lemma 4.5 (vi)). For a subgroup
`H ⊆ Δ` the **cusps of `H`** are the `H`-conjugacy classes of `S`
(`CurvesJacobian.CuspChar.CuspQuot S H`), and `cuspCount S H` is their number (for a curve: the
number of cusps of the covering corresponding to `H`).

For an additive character `ξ : H → ℤ/p` (`p` prime) which is onto, let `H' = ker ξ` and call the
cusp of `I` *ramified* in `ξ` if `ξ` is nontrivial on `I ∩ H`. Main result
(`CurvesJacobian.CuspChar.cuspCount_ker_add`):

  `r(H') + (p - 1) · #{ramified cusps of H} = p · r(H)`,

i.e. an unramified cusp splits into `p` cusps of `H'`, a ramified one into a single one. Hence the
number of cusps ramified in `ξ` is determined by the cusp counts of `H` and `H'`
(`CurvesJacobian.CuspChar.ramCusps_eq_of_cuspCount_eq`).
-/

namespace CurvesJacobian.CuspChar

variable {Δ : Type*} [Group Δ]

/-- The conjugate `g I g⁻¹` of a subgroup. -/
abbrev conjSub (g : Δ) (I : Subgroup Δ) : Subgroup Δ := I.map (MulAut.conj g).toMonoidHom

lemma mem_conjSub_iff {g x : Δ} {I : Subgroup Δ} : x ∈ conjSub g I ↔ g⁻¹ * x * g ∈ I := by
  simp only [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa [mul_assoc] using hi
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

lemma conj_mem_conjSub {g x : Δ} {I : Subgroup Δ} (hx : x ∈ I) : g * x * g⁻¹ ∈ conjSub g I :=
  mem_conjSub_iff.2 (by simpa [mul_assoc] using hx)

@[simp] lemma conjSub_one (I : Subgroup Δ) : conjSub 1 I = I := by
  ext x
  simp

lemma conjSub_mul (g h : Δ) (I : Subgroup Δ) : conjSub (g * h) I = conjSub g (conjSub h I) := by
  ext x
  simp only [mem_conjSub_iff, mul_inv_rev]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

lemma conjSub_inv_conjSub (g : Δ) (I : Subgroup Δ) : conjSub g⁻¹ (conjSub g I) = I := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

/-- A set of subgroups is **conjugation-stable**. -/
def ConjStable (S : Set (Subgroup Δ)) : Prop := ∀ I ∈ S, ∀ g : Δ, conjSub g I ∈ S

/-- The `H`-conjugacy relation on `S`. -/
def cuspSetoid (S : Set (Subgroup Δ)) (H : Subgroup Δ) : Setoid S where
  r I J := ∃ h ∈ H, conjSub h (I : Subgroup Δ) = J
  iseqv :=
    { refl := fun I ↦ ⟨1, H.one_mem, conjSub_one _⟩
      symm := by
        rintro I J ⟨h, hh, hIJ⟩
        exact ⟨h⁻¹, H.inv_mem hh, by rw [← hIJ, conjSub_inv_conjSub]⟩
      trans := by
        rintro I J K ⟨h, hh, hIJ⟩ ⟨h', hh', hJK⟩
        exact ⟨h' * h, H.mul_mem hh' hh, by rw [conjSub_mul, hIJ, hJK]⟩ }

/-- The **cusps of `H`**: the `H`-conjugacy classes of `S`. -/
abbrev CuspQuot (S : Set (Subgroup Δ)) (H : Subgroup Δ) : Type _ := Quotient (cuspSetoid S H)

/-- The **number of cusps of `H`**. -/
noncomputable def cuspCount (S : Set (Subgroup Δ)) (H : Subgroup Δ) : ℕ := Nat.card (CuspQuot S H)

/-- For `H' ≤ H`, the natural map from the cusps of `H'` to those of `H`. -/
def cuspMap (S : Set (Subgroup Δ)) {H' H : Subgroup Δ} (hle : H' ≤ H) :
    CuspQuot S H' → CuspQuot S H :=
  Quotient.map' id fun _ _ ⟨h, hh, e⟩ ↦ ⟨h, hle hh, e⟩

lemma cuspMap_surjective (S : Set (Subgroup Δ)) {H' H : Subgroup Δ} (hle : H' ≤ H) :
    Function.Surjective (cuspMap S hle) := by
  rintro ⟨I⟩
  exact ⟨Quotient.mk _ I, rfl⟩

section Ker

variable {p : ℕ} (H : Subgroup Δ) (ξ : Additive H →+ ZMod p)

/-- The kernel `H' = ker ξ ⊆ H`, as a subgroup of `Δ`. -/
def kerSub : Subgroup Δ where
  carrier := {x | ∃ hx : x ∈ H, ξ (Additive.ofMul ⟨x, hx⟩) = 0}
  one_mem' := ⟨H.one_mem, ξ.map_zero⟩
  mul_mem' := by
    rintro x y ⟨hx, ex⟩ ⟨hy, ey⟩
    refine ⟨H.mul_mem hx hy, ?_⟩
    have : (Additive.ofMul (⟨x * y, H.mul_mem hx hy⟩ : H)) =
        Additive.ofMul (⟨x, hx⟩ : H) + Additive.ofMul ⟨y, hy⟩ := rfl
    rw [this, map_add, ex, ey, add_zero]
  inv_mem' := by
    rintro x ⟨hx, ex⟩
    refine ⟨H.inv_mem hx, ?_⟩
    have : (Additive.ofMul (⟨x⁻¹, H.inv_mem hx⟩ : H)) = -Additive.ofMul (⟨x, hx⟩ : H) := rfl
    rw [this, map_neg, ex, neg_zero]

lemma kerSub_le : kerSub H ξ ≤ H := fun _ ⟨hx, _⟩ ↦ hx

/-- The value of `ξ` at an element of `Δ` lying in `H` (`0` outside `H`). -/
noncomputable def ξv (x : Δ) : ZMod p := by
  classical
  exact if hx : x ∈ H then ξ (Additive.ofMul ⟨x, hx⟩) else 0

variable {H ξ}

lemma ξv_of_mem {x : Δ} (hx : x ∈ H) : ξv H ξ x = ξ (Additive.ofMul ⟨x, hx⟩) := by
  simp [ξv, hx]

lemma ξv_mul {x y : Δ} (hx : x ∈ H) (hy : y ∈ H) :
    ξv H ξ (x * y) = ξv H ξ x + ξv H ξ y := by
  rw [ξv_of_mem (H.mul_mem hx hy), ξv_of_mem hx, ξv_of_mem hy, ← map_add]
  rfl

lemma ξv_inv {x : Δ} (hx : x ∈ H) : ξv H ξ x⁻¹ = -ξv H ξ x := by
  rw [ξv_of_mem (H.inv_mem hx), ξv_of_mem hx, ← map_neg]
  rfl

lemma ξv_conj {h x : Δ} (hh : h ∈ H) (hx : x ∈ H) : ξv H ξ (h * x * h⁻¹) = ξv H ξ x := by
  rw [ξv_mul (H.mul_mem hh hx) (H.inv_mem hh), ξv_mul hh hx, ξv_inv hh]
  abel

lemma mem_kerSub_iff {x : Δ} : x ∈ kerSub H ξ ↔ x ∈ H ∧ ξv H ξ x = 0 := by
  constructor
  · rintro ⟨hx, e⟩
    exact ⟨hx, by rw [ξv_of_mem hx, e]⟩
  · rintro ⟨hx, e⟩
    exact ⟨hx, by rwa [ξv_of_mem hx] at e⟩

variable (H ξ)

/-- `ξ` is **ramified** at the cusp group `I`: it is nontrivial on `I ∩ H`. -/
def IsRam (I : Subgroup Δ) : Prop := ∃ x ∈ I, x ∈ H ∧ ξv H ξ x ≠ 0

lemma isRam_conjSub {I : Subgroup Δ} {h : Δ} (hh : h ∈ H) :
    IsRam H ξ (conjSub h I) ↔ IsRam H ξ I := by
  constructor
  · rintro ⟨x, hxI, hxH, hx⟩
    refine ⟨h⁻¹ * x * h, mem_conjSub_iff.1 hxI, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem hh) hxH) hh
    · have := ξv_conj (ξ := ξ) (H.inv_mem hh) hxH
      rw [inv_inv] at this
      rwa [this]
  · rintro ⟨x, hxI, hxH, hx⟩
    refine ⟨h * x * h⁻¹, conj_mem_conjSub hxI, H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), ?_⟩
    rwa [ξv_conj hh hxH]

/-- Ramification of a cusp of `H` (well defined on `H`-conjugacy classes). -/
def CuspRam (S : Set (Subgroup Δ)) : CuspQuot S H → Prop :=
  Quotient.lift (fun I : S ↦ IsRam H ξ (I : Subgroup Δ)) fun I J ⟨h, hh, e⟩ ↦ by
    rw [← e, isRam_conjSub H ξ hh]

/-- The number of cusps of `H` ramified in `ξ`. -/
noncomputable def ramCusps (S : Set (Subgroup Δ)) : ℕ :=
  Nat.card {y : CuspQuot S H // CuspRam H ξ S y}

variable {S : Set (Subgroup Δ)}

/-- The fibre of `cusps(ker ξ) → cusps(H)` over the class of `I`. -/
abbrev Fib (I : S) : Type _ :=
  {z : CuspQuot S (kerSub H ξ) // cuspMap S (kerSub_le H ξ) z = Quotient.mk _ I}

/-- Over an unramified cusp, the fibre is a `ZMod p`-torsor: `k ↦ [h_k I h_k⁻¹]`. -/
lemma card_fib_of_not_ram [Fact p.Prime] (hS : ConjStable S)
    (hN : ∀ I ∈ S, ∀ g : Δ, conjSub g I = I → g ∈ I)
    (hξ : Function.Surjective ξ) (I : S) (hI : ¬ IsRam H ξ I) : Nat.card (Fib H ξ I) = p := by
  classical
  have hlift : ∀ k : ZMod p, ∃ h : Δ, h ∈ H ∧ ξv H ξ h = k := by
    intro k
    obtain ⟨⟨h, hh⟩, e⟩ := hξ k
    exact ⟨h, hh, by rw [ξv_of_mem hh]; exact e⟩
  choose hk hkH hkv using hlift
  let elt : ZMod p → S := fun k ↦ ⟨conjSub (hk k) I, hS _ I.2 _⟩
  let φ : ZMod p → Fib H ξ I := fun k ↦
    ⟨Quotient.mk _ (elt k),
      Quotient.sound ⟨(hk k)⁻¹, H.inv_mem (hkH k), conjSub_inv_conjSub _ _⟩⟩
  have hinj : Function.Injective φ := by
    intro k m hkm
    have hq : (Quotient.mk _ (elt k) : CuspQuot S (kerSub H ξ)) = Quotient.mk _ (elt m) :=
      congrArg Subtype.val hkm
    obtain ⟨h', hh', e⟩ := Quotient.exact hq
    -- `(h_m)⁻¹ h' h_k` normalises `I`, hence lies in `I ∩ H`
    have hmem : (hk m)⁻¹ * h' * hk k ∈ (I : Subgroup Δ) := by
      apply hN _ I.2
      simp only [elt] at e
      rw [conjSub_mul, conjSub_mul, e, conjSub_inv_conjSub]
    have hh'H := (mem_kerSub_iff.1 hh').1
    have hH : (hk m)⁻¹ * h' * hk k ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem (hkH m)) hh'H) (hkH k)
    have hv : ξv H ξ ((hk m)⁻¹ * h' * hk k) = 0 := by
      by_contra hne
      exact hI ⟨_, hmem, hH, hne⟩
    rw [ξv_mul (H.mul_mem (H.inv_mem (hkH m)) hh'H) (hkH k),
      ξv_mul (H.inv_mem (hkH m)) hh'H, ξv_inv (hkH m), (mem_kerSub_iff.1 hh').2, hkv, hkv] at hv
    have : k - m = 0 := by rw [← hv]; ring
    exact (sub_eq_zero.1 this)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    induction z using Quotient.inductionOn with
    | h J =>
    obtain ⟨h, hh, e⟩ := Quotient.exact hz
    -- `J = h⁻¹ I h`, write `h⁻¹ = h'' h_k` with `ξ h'' = 0`
    set k := ξv H ξ h⁻¹
    refine ⟨k, Subtype.ext (Quotient.sound ?_)⟩
    refine ⟨h⁻¹ * (hk k)⁻¹, H.mul_mem (H.inv_mem hh) (H.inv_mem (hkH k)) |> fun hm ↦
      mem_kerSub_iff.2 ⟨hm, ?_⟩, ?_⟩
    · rw [ξv_mul (H.inv_mem hh) (H.inv_mem (hkH k)), ξv_inv (hkH k), hkv]
      simp [k]
    · simp only [elt]
      rw [← conjSub_mul, inv_mul_cancel_right, ← e, conjSub_inv_conjSub]
      rfl
  have := Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
  rw [Nat.card_zmod] at this
  exact this.symm

/-- Over a ramified cusp, the fibre is a single point. -/
lemma card_fib_of_ram [Fact p.Prime] (I : S) (hI : IsRam H ξ I) :
    Nat.card (Fib H ξ I) = 1 := by
  classical
  obtain ⟨x, hxI, hxH, hx⟩ := hI
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨?_⟩, ⟨⟨Quotient.mk _ I, rfl⟩⟩⟩
  -- every point of the fibre is the class of `I`
  have key : ∀ z : Fib H ξ I, z.1 = Quotient.mk _ I := by
    rintro ⟨z, hz⟩
    induction z using Quotient.inductionOn with
    | h J =>
    obtain ⟨h, hh, e⟩ := Quotient.exact hz
    -- `J = h⁻¹ I h`; find `x^n ∈ I ∩ H` with `ξ(x^n) = ξ(h)`
    have hxv : ∀ n : ℕ, ξv H ξ (x ^ n) = n • ξv H ξ x := by
      intro n
      induction n with
      | zero =>
        rw [pow_zero, zero_smul, ξv_of_mem H.one_mem]
        exact ξ.map_zero
      | succ n ih =>
        rw [pow_succ, ξv_mul (H.pow_mem hxH n) hxH, ih, succ_nsmul]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n • ξv H ξ x = -ξv H ξ h := by
      refine ⟨((-ξv H ξ h) / ξv H ξ x).val, ?_⟩
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hx]
    have hxn : conjSub (x ^ n) (I : Subgroup Δ) = I := by
      ext y
      rw [mem_conjSub_iff]
      have hxn' := (I : Subgroup Δ).pow_mem hxI n
      constructor
      · intro hy
        have := (I : Subgroup Δ).mul_mem ((I : Subgroup Δ).mul_mem hxn' hy)
          ((I : Subgroup Δ).inv_mem hxn')
        simpa [mul_assoc] using this
      · intro hy
        exact (I : Subgroup Δ).mul_mem ((I : Subgroup Δ).mul_mem
          ((I : Subgroup Δ).inv_mem hxn') hy) hxn'
    refine Quotient.sound ⟨x ^ n * h, mem_kerSub_iff.2 ⟨H.mul_mem (H.pow_mem hxH n) hh, ?_⟩, ?_⟩
    · rw [ξv_mul (H.pow_mem hxH n) hh, hxv, hn, neg_add_cancel]
    · rw [conjSub_mul, show conjSub h (J : Subgroup Δ) = I from e, hxn]
  exact fun a b ↦ Subtype.ext ((key a).trans (key b).symm)

open Classical in
/-- The fibre of `cusps(ker ξ) → cusps(H)` over a cusp `y` of `H` has `1` element if `y` is
ramified in `ξ` and `p` elements otherwise. -/
lemma card_fiber [Fact p.Prime] (hS : ConjStable S)
    (hN : ∀ I ∈ S, ∀ g : Δ, conjSub g I = I → g ∈ I) (hξ : Function.Surjective ξ)
    (y : CuspQuot S H) :
    Nat.card {z : CuspQuot S (kerSub H ξ) // cuspMap S (kerSub_le H ξ) z = y} =
      if CuspRam H ξ S y then 1 else p := by
  classical
  obtain ⟨I, rfl⟩ := Quotient.exists_rep y
  change Nat.card (Fib H ξ I) = if IsRam H ξ I then 1 else p
  by_cases h : IsRam H ξ I
  · rw [if_pos h]
    exact card_fib_of_ram H ξ I h
  · rw [if_neg h]
    exact card_fib_of_not_ram H ξ hS hN hξ I h

open Classical in
/-- **Cusp count of a cyclic cover of prime degree** (G1):
`r(ker ξ) + (p - 1) · #{cusps of H ramified in ξ} = p · r(H)`. -/
theorem cuspCount_ker_add [Fact p.Prime] (hS : ConjStable S)
    (hN : ∀ I ∈ S, ∀ g : Δ, conjSub g I = I → g ∈ I) (hξ : Function.Surjective ξ)
    [Finite (CuspQuot S H)] :
    cuspCount S (kerSub H ξ) + (p - 1) * ramCusps H ξ S = p * cuspCount S H := by
  classical
  have := Fintype.ofFinite (CuspQuot S H)
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hfin : ∀ y : CuspQuot S H,
      Finite {z : CuspQuot S (kerSub H ξ) // cuspMap S (kerSub_le H ξ) z = y} := by
    intro y
    apply Nat.finite_of_card_ne_zero
    rw [card_fiber H ξ hS hN hξ y]
    by_cases h : CuspRam H ξ S y
    · rw [if_pos h]; exact one_ne_zero
    · rw [if_neg h]; exact (Fact.out : p.Prime).ne_zero
  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv (cuspMap S (kerSub_le H ξ)))
  rw [Nat.card_sigma] at hsig
  simp_rw [card_fiber H ξ hS hN hξ] at hsig
  unfold cuspCount ramCusps
  rw [← hsig, Nat.card_eq_fintype_card (α := CuspQuot S H), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul, mul_one]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun y : CuspQuot S H ↦ CuspRam H ξ S y)
  rw [Finset.card_univ] at hsplit
  rw [← hsplit]
  set a := (Finset.univ.filter fun y : CuspQuot S H ↦ CuspRam H ξ S y).card
  set b := (Finset.univ.filter fun y : CuspQuot S H ↦ ¬ CuspRam H ξ S y).card
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- The number of cusps ramified in `ξ` is determined by the cusp counts. -/
theorem ramCusps_eq_of_cuspCount_eq [Fact p.Prime] {Δ' : Type*} [Group Δ']
    {S' : Set (Subgroup Δ')} {H' : Subgroup Δ'} {ξ' : Additive H' →+ ZMod p}
    (hS : ConjStable S) (hN : ∀ I ∈ S, ∀ g : Δ, conjSub g I = I → g ∈ I)
    (hξ : Function.Surjective ξ) [Finite (CuspQuot S H)]
    (hS' : ConjStable S') (hN' : ∀ I ∈ S', ∀ g : Δ', conjSub g I = I → g ∈ I)
    (hξ' : Function.Surjective ξ') [Finite (CuspQuot S' H')]
    (h1 : cuspCount S H = cuspCount S' H')
    (h2 : cuspCount S (kerSub H ξ) = cuspCount S' (kerSub H' ξ')) :
    ramCusps H ξ S = ramCusps H' ξ' S' := by
  have e := cuspCount_ker_add H ξ hS hN hξ
  have e' := cuspCount_ker_add H' ξ' hS' hN' hξ'
  rw [h1, h2] at e
  have hp0 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  exact Nat.eq_of_mul_eq_mul_left hp0 (by omega)

end Ker

end CurvesJacobian.CuspChar
