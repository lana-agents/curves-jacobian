/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weight exponents and the ratio argument (step B4 of [AbsTopI] Lemma 4.5 (v))

For an open subgroup `H` of the geometric fundamental group `Δ` of a hyperbolic curve `U`
(cover `U_H → U` of degree `d_H`, with `r_H` cusps), the determinant of the Galois action on
`Hom(H, ℤ/l^k)` squares to `χ^{-e_H}` on an open subgroup, `e_H = d_H · (2g - 2 + r) + r_H`
(Weil pairing, cusp residues and Riemann–Hurwitz; see `MR3-plan.md`, route (B)). Transport along
`Π_U ≃ₜ* Π_{U'}` over `G_K ≃ₜ* G_{K'}` yields `χ^{e_H} = ρ^{e'_H}` on open subgroups, where
`ρ = χ' ∘ ψ`. This file contains the two formal steps that turn these identities into equal cusp
counts:

* `CurvesJacobian.CuspChar.mul_eq_mul_of_pow_eq`: if `χ^a = ρ^{a'}` on `A` and `χ^b = ρ^{b'}` on
  `B`, and `χ` has no nontrivial exponent on `A ⊓ B` (`χ` has infinite image on open subgroups),
  then `a b' = b a'`;
* `CurvesJacobian.CuspChar.eq_of_mul_eq_mul`: if `e_H = d_H χ₀ + r_H`, `e'_H = d_H χ₀ + r'_H`,
  `e_H e'_K = e_K e'_H` for all `H, K`, and on both sides there are covers in which every cusp
  ramifies to order `≥ m` for every `m` (`r_H m ≤ C d_H`), then `r_H = r'_H` for all `H`.
-/

namespace CurvesJacobian.CuspChar

section Exponent

variable {G : Type*} [Group G] {ι : Type*} {M : ι → Type*} [∀ k, CommGroup (M k)]

/-- **Equal ratios of exponents.** If `χ^a = ρ^{a'}` on `A` and `χ^b = ρ^{b'}` on `B` (at every
level `k`), and `χ` has no nontrivial exponent on `A ⊓ B`, then `a b' = b a'`. -/
lemma mul_eq_mul_of_pow_eq (χ ρ : ∀ k, G →* M k) {A B : Subgroup G} {a a' b b' : ℕ}
    (ha : ∀ σ ∈ A, ∀ k, χ k σ ^ a = ρ k σ ^ a') (hb : ∀ σ ∈ B, ∀ k, χ k σ ^ b = ρ k σ ^ b')
    (hinf : ∀ N : ℕ, (∀ σ ∈ A ⊓ B, ∀ k, χ k σ ^ N = 1) → N = 0) : a * b' = b * a' := by
  have key : ∀ σ ∈ A ⊓ B, ∀ k, χ k σ ^ (a * b') = χ k σ ^ (b * a') := by
    intro σ hσ k
    rw [pow_mul, ha σ hσ.1 k, ← pow_mul, mul_comm a' b', pow_mul, ← hb σ hσ.2 k, ← pow_mul]
  have h1 : a * b' - b * a' = 0 := hinf _ fun σ hσ k ↦ by
    rcases le_total (a * b') (b * a') with h | h
    · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    · have := key σ hσ k
      rw [← Nat.sub_add_cancel h, pow_add] at this
      exact mul_eq_right.1 this
  have h2 : b * a' - a * b' = 0 := hinf _ fun σ hσ k ↦ by
    rcases le_total (b * a') (a * b') with h | h
    · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    · have := (key σ hσ k).symm
      rw [← Nat.sub_add_cancel h, pow_add] at this
      exact mul_eq_right.1 this
  omega

end Exponent

section Ratio

variable {H : Type*}

/-- One half of the ratio argument: covers with large ramification on the first side force
`e_{h₀} ≤ e'_{h₀}`. -/
lemma le_of_mul_eq_mul (e e' d r r' : H → ℕ) {χ₀ : ℕ} (hχ₀ : 0 < χ₀)
    (he : ∀ h, e h = d h * χ₀ + r h) (he' : ∀ h, e' h = d h * χ₀ + r' h)
    (hmul : ∀ h k, e h * e' k = e k * e' h)
    (hfam : ∃ C, ∀ m : ℕ, ∃ h, r h * m ≤ C * d h ∧ 0 < d h) (h₀ : H) : e h₀ ≤ e' h₀ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hC⟩ := hfam
  obtain ⟨h, hrm, hd⟩ := hC (C * e' h₀ + 1)
  set m := C * e' h₀ + 1
  have hm := hmul h₀ h
  -- `e h₀ · d χ₀ ≤ e h₀ · e' h = e h · e' h₀ = (d χ₀ + r h) e' h₀`
  have h1 : e h₀ * (d h * χ₀) ≤ (d h * χ₀ + r h) * e' h₀ := by
    rw [← he h, ← hm, he' h]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  -- multiply by `m` and use `r h · m ≤ C d`
  have h2 : e h₀ * (d h * χ₀) * m ≤ (d h * χ₀ * m + C * d h) * e' h₀ := by
    calc e h₀ * (d h * χ₀) * m ≤ (d h * χ₀ + r h) * e' h₀ * m := Nat.mul_le_mul_right _ h1
      _ = (d h * χ₀ * m + r h * m) * e' h₀ := by ring
      _ ≤ (d h * χ₀ * m + C * d h) * e' h₀ :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left hrm _)
  -- cancel `d h`
  have h3 : e h₀ * χ₀ * m ≤ (χ₀ * m + C) * e' h₀ := by
    have : d h * (e h₀ * χ₀ * m) ≤ d h * ((χ₀ * m + C) * e' h₀) := by
      calc d h * (e h₀ * χ₀ * m) = e h₀ * (d h * χ₀) * m := by ring
        _ ≤ (d h * χ₀ * m + C * d h) * e' h₀ := h2
        _ = d h * ((χ₀ * m + C) * e' h₀) := by ring
    exact Nat.le_of_mul_le_mul_left this hd
  -- with `e h₀ ≥ e' h₀ + 1`: `χ₀ m ≤ C e' h₀ < m`
  have h4 : (e' h₀ + 1) * χ₀ * m ≤ (χ₀ * m + C) * e' h₀ :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlt)) h3
  have h5 : χ₀ * m ≤ C * e' h₀ := by nlinarith
  have h6 : m ≤ χ₀ * m := Nat.le_mul_of_pos_left m hχ₀
  omega

/-- **The ratio argument** (B4): equal exponent ratios plus covers with large ramification on
both sides give equal cusp counts. -/
theorem eq_of_mul_eq_mul (e e' d r r' : H → ℕ) {χ₀ : ℕ} (hχ₀ : 0 < χ₀)
    (he : ∀ h, e h = d h * χ₀ + r h) (he' : ∀ h, e' h = d h * χ₀ + r' h)
    (hmul : ∀ h k, e h * e' k = e k * e' h)
    (hfam : ∃ C, ∀ m : ℕ, ∃ h, r h * m ≤ C * d h ∧ 0 < d h)
    (hfam' : ∃ C, ∀ m : ℕ, ∃ h, r' h * m ≤ C * d h ∧ 0 < d h) (h : H) : r h = r' h := by
  obtain ⟨C, hC⟩ := hfam
  obtain ⟨h₀, -, hd₀⟩ := hC 0
  have hle := le_of_mul_eq_mul e e' d r r' hχ₀ he he' hmul ⟨C, hC⟩ h₀
  have hge := le_of_mul_eq_mul e' e d r' r hχ₀ he' he (fun h k ↦ by
    rw [mul_comm, hmul k h, mul_comm]) hfam' h₀
  have heq : e h₀ = e' h₀ := le_antisymm hle hge
  have hpos : 0 < e h₀ := by
    rw [he h₀]
    exact Nat.add_pos_left (Nat.mul_pos hd₀ hχ₀) _
  have hm := hmul h h₀
  rw [heq] at hm
  have : e h = e' h := Nat.eq_of_mul_eq_mul_right (heq ▸ hpos) (by rw [hm, mul_comm])
  rw [he, he'] at this
  omega

end Ratio

end CurvesJacobian.CuspChar
