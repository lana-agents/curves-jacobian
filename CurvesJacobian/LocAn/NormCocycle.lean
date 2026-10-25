/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The norm cocycle splitting a Kummer cup product ((P6), step 3)

Abelian form of McCallum–Sharifi, arXiv math/0202161v3, Lemmas 2.2–2.3 / Thm 2.4
(`lit/dl/jac-p6/ms/ms.txt` l.291–458; see JAC-plan "JAC agent 29"). Let a group `G` act on a
field `Ω`, let `g : ℕ → Ω` be `n`-periodic and non-vanishing (in the application `g j = σ^j γ`
for a generator `σ` of a cyclic extension `L/K` of degree `n` and `γ ∈ L`), and let `τ` act on
the `g j` by the shift `m τ < n`, `m (τ τ') ≡ m τ + m τ' (mod n)`. Put `ρ m = ∏_{j<m} g j` (so
`ρ n = N γ`), let `β` be an `n`-th root of `ρ n` with `τ β = ζ^{l τ} β`, and

* `lam τ = β^{m τ} / ρ (m τ)`, `normF = ∏_{i<n} ρ i`.

Then **`lam_cocycle`**: `lam τ · τ(lam τ') / lam (τ τ') = ζ^{l τ · m τ'}` — the coboundary of `lam`
is the cup-product cocycle `χ_b ∪ ψ_a` — and **`smul_normF`**: `τ(F) = F · (lam τ)^n`, i.e. `F` is
a Kummer representative whose Chern cocycle (with the roots `lam τ`) is that cup product.
-/

open Finset

namespace CurvesJacobian.LocAn.NormCocycle

variable {G Ω : Type*} [Group G] [Field Ω] [MulSemiringAction G Ω]

/-- `ρ m = ∏_{j<m} g j`. -/
def rho (g : ℕ → Ω) (m : ℕ) : Ω := ∏ j ∈ range m, g j

theorem rho_add (g : ℕ → Ω) (a b : ℕ) : rho g (a + b) = rho g a * ∏ j ∈ range b, g (a + j) :=
  prod_range_add g a b

theorem rho_ne_zero {g : ℕ → Ω} (hg : ∀ j, g j ≠ 0) (m : ℕ) : rho g m ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ => hg j

variable {n : ℕ} {g : ℕ → Ω}

theorem rho_add_n (hper : ∀ j, g (j + n) = g j) (m : ℕ) : rho g (m + n) = rho g m * rho g n := by
  rw [add_comm, rho_add, mul_comm]
  congr 1
  exact prod_congr rfl fun j _ => by rw [add_comm, hper]

variable {m : G → ℕ} (hg : ∀ j, g j ≠ 0) (hact : ∀ (τ : G) (j : ℕ), τ • g j = g (j + m τ))

theorem smul_prod_range (τ : G) (k : ℕ) (f : ℕ → Ω) :
    τ • ∏ j ∈ range k, f j = ∏ j ∈ range k, τ • f j :=
  map_prod (MulSemiringAction.toRingHom G Ω τ) f (range k)

include hg hact in
theorem smul_rho (τ : G) (k : ℕ) : τ • rho g k = rho g (m τ + k) / rho g (m τ) := by
  rw [eq_div_iff (rho_ne_zero hg _), rho_add, mul_comm]
  congr 1
  rw [rho, smul_prod_range]
  exact prod_congr rfl fun j _ => by rw [hact, add_comm]

variable (g m) in
/-- `λ_τ = β^{m τ} / ρ(m τ)`. -/
noncomputable def lam (β : Ω) (τ : G) : Ω := β ^ m τ / rho g (m τ)

variable (g n) in
/-- `F = ∏_{i<n} ρ i`. -/
noncomputable def normF : Ω := ∏ i ∈ range n, rho g i

variable {ζ β : Ω} {l : G → ℕ}

include hg hact in
/-- **The coboundary of `λ` is the cup-product cocycle** `(τ, τ') ↦ ζ^{l τ · m τ'}`. -/
theorem lam_cocycle (hper : ∀ j, g (j + n) = g j) (hβ : β ^ n = rho g n) (hβ0 : β ≠ 0)
    (hβτ : ∀ τ : G, τ • β = ζ ^ l τ * β)
    (hm : ∀ τ τ' : G, m τ + m τ' = m (τ * τ') ∨ m τ + m τ' = m (τ * τ') + n) (τ τ' : G) :
    lam g m β τ * τ • lam g m β τ' / lam g m β (τ * τ') = ζ ^ (l τ * m τ') := by
  have hρ := rho_ne_zero hg
  have hsβ : τ • β ^ m τ' = ζ ^ (l τ * m τ') * β ^ m τ' := by
    rw [smul_pow', hβτ, mul_pow, ← pow_mul]
  have key : lam g m β τ * τ • lam g m β τ' =
      ζ ^ (l τ * m τ') * (β ^ (m τ + m τ') / rho g (m τ + m τ')) := by
    simp only [lam]
    rw [smul_div₀', hsβ, smul_rho hg hact, pow_add]
    have := hρ (m τ)
    have := hρ (m τ + m τ')
    field_simp
  have hl : lam g m β (τ * τ') ≠ 0 := div_ne_zero (pow_ne_zero _ hβ0) (hρ _)
  rw [key, div_eq_iff hl]
  congr 1
  simp only [lam]
  rcases hm τ τ' with h | h
  · rw [h]
  · rw [h, rho_add_n hper, pow_add, hβ]
    have := hρ n
    have := hρ (m (τ * τ'))
    field_simp

include hg hact in
/-- `lam_cocycle` for an arbitrary multiplier: if `τ β = c τ · β`, the coboundary of `λ` is
`(τ, τ') ↦ (c τ)^{m τ'}`. -/
theorem lam_cocycle_of (hper : ∀ j, g (j + n) = g j) (hβ : β ^ n = rho g n) (hβ0 : β ≠ 0)
    {c : G → Ω} (hβτ : ∀ τ : G, τ • β = c τ * β)
    (hm : ∀ τ τ' : G, m τ + m τ' = m (τ * τ') ∨ m τ + m τ' = m (τ * τ') + n) (τ τ' : G) :
    lam g m β τ * τ • lam g m β τ' / lam g m β (τ * τ') = c τ ^ m τ' := by
  have hρ := rho_ne_zero hg
  have hsβ : τ • β ^ m τ' = c τ ^ m τ' * β ^ m τ' := by
    rw [smul_pow', hβτ, mul_pow]
  have key : lam g m β τ * τ • lam g m β τ' =
      c τ ^ m τ' * (β ^ (m τ + m τ') / rho g (m τ + m τ')) := by
    simp only [lam]
    rw [smul_div₀', hsβ, smul_rho hg hact, pow_add]
    have := hρ (m τ)
    have := hρ (m τ + m τ')
    field_simp
  have hl : lam g m β (τ * τ') ≠ 0 := div_ne_zero (pow_ne_zero _ hβ0) (hρ _)
  rw [key, div_eq_iff hl]
  congr 1
  simp only [lam]
  rcases hm τ τ' with h | h
  · rw [h]
  · rw [h, rho_add_n hper, pow_add, hβ]
    have := hρ n
    have := hρ (m (τ * τ'))
    field_simp

include hg hact in
/-- **`τ F = F · λ_τ^n`**: `F` is a Kummer representative with roots `λ_τ`. -/
theorem smul_normF (hper : ∀ j, g (j + n) = g j) (hβ : β ^ n = rho g n) (τ : G) :
    τ • normF n g = normF n g * lam g m β τ ^ n := by
  have hρ := rho_ne_zero hg
  -- `∏_{i<n} ρ(m + i) = F · ρ(n)^m`
  have hshift : ∀ k : ℕ, ∏ i ∈ range n, rho g (k + i) = normF n g * rho g n ^ k := by
    intro k
    induction k with
    | zero => simp [normF]
    | succ k ih =>
      have e : ∀ i, k + 1 + i = k + (i + 1) := fun i => by omega
      simp only [e]
      have h1 : (∏ i ∈ range n, rho g (k + (i + 1))) * rho g k =
          (∏ i ∈ range n, rho g (k + i)) * rho g (k + n) := by
        rw [← prod_range_succ (fun i => rho g (k + i)) n, prod_range_succ', add_zero]
      rw [rho_add_n hper, ih] at h1
      rw [pow_succ]
      have := hρ k
      field_simp at h1 ⊢
      linear_combination h1
  rw [normF, smul_prod_range]
  simp_rw [smul_rho hg hact]
  rw [prod_div_distrib, prod_const, card_range, ← normF, hshift, lam, div_pow, ← pow_mul,
    mul_comm (m τ) n, pow_mul, hβ]
  have := hρ (m τ)
  field_simp

end CurvesJacobian.LocAn.NormCocycle
