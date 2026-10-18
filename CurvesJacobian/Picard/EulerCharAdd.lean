/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Additivity of the Euler characteristic of two-term complexes

For a short exact sequence of two-term complexes `dᵢ : Xᵢ → Yᵢ` of vector spaces over a field
(exact rows `0 → X₁ → X₂ → X₃ → 0`, `0 → Y₁ → Y₂ → Y₃ → 0`) whose kernels and cokernels are
finite-dimensional, the Euler characteristics `χ(dᵢ) = dim ker dᵢ − dim coker dᵢ` satisfy
`χ(d₂) = χ(d₁) + χ(d₃)` (`CurvesJacobian.TwoTerm.chi_add`). The terms `Xᵢ`, `Yᵢ` may be
infinite-dimensional (they are rings of sections over affine charts); the proof uses the snake
lemma (`Mathlib.Algebra.Module.SnakeLemma`) and counts dimensions along the six-term exact
sequence `0 → ker d₁ → ker d₂ → ker d₃ → coker d₁ → coker d₂ → coker d₃ → 0`.

This is the additivity of `χ` used for the degree of line bundles on curves
(`χ(L(x)) = χ(L) + 1`, the input to the decomposition `Pic = ∐ Pic^d` of Stacks,
Lemma 44.6.7, Tag 0BA0, where degrees are defined by `χ = d + 1 − g`).
-/

open LinearMap Function Module

namespace CurvesJacobian.TwoTerm

variable {F : Type*} [Field F] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*}
  [AddCommGroup X₁] [Module F X₁] [AddCommGroup X₂] [Module F X₂] [AddCommGroup X₃] [Module F X₃]
  [AddCommGroup Y₁] [Module F Y₁] [AddCommGroup Y₂] [Module F Y₂] [AddCommGroup Y₃] [Module F Y₃]
  {d₁ : X₁ →ₗ[F] Y₁} {d₂ : X₂ →ₗ[F] Y₂} {d₃ : X₃ →ₗ[F] Y₃}
  {a₁ : X₁ →ₗ[F] X₂} {a₂ : X₂ →ₗ[F] X₃} {b₁ : Y₁ →ₗ[F] Y₂} {b₂ : Y₂ →ₗ[F] Y₃}

/-- **Additivity of the Euler characteristic** of two-term complexes over a field (snake
lemma). -/
theorem chi_add (ha : Exact a₁ a₂) (ha₁ : Injective a₁) (ha₂ : Surjective a₂)
    (hb : Exact b₁ b₂) (hb₁ : Injective b₁) (hb₂ : Surjective b₂)
    (h₁ : b₁ ∘ₗ d₁ = d₂ ∘ₗ a₁) (h₂ : b₂ ∘ₗ d₂ = d₃ ∘ₗ a₂)
    [FiniteDimensional F (ker d₁)] [FiniteDimensional F (ker d₂)]
    [FiniteDimensional F (ker d₃)] [FiniteDimensional F (Y₁ ⧸ range d₁)]
    [FiniteDimensional F (Y₂ ⧸ range d₂)] [FiniteDimensional F (Y₃ ⧸ range d₃)] :
    (finrank F (ker d₂) : ℤ) - finrank F (Y₂ ⧸ range d₂) =
      ((finrank F (ker d₁) : ℤ) - finrank F (Y₁ ⧸ range d₁)) +
        ((finrank F (ker d₃) : ℤ) - finrank F (Y₃ ⧸ range d₃)) := by
  -- the maps on kernels and cokernels
  have m₁ : ∀ x ∈ ker d₁, a₁ x ∈ ker d₂ := fun x hx ↦ by
    rw [mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply d₂, ← h₁, LinearMap.comp_apply, hx, map_zero]
  have m₂ : ∀ x ∈ ker d₂, a₂ x ∈ ker d₃ := fun x hx ↦ by
    rw [mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply d₃, ← h₂, LinearMap.comp_apply, hx, map_zero]
  let φ₁ : ker d₁ →ₗ[F] ker d₂ := a₁.restrict m₁
  let φ₂ : ker d₂ →ₗ[F] ker d₃ := a₂.restrict m₂
  have n₁ : range d₁ ≤ (range d₂).comap b₁ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨a₁ x, (LinearMap.congr_fun h₁ x).symm⟩
  have n₂ : range d₂ ≤ (range d₃).comap b₂ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨a₂ x, (LinearMap.congr_fun h₂ x).symm⟩
  let ψ₁ := (range d₁).mapQ (range d₂) b₁ n₁
  let ψ₂ := (range d₂).mapQ (range d₃) b₂ n₂
  let δ := SnakeLemma.δ' d₁ d₂ d₃ a₁ a₂ ha b₁ b₂ hb h₁ h₂ (ker d₃).subtype
    (exact_subtype_ker_map d₃) (range d₁).mkQ (exact_map_mkQ_range d₁) ha₂ hb₁
  -- exactness of `0 → ker d₁ → ker d₂ → ker d₃ → coker d₁ → coker d₂ → coker d₃ → 0`
  have e₁ : Injective φ₁ := fun x y h ↦ Subtype.ext (ha₁ (congrArg Subtype.val h))
  have e₂ : Exact φ₁ φ₂ := by
    refine exact_of_comp_of_mem_range
      (LinearMap.ext fun x ↦ Subtype.ext (ha.apply_apply_eq_zero x.1)) fun x hx ↦ ?_
    obtain ⟨y, hy⟩ := (ha x.1).mp (congrArg Subtype.val hx)
    have hy0 : d₁ y = 0 := by
      apply hb₁
      rw [map_zero, ← LinearMap.comp_apply b₁, h₁, LinearMap.comp_apply, hy]
      exact x.2
    exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩
  have e₃ : Exact φ₂ δ :=
    SnakeLemma.exact_δ'_right d₁ d₂ d₃ a₁ a₂ ha b₁ b₂ hb h₁ h₂ (ker d₂).subtype
      (exact_subtype_ker_map d₂) (ker d₃).subtype (exact_subtype_ker_map d₃) (range d₁).mkQ
      (exact_map_mkQ_range d₁) ha₂ hb₁ φ₂ rfl (ker d₃).injective_subtype
  have e₄ : Exact δ ψ₁ :=
    SnakeLemma.exact_δ'_left d₁ d₂ d₃ a₁ a₂ ha b₁ b₂ hb h₁ h₂ (ker d₃).subtype
      (exact_subtype_ker_map d₃) (range d₁).mkQ (exact_map_mkQ_range d₁) (range d₂).mkQ
      (exact_map_mkQ_range d₂) ha₂ hb₁ ψ₁ (Submodule.mapQ_mkQ _ _ _) (Submodule.mkQ_surjective _)
  have e₅ : Exact ψ₁ ψ₂ := by
    refine exact_of_comp_of_mem_range (LinearMap.ext fun c ↦ ?_) fun c hc ↦ ?_
    · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ c
      change (range d₃).mkQ (b₂ (b₁ y)) = 0
      rw [hb.apply_apply_eq_zero, map_zero]
    · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ c
      change (range d₃).mkQ (b₂ y) = 0 at hc
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
      obtain ⟨x₃, hx₃⟩ := hc
      obtain ⟨x₂, rfl⟩ := ha₂ x₃
      have hz : b₂ (y - d₂ x₂) = 0 := by
        rw [map_sub, ← hx₃, ← LinearMap.comp_apply b₂, h₂, LinearMap.comp_apply, sub_self]
      obtain ⟨z, hz'⟩ := (hb _).mp hz
      refine ⟨(range d₁).mkQ z, ?_⟩
      change (range d₂).mkQ (b₁ z) = (range d₂).mkQ y
      rw [hz', map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x₂, rfl⟩
  have e₆ : Surjective ψ₂ := by
    intro c
    obtain ⟨y₃, rfl⟩ := Submodule.mkQ_surjective _ c
    obtain ⟨y₂, rfl⟩ := hb₂ y₃
    exact ⟨(range d₂).mkQ y₂, rfl⟩
  -- counting dimensions
  have r₂ := LinearMap.finrank_range_add_finrank_ker φ₂
  have r₃ := LinearMap.finrank_range_add_finrank_ker δ
  have r₄ := LinearMap.finrank_range_add_finrank_ker ψ₁
  have r₅ := LinearMap.finrank_range_add_finrank_ker ψ₂
  have k₁ := LinearMap.finrank_range_of_inj e₁
  rw [e₂.linearMap_ker_eq] at r₂
  rw [e₃.linearMap_ker_eq] at r₃
  rw [e₄.linearMap_ker_eq] at r₄
  rw [e₅.linearMap_ker_eq, LinearMap.range_eq_top.mpr e₆, finrank_top] at r₅
  omega

end CurvesJacobian.TwoTerm
