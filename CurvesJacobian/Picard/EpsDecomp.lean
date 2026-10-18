/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CechBaseChange

/-!
# Sections over a free rank-two base change

This file is generic. Let `B` be an `A`-algebra which is free with basis `1, e` (e.g. the dual
numbers `A[ε]`). Then every element of `B ⊗_A R` is uniquely `1 ⊗ r₀ + e ⊗ r₁`
(`EpsDecomp.tensor_decomp`). For schemes: let `T → S` be affine with `Γ(T) = Γ(S) ⊕ Γ(S) e`
and `X` over `S`; for an affine open `W ⊆ X` with preimage `W_T ⊆ X_T`, every section of
`𝒪_{X_T}` over `W_T` is uniquely `p^♯ a + p^♯ b · e` with `a, b ∈ Γ(X, W)`
(`EpsDecomp.exists_eq`, `EpsDecomp.eq_zero_of_eq_zero`): `Γ(W_T) = Γ(T) ⊗_{Γ(S)} Γ(W)`
(`CurvesJacobian.Cech.isPushout_sections`).
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.EpsDecomp

section Algebra

variable {A B R : Type*} [CommRing A] [CommRing B] [CommRing R] [Algebra A B] [Algebra A R]
  (e : B)

/-- **Tensor products with a free algebra of rank two.** -/
theorem tensor_decomp
    (hB : ∀ b : B, ∃ a₀ a₁ : A, b = algebraMap A B a₀ + algebraMap A B a₁ * e)
    (hB' : ∀ a₀ a₁ : A, algebraMap A B a₀ + algebraMap A B a₁ * e = 0 → a₀ = 0 ∧ a₁ = 0) :
    (∀ z : B ⊗[A] R, ∃ r₀ r₁ : R, z = (1 : B) ⊗ₜ r₀ + e ⊗ₜ r₁) ∧
      ∀ r₀ r₁ : R, (1 : B) ⊗ₜ[A] r₀ + e ⊗ₜ r₁ = 0 → r₀ = 0 ∧ r₁ = 0 := by
  let L : A × A →ₗ[A] B := (Algebra.linearMap A B).coprod (LinearMap.toSpanSingleton A B e)
  have hL : ∀ a₀ a₁ : A, L (a₀, a₁) = algebraMap A B a₀ + algebraMap A B a₁ * e := by
    intro a₀ a₁
    simp [L, Algebra.smul_def]
  have hbij : Function.Bijective L := by
    refine ⟨fun p q hpq ↦ ?_, fun b ↦ ?_⟩
    · have h0 : L (p - q) = 0 := by rw [map_sub, hpq, sub_self]
      obtain ⟨h1, h2⟩ := hB' (p - q).1 (p - q).2 (by rw [← hL]; exact h0)
      exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
    · obtain ⟨a₀, a₁, rfl⟩ := hB b
      exact ⟨(a₀, a₁), hL a₀ a₁⟩
  let E := LinearEquiv.ofBijective L hbij
  have hE1 : E.symm 1 = (1, 0) := by
    rw [LinearEquiv.symm_apply_eq]
    change (1 : B) = L (1, 0)
    rw [hL]; simp
  have hEe : E.symm e = (0, 1) := by
    rw [LinearEquiv.symm_apply_eq]
    change e = L (0, 1)
    rw [hL]; simp
  let φ : (A × A →ₗ[A] A) → (B ⊗[A] R →ₗ[A] R) := fun c ↦
    (TensorProduct.lid A R).toLinearMap ∘ₗ ((c ∘ₗ E.symm.toLinearMap).rTensor R)
  have hφ : ∀ (c : A × A →ₗ[A] A) (b : B) (r : R), φ c (b ⊗ₜ r) = c (E.symm b) • r := by
    intro c b r
    simp [φ]
  refine ⟨fun z ↦ ?_, fun r₀ r₁ h ↦ ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul b r =>
      obtain ⟨a₀, a₁, rfl⟩ := hB b
      refine ⟨a₀ • r, a₁ • r, ?_⟩
      rw [add_tmul, ← Algebra.smul_def, ← smul_tmul, Algebra.algebraMap_eq_smul_one,
        smul_tmul, smul_tmul]
    | add z z' hz hz' =>
      obtain ⟨r₀, r₁, rfl⟩ := hz
      obtain ⟨r₀', r₁', rfl⟩ := hz'
      exact ⟨r₀ + r₀', r₁ + r₁', by rw [tmul_add, tmul_add]; abel⟩
  · have h0 := congrArg (φ (LinearMap.fst A A A)) h
    have h1 := congrArg (φ (LinearMap.snd A A A)) h
    simp only [map_add, hφ, hE1, hEe, LinearMap.fst_apply, LinearMap.snd_apply, one_smul,
      zero_smul, add_zero, zero_add, map_zero] at h0 h1
    exact ⟨h0, h1⟩

end Algebra

section Scheme

variable {S X T : Scheme.{u}} [IsAffine S] [IsAffine T] [X.Over S] [T.Over S]

omit [IsAffine S] [IsAffine T] in
lemma appLE_top_apply (a : Γ(S, ⊤)) :
    (T ↘ S).appLE ⊤ ⊤ (by simp) a = (T ↘ S).appTop a :=
  congrArg (fun φ ↦ φ a) (Scheme.Hom.appLE_eq_app (f := T ↘ S) (U := ⊤))

variable (e : Γ(T, ⊤))
  (hB : ∀ b : Γ(T, ⊤), ∃ a₀ a₁ : Γ(S, ⊤), b = (T ↘ S).appTop a₀ + (T ↘ S).appTop a₁ * e)
  (hB' : ∀ a₀ a₁ : Γ(S, ⊤), (T ↘ S).appTop a₀ + (T ↘ S).appTop a₁ * e = 0 → a₀ = 0 ∧ a₁ = 0)
  {W : X.Opens} (hW : IsAffineOpen W) {W' : (pullback (X ↘ S) (T ↘ S)).Opens}
  (hW' : W' = pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ W)

include hB hB' hW in
/-- **Sections over `W_T` decompose**: `z = p^♯ a + p^♯ b · e`. -/
theorem exists_eq (z : Γ(pullback (X ↘ S) (T ↘ S), W')) : ∃ a b : Γ(X, W),
    z = (pullback.fst (X ↘ S) (T ↘ S)).appLE W W' hW'.le a +
      (pullback.fst (X ↘ S) (T ↘ S)).appLE W W' hW'.le b *
        (pullback.snd (X ↘ S) (T ↘ S)).appLE ⊤ W' (by simp) e := by
  have hP := Cech.isPushout_sections (S := S) (X := X) (T := T) W hW W' hW'
  letI := ((T ↘ S).appLE ⊤ ⊤ (by simp)).hom.toAlgebra
  letI := ((X ↘ S).appLE ⊤ W (by simp)).hom.toAlgebra
  obtain ⟨H, -⟩ := tensor_decomp (R := Γ(X, W)) e
    (fun b ↦ by
      obtain ⟨a₀, a₁, h⟩ := hB b
      refine ⟨a₀, a₁, ?_⟩
      change b = (T ↘ S).appLE ⊤ ⊤ _ a₀ + (T ↘ S).appLE ⊤ ⊤ _ a₁ * e
      rw [appLE_top_apply, appLE_top_apply]
      exact h)
    (fun a₀ a₁ h ↦ by
      refine hB' a₀ a₁ ?_
      change (T ↘ S).appLE ⊤ ⊤ _ a₀ + (T ↘ S).appLE ⊤ ⊤ _ a₁ * e = 0 at h
      rwa [appLE_top_apply, appLE_top_apply] at h)
  obtain ⟨w, rfl⟩ := (pushoutTensorEquiv hP).surjective z
  obtain ⟨r₀, r₁, rfl⟩ := H w
  refine ⟨r₀, r₁, ?_⟩
  rw [map_add, pushoutTensorEquiv_tmul, pushoutTensorEquiv_tmul, map_one, one_mul, mul_comm]

include hB hB' hW in
/-- **Uniqueness of the decomposition.** -/
theorem eq_zero_of_eq_zero (a b : Γ(X, W))
    (h : (pullback.fst (X ↘ S) (T ↘ S)).appLE W W' hW'.le a +
      (pullback.fst (X ↘ S) (T ↘ S)).appLE W W' hW'.le b *
        (pullback.snd (X ↘ S) (T ↘ S)).appLE ⊤ W' (by simp) e = 0) :
    a = 0 ∧ b = 0 := by
  have hP := Cech.isPushout_sections (S := S) (X := X) (T := T) W hW W' hW'
  letI := ((T ↘ S).appLE ⊤ ⊤ (by simp)).hom.toAlgebra
  letI := ((X ↘ S).appLE ⊤ W (by simp)).hom.toAlgebra
  obtain ⟨-, H⟩ := tensor_decomp (R := Γ(X, W)) e
    (fun b ↦ by
      obtain ⟨a₀, a₁, h⟩ := hB b
      refine ⟨a₀, a₁, ?_⟩
      change b = (T ↘ S).appLE ⊤ ⊤ _ a₀ + (T ↘ S).appLE ⊤ ⊤ _ a₁ * e
      rw [appLE_top_apply, appLE_top_apply]
      exact h)
    (fun a₀ a₁ h ↦ by
      refine hB' a₀ a₁ ?_
      change (T ↘ S).appLE ⊤ ⊤ _ a₀ + (T ↘ S).appLE ⊤ ⊤ _ a₁ * e = 0 at h
      rwa [appLE_top_apply, appLE_top_apply] at h)
  refine H a b ((pushoutTensorEquiv hP).injective ?_)
  rw [map_add, pushoutTensorEquiv_tmul, pushoutTensorEquiv_tmul, map_one, one_mul, mul_comm,
    map_zero]
  exact h

end Scheme

end CurvesJacobian.EpsDecomp
