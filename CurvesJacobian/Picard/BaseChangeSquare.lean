/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change along a pushout square

Let `R₀ → R₀'` and `R₀ → A` be ring maps and `A' = A ⊗_{R₀} R₀'` (given by an `A`-linear
isomorphism `e : A ⊗_{R₀} R₀' ≃ A'`, `a ⊗ b ↦ a b`). If an `A'`-module `N` is the base change of
an `A`-module `M` along `A → A'` (`IsBaseChange A' θ`), then `N` is also the base change of `M`
along `R₀ → R₀'`: `R₀' ⊗_{R₀} M ≅ N`, `b ⊗ m ↦ b • θ m`
(`CurvesJacobian.bijective_liftBaseChange_of_isBaseChange`). This is the transitivity
`R₀' ⊗_{R₀} M ≅ (A ⊗_{R₀} R₀') ⊗_A M ≅ A' ⊗_A M` (Stacks, Lemma 10.12.7, Tag 00DE).
-/

open TensorProduct

namespace CurvesJacobian

variable {R₀ R₀' A A' : Type*} [CommRing R₀] [CommRing R₀'] [CommRing A] [CommRing A']
  [Algebra R₀ R₀'] [Algebra R₀ A] [Algebra A A'] [Algebra R₀' A']
  {M N : Type*} [AddCommGroup M] [Module A M] [Module R₀ M] [IsScalarTower R₀ A M]
  [AddCommGroup N] [Module A' N] [Module A N] [IsScalarTower A A' N] [Module R₀' N]
  [IsScalarTower R₀' A' N] [Module R₀ N] [IsScalarTower R₀ R₀' N] [IsScalarTower R₀ A N]

/-- The base change map `R₀' ⊗_{R₀} M → N`, `b ⊗ m ↦ b • θ m`. -/
noncomputable abbrev baseChangeMap (θ : M →ₗ[A] N) : R₀' ⊗[R₀] M →ₗ[R₀'] N :=
  (θ.restrictScalars R₀).liftBaseChange R₀'

lemma baseChangeMap_tmul (θ : M →ₗ[A] N) (b : R₀') (m : M) :
    baseChangeMap (R₀ := R₀) θ (b ⊗ₜ m) = b • θ m := by
  simp [baseChangeMap, LinearMap.liftBaseChange_tmul]

/-- If `A' = A ⊗_{R₀} R₀'` and `N = A' ⊗_A M`, then `N = R₀' ⊗_{R₀} M`. -/
theorem bijective_baseChangeMap (θ : M →ₗ[A] N) (hθ : IsBaseChange A' θ)
    (e : A ⊗[R₀] R₀' ≃ₗ[A] A')
    (he : ∀ (a : A) (b : R₀'), e (a ⊗ₜ b) = algebraMap A A' a * algebraMap R₀' A' b) :
    Function.Bijective (baseChangeMap (R₀ := R₀) (R₀' := R₀') θ) := by
  -- the chain `R₀' ⊗_{R₀} M ≃ M ⊗_{R₀} R₀' ≃ M ⊗_A (A ⊗_{R₀} R₀') ≃ (A ⊗_{R₀} R₀') ⊗_A M
  --   ≃ A' ⊗_A M ≃ N`, as additive equivalences
  let c₁ : R₀' ⊗[R₀] M ≃+ M ⊗[R₀] R₀' := (TensorProduct.comm R₀ R₀' M).toAddEquiv
  let c₂ : M ⊗[R₀] R₀' ≃+ M ⊗[A] (A ⊗[R₀] R₀') :=
    (AlgebraTensorModule.cancelBaseChange R₀ A A M R₀').symm.toAddEquiv
  let c₃ : M ⊗[A] (A ⊗[R₀] R₀') ≃+ (A ⊗[R₀] R₀') ⊗[A] M :=
    (TensorProduct.comm A M (A ⊗[R₀] R₀')).toAddEquiv
  let c₄ : (A ⊗[R₀] R₀') ⊗[A] M ≃+ A' ⊗[A] M := (LinearEquiv.rTensor M e).toAddEquiv
  let c₅ : A' ⊗[A] M ≃+ N := hθ.equiv.toAddEquiv.trans (AddEquiv.refl N)
  let Φ : R₀' ⊗[R₀] M ≃+ N := c₁.trans (c₂.trans (c₃.trans (c₄.trans c₅)))
  have hΦ : ∀ x, Φ x = baseChangeMap (R₀ := R₀) θ x := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b m =>
      rw [baseChangeMap_tmul]
      change hθ.equiv (LinearEquiv.rTensor M e (TensorProduct.comm A M _
        ((AlgebraTensorModule.cancelBaseChange R₀ A A M R₀').symm
          (TensorProduct.comm R₀ R₀' M (b ⊗ₜ m))))) = _
      rw [TensorProduct.comm_tmul, AlgebraTensorModule.cancelBaseChange_symm_tmul,
        TensorProduct.comm_tmul, LinearEquiv.rTensor_tmul, IsBaseChange.equiv_tmul, he, map_one,
        one_mul, algebraMap_smul]
  have : ⇑(baseChangeMap (R₀ := R₀) (R₀' := R₀') θ) = Φ := funext fun x ↦ (hΦ x).symm
  rw [this]
  exact Φ.bijective

end CurvesJacobian
