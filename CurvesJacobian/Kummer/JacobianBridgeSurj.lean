/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.DivisorPicSurj
import CurvesJacobian.Kummer.JacobianDivisible

/-!
# `Pic⁰` of the function field is the Jacobian; divisibility of `Pic⁰`

* `CurvesJacobian.exists_nsmul_eq_picZero`: for a curve `C/k` with a rational point and `κ ⊇ k`
  algebraically closed, `Pic⁰(K(C_κ))` is `n`-divisible for `n` invertible in `k` (transport
  `exists_nsmul_eq_jacPoints` along `jacBridgeEquiv`); `exists_nsmul_eq_picZero_of_charZero`.
* For the Galois model `F` of a curve `X/k` in characteristic `0`:
  **`CurvesJacobian.Kummer.jacPsi_surjective`**, the isomorphism
  **`CurvesJacobian.Kummer.jacPsiEquiv : Pic⁰(F k̄) ≃+ J(k̄)`**, and
  **`CurvesJacobian.Kummer.exists_nsmul_eq_jacPsi`**: `Pic⁰(F k̄)` is divisible.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian

section Divisible

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
  [IsCurveOver k C] (κ : Type u) [Field κ] [IsAlgClosed κ] [Algebra k κ]
  (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
include σ hσ

local notation "Sk" => Spec (CommRingCat.of k)
local notation "Cκ" => pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) κ)

/-- **`Pic⁰(K(C_κ))` is `n`-divisible** for `n` invertible in `k` (`C` with a rational point
`σ`, `κ ⊇ k` algebraically closed). -/
theorem exists_nsmul_eq_picZero {n : ℕ} (hn : (n : k) ≠ 0)
    (y : (Pic.deg κ (Cκ).functionField).ker) :
    ∃ x : (Pic.deg κ (Cκ).functionField).ker, n • x = y := by
  obtain ⟨z, hz⟩ := exists_nsmul_eq_jacPoints C σ hσ hn κ (jacBridgeEquiv C κ σ hσ y)
  refine ⟨(jacBridgeEquiv C κ σ hσ).symm z, (jacBridgeEquiv C κ σ hσ).injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply, hz]

/-- **`Pic⁰(K(C_κ))` is divisible in characteristic `0`.** -/
theorem exists_nsmul_eq_picZero_of_charZero [CharZero k] {n : ℕ} (hn : n ≠ 0)
    (y : (Pic.deg κ (Cκ).functionField).ker) :
    ∃ x : (Pic.deg κ (Cκ).functionField).ker, n • x = y :=
  exists_nsmul_eq_picZero C κ σ hσ (Nat.cast_ne_zero.mpr hn) y

end Divisible

namespace Kummer

open CurvesJacobian.Cusp

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

attribute [local instance] isFunctionField_F

/-- **The bridge `Pic⁰(F k̄) → J(k̄)` is surjective.** -/
theorem jacPsi_surjective : Function.Surjective (jacPsi k hτ σ hσ) := by
  intro y
  obtain ⟨x, rfl⟩ := jacBridge_surjective X (kbar k (FFClosure X)) σ hσ y
  refine ⟨⟨(picFFEquiv k hτ).symm x.1, ?_⟩, ?_⟩
  · rw [AddMonoidHom.mem_ker, ← deg_picFFEquiv k hτ, AddEquiv.apply_symm_apply]
    exact x.2
  · change jacBridge X (kbar k (FFClosure X)) σ hσ _ = _
    congr 1
    exact Subtype.ext ((picFFEquiv k hτ).apply_symm_apply x.1)

/-- **`Pic⁰(F k̄) ≃+ J(k̄)`** for the Galois model `F` of `X`. -/
def jacPsiEquiv :
    (Pic.deg (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))).ker ≃+
      jacPoints X σ hσ (kbar k (FFClosure X)) :=
  AddEquiv.ofBijective (jacPsi k hτ σ hσ) ⟨jacPsi_injective k hτ σ hσ, jacPsi_surjective k hτ σ hσ⟩

@[simp]
lemma jacPsiEquiv_apply
    (x : (Pic.deg (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))).ker) :
    jacPsiEquiv k hτ σ hσ x = jacPsi k hτ σ hσ x :=
  rfl

include σ hσ in
/-- **`Pic⁰(F k̄)` is divisible**: every degree-zero class is `n` times a degree-zero class,
`n ≥ 1`. -/
theorem exists_nsmul_eq_jacPsi {n : ℕ} (hn : n ≠ 0)
    (y : (Pic.deg (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))).ker) :
    ∃ x : (Pic.deg (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))).ker,
      n • x = y := by
  obtain ⟨z, hz⟩ := exists_nsmul_eq_jacPoints_of_charZero X σ hσ hn (kbar k (FFClosure X))
    (jacPsi k hτ σ hσ y)
  obtain ⟨x, rfl⟩ := jacPsi_surjective k hτ σ hσ z
  exact ⟨x, jacPsi_injective k hτ σ hσ ((map_nsmul (jacPsi k hτ σ hσ) n x).trans hz)⟩

end Kummer

end CurvesJacobian
