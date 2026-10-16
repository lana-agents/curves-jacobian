/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Kummer coverings `R → R[T]/(Tⁿ - u)`

Let `R` be a ring, `n ≥ 1` with `n` invertible in `R`, and `u ∈ Rˣ`. The algebra
`R[T]/(Tⁿ - u)` is

* standard étale (`CurvesJacobian.kummerPair`, `CurvesJacobian.etale_kummer`), because
  `T·(Tⁿ - u)' = n·Tⁿ = n·(Tⁿ - u) + n·u` exhibits `(Tⁿ - u)'` as a unit modulo `Tⁿ - u`;
* free of rank `n`, hence faithfully flat when `R` is nontrivial
  (`CurvesJacobian.faithfullyFlat_kummer`);
* and `u` becomes an `n`-th power in it (`CurvesJacobian.root_pow_kummer`).

This is the local input of the exactness of the **Kummer sequence**
`1 → μₙ → 𝔾ₘ →(·)ⁿ 𝔾ₘ → 1` on the (small) étale site of a scheme on which `n` is invertible
(Stacks, Lemma 03PK, whose proof uses exactly these étale coverings): every unit is étale-locally
an `n`-th power.
-/

open Polynomial

namespace CurvesJacobian

variable {R : Type*} [CommRing R]

/-- The Kummer polynomial `Tⁿ - u`. -/
noncomputable abbrev kummerPoly (n : ℕ) (u : R) : R[X] := X ^ n - C u

lemma monic_kummerPoly {n : ℕ} (hn : 0 < n) (u : R) : (kummerPoly n u).Monic :=
  monic_X_pow_sub_C u hn.ne'

/-- The standard étale pair `(Tⁿ - u, 1)`, for `n` and `u` units. -/
noncomputable def kummerPair {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) (u : Rˣ) :
    StandardEtalePair R where
  f := kummerPoly n (u : R)
  monic_f := monic_kummerPoly hn (u : R)
  g := 1
  cond := by
    obtain ⟨m, hm⟩ := hnR
    refine ⟨C (↑(m⁻¹ * u⁻¹) : R) * X, -C (↑u⁻¹ : R), 0, ?_⟩
    have hd : derivative (kummerPoly n (u : R)) = C (n : R) * X ^ (n - 1) := by
      simp [kummerPoly, derivative_X_pow]
    rw [hd, pow_zero]
    have hX : X * X ^ (n - 1) = (X ^ n : R[X]) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    have h1 : C (↑(m⁻¹ * u⁻¹) : R) * C (n : R) = C (↑u⁻¹ : R) := by
      rw [← C_mul, ← hm, Units.val_mul, mul_comm (↑m⁻¹ : R), mul_assoc, Units.inv_mul,
        mul_one]
    have h2 : C (↑u⁻¹ : R) * C (u : R) = 1 := by rw [← C_mul, Units.inv_mul, C_1]
    calc C (n : R) * X ^ (n - 1) * (C (↑(m⁻¹ * u⁻¹) : R) * X) +
          (X ^ n - C (u : R)) * -C (↑u⁻¹ : R)
        = C (↑(m⁻¹ * u⁻¹) : R) * C (n : R) * (X * X ^ (n - 1)) - C (↑u⁻¹ : R) * X ^ n +
            C (↑u⁻¹ : R) * C (u : R) := by ring
      _ = 1 := by rw [h1, hX, h2]; ring

lemma kummerPair_f {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) (u : Rˣ) :
    (kummerPair hn hnR u).f = kummerPoly n (u : R) := rfl

/-- `R[T]/(Tⁿ - u)` is presented by the standard étale pair `(Tⁿ - u, 1)`. -/
noncomputable def kummerPresentation {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) (u : Rˣ) :
    StandardEtalePresentation R (AdjoinRoot (kummerPoly n (u : R))) where
  P := kummerPair hn hnR u
  x := AdjoinRoot.root _
  hasMap := ⟨by rw [kummerPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], by simp [kummerPair]⟩
  lift_bijective := by
    let P := kummerPair hn hnR u
    have hP : P.HasMap (AdjoinRoot.root (kummerPoly n (u : R))) :=
      ⟨by rw [kummerPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], by simp [P, kummerPair]⟩
    let φ := P.lift _ hP
    let ψ : AdjoinRoot (kummerPoly n (u : R)) →ₐ[R] P.Ring :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
    have h1 : ψ.comp φ = AlgHom.id R P.Ring := P.hom_ext (by simp [φ, ψ])
    have h2 : φ.comp ψ = AlgHom.id R _ := AdjoinRoot.algHom_ext (by simp [φ, ψ])
    exact ⟨Function.LeftInverse.injective (g := ψ) fun x ↦ congrArg (· x) h1,
      Function.RightInverse.surjective (g := ψ) fun x ↦ congrArg (· x) h2⟩

/-- **Kummer coverings are étale.** -/
theorem etale_kummer {n : ℕ} (hn : 0 < n) (hnR : IsUnit (n : R)) (u : Rˣ) :
    Algebra.Etale R (AdjoinRoot (kummerPoly n (u : R))) :=
  haveI : Algebra.IsStandardEtale R (AdjoinRoot (kummerPoly n (u : R))) :=
    ⟨⟨kummerPresentation hn hnR u⟩⟩
  inferInstance

/-- **Kummer coverings are faithfully flat** (free of rank `n`). -/
theorem faithfullyFlat_kummer [Nontrivial R] {n : ℕ} (hn : 0 < n) (u : R) :
    Module.FaithfullyFlat R (AdjoinRoot (kummerPoly n u)) :=
  haveI := (monic_kummerPoly hn u).free_adjoinRoot
  haveI : Nontrivial (AdjoinRoot (kummerPoly n u)) := by
    refine ⟨⟨1, 0, fun h ↦ ?_⟩⟩
    rw [← map_one (AdjoinRoot.mk (kummerPoly n u)), AdjoinRoot.mk_eq_zero] at h
    refine (monic_kummerPoly hn u).not_dvd_of_natDegree_lt one_ne_zero ?_ h
    rw [natDegree_one, natDegree_X_pow_sub_C]
    exact hn
  inferInstance

/-- In the Kummer covering, `u` acquires an `n`-th root. -/
theorem root_pow_kummer (n : ℕ) (u : R) :
    AdjoinRoot.root (kummerPoly n u) ^ n = algebraMap R _ u := by
  have h := AdjoinRoot.eval₂_root (kummerPoly n u)
  simp only [kummerPoly, eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← sub_eq_zero]
  exact h

end CurvesJacobian
