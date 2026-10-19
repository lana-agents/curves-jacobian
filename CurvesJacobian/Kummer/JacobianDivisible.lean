/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.KummerFaithful
import CurvesJacobian.Picard.GroupEtale

/-!
# Divisibility of `J(k̄)` (JAC-4a)

Let `C` be a curve over a perfect field `k` with a rational point `σ`, `J_k = jacK C σ hσ Ω` its
Jacobian (an abelian variety over `k`), and `n ≥ 1` invertible in `k`.

* `CurvesJacobian.jacKOfClass_nsmul`: `jacKOfClass (n • x) = (jacKOfClass x) ^ n` (from
  `jacKOfClass_add`).
* **`CurvesJacobian.etale_jacK_pow`**, **`surjective_jacK_pow`**: `[n] : J_k → J_k` is étale and
  surjective (`CurvesJacobian.GrpEtale.etale_pow`, `surjective_pow`).
* **`CurvesJacobian.exists_nsmul_eq_jacPoints`**: for every algebraically closed field `K ⊇ k`,
  `J(K) = Pic⁰_{C/k,σ}(K)` is `n`-divisible: every `y ∈ J(K)` is `n • x` with `x ∈ J(K)`.
  In particular `J(k̄)` is divisible if `char k = 0`
  (`CurvesJacobian.exists_nsmul_eq_jacPoints_of_charZero`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry CategoryTheory.MonObj

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi GaloisDescent

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

instance : ConnectedSpace (jacK C σ hσ Ω).left :=
  GeometricallyConnected.connectedSpace_of_subsingleton (jacK C σ hσ Ω).hom

lemma jacKOfClass_zero {T : Over (Spec (CommRingCat.of k))} :
    jacKOfClass C σ hσ Ω (T := T) 0 = 1 := by
  have h := jacKOfClass_add C σ hσ Ω (T := T) 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

lemma jacKOfClass_nsmul {T : Over (Spec (CommRingCat.of k))}
    (x : (picZero C σ hσ (curveToP1 k C)).obj (op T)) (n : ℕ) :
    jacKOfClass C σ hσ Ω (n • x) = jacKOfClass C σ hσ Ω x ^ n := by
  induction n with
  | zero => rw [zero_smul, jacKOfClass_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, jacKOfClass_add, ih, pow_succ]

variable {n : ℕ} (hn : (n : k) ≠ 0)
include hn

/-- **`[n] : J_k → J_k` is étale** for `n` invertible in `k`. -/
theorem etale_jacK_pow : Etale ((𝟙 (jacK C σ hσ Ω) : jacK C σ hσ Ω ⟶ jacK C σ hσ Ω) ^ n).left :=
  GrpEtale.etale_pow hn

/-- **`[n] : J_k → J_k` is surjective** for `n` invertible in `k`. -/
theorem surjective_jacK_pow :
    Surjective ((𝟙 (jacK C σ hσ Ω) : jacK C σ hσ Ω ⟶ jacK C σ hσ Ω) ^ n).left :=
  GrpEtale.surjective_pow hn

/-- **Divisibility of `J(K)` for `K` algebraically closed (JAC-4a)**: if `n` is invertible in
`k`, every point of `J(K) = Pic⁰_{C/k,σ}(K)` is `n` times a point of `J(K)`. -/
theorem exists_nsmul_eq_jacPoints (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (y : jacPoints C σ hσ K) : ∃ x : jacPoints C σ hσ K, n • x = y := by
  let Ω := AlgebraicClosure k
  obtain ⟨x', hx'⟩ := GrpEtale.exists_pow_eq hn K (specAlgebraMap (k₀ := k) K)
    ((jacKPointsEquiv C σ hσ Ω K).symm y)
  refine ⟨jacKPointsEquiv C σ hσ Ω K x', (jacKPointsEquiv C σ hσ Ω K).symm.injective ?_⟩
  rw [jacKPointsEquiv_symm_apply, ← hx']
  refine (jacKOfClass_nsmul C σ hσ Ω (T := Over.mk (specAlgebraMap (k₀ := k) K))
    (jacKPointsEquiv C σ hσ Ω K x') n).trans ?_
  rw [← jacKPointsEquiv_symm_apply, Equiv.symm_apply_apply]

omit hn in
/-- **`J(k̄)` is divisible in characteristic `0` (JAC-4a).** -/
theorem exists_nsmul_eq_jacPoints_of_charZero [CharZero k] (hn : n ≠ 0) (K : Type u) [Field K]
    [Algebra k K] [IsAlgClosed K] (y : jacPoints C σ hσ K) :
    ∃ x : jacPoints C σ hσ K, n • x = y :=
  exists_nsmul_eq_jacPoints C σ hσ (Nat.cast_ne_zero.mpr hn) K y

end CurvesJacobian
