/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.BaseChangeFunctionField
import CurvesJacobian.Kummer.JacobianTate
import CurvesJacobian.Cusp.GenusBaseChange

/-!
# `#Pic(F k̄)[n] = n^{2g}` in the Galois model

Let `X` be a curve over a field `k` of characteristic `0`, `τ ∈ K(X)` transcendental, and
`D = curveGaloisData k hτ` its Galois model, with `k̄ = kbar k Ω` and `F k̄ = F (baseChange D)`.
By `ffEquiv k hτ : F k̄ ≃ₐ[k̄] K(X_{k̄})` the results of `Galois/PicTorsionCount.lean` and
`Kummer/JacobianTate.lean` for the curve `X_{k̄}` over the algebraically closed field `k̄` transfer
to `Pic(F k̄) = Pic(X_{k̄})`:

* `CurvesJacobian.Kummer.natCard_picTorsion_baseChange`: `#Pic(F k̄)[n] = n^{2g}` for `n ≥ 1`,
  with `g = g(X_{k̄})`;
* `CurvesJacobian.Kummer.curveGenus_baseChangeKbar`: `g(X_{k̄}) = g(X)`
  (`CurvesJacobian.Cusp.curveGenus_baseChange`); hence `natCard_picTorsion_baseChange'`:
  `#Pic(F k̄)[n] = n^{2 g(X)}`;
* `CurvesJacobian.Kummer.exists_nsmul_eq_of_mem_picTorsion_baseChange`:
  `m · Pic(F k̄)[nm] = Pic(F k̄)[n]`;
* `CurvesJacobian.Kummer.tateProj_surjective_pic_baseChange`: the projections
  `T_ℓ Pic(F k̄) → Pic(F k̄)[ℓ^m]` are onto.
-/

open CategoryTheory AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian.Kummer

open CurvesJacobian.Cusp CurvesJacobian.Tate

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- **`#Pic(F k̄)[n] = n^{2g}`**, `g = g(X_{k̄})`, for the Galois model `D = curveGaloisData k hτ`
of a curve `X` over a field of characteristic `0` and `n ≥ 1`. -/
theorem natCard_picTorsion_baseChange (n : ℕ) [NeZero n] :
    Nat.card (picTorsion (kbar k (FFClosure X))
      (F (Kummer.baseChange (curveGaloisData k hτ))) n) =
      n ^ (2 * (curveGenus (kbar k (FFClosure X)) (baseChangeKbar k X)).toNat) := by
  rw [natCard_picTorsion_eq (ffEquiv k hτ) n]
  exact natCard_picTorsion n

variable (X) in
/-- **`g(X_{k̄}) = g(X)`**. -/
theorem curveGenus_baseChangeKbar :
    curveGenus (kbar k (FFClosure X)) (baseChangeKbar k X) = curveGenus k X :=
  curveGenus_baseChange k (kbar k (FFClosure X)) X

/-- **`#Pic(F k̄)[n] = n^{2g}`**, `g = g(X)`. -/
theorem natCard_picTorsion_baseChange' (n : ℕ) [NeZero n] :
    Nat.card (picTorsion (kbar k (FFClosure X))
      (F (Kummer.baseChange (curveGaloisData k hτ))) n) =
      n ^ (2 * (curveGenus k X).toNat) := by
  rw [natCard_picTorsion_baseChange k hτ n, curveGenus_baseChangeKbar]

/-- `#Pic(F k̄)[d] = d^{2g}` in the form used by `CurvesJacobian.Tate`. -/
lemma natCard_torsionBy_pic_baseChange (d : ℕ) (hd : 0 < d) :
    Nat.card (torsionBy (Pic (kbar k (FFClosure X))
      (F (Kummer.baseChange (curveGaloisData k hτ)))) d) = d ^ (2 * (curveGenus k X).toNat) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  exact natCard_picTorsion_baseChange' k hτ d

/-- **`m · Pic(F k̄)[nm] = Pic(F k̄)[n]`**: the torsion of `J(k̄)` is divisible. -/
theorem exists_nsmul_eq_of_mem_picTorsion_baseChange {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {x : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))}
    (hx : x ∈ picTorsion (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) n) :
    ∃ y ∈ picTorsion (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))
      (n * m), m • y = x :=
  exists_nsmul_eq_of_mem_torsion (natCard_torsionBy_pic_baseChange k hτ) hn hm hx

/-- **The projections `T_ℓ Pic(F k̄) → Pic(F k̄)[ℓ^m]` are onto.** -/
theorem tateProj_surjective_pic_baseChange {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) :
    Function.Surjective (tateProj (A := Pic (kbar k (FFClosure X))
      (F (Kummer.baseChange (curveGaloisData k hτ)))) ℓ m) :=
  tateProj_surjective (natCard_torsionBy_pic_baseChange k hτ) hℓ m

end CurvesJacobian.Kummer
