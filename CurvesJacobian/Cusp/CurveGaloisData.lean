/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Inertia
import CurvesJacobian.Galois.CurveGaloisData

/-!
# The Galois model of a curve, as definitions (MR8.3)

`CurvesJacobian.exists_curveGaloisData` (`CurvesJacobian/Galois/CurveGaloisData.lean`) shows that
every curve in characteristic `0` admits Galois data `D` with `H = H_L` and `eL : K(X) ≃ L`. To
*define* the cuspidal inertia groups of a given curve (`CurvesJacobian.Cusp.cuspInertia`, which
depend on this data) we need the same construction as definitions, for a chosen transcendental
`τ ∈ K(X)`: `Ω = K(X)^alg`, `t = τ`, `H = H_L = Gal(Ω/K(X))`:

* `CurvesJacobian.Cusp.curveGaloisData k hτ : GaloisData k t`;
* `CurvesJacobian.Cusp.curveEquivL k hτ : K(X) ≃+* L` (`curveEquivL_algebraMap`,
  `curveEquivL_τ`).
-/

open CategoryTheory AlgebraicGeometry Belyi Pi1.Orbifold AffOrbicurve WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsFunctionField k X.functionField] {τ : X.functionField} (hτ : Transcendental k τ)

/-- `K(X)^alg`. -/
abbrev FFClosure (X : Scheme.{u}) [IsIntegral X] : Type u := AlgebraicClosure X.functionField

/-- The coordinate `t = τ ∈ K(X)^alg`. -/
abbrev coordT (τ : X.functionField) : FFClosure X := algebraMap X.functionField (FFClosure X) τ

/-- **Galois data of a curve**: `H = H_L = Gal(K(X)^alg / K(X)) ≤ Gal(K(X)^alg / k(τ))`. -/
def curveGaloisData : GaloisData k (coordT τ) :=
  haveI := finiteDimensional_imageL (k := k) hτ
  { H := (imageL (k := k) τ).fixingSubgroup
    HL := (imageL (k := k) τ).fixingSubgroup
    le := le_rfl
    isOpen_HL := (imageL (k := k) τ).fixingSubgroup_isOpen
    conj_mem := fun _ hh _ hn ↦ mul_mem (mul_mem hh hn) (inv_mem hh)
    transcendental := transcendental_image hτ }

lemma curveGaloisData_H_le : (curveGaloisData k hτ).H ≤ (curveGaloisData k hτ).HL := le_rfl

variable [CharZero k]

lemma curveGaloisData_L : (curveGaloisData k hτ).L = imageL (k := k) τ := by
  haveI := isGalois_K₀_algebraicClosure (k := k) τ hτ
  exact InfiniteGalois.fixedField_fixingSubgroup _

/-- **`K(X) ≃ L`** for the Galois data of the curve. -/
def curveEquivL : X.functionField ≃+* (curveGaloisData k hτ).L :=
  (equivImageL (k := k) τ).trans (IntermediateField.equivOfEq (curveGaloisData_L k hτ).symm)

@[simp] lemma curveEquivL_apply (e : X.functionField) :
    ((curveEquivL k hτ e : (curveGaloisData k hτ).L) : FFClosure X) =
      algebraMap X.functionField (FFClosure X) e := rfl

lemma curveEquivL_algebraMap (c : k) :
    ((curveEquivL k hτ (algebraMap k X.functionField c) : (curveGaloisData k hτ).L) :
      FFClosure X) = algebraMap k (FFClosure X) c := by
  rw [curveEquivL_apply, ← IsScalarTower.algebraMap_apply]

lemma curveEquivL_τ :
    ((curveEquivL k hτ τ : (curveGaloisData k hτ).L) : FFClosure X) = coordT τ := rfl

end CurvesJacobian.Cusp
