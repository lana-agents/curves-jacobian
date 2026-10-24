/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Limits

/-!
# Morphisms agreeing on all closed points (MR7, proper-curve uniqueness, step R6)

Uniqueness for proper hyperbolic curves over `p`-adic fields (S8 sub-task, Thm C route): an
automorphism `h` of `X` inducing an inner automorphism of `Π_X` fixes every closed point together
with its residue field (Thm C over the finite extensions `κ(x)`). This file supplies the last
step: on a reduced Jacobson scheme `X`, two `S`-morphisms `f, g : X ⟶ Y` (`Y` separated over `S`)
with `x̃ ≫ f = x̃ ≫ g` for the canonical point `x̃ : Spec κ(x) ⟶ X` of every closed point `x` are
equal. The closed points are dense (`closure_closedPoints`), so `∐_x Spec κ(x) ⟶ X` is dominant,
and `ext_of_isDominant_of_isSeparated'` applies.

## Main results

* `CurvesJacobian.LocAn.isDominant_closedPointsDesc`: `∐_{x closed} Spec κ(x) ⟶ X` is
  dominant on a Jacobson scheme;
* **`CurvesJacobian.LocAn.ext_of_fromSpecResidueField_closedPoints`**: morphisms agreeing on all
  closed points (with residue fields) are equal;
* `CurvesJacobian.LocAn.eq_id_of_fromSpecResidueField_closedPoints`: an `S`-endomorphism fixing
  all closed points with their residue fields is the identity.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology

noncomputable section

namespace CurvesJacobian.LocAn

variable {X : Scheme.{u}}

/-- The canonical points of the closed points of `X`, as one morphism
`∐_{x closed} Spec κ(x) ⟶ X`. -/
def closedPointsDesc (X : Scheme.{u}) :
    (∐ fun x : closedPoints X ↦ Spec (X.residueField x.1)) ⟶ X :=
  Sigma.desc fun x ↦ X.fromSpecResidueField x.1

/-- **The closed points are dense**: on a Jacobson scheme, `∐_{x closed} Spec κ(x) ⟶ X` is
dominant. -/
theorem isDominant_closedPointsDesc [JacobsonSpace X] : IsDominant (closedPointsDesc X) := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hsub : closedPoints X ⊆ Set.range (closedPointsDesc X) := fun x hx ↦ by
    refine ⟨Sigma.ι (fun x : closedPoints X ↦ Spec (X.residueField x.1)) ⟨x, hx⟩
      (IsLocalRing.closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply, closedPointsDesc, Sigma.ι_desc,
      Scheme.fromSpecResidueField_apply]
  exact closure_mono hsub (by rw [closure_closedPoints]; trivial)

/-- **Morphisms agreeing on the closed points are equal**: for a reduced Jacobson scheme `X` over
`S`, `Y` separated over `S` and `S`-morphisms `f, g : X ⟶ Y`, if `x̃ ≫ f = x̃ ≫ g` for the
canonical point `x̃ : Spec κ(x) ⟶ X` of every closed point `x`, then `f = g`. -/
theorem ext_of_fromSpecResidueField_closedPoints {S Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsReduced X] [JacobsonSpace X] [IsSeparated (Y ↘ S)] {f g : X ⟶ Y} [f.IsOver S]
    [g.IsOver S]
    (h : ∀ x ∈ closedPoints X, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g) :
    f = g := by
  haveI := isDominant_closedPointsDesc (X := X)
  refine ext_of_isDominant_of_isSeparated' (S := S) (closedPointsDesc X) ?_
  refine Sigma.hom_ext _ _ fun x ↦ ?_
  rw [closedPointsDesc, Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
  exact h x.1 x.2

/-- **An endomorphism fixing all closed points with their residue fields is the identity**
(reduced Jacobson `X`, separated over `S`). -/
theorem eq_id_of_fromSpecResidueField_closedPoints {S : Scheme.{u}} [X.Over S] [IsReduced X]
    [JacobsonSpace X] [IsSeparated (X ↘ S)] {h : X ⟶ X} [h.IsOver S]
    (hh : ∀ x ∈ closedPoints X, X.fromSpecResidueField x ≫ h = X.fromSpecResidueField x) :
    h = 𝟙 X :=
  ext_of_fromSpecResidueField_closedPoints (S := S) fun x hx ↦ by
    rw [hh x hx, Category.comp_id]

end CurvesJacobian.LocAn
