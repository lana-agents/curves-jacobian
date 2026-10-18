/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.AlgClosedSurfaceGroup
import Pi1.FundamentalGroup.FiberFunctorIso
import Pi1.Surface.Profinite

/-!
# `π₁ᵉᵗ(X ∖ D) ≃ₜ* Π̂_{g,r}` at every geometric point

For a curve `X` over any algebraically closed field `k` of characteristic zero
(`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_isAlgClosed`; over `ℚ̄` also
`CurvesJacobian.exists_etaleFundamentalGroup_equiv_profiniteSurfaceGroup` via Belyi maps):

* `CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup`: for every geometric point
  `ξ : Spec Ω ⟶ U` (`Ω` separably closed), `π₁ᵉᵗ(U, ξ) ≃ₜ* Π̂_{g,r}` (in universe `u`, via
  `ULift`);
* `CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup₀`: the same in universe `0`
  with pi1's `Pi1.ProfiniteSurfaceGroup g r`.
-/

open CategoryTheory AlgebraicGeometry Belyi Pi1.Profinite

universe u

namespace CurvesJacobian

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **`π₁ᵉᵗ` of a punctured curve is the profinite surface group, at every geometric point.**
Let `X` be a curve over `k` (algebraically closed, characteristic zero) of genus `g`, and
`U ⊆ X` an open subset with finite nonempty complement of cardinality `r`. Then
`π₁ᵉᵗ(U, ξ) ≃ₜ* Π̂_{g,r}` for every geometric point `ξ : Spec Ω ⟶ U`. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ U.toScheme) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat
          (Nat.card ((U : Set X)ᶜ : Set X)))))) :=
  etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_isAlgClosed U hUfin hUne ξ

end Main

section Zero

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **`π₁ᵉᵗ(X ∖ D) ≃ₜ* Π̂_{g,r}`** with pi1's `Pi1.ProfiniteSurfaceGroup` (universe `0`), at every
geometric point. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup₀ (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ U.toScheme) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
      (Nat.card ((U : Set X)ᶜ : Set X))) := by
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup (k := k) U hUfin hUne ξ
  exact ⟨e.trans (completionCongr MulEquiv.ulift)⟩

end Zero

end CurvesJacobian
