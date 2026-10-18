/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.CoordinateRingBaseChange
import Mathlib.RingTheory.Etale.Field
import Pi1.FundamentalGroup.FiniteEtale
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Base change of `E ∖ {O}` along a finite separable extension is finite étale

For a Weierstrass curve `E` over a field `K` and a finite separable extension `M / K`, the map
`K[E] → M[E_M]` (`WeierstrassCurve.Affine.CoordinateRing.map`) is finite étale
(`CurvesJacobian.Cusp.finiteEtale_coordinateRing_map`): by the `elliptic-curves` package,
`M[E_M] ≅ K[E] ⊗_K M` (`WeierstrassCurve.Affine.CoordinateRing.baseChangeLinearEquiv`), the base
change of the finite étale `K → M`.
-/

open Polynomial TensorProduct WeierstrassCurve.Affine.CoordinateRing

universe u

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] (E : WeierstrassCurve K) (M : Type u) [Field M] [Algebra K M]

/-- `M[E_M] ≃ₐ[K[E]] K[E] ⊗_K M`. -/
noncomputable def coordinateRingBaseChangeAlgEquiv :
    (E.toAffine.map (algebraMap K M)).CoordinateRing ≃ₐ[E.toAffine.CoordinateRing]
      E.toAffine.CoordinateRing ⊗[K] M :=
  AlgEquiv.ofRingEquiv (f := ((baseChangeAlgEquiv E.toAffine M).toRingEquiv.trans
    (Algebra.TensorProduct.comm K M E.toAffine.CoordinateRing).toRingEquiv)) fun a ↦ by
    change (Algebra.TensorProduct.comm K M _) (baseChangeAlgEquiv E.toAffine M
      (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (algebraMap K M) a)) = _
    rw [baseChangeAlgEquiv_map, Algebra.TensorProduct.comm_tmul]
    rfl

variable [FiniteDimensional K M] [Algebra.IsSeparable K M]

instance : Algebra.Etale K M :=
  { formallyEtale := Algebra.FormallyEtale.of_isSeparable K M
    finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }

instance : Algebra.Etale E.toAffine.CoordinateRing
    (E.toAffine.map (algebraMap K M)).CoordinateRing :=
  Algebra.Etale.of_equiv (coordinateRingBaseChangeAlgEquiv E M).symm

instance : Module.Finite E.toAffine.CoordinateRing
    (E.toAffine.map (algebraMap K M)).CoordinateRing :=
  Module.Finite.equiv (coordinateRingBaseChangeAlgEquiv E M).symm.toLinearEquiv

/-- **`K[E] → M[E_M]` is finite étale.** -/
theorem finiteEtale_coordinateRing_map :
    (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (algebraMap K M)).FiniteEtale := by
  rw [← RingHom.algebraMap_toAlgebra
    (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (algebraMap K M)),
    RingHom.finiteEtale_algebraMap_iff]
  exact ⟨⟩

end CurvesJacobian.Cusp
