/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Pi1.FundamentalGroup.AlgClosedBaseChange

/-!
# Integral schemes over an algebraically closed field are geometrically integral

**Theorem** (`CurvesJacobian.geometricallyIntegral_of_isAlgClosed`). Let `k` be an
algebraically closed field and `X` an integral scheme, locally of finite type over `Spec k`.
Then `X ⟶ Spec k` is geometrically integral.

**Proof sketch.**
1. For any field extension `Ω / k`, the morphism `Spec Ω ⟶ Spec k` is geometrically integral
   (`CurvesJacobian.geometricallyIntegral_Spec_of_isAlgClosed`): for every field `K / k` the
   fibre product is `Spec (Ω ⊗[k] K)`, and `Ω ⊗[k] K` is a domain since `k` is algebraically
   closed (pi1's `Algebra.TensorProduct.isDomain_of_isAlgClosed`).
2. Fix a field `K / k` and put `g : Spec K ⟶ Spec k`. Then `g` is geometrically reduced and
   geometrically irreducible by step 1, flat (everything is flat over a field) and universally
   open (any morphism to `Spec` of a field is). Since `X` is irreducible, Mathlib's instance
   gives `X ×_k K` irreducible; since `X` is reduced and locally noetherian (locally of finite
   type over a field), Mathlib's instance gives `X ×_k K` reduced.
3. Hence `X ⟶ Spec k` is geometrically reduced and geometrically irreducible, i.e.
   geometrically integral.
-/

universe u

open CategoryTheory Limits TensorProduct AlgebraicGeometry

namespace CurvesJacobian

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- For a field extension `Ω / k` of an algebraically closed field `k`, the base change of
`Spec Ω ⟶ Spec k` along any field `K / k` is `Spec (Ω ⊗[k] K)`, which is integral. -/
private lemma isIntegral_pullback_Spec (Ω K : Type u) [Field Ω] [Algebra k Ω] [Field K]
    [Algebra k K] :
    IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  haveI : IsDomain (Ω ⊗[k] K) := Algebra.TensorProduct.isDomain_of_isAlgClosed
  exact IsIntegral.of_isIso (pullbackSpecIso k Ω K).inv

/-- **`Spec Ω ⟶ Spec k` is geometrically integral** for every field extension `Ω` of an
algebraically closed field `k`. -/
theorem geometricallyIntegral_Spec_of_isAlgClosed (Ω : Type u) [Field Ω] [Algebra k Ω] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  haveI : GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
    rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    haveI := isIntegral_pullback_Spec k Ω K
    infer_instance
  haveI : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
    rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    haveI := isIntegral_pullback_Spec k Ω K
    infer_instance
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

variable {k}

/-- **An integral scheme locally of finite type over an algebraically closed field is
geometrically integral.** -/
theorem geometricallyIntegral_of_isAlgClosed {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : GeometricallyReduced f := by
    rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    haveI := geometricallyIntegral_Spec_of_isAlgClosed k K
    haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
      rw [Flat.SpecMap_iff]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    infer_instance
  haveI : GeometricallyIrreducible f := by
    rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    haveI := geometricallyIntegral_Spec_of_isAlgClosed k K
    infer_instance
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- Variant of `geometricallyIntegral_of_isAlgClosed` for the structure morphism of a scheme
over `Spec k`, as used in the `GeometricallyIntegral` field of belyi's `IsCurveOver`. -/
theorem geometricallyIntegral_over_of_isAlgClosed (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    GeometricallyIntegral (X ↘ Spec (CommRingCat.of k)) :=
  geometricallyIntegral_of_isAlgClosed _

end CurvesJacobian
