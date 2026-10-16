/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.FunctionField.OfSmooth
import CurvesJacobian.Scheme.CurvePlaces
import WeilCurves.FunctionField.RiemannRoch

/-!
# The function field of a curve

For a curve `X` over a perfect field `k` (belyi's `IsCurveOver`: smooth of relative dimension
one, proper, geometrically integral), the function field `K(X)` with belyi's `k`-algebra
structure is a function field of one variable over `k` in the sense of weil-curves
(`CurvesJacobian.isFunctionField_functionField`). Consequently the weil-curves theory
(places, divisors, `ℓ(D)`, Riemann–Roch, genus) applies to `K(X)`, and by `curvePlaceEquiv` its
places are the non-generic points of `X`.

The proof takes a standard smooth affine chart `Γ(X, V)` of relative dimension one
(Mathlib's `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`), whose fraction
field is `K(X)`, and applies `CurvesJacobian.isFunctionField_of_smooth`.
-/

open CategoryTheory AlgebraicGeometry Belyi

namespace CurvesJacobian

universe u

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **The function field of a curve over a perfect field is a function field of one variable.** -/
instance isFunctionField_functionField :
    WeilCurves.FunctionField.IsFunctionField k X.functionField := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := X ↘ Spec (CommRingCat.of k)) (genericPoint X)
  have hUtop : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
    rw [Subsingleton.elim y ((X ↘ Spec (CommRingCat.of k)).base (genericPoint X))]
    exact hVU hxV
  subst hUtop
  set φ := ((X ↘ Spec (CommRingCat.of k)).appLE ⊤ V hVU).hom
  let e : Γ(Spec (CommRingCat.of k), ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  letI algA : Algebra k Γ(X, V) := (φ.comp (e.symm : k →+* _)).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(X, V) := by
    have he0 := RingHom.IsStandardSmoothOfRelativeDimension.equiv e.symm
    have hc := hss.comp he0
    rw [Nat.add_zero] at hc
    exact hc
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  haveI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  haveI : IsScalarTower k Γ(X, V) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial) c =
      X.germToFunctionField V (((X ↘ Spec (CommRingCat.of k)).appLE ⊤ V hVU)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
    rw [Scheme.germToFunctionField, Scheme.Hom.appLE]
    simp only [CommRingCat.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  exact isFunctionField_of_smooth k Γ(X, V) X.functionField

open WeilCurves.FunctionField in
/-- The genus of a curve `X/k`: the weil-curves genus `riemannConst + 1` of `K(X)/k`. (It is the
usual genus when `k` is algebraically closed in `K(X)`, which holds for geometrically integral
`X`; that comparison is not formalised here.) -/
noncomputable def curveGenus : ℤ := genus k X.functionField

open WeilCurves.FunctionField in
/-- **Riemann–Roch on a curve** `X/k` (weil-curves `riemannRoch` for `K(X)`): for every divisor
`D` on `X` (a finitely supported `ℤ`-valued function on the places of `K(X)`, i.e. on the
closed points of `X` via `curvePlaceEquiv`), `ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/
theorem curve_riemannRoch (D : Divisor k X.functionField) :
    (D.ell : ℤ) - (canonical k X.functionField - D).ell = D.deg + 1 - curveGenus k X :=
  riemannRoch D

open WeilCurves.FunctionField in
/-- `deg W = 2g - 2` on a curve. -/
theorem curve_deg_canonical : (canonical k X.functionField).deg = 2 * curveGenus k X - 2 :=
  deg_canonical

end CurvesJacobian
