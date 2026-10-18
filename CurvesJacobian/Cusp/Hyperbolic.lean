/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GenusLocAn
import CurvesJacobian.Cusp.GenusBaseChange
import CurvesJacobian.Cusp.CuspCount
import Pi1.Surface.Basic

/-!
# A hyperbolic curve over `K` is hyperbolic over an algebraic closure

Let `K` be a field of characteristic zero, `Ω` an algebraically closed extension and `C` a
hyperbolic curve over `K` (`Belyi.Anabelian.HypCurve`: `2 g + r > 2` with `g = dim H⁰(X̄, Ω¹)`
and `r = Σ_{c ∉ U} [κ(c) : K]`). Then `U_Ω ⊆ X̄_Ω` is hyperbolic: `2 g(X̄_Ω) + #(X̄_Ω ∖ U_Ω) > 2`
(`CurvesJacobian.Cusp.isHyperbolic_baseChange`), since

* `dim_K H⁰(X̄, Ω¹) ≤ g(X̄) = g(X̄_Ω)` (`CurvesJacobian.Cusp.locAn_curveGenus_le`,
  `CurvesJacobian.Cusp.curveGenus_baseChange`);
* `Σ_{c ∉ U} [κ(c) : K] ≤ #(X̄_Ω ∖ U_Ω)` (`CurvesJacobian.Cusp.cuspDegree_le_card_compl`).

This discharges the hypothesis `hhyp` of the arithmetic `CuspidalExt`
(`CurvesJacobian.Cusp.arithmeticExt`).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi Belyi.Anabelian

universe u

namespace CurvesJacobian.Cusp

/-- **Hyperbolicity is preserved by base change to an algebraically closed field.** -/
theorem isHyperbolic_baseChange {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω]
    [Algebra K Ω] [IsAlgClosed Ω] (C : HypCurve K) :
    Pi1.SurfaceGroup.IsHyperbolic (curveGenus Ω (baseChange K Ω C.Xbar)).toNat
      (Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _)) := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI := IsCurveOver.isIntegral Ω (baseChange K Ω C.Xbar)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : LocallyOfFiniteType (pullback.snd (C.Xbar ↘ Spec (.of K)) (specAlgebraMap K Ω)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  have hhyp := C.hyperbolic
  have hg := locAn_curveGenus_le K C.Xbar
  have hgb := curveGenus_baseChange K Ω C.Xbar
  have hr := cuspDegree_le_card_compl K Ω C.U C.cusps_finite
    (compl_finite_baseChangeOpen K Ω C.nonempty)
  have hg' : Anabelian.curveGenus K C.Xbar ≤ (curveGenus Ω (baseChange K Ω C.Xbar)).toNat := by
    rw [hgb]
    omega
  unfold Pi1.SurfaceGroup.IsHyperbolic
  omega

end CurvesJacobian.Cusp
