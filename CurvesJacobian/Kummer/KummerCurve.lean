/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.Image
import CurvesJacobian.Kummer.KummerFaithful
import ContinuousKummerTheory.Kummer.Faithful

/-!
# [AbsTopIII] Prop. 1.6(i), (iii) for the Galois model of a curve

[AbsTopIII] Prop. 1.6 (`Topics in Absolute Anabelian Geometry III.txt` l.1969–2039) for the
Galois model `D = curveGaloisData k hτ` of a curve `X` over a field `k` of characteristic `0`
(`Π_X = Pi D`, `Γ(X_η, 𝒪^×) = units D`, `M_X = Ẑ(1)`). The hypothesis "`k` algebraically closed
in `F`" of the generic statements is discharged by `mem_range_of_isAlgebraic_F`, and
Kummer-faithfulness for the Jacobian by `isKummerFaithfulJac_of_isKummerFaithful`:

* **`kummerMapZHat_injective_curve`** (Prop. 1.6(i), l.1988): `κ : Γ(U, 𝒪^×) → H¹(Π_U, Ẑ(1))` is
  injective for torally Kummer-faithful `k` (`KummerTheory.IsTorallyKummerFaithful`, the
  `𝔾_m`-form of [AbsTopIII] Def. 1.5); `kummerMapZHat_injective_curve_numberField` and
  `kummerMapZHat_injective_curve_localField`: for number fields and for finite extensions of
  `ℚ_p` ([AbsTopIII] Rem. 1.5.3(i), 1.5.4(i) for tori) without further hypotheses; the same on
  `π₁ᵉᵗ` (`kummerMapEtaleZHat_injective_curve`);
* **`ker_res_curve`**, **`PU_eq_curve`** (Prop. 1.6(iii), l.2001–2012): `ker(res) = (kˣ)^∧` and
  `P_U = κ(Γ(U, 𝒪^×)) · (kˣ)^∧` for Kummer-faithful `k` (`CurvesJacobian.IsKummerFaithful`) and
  `X(k) ≠ ∅`.
-/

open CategoryTheory AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open CurvesJacobian.Cusp

universe u

namespace CurvesJacobian.Kummer

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- **[AbsTopIII] Prop. 1.6(i) for a curve** over a torally Kummer-faithful field. -/
theorem kummerMapZHat_injective_curve (hkf : IsTorallyKummerFaithful k) :
    Function.Injective (kummerMapZHat (curveGaloisData k hτ)) :=
  kummerMapZHat_injective_of_isTorallyKummerFaithful (mem_range_of_isAlgebraic_F k hτ) hkf

/-- [AbsTopIII] Prop. 1.6(i) for a curve, on `π₁ᵉᵗ`. -/
theorem kummerMapEtaleZHat_injective_curve (hkf : IsTorallyKummerFaithful k) :
    Function.Injective (kummerMapEtaleZHat (curveGaloisData k hτ)) :=
  kummerMapEtaleZHat_injective_of_isTorallyKummerFaithful (mem_range_of_isAlgebraic_F k hτ) hkf

/-- **[AbsTopIII] Prop. 1.6(i) for a curve over a number field.** -/
theorem kummerMapZHat_injective_curve_numberField [NumberField k] :
    Function.Injective (kummerMapZHat (curveGaloisData k hτ)) :=
  kummerMapZHat_injective_curve k hτ (NumberField.isTorallyKummerFaithful k)

open ValuativeRel in
/-- **[AbsTopIII] Prop. 1.6(i) for a curve over a finite extension of `ℚ_p`.** -/
theorem kummerMapZHat_injective_curve_localField [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    Function.Injective (kummerMapZHat (curveGaloisData k hτ)) :=
  kummerMapZHat_injective_curve k hτ (isTorallyKummerFaithful_of_isNonarchimedeanLocalField k)

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve, exactness**: `ker(res) = (kˣ)^∧`, for `k`
Kummer-faithful and `X(k) ≠ ∅`. -/
theorem ker_res_curve (hk : IsKummerFaithful k) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k))) :
    (res (curveGaloisData k hτ)).ker = (constMapZHat (curveGaloisData k hτ)).range :=
  ker_res (isKummerFaithfulJac_of_isKummerFaithful k hτ hk σ hσ)
    (mem_range_of_isAlgebraic_F k hτ)

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve, the image**: `P_U = κ(Γ(U, 𝒪^×)) · (kˣ)^∧`, for
`k` Kummer-faithful and `X(k) ≠ ∅`. -/
theorem PU_eq_curve (hk : IsKummerFaithful k) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k))) :
    PU (curveGaloisData k hτ) = (kummerMapZHat (curveGaloisData k hτ)).range ⊔
      (constMapZHat (curveGaloisData k hτ)).range :=
  PU_eq (isKummerFaithfulJac_of_isKummerFaithful k hτ hk σ hσ)
    (mem_range_of_isAlgebraic_F k hτ)

end CurvesJacobian.Kummer
