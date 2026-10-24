/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThmC
import CurvesJacobian.Kummer.JacobianDivExt
import CurvesJacobian.Kummer.JacobianLocalField
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# [LocAn] Theorem C (profinite) over finite extensions of `ℚ_p` and over their subfields

[LocAn] Theorem C (§19, txt l.5050) is stated for (sub-)`p`-adic base fields. The profinite proof
of `LocAn/ThmC.lean` (Kummer sequence of the Jacobian, [LocAn] l.5116–5118) needs exactly one
arithmetic input about the base field: `⋂_{N ≥ 1} N · J(K) = 0` for the Jacobian `J` of the curve
(MR5's `CurvesJacobian.Kummer.JacDivFree X σ hσ K`).

For `K` finite over `ℚ_p` and for number fields this is [AbsTopIII] Rem. 1.5.4(i) for `J`, proved
by MR5 (`CurvesJacobian.Kummer.jacDivFree_padic`, `jacDivFree_numberField`; this discharged the
former MR7 debt D-KF). So the `_padic` and `_numberField` theorems below are unconditional.

* **`CurvesJacobian.LocAn.placeOfF_eq_of_xSectionGk_conj_padic`**: proper `X` over `K / ℚ_p`
  finite; `…_numberField` over a number field;
* **`CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj_padic`**: rational points of the affine
  `U`, `Δ_U`-conjugate sections of `Π_U → G_K`; `…_numberField` over a number field;
* `…_of_ext` forms: the hypothesis is stated over any extension field `L ⊇ k`, for example a
  finite extension of `ℚ_p` containing a number field `k` (`JacDivFree.of_ext`). This covers
  sub-`p`-adic `k` in the sense of [LocAn] Def. 15.4(i).

The genus-`0` case is not covered (`hg`): it needs Kummer classes of units instead of the Jacobian
(MR7 plan, S3(a)).
-/

universe u

open WeilCurves.FunctionField

namespace CurvesJacobian.LocAn

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve AlgebraicGeometry Belyi
  CurvesJacobian.Cusp CategoryTheory

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for a proper curve over a subfield `k` of a field `L` with
`⋂_N N · J(L) = 0`** (e.g. `L` a finite extension of `ℚ_p`, `k` a number field in `L`): rational
points of `X` with `Δ_X`-conjugate sections `s_x, s_y : G_k → Π_X` are equal, if `X_{k̄}` has
genus `≠ 0`. -/
theorem placeOfF_eq_of_xSectionGk_conj_of_ext (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (L : Type u) [Field L] [Algebra k L] (hKF : JacDivFree X σ hσ L)
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {x y : RatPoint (curveGaloisData k hτ)} {δ : PiX (curveGaloisData k hτ)}
    (hδ : δ ∈ DeltaX (curveGaloisData k hτ))
    (h : ∀ g, xSectionGk y g = δ * xSectionGk x g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_xSectionGk_conj_curve k hτ σ hσ (JacDivFree.of_ext L hKF) hg hδ h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for a proper curve over a finite extension `K` of `ℚ_p`**
(`⋂_N N · J(K) = 0` is `jacDivFree_padic`). -/
theorem placeOfF_eq_of_xSectionGk_conj_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {x y : RatPoint (curveGaloisData k hτ)} {δ : PiX (curveGaloisData k hτ)}
    (hδ : δ ∈ DeltaX (curveGaloisData k hτ))
    (h : ∀ g, xSectionGk y g = δ * xSectionGk x g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_xSectionGk_conj_curve k hτ σ hσ (jacDivFree_padic X σ hσ p) hg hδ h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for the affine curve `U` over a subfield `k` of a field `L` with
`⋂_N N · J(L) = 0`**: rational points of `U` whose sections of `Π_U → G_k` are
`Δ_U`-conjugate are equal, if the compactification has geometric genus `≠ 0`. -/
theorem placeOfF_eq_of_ratSectionGk_conj_of_ext (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (L : Type u) [Field L] [Algebra k L] (hKF : JacDivFree X σ hσ L)
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    (hHL : (curveGaloisData k hτ).HL = (curveGaloisData k hτ).H)
    {x y : RatPoint (curveGaloisData k hτ)} (hx : coordT τ ∈ x.A) (hy : coordT τ ∈ y.A)
    {δ : Pi (curveGaloisData k hτ)} (hδ : δ ∈ (piToGk (curveGaloisData k hτ)).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_ratSectionGk_conj_curve k hτ σ hσ (JacDivFree.of_ext L hKF) hg hHL hx hy hδ h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for the affine curve `U` over a finite extension `K` of `ℚ_p`**
(`⋂_N N · J(K) = 0` is `jacDivFree_padic`). -/
theorem placeOfF_eq_of_ratSectionGk_conj_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    (hHL : (curveGaloisData k hτ).HL = (curveGaloisData k hτ).H)
    {x y : RatPoint (curveGaloisData k hτ)} (hx : coordT τ ∈ x.A) (hy : coordT τ ∈ y.A)
    {δ : Pi (curveGaloisData k hτ)} (hδ : δ ∈ (piToGk (curveGaloisData k hτ)).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_ratSectionGk_conj_curve k hτ σ hσ (jacDivFree_padic X σ hσ p) hg hHL hx hy hδ h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for a proper curve over a number field**
(`jacDivFree_numberField`). -/
theorem placeOfF_eq_of_xSectionGk_conj_numberField [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {x y : RatPoint (curveGaloisData k hτ)} {δ : PiX (curveGaloisData k hτ)}
    (hδ : δ ∈ DeltaX (curveGaloisData k hτ))
    (h : ∀ g, xSectionGk y g = δ * xSectionGk x g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_xSectionGk_conj_curve k hτ σ hσ (jacDivFree_numberField X σ hσ) hg hδ h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for the affine curve `U` over a number field**
(`jacDivFree_numberField`). -/
theorem placeOfF_eq_of_ratSectionGk_conj_numberField [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    (hHL : (curveGaloisData k hτ).HL = (curveGaloisData k hτ).H)
    {x y : RatPoint (curveGaloisData k hτ)} (hx : coordT τ ∈ x.A) (hy : coordT τ ∈ y.A)
    {δ : Pi (curveGaloisData k hτ)} (hδ : δ ∈ (piToGk (curveGaloisData k hτ)).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_ratSectionGk_conj_curve k hτ σ hσ (jacDivFree_numberField X σ hσ) hg hHL hx hy
    hδ h

end CurvesJacobian.LocAn
