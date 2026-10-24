/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThmCGenusZeroConstExt
import Mathlib.NumberTheory.Padics.PadicIntegers
import ContinuousKummerTheory.Kummer.Faithful

/-!
# [LocAn] Theorem C in genus `0` over number fields and `p`-adic fields (MR7 S3(a))

`placeOfF_eq_of_ratSectionGk_conj_genus_zero_constExt` (`LocAn/ThmCGenusZeroConstExt.lean`) needs
the constant extension `K ⊆ Ω` (over which two cusps become rational) to be Kummer-faithful for
`𝔾_m`. For `k` a number field or a finite extension of `ℚ_p` and `K/k` finite this holds by
[AbsTopIII] Remark 1.5.3(i), 1.5.4(i) (MR5's continuous-kummer-theory:
`NumberField.isTorallyKummerFaithful`, `KummerTheory.isKummerFaithfulGm_of_finite`), so the
hypothesis can be dropped.

## Main results

* `CurvesJacobian.LocAn.isKummerFaithfulGm_of_finite_numberField`,
  `CurvesJacobian.LocAn.isKummerFaithfulGm_of_finite_padic`: finite extensions of number fields
  and of finite extensions of `ℚ_p` are Kummer-faithful for `𝔾_m` (any universe);
* `CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj_genus_zero_numberField`,
  `CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj_genus_zero_padic`: Thm C (profinite) in
  genus `0` over number fields / finite extensions of `ℚ_p`, for a finite extension `K` over which
  two cusps are rational.
-/

namespace CurvesJacobian.LocAn

open KummerTheory Curve AffOrbicurve IsLocalRing CurvesJacobian.Kummer WeilCurves.FunctionField

universe u

/-- **Finite extensions of number fields are Kummer-faithful for `𝔾_m`** ([AbsTopIII]
Remark 1.5.3(i)). -/
theorem isKummerFaithfulGm_of_finite_numberField (k K : Type u) [Field k] [NumberField k]
    [Field K] [Algebra k K] [FiniteDimensional k K] : IsKummerFaithfulGm K :=
  ((NumberField.isTorallyKummerFaithful k).of_finite K).isKummerFaithfulGm

/-- **Finite extensions of finite extensions of `ℚ_p` are Kummer-faithful for `𝔾_m`**
([AbsTopIII] Remark 1.5.4(i) for tori): `ℤ_p` is a Dedekind domain with finite residue field and
fraction field `ℚ_p`, and `K/ℚ_p` is finite separable. -/
theorem isKummerFaithfulGm_of_finite_padic (p : ℕ) [Fact p.Prime] (k K : Type u) [Field k]
    [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k] [Field K] [Algebra k K]
    [FiniteDimensional k K] : IsKummerFaithfulGm K := by
  letI : Algebra ℚ_[p] K := ((algebraMap k K).comp (algebraMap ℚ_[p] k)).toAlgebra
  haveI : IsScalarTower ℚ_[p] k K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional ℚ_[p] K := Module.Finite.trans k K
  letI : Algebra ℤ_[p] K := ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  haveI : IsScalarTower ℤ_[p] ℚ_[p] K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) := inferInstanceAs (Finite (ResidueField ℤ_[p]))
  exact isKummerFaithfulGm_of_finite ℤ_[p] ℚ_[p] K (maximalIdeal ℤ_[p])
    (IsDiscreteValuationRing.not_a_field _)

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K]

attribute [local instance] isFunctionField_F

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) in genus `0` over a number field** `k`: if over a finite
extension `K ⊆ Ω` of `k` the curve has genus `0` and `U_K` has two distinct cusps of degree `1`,
then rational points of `U` with `Δ_U`-conjugate sections of `Π_U → G_k` are equal. -/
theorem placeOfF_eq_of_ratSectionGk_conj_genus_zero_numberField [NumberField k]
    (hHL : D.HL = D.H) {x y : RatPoint D} (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D}
    (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹)
    (hg : genus K (F (constExt K D)) = 0) {P Q : Place K (F (constExt K D))} (hPQ : P ≠ Q)
    (hP : P.deg = 1) (hQ : Q.deg = 1) (hPc : tF (constExt K D) ∉ P.1)
    (hQc : tF (constExt K D) ∉ Q.1) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_ratSectionGk_conj_genus_zero_constExt
    (isKummerFaithfulGm_of_finite_numberField k K) hHL hx hy hδ h hg hPQ hP hQ hPc hQc

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) in genus `0` over a finite extension `k` of `ℚ_p`**: as
`placeOfF_eq_of_ratSectionGk_conj_genus_zero_numberField`. -/
theorem placeOfF_eq_of_ratSectionGk_conj_genus_zero_padic (p : ℕ) [Fact p.Prime]
    [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
    (hHL : D.HL = D.H) {x y : RatPoint D} (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D}
    (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹)
    (hg : genus K (F (constExt K D)) = 0) {P Q : Place K (F (constExt K D))} (hPQ : P ≠ Q)
    (hP : P.deg = 1) (hQ : Q.deg = 1) (hPc : tF (constExt K D) ∉ P.1)
    (hQc : tF (constExt K D) ∉ Q.1) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_ratSectionGk_conj_genus_zero_constExt
    (isKummerFaithfulGm_of_finite_padic p k K) hHL hx hy hδ h hg hPQ hP hQ hPc hQc

end CurvesJacobian.LocAn
