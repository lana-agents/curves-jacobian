/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticDoubleCover
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.MulByTwoPullback
import EllipticCurves.FunctionField.MulByTwoEndomorphism
import EllipticCurves.DivisionPolynomial.Coprime
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Fiber

/-!
# The duplication map `[2] : E ∖ E[2] → E ∖ {O}` is finite étale

Let `E` be an elliptic curve over a field `K` of characteristic zero, `K[E]` its affine
coordinate ring (`E ∖ {O}`) and `B = K[E][1/ψ]` (`CurvesJacobian.Cusp.coverRingE E`,
`E ∖ E[2]`, `ψ = 2y + a₁x + a₃`). The duplication formulas

  `x ↦ Φ₂(x)/ψ²`, `y ↦ (preΨ₄(x) - ψ (a₁ Φ₂(x) + a₃ ψ²)) / (2 ψ³)`

define a `K`-algebra map `[2]^* : K[E] → B` (`CurvesJacobian.Cusp.dupHom`); it is the
multiplication-by-two pullback of the `elliptic-curves` package
(`WeierstrassCurve.Affine.CoordinateRing.mulByTwoCoordHom`, which is tied to the group law by
`genericPoint_add_self`) followed by the inclusion `B ⊆ K(E)` (`CurvesJacobian.Cusp.coe_dupHom`).

**Main theorem** (`CurvesJacobian.Cusp.isFiniteEtale_spec_dupHom`): `Spec [2]^*` is finite étale.

* *Finite*: `x` is a root of the monic quartic `Φ₂(T) - [2]^*x · Ψ₂Sq(T)`, `y` of the Weierstrass
  polynomial over `K[x]`, and `1/ψ² = 1/Ψ₂Sq(x) = u(x) [2]^*x + v(x)` for a Bézout identity
  `u Φ₂ + v Ψ₂Sq = 1` (`WeierstrassCurve.isCoprime_Φ_two_Ψ₂Sq`).
* *Unramified*: `Ω_{B/K}` is free with basis `dx` (`B` is étale over `K[x]`); write
  `d b = δ(b) dx`. Then `δ([2]^*x) = 2 [2]^*ψ / ψ` (the invariant differential: the identity
  `Φ₂' Ψ₂Sq - Φ₂ Ψ₂Sq' = 2 preΨ₄` and `[2]^*ψ = preΨ₄/ψ³`), and differentiating the Weierstrass
  equation at the doubled point gives `δ([2]^*y) = -2 [2]^*W_X / ψ`. As `ψ` and `W_X` generate the
  unit ideal of `K[E]` (nonsingularity), so do their images, hence `dx = 0` in `Ω_{B/K[E]}`.
* *Flat*: `K[E]` is a Dedekind domain (`elliptic-curves`) and `B` is a torsion-free domain.
-/

open Polynomial AlgebraicGeometry WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

universe u

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-- **The invariant differential identity** `Φ₂' Ψ₂Sq - Φ₂ Ψ₂Sq' = 2 preΨ₄`. -/
lemma derivative_Φ_two_mul_sub : derivative (E.Φ 2) * E.Ψ₂Sq - E.Φ 2 * derivative E.Ψ₂Sq =
    2 * E.preΨ₄ := by
  have h := congrArg (C : K → K[X]) E.b_relation
  simp only [map_mul, map_sub, map_pow, map_ofNat] at h
  rw [WeierstrassCurve.Φ_two, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.preΨ₄]
  simp only [derivative_add, derivative_mul, derivative_X_pow, derivative_C,
    derivative_X, derivative_ofNat, map_mul, map_sub, map_pow, map_ofNat]
  simp only [Nat.cast_ofNat, map_ofNat]
  linear_combination (-2 * X ^ 2) * h

/-! ### `B = K[E][1/ψ]` inside the function field -/

section FunctionField

/-- `ψ ≠ 0` in the coordinate ring, for `2 ≠ 0`. -/
lemma psiE_ne_zero' (h2 : (2 : K) ≠ 0) : psiE E ≠ 0 := by
  intro h
  rw [psiE_eq] at h
  have h2' := (WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero h).2
  rw [C_eq_zero] at h2'
  exact h2 h2'

/-- The inclusion `B = K[E][1/ψ] → K(E)`. -/
noncomputable instance [CharZero K] : Algebra (coverRingE E) E.toAffine.FunctionField :=
  (IsLocalization.Away.lift (psiE E) (g := algebraMap E.toAffine.CoordinateRing
    E.toAffine.FunctionField)
    (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (psiE_ne_zero' E two_ne_zero)))).toAlgebra

instance [CharZero K] : IsScalarTower E.toAffine.CoordinateRing (coverRingE E)
    E.toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq (psiE E) _ a).symm

instance [CharZero K] : IsFractionRing (coverRingE E) E.toAffine.FunctionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (psiE E)) _ _

lemma algebraMap_coverRingE_injective [CharZero K] :
    Function.Injective (algebraMap (coverRingE E) E.toAffine.FunctionField) :=
  IsFractionRing.injective _ _

end FunctionField

/-! ### The duplication map -/

section Dup

variable [CharZero K]

/-- `x ∈ B`. -/
noncomputable abbrev xB : coverRingE E :=
  algebraMap E.toAffine.CoordinateRing (coverRingE E) (AdjoinRoot.mk E.toAffine.polynomial (C X))

/-- `y ∈ B`. -/
noncomputable abbrev yB : coverRingE E :=
  algebraMap E.toAffine.CoordinateRing (coverRingE E) (AdjoinRoot.root E.toAffine.polynomial)

/-- `ψ ∈ B`. -/
noncomputable abbrev psiB : coverRingE E :=
  algebraMap E.toAffine.CoordinateRing (coverRingE E) (psiE E)

/-- `1/ψ ∈ B`. -/
noncomputable abbrev invPsiB : coverRingE E := IsLocalization.Away.invSelf (psiE E)

omit [CharZero K] in
lemma psiB_mul_invPsiB : psiB E * invPsiB E = 1 := IsLocalization.Away.mul_invSelf _

/-- The `x`-coordinate of `2P`: `Φ₂(x)/ψ²`. -/
noncomputable def x2B : coverRingE E := aeval (xB E) (E.Φ 2) * invPsiB E ^ 2

/-- The `y`-coordinate of `2P`: `(preΨ₄(x) - ψ (a₁ Φ₂(x) + a₃ Ψ₂Sq(x))) / (2 ψ³)`. -/
noncomputable def y2B : coverRingE E :=
  algebraMap K (coverRingE E) 2⁻¹ * (aeval (xB E) E.preΨ₄ - psiB E *
    (algebraMap K (coverRingE E) E.a₁ * aeval (xB E) (E.Φ 2) +
      algebraMap K (coverRingE E) E.a₃ * aeval (xB E) E.Ψ₂Sq)) * invPsiB E ^ 3

local notation "ι" => algebraMap (coverRingE E) E.toAffine.FunctionField
local notation "φ" => algebraMap K E.toAffine.FunctionField

lemma ι_algebraMap_coordinateRing (a : E.toAffine.CoordinateRing) :
    ι (algebraMap _ (coverRingE E) a) = algebraMap _ E.toAffine.FunctionField a :=
  (IsScalarTower.algebraMap_apply _ _ _ a).symm

lemma ι_algebraMap_K (c : K) : ι (algebraMap K (coverRingE E) c) = φ c := by
  rw [IsScalarTower.algebraMap_apply K E.toAffine.CoordinateRing (coverRingE E),
    ι_algebraMap_coordinateRing, ← IsScalarTower.algebraMap_apply]

instance : IsScalarTower K (coverRingE E) E.toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (ι_algebraMap_K E c).symm

lemma ι_xB : ι (xB E) = genX E.toAffine := ι_algebraMap_coordinateRing E _

lemma ι_yB : ι (yB E) = genY E.toAffine := ι_algebraMap_coordinateRing E _

lemma ι_aeval_xB (p : K[X]) : ι (aeval (xB E) p) = (p.map φ).eval (genX E.toAffine) := by
  rw [← ι_xB, eval_map, aeval_def, hom_eval₂, ← IsScalarTower.algebraMap_eq]

lemma ι_psiB : ι (psiB E) =
    ((E.map φ).ψ 2).evalEval (genX E.toAffine) (genY E.toAffine) := by
  rw [WeierstrassCurve.map_ψ, ← genPsi_mk_map_evalEval, ι_algebraMap_coordinateRing, psiE,
    WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂]

lemma ι_psiB_mul_invPsiB : ι (psiB E) * ι (invPsiB E) = 1 := by
  rw [← map_mul, psiB_mul_invPsiB, map_one]

lemma ι_psiB_sq : ι (psiB E) ^ 2 = ((E.map φ).Ψ₂Sq).eval (genX E.toAffine) := by
  rw [← map_pow, ← map_pow, psi_sq, ι_algebraMap_coordinateRing,
    show algebraMap K[X] E.toAffine.CoordinateRing (gE E) = AdjoinRoot.mk _ (C (gE E)) from rfl,
    ← genPsi, genPsi_mk_map_evalEval, Polynomial.map_C, evalEval_C, WeierstrassCurve.map_Ψ₂Sq,
    gE]
  rfl

/-- The `x`-coordinate of `2P` in `K(E)` (the `elliptic-curves` duplication formula). -/
noncomputable abbrev x2F : E.toAffine.FunctionField :=
  ((E.map φ).Φ 2).eval (genX E.toAffine) / (E.map φ).Ψ₂Sq.eval (genX E.toAffine)

/-- The `y`-coordinate of `2P` in `K(E)`. -/
noncomputable abbrev y2F : E.toAffine.FunctionField :=
  ((E.map φ).preΨ₄.eval (genX E.toAffine) -
          ((E.map φ).ψ 2).evalEval (genX E.toAffine) (genY E.toAffine) *
            ((E.map φ).a₁ * ((E.map φ).Φ 2).eval (genX E.toAffine) +
              (E.map φ).a₃ * (E.map φ).Ψ₂Sq.eval (genX E.toAffine))) /
        (2 * ((E.map φ).ψ 2).evalEval (genX E.toAffine) (genY E.toAffine) ^ 3)

lemma ι_psiB_ne_zero : ι (psiB E) ≠ 0 := by
  intro h
  simpa [h] using ι_psiB_mul_invPsiB E

lemma ι_x2B : ι (x2B E) = x2F E := by
  have h := ι_psiB_mul_invPsiB E
  have hp := ι_psiB_ne_zero E
  rw [x2B, map_mul, map_pow, ι_aeval_xB, ← WeierstrassCurve.map_Φ]
  unfold x2F
  rw [← ι_psiB_sq, eq_div_iff (pow_ne_zero 2 hp)]
  linear_combination ((E.map φ).Φ 2).eval (genX E.toAffine) * (ι (psiB E) * ι (invPsiB E) + 1) * h

lemma ι_y2B : ι (y2B E) = y2F E := by
  have h := ι_psiB_mul_invPsiB E
  have hp := ι_psiB_ne_zero E
  have h2 : (2 : E.toAffine.FunctionField) ≠ 0 := by
    have := (map_ne_zero φ).2 (two_ne_zero (α := K))
    rwa [map_ofNat] at this
  rw [y2B, map_mul, map_mul, map_pow, map_sub, map_mul, map_add, map_mul, map_mul, ι_aeval_xB,
    ι_aeval_xB, ι_aeval_xB, ι_algebraMap_K, ι_algebraMap_K, ι_algebraMap_K,
    ← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_Ψ₂Sq, ← WeierstrassCurve.map_preΨ₄]
  unfold y2F
  rw [← ι_psiB, eq_div_iff (mul_ne_zero h2 (pow_ne_zero 3 hp)), map_inv₀, map_ofNat]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  field_simp
  set P := ι (psiB E)
  set I := ι (invPsiB E)
  linear_combination ((E.map φ).preΨ₄.eval (genX E.toAffine) -
    P * φ E.a₁ * ((E.map φ).Φ 2).eval (genX E.toAffine) -
    P * φ E.a₃ * (E.map φ).Ψ₂Sq.eval (genX E.toAffine)) * (P ^ 2 * I ^ 2 + P * I + 1) * h

/-- **The duplication map** `[2]^* : K[E] → K[E][1/ψ]`, `x ↦ x(2P)`, `y ↦ y(2P)`. -/
noncomputable def dupHom : E.toAffine.CoordinateRing →+* coverRingE E :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap K (coverRingE E)) (x2B E)) (y2B E) (by
    apply algebraMap_coverRingE_injective E
    have hc : (algebraMap (coverRingE E) E.toAffine.FunctionField).comp
        (eval₂RingHom (algebraMap K (coverRingE E)) (x2B E)) =
        eval₂RingHom φ (x2F E) := by
      refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
      · simp [ι_algebraMap_K]
      · simp [ι_x2B]
    have h0 := congrArg (mulByTwoCoordHom (W := E.toAffine) two_ne_zero)
      (AdjoinRoot.mk_self (f := E.toAffine.polynomial))
    rw [map_zero, mulByTwoCoordHom, AdjoinRoot.lift_mk] at h0
    rw [map_zero, hom_eval₂, ι_y2B, hc]
    exact h0)

lemma dupHom_x : dupHom E (AdjoinRoot.mk E.toAffine.polynomial (C X)) = x2B E := by
  rw [dupHom, AdjoinRoot.lift_mk, eval₂_C, coe_eval₂RingHom, eval₂_X]

lemma dupHom_y : dupHom E (AdjoinRoot.root E.toAffine.polynomial) = y2B E := by
  rw [dupHom, AdjoinRoot.lift_root]

lemma dupHom_algebraMap (c : K) :
    dupHom E (algebraMap K E.toAffine.CoordinateRing c) = algebraMap K (coverRingE E) c := by
  rw [IsScalarTower.algebraMap_apply K K[X] E.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    dupHom, AdjoinRoot.lift_of, coe_eval₂RingHom, Polynomial.algebraMap_apply, eval₂_C]
  rfl

/-- `[2]^*` followed by `B ⊆ K(E)` is the multiplication-by-two pullback of `elliptic-curves`. -/
theorem coe_dupHom :
    (algebraMap (coverRingE E) E.toAffine.FunctionField).comp (dupHom E) =
      mulByTwoCoordHom (W := E.toAffine) two_ne_zero := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change ι (dupHom E (AdjoinRoot.of _ (C c))) =
        mulByTwoCoordHom (W := E.toAffine) two_ne_zero (AdjoinRoot.of _ (C c))
      rw [dupHom, mulByTwoCoordHom, AdjoinRoot.lift_of, AdjoinRoot.lift_of]
      simp [ι_algebraMap_K]
    · change ι (dupHom E (AdjoinRoot.mk _ (C X))) =
        mulByTwoCoordHom (W := E.toAffine) two_ne_zero (AdjoinRoot.mk _ (C X))
      rw [dupHom_x, mulByTwoCoordHom_X, ι_x2B]
  · rw [RingHom.comp_apply, dupHom_y, mulByTwoCoordHom_root, ι_y2B]

/-- `[2]^*` is injective (`[2]` is dominant). -/
theorem dupHom_injective : Function.Injective (dupHom E) := by
  intro a b h
  apply mulByTwoCoordHom_injective (W := E.toAffine) (two_ne_zero (α := K))
  rw [← coe_dupHom, RingHom.comp_apply, RingHom.comp_apply, h]

/-! #### Identities in `B` -/

omit [CharZero K] in
lemma xB_eq : xB E = algebraMap K[X] (coverRingE E) X := by
  rw [IsScalarTower.algebraMap_apply K[X] E.toAffine.CoordinateRing (coverRingE E),
    AdjoinRoot.algebraMap_eq]
  rfl

omit [CharZero K] in
lemma algebraMap_polynomial_eq_aeval (p : K[X]) :
    algebraMap K[X] (coverRingE E) p = aeval (xB E) p := by
  rw [xB_eq, aeval_algebraMap_apply, aeval_X_left_apply]

omit [CharZero K] in
lemma psiB_sq : psiB E ^ 2 = aeval (xB E) E.Ψ₂Sq := by
  rw [← map_pow, psi_sq, ← IsScalarTower.algebraMap_apply, algebraMap_polynomial_eq_aeval]
  rfl

omit [CharZero K] in
lemma x2B_mul_psiB_sq : x2B E * psiB E ^ 2 = aeval (xB E) (E.Φ 2) := by
  rw [x2B]
  linear_combination aeval (xB E) (E.Φ 2) * (psiB E * invPsiB E + 1) * psiB_mul_invPsiB E

omit [CharZero K] in
/-- `1/ψ² = u(x) x(2P) + v(x)` for a Bézout identity `u Φ₂ + v Ψ₂Sq = 1`. -/
lemma exists_invPsiB_sq [E.IsElliptic] :
    ∃ a b : K[X], invPsiB E ^ 2 = aeval (xB E) a * x2B E + aeval (xB E) b := by
  obtain ⟨a, b, hab⟩ := E.isCoprime_Φ_two_Ψ₂Sq
  refine ⟨a, b, ?_⟩
  have h := congrArg (aeval (xB E)) hab
  rw [map_add, map_mul, map_mul, map_one, ← x2B_mul_psiB_sq, ← psiB_sq] at h
  linear_combination (-(invPsiB E ^ 2)) * h +
    (aeval (xB E) a * x2B E + aeval (xB E) b) * (psiB E * invPsiB E + 1) * psiB_mul_invPsiB E

omit [CharZero K] in
lemma psiB_eq : psiB E = 2 * yB E + algebraMap K (coverRingE E) E.a₁ * xB E +
    algebraMap K (coverRingE E) E.a₃ := by
  have h : psiE E = 2 * AdjoinRoot.root E.toAffine.polynomial +
      AdjoinRoot.of _ (C E.a₁) * AdjoinRoot.mk E.toAffine.polynomial (C X) +
      AdjoinRoot.of _ (C E.a₃) := by
    rw [psiE, WeierstrassCurve.Affine.polynomialY, ← AdjoinRoot.mk_X, ← AdjoinRoot.mk_C,
      ← AdjoinRoot.mk_C, ← map_ofNat (AdjoinRoot.mk E.toAffine.polynomial), ← map_mul,
      ← map_mul, ← map_add, ← map_add]
    congr 1
    simp only [map_ofNat, C_add, C_mul]
    ring
  rw [show psiB E = algebraMap _ (coverRingE E) _ from congrArg (algebraMap _ (coverRingE E)) h,
    map_add, map_add, map_mul, map_mul, map_ofNat]
  have hK : ∀ c : K, algebraMap E.toAffine.CoordinateRing (coverRingE E)
      (AdjoinRoot.of _ (C c)) = algebraMap K (coverRingE E) c := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K E.toAffine.CoordinateRing (coverRingE E)]
    rfl
  rw [hK, hK]

end Dup

/-! ### `B` as a `K[E]`-algebra via `[2]^*`: finiteness -/

section DupAlgebra

variable [CharZero K]

/-- `B = K[E][1/ψ]` regarded as a `K[E]`-algebra through `[2]^*`. -/
def DupB : Type u := coverRingE E

noncomputable instance : CommRing (DupB E) := inferInstanceAs (CommRing (coverRingE E))

instance : IsDomain (DupB E) := inferInstanceAs (IsDomain (coverRingE E))

noncomputable instance : Algebra K (DupB E) := inferInstanceAs (Algebra K (coverRingE E))

noncomputable instance : Algebra E.toAffine.CoordinateRing (DupB E) := (dupHom E).toAlgebra

instance : IsScalarTower K E.toAffine.CoordinateRing (DupB E) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (dupHom_algebraMap E c).symm

lemma algebraMap_dupB (a : E.toAffine.CoordinateRing) :
    algebraMap E.toAffine.CoordinateRing (DupB E) a = dupHom E a := rfl

/-- The identity `B → DupB`, changing the `K[E]`-algebra structure to the one via `[2]^*`. -/
noncomputable def toDupB : coverRingE E ≃ₐ[K] DupB E := AlgEquiv.refl

lemma algebraMap_dupB' (a : E.toAffine.CoordinateRing) :
    algebraMap E.toAffine.CoordinateRing (DupB E) a = toDupB E (dupHom E a) := rfl

/-- The coordinate `x` of `K[E]`. -/
noncomputable abbrev xE : E.toAffine.CoordinateRing := AdjoinRoot.mk E.toAffine.polynomial (C X)

local notation "A" => E.toAffine.CoordinateRing

lemma isIntegral_algebraMap_K (c : K) : IsIntegral A (toDupB E (algebraMap K _ c)) := by
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply K A (DupB E)]
  exact isIntegral_algebraMap

lemma isIntegral_xB [E.IsElliptic] : IsIntegral A (toDupB E (xB E)) := by
  refine ⟨(E.Φ 2).map (algebraMap K A) - C (xE E) * E.Ψ₂Sq.map (algebraMap K A), ?_, ?_⟩
  · refine Monic.sub_of_left ((show (E.Φ 2).Monic from E.leadingCoeff_Φ 2).map _) ?_
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    rw [degree_map, degree_map, degree_eq_natDegree (E.Φ_ne_zero 2),
      E.natDegree_Φ]
    exact (degree_le_natDegree.trans (WithBot.coe_le_coe.2 E.natDegree_Ψ₂Sq_le)).trans_lt
      (by norm_num)
  · have hc : ∀ p : K[X], eval₂ (algebraMap K (DupB E)) (toDupB E (xB E)) p =
        toDupB E (aeval (xB E) p) := fun p ↦ by
      rw [← aeval_def]
      exact aeval_algHom_apply (toDupB E).toAlgHom _ _
    rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_map, eval₂_map, ← IsScalarTower.algebraMap_eq,
      hc, hc, algebraMap_dupB', dupHom_x, ← map_mul, ← map_sub, ← x2B_mul_psiB_sq, psiB_sq,
      sub_self, map_zero]

lemma isIntegral_aeval_xB [E.IsElliptic] (p : K[X]) : IsIntegral A (toDupB E (aeval (xB E) p)) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C]; exact isIntegral_algebraMap_K E a
  | add p q hp hq => rw [map_add, map_add]; exact hp.add hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, map_mul]
    exact h.mul (isIntegral_xB E)

lemma isIntegral_x2B : IsIntegral A (toDupB E (x2B E)) := by
  rw [← dupHom_x, ← algebraMap_dupB']
  exact isIntegral_algebraMap

lemma isIntegral_invPsiB [E.IsElliptic] : IsIntegral A (toDupB E (invPsiB E)) := by
  obtain ⟨a, b, h⟩ := exists_invPsiB_sq E
  refine IsIntegral.of_pow two_pos ?_
  rw [← map_pow, h, map_add, map_mul]
  exact ((isIntegral_aeval_xB E a).mul (isIntegral_x2B E)).add (isIntegral_aeval_xB E b)

lemma isIntegral_psiB [E.IsElliptic] : IsIntegral A (toDupB E (psiB E)) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [← map_pow, psiB_sq]
  exact isIntegral_aeval_xB E _

lemma isIntegral_yB [E.IsElliptic] : IsIntegral A (toDupB E (yB E)) := by
  have h : (yB E : coverRingE E) = algebraMap K (coverRingE E) 2⁻¹ *
      (psiB E - algebraMap K (coverRingE E) E.a₁ * xB E - algebraMap K (coverRingE E) E.a₃) := by
    rw [psiB_eq]
    have : algebraMap K (coverRingE E) 2⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap K (coverRingE E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
        map_one]
    linear_combination (-yB E) * this
  rw [h, map_mul, map_sub, map_sub, map_mul]
  exact (isIntegral_algebraMap_K E _).mul (((isIntegral_psiB E).sub
    ((isIntegral_algebraMap_K E _).mul (isIntegral_xB E))).sub (isIntegral_algebraMap_K E _))

/-- The image of `K[E]` in `B` is integral over `K[E]` via `[2]^*`. -/
lemma isIntegral_algebraMap_coordinateRing [E.IsElliptic] (a : A) :
    IsIntegral A (toDupB E (algebraMap A (coverRingE E) a)) := by
  let S := integralClosure A (DupB E)
  let φ : A →+* DupB E := (toDupB E).toRingHom.comp (algebraMap A (coverRingE E))
  let f : K[X] →+* S := eval₂RingHom ((algebraMap A S).comp (algebraMap K A))
    ⟨toDupB E (xB E), isIntegral_xB E⟩
  have h1 : φ.comp (algebraMap K[X] A) = S.val.toRingHom.comp f := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp only [RingHom.comp_apply, f, coe_eval₂RingHom, eval₂_C]
      change toDupB E (algebraMap A (coverRingE E) (algebraMap K[X] A (C c))) =
        algebraMap A (DupB E) (algebraMap K A c)
      rw [algebraMap_dupB', dupHom_algebraMap, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K K[X] (coverRingE E)]
      rfl
    · simp only [RingHom.comp_apply, f, coe_eval₂RingHom, eval₂_X]
      rfl
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  have h2 : φ (AdjoinRoot.mk _ p) = S.val (p.eval₂ f ⟨toDupB E (yB E), isIntegral_yB E⟩) := by
    rw [← AdjoinRoot.aeval_eq, aeval_def, hom_eval₂, h1]
    exact (hom_eval₂ p f S.val.toRingHom ⟨toDupB E (yB E), isIntegral_yB E⟩).symm
  exact h2 ▸ (p.eval₂ f ⟨toDupB E (yB E), isIntegral_yB E⟩).2

instance [E.IsElliptic] : Algebra.IsIntegral A (DupB E) := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (psiE E) ((toDupB E).symm b)
  have hb : (toDupB E).symm b = algebraMap A (coverRingE E) a * invPsiB E ^ n := by
    rw [← h, mul_assoc, ← mul_pow, psiB_mul_invPsiB, one_pow, mul_one]
  rw [← (toDupB E).apply_symm_apply b, hb, map_mul, map_pow]
  exact (isIntegral_algebraMap_coordinateRing E a).mul ((isIntegral_invPsiB E).pow n)

instance [E.IsElliptic] : Module.Finite A (DupB E) :=
  haveI : Algebra.FiniteType K (DupB E) := inferInstanceAs (Algebra.FiniteType K (coverRingE E))
  haveI := Algebra.FiniteType.of_restrictScalars_finiteType K A (DupB E)
  Algebra.IsIntegral.finite

end DupAlgebra

/-! ### Differentials: `Ω_{B/K}` is free with basis `dx` -/

section Kaehler

open KaehlerDifferential

noncomputable instance : Algebra K[X] (DupB E) := inferInstanceAs (Algebra K[X] (coverRingE E))

instance : IsScalarTower K K[X] (DupB E) :=
  inferInstanceAs (IsScalarTower K K[X] (coverRingE E))

instance : Algebra.Etale K[X] (DupB E) := inferInstanceAs (Algebra.Etale K[X] (coverRingE E))

/-- `Ω[B⁄K] ≅ B`, `dx ↦ 1`: `B` is étale over `K[x]`. -/
noncomputable def kaehlerEquivB : Ω[DupB E⁄K] ≃ₗ[DupB E] DupB E :=
  (tensorKaehlerEquivOfFormallyEtale K K[X] (DupB E)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (DupB E) (DupB E))
      (polynomialEquiv K) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid K[X] (DupB E) (DupB E)

/-- `x` in `DupB`. -/
noncomputable abbrev xD : DupB E := algebraMap K[X] (DupB E) X

lemma toDupB_xB : toDupB E (xB E) = xD E := xB_eq E

lemma kaehlerEquivB_D_xD : kaehlerEquivB E (D K (DupB E) (xD E)) = 1 := by
  have h : tensorKaehlerEquivOfFormallyEtale K K[X] (DupB E) (1 ⊗ₜ D K K[X] X) =
      D K (DupB E) (xD E) := by
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D]
  rw [kaehlerEquivB, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← h,
    LinearEquiv.symm_apply_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    polynomialEquiv_D, derivative_X]
  simp

/-- The derivation `d/dx` of `B`. -/
noncomputable def deltaB : Derivation K (DupB E) (DupB E) :=
  (kaehlerEquivB E).toLinearMap.compDer (D K (DupB E))

lemma deltaB_xD : deltaB E (xD E) = 1 := kaehlerEquivB_D_xD E

/-- Every `K`-derivation `d` of `B` satisfies `d b = δ(b) • d x`. -/
lemma derivation_eq_deltaB_smul {M : Type*} [AddCommGroup M] [Module (DupB E) M] [Module K M]
    [IsScalarTower K (DupB E) M] (d : Derivation K (DupB E) M) (b : DupB E) :
    d b = deltaB E b • d (xD E) := by
  have hD : D K (DupB E) b = deltaB E b • D K (DupB E) (xD E) := by
    apply (kaehlerEquivB E).injective
    rw [map_smul, kaehlerEquivB_D_xD, smul_eq_mul, mul_one]
    rfl
  rw [← d.liftKaehlerDifferential_comp_D, hD, map_smul, d.liftKaehlerDifferential_comp_D]

lemma deltaB_aeval (p : K[X]) :
    deltaB E (toDupB E (aeval (xB E) p)) = toDupB E (aeval (xB E) (derivative p)) := by
  have hc : ∀ q : K[X], toDupB E (aeval (xB E) q) = aeval (toDupB E (xB E)) q := fun q ↦
    (aeval_algHom_apply (toDupB E).toAlgHom _ _).symm
  rw [hc, hc, toDupB_xB, Derivation.map_aeval, deltaB_xD, smul_eq_mul, mul_one]

end Kaehler

/-! ### Nonsingularity: `ψ` and `W_X` generate the unit ideal of `K[E]` -/

section Nonsingular

local notation "A" => E.toAffine.CoordinateRing

/-- The coordinate `y` of `K[E]`. -/
noncomputable abbrev yE : A := AdjoinRoot.root E.toAffine.polynomial

/-- `W_X = a₁ y - (3x² + 2a₂ x + a₄)` in `K[E]`. -/
noncomputable def wxE : A :=
  algebraMap K A E.a₁ * yE E -
    (3 * xE E ^ 2 + algebraMap K A (2 * E.a₂) * xE E + algebraMap K A E.a₄)

lemma psiE_eq' : psiE E = 2 * yE E + algebraMap K A E.a₁ * xE E + algebraMap K A E.a₃ := by
  change psiE E = 2 * AdjoinRoot.root E.toAffine.polynomial +
      AdjoinRoot.of _ (C E.a₁) * AdjoinRoot.mk E.toAffine.polynomial (C X) +
      AdjoinRoot.of _ (C E.a₃)
  rw [psiE, WeierstrassCurve.Affine.polynomialY, ← AdjoinRoot.mk_X, ← AdjoinRoot.mk_C,
    ← AdjoinRoot.mk_C, ← map_ofNat (AdjoinRoot.mk E.toAffine.polynomial), ← map_mul,
    ← map_mul, ← map_add, ← map_add]
  congr 1
  simp only [map_ofNat, C_add, C_mul]
  ring

/-- The Weierstrass equation in `K[E]`. -/
lemma equation_E : yE E ^ 2 + algebraMap K A E.a₁ * xE E * yE E + algebraMap K A E.a₃ * yE E -
    (xE E ^ 3 + algebraMap K A E.a₂ * xE E ^ 2 + algebraMap K A E.a₄ * xE E +
      algebraMap K A E.a₆) = 0 := by
  apply IsFractionRing.injective A E.toAffine.FunctionField
  have h := equation_gen (W := E.toAffine)
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, ← IsScalarTower.algebraMap_apply]
  change genY E.toAffine ^ 2 + _ * genX E.toAffine * genY E.toAffine + _ * genY E.toAffine -
    (genX E.toAffine ^ 3 + _ * genX E.toAffine ^ 2 + _ * genX E.toAffine + _) = 0
  linear_combination h

/-- **Nonsingularity**: `ψ` and `W_X` generate the unit ideal of `K[E]`. -/
theorem exists_mul_psiE_add_mul_wxE [E.IsElliptic] : ∃ c d : A, c * psiE E + d * wxE E = 1 := by
  by_contra hne
  have hI : Ideal.span {psiE E, wxE E} ≠ ⊤ := by
    intro h
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 (h ▸ Submodule.mem_top (x := (1 : A)))
    exact hne ⟨c, d, hcd⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  letI := Ideal.Quotient.field m
  let π : A →ₐ[K] A ⧸ m := Ideal.Quotient.mkₐ K m
  have hψ : π (psiE E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (hIm (Ideal.subset_span (by simp)))
  have hw : π (wxE E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (hIm (Ideal.subset_span (by simp)))
  have heq : (E.map (algebraMap K (A ⧸ m))).toAffine.Equation (π (xE E)) (π (yE E)) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have := congrArg π (equation_E E)
    simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_zero] at this
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination this
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular.1 heq)
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  rcases hns.2 with h | h
  · apply h
    rw [wxE] at hw
    simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_ofNat] at hw
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
    linear_combination hw
  · apply h
    rw [psiE_eq'] at hψ
    simp only [map_add, map_mul, AlgHom.commutes, map_ofNat] at hψ
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    linear_combination hψ

end Nonsingular

/-! ### `[2]` is unramified -/

section Unramified

variable [CharZero K]

local notation "A" => E.toAffine.CoordinateRing

lemma two_inv_mul_two : algebraMap K (coverRingE E) 2⁻¹ * 2 = 1 := by
  rw [← map_ofNat (algebraMap K (coverRingE E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]

/-- `[2]^* ψ = preΨ₄(x) / ψ³`. -/
lemma dupHom_psiE : dupHom E (psiE E) = aeval (xB E) E.preΨ₄ * invPsiB E ^ 3 := by
  rw [show dupHom E (psiE E) = dupHom E _ from congrArg (dupHom E) (psiE_eq' E), map_add,
    map_add, map_mul, map_mul, dupHom_y, dupHom_algebraMap,
    dupHom_algebraMap, map_ofNat, show dupHom E (xE E) = x2B E from dupHom_x E, x2B, y2B]
  set P := psiB E
  set U := invPsiB E
  linear_combination (aeval (xB E) E.preΨ₄ - P * (algebraMap K (coverRingE E) E.a₁ *
      aeval (xB E) (E.Φ 2) + algebraMap K (coverRingE E) E.a₃ * aeval (xB E) E.Ψ₂Sq)) * U ^ 3 *
      two_inv_mul_two E +
    (-(algebraMap K (coverRingE E) E.a₁ * aeval (xB E) (E.Φ 2) * U ^ 2) -
      algebraMap K (coverRingE E) E.a₃ * (P ^ 2 * U ^ 2 + P * U + 1)) * psiB_mul_invPsiB E +
    algebraMap K (coverRingE E) E.a₃ * P * U ^ 3 * psiB_sq E

lemma dupHom_psiE_ne_zero : dupHom E (psiE E) ≠ 0 :=
  (map_ne_zero_iff _ (dupHom_injective E)).2 (psiE_ne_zero E)

omit [CharZero K] in
/-- `δ([2]^* x) = 2 [2]^* ψ / ψ`: the invariant differential `dx/ψ` is multiplied by two. -/
lemma deltaB_x2B : deltaB E (toDupB E (x2B E)) =
    2 * toDupB E (aeval (xB E) E.preΨ₄) * toDupB E (invPsiB E) ^ 4 := by
  rw [x2B, map_mul, map_pow, sq, Derivation.leibniz, Derivation.leibniz, deltaB_aeval]
  simp only [smul_eq_mul]
  set P := toDupB E (psiB E)
  set U := toDupB E (invPsiB E)
  have h1 : P * U = 1 := by rw [← map_mul, psiB_mul_invPsiB, map_one]
  have h5 : P * P = toDupB E (aeval (xB E) E.Ψ₂Sq) := by rw [← map_mul, ← sq, psiB_sq]
  have h2 := congrArg (deltaB E) h5
  rw [Derivation.leibniz, deltaB_aeval, smul_eq_mul] at h2
  have h3 := congrArg (deltaB E) h1
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h3
  have hid := congrArg (fun p ↦ toDupB E (aeval (xB E) p)) (derivative_Φ_two_mul_sub E)
  simp only [map_sub, map_mul, map_ofNat] at hid
  have hdP2 : 2 * deltaB E P = toDupB E (aeval (xB E) (derivative E.Ψ₂Sq)) * U := by
    linear_combination U * h2 - 2 * deltaB E P * h1
  have hdU : deltaB E U = -(U ^ 2 * deltaB E P) := by
    linear_combination U * h3 - deltaB E U * h1
  linear_combination 2 * toDupB E (aeval (xB E) (E.Φ 2)) * U * hdU -
    toDupB E (aeval (xB E) (E.Φ 2)) * U ^ 3 * hdP2 + U ^ 4 * hid -
    toDupB E (aeval (xB E) (derivative (E.Φ 2))) * U ^ 2 * (P * U + 1) * h1 +
    toDupB E (aeval (xB E) (derivative (E.Φ 2))) * U ^ 4 * h5

/-- `δ([2]^* y) = -2 [2]^* W_X / ψ`, from the Weierstrass equation at the doubled point. -/
lemma deltaB_y2B : deltaB E (toDupB E (y2B E)) =
    -(2 * toDupB E (dupHom E (wxE E)) * toDupB E (invPsiB E)) := by
  have heq := congrArg (fun a ↦ toDupB E (dupHom E a)) (equation_E E)
  simp only [map_sub, map_add, map_mul, map_pow, dupHom_algebraMap, map_zero,
    AlgEquiv.commutes] at heq
  rw [show dupHom E (yE E) = y2B E from dupHom_y E,
    show dupHom E (xE E) = x2B E from dupHom_x E] at heq
  have hd := congrArg (deltaB E) heq
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, smul_eq_mul, map_zero, nsmul_eq_mul] at hd
  have hψ := congrArg (fun a ↦ toDupB E (dupHom E a)) (psiE_eq' E)
  simp only [map_add, map_mul, dupHom_algebraMap, map_ofNat, AlgEquiv.commutes] at hψ
  rw [show dupHom E (yE E) = y2B E from dupHom_y E,
    show dupHom E (xE E) = x2B E from dupHom_x E, dupHom_psiE, map_mul, map_pow] at hψ
  have hx := deltaB_x2B E
  have hne : toDupB E (dupHom E (psiE E)) ≠ 0 := by
    rw [map_ne_zero_iff _ (toDupB E).injective]; exact dupHom_psiE_ne_zero E
  have hwx : toDupB E (dupHom E (wxE E)) = algebraMap K (DupB E) E.a₁ * toDupB E (y2B E) -
      (3 * toDupB E (x2B E) ^ 2 + algebraMap K (DupB E) (2 * E.a₂) * toDupB E (x2B E) +
        algebraMap K (DupB E) E.a₄) := by
    rw [wxE]
    simp only [map_sub, map_add, map_mul, map_pow, dupHom_algebraMap, map_ofNat,
      AlgEquiv.commutes]
    rw [show dupHom E (yE E) = y2B E from dupHom_y E,
      show dupHom E (xE E) = x2B E from dupHom_x E]
  have key : toDupB E (dupHom E (psiE E)) * (deltaB E (toDupB E (y2B E)) +
      2 * toDupB E (dupHom E (wxE E)) * toDupB E (invPsiB E)) = 0 := by
    rw [hwx, dupHom_psiE, map_mul, map_pow]
    simp only [map_mul, map_ofNat, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      show (3 : ℕ) - 1 = 2 from rfl, pow_one] at hd ⊢
    linear_combination hd + deltaB E (toDupB E (y2B E)) * hψ -
      (algebraMap K (DupB E) E.a₁ * toDupB E (y2B E) -
      (3 * toDupB E (x2B E) ^ 2 + 2 * algebraMap K (DupB E) E.a₂ * toDupB E (x2B E) +
        algebraMap K (DupB E) E.a₄)) * hx
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 key).resolve_left hne)

/-- **`[2]` is unramified**: `Ω_{B/K[E]} = 0`. -/
instance [E.IsElliptic] : Algebra.FormallyUnramified A (DupB E) := by
  rw [Algebra.formallyUnramified_iff]
  let d : Derivation K (DupB E) Ω[DupB E⁄A] :=
    (KaehlerDifferential.D A (DupB E)).restrictScalars K
  have hx2 : d (toDupB E (x2B E)) = 0 := by
    rw [← dupHom_x, ← algebraMap_dupB']
    exact (KaehlerDifferential.D A (DupB E)).map_algebraMap _
  have hy2 : d (toDupB E (y2B E)) = 0 := by
    rw [← dupHom_y, ← algebraMap_dupB']
    exact (KaehlerDifferential.D A (DupB E)).map_algebraMap _
  rw [derivation_eq_deltaB_smul, deltaB_x2B] at hx2
  rw [derivation_eq_deltaB_smul, deltaB_y2B] at hy2
  have h2 : algebraMap K (DupB E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap K (DupB E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  set P := toDupB E (psiB E)
  set U := toDupB E (invPsiB E)
  set i2 := algebraMap K (DupB E) 2⁻¹
  have h1 : P * U = 1 := by rw [← map_mul, psiB_mul_invPsiB, map_one]
  have hψ : toDupB E (dupHom E (psiE E)) = toDupB E (aeval (xB E) E.preΨ₄) * U ^ 3 := by
    rw [dupHom_psiE, map_mul, map_pow]
  have hpsi : toDupB E (dupHom E (psiE E)) • d (xD E) = 0 := by
    have hs : (i2 * P) * (2 * toDupB E (aeval (xB E) E.preΨ₄) * U ^ 4) =
        toDupB E (dupHom E (psiE E)) := by
      rw [hψ]
      linear_combination (toDupB E (aeval (xB E) E.preΨ₄) * U ^ 3 * P * U) * h2 +
        toDupB E (aeval (xB E) E.preΨ₄) * U ^ 3 * h1
    rw [← hs, ← smul_smul, hx2, smul_zero]
  have hwx : toDupB E (dupHom E (wxE E)) • d (xD E) = 0 := by
    have hs : -(i2 * P) * -(2 * toDupB E (dupHom E (wxE E)) * U) =
        toDupB E (dupHom E (wxE E)) := by
      linear_combination (toDupB E (dupHom E (wxE E)) * P * U) * h2 +
        toDupB E (dupHom E (wxE E)) * h1
    rw [← hs, ← smul_smul, hy2, smul_zero]
  obtain ⟨c, e, hce⟩ := exists_mul_psiE_add_mul_wxE E
  have hce' := congrArg (fun a ↦ toDupB E (dupHom E a)) hce
  simp only [map_add, map_mul, map_one] at hce'
  have hxD : d (xD E) = 0 := by
    rw [← one_smul (DupB E) (d (xD E)), ← hce', add_smul, mul_smul, mul_smul, hpsi, hwx,
      smul_zero, smul_zero, add_zero]
  refine subsingleton_of_forall_eq 0 fun ω ↦ ?_
  have hω : ω ∈ Submodule.span (DupB E) (Set.range (KaehlerDifferential.D A (DupB E))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction (fun _ ⟨b, hb⟩ ↦ ?_) rfl (fun _ _ _ _ h h' ↦ by
    rw [h, h', add_zero]) (fun a _ _ h ↦ by rw [h, smul_zero]) hω
  rw [← hb]
  change d b = 0
  rw [derivation_eq_deltaB_smul, hxD, smul_zero]

/-- **`[2]` is flat**: `K[E]` is a Dedekind domain and `B` is torsion-free. -/
instance [E.IsElliptic] : Module.Flat A (DupB E) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
  refine eq_bot_iff.2 fun b hb ↦ ?_
  obtain ⟨⟨a, ha⟩, hab⟩ := (Submodule.mem_torsion_iff b).1 hb
  rw [Submodule.mem_bot]
  rw [Submonoid.smul_def, Algebra.smul_def, algebraMap_dupB'] at hab
  refine (mul_eq_zero.1 hab).resolve_left ?_
  exact (map_ne_zero_iff _ (toDupB E).injective).2
    ((map_ne_zero_iff _ (dupHom_injective E)).2 (nonZeroDivisors.ne_zero ha))

instance [E.IsElliptic] : Algebra.Etale A (DupB E) :=
  haveI : Algebra.FinitePresentation A (DupB E) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  Algebra.Etale.of_formallyUnramified_of_flat

/-- **`[2] : E ∖ E[2] → E ∖ {O}` is finite étale.** -/
theorem isFiniteEtale_spec_dupHom [E.IsElliptic] :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (dupHom E))) := by
  have : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap A (DupB E)))) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
    exact ⟨⟩
  exact this

end Unramified

end CurvesJacobian.Cusp
