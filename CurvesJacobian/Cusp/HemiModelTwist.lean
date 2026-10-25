/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The `F_mod`-model of the hemi-elliptic orbicurve: twists and `x`-coordinates (MR8)

IUT I Def. 3.1(b) / Rem. 3.1.7(i): the hemi-elliptic orbicurve `C_F = X_F / ±1` has a model over
the field of moduli `F_mod = ℚ(j(E))`. Its coarse space is the `x`-line, which only sees `E` up to
quadratic twist. This file proves the algebraic fact behind this: if `E`, `E'` are elliptic curves
over a field `F` of characteristic `0` with `j(E) = j(E') ∉ {0, 1728}`, then every variable change
`C` over `F̄ = AlgebraicClosure F` with `C • E'_{F̄} = E_{F̄}` (which exists by Mathlib's
`WeierstrassCurve.exists_variableChange_of_j_eq`) has `C.u ^ 2 ∈ F` and `C.r ∈ F`, i.e. the
`x`-coordinates are related by the `F`-rational affine change `x' = u2 • x + r`.

## Main statements

* `CurvesJacobian.Cusp.variableChange_aut_twist₃`: for `j ≠ 0, 1728` (and `12` invertible), an
  automorphism `D • E = E` has `D.u ^ 2 = 1` and `D.r = 0`.
* `CurvesJacobian.Cusp.forall_variableChange_xrat₃`,
  `CurvesJacobian.Cusp.exists_variableChange_xrat₃`: the rationality of `u ^ 2` and `r`.
* `CurvesJacobian.Cusp.Ψ₂Sq_comp_variableChange₃`: transformation law
  `W.Ψ₂Sq.comp (u² X + r) = u⁶ • (C • W).Ψ₂Sq` of the `2`-division polynomial.
* `CurvesJacobian.Cusp.exists_Ψ₂Sq_comp_xrat₃`: over `F`,
  `E'.Ψ₂Sq.comp (u2 X + r) = u2 ^ 3 • E.Ψ₂Sq` with `u2 ≠ 0`, `u2, r ∈ F`.
* `CurvesJacobian.Cusp.exists_ofJ_model₃`: `WeierstrassCurve.ofJ j` is an elliptic model over
  `k` with `j`-invariant `j` (also after base change to any `k`-algebra field).

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 (Table 3.1), III.10.
-/

namespace CurvesJacobian.Cusp

open WeierstrassCurve Polynomial

section Aut

variable {K : Type*} [Field K]

/-- For an elliptic curve with `j ≠ 0`, `c₄ ≠ 0`. -/
lemma c₄_ne_zero_of_j_ne_zero₃ (E : WeierstrassCurve K) [E.IsElliptic] (h0 : E.j ≠ 0) :
    E.c₄ ≠ 0 := by
  intro h
  apply h0
  rw [WeierstrassCurve.j, h]
  ring

/-- For an elliptic curve with `j ≠ 1728`, `c₆ ≠ 0`. -/
lemma c₆_ne_zero_of_j_ne_1728₃ (E : WeierstrassCurve K) [E.IsElliptic] (h1728 : E.j ≠ 1728) :
    E.c₆ ≠ 0 := by
  intro h
  apply h1728
  have hrel := E.c_relation
  rw [h] at hrel
  have hΔ : (E.Δ'⁻¹ : Kˣ).val * E.Δ = 1 := by
    rw [← E.coe_Δ']
    exact Units.inv_mul _
  rw [WeierstrassCurve.j]
  linear_combination (-(E.Δ'⁻¹ : Kˣ).val) * hrel + 1728 * hΔ

/-- Automorphisms of an elliptic curve with `j ≠ 0, 1728` (in a field where `12 ≠ 0`) are `±1`
on the `x`-line: `D • E = E` forces `D.u ^ 2 = 1` and `D.r = 0` (Silverman III.10.1). -/
theorem variableChange_aut_twist₃ (E : WeierstrassCurve K) [E.IsElliptic] (h0 : E.j ≠ 0)
    (h1728 : E.j ≠ 1728) (h12 : (12 : K) ≠ 0) (D : VariableChange K) (hD : D • E = E) :
    (D.u : K) ^ 2 = 1 ∧ D.r = 0 := by
  have hc4 := c₄_ne_zero_of_j_ne_zero₃ E h0
  have hc6 := c₆_ne_zero_of_j_ne_1728₃ E h1728
  have e4 : E.c₄ = (D.u⁻¹ : Kˣ).val ^ 4 * E.c₄ := by
    conv_lhs => rw [← hD]
    exact variableChange_c₄ E D
  have e6 : E.c₆ = (D.u⁻¹ : Kˣ).val ^ 6 * E.c₆ := by
    conv_lhs => rw [← hD]
    exact variableChange_c₆ E D
  have v4 : (D.u⁻¹ : Kˣ).val ^ 4 = 1 := by
    have := mul_right_cancel₀ hc4 (e4.symm.trans (one_mul E.c₄).symm)
    exact this
  have v6 : (D.u⁻¹ : Kˣ).val ^ 6 = 1 := by
    have := mul_right_cancel₀ hc6 (e6.symm.trans (one_mul E.c₆).symm)
    exact this
  have v2 : (D.u⁻¹ : Kˣ).val ^ 2 = 1 := by
    linear_combination v6 - (D.u⁻¹ : Kˣ).val ^ 2 * v4
  have huv : (D.u : K) * (D.u⁻¹ : Kˣ).val = 1 := Units.mul_inv _
  have hu2 : (D.u : K) ^ 2 = 1 := by
    linear_combination (1 + (D.u : K) * (D.u⁻¹ : Kˣ).val) * huv - (D.u : K) ^ 2 * v2
  refine ⟨hu2, ?_⟩
  have e2 : E.b₂ = (D.u⁻¹ : Kˣ).val ^ 2 * (E.b₂ + 12 * D.r) := by
    conv_lhs => rw [← hD]
    exact variableChange_b₂ E D
  have h12r : 12 * D.r = 0 := by
    rw [v2, one_mul] at e2
    linear_combination -e2
  exact (mul_eq_zero.mp h12r).resolve_left h12

end Aut

section TransformationLaw

variable {R : Type*} [CommRing R]

/-- Transformation law of the `2`-division polynomial under the variable change
`x = u² x' + r`: `W.Ψ₂Sq (u² X + r) = u⁶ (C • W).Ψ₂Sq (X)`. -/
theorem Ψ₂Sq_comp_variableChange₃ (W : WeierstrassCurve R) (C : VariableChange R) :
    W.Ψ₂Sq.comp (Polynomial.C ((C.u : R) ^ 2) * X + Polynomial.C C.r) =
      Polynomial.C ((C.u : R) ^ 6) * (C • W).Ψ₂Sq := by
  have huv : (C.u : R) * (C.u⁻¹ : Rˣ).val = 1 := Units.mul_inv _
  have h2 : (C.u : R) ^ 6 * (C • W).b₂ = (C.u : R) ^ 4 * (W.b₂ + 12 * C.r) := by
    rw [variableChange_b₂]
    linear_combination
      ((C.u : R) ^ 4 * (W.b₂ + 12 * C.r) * ((C.u : R) * (C.u⁻¹ : Rˣ).val + 1)) * huv
  have h4 : (C.u : R) ^ 6 * (2 * (C • W).b₄) =
      (C.u : R) ^ 2 * (2 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)) := by
    rw [variableChange_b₄]
    linear_combination ((C.u : R) ^ 2 * (2 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)) *
      ((C.u : R) * (C.u⁻¹ : Rˣ).val + 1) * (((C.u : R) * (C.u⁻¹ : Rˣ).val) ^ 2 + 1)) * huv
  have h6 : (C.u : R) ^ 6 * (C • W).b₆ =
      W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3 := by
    rw [variableChange_b₆]
    linear_combination ((W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) *
      (((C.u : R) * (C.u⁻¹ : Rˣ).val) ^ 5 + ((C.u : R) * (C.u⁻¹ : Rˣ).val) ^ 4 +
        ((C.u : R) * (C.u⁻¹ : Rˣ).val) ^ 3 + ((C.u : R) * (C.u⁻¹ : Rˣ).val) ^ 2 +
        (C.u : R) * (C.u⁻¹ : Rˣ).val + 1)) * huv
  have hR : Polynomial.C ((C.u : R) ^ 6) * (C • W).Ψ₂Sq =
      Polynomial.C (4 * (C.u : R) ^ 6) * X ^ 3 +
        Polynomial.C ((C.u : R) ^ 4 * (W.b₂ + 12 * C.r)) * X ^ 2 +
        Polynomial.C ((C.u : R) ^ 2 * (2 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2))) * X +
        Polynomial.C (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) := by
    rw [← h2, ← h4, ← h6, Ψ₂Sq]
    simp only [map_mul]
    ring
  rw [hR, Ψ₂Sq]
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

end TransformationLaw

section BaseChange

variable {k : Type*} [Field k] {A : Type*} [Field A] [Algebra k A]

/-- Base change of an elliptic curve is elliptic (Mathlib has this for `map`). -/
theorem isElliptic_baseChangeTw₃ (E : WeierstrassCurve k) [E.IsElliptic] :
    (E.baseChange A).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k A)).IsElliptic

attribute [local instance] isElliptic_baseChangeTw₃

/-- The `j`-invariant of a base change. -/
theorem j_baseChangeTw₃ (E : WeierstrassCurve k) [E.IsElliptic] :
    (E.baseChange A).j = algebraMap k A E.j :=
  map_j E (algebraMap k A)

end BaseChange

attribute [local instance] isElliptic_baseChangeTw₃

section Twist

variable {F : Type*} [Field F]

local notation "F̄" => AlgebraicClosure F

/-- Base change of a curve over `F` to `F̄` is fixed by every `σ ∈ Gal(F̄/F)`. -/
lemma baseChange_map_gal₃ (E : WeierstrassCurve F) (σ : F̄ ≃ₐ[F] F̄) :
    (E.baseChange F̄).map (σ : F̄ →+* F̄) = E.baseChange F̄ :=
  WeierstrassCurve.map_baseChange E (σ : F̄ →ₐ[F] F̄)

/-- **`x`-rationality of twists.** Let `F` have characteristic `0` and let `E`, `E'` be elliptic
curves over `F` with `j(E) = j(E') ∉ {0, 1728}`. Then every variable change `C` over `F̄` with
`C • E'_{F̄} = E_{F̄}` has `C.u ^ 2 ∈ F` and `C.r ∈ F`. -/
theorem forall_variableChange_xrat₃ [CharZero F] (E E' : WeierstrassCurve F) [E.IsElliptic]
    (h0 : E.j ≠ 0) (h1728 : E.j ≠ 1728) (C : VariableChange F̄)
    (hC : C • E'.baseChange F̄ = E.baseChange F̄) :
    ∃ u2 r : F, (C.u : F̄) ^ 2 = algebraMap F F̄ u2 ∧ C.r = algebraMap F F̄ r := by
  have hinj : Function.Injective (algebraMap F F̄) := (algebraMap F F̄).injective
  have hj0 : (E.baseChange F̄).j ≠ 0 := by
    rw [j_baseChangeTw₃]
    exact fun h => h0 (hinj (h.trans (map_zero _).symm))
  have hj1728 : (E.baseChange F̄).j ≠ 1728 := by
    rw [j_baseChangeTw₃]
    exact fun h => h1728 (hinj (h.trans (map_ofNat _ 1728).symm))
  have h12 : (12 : F̄) ≠ 0 := by
    exact_mod_cast (by norm_num : (12 : ℕ) ≠ 0)
  have hinv : C⁻¹ • E.baseChange F̄ = E'.baseChange F̄ := by
    rw [← hC, inv_smul_smul]
  have key : ∀ σ : F̄ ≃ₐ[F] F̄, σ ((C.u : F̄) ^ 2) = (C.u : F̄) ^ 2 ∧ σ C.r = C.r := by
    intro σ
    have hσ : C.map (σ : F̄ →+* F̄) • E'.baseChange F̄ = E.baseChange F̄ := by
      have h1 := map_variableChange (E'.baseChange F̄) C (σ : F̄ →+* F̄)
      rw [baseChange_map_gal₃, hC, baseChange_map_gal₃] at h1
      exact h1
    have hD : (C.map (σ : F̄ →+* F̄) * C⁻¹) • E.baseChange F̄ = E.baseChange F̄ := by
      rw [mul_smul, hinv, hσ]
    obtain ⟨hu, hr⟩ := variableChange_aut_twist₃ (E.baseChange F̄) hj0 hj1728 h12 _ hD
    have hDu : ((C.map (σ : F̄ →+* F̄) * C⁻¹).u : F̄) = σ (C.u : F̄) * (C.u⁻¹ : F̄ˣ).val := rfl
    have hDr : (C.map (σ : F̄ →+* F̄) * C⁻¹).r =
        σ C.r * (C.u⁻¹ : F̄ˣ).val ^ 2 + -C.r * (C.u⁻¹ : F̄ˣ).val ^ 2 := rfl
    rw [hDu] at hu
    rw [hDr] at hr
    have huv : (C.u : F̄) * (C.u⁻¹ : F̄ˣ).val = 1 := Units.mul_inv _
    refine ⟨?_, ?_⟩
    · rw [map_pow]
      linear_combination (C.u : F̄) ^ 2 * hu - (σ (C.u : F̄)) ^ 2 *
        ((C.u : F̄) * (C.u⁻¹ : F̄ˣ).val + 1) * huv
    · linear_combination (C.u : F̄) ^ 2 * hr - (σ C.r - C.r) *
        ((C.u : F̄) * (C.u⁻¹ : F̄ˣ).val + 1) * huv
  obtain ⟨u2, hu2⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F)
    ((C.u : F̄) ^ 2)).mpr fun σ => (key σ).1
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) C.r).mpr
    fun σ => (key σ).2
  exact ⟨u2, r, hu2.symm, hr.symm⟩

/-- Existence form: there is a variable change `C` over `F̄` with `C • E'_{F̄} = E_{F̄}`
(Mathlib `exists_variableChange_of_j_eq`) and `C.u ^ 2`, `C.r` lie in `F`. -/
theorem exists_variableChange_xrat₃ [CharZero F] (E E' : WeierstrassCurve F) [E.IsElliptic]
    [E'.IsElliptic] (hj : E.j = E'.j) (h0 : E.j ≠ 0) (h1728 : E.j ≠ 1728) :
    ∃ C : VariableChange F̄, C • E'.baseChange F̄ = E.baseChange F̄ ∧
      ∃ u2 r : F, (C.u : F̄) ^ 2 = algebraMap F F̄ u2 ∧ C.r = algebraMap F F̄ r := by
  have hj' : (E'.baseChange F̄).j = (E.baseChange F̄).j := by
    rw [j_baseChangeTw₃, j_baseChangeTw₃, hj]
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq (E'.baseChange F̄) (E.baseChange F̄) hj'
  exact ⟨C, hC, forall_variableChange_xrat₃ E E' h0 h1728 C hC⟩

/-- The `F`-rational `x`-coordinate change on `2`-division polynomials: if `C • E'_{F̄} = E_{F̄}`
with `C.u ^ 2 = u2`, `C.r = r` in `F`, then `E'.Ψ₂Sq (u2 X + r) = u2 ³ E.Ψ₂Sq (X)` over `F`. -/
theorem Ψ₂Sq_comp_xrat₃ (E E' : WeierstrassCurve F) (C : VariableChange F̄)
    (hC : C • E'.baseChange F̄ = E.baseChange F̄) (u2 r : F)
    (hu2 : (C.u : F̄) ^ 2 = algebraMap F F̄ u2) (hr : C.r = algebraMap F F̄ r) :
    E'.Ψ₂Sq.comp (Polynomial.C u2 * X + Polynomial.C r) = Polynomial.C (u2 ^ 3) * E.Ψ₂Sq := by
  apply Polynomial.map_injective (algebraMap F F̄) (algebraMap F F̄).injective
  have h := Ψ₂Sq_comp_variableChange₃ (E'.baseChange F̄) C
  rw [hC, hu2, hr, show (C.u : F̄) ^ 6 = ((C.u : F̄) ^ 2) ^ 3 by ring, hu2] at h
  have hb : ∀ W : WeierstrassCurve F, (W.baseChange F̄).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F F̄) :=
    fun W => map_Ψ₂Sq W (algebraMap F F̄)
  rw [hb, hb] at h
  rw [Polynomial.map_comp, Polynomial.map_mul]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow, map_pow] at h ⊢
  exact h

/-- Combined `F`-rational form: for `j(E) = j(E') ∉ {0, 1728}` in characteristic `0` there are
`u2 ≠ 0` and `r` in `F` with `E'.Ψ₂Sq (u2 X + r) = u2 ³ E.Ψ₂Sq (X)`. -/
theorem exists_Ψ₂Sq_comp_xrat₃ [CharZero F] (E E' : WeierstrassCurve F) [E.IsElliptic]
    [E'.IsElliptic] (hj : E.j = E'.j) (h0 : E.j ≠ 0) (h1728 : E.j ≠ 1728) :
    ∃ u2 r : F, u2 ≠ 0 ∧
      E'.Ψ₂Sq.comp (Polynomial.C u2 * X + Polynomial.C r) = Polynomial.C (u2 ^ 3) * E.Ψ₂Sq := by
  obtain ⟨C, hC, u2, r, hu2, hr⟩ := exists_variableChange_xrat₃ E E' hj h0 h1728
  refine ⟨u2, r, ?_, Ψ₂Sq_comp_xrat₃ E E' C hC u2 r hu2 hr⟩
  rintro rfl
  rw [map_zero] at hu2
  exact C.u.ne_zero (pow_eq_zero_iff two_ne_zero |>.mp hu2)

end Twist

section Model

/-- The model `WeierstrassCurve.ofJ j` over `k` (Mathlib `ModelsWithJ`): it is elliptic and has
`j`-invariant `j`, also after base change to any field extension `F` of `k`. -/
theorem exists_ofJ_model₃ {k : Type*} [Field k] [DecidableEq k] (j : k) (F : Type*) [Field F]
    [Algebra k F] :
    (WeierstrassCurve.ofJ j).IsElliptic ∧ (WeierstrassCurve.ofJ j).j = j ∧
      ((WeierstrassCurve.ofJ j).baseChange F).IsElliptic ∧
      ((WeierstrassCurve.ofJ j).baseChange F).j = algebraMap k F j := by
  refine ⟨inferInstance, ofJ_j j, isElliptic_baseChangeTw₃ _, ?_⟩
  rw [j_baseChangeTw₃, ofJ_j]

end Model

end CurvesJacobian.Cusp
