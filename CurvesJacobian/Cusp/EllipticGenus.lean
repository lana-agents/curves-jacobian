/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Belyi.Anabelian.LocAn
import CurvesJacobian.Cusp.CoverGenus

/-!
# The invariant differential `dx/ψ` is regular: curves with a Weierstrass model have genus `≥ 1`

Let `E : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` be an elliptic curve over a field `k` of
characteristic zero and let `x, y` be elements of a field `F ⊇ k` satisfying the Weierstrass
equation, with `ψ = 2y + a₁x + a₃ ≠ 0`. Put `ω = dx/ψ ∈ Ω_{F/k}` (the invariant differential).

**Local regularity** (`CurvesJacobian.Cusp.invariantDifferential_mem_range`): for every valuation
ring `R ⊆ F` containing `k` with fraction field `F`, `ω` lies in the image of `Ω_{R/k}`.

* If `x ∈ R`, then `y ∈ R` (it is integral over `R[x]`), and the residues `(x̄, ȳ)` are a point of
  `E` over the residue field, which is nonsingular (`Δ ≠ 0`); so `ψ` or
  `W_X = a₁y - (3x² + 2a₂x + a₄)` is a unit of `R`, and `ω = dx/ψ = -dy/W_X` (from
  `ψ dy + W_X dx = 0`).
* If `x ∉ R`, then `z = 1/x` lies in the maximal ideal; `t = x/y` lies in `R` (from
  `t² (1 + a₂z + a₄z² + a₆z³) = z (1 + a₁t + a₃zt)`) and `ω = h dt` with the unit
  `h = U / ((1 + a₁t + a₃zt)(-1 + a₄z² + 2a₆z³) - a₃ztU)`, `U = 1 + a₂z + a₄z² + a₆z³`.

**Genus** (`CurvesJacobian.Cusp.one_le_curveGenus_of_weierstrass`): if `X` is a curve over `k`
whose function field contains such `x, y` with `dx ≠ 0`, then `ω` is a nonzero global regular
differential (every stalk of a curve is a valuation ring of `K(X)`), so the genus
`dim_k H⁰(X, Ω¹)` is at least one.
-/

open Polynomial KaehlerDifferential

universe u v w

namespace CurvesJacobian.Cusp

section Local

variable {k : Type u} {R : Type v} {F : Type w} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [ValuationRing R] [Field F] [Algebra k R] [Algebra R F] [Algebra k F] [IsScalarTower k R F]
  [IsFractionRing R F] (W : WeierstrassCurve k) [W.IsElliptic] {x y : F}

local notation "↑ₖ" => algebraMap k F

/-- The Weierstrass equation for `x, y ∈ F`. -/
def WEq (W : WeierstrassCurve k) (x y : F) : Prop :=
  y ^ 2 + ↑ₖ W.a₁ * x * y + ↑ₖ W.a₃ * y =
    x ^ 3 + ↑ₖ W.a₂ * x ^ 2 + ↑ₖ W.a₄ * x + ↑ₖ W.a₆

omit [CharZero k] [W.IsElliptic] in
/-- `ψ dy + W_X dx = 0`. -/
lemma psi_smul_D_add (h : WEq W x y) :
    (2 * y + ↑ₖ W.a₁ * x + ↑ₖ W.a₃) • D k F y +
      (↑ₖ W.a₁ * y - (3 * x ^ 2 + 2 * ↑ₖ W.a₂ * x + ↑ₖ W.a₄)) • D k F x = 0 := by
  have h' := congrArg (D k F) h
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    smul_zero, add_zero] at h'
  simp only [show (2 : ℕ) - 1 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl, pow_one] at h'
  rw [← sub_eq_zero] at h'
  linear_combination (norm := module) h'

omit [CharZero k] in
/-- A root of a monic quadratic over a valuation ring `R` lies in `R`. -/
lemma exists_eq_of_quadratic {f : F} (b c : R)
    (h : f ^ 2 + algebraMap R F b * f + algebraMap R F c = 0) :
    ∃ f' : R, algebraMap R F f' = f := by
  rcases ValuationRing.isInteger_or_isInteger R f with hf | hf
  · exact hf
  obtain ⟨s, hs⟩ := hf
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, map_zero]⟩
  have hfs : f * algebraMap R F s = 1 := by rw [hs, mul_inv_cancel₀ hf0]
  have hu : s * -(b + c * s) = 1 := by
    apply IsFractionRing.injective R F
    simp only [map_mul, map_neg, map_add, map_one]
    linear_combination (-(algebraMap R F s) ^ 2) * h +
      (f * algebraMap R F s + 1 + algebraMap R F b * algebraMap R F s) * hfs
  refine ⟨-(b + c * s), ?_⟩
  have := congrArg (algebraMap R F) hu
  rw [map_mul, map_one] at this
  rw [← mul_one (algebraMap R F _), ← hfs]
  linear_combination f * this

omit [CharZero k] [IsFractionRing R F] in
lemma isUnit_one_add_of_mem {w : R} (hw : w ∈ IsLocalRing.maximalIdeal R) : IsUnit (1 + w) := by
  have : -w ∈ nonunits R := (IsLocalRing.maximalIdeal R).neg_mem_iff.2 hw
  simpa [sub_eq_add_neg] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ this

omit [CharZero k] [IsDomain R] [ValuationRing R] [IsFractionRing R F] in
lemma mem_range_of_eq {ω : Ω[F⁄k]} (a r : R)
    (h : ω = algebraMap R F a • D k F (algebraMap R F r)) :
    ω ∈ LinearMap.range (KaehlerDifferential.map k k R F) :=
  ⟨a • D k R r, by rw [map_smul, map_D, h, algebraMap_smul]⟩

omit [CharZero k] in
/-- **The invariant differential `dx/ψ` is regular at every valuation ring.** -/
theorem invariantDifferential_mem_range (h : WEq W x y)
    (hψ : 2 * y + ↑ₖ W.a₁ * x + ↑ₖ W.a₃ ≠ 0) :
    (2 * y + ↑ₖ W.a₁ * x + ↑ₖ W.a₃)⁻¹ • D k F x ∈
      LinearMap.range (KaehlerDifferential.map k k R F) := by
  have hrel := psi_smul_D_add W h
  have hk : ∀ c : k, algebraMap R F (algebraMap k R c) = ↑ₖ c := fun c ↦
    (IsScalarTower.algebraMap_apply k R F c).symm
  by_cases hx : ∃ x' : R, algebraMap R F x' = x
  · obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := exists_eq_of_quadratic (f := y)
      (algebraMap k R W.a₁ * x' + algebraMap k R W.a₃)
      (-(x' ^ 3 + algebraMap k R W.a₂ * x' ^ 2 + algebraMap k R W.a₄ * x' + algebraMap k R W.a₆))
      (by simp only [map_add, map_mul, map_neg, map_pow, hk]; rw [WEq] at h; linear_combination h)
    have hR : y' ^ 2 + algebraMap k R W.a₁ * x' * y' + algebraMap k R W.a₃ * y' =
        x' ^ 3 + algebraMap k R W.a₂ * x' ^ 2 + algebraMap k R W.a₄ * x' + algebraMap k R W.a₆ := by
      apply IsFractionRing.injective R F
      simp only [map_add, map_mul, map_pow, hk]
      exact h
    let π := IsLocalRing.residue R
    have heq : (W.map (algebraMap k (IsLocalRing.ResidueField R))).toAffine.Equation (π x')
        (π y') := by
      rw [WeierstrassCurve.Affine.equation_iff]
      have := congrArg π hR
      simp only [map_add, map_mul, map_pow] at this
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
        IsScalarTower.algebraMap_apply k R (IsLocalRing.ResidueField R)]
      exact this
    have hns := WeierstrassCurve.Affine.equation_iff_nonsingular.1 heq
    rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, IsScalarTower.algebraMap_apply k R (IsLocalRing.ResidueField R)]
      at hns
    rcases hns.2 with hw | hp
    · -- `W_X` is a unit
      have hu : IsUnit (algebraMap k R W.a₁ * y' -
          (3 * x' ^ 2 + 2 * algebraMap k R W.a₂ * x' + algebraMap k R W.a₄)) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
        simpa [π, map_ofNat] using hw
      refine mem_range_of_eq (-↑hu.unit⁻¹) y' ?_
      have hwF : algebraMap R F (algebraMap k R W.a₁ * y' -
          (3 * x' ^ 2 + 2 * algebraMap k R W.a₂ * x' + algebraMap k R W.a₄)) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hu.ne_zero
      have hinv : algebraMap R F (↑hu.unit⁻¹) = (algebraMap R F (algebraMap k R W.a₁ * y' -
          (3 * x' ^ 2 + 2 * algebraMap k R W.a₂ * x' + algebraMap k R W.a₄)))⁻¹ := by
        exact map_units_inv (algebraMap R F).toMonoidHom hu.unit
      rw [map_neg, hinv]
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hk] at hwF ⊢
      set ψ := 2 * algebraMap R F y' + ↑ₖ W.a₁ * algebraMap R F x' + ↑ₖ W.a₃
      set wx := ↑ₖ W.a₁ * algebraMap R F y' -
        (3 * algebraMap R F x' ^ 2 + 2 * ↑ₖ W.a₂ * algebraMap R F x' + ↑ₖ W.a₄)
      have e : ψ⁻¹ • D k F (algebraMap R F x') + wx⁻¹ • D k F (algebraMap R F y') =
          (ψ⁻¹ * wx⁻¹) • (ψ • D k F (algebraMap R F y') + wx • D k F (algebraMap R F x')) := by
        rw [smul_add, smul_smul, smul_smul, add_comm]
        congr 2 <;> field_simp
      rw [hrel, smul_zero] at e
      rw [neg_smul, eq_neg_iff_add_eq_zero, e]
    · -- `ψ` is a unit
      have hu : IsUnit (2 * y' + algebraMap k R W.a₁ * x' + algebraMap k R W.a₃) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
        simpa [π, map_ofNat] using hp
      refine mem_range_of_eq (↑hu.unit⁻¹) x' ?_
      have hinv : algebraMap R F (↑hu.unit⁻¹) =
          (algebraMap R F (2 * y' + algebraMap k R W.a₁ * x' + algebraMap k R W.a₃))⁻¹ := by
        exact map_units_inv (algebraMap R F).toMonoidHom hu.unit
      rw [hinv]
      simp only [map_add, map_mul, map_ofNat, hk]
  · push Not at hx
    have hx0 : x ≠ 0 := fun h0 ↦ hx 0 (by rw [map_zero, h0])
    obtain ⟨z', hz'⟩ : ∃ z' : R, algebraMap R F z' = x⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | h1
      · exact absurd ha (hx a)
      · exact h1
    have hzm : z' ∈ IsLocalRing.maximalIdeal R := by
      intro hu
      apply hx (↑hu.unit⁻¹)
      refine (map_units_inv (algebraMap R F).toMonoidHom hu.unit).trans ?_
      change (algebraMap R F z')⁻¹ = x
      rw [hz', inv_inv]
    set U' := 1 + z' * (algebraMap k R W.a₂ + algebraMap k R W.a₄ * z' +
      algebraMap k R W.a₆ * z' ^ 2)
    have hU : IsUnit U' := isUnit_one_add_of_mem (Ideal.mul_mem_right _ _ hzm)
    have hUF : algebraMap R F U' = 1 + ↑ₖ W.a₂ * x⁻¹ + ↑ₖ W.a₄ * x⁻¹ ^ 2 + ↑ₖ W.a₆ * x⁻¹ ^ 3 := by
      simp only [U', map_add, map_mul, map_pow, map_one, hz', hk]
      ring
    rw [WEq] at h
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hU.ne_zero
      apply IsFractionRing.injective R F
      rw [hUF, map_zero]
      field_simp
      linear_combination -h
    -- `t = x / y ∈ R`
    obtain ⟨t', ht'⟩ : ∃ t' : R, algebraMap R F t' = x * y⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger R (x * y⁻¹) with h1 | ⟨s', hs'⟩
      · exact h1
      · exfalso
        have hrelR : U' = z' * (s' ^ 2 + algebraMap k R W.a₁ * s' +
            algebraMap k R W.a₃ * z' * s') := by
          apply IsFractionRing.injective R F
          rw [hUF]
          simp only [map_add, map_mul, map_pow, hs', hz', hk]
          field_simp
          linear_combination -h
        exact (hrelR ▸ Ideal.mul_mem_right _ _ hzm : U' ∈ IsLocalRing.maximalIdeal R) hU
    -- `t² U = z (1 + a₁ t + a₃ z t)`, so `t` lies in the maximal ideal
    have hrelt : t' ^ 2 * U' =
        z' * (1 + algebraMap k R W.a₁ * t' + algebraMap k R W.a₃ * z' * t') := by
      apply IsFractionRing.injective R F
      rw [map_mul, hUF]
      simp only [map_add, map_mul, map_pow, map_one, ht', hz', hk]
      field_simp
      linear_combination -h
    have htm : t' ∈ IsLocalRing.maximalIdeal R := by
      intro ht
      exact (hrelt ▸ Ideal.mul_mem_right _ _ hzm : t' ^ 2 * U' ∈ IsLocalRing.maximalIdeal R)
        ((ht.pow 2).mul hU)
    -- the unit `D = (1 + a₁t + a₃zt)(-1 + a₄z² + 2a₆z³) - a₃ztU`
    set D' := (1 + algebraMap k R W.a₁ * t' + algebraMap k R W.a₃ * z' * t') *
      (-1 + algebraMap k R W.a₄ * z' ^ 2 + 2 * algebraMap k R W.a₆ * z' ^ 3) -
        algebraMap k R W.a₃ * z' * t' * U'
    have hD : IsUnit D' := by
      have hw : algebraMap k R W.a₁ * t' + z' * (algebraMap k R W.a₃ * t' -
          (1 + algebraMap k R W.a₁ * t' + algebraMap k R W.a₃ * z' * t') *
            (algebraMap k R W.a₄ * z' + 2 * algebraMap k R W.a₆ * z' ^ 2) +
          algebraMap k R W.a₃ * t' * U') ∈ IsLocalRing.maximalIdeal R :=
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_right _ _ hzm)
      have := (isUnit_one_add_of_mem hw).neg
      convert this using 1
      simp only [D']
      ring
    refine mem_range_of_eq (U' * ↑hD.unit⁻¹) t' ?_
    have hDF : algebraMap R F D' ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hD.ne_zero
    have hinv : algebraMap R F (↑hD.unit⁻¹) = (algebraMap R F D')⁻¹ :=
      map_units_inv (algebraMap R F).toMonoidHom hD.unit
    rw [map_mul, hinv, ht']
    have hDy : D k F y = (-(↑ₖ W.a₁ * y - (3 * x ^ 2 + 2 * ↑ₖ W.a₂ * x + ↑ₖ W.a₄)) *
        (2 * y + ↑ₖ W.a₁ * x + ↑ₖ W.a₃)⁻¹) • D k F x := by
      rw [← one_smul F (D k F y), ← inv_mul_cancel₀ hψ, mul_smul,
        eq_sub_of_add_eq hrel, zero_sub, smul_neg, ← neg_smul, smul_smul]
      congr 1
      ring
    rw [Derivation.leibniz, Derivation.leibniz_inv, hDy]
    simp only [smul_smul, ← add_smul]
    congr 1
    have hDval : algebraMap R F D' = (1 + ↑ₖ W.a₁ * (x * y⁻¹) + ↑ₖ W.a₃ * x⁻¹ * (x * y⁻¹)) *
        (-1 + ↑ₖ W.a₄ * x⁻¹ ^ 2 + 2 * ↑ₖ W.a₆ * x⁻¹ ^ 3) -
          ↑ₖ W.a₃ * x⁻¹ * (x * y⁻¹) * algebraMap R F U' := by
      simp only [D', map_sub, map_add, map_mul, map_pow, map_one, map_neg, map_ofNat, hk, hz', ht']
    rw [mul_comm (algebraMap R F U'), mul_assoc, eq_inv_mul_iff_mul_eq₀ hDF, hDval, hUF]
    have hψ' : y * 2 + ↑ₖ W.a₁ * x + ↑ₖ W.a₃ ≠ 0 := by rwa [mul_comm y]
    field_simp
    linear_combination (-(x * (3 * x ^ 2 + 2 * ↑ₖ W.a₂ * x + ↑ₖ W.a₄))) * h

end Local

/-! ### Genus -/

section Genus

open AlgebraicGeometry Belyi
open scoped Belyi

variable {k : Type u} [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] (W : WeierstrassCurve k) [W.IsElliptic]

/-- **A curve whose function field contains a Weierstrass point `(x, y)` with `dx ≠ 0` has genus
at least one**: the invariant differential `dx/ψ` is a nonzero regular differential. -/
theorem one_le_curveGenus_of_weierstrass {x y : X.functionField} (h : WEq W x y)
    (hψ : 2 * y + algebraMap k _ W.a₁ * x + algebraMap k _ W.a₃ ≠ 0)
    (hdx : D k X.functionField x ≠ 0) : 1 ≤ Anabelian.curveGenus k X := by
  set ω := (2 * y + algebraMap k _ W.a₁ * x + algebraMap k _ W.a₃)⁻¹ • D k X.functionField x
  have hω : ω ∈ Anabelian.globalDifferentials k X := by
    refine Submodule.mem_iInf _ |>.2 fun p ↦ ?_
    letI := Anabelian.stalkAlgebra k X p
    haveI := Anabelian.stalkAlgebra_isScalarTower k X p
    haveI := valuationRing_stalk_of_isCurveOver k X p
    obtain ⟨a, ha⟩ := invariantDifferential_mem_range (R := X.presheaf.stalk p) W h hψ
    exact ⟨a, ha⟩
  have hω0 : ω ≠ 0 := smul_ne_zero (inv_ne_zero hψ) hdx
  haveI := finiteDimensional_globalDifferentials k X
  exact Nat.one_le_iff_ne_zero.2 (Module.finrank_pos_iff_exists_ne_zero.2
    ⟨⟨ω, hω⟩, fun h0 ↦ hω0 (congrArg Subtype.val h0)⟩).ne'

end Genus

end CurvesJacobian.Cusp
