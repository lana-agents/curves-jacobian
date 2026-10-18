/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Pi1.FundamentalGroup.Galois

/-!
# The `x`-coordinate of an elliptic curve minus its `2`-torsion is a finite étale double cover

Let `E : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` be a Weierstrass curve over a field `k`, with
affine coordinate ring `k[E] = k[X][Y]/⟨W(X, Y)⟩` (Mathlib's `E.toAffine.CoordinateRing`). Put
`ψ = 2y + a₁x + a₃ ∈ k[E]` (`CurvesJacobian.Cusp.psiE`) and
`g = 4x³ + b₂x² + 2b₄x + b₆ ∈ k[x]` (`CurvesJacobian.Cusp.gE`, Mathlib's `Ψ₂Sq`), so that
`ψ² = g` in `k[E]` (`CurvesJacobian.Cusp.psi_sq`). Then

* `lineRingE E = k[x, 1/g]` is the ring of the line minus the branch points `g = 0`;
* `coverRingE E = k[E][1/ψ] = k[x, y, 1/ψ]` is the ring of `E` minus `O` and the points of order
  two (the affine points with `ψ = 0`);

and `x : Spec (coverRingE E) ⟶ Spec (lineRingE E)` is finite étale of degree two
(`CurvesJacobian.Cusp.isFiniteEtale_spec`). This is the first step of the strictly Belyi type
structure of once-punctured elliptic curves ([AbsTopII] Def 3.5 / Example 3.6).

Proof: `coverRingE E` is the standard étale algebra `(k[X][Y]/W)[1/W_Y]` over `k[X]`
(`StandardEtalePair`, `W_Y = ψ` being the `Y`-derivative of the monic `W`); hence it is étale
over `k[X]`, and over its localization `lineRingE E` (`Algebra.Etale.of_restrictScalars`). Since
inverting `ψ` is the same as inverting `ψ² = g`, `coverRingE E` is the base change of `k[E]`
along `k[X] → lineRingE E`, so it is free of rank two with basis `1, y` (base change of
Mathlib's `CoordinateRing.basis`).
-/

open Polynomial AlgebraicGeometry
open scoped Polynomial.Bivariate

universe u

namespace CurvesJacobian.Cusp

variable {k : Type u} [Field k] (E : WeierstrassCurve k)

/-- `ψ = 2y + a₁x + a₃` in the affine coordinate ring of `E`. -/
noncomputable def psiE : E.toAffine.CoordinateRing :=
  AdjoinRoot.mk E.toAffine.polynomial E.toAffine.polynomialY

/-- The two-torsion cubic `g = 4x³ + b₂x² + 2b₄x + b₆` (Mathlib's `Ψ₂Sq`). -/
noncomputable def gE : k[X] := E.Ψ₂Sq

/-- `k[x, 1/g(x)]`: the line minus the branch points. -/
abbrev lineRingE := Localization.Away (gE E)

/-- `Γ(E ∖ E[2]) = k[x, y, 1/ψ]`. -/
abbrev coverRingE := Localization.Away (psiE E)

/-- `ψ² = g` in the coordinate ring. -/
lemma psi_sq : psiE E ^ 2 = algebraMap k[X] E.toAffine.CoordinateRing (gE E) := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
  exact WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq (W := E)

/-- The cubic `g` becomes a unit in `coverRingE E`. -/
lemma isUnit_algebraMap_gE : IsUnit (algebraMap k[X] (coverRingE E) (gE E)) := by
  rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing (coverRingE E), ← psi_sq,
    map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (psiE E)).pow 2

/-- `k[x, 1/g] → k[x, y, 1/ψ]`, induced by `k[X] → k[E]`. -/
noncomputable instance : Algebra (lineRingE E) (coverRingE E) :=
  (IsLocalization.Away.lift (S := lineRingE E) (gE E) (g := algebraMap k[X] (coverRingE E))
    (isUnit_algebraMap_gE E)).toAlgebra

instance : IsScalarTower k[X] (lineRingE E) (coverRingE E) :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (IsLocalization.Away.lift_eq (S := lineRingE E) (gE E) (isUnit_algebraMap_gE E) p).symm

instance : IsScalarTower k (lineRingE E) (coverRingE E) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] (lineRingE E),
      ← IsScalarTower.algebraMap_apply k[X] (lineRingE E) (coverRingE E),
      ← IsScalarTower.algebraMap_apply k k[X] (coverRingE E)]

/-- Inverting `ψ` is the same as inverting `g = ψ²`. -/
instance isLocalizationAway_gE :
    IsLocalization.Away (algebraMap k[X] E.toAffine.CoordinateRing (gE E)) (coverRingE E) := by
  rw [← psi_sq]
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (psiE E)).pow 2
  · intro s
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (psiE E) s
    refine ⟨n, a * psiE E ^ n, ?_⟩
    rw [map_mul, ← h, map_pow, map_pow]
    ring
  · intro a b h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (psiE E) h
    refine ⟨n, ?_⟩
    calc (psiE E ^ 2) ^ n * a = psiE E ^ n * (psiE E ^ n * a) := by ring
      _ = psiE E ^ n * (psiE E ^ n * b) := by rw [hn]
      _ = (psiE E ^ 2) ^ n * b := by ring

/-- `coverRingE E = k[E] ⊗_{k[X]} lineRingE E`. -/
instance isPushout_coverRingE :
    Algebra.IsPushout k[X] (lineRingE E) E.toAffine.CoordinateRing (coverRingE E) :=
  (Algebra.isPushout_of_isLocalization (R := k[X]) (Submonoid.powers (gE E)) (A := lineRingE E)
    E.toAffine.CoordinateRing (coverRingE E)).symm

/-- The basis `1, y` of `coverRingE E` over `lineRingE E`. -/
noncomputable def coverBasisE : Module.Basis (Fin 2) (lineRingE E) (coverRingE E) :=
  (isPushout_coverRingE E).out.basis (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine)

lemma coverBasisE_zero : coverBasisE E 0 = 1 := by
  simp [coverBasisE, IsBaseChange.basis_apply,
    WeierstrassCurve.Affine.CoordinateRing.basis_zero]

lemma coverBasisE_one :
    coverBasisE E 1 = algebraMap E.toAffine.CoordinateRing (coverRingE E)
      (AdjoinRoot.mk E.toAffine.polynomial Y) := by
  simp [coverBasisE, IsBaseChange.basis_apply,
    WeierstrassCurve.Affine.CoordinateRing.basis_one]

instance : Module.Free (lineRingE E) (coverRingE E) :=
  .of_basis (coverBasisE E)

instance : Module.Finite (lineRingE E) (coverRingE E) :=
  .of_basis (coverBasisE E)

/-- The `Y`-derivative of the Weierstrass polynomial is `W_Y = 2Y + a₁X + a₃`. -/
lemma derivative_polynomial_E : derivative E.toAffine.polynomial = E.toAffine.polynomialY := by
  simp only [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.Affine.polynomialY,
    derivative_add, derivative_sub, derivative_X_pow, derivative_mul, derivative_C,
    derivative_X]
  simp only [zero_mul, zero_add, sub_zero, mul_one]
  have h2 : ((2 : ℕ) : k[X]) = C 2 := by rw [← map_natCast C 2, Nat.cast_ofNat]
  rw [h2, show 2 - 1 = 1 from rfl, pow_one]

/-- The standard étale pair `(W, W_Y)` over `k[X]`. -/
noncomputable def standardEtalePairE : StandardEtalePair k[X] where
  f := E.toAffine.polynomial
  monic_f := E.toAffine.monic_polynomial
  g := E.toAffine.polynomialY
  cond := ⟨1, 0, 1, by rw [derivative_polynomial_E]; ring⟩

instance : Algebra.Etale k[X] (coverRingE E) :=
  Algebra.Etale.of_equiv (standardEtalePairE E).equivAwayAdjoinRoot

instance : Algebra.Etale (lineRingE E) (coverRingE E) :=
  haveI : Algebra.Etale k[X] (lineRingE E) := .of_isLocalizationAway (gE E)
  Algebra.Etale.of_restrictScalars k[X] (lineRingE E) (coverRingE E)

/-- `x : E ∖ E[2] → 𝔸¹ ∖ {g = 0}` is finite étale. -/
theorem isFiniteEtale_spec :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap (lineRingE E) (coverRingE E)))) := by
  rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
  exact ⟨⟩

/-- `ψ = (a₁X + a₃) • 1 + 2 • Y` in terms of the basis `1, Y` of `k[E]` over `k[X]`. -/
lemma psiE_eq : psiE E = (C E.a₁ * X + C E.a₃) • (1 : E.toAffine.CoordinateRing) +
    (C 2 : k[X]) • AdjoinRoot.mk E.toAffine.polynomial Y := by
  rw [Algebra.smul_def, Algebra.smul_def, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
    ← AdjoinRoot.mk_C, mul_one, ← map_mul, ← map_add, psiE,
    WeierstrassCurve.Affine.polynomialY]
  congr 1
  ring

lemma psiE_ne_zero [CharZero k] : psiE E ≠ 0 := by
  intro h
  rw [psiE_eq] at h
  have h2 := (WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero h).2
  rw [C_eq_zero] at h2
  exact two_ne_zero h2

instance [CharZero k] : IsDomain (coverRingE E) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (psiE_ne_zero E))

instance [CharZero k] : Nontrivial (lineRingE E) :=
  (algebraMap (lineRingE E) (coverRingE E)).domain_nontrivial

/-- The cover has degree two. -/
lemma finrank_coverRingE [CharZero k] : Module.finrank (lineRingE E) (coverRingE E) = 2 := by
  rw [Module.finrank_eq_card_basis (coverBasisE E), Fintype.card_fin]

end CurvesJacobian.Cusp
