/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.WeierAutVE
import CurvesJacobian.Cusp.EllipticMulByN

/-!
# `K`-automorphisms of `E ∖ {O}` preserve `E ∖ E[N]`

Let `E / K` be an elliptic curve in Weierstrass form over a field of characteristic zero,
`K[E] = Γ(E ∖ {O})` its affine coordinate ring, `N ≥ 1` and `ψ_N ∈ K[E]` the `N`-division
polynomial (`CurvesJacobian.Cusp.psiN`), so that `E ∖ E[N] = D(ψ_N) ⊆ E ∖ {O}`
(`CurvesJacobian.Cusp.VNE`) and `Γ(E ∖ E[N]) = K[E][1/ψ_N]`.

* `CurvesJacobian.Cusp.varChangeHomField`: a substitution `(x, y) ↦ (a x + b, d y + e x + f)`
  mapping a Weierstrass curve `W` to itself (`CurvesJacobian.Cusp.IsVarChangeField`) is a group
  endomorphism of `W(F)`;
* `CurvesJacobian.Cusp.comp_mul_ΨSq_eq_of_aut`: if `α` is a `K`-automorphism of `K[E]` with
  `α(x) = p(x)`, then `Φ_N(p) · ΨSq_N = (a Φ_N + b ΨSq_N) · ΨSq_N(p)` (`p = a X + b`);
* `CurvesJacobian.Cusp.isUnit_aut_psiN`: `α(ψ_N)` is a unit of `K[E][1/ψ_N]`;
* `CurvesJacobian.Cusp.exists_isoVNE_of_isoXE`: every `K`-automorphism `F` of `Spec Γ(E ∖ {O})`
  restricts to a `K`-automorphism `G` of `Spec Γ(E ∖ E[N])`;
* `CurvesJacobian.Cusp.exists_isoVNE_piV_of_isoXE`: the induced automorphism `θ_V` of
  `Π_{E ∖ E[N]}` satisfies `fill ∘ θ_V = conj(s) ∘ θ ∘ fill` for `fill = cor38Fill`.

**Proof of `isUnit_aut_psiN`.** By `exists_aut_X_eq₂` and `exists_aut_psiE_eq_smul`,
`α(x) = a x + b` and `α(y) = d y + e x + f` with `d ≠ 0`. As `α` respects the Weierstrass
equation and `x` is transcendental, the substitution maps `E` to itself, so it is a group
endomorphism of `E(K(E))`; it agrees with the automorphism `τ` of `K(E)` extending `α` on the
generic point `P`, hence on `N • P`. Comparing `x`-coordinates, `x(N • P) = Φ_N(x)/ΨSq_N(x)`,
gives `Φ_N(p) ΨSq_N = (a Φ_N + b ΨSq_N) ΨSq_N(p)`; as `Φ_N` and `ΨSq_N` are coprime,
`ΨSq_N(p) ∣ ΨSq_N`. Finally `α(ψ_N)² = ΨSq_N(p)(x)` divides `ψ_N² = ΨSq_N(x)` in `K[E]`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory Polynomial

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Substitutions `(x, y) ↦ (a x + b, d y + e x + f)` preserving a Weierstrass curve -/

section VarChange

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) (a b d e f : F)

/-- The coefficient relations saying `W(a x + b, d y + e x + f) = d² W(x, y)` for the Weierstrass
polynomial `W(x, y) = y² + a₁ x y + a₃ y - (x³ + a₂ x² + a₄ x + a₆)`. -/
def IsVarChangeField : Prop :=
  2 * e + a * W.a₁ = d * W.a₁ ∧ 2 * f + W.a₁ * b + W.a₃ = d * W.a₃ ∧ a ^ 3 = d ^ 2 ∧
    e ^ 2 + a * W.a₁ * e - 3 * a ^ 2 * b - a ^ 2 * W.a₂ + d ^ 2 * W.a₂ = 0 ∧
    2 * e * f + a * W.a₁ * f + W.a₁ * b * e + W.a₃ * e - 3 * a * b ^ 2 - 2 * a * W.a₂ * b -
      a * W.a₄ + d ^ 2 * W.a₄ = 0 ∧
    f ^ 2 + W.a₁ * b * f + W.a₃ * f - b ^ 3 - W.a₂ * b ^ 2 - W.a₄ * b - W.a₆ + d ^ 2 * W.a₆ = 0

variable {W a b d e f}

lemma IsVarChangeField.equation (h : IsVarChangeField W a b d e f) {x y : F}
    (hxy : W.Equation x y) : W.Equation (a * x + b) (d * y + e * x + f) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h
  rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
  linear_combination d ^ 2 * hxy + d * x * y * r1 + d * y * r2 - x ^ 3 * r3 + x ^ 2 * r4 +
    x * r5 + r6

lemma IsVarChangeField.negY (h : IsVarChangeField W a b d e f) (x y : F) :
    W.negY (a * x + b) (d * y + e * x + f) = d * W.negY x y + e * x + f := by
  obtain ⟨r1, r2, -⟩ := h
  simp only [WeierstrassCurve.Affine.negY]
  linear_combination -x * r1 - r2

lemma IsVarChangeField.ne_zero (h : IsVarChangeField W a b d e f) (hd : d ≠ 0) : a ≠ 0 := by
  intro h0
  have h3 := h.2.2.1
  rw [h0] at h3
  exact hd (pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination -h3))

lemma IsVarChangeField.slope [DecidableEq F] (h : IsVarChangeField W a b d e f) (hd : d ≠ 0)
    {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    a * W.slope (a * x₁ + b) (a * x₂ + b) (d * y₁ + e * x₁ + f) (d * y₂ + e * x₂ + f) =
      d * W.slope x₁ x₂ y₁ y₂ + e := by
  have ha := h.ne_zero hd
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.negY x₂ y₂ := fun hy ↦ hxy ⟨hx, hy⟩
    have hx' : a * x₁ + b = a * x₂ + b := by rw [hx]
    have hy' : d * y₁ + e * x₁ + f ≠ W.negY (a * x₂ + b) (d * y₂ + e * x₂ + f) := by
      rw [h.negY]
      intro h0
      apply hy
      subst hx
      exact mul_left_cancel₀ hd (by linear_combination h0)
    have hyy := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy,
      WeierstrassCurve.Affine.slope_of_Y_ne hx' hy']
    subst hx hyy
    have hden : y₁ - W.negY x₁ y₁ ≠ 0 := sub_ne_zero.2 hy
    have hden' : d * y₁ + e * x₁ + f - W.negY (a * x₁ + b) (d * y₁ + e * x₁ + f) =
        d * (y₁ - W.negY x₁ y₁) := by
      rw [h.negY]
      ring
    obtain ⟨r1, r2, r3, r4, r5, -⟩ := h
    have hnum : a * (3 * (a * x₁ + b) ^ 2 + 2 * W.a₂ * (a * x₁ + b) + W.a₄ -
        W.a₁ * (d * y₁ + e * x₁ + f)) = d ^ 2 * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) +
          d * e * (y₁ - W.negY x₁ y₁) := by
      simp only [WeierstrassCurve.Affine.negY]
      linear_combination e * (x₁ * r1 + r2) - d * y₁ * r1 + 3 * x₁ ^ 2 * r3 - 2 * x₁ * r4 - r5
    rw [hden', ← mul_div_assoc, hnum]
    field_simp
  · have hx' : a * x₁ + b ≠ a * x₂ + b :=
      fun h0 ↦ hx (mul_left_cancel₀ ha (by linear_combination h0))
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.slope_of_X_ne hx']
    have hsub : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    have hden : a * x₁ + b - (a * x₂ + b) = a * (x₁ - x₂) := by ring
    rw [hden]
    field_simp
    ring

lemma IsVarChangeField.addX (h : IsVarChangeField W a b d e f) (hd : d ≠ 0) {x₁ x₂ ℓ ℓ' : F}
    (hs : a * ℓ' = d * ℓ + e) :
    W.addX (a * x₁ + b) (a * x₂ + b) ℓ' = a * W.addX x₁ x₂ ℓ + b := by
  have ha := h.ne_zero hd
  obtain ⟨r1, -, r3, r4, -⟩ := h
  have h2 : a ^ 2 * (W.addX (a * x₁ + b) (a * x₂ + b) ℓ' - (a * W.addX x₁ x₂ ℓ + b)) = 0 := by
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination (a * ℓ' + d * ℓ + e + W.a₁ * a) * hs - ℓ ^ 2 * r3 +
      (d * r1 - W.a₁ * r3) * ℓ + r4 + W.a₂ * r3
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 ha))

lemma IsVarChangeField.addY (h : IsVarChangeField W a b d e f) (hd : d ≠ 0) {x₁ x₂ y₁ ℓ ℓ' : F}
    (hs : a * ℓ' = d * ℓ + e) :
    W.addY (a * x₁ + b) (a * x₂ + b) (d * y₁ + e * x₁ + f) ℓ' =
      d * W.addY x₁ x₂ y₁ ℓ + e * W.addX x₁ x₂ ℓ + f := by
  have hX := h.addX hd (x₁ := x₁) (x₂ := x₂) hs
  have hN : W.negAddY (a * x₁ + b) (a * x₂ + b) (d * y₁ + e * x₁ + f) ℓ' =
      d * W.negAddY x₁ x₂ y₁ ℓ + e * W.addX x₁ x₂ ℓ + f := by
    rw [WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negAddY, hX]
    linear_combination (W.addX x₁ x₂ ℓ - x₁) * hs
  rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addY, hN, hX, h.negY]

lemma point_some_congr₂ {x y x' y' : F} {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') : (Point.some x y h : W.Point) = Point.some x' y' h' := by
  subst hx hy
  rfl

variable [W.IsElliptic]

/-- The substitution `(x, y) ↦ (a x + b, d y + e x + f)` on the points of `W`. -/
def varChangeField (h : IsVarChangeField W a b d e f) : W.Point → W.Point
  | .zero => .zero
  | .some x y hxy => .some (a * x + b) (d * y + e * x + f)
      (WeierstrassCurve.Affine.equation_iff_nonsingular.1 (h.equation hxy.1))

lemma varChangeField_some (h : IsVarChangeField W a b d e f) {x y : F} (hxy : W.Nonsingular x y) :
    varChangeField h (Point.some x y hxy) = Point.some (a * x + b) (d * y + e * x + f)
      (WeierstrassCurve.Affine.equation_iff_nonsingular.1 (h.equation hxy.1)) :=
  rfl

lemma varChangeField_add [DecidableEq F] (h : IsVarChangeField W a b d e f) (hd : d ≠ 0)
    (P Q : W.Point) : varChangeField h (P + Q) = varChangeField h P + varChangeField h Q := by
  have ha := h.ne_zero hd
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    refine (Point.add_of_Y_eq (by rw [hxy.1]) ?_).symm
    rw [h.negY, hxy.2, hxy.1]
  · have hxy' : ¬(a * x₁ + b = a * x₂ + b ∧
        d * y₁ + e * x₁ + f = W.negY (a * x₂ + b) (d * y₂ + e * x₂ + f)) := by
      rintro ⟨hx, hy⟩
      have hx0 : x₁ = x₂ := mul_left_cancel₀ ha (by linear_combination hx)
      refine hxy ⟨hx0, ?_⟩
      rw [h.negY] at hy
      subst hx0
      exact mul_left_cancel₀ hd (by linear_combination hy)
    have hs := h.slope hd h₁.1 h₂.1 hxy
    rw [Point.add_some hxy, varChangeField_some, varChangeField_some, varChangeField_some,
      Point.add_some hxy']
    exact point_some_congr₂ (h.addX hd hs).symm (h.addY hd hs).symm

/-- **A substitution preserving `W` is a group endomorphism of `W(F)`.** -/
def varChangeHomField [DecidableEq F] (h : IsVarChangeField W a b d e f) (hd : d ≠ 0) :
    W.Point →+ W.Point where
  toFun := varChangeField h
  map_zero' := rfl
  map_add' := varChangeField_add h hd

lemma varChangeHomField_apply [DecidableEq F] (h : IsVarChangeField W a b d e f) (hd : d ≠ 0)
    (P : W.Point) : varChangeHomField h hd P = varChangeField h P :=
  rfl

end VarChange

/-! ### `K`-automorphisms of `K[E]` and the division polynomials -/

section DivPoly

open WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "A" => E.toAffine.CoordinateRing
local notation "L" => E.toAffine.FunctionField
local notation "φ" => algebraMap K E.toAffine.FunctionField

omit [CharZero K] [E.IsElliptic] in
/-- The `K`-automorphism of `K(E) = Frac K[E]` extending a `K`-automorphism of `K[E]`. -/
def autFracFieldN (α : A ≃ₐ[K] A) : L ≃ₐ[K] L :=
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv α.toRingEquiv) fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K A L, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact congrArg _ (α.commutes c)

omit [CharZero K] [E.IsElliptic] in
lemma autFracFieldN_algebraMap (α : A ≃ₐ[K] A) (r : A) :
    autFracFieldN E α (algebraMap A L r) = algebraMap A L (α r) :=
  show IsFractionRing.ringEquivOfRingEquiv α.toRingEquiv (algebraMap A L r) = _ from
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ r

omit [CharZero K] [E.IsElliptic] in
lemma algebraMap_C_coord (k : K) : algebraMap K[X] A (C k) = algebraMap K A k := by
  rw [IsScalarTower.algebraMap_apply K K[X] A, Polynomial.algebraMap_eq]

omit [E.IsElliptic] in
lemma two_ne_zero_coord : (2 : A) ≠ 0 := by
  rw [← map_ofNat (algebraMap K A) 2]
  exact (map_ne_zero_iff _ (algebraMap K A).injective).2 two_ne_zero

omit [CharZero K] in
/-- If `c₃ t³ + c₂ t² + c₁ t + c₀ = 0` for a transcendental `t`, all `cᵢ` vanish. -/
lemma eq_zero_of_cubic_transcendental {R : Type*} [CommRing R] [Algebra K R] {t : R}
    (ht : Transcendental K t) {c₃ c₂ c₁ c₀ : K}
    (h : algebraMap K R c₃ * t ^ 3 + algebraMap K R c₂ * t ^ 2 + algebraMap K R c₁ * t +
      algebraMap K R c₀ = 0) : c₃ = 0 ∧ c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 := by
  have hQ : C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀ = 0 := by
    by_contra hQ
    refine ht ⟨_, hQ, ?_⟩
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X]
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg (Polynomial.coeff · 3) hQ
  · simpa using congrArg (Polynomial.coeff · 2) hQ
  · simpa using congrArg (Polynomial.coeff · 1) hQ
  · simpa using congrArg (Polynomial.coeff · 0) hQ

omit [CharZero K] [E.IsElliptic] in
/-- The action of a `K`-automorphism `τ` of `K(E)` on the points of `E` over `K(E)`. -/
def pointMapN (τ : L ≃ₐ[K] L) : (E.toAffine.map φ).Point →+ (E.toAffine.map φ).Point :=
  Point.map (W' := E.toAffine) τ.toAlgHom

omit [CharZero K] in
lemma xCoord_eq_of_varChange_eq {τ : L ≃ₐ[K] L} {a b d e f : L}
    (hVC : IsVarChangeField (E.toAffine.map φ) a b d e f) {Q : (E.toAffine.map φ).Point}
    (hQ : Q ≠ 0) (h : varChangeField hVC Q = pointMapN E τ Q) :
    τ Q.xCoord = a * Q.xCoord + b := by
  rcases Q with _ | ⟨x, y, hxy⟩
  · exact absurd rfl hQ
  · have h1 := congrArg Point.xCoord h
    exact h1.symm

/-- `α(x) = a x + b` and `α(y) = c y + e x + f`, read in `K(E)` for the automorphism `τ`
extending `α`. -/
lemma exists_aut_genXY (α : A ≃ₐ[K] A) {p : K[X]} (hp1 : p.natDegree = 1)
    (hpα : α (algebraMap K[X] A X) = algebraMap K[X] A p) :
    ∃ τ : L ≃ₐ[K] L, ∃ c e f : K, c ≠ 0 ∧
      τ (genX E.toAffine) = φ (p.coeff 1) * genX E.toAffine + φ (p.coeff 0) ∧
      τ (genY E.toAffine) = φ c * genY E.toAffine + φ e * genX E.toAffine + φ f ∧
      2 * e + p.coeff 1 * E.a₁ = c * E.a₁ ∧ 2 * f + E.a₁ * p.coeff 0 + E.a₃ = c * E.a₃ := by
  obtain ⟨c, hc, hcα⟩ := exists_aut_psiE_eq_smul E α
  set a := p.coeff 1
  set b := p.coeff 0
  have hpab : p = C a * X + C b := eq_X_add_C_of_natDegree_le_one hp1.le
  set e : K := (c * E.a₁ - E.a₁ * a) / 2 with he_def
  set f : K := (c * E.a₃ - E.a₁ * b - E.a₃) / 2 with hf_def
  have he : 2 * e = c * E.a₁ - E.a₁ * a := by rw [he_def]; ring
  have hf : 2 * f = c * E.a₃ - E.a₁ * b - E.a₃ := by rw [hf_def]; ring
  have hxA : α (xE E) = algebraMap K A a * xE E + algebraMap K A b := by
    have hxE : xE E = algebraMap K[X] A X := rfl
    rw [hxE, hpα, hpab, map_add, map_mul, algebraMap_C_coord, algebraMap_C_coord]
  have hyA : α (yE E) = algebraMap K A c * yE E + algebraMap K A e * xE E + algebraMap K A f := by
    have h1 := hcα
    rw [psiE_eq', Algebra.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
      AlgEquiv.commutes, AlgEquiv.commutes, hxA] at h1
    have he2 : (2 : A) * algebraMap K A e = algebraMap K A c * algebraMap K A E.a₁ -
        algebraMap K A E.a₁ * algebraMap K A a := by
      rw [← map_ofNat (algebraMap K A) 2, ← map_mul, he, map_sub, map_mul, map_mul]
    have hf2 : (2 : A) * algebraMap K A f = algebraMap K A c * algebraMap K A E.a₃ -
        algebraMap K A E.a₁ * algebraMap K A b - algebraMap K A E.a₃ := by
      rw [← map_ofNat (algebraMap K A) 2, ← map_mul, hf, map_sub, map_sub, map_mul, map_mul]
    have h2 : (2 : A) * (α (yE E) - (algebraMap K A c * yE E + algebraMap K A e * xE E +
        algebraMap K A f)) = 0 := by
      linear_combination h1 - xE E * he2 - hf2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (two_ne_zero_coord E))
  have hgX : genX E.toAffine = algebraMap A L (xE E) := rfl
  have hgY : genY E.toAffine = algebraMap A L (yE E) := rfl
  refine ⟨autFracFieldN E α, c, e, f, hc, ?_, ?_, by linear_combination he,
    by linear_combination hf⟩
  · rw [hgX, autFracFieldN_algebraMap, hxA, map_add, map_mul, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  · rw [hgX, hgY, autFracFieldN_algebraMap, hyA, map_add, map_add, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

omit [CharZero K] [E.IsElliptic] in
/-- **The substitution `(x, y) ↦ (a x + b, c y + e x + f)` induced by `α` maps `E` to itself**:
`α` respects the Weierstrass equation and `x` is transcendental. -/
lemma isVarChangeField_of_aut {τ : L ≃ₐ[K] L} {a b c e f : K}
    (hx : τ (genX E.toAffine) = φ a * genX E.toAffine + φ b)
    (hy : τ (genY E.toAffine) = φ c * genY E.toAffine + φ e * genX E.toAffine + φ f)
    (r1 : 2 * e + a * E.a₁ = c * E.a₁) (r2 : 2 * f + E.a₁ * b + E.a₃ = c * E.a₃) :
    IsVarChangeField (E.toAffine.map φ) (φ a) (φ b) (φ c) (φ e) (φ f) := by
  have hG := equation_gen (W := E.toAffine)
  rw [WeierstrassCurve.Affine.equation_iff] at hG
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hG
  have hτG := congrArg τ hG
  simp only [map_add, map_mul, map_pow, AlgEquiv.commutes] at hτG
  rw [hx, hy] at hτG
  have r1L : 2 * φ e + φ a * φ E.a₁ = φ c * φ E.a₁ := by
    have := congrArg φ r1
    simpa only [map_add, map_mul, map_ofNat] using this
  have r2L : 2 * φ f + φ E.a₁ * φ b + φ E.a₃ = φ c * φ E.a₃ := by
    have := congrArg φ r2
    simpa only [map_add, map_mul, map_ofNat] using this
  obtain ⟨r3, r4, r5, r6⟩ := eq_zero_of_cubic_transcendental (transcendental_genX (W := E.toAffine))
    (c₃ := c ^ 2 - a ^ 3)
    (c₂ := e ^ 2 + a * E.a₁ * e - 3 * a ^ 2 * b - a ^ 2 * E.a₂ + c ^ 2 * E.a₂)
    (c₁ := 2 * e * f + a * E.a₁ * f + E.a₁ * b * e + E.a₃ * e - 3 * a * b ^ 2 -
      2 * a * E.a₂ * b - a * E.a₄ + c ^ 2 * E.a₄)
    (c₀ := f ^ 2 + E.a₁ * b * f + E.a₃ * f - b ^ 3 - E.a₂ * b ^ 2 - E.a₄ * b - E.a₆ +
      c ^ 2 * E.a₆) (by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination hτG - φ c ^ 2 * hG - φ c * genX E.toAffine * genY E.toAffine * r1L -
      φ c * genY E.toAffine * r2L)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [WeierstrassCurve.map_a₁] using r1L
  · simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] using r2L
  · have := congrArg φ r3
    simp only [map_sub, map_pow, map_zero] at this
    linear_combination -this
  · have := congrArg φ r4
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, map_add, map_sub, map_mul,
      map_pow, map_ofNat, map_zero] using this
  · have := congrArg φ r5
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, map_add, map_sub, map_mul, map_pow, map_ofNat,
      map_zero] using this
  · have := congrArg φ r6
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero] using this

/-- **`τ` acts on `x(N • P)` affinely**: the substitution and `τ` agree on the generic point `P`,
and the substitution is a group endomorphism. -/
lemma xCoord_nsmul_aut {τ : L ≃ₐ[K] L} {a b c e f : L}
    (hVC : IsVarChangeField (E.toAffine.map φ) a b c e f) (hc : c ≠ 0)
    (hx : τ (genX E.toAffine) = a * genX E.toAffine + b)
    (hy : τ (genY E.toAffine) = c * genY E.toAffine + e * genX E.toAffine + f)
    (N : ℕ) [NeZero N] :
    τ (N • genericPoint (W := E.toAffine)).xCoord =
      a * (N • genericPoint (W := E.toAffine)).xCoord + b := by
  have hgen : varChangeHomField hVC hc (genericPoint (W := E.toAffine)) =
      pointMapN E τ (genericPoint (W := E.toAffine)) :=
    point_some_congr₂ hx.symm hy.symm
  have hN : varChangeHomField hVC hc (N • genericPoint (W := E.toAffine)) =
      pointMapN E τ (N • genericPoint (W := E.toAffine)) := by
    rw [map_nsmul, map_nsmul, hgen]
  have hN0 : (N • genericPoint (W := E.toAffine)) ≠ 0 := by
    intro h0
    have ht := transcendental_N E N
    rw [h0, Point.xCoord_zero] at ht
    exact ht isAlgebraic_zero
  exact xCoord_eq_of_varChange_eq E hVC hN0 hN

omit [CharZero K] [E.IsElliptic] in
/-- **Clearing denominators**: if `τ(t) = p(t)` and `τ(P(t)/Q(t)) = a P(t)/Q(t) + b` for a
transcendental `t`, then `P(p) Q = (a P + b Q) Q(p)`. -/
lemma comp_eq_of_aut_div {M : Type*} [Field M] [Algebra K M] {t : M} (ht : Transcendental K t)
    (τ : M ≃ₐ[K] M) {p P Q : K[X]} (hτt : τ t = aeval t p) (hQ : Q ≠ 0) {a b : K}
    (h : τ (aeval t P / aeval t Q) =
      algebraMap K M a * (aeval t P / aeval t Q) + algebraMap K M b) :
    P.comp p * Q = (C a * P + C b * Q) * Q.comp p := by
  have hτaeval : ∀ q : K[X], τ (aeval t q) = aeval t (q.comp p) := fun q ↦ by
    rw [aeval_comp, ← hτt]
    exact (Polynomial.aeval_algHom_apply τ.toAlgHom _ q).symm
  rw [map_div₀, hτaeval, hτaeval] at h
  have hV : aeval t Q ≠ 0 := fun h0 ↦ ht ⟨_, hQ, h0⟩
  have hY : aeval t (Q.comp p) ≠ 0 := by
    rw [← hτaeval]
    exact (map_ne_zero_iff _ τ.injective).2 hV
  have hXY := div_mul_cancel₀ (aeval t (P.comp p)) hY
  have hUV := div_mul_cancel₀ (aeval t P) hV
  have hpoly : aeval t (P.comp p * Q - (C a * P + C b * Q) * Q.comp p) = 0 := by
    simp only [map_sub, map_mul, map_add, aeval_C]
    linear_combination aeval t (Q.comp p) * aeval t Q * h - aeval t Q * hXY +
      algebraMap K M a * aeval t (Q.comp p) * hUV
  have hpoly0 : P.comp p * Q - (C a * P + C b * Q) * Q.comp p = 0 := by
    by_contra h0
    exact ht ⟨_, h0, hpoly⟩
  exact sub_eq_zero.1 hpoly0

/-- **The division polynomials under a `K`-automorphism `α` of `K[E]`**: if `α(x) = p(x)`, then
`Φ_N(p) · ΨSq_N = (a Φ_N + b ΨSq_N) · ΨSq_N(p)` with `p = a X + b`. -/
theorem comp_mul_ΨSq_eq_of_aut (α : A ≃ₐ[K] A) {p : K[X]} (hp1 : p.natDegree = 1)
    (hpα : α (algebraMap K[X] A X) = algebraMap K[X] A p) (N : ℕ) [NeZero N] :
    (E.Φ N).comp p * E.ΨSq N = (C (p.coeff 1) * E.Φ N + C (p.coeff 0) * E.ΨSq N) *
      (E.ΨSq N).comp p := by
  obtain ⟨τ, c, e, f, hc, hx, hy, r1, r2⟩ := exists_aut_genXY E α hp1 hpα
  have hVC := isVarChangeField_of_aut E hx hy r1 r2
  have hcL : φ c ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).2 hc
  have hxN := xCoord_nsmul_aut E hVC hcL hx hy N
  rw [xCoord_nsmul_genericPoint two_ne_zero (intCast_N_ne_zero N)] at hxN
  have hτt : τ (genX E.toAffine) = aeval (genX E.toAffine) p := by
    have hpab : p = C (p.coeff 1) * X + C (p.coeff 0) := eq_X_add_C_of_natDegree_le_one hp1.le
    rw [hx]
    conv_rhs => rw [hpab]
    simp only [map_add, map_mul, aeval_C, aeval_X]
  exact comp_eq_of_aut_div (transcendental_genX (W := E.toAffine)) τ hτt
    (E.ΨSq_ne_zero (intCast_N_ne_zero N)) hxN

/-- **A `K`-automorphism of `K[E]` maps `ψ_N` to a unit of `K[E][1/ψ_N]`**, i.e. it preserves
`E ∖ E[N] = D(ψ_N) ⊆ E ∖ {O}`. -/
theorem isUnit_aut_psiN (N : ℕ) [NeZero N] (α : A ≃ₐ[K] A) :
    IsUnit (algebraMap A (coverRingN E N) (α (psiN E N))) := by
  obtain ⟨p, hp1, hpα⟩ := exists_aut_X_eq₂ E α
  have H := comp_mul_ΨSq_eq_of_aut E α hp1 hpα N
  have hcop : IsCoprime (E.Φ N) (E.ΨSq N) :=
    WeierstrassCurve.Affine.isCoprime_Φ_ΨSq (W := E.toAffine) two_ne_zero N
  have hcop' : IsCoprime ((E.Φ N).comp p) ((E.ΨSq N).comp p) :=
    hcop.map (Polynomial.compRingHom p)
  have hdvd : (E.ΨSq N).comp p ∣ E.ΨSq N * (E.Φ N).comp p :=
    ⟨C (p.coeff 1) * E.Φ N + C (p.coeff 0) * E.ΨSq N, by rw [mul_comm (E.ΨSq N), H]; ring⟩
  obtain ⟨q, hq⟩ := hcop'.symm.dvd_of_dvd_mul_right hdvd
  have hα2 : α (psiN E N) ^ 2 = algebraMap K[X] A ((E.ΨSq N).comp p) := by
    rw [← map_pow, psiN_sq, algebraMap_polynomial_eq_aeval_xE,
      show α (aeval (xE E) (E.ΨSq N)) = aeval (α (xE E)) (E.ΨSq N) from
        (Polynomial.aeval_algHom_apply α.toAlgHom _ _).symm,
      show xE E = algebraMap K[X] A X from rfl, hpα, Polynomial.aeval_algebraMap_apply,
      ← Polynomial.comp_eq_aeval]
  have key : algebraMap A (coverRingN E N) (psiN E N) ^ 2 =
      algebraMap A (coverRingN E N) (α (psiN E N)) ^ 2 *
        algebraMap A (coverRingN E N) (algebraMap K[X] A q) := by
    rw [← map_pow, ← map_pow, ← map_mul, psiN_sq, hα2, ← map_mul, ← hq]
  have hu : IsUnit (algebraMap A (coverRingN E N) (psiN E N) ^ 2) :=
    (IsLocalization.Away.algebraMap_isUnit (psiN E N)).pow 2
  rw [key] at hu
  exact (isUnit_pow_iff two_ne_zero).1 (isUnit_of_mul_isUnit_left hu)

end DivPoly

/-! ### Extension to `K[E][1/ψ_N] = Γ(E ∖ E[N])` -/

section CoverAutN

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N]

/-- The automorphism of `K[E][1/ψ_N]` extending a `K`-automorphism `α` of `K[E]`. -/
def coverAutN (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    coverRingN E N ≃+* coverRingN E N :=
  awayRingEquiv₂ (psiN E N) α.toRingEquiv (isUnit_aut_psiN E N α) (isUnit_aut_psiN E N α.symm)

/-- The automorphism of `Γ(E ∖ E[N])` extending a `K`-automorphism `α` of `K[E]`. -/
def sectionsVNEAut (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    Γ(curveE E, VNE E N) ≃+* Γ(curveE E, VNE E N) :=
  (sectionsVNEEquiv E N).trans ((coverAutN E N α).trans (sectionsVNEEquiv E N).symm)

lemma sectionsVNEEquiv_sectionsVNEAut
    (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) (s : Γ(curveE E, VNE E N)) :
    sectionsVNEEquiv E N (sectionsVNEAut E N α s) = coverAutN E N α (sectionsVNEEquiv E N s) := by
  rw [sectionsVNEAut, RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]

lemma sectionsVNEAut_algebraMap (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing)
    (s : Γ(curveE E, XE E)) :
    sectionsVNEAut E N α (algebraMap Γ(curveE E, XE E) Γ(curveE E, VNE E N) s) =
      algebraMap Γ(curveE E, XE E) Γ(curveE E, VNE E N)
        ((sectionsXEAlgEquiv E).symm (α (sectionsXEAlgEquiv E s))) := by
  apply (sectionsVNEEquiv E N).injective
  rw [sectionsVNEEquiv_sectionsVNEAut, sectionsVNEEquiv_algebraMap, sectionsVNEEquiv_algebraMap,
    AlgEquiv.apply_symm_apply]
  exact awayRingEquiv₂_algebraMap (psiN E N) α.toRingEquiv _ _ _

omit [NeZero N] in
set_option backward.isDefEq.respectTransparency false in
lemma resAlg_apply_VNE (s : Γ(curveE E, XE E)) :
    resAlg K (VNE_le_XE E N) s = algebraMap Γ(curveE E, XE E) Γ(curveE E, VNE E N) s := by
  have h1 : resAlg K (VNE_le_XE E N) s =
      (curveE E).presheaf.map (homOfLE (VNE_le_XE E N)).op s := by
    change (Scheme.Hom.appLE (𝟙 (curveE E)) (XE E) (VNE E N) (VNE_le_XE E N)) s = _
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact h1

lemma sectionsVNEAut_algebraMap_K
    (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) (c : K) :
    sectionsVNEAut E N α (algebraMap K Γ(curveE E, VNE E N) c) =
      algebraMap K Γ(curveE E, VNE E N) c := by
  have h1 : algebraMap K Γ(curveE E, VNE E N) c =
      algebraMap Γ(curveE E, XE E) Γ(curveE E, VNE E N) (algebraMap K Γ(curveE E, XE E) c) := by
    rw [← resAlg_apply_VNE, AlgHom.commutes]
  rw [h1, sectionsVNEAut_algebraMap, AlgEquiv.commutes, AlgEquiv.commutes, AlgEquiv.commutes]

end CoverAutN

/-! ### Automorphisms of `Spec Γ(E ∖ {O})` restrict to `Spec Γ(E ∖ E[N])` -/

section Sch

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic] (N : ℕ)
  [NeZero N]

set_option backward.isDefEq.respectTransparency false

/-- **[AbsTopII] Cor 3.4, step G4 (scheme part), for `X = E ∖ {O}`, `V = E ∖ E[N]`**: every
`K`-automorphism `F` of `Spec Γ(E ∖ {O})` restricts to a `K`-automorphism `G` of
`Spec Γ(E ∖ E[N])`: `res ≫ F = G ≫ res` for `res : Spec Γ(E ∖ E[N]) ⟶ Spec Γ(E ∖ {O})`. -/
theorem exists_isoVNE_of_isoXE
    (hne : ((VNE E N : (curveE E).Opens) : Set (curveE E)).Nonempty)
    (F : Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U) ≅ Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U))
    (hF : F.hom ≫ sKU (hypCurveX E) = sKU (hypCurveX E)) :
    ∃ G : Spec Γ((subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).Xbar,
        (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).U) ≅
      Spec Γ((subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).Xbar,
        (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).U),
      G.hom ≫ sKU (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne) =
          sKU (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne) ∧
        Spec.map (CommRingCat.ofHom (resAlg K (VNE_le_XE E N)).toRingHom) ≫ F.hom =
          G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg K (VNE_le_XE E N)).toRingHom) := by
  refine ⟨specIsoOfRingEquiv₂ (sectionsVNEAut E N (coordAutOfIso₂ E F hF)), ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (sectionsVNEAut E N (coordAutOfIso₂ E F hF)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, VNE E N))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, VNE E N)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    exact sectionsVNEAut_algebraMap_K E N _ c
  · conv_lhs => rw [← Spec.map_preimage F.hom]
    change Spec.map _ ≫ Spec.map (Spec.preimage F.hom) =
      Spec.map (CommRingCat.ofHom (sectionsVNEAut E N (coordAutOfIso₂ E F hF)).toRingHom) ≫
        Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext s
    change resAlg K (VNE_le_XE E N) (coverRing (hypCurveX E) (hypCurveX E) F.hom s) =
      sectionsVNEAut E N (coordAutOfIso₂ E F hF) (resAlg K (VNE_le_XE E N) s)
    rw [resAlg_apply_VNE, resAlg_apply_VNE, sectionsVNEAut_algebraMap]
    congr 1
    rw [coordAutOfIso₂, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    exact (AlgEquiv.symm_apply_apply (sectionsXEAlgEquiv E) _).symm

end Sch

/-! ### The induced automorphism of `Π_{E ∖ E[N]}` -/

section Pi1Elliptic

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (E : WeierstrassCurve K)
  [E.IsElliptic] (N : ℕ) [NeZero N]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopII] Cor 3.4, step G4, for `X = E ∖ {O}`, `V = E ∖ E[N]`**: a `K`-automorphism `F`
of `Spec Γ(X)` restricts to a `K`-automorphism `G` of `Spec Γ(V)`, and an automorphism `θ` of
`Π_X` induced by `F` lifts along `cor38Fill : Π_V ↠ Π_X` to the automorphism `θ_V` of `Π_V`
induced by `G`, up to an inner automorphism of `Π_X`. -/
theorem exists_isoVNE_piV_of_isoXE
    (hcX : ((hypCurveX E).U : Set (hypCurveX E).Xbar)ᶜ.Nonempty)
    (hne : ((VNE E N : (curveE E).Opens) : Set (curveE E)).Nonempty)
    (α₀ : fiber (basePoint Ω (hypCurveX E) hcX) ≅
      fiber (fillPoint Ω (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
        (compl_nonempty_of_le (VNE_le_XE E N) hcX) (VNE_le_XE E N)))
    (F : Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U) ≅ Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U))
    (hF : F.hom ≫ sKU (hypCurveX E) = sKU (hypCurveX E))
    (θ : π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
        baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
        baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U)))
    (hθ : IsConjInduced F.hom θ) :
    ∃ G : Spec Γ((subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).Xbar,
        (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).U) ≅
      Spec Γ((subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).Xbar,
        (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).U),
      G.hom ≫ sKU (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne) =
          sKU (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne) ∧
        Spec.map (CommRingCat.ofHom (resAlg K (VNE_le_XE E N)).toRingHom) ≫ F.hom =
          G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg K (VNE_le_XE E N)).toRingHom) ∧
        ∃ θV : π₁ᵉᵗ(basePoint Ω (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
            (compl_nonempty_of_le (VNE_le_XE E N) hcX) ≫ baseChangeSpec K Ω
              Γ((subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).Xbar,
                (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).U)) ≃ₜ*
          π₁ᵉᵗ(basePoint Ω (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne)
            (compl_nonempty_of_le (VNE_le_XE E N) hcX) ≫ baseChangeSpec K Ω
              Γ((subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).Xbar,
                (subCurve (hypCurveX E) (VNE E N) (VNE_le_XE E N) hne).U)),
          IsConjInduced G.hom θV ∧ ∃ s : π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
              baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U)), ∀ σ,
            (cor38Fill Ω (hypCurveX E) hcX (VNE E N) (VNE_le_XE E N) hne α₀ (θV σ) :
              π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
                baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U))) =
              s * θ (cor38Fill Ω (hypCurveX E) hcX (VNE E N) (VNE_le_XE E N) hne α₀ σ) * s⁻¹ := by
  obtain ⟨G, hGK, hGsq⟩ := exists_isoVNE_of_isoXE E N hne F hF
  exact ⟨G, hGK, hGsq, exists_piV_conj_of_square₂ Ω (hypCurveX E) hcX (VNE E N) (VNE_le_XE E N)
    hne α₀ F G hGsq θ hθ⟩

end Pi1Elliptic

end CurvesJacobian.Cusp
