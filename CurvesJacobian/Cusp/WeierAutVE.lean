/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticGenusOne
import CurvesJacobian.Cusp.Cor38Unique

/-!
# `K`-automorphisms of `E ∖ {O}` preserve `E ∖ E[2]`

Let `E / K` be an elliptic curve in Weierstrass form, `K[E] = Γ(E ∖ {O})` its affine coordinate
ring and `ψ = 2y + a₁x + a₃ ∈ K[E]` (`CurvesJacobian.Cusp.psiE`), so that
`E ∖ E[2] = D(ψ) ⊆ E ∖ {O}` and `Γ(E ∖ E[2]) = K[E][1/ψ]`.

* `CurvesJacobian.Cusp.exists_aut_X_eq₂`: every `K`-automorphism `α` of `K[E]` maps `x` to a
  polynomial of degree one in `x`;
* `CurvesJacobian.Cusp.exists_aut_psiE_eq_smul`: `α(ψ) = c · ψ` for some `c ∈ K ˣ`;
* `CurvesJacobian.Cusp.exists_isoVE_of_isoXE`: every `K`-automorphism `F` of `Spec Γ(E ∖ {O})`
  restricts to a `K`-automorphism `G` of `Spec Γ(E ∖ E[2])` (the square with the restriction
  `Γ(E ∖ {O}) → Γ(E ∖ E[2])` commutes);
* `CurvesJacobian.Cusp.exists_piV_conj_of_square₂` (any hyperbolic curve) and
  `CurvesJacobian.Cusp.exists_isoVE_piV_of_isoXE` (the elliptic case): if `θ` is an automorphism
  of `Π_X` induced by `F`, then the automorphism `θ_V` of `Π_V` induced by `G` satisfies
  `fill ∘ θ_V = conj(s) ∘ θ ∘ fill` for the filling `fill = cor38Fill : Π_V ↠ Π_X`.

**Proof of `α(ψ) = c ψ`.** `α` extends to a `K`-automorphism `τ` of `K(Ē)`. The pole `P_∞` of
`x` is the unique place of `K(Ē)` not containing `x`
(`CurvesJacobian.Cusp.exists_unique_pole_of_weq₂`); a place containing `x` contains `y`, hence
`K[E]` and `τ(x)`, so `τ(P_∞) = P_∞` and `ord_∞ ∘ τ = ord_∞`. Writing elements of `K[E]` as
`A(x) + B(x) y` (orders `deg A · ord_∞ x` and `deg B · ord_∞ x + ord_∞ y`, never equal as
`2 ord_∞ y = 3 ord_∞ x`) gives `τ(x) = A(x)` and `τ(ψ) = A(x) + c y`. Then
`τ(ψ)² = τ(ψ²) ∈ K[x]` forces `A(x) = (c/2)(a₁ x + a₃)`, i.e. `τ(ψ) = (c/2) ψ`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory Polynomial WeilCurves.FunctionField
open scoped WithZero

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Automorphisms of a function field act on places -/

section PlaceMap

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The image `τ(Q)` of a place under a `k`-automorphism `τ` (valuation ring `τ(O_Q)`). -/
def placeMapField (τ : F ≃ₐ[k] F) (Q : Place k F) : Place k F :=
  ⟨Q.1.comap (τ.symm : F →+* F), fun h ↦ Q.ne_top (top_unique fun x _ ↦ by
      have : τ x ∈ Q.1.comap (τ.symm : F →+* F) := by rw [h]; trivial
      simpa using (ValuationSubring.mem_comap.mp this)),
    fun c ↦ ValuationSubring.mem_comap.mpr (by simp [Q.algebraMap_mem])⟩

lemma apply_mem_placeMapField {τ : F ≃ₐ[k] F} {Q : Place k F} {x : F} :
    τ x ∈ (placeMapField τ Q).1 ↔ x ∈ Q.1 := by
  change τ.symm (τ x) ∈ Q.1 ↔ x ∈ Q.1
  rw [AlgEquiv.symm_apply_apply]

variable [PerfectField k] [IsFunctionField k F]

/-- **`ord_{τQ}(τ f) = ord_Q f`.** -/
lemma ord_placeMapField_apply (τ : F ≃ₐ[k] F) (Q : Place k F) (f : F) :
    (placeMapField τ Q).ord (τ f) = Q.ord f := by
  set w : Valuation F ℤᵐ⁰ := Q.valuation.comap (τ.symm : F →+* F)
  have hw : ∀ z, z ∈ (placeMapField τ Q).1 ↔ w z ≤ 1 := by
    intro z
    change τ.symm z ∈ Q.1 ↔ _
    rw [Q.mem_iff_valuation_le_one]
    rfl
  obtain ⟨π, hπ⟩ := Q.exists_ord_eq_one
  have hπw : w (τ π) = WithZero.exp (-1) := by
    have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
    simp only [w, Valuation.comap_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply]
    rw [Q.valuation_eq_exp hπ0, hπ]
  rw [(placeMapField τ Q).ord_eq_neg_log w hw ⟨_, hπw⟩ (τ f)]
  simp only [w, Valuation.comap_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply, Place.ord]

end PlaceMap

/-! ### Automorphisms of a Weierstrass function field -/

section WeierAut

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k] [IsFunctionField k F]
  (W : WeierstrassCurve k) {x y : F}

/-- **An automorphism mapping `x` into `k[x] + k[x] y` preserves the order at the pole of `x`.** -/
lemma ord_eq_of_aut₂ (h : WEq₂ W x y) {P : Place k F} (hxP : x ∉ P.1)
    (huniq : ∀ Q : Place k F, x ∉ Q.1 → Q = P) (τ : F ≃ₐ[k] F) {p q : k[X]}
    (hτ : τ x = aeval x p + aeval x q * y) (f : F) : P.ord (τ f) = P.ord f := by
  have hQ : placeMapField τ P = P := by
    refine huniq _ fun hx ↦ hxP ?_
    have h1 : τ x ∈ (placeMapField τ P).1 := by
      rw [hτ]
      exact add_mem (aeval_mem₂ hx p) (mul_mem (aeval_mem₂ hx q) (mem_of_weq₂ W h hx))
    exact apply_mem_placeMapField.1 h1
  have h2 := ord_placeMapField_apply τ P f
  rwa [hQ] at h2

/-- At a pole of `x`, `ord_P (A(x) + B(x) y) ≤ deg B · ord_P x + ord_P y` for `B ≠ 0`. -/
lemma ord_aeval_add_mul_le₂ (h : WEq₂ W x y) (hx : Transcendental k x) {P : Place k F}
    (hP : P.ord x < 0) {A B : k[X]} (hB : B ≠ 0) :
    P.ord (aeval x A + aeval x B * y) ≤ B.natDegree * P.ord x + P.ord y := by
  have hx0 : x ≠ 0 := ne_zero_of_transcendental hx
  have hyx := two_mul_ord_eq_of_weq₂ W h (P.ord_neg_iff.1 hP)
  have hne : ∀ C : k[X], C ≠ 0 → aeval x C ≠ 0 := fun C hC h0 ↦ hx ⟨C, hC, h0⟩
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, P.ord_zero] at hyx
    omega
  have hBy : aeval x B * y ≠ 0 := mul_ne_zero (hne B hB) hy0
  have hordB : P.ord (aeval x B * y) = B.natDegree * P.ord x + P.ord y := by
    rw [P.ord_mul (hne B hB) hy0, ord_aeval_eq₂ hx0 hP hB]
  by_cases hA : A = 0
  · rw [hA, map_zero, zero_add, hordB]
  have hAx := ord_aeval_eq₂ hx0 hP hA
  have hneq : P.ord (aeval x A) ≠ P.ord (aeval x B * y) := by
    rw [hAx, hordB]
    intro h3
    have h4 : P.ord x * (2 * A.natDegree - 2 * B.natDegree - 3) = 0 := by
      linear_combination 2 * h3 + hyx
    rcases mul_eq_zero.1 h4 with h5 | h5 <;> omega
  rcases lt_or_gt_of_ne hneq with hlt | hlt
  · rw [P.ord_add_eq_of_lt (hne A hA) hBy hlt]
    rw [hAx, hordB] at hlt
    rw [hAx]
    exact hlt.le
  · rw [add_comm, P.ord_add_eq_of_lt hBy (hne A hA) hlt, hordB]

/-- If `ord_P (A(x) + B(x) y) = ord_P x` at the pole of `x`, then `B = 0`. -/
lemma eq_zero_of_ord_eq₂ (h : WEq₂ W x y) (hx : Transcendental k x) {P : Place k F}
    (hP : P.ord x < 0) {A B : k[X]} (hord : P.ord (aeval x A + aeval x B * y) = P.ord x) :
    B = 0 := by
  by_contra hB
  have h1 := ord_aeval_add_mul_le₂ W h hx hP (A := A) hB
  have hyx := two_mul_ord_eq_of_weq₂ W h (P.ord_neg_iff.1 hP)
  have h2 : (0 : ℤ) ≤ B.natDegree := Nat.cast_nonneg _
  have h3 : (B.natDegree : ℤ) * P.ord x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 hP.le
  linarith

/-- If `ord_P (A(x) + B(x) y) = ord_P y` at the pole of `x`, then `B` is a nonzero constant. -/
lemma exists_C_of_ord_eq₂ (h : WEq₂ W x y) (hx : Transcendental k x) {P : Place k F}
    (hP : P.ord x < 0) {A B : k[X]} (hord : P.ord (aeval x A + aeval x B * y) = P.ord y) :
    ∃ c : k, c ≠ 0 ∧ B = C c := by
  have hx0 : x ≠ 0 := ne_zero_of_transcendental hx
  have hyx := two_mul_ord_eq_of_weq₂ W h (P.ord_neg_iff.1 hP)
  by_cases hB : B = 0
  · exfalso
    rw [hB, map_zero, zero_mul, add_zero] at hord
    by_cases hA : A = 0
    · rw [hA, map_zero, P.ord_zero] at hord
      linarith
    · rw [ord_aeval_eq₂ hx0 hP hA] at hord
      have h4 : P.ord x * (2 * A.natDegree - 3) = 0 := by linear_combination 2 * hord + hyx
      rcases mul_eq_zero.1 h4 with h5 | h5 <;> omega
  have h1 := ord_aeval_add_mul_le₂ W h hx hP (A := A) hB
  have hb0 : B.natDegree = 0 := by
    by_contra hne
    have h2 : (1 : ℤ) ≤ B.natDegree := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
    nlinarith
  refine ⟨B.coeff 0, fun h0 ↦ hB ?_, eq_C_of_natDegree_eq_zero hb0⟩
  rw [eq_C_of_natDegree_eq_zero hb0, h0, C_0]

/-- **If `(A(x) + c y)² ∈ k[x]` with `c ≠ 0`, then `A(x) + c y = d · (2y + a₁ x + a₃)`.** -/
lemma exists_eq_smul_psi₂ [CharZero k] (h : WEq₂ W x y) (hx : Transcendental k x)
    {P : Place k F} (hP : P.ord x < 0) {A : k[X]} {c : k} (hc : c ≠ 0) {S : k[X]}
    (hsq : (aeval x A + algebraMap k F c * y) ^ 2 = aeval x S) :
    ∃ d : k, d ≠ 0 ∧ aeval x A + algebraMap k F c * y =
      algebraMap k F d * (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) := by
  set d : k := c / 2 with hd_def
  have hd : c = 2 * d := by rw [hd_def]; ring
  have hd0 : d ≠ 0 := by
    intro h0
    apply hc
    rw [hd, h0, mul_zero]
  have hcd : algebraMap k F c = 2 * algebraMap k F d := by rw [hd, map_mul, map_ofNat]
  rw [hcd] at hsq ⊢
  have key : aeval x (C (2 * d) * (A - C d * (C W.a₁ * X + C W.a₃)) * (C W.a₁ * X + C W.a₃) -
      (S - (A - C d * (C W.a₁ * X + C W.a₃)) ^ 2 - C (d ^ 2) *
        (4 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) + (C W.a₁ * X + C W.a₃) ^ 2))) +
      aeval x (C (4 * d) * (A - C d * (C W.a₁ * X + C W.a₃))) * y = 0 := by
    simp only [map_sub, map_mul, map_add, map_pow, aeval_C, aeval_X, map_ofNat]
    linear_combination hsq - 4 * algebraMap k F d ^ 2 * h
  obtain ⟨-, h2⟩ := eq_zero_of_aeval_add_mul₂ W h hx hP key
  have hR : A - C d * (C W.a₁ * X + C W.a₃) = 0 := by
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso
      rw [C_eq_zero] at h3
      exact hd0 (by simpa using h3)
    · exact h3
  have hR' := congrArg (aeval x) hR
  simp only [map_sub, map_mul, map_add, aeval_C, aeval_X, map_zero] at hR'
  exact ⟨d, hd0, by linear_combination hR'⟩

end WeierAut

/-! ### `K`-automorphisms of `K[E]` -/

section CoordAut

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- `K[E] = Γ(E ∖ {O}) ⊆ K(Ē)`. -/
def coordToFunField₂ : E.toAffine.CoordinateRing →+* (curveE E).functionField :=
  (algebraMap Γ(curveE E, XE E) (curveE E).functionField).comp
    (sectionsXEAlgEquiv E).symm.toRingEquiv.toRingHom

lemma coordToFunField₂_apply (a : E.toAffine.CoordinateRing) :
    coordToFunField₂ E a =
      algebraMap Γ(curveE E, XE E) (curveE E).functionField ((sectionsXEAlgEquiv E).symm a) :=
  rfl

lemma coordToFunField₂_injective : Function.Injective (coordToFunField₂ E) :=
  (IsFractionRing.injective Γ(curveE E, XE E) (curveE E).functionField).comp
    (sectionsXEAlgEquiv E).symm.injective

lemma coordToFunField₂_algebraMap (c : K) :
    coordToFunField₂ E (algebraMap K _ c) = algebraMap K (curveE E).functionField c := by
  rw [coordToFunField₂_apply, AlgEquiv.commutes, germ_algebraMap_XE]

lemma coordToFunField₂_polynomial (p : K[X]) :
    coordToFunField₂ E (algebraMap K[X] E.toAffine.CoordinateRing p) = aeval (xN E) p := by
  have e : (coordToFunField₂ E).comp (algebraMap K[X] E.toAffine.CoordinateRing) =
      (aeval (xN E) : K[X] →ₐ[K] (curveE E).functionField).toRingHom := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · have e1 : algebraMap K[X] E.toAffine.CoordinateRing (C c) =
          algebraMap K E.toAffine.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply K K[X] E.toAffine.CoordinateRing,
          Polynomial.algebraMap_eq]
      rw [RingHom.comp_apply, e1, coordToFunField₂_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_C]
    · rw [RingHom.comp_apply, AdjoinRoot.algebraMap_eq, ← sectionsXEAlgEquiv_xX,
        coordToFunField₂_apply, AlgEquiv.symm_apply_apply, germ_xX, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X]
  exact DFunLike.congr_fun e p

lemma coordToFunField₂_X : coordToFunField₂ E (algebraMap K[X] E.toAffine.CoordinateRing X) =
    xN E := by
  rw [coordToFunField₂_polynomial, aeval_X]

lemma coordToFunField₂_mkY :
    coordToFunField₂ E (AdjoinRoot.mk E.toAffine.polynomial X) = yN E := by
  rw [AdjoinRoot.mk_X, coordToFunField₂_apply, sectionsXEAlgEquiv_symm_apply, coordToXE,
    AdjoinRoot.lift_root, germ_yX]

/-- Every element of `K[E]` is `A(x) + B(x) y` in `K(Ē)`. -/
lemma exists_coordToFunField₂_eq (a : E.toAffine.CoordinateRing) :
    ∃ p q : K[X], coordToFunField₂ E a = aeval (xN E) p + aeval (xN E) q * yN E := by
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  have hY : coordToFunField₂ E (WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine X) =
      yN E := coordToFunField₂_mkY E
  refine ⟨p, q, ?_⟩
  rw [← hpq, map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    coordToFunField₂_polynomial, coordToFunField₂_polynomial, hY]

lemma coordToFunField₂_psiE : coordToFunField₂ E (psiE E) =
    2 * yN E + algebraMap K _ E.a₁ * xN E + algebraMap K _ E.a₃ := by
  have e : psiE E = algebraMap K[X] E.toAffine.CoordinateRing (C 2) *
      AdjoinRoot.mk E.toAffine.polynomial X +
        algebraMap K[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃) := by
    rw [psiE, WeierstrassCurve.Affine.polynomialY, map_add, map_mul, AdjoinRoot.mk_C,
      AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  refine (congrArg (coordToFunField₂ E) e).trans ?_
  rw [map_add, map_mul, coordToFunField₂_polynomial, coordToFunField₂_polynomial,
    coordToFunField₂_mkY]
  simp only [map_add, map_mul, aeval_C, aeval_X, map_ofNat]
  ring

/-- `ψ² = 4(x³ + a₂x² + a₄x + a₆) + (a₁x + a₃)²`. -/
def psiSqPoly₂ : K[X] :=
  4 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆) + (C E.a₁ * X + C E.a₃) ^ 2

lemma coordToFunField₂_psiE_sq :
    coordToFunField₂ E (psiE E) ^ 2 = aeval (xN E) (psiSqPoly₂ E) := by
  have hW : yN E ^ 2 + algebraMap K _ E.a₁ * xN E * yN E + algebraMap K _ E.a₃ * yN E =
      xN E ^ 3 + algebraMap K _ E.a₂ * xN E ^ 2 + algebraMap K _ E.a₄ * xN E +
        algebraMap K _ E.a₆ := wEq_curveE E
  rw [coordToFunField₂_psiE, psiSqPoly₂]
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, map_ofNat]
  linear_combination 4 * hW

/-- The ring automorphism of `K(Ē)` induced by a `K`-automorphism of `K[E]`. -/
def autRingFunField₂ (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    (curveE E).functionField ≃+* (curveE E).functionField :=
  IsFractionRing.ringEquivOfRingEquiv
    ((sectionsXEAlgEquiv E).trans (α.trans (sectionsXEAlgEquiv E).symm)).toRingEquiv

lemma autRingFunField₂_coord (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing)
    (a : E.toAffine.CoordinateRing) :
    autRingFunField₂ E α (coordToFunField₂ E a) = coordToFunField₂ E (α a) := by
  rw [coordToFunField₂_apply, autRingFunField₂, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    coordToFunField₂_apply]
  change algebraMap _ _ ((sectionsXEAlgEquiv E).symm (α ((sectionsXEAlgEquiv E)
    ((sectionsXEAlgEquiv E).symm a)))) = _
  rw [AlgEquiv.apply_symm_apply]

/-- The `K`-automorphism of `K(Ē)` induced by a `K`-automorphism of `K[E]`. -/
def autFunField₂ (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    (curveE E).functionField ≃ₐ[K] (curveE E).functionField :=
  AlgEquiv.ofRingEquiv (f := autRingFunField₂ E α) fun c ↦ by
    rw [← coordToFunField₂_algebraMap, autRingFunField₂_coord, AlgEquiv.commutes]

lemma autFunField₂_coord (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing)
    (a : E.toAffine.CoordinateRing) :
    autFunField₂ E α (coordToFunField₂ E a) = coordToFunField₂ E (α a) :=
  autRingFunField₂_coord E α a

/-- **A `K`-automorphism of `K[E]` maps `x` to a polynomial of degree one in `x`.** -/
theorem exists_aut_X_eq₂ (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    ∃ p : K[X], p.natDegree = 1 ∧
      α (algebraMap K[X] E.toAffine.CoordinateRing X) =
        algebraMap K[X] E.toAffine.CoordinateRing p := by
  obtain ⟨P, hxP, -, huniq⟩ := exists_unique_pole_of_weq₂ E (wEq_curveE E)
    (transcendental_xN E) (finrank_adjoin_xN₂ E)
  have hP : P.ord (xN E) < 0 := P.ord_neg_iff.2 hxP
  have hx0 : xN E ≠ 0 := ne_zero_of_transcendental (transcendental_xN E)
  obtain ⟨p, q, hpq⟩ := exists_coordToFunField₂_eq E (α (algebraMap K[X] _ X))
  have hτx : autFunField₂ E α (xN E) = aeval (xN E) p + aeval (xN E) q * yN E := by
    have h0 := autFunField₂_coord E α (algebraMap K[X] _ X)
    rwa [coordToFunField₂_X, hpq] at h0
  have hord := ord_eq_of_aut₂ E (wEq_curveE E) hxP huniq (autFunField₂ E α) hτx (xN E)
  rw [hτx] at hord
  have hq : q = 0 := eq_zero_of_ord_eq₂ E (wEq_curveE E) (transcendental_xN E) hP hord
  rw [hq, map_zero, zero_mul, add_zero] at hord hpq
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero, P.ord_zero] at hord
    omega
  rw [ord_aeval_eq₂ hx0 hP hp0] at hord
  refine ⟨p, ?_, coordToFunField₂_injective E (by rw [hpq, coordToFunField₂_polynomial])⟩
  have h1 : P.ord (xN E) * ((p.natDegree : ℤ) - 1) = 0 := by linear_combination hord
  rcases mul_eq_zero.1 h1 with h2 | h2 <;> omega

/-- **A `K`-automorphism of `K[E]` maps `ψ = 2y + a₁x + a₃` to a nonzero multiple of `ψ`**,
i.e. it preserves `E ∖ E[2] = D(ψ) ⊆ E ∖ {O}`. -/
theorem exists_aut_psiE_eq_smul
    (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    ∃ c : K, c ≠ 0 ∧ α (psiE E) = c • psiE E := by
  obtain ⟨P, hxP, -, huniq⟩ := exists_unique_pole_of_weq₂ E (wEq_curveE E)
    (transcendental_xN E) (finrank_adjoin_xN₂ E)
  have hP : P.ord (xN E) < 0 := P.ord_neg_iff.2 hxP
  have hW : WEq₂ E (xN E) (yN E) := wEq_curveE E
  have hyx := two_mul_ord_eq_of_weq₂ E hW hxP
  obtain ⟨p, -, hp⟩ := exists_aut_X_eq₂ E α
  have hpx : autFunField₂ E α (xN E) = aeval (xN E) p := by
    have h0 := autFunField₂_coord E α (algebraMap K[X] _ X)
    rwa [coordToFunField₂_X, hp, coordToFunField₂_polynomial] at h0
  have hτx : autFunField₂ E α (xN E) = aeval (xN E) p + aeval (xN E) (0 : K[X]) * yN E := by
    rw [map_zero, zero_mul, add_zero, hpx]
  have hord := ord_eq_of_aut₂ E hW hxP huniq (autFunField₂ E α) hτx
  -- `ord_∞ ψ = ord_∞ y`
  have hy0 : yN E ≠ 0 := by
    intro h0
    rw [h0, P.ord_zero] at hyx
    omega
  have h20 : (2 : (curveE E).functionField) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (curveE E).functionField) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  have h2ord : P.ord (2 : (curveE E).functionField) = 0 := by
    rw [← map_ofNat (algebraMap K (curveE E).functionField) 2]
    exact P.ord_algebraMap_base 2
  have hordψ : P.ord (coordToFunField₂ E (psiE E)) = P.ord (yN E) := by
    rw [coordToFunField₂_psiE, add_assoc]
    have hv : OrdGe₂ P (P.ord (xN E))
        (algebraMap K _ E.a₁ * xN E + algebraMap K _ E.a₃) :=
      ordGe₂_add (ordGe₂_mul (ordGe₂_algebraMap _) (ordGe₂_ord _) (by omega))
        (ordGe₂_mono hP.le (ordGe₂_algebraMap _))
    have h2y : P.ord (2 * yN E) = P.ord (yN E) := by
      rw [P.ord_mul h20 hy0, h2ord, zero_add]
    rw [ord_add_eq_of_ordGe₂ hv (mul_ne_zero h20 hy0) (by rw [h2y]; omega), h2y]
  -- `τ ψ = A(x) + c y`
  obtain ⟨A₁, B₁, hAB⟩ := exists_coordToFunField₂_eq E (α (psiE E))
  have hτψ : autFunField₂ E α (coordToFunField₂ E (psiE E)) =
      aeval (xN E) A₁ + aeval (xN E) B₁ * yN E := by
    rw [autFunField₂_coord, hAB]
  obtain ⟨c, hc, hB⟩ := exists_C_of_ord_eq₂ E hW (transcendental_xN E) hP (A := A₁) (B := B₁)
    (by rw [← hτψ, hord, hordψ])
  rw [hB, aeval_C] at hτψ
  -- `(τ ψ)² ∈ K[x]`
  have hsq : (aeval (xN E) A₁ + algebraMap K _ c * yN E) ^ 2 =
      aeval (xN E) ((psiSqPoly₂ E).comp p) := by
    rw [← hτψ, ← map_pow, coordToFunField₂_psiE_sq, aeval_comp, ← hpx]
    exact (Polynomial.aeval_algHom_apply (autFunField₂ E α).toAlgHom (xN E) _).symm
  obtain ⟨d, hd, hfin⟩ := exists_eq_smul_psi₂ E hW (transcendental_xN E) hP hc hsq
  refine ⟨d, hd, coordToFunField₂_injective E ?_⟩
  rw [← autFunField₂_coord E α, hτψ, hfin, Algebra.smul_def, map_mul,
    coordToFunField₂_algebraMap, coordToFunField₂_psiE]

end CoordAut

/-! ### Extension to `K[E][1/ψ] = Γ(E ∖ E[2])` -/

section Away

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x : R)
  [IsLocalization.Away x S]

/-- A ring automorphism `e` of `R` with `e(x)`, `e⁻¹(x)` units in `S = R[1/x]` extends to `S`. -/
def awayRingEquiv₂ (e : R ≃+* R) (h₁ : IsUnit (algebraMap R S (e x)))
    (h₂ : IsUnit (algebraMap R S (e.symm x))) : S ≃+* S :=
  RingEquiv.ofRingHom
    (IsLocalization.Away.lift x (S := S) (g := (algebraMap R S).comp e.toRingHom) h₁)
    (IsLocalization.Away.lift x (S := S) (g := (algebraMap R S).comp e.symm.toRingHom) h₂)
    (IsLocalization.ringHom_ext (Submonoid.powers x) (RingHom.ext fun r ↦ by
      simp [IsLocalization.Away.lift_eq]))
    (IsLocalization.ringHom_ext (Submonoid.powers x) (RingHom.ext fun r ↦ by
      simp [IsLocalization.Away.lift_eq]))

lemma awayRingEquiv₂_algebraMap (e : R ≃+* R) (h₁ : IsUnit (algebraMap R S (e x)))
    (h₂ : IsUnit (algebraMap R S (e.symm x))) (r : R) :
    awayRingEquiv₂ x e h₁ h₂ (algebraMap R S r) = algebraMap R S (e r) :=
  IsLocalization.Away.lift_eq x h₁ r

end Away

section CoverAut

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

lemma isUnit_aut_psiE₂ (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    IsUnit (algebraMap E.toAffine.CoordinateRing (coverRingE E) (α (psiE E))) := by
  obtain ⟨c, hc, h⟩ := exists_aut_psiE_eq_smul E α
  rw [h, Algebra.smul_def, map_mul]
  exact (((IsUnit.mk0 c hc).map (algebraMap K E.toAffine.CoordinateRing)).map
    (algebraMap E.toAffine.CoordinateRing (coverRingE E))).mul
      (IsLocalization.Away.algebraMap_isUnit (psiE E))

/-- The automorphism of `K[E][1/ψ]` extending a `K`-automorphism `α` of `K[E]`. -/
def coverAut₂ (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    coverRingE E ≃+* coverRingE E :=
  awayRingEquiv₂ (psiE E) α.toRingEquiv (isUnit_aut_psiE₂ E α) (isUnit_aut_psiE₂ E α.symm)

/-- The automorphism of `Γ(E ∖ E[2])` extending a `K`-automorphism `α` of `K[E]`. -/
def sectionsVEAut₂ (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) :
    Γ(curveE E, VE E) ≃+* Γ(curveE E, VE E) :=
  (sectionsVEEquiv E).trans ((coverAut₂ E α).trans (sectionsVEEquiv E).symm)

lemma sectionsVEEquiv_sectionsVEAut₂
    (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing) (s : Γ(curveE E, VE E)) :
    sectionsVEEquiv E (sectionsVEAut₂ E α s) = coverAut₂ E α (sectionsVEEquiv E s) := by
  rw [sectionsVEAut₂, RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]

lemma sectionsVEAut₂_resVX (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing)
    (s : Γ(curveE E, XE E)) :
    sectionsVEAut₂ E α (resVX E s) =
      resVX E ((sectionsXEAlgEquiv E).symm (α (sectionsXEAlgEquiv E s))) := by
  apply (sectionsVEEquiv E).injective
  rw [sectionsVEEquiv_sectionsVEAut₂, sectionsVEEquiv_resVX, sectionsVEEquiv_resVX,
    AlgEquiv.apply_symm_apply]
  exact awayRingEquiv₂_algebraMap (psiE E) α.toRingEquiv _ _ _

lemma sectionsVEAut₂_algebraMap (α : E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing)
    (c : K) : sectionsVEAut₂ E α (algebraMap K Γ(curveE E, VE E) c) =
      algebraMap K Γ(curveE E, VE E) c := by
  apply (sectionsVEEquiv E).injective
  rw [sectionsVEEquiv_sectionsVEAut₂, sectionsVEEquiv_algebraMap,
    IsScalarTower.algebraMap_apply K E.toAffine.CoordinateRing (coverRingE E)]
  refine (awayRingEquiv₂_algebraMap (psiE E) α.toRingEquiv _ _ _).trans ?_
  exact congrArg _ (α.commutes c)

end CoverAut

/-! ### Automorphisms of `Spec Γ(E ∖ {O})` restrict to `Spec Γ(E ∖ E[2])` -/

/-- `Spec` of a ring automorphism. -/
def specIsoOfRingEquiv₂ {R : CommRingCat.{u}} (g : R ≃+* R) : Spec R ≅ Spec R where
  hom := Spec.map (CommRingCat.ofHom g.toRingHom)
  inv := Spec.map (CommRingCat.ofHom g.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 2
    ext a
    exact g.apply_symm_apply a
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 2
    ext a
    exact g.symm_apply_apply a

section Sch

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]

set_option backward.isDefEq.respectTransparency false

/-- The `K`-automorphism of `K[E]` of a `K`-automorphism of `Spec Γ(E ∖ {O})`. -/
def coordAutOfIso₂
    (F : Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U) ≅ Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U))
    (hF : F.hom ≫ sKU (hypCurveX E) = sKU (hypCurveX E)) :
    E.toAffine.CoordinateRing ≃ₐ[K] E.toAffine.CoordinateRing :=
  ((sectionsXEAlgEquiv E).symm.trans (CurvesJacobian.LocAn.secAlgEquiv (hypCurveX E) F hF)).trans
    (sectionsXEAlgEquiv E)

omit [NumberField K] [E.IsElliptic] in
lemma resAlg_apply_VE₂ (s : Γ(curveE E, XE E)) : resAlg K (VE_le_XE E) s = resVX E s := by
  change (Scheme.Hom.appLE (𝟙 (curveE E)) (XE E) (VE E) (VE_le_XE E)) s = _
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]

/-- **Every `K`-automorphism `F` of `Spec Γ(E ∖ {O})` restricts to a `K`-automorphism `G` of
`Spec Γ(E ∖ E[2])`**: `res ≫ F = G ≫ res` for `res : Spec Γ(E ∖ E[2]) ⟶ Spec Γ(E ∖ {O})`. -/
theorem exists_isoVE_of_isoXE
    (hne : ((VE E : (curveE E).Opens) : Set (curveE E)).Nonempty)
    (F : Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U) ≅ Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U))
    (hF : F.hom ≫ sKU (hypCurveX E) = sKU (hypCurveX E)) :
    ∃ G : Spec Γ((subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).Xbar,
        (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).U) ≅
      Spec Γ((subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).Xbar,
        (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).U),
      G.hom ≫ sKU (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne) =
          sKU (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne) ∧
        Spec.map (CommRingCat.ofHom (resAlg K (VE_le_XE E)).toRingHom) ≫ F.hom =
          G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg K (VE_le_XE E)).toRingHom) := by
  refine ⟨specIsoOfRingEquiv₂ (sectionsVEAut₂ E (coordAutOfIso₂ E F hF)), ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (sectionsVEAut₂ E (coordAutOfIso₂ E F hF)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, VE E))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, VE E)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    exact sectionsVEAut₂_algebraMap E _ c
  · conv_lhs => rw [← Spec.map_preimage F.hom]
    change Spec.map _ ≫ Spec.map (Spec.preimage F.hom) =
      Spec.map (CommRingCat.ofHom (sectionsVEAut₂ E (coordAutOfIso₂ E F hF)).toRingHom) ≫
        Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext s
    change resAlg K (VE_le_XE E) (coverRing (hypCurveX E) (hypCurveX E) F.hom s) =
      sectionsVEAut₂ E (coordAutOfIso₂ E F hF) (resAlg K (VE_le_XE E) s)
    rw [resAlg_apply_VE₂, resAlg_apply_VE₂, sectionsVEAut₂_resVX]
    congr 1
    rw [coordAutOfIso₂, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    exact (AlgEquiv.symm_apply_apply (sectionsXEAlgEquiv E) _).symm

end Sch

/-! ### The induced automorphism of `Π_V` -/

section Pi1Generic

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

set_option backward.isDefEq.respectTransparency false

/-- `π₁ᵉᵗ` along an isomorphism of schemes. -/
def piEquivOfIsoField {Y Z : Scheme.{u}} (e : Y ≅ Z) (pt : Spec (.of Ω) ⟶ Y) :
    π₁ᵉᵗ(pt) ≃ₜ* π₁ᵉᵗ(pt ≫ e.hom) :=
  let φ := FiniteEtale.fundamentalGroupMap e.hom (rfl : pt ≫ e.hom = _)
  let m : π₁ᵉᵗ(pt) ≃* π₁ᵉᵗ(pt ≫ e.hom) := MulEquiv.ofBijective φ.toMonoidHom
    (FiniteEtale.fundamentalGroupMap_bijective_of_isIso e.hom rfl)
  let h : π₁ᵉᵗ(pt) ≃ₜ π₁ᵉᵗ(pt ≫ e.hom) :=
    Continuous.homeoOfEquivCompactToT2 (f := m.toEquiv) φ.continuous_toFun
  { m with
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `fillMap` is induced by the restriction `Spec Γ(U) ⟶ Spec Γ(U')`. -/
lemma isConjInduced_fillMap₂ (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    {U' : C.Xbar.Opens} (h : C.U ≤ U') :
    IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (fillMap Ω C hc h) :=
  (isConjInduced_iff _ (fillPoint_spec Ω C hc h) _).2 ⟨Iso.refl _, fun σ ↦ by
    change _ = (Iso.refl _).conjAut _
    rw [Iso.conjAut_apply]
    ext
    simp
    rfl⟩

variable (CX : HypCurve K) (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens)
  (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))

/-- **Restricting an induced automorphism to `U_X`**: if `res ≫ F = G ≫ res` and `θ` is an
automorphism of `Π_X` induced by `F`, then the automorphism `θ_V` of `Π_{U_X}` induced by `G`
(with a fixed change of base point) satisfies `fill ∘ θ_V = conj(s) ∘ θ ∘ fill` for the filling
`fill = cor38Fill : Π_{U_X} ↠ Π_X`. -/
theorem exists_piV_conj_of_square₂
    (F : Spec Γ(CX.Xbar, CX.U) ≅ Spec Γ(CX.Xbar, CX.U))
    (G : Spec Γ((subCurve CX UX hUX hne).Xbar, (subCurve CX UX hUX hne).U) ≅
      Spec Γ((subCurve CX UX hUX hne).Xbar, (subCurve CX UX hUX hne).U))
    (hsq : Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom) ≫ F.hom =
      G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom))
    (θ : π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))
    (hθ : IsConjInduced F.hom θ) :
    ∃ θV : π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) ≫
        baseChangeSpec K Ω Γ((subCurve CX UX hUX hne).Xbar, (subCurve CX UX hUX hne).U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) ≫
        baseChangeSpec K Ω Γ((subCurve CX UX hUX hne).Xbar, (subCurve CX UX hUX hne).U)),
      IsConjInduced G.hom θV ∧
        ∃ s : π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)), ∀ σ,
          (cor38Fill Ω CX hcX UX hUX hne α₀ (θV σ) :
            π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))) =
          s * θ (cor38Fill Ω CX hcX UX hUX hne α₀ σ) * s⁻¹ := by
  have HθV : IsConjInduced G.hom ((piEquivOfIsoField Ω G _).trans (autContinuousMulEquivOfIso
      (coverFib Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)
        (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) G.hom))) :=
    ⟨coverFib Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)
        (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) G.hom, fun _ ↦ rfl⟩
  refine ⟨_, HθV, ?_⟩
  have Hfill := isConjInduced_fillMap₂ Ω (subCurve CX UX hUX hne)
    (compl_nonempty_of_le hUX hcX) hUX
  have He := IsConjInduced.symm_of_iso (Iso.refl _)
    (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
      α₀)).toMulEquiv (isConjInduced_id_autIso _)
  have H1 := (Hfill.comp He).comp hθ
  have H2 := (HθV.comp Hfill).comp He
  have hmor : (Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom) ≫ (Iso.refl _).inv) ≫
      F.hom = (G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg K hUX).toRingHom)) ≫
        (Iso.refl _).inv := by
    rw [Iso.refl_inv, Category.comp_id, Category.comp_id, hsq]
  obtain ⟨u, hu⟩ := IsConjInduced.exists_conj_eq H2 (H1.congr_hom hmor)
  exact ⟨u, fun σ ↦ hu σ⟩

end Pi1Generic

section Pi1Elliptic

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (E : WeierstrassCurve K)
  [E.IsElliptic]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopII] Cor 3.4, step G4, for `X = E ∖ {O}`, `V = E ∖ E[2]`**: a `K`-automorphism `F`
of `Spec Γ(X)` restricts to a `K`-automorphism `G` of `Spec Γ(V)`, and an automorphism `θ` of
`Π_X` induced by `F` lifts along `cor38Fill : Π_V ↠ Π_X` to the automorphism `θ_V` of `Π_V`
induced by `G`, up to an inner automorphism of `Π_X`. -/
theorem exists_isoVE_piV_of_isoXE
    (hcX : ((hypCurveX E).U : Set (hypCurveX E).Xbar)ᶜ.Nonempty)
    (hne : ((VE E : (curveE E).Opens) : Set (curveE E)).Nonempty)
    (α₀ : fiber (basePoint Ω (hypCurveX E) hcX) ≅
      fiber (fillPoint Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
        (compl_nonempty_of_le (VE_le_XE E) hcX) (VE_le_XE E)))
    (F : Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U) ≅ Spec Γ((hypCurveX E).Xbar, (hypCurveX E).U))
    (hF : F.hom ≫ sKU (hypCurveX E) = sKU (hypCurveX E))
    (θ : π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
        baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
        baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U)))
    (hθ : IsConjInduced F.hom θ) :
    ∃ G : Spec Γ((subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).Xbar,
        (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).U) ≅
      Spec Γ((subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).Xbar,
        (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).U),
      G.hom ≫ sKU (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne) =
          sKU (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne) ∧
        Spec.map (CommRingCat.ofHom (resAlg K (VE_le_XE E)).toRingHom) ≫ F.hom =
          G.hom ≫ Spec.map (CommRingCat.ofHom (resAlg K (VE_le_XE E)).toRingHom) ∧
        ∃ θV : π₁ᵉᵗ(basePoint Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
            (compl_nonempty_of_le (VE_le_XE E) hcX) ≫ baseChangeSpec K Ω
              Γ((subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).Xbar,
                (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).U)) ≃ₜ*
          π₁ᵉᵗ(basePoint Ω (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne)
            (compl_nonempty_of_le (VE_le_XE E) hcX) ≫ baseChangeSpec K Ω
              Γ((subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).Xbar,
                (subCurve (hypCurveX E) (VE E) (VE_le_XE E) hne).U)),
          IsConjInduced G.hom θV ∧ ∃ s : π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
              baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U)), ∀ σ,
            (cor38Fill Ω (hypCurveX E) hcX (VE E) (VE_le_XE E) hne α₀ (θV σ) :
              π₁ᵉᵗ(basePoint Ω (hypCurveX E) hcX ≫
                baseChangeSpec K Ω Γ((hypCurveX E).Xbar, (hypCurveX E).U))) =
              s * θ (cor38Fill Ω (hypCurveX E) hcX (VE E) (VE_le_XE E) hne α₀ σ) * s⁻¹ := by
  obtain ⟨G, hGK, hGsq⟩ := exists_isoVE_of_isoXE E hne F hF
  exact ⟨G, hGK, hGsq, exists_piV_conj_of_square₂ Ω (hypCurveX E) hcX (VE E) (VE_le_XE E) hne
    α₀ F G hGsq θ hθ⟩

end Pi1Elliptic

end CurvesJacobian.Cusp
