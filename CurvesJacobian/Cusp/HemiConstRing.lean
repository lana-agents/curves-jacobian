/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiConstExt
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral

/-!
# The ring of `V = X_M` in Galois form: `(hemiDataM E M).R ≅ M[E]` (MR8, [AbsTopII] Cor. 3.3)

Let `D : GaloisData k t` (`char k = 0`, `Ω` algebraically closed and Galois over `k(t)`), let
`M ⊆ k̄` be a finite Galois extension of `k` inside the algebraic closure `k̄` of `k` in `Ω`, and
let `W` be a Weierstrass curve over `k` with an isomorphism `e : k[W] ≃ₐ[k] R` (the ring of `D`)
mapping `x` to `t`. The Galois data `galoisDataConst₃ D M` (`H_L ⊓ Gal(Ω / M)`) has function
field `L_M = L ⊔ k(t)(M)` and ring `R_M` (the integral closure of `k[t]` in `L_M`). We show:

* `CurvesJacobian.Cusp.coordRing_injective₃`: a ring map from the coordinate ring of a Weierstrass
  curve over a field to a domain is injective as soon as it is injective on `F[X]` (via the norm
  `N(p + q y) = p² − p q (a₁ X + a₃) − q² (X³ + …)` and its degree, Mathlib's
  `degree_norm_smul_basis`);
* `CurvesJacobian.Cusp.mem_range_of_isIntegral₃`: for an injective `φ : B → Ω` from an integrally
  closed domain, an element `z = φ(b) / φ(d)` integral over a ring with image in `φ(B)` lies in
  `φ(B)`;
* `CurvesJacobian.Cusp.constRingPsi₃ : M[W] → R_M` (`m ↦ m`, `x ↦ t`, `y ↦ e(y)`), injective
  (`t` stays transcendental over `M`, `eq_zero_of_eval₂_constι₃`) and surjective (`M[W]` is
  integrally closed for `W` elliptic, elliptic-curves' `instIsIntegrallyClosed`, and every element
  of `L_M` is a quotient of elements of the image, `exists_mul_eq_constRingPhi₃`);
* `CurvesJacobian.Cusp.constRingREquiv₃ : M[W] ≃ₐ[k] R_M`, restricting to `e` on the base change
  `weierBcMap₃ : k[W] → M[W]` (`constRingPhi₃_comp_weierBcMap₃`).

Applied to `D = hemiData E`, `e = hemiREquiv E`:
**`CurvesJacobian.Cusp.hemiConstREquiv : (E.baseChange M).toAffine.CoordinateRing ≃ₐ[K]
(hemiDataM E M).R`**, compatible with the embeddings into `Ω`: polynomials in `x`
(`algebraMap_hemiConstREquiv_of`), constants (`algebraMap_hemiConstREquiv_C`),
`x ↦ coordT (xN E)` (`algebraMap_hemiConstREquiv_X`), `y ↦ hemiRho E Y`
(`algebraMap_hemiConstREquiv_root`), and `K[E] → M[E]` (`algebraMap_hemiConstREquiv_weierBcMap₃`:
it restricts to `hemiREquiv` followed by `R ⊆ R_M`).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Pi1.Orbifold AffOrbicurve Topology
open WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section Generic

/-- **Injectivity criterion for maps out of `F[W]`**: a ring map from the coordinate ring of a
Weierstrass curve over a field `F` to a domain which is injective on `F[X]` is injective. -/
theorem coordRing_injective₃ {F Ω : Type*} [Field F] [CommRing Ω] [IsDomain Ω]
    {W : WeierstrassCurve.Affine F} (φ : W.CoordinateRing →+* Ω)
    (h : ∀ p : F[X], φ (algebraMap F[X] W.CoordinateRing p) = 0 → p = 0) :
    Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun b hb => ?_
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq b
  have h2 : algebraMap F[X] W.CoordinateRing
      (Algebra.norm F[X] (p • (1 : W.CoordinateRing) + q • mk W Y)) =
      mk W ((C p + C q * Y) * (C p + C q * (-(Y : F[X][Y]) - C (C W.a₁ * X + C W.a₃)))) :=
    coe_norm_smul_basis p q
  have h1 : mk W (C p + C q * Y) = p • (1 : W.CoordinateRing) + q • mk W Y := by
    rw [smul, smul, map_add, map_mul, mul_one]
  have hn : φ (algebraMap F[X] W.CoordinateRing
      (Algebra.norm F[X] (p • (1 : W.CoordinateRing) + q • mk W Y))) = 0 := by
    rw [h2, map_mul, map_mul, h1, hb, zero_mul]
  have h0 := congrArg Polynomial.degree (h _ hn)
  rw [degree_norm_smul_basis, degree_zero] at h0
  obtain ⟨hp, hq⟩ := max_eq_bot.1 h0
  rw [two_nsmul, WithBot.add_eq_bot, or_self, degree_eq_bot] at hp
  rcases WithBot.add_eq_bot.1 hq with hq | hq
  · rw [two_nsmul, WithBot.add_eq_bot, or_self, degree_eq_bot] at hq
    rw [hp, hq, zero_smul, zero_smul, add_zero]
  · simp at hq

/-- **Integral elements of the fraction field of an integrally closed image**: let `φ : B → Ω`
be injective, `B` integrally closed, and `A → Ω` with image in `φ(B)`. If `z ∈ Ω` is integral
over `A` and `φ(d) z = φ(b)` with `φ(d) ≠ 0`, then `z ∈ φ(B)`. -/
theorem mem_range_of_isIntegral₃ {A B Ω : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Field Ω] [Algebra A Ω] (φ : B →+* Ω) (hφ : Function.Injective φ)
    (hA : ∀ a : A, algebraMap A Ω a ∈ φ.range) {z : Ω} (hz : IsIntegral A z) {d b : B}
    (hd : φ d ≠ 0) (hdb : φ d * z = φ b) : z ∈ Set.range φ := by
  let e : B ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y hxy => hφ (congrArg Subtype.val hxy), φ.rangeRestrict_surjective⟩
  let g : A →+* B := (e.symm : φ.range →+* B).comp ((algebraMap A Ω).codRestrict φ.range hA)
  have hg : ∀ a, φ (g a) = algebraMap A Ω a := fun a => by
    have h1 : e (e.symm ((algebraMap A Ω).codRestrict φ.range hA a)) =
        (algebraMap A Ω).codRestrict φ.range hA a := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  let φt : FractionRing B →+* Ω := IsFractionRing.lift hφ
  have hd0 : algebraMap B (FractionRing B) d ≠ 0 := fun h0 => hd (by
    rw [← IsFractionRing.lift_algebraMap (K := FractionRing B) hφ d, h0, map_zero])
  have hw : φt (algebraMap B (FractionRing B) b / algebraMap B (FractionRing B) d) = z := by
    rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    rw [← hdb, mul_comm, mul_div_assoc, div_self hd, mul_one]
  have hc : φt.comp ((algebraMap B (FractionRing B)).comp g) = algebraMap A Ω :=
    RingHom.ext fun a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.lift_algebraMap, hg]
  obtain ⟨p, hpm, hp⟩ := hz
  have hint : IsIntegral B
      (algebraMap B (FractionRing B) b / algebraMap B (FractionRing B) d) := by
    refine ⟨p.map g, hpm.map g, φt.injective ?_⟩
    rw [eval₂_map, hom_eval₂, hc, hw, hp, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨y, by rw [← IsFractionRing.lift_algebraMap (K := FractionRing B) hφ y, hy, hw]⟩

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- The embedding `M ⊆ k̄ ⊆ Ω` of an intermediate field `M` of `k̄ / k`. -/
def constι₃ (M : IntermediateField k (ConstField₂ k Ω)) : M →+* Ω :=
  (algebraMap (ConstField₂ k Ω) Ω).comp (algebraMap M (ConstField₂ k Ω))

/-- **A transcendental `t` stays transcendental over `M ⊆ k̄`.** -/
theorem eq_zero_of_eval₂_constι₃ {t : Ω} (ht : Transcendental k t)
    (M : IntermediateField k (ConstField₂ k Ω)) (p : M[X]) (hp : p.eval₂ (constι₃ M) t = 0) :
    p = 0 := by
  by_contra hne
  refine ht (IsAlgebraic.restrictScalars (R := k) (S := ConstField₂ k Ω) ?_)
  refine ⟨p.map (algebraMap M (ConstField₂ k Ω)),
    (Polynomial.map_ne_zero_iff (algebraMap M (ConstField₂ k Ω)).injective).2 hne, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hp

lemma constι₃_comp_algebraMap (M : IntermediateField k (ConstField₂ k Ω)) :
    (constι₃ M).comp (algebraMap k M) = algebraMap k Ω :=
  RingHom.ext fun _ => rfl

lemma isIntegral_constι₃ (t : Ω) (M : IntermediateField k (ConstField₂ k Ω)) (m : M) :
    IsIntegral (A₀ k t) (constι₃ M m) :=
  (mem_algebraicClosure_iff'.1 (m : ConstField₂ k Ω).2).tower_top

lemma eval₂_weierBcMap₃ (W : WeierstrassCurve k) (M : IntermediateField k (ConstField₂ k Ω)) :
    W.toAffine.polynomial.eval₂ ((AdjoinRoot.of (W.baseChange M).toAffine.polynomial).comp
      (mapRingHom (algebraMap k M)))
      (AdjoinRoot.root (W.baseChange M).toAffine.polynomial) = 0 := by
  have hW : (W.baseChange M).toAffine.polynomial =
      W.toAffine.polynomial.map (mapRingHom (algebraMap k M)) :=
    WeierstrassCurve.Affine.map_polynomial (W := W.toAffine) (algebraMap k M)
  rw [← eval₂_map, ← hW, AdjoinRoot.eval₂_root]

variable (k) in
/-- The base change map `k[W] → M[W]` (`x ↦ x`, `y ↦ y`, `c ↦ c`). -/
def weierBcMap₃ (W : WeierstrassCurve k) (M : IntermediateField k (ConstField₂ k Ω)) :
    W.toAffine.CoordinateRing →+* (W.baseChange M).toAffine.CoordinateRing :=
  AdjoinRoot.lift ((AdjoinRoot.of (W.baseChange M).toAffine.polynomial).comp
    (mapRingHom (algebraMap k M))) (AdjoinRoot.root (W.baseChange M).toAffine.polynomial)
    (eval₂_weierBcMap₃ W M)

lemma weierBcMap₃_of (W : WeierstrassCurve k) (M : IntermediateField k (ConstField₂ k Ω))
    (q : k[X]) :
    weierBcMap₃ k W M (AdjoinRoot.of W.toAffine.polynomial q) =
      AdjoinRoot.of (W.baseChange M).toAffine.polynomial (q.map (algebraMap k M)) :=
  AdjoinRoot.lift_of (eval₂_weierBcMap₃ W M)

lemma weierBcMap₃_root (W : WeierstrassCurve k) (M : IntermediateField k (ConstField₂ k Ω)) :
    weierBcMap₃ k W M (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root (W.baseChange M).toAffine.polynomial :=
  AdjoinRoot.lift_root (eval₂_weierBcMap₃ W M)

end Generic

section ConstRing

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero k] {t : Ω}
  [IsGalois (K₀ k t) Ω] (D : GaloisData k t) (M : IntermediateField k (ConstField₂ k Ω))
  [FiniteDimensional k M] [IsGalois k M] (W : WeierstrassCurve k)
  (e : W.toAffine.CoordinateRing ≃ₐ[k] D.R)
  (he : ∀ q : k[X], algebraMap D.R Ω (e (AdjoinRoot.of W.toAffine.polynomial q)) = aeval t q)

/-- `ρ : k[W] ≅ R ⊆ Ω`. -/
abbrev constRingRho₃ : W.toAffine.CoordinateRing →+* Ω :=
  (algebraMap D.R Ω).comp e.toAlgHom.toRingHom

/-- The element `y = ρ(Y) ∈ Ω`. -/
abbrev constRingY₃ : Ω := algebraMap D.R Ω (e (AdjoinRoot.root W.toAffine.polynomial))

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
include he in
lemma eval₂RingHom_comp_mapRingHom₃ :
    (eval₂RingHom (constι₃ M) t).comp (mapRingHom (algebraMap k M)) =
      (constRingRho₃ D W e).comp (AdjoinRoot.of W.toAffine.polynomial) := by
  refine RingHom.ext fun q => ?_
  change (q.map (algebraMap k M)).eval₂ (constι₃ M) t =
    algebraMap D.R Ω (e (AdjoinRoot.of W.toAffine.polynomial q))
  rw [he, eval₂_map, constι₃_comp_algebraMap, aeval_def]

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
include he in
/-- `(x, y) = (t, ρ(Y))` satisfies the Weierstrass equation of `W_M`. -/
theorem eval₂_polynomial_constRingY₃ :
    (W.baseChange M).toAffine.polynomial.eval₂ (eval₂RingHom (constι₃ M) t)
      (constRingY₃ D W e) = 0 := by
  have hW : (W.baseChange M).toAffine.polynomial =
      W.toAffine.polynomial.map (mapRingHom (algebraMap k M)) :=
    WeierstrassCurve.Affine.map_polynomial (W := W.toAffine) (algebraMap k M)
  rw [hW, eval₂_map, eval₂RingHom_comp_mapRingHom₃ D M W e he]
  have h := hom_eval₂ W.toAffine.polynomial (AdjoinRoot.of W.toAffine.polynomial)
    (constRingRho₃ D W e) (AdjoinRoot.root W.toAffine.polynomial)
  rw [AdjoinRoot.eval₂_root, map_zero] at h
  exact h.symm

/-! ### The map `M[W] → R_M` -/

lemma constι₃_mem_L (m : M) : constι₃ M m ∈ (galoisDataConst₃ D M).L := by
  rw [L_galoisDataConst₃]
  exact (le_sup_right : IntermediateField.adjoin (K₀ k t) (constSet₃ M) ≤ _)
    (IntermediateField.subset_adjoin _ _ ⟨m, rfl⟩)

lemma L_le_L_galoisDataConst₃ : D.L ≤ (galoisDataConst₃ D M).L := by
  rw [L_galoisDataConst₃]
  exact le_sup_left

/-- The constants `M → R_M`. -/
def constRingC₃ : M →+* (galoisDataConst₃ D M).R where
  toFun m := CoordRing.mk (constι₃ M m) (constι₃_mem_L D M m) (isIntegral_constι₃ t M m)
  map_one' := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_one])
  map_mul' a b := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_mul])
  map_zero' := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_zero])
  map_add' a b := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_add])

/-- The element `x = t ∈ R_M`. -/
def constRingT₃ : (galoisDataConst₃ D M).R :=
  algebraMap (A₀ k t) (galoisDataConst₃ D M).R ⟨t, Algebra.self_mem_adjoin_singleton k t⟩

/-- The element `y ∈ R_M`. -/
def constRingYR₃ : (galoisDataConst₃ D M).R :=
  CoordRing.mk (constRingY₃ D W e)
    (L_le_L_galoisDataConst₃ D M (CoordRing.algebraMap_mem (e _)))
    (CoordRing.isIntegral_algebraMap (e _))

lemma algebraMap_comp_constRingC₃ :
    (algebraMap (galoisDataConst₃ D M).R Ω).comp
      (eval₂RingHom (constRingC₃ D M) (constRingT₃ D M)) =
      eval₂RingHom (constι₃ M) t := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_C, eval₂_C]
    rfl
  · rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_X, eval₂_X]
    rfl

include he in
lemma eval₂_polynomial_constRingYR₃ :
    (W.baseChange M).toAffine.polynomial.eval₂ (eval₂RingHom (constRingC₃ D M) (constRingT₃ D M))
      (constRingYR₃ D M W e) = 0 := by
  apply CoordRing.algebraMap_injective
  rw [hom_eval₂, map_zero, algebraMap_comp_constRingC₃]
  exact eval₂_polynomial_constRingY₃ D M W e he

/-- **The map `ψ : M[W] → R_M`**, `m ↦ m`, `x ↦ x`, `y ↦ y`. -/
def constRingPsi₃ : (W.baseChange M).toAffine.CoordinateRing →+* (galoisDataConst₃ D M).R :=
  AdjoinRoot.lift _ _ (eval₂_polynomial_constRingYR₃ D M W e he)

/-- `φ = (R_M ⊆ Ω) ∘ ψ : M[W] → Ω`. -/
abbrev constRingPhi₃ : (W.baseChange M).toAffine.CoordinateRing →+* Ω :=
  (algebraMap (galoisDataConst₃ D M).R Ω).comp (constRingPsi₃ D M W e he)

lemma constRingPhi₃_comp_of :
    (constRingPhi₃ D M W e he).comp (AdjoinRoot.of (W.baseChange M).toAffine.polynomial) =
      eval₂RingHom (constι₃ M) t := by
  rw [RingHom.comp_assoc, constRingPsi₃, AdjoinRoot.lift_comp_of, algebraMap_comp_constRingC₃]

lemma constRingPhi₃_of (p : M[X]) :
    constRingPhi₃ D M W e he (AdjoinRoot.of (W.baseChange M).toAffine.polynomial p) =
      p.eval₂ (constι₃ M) t :=
  RingHom.congr_fun (constRingPhi₃_comp_of D M W e he) p

lemma constRingPhi₃_root :
    constRingPhi₃ D M W e he (AdjoinRoot.root (W.baseChange M).toAffine.polynomial) =
      constRingY₃ D W e := by
  change algebraMap (galoisDataConst₃ D M).R Ω
    (AdjoinRoot.lift _ _ (eval₂_polynomial_constRingYR₃ D M W e he)
      (AdjoinRoot.root (W.baseChange M).toAffine.polynomial)) = _
  rw [AdjoinRoot.lift_root]
  rfl

/-- **`φ ∘ (k[W] → M[W]) = ρ`.** -/
theorem constRingPhi₃_comp_weierBcMap₃ :
    (constRingPhi₃ D M W e he).comp (weierBcMap₃ k W M) = constRingRho₃ D W e := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext fun q => ?_) ?_
  · change constRingPhi₃ D M W e he (weierBcMap₃ k W M (AdjoinRoot.of W.toAffine.polynomial q)) =
      algebraMap D.R Ω (e (AdjoinRoot.of W.toAffine.polynomial q))
    rw [weierBcMap₃_of, constRingPhi₃_of, eval₂_map, constι₃_comp_algebraMap, he, aeval_def]
  · change constRingPhi₃ D M W e he (weierBcMap₃ k W M (AdjoinRoot.root W.toAffine.polynomial)) =
      constRingY₃ D W e
    rw [weierBcMap₃_root, constRingPhi₃_root]

/-- **`φ` is injective**: `t` is transcendental over `M`. -/
theorem constRingPhi₃_injective : Function.Injective (constRingPhi₃ D M W e he) :=
  coordRing_injective₃ _ fun p hp => eq_zero_of_eval₂_constι₃ D.transcendental M p
    (by rw [← constRingPhi₃_of D M W e he p, ← AdjoinRoot.algebraMap_eq]; exact hp)

/-! ### Surjectivity -/

/-- The elements of `L` are quotients of elements of `ρ(k[W]) ⊆ φ(M[W])`. -/
lemma exists_mul_eq_of_mem_L₃ {z : Ω} (hz : z ∈ D.L) :
    ∃ d b : (W.baseChange M).toAffine.CoordinateRing,
      constRingPhi₃ D M W e he d ≠ 0 ∧
        constRingPhi₃ D M W e he d * z = constRingPhi₃ D M W e he b := by
  haveI := isFractionRing_coordRing t D.L
  obtain ⟨a, c, hc, hac⟩ := IsFractionRing.div_surjective
    (A := coordRing k t D.L) (⟨z, hz⟩ : D.L)
  have hz' := congrArg (IntermediateField.val D.L) hac
  rw [map_div₀] at hz'
  change algebraMap D.R Ω a / algebraMap D.R Ω c = z at hz'
  have hρ : ∀ r : D.R,
      constRingPhi₃ D M W e he (weierBcMap₃ k W M (e.symm r)) = algebraMap D.R Ω r := by
    intro r
    rw [← RingHom.comp_apply, constRingPhi₃_comp_weierBcMap₃]
    change algebraMap D.R Ω (e (e.symm r)) = _
    rw [AlgEquiv.apply_symm_apply]
  have hc0 : algebraMap D.R Ω c ≠ 0 := by
    intro h0
    refine nonZeroDivisors.ne_zero hc ?_
    exact CoordRing.algebraMap_injective (h0.trans (map_zero _).symm)
  refine ⟨weierBcMap₃ k W M (e.symm c), weierBcMap₃ k W M (e.symm a), ?_, ?_⟩
  · rw [hρ]
    exact hc0
  · rw [hρ, hρ, ← hz', mul_comm, div_mul_cancel₀ _ hc0]

/-- **Every element of `L_M` is a quotient of elements of `φ(M[W])`.** -/
theorem exists_mul_eq_constRingPhi₃ {z : Ω} (hz : z ∈ (galoisDataConst₃ D M).L) :
    ∃ d b : (W.baseChange M).toAffine.CoordinateRing,
      constRingPhi₃ D M W e he d ≠ 0 ∧
        constRingPhi₃ D M W e he d * z = constRingPhi₃ D M W e he b := by
  let S : IntermediateField (K₀ k t) Ω :=
    { carrier := {z | ∃ d b : (W.baseChange M).toAffine.CoordinateRing,
        constRingPhi₃ D M W e he d ≠ 0 ∧
          constRingPhi₃ D M W e he d * z = constRingPhi₃ D M W e he b}
      mul_mem' := by
        rintro z₁ z₂ ⟨d₁, b₁, hd₁, h₁⟩ ⟨d₂, b₂, hd₂, h₂⟩
        refine ⟨d₁ * d₂, b₁ * b₂, ?_, ?_⟩
        · rw [map_mul]
          exact mul_ne_zero hd₁ hd₂
        · rw [map_mul, map_mul, ← h₁, ← h₂]
          ring
      add_mem' := by
        rintro z₁ z₂ ⟨d₁, b₁, hd₁, h₁⟩ ⟨d₂, b₂, hd₂, h₂⟩
        refine ⟨d₁ * d₂, d₂ * b₁ + d₁ * b₂, ?_, ?_⟩
        · rw [map_mul]
          exact mul_ne_zero hd₁ hd₂
        · rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]
          ring
      algebraMap_mem' := fun c => exists_mul_eq_of_mem_L₃ D M W e he (D.L.algebraMap_mem c)
      inv_mem' := by
        rintro z ⟨d, b, hd, h⟩
        by_cases hz0 : z = 0
        · refine ⟨1, 0, ?_, ?_⟩
          · rw [map_one]
            exact one_ne_zero
          · rw [hz0, inv_zero, mul_zero, map_zero]
        · have hb : constRingPhi₃ D M W e he b ≠ 0 := by
            rw [← h]
            exact mul_ne_zero hd hz0
          refine ⟨b, d, hb, ?_⟩
          rw [← h, mul_assoc, mul_inv_cancel₀ hz0, mul_one] }
  have hle : (galoisDataConst₃ D M).L ≤ S := by
    rw [L_galoisDataConst₃]
    refine sup_le (fun w hw => exists_mul_eq_of_mem_L₃ D M W e he hw) ?_
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨m, rfl⟩
    refine ⟨1, AdjoinRoot.of _ (C m), ?_, ?_⟩
    · rw [map_one]
      exact one_ne_zero
    · rw [map_one, one_mul, constRingPhi₃_of, eval₂_C]
      rfl
  exact hle hz

/-- `k[t] ⊆ φ(M[W])`. -/
lemma algebraMap_A₀_mem_range_constRingPhi₃ (a : A₀ k t) :
    algebraMap (A₀ k t) Ω a ∈ (constRingPhi₃ D M W e he).range := by
  obtain ⟨a, ha⟩ := a
  change a ∈ (constRingPhi₃ D M W e he).range
  induction ha using Algebra.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨AdjoinRoot.of _ X, by rw [constRingPhi₃_of, eval₂_X]⟩
  | algebraMap c =>
    exact ⟨AdjoinRoot.of _ (C (algebraMap k M c)), by rw [constRingPhi₃_of, eval₂_C]; rfl⟩
  | add w v _ _ hw hv => exact add_mem hw hv
  | mul w v _ _ hw hv => exact mul_mem hw hv

variable [W.IsElliptic]

instance isElliptic_baseChange₃ : (W.baseChange M).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap k M)).IsElliptic)

/-- **`ψ` is surjective**: `M[W]` is integrally closed (elliptic-curves). -/
theorem constRingPsi₃_surjective : Function.Surjective (constRingPsi₃ D M W e he) := by
  intro r
  obtain ⟨d, b, hd, hdb⟩ := exists_mul_eq_constRingPhi₃ D M W e he (CoordRing.algebraMap_mem r)
  obtain ⟨y, hy⟩ := mem_range_of_isIntegral₃ (constRingPhi₃ D M W e he)
    (constRingPhi₃_injective D M W e he) (algebraMap_A₀_mem_range_constRingPhi₃ D M W e he)
    (CoordRing.isIntegral_algebraMap r) hd hdb
  exact ⟨y, CoordRing.ext hy⟩

omit [W.IsElliptic] in
lemma constRingPsi₃_algebraMap (c : k) :
    constRingPsi₃ D M W e he (algebraMap k (W.baseChange M).toAffine.CoordinateRing c) =
      algebraMap k (galoisDataConst₃ D M).R c := by
  apply CoordRing.ext
  rw [← IsScalarTower.algebraMap_apply k (galoisDataConst₃ D M).R Ω]
  have h : algebraMap k (W.baseChange M).toAffine.CoordinateRing c =
      AdjoinRoot.of _ (C (algebraMap k M c)) := by
    rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply]
  change constRingPhi₃ D M W e he _ = _
  rw [h, constRingPhi₃_of, eval₂_C]
  rfl

/-- **`M[W] ≃ₐ[k] R_M`** (generic form). -/
def constRingREquiv₃ : (W.baseChange M).toAffine.CoordinateRing ≃ₐ[k] (galoisDataConst₃ D M).R :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _
    ⟨fun _ _ h => constRingPhi₃_injective D M W e he (congrArg (algebraMap _ Ω) h),
      constRingPsi₃_surjective D M W e he⟩) (constRingPsi₃_algebraMap D M W e he)

lemma algebraMap_constRingREquiv₃ (a : (W.baseChange M).toAffine.CoordinateRing) :
    algebraMap (galoisDataConst₃ D M).R Ω (constRingREquiv₃ D M W e he a) =
      constRingPhi₃ D M W e he a := rfl

end ConstRing

section Hemi

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E)))) [FiniteDimensional K M]
  [IsGalois K M]

lemma hemiREquiv_of₃ (q : K[X]) :
    algebraMap (hemiData E).R (FFClosure (curveE E))
      (hemiREquiv E (AdjoinRoot.of E.toAffine.polynomial q)) = aeval (coordT (xN E)) q :=
  (hemiRho_apply E _).symm.trans (hemiRho_of E q)

/-- **`M[E] ≃ₐ[K] R_M`**: the coordinate ring of `E_M = E ×_K M` is the ring `R_M` (the integral
closure of `K[x]` in `L_M = K(E) · M`) of the Galois data `hemiDataM E M` of `V = X_M`. -/
def hemiConstREquiv : (E.baseChange M).toAffine.CoordinateRing ≃ₐ[K] (hemiDataM E M).R :=
  constRingREquiv₃ (hemiData E) M E (hemiREquiv E) (hemiREquiv_of₃ E)

/-- On `M[X] ⊆ M[E]`: `p ↦ p(x)` (constants `m ↦ m ∈ Ω`, `x ↦ x = coordT (xN E)`). -/
theorem algebraMap_hemiConstREquiv_of (p : M[X]) :
    algebraMap (hemiDataM E M).R (FFClosure (curveE E))
      (hemiConstREquiv E M (AdjoinRoot.of (E.baseChange M).toAffine.polynomial p)) =
      p.eval₂ (constι₃ M) (coordT (xN E)) :=
  constRingPhi₃_of (hemiData E) M E (hemiREquiv E) (hemiREquiv_of₃ E) p

/-- Constants: `m ↦ m`. -/
theorem algebraMap_hemiConstREquiv_C (m : M) :
    algebraMap (hemiDataM E M).R (FFClosure (curveE E))
      (hemiConstREquiv E M (AdjoinRoot.of (E.baseChange M).toAffine.polynomial (C m))) =
      ((m : ConstField₂ K (FFClosure (curveE E))) : FFClosure (curveE E)) := by
  rw [algebraMap_hemiConstREquiv_of, eval₂_C]
  rfl

/-- `x ↦ x = coordT (xN E)`. -/
theorem algebraMap_hemiConstREquiv_X :
    algebraMap (hemiDataM E M).R (FFClosure (curveE E))
      (hemiConstREquiv E M (AdjoinRoot.of (E.baseChange M).toAffine.polynomial X)) =
      coordT (xN E) := by
  rw [algebraMap_hemiConstREquiv_of, eval₂_X]

/-- `y ↦ y`, the `y` of `hemiData E` (`hemiRho`). -/
theorem algebraMap_hemiConstREquiv_root :
    algebraMap (hemiDataM E M).R (FFClosure (curveE E))
      (hemiConstREquiv E M (AdjoinRoot.root (E.baseChange M).toAffine.polynomial)) =
      hemiRho E (AdjoinRoot.root E.toAffine.polynomial) :=
  (constRingPhi₃_root (hemiData E) M E (hemiREquiv E) (hemiREquiv_of₃ E)).trans
    (hemiRho_apply E _).symm

/-- **Compatibility with `K[E] ≃ R`** (`hemiREquiv`): on the image of the base change map
`K[E] → M[E]`, `hemiConstREquiv` is `hemiREquiv` followed by `R ⊆ R_M`. -/
theorem algebraMap_hemiConstREquiv_weierBcMap₃ (a : E.toAffine.CoordinateRing) :
    algebraMap (hemiDataM E M).R (FFClosure (curveE E))
      (hemiConstREquiv E M (weierBcMap₃ K E M a)) =
      algebraMap (hemiData E).R (FFClosure (curveE E)) (hemiREquiv E a) :=
  RingHom.congr_fun
    (constRingPhi₃_comp_weierBcMap₃ (hemiData E) M E (hemiREquiv E) (hemiREquiv_of₃ E)) a

end Hemi

end CurvesJacobian.Cusp
