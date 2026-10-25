/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiConstArith
import CurvesJacobian.Cusp.HemiModelTwist

/-!
# Twists in the hemi-elliptic orbicurve (MR8, [AbsTopII] Cor. 3.3, IUT I Def. 3.1(b))

IUT applies [AbsTopII] Cor. 3.3 with base the `F_mod`-model `C_K` of the hemi-elliptic orbicurve
(IUT I Def. 3.1(b), Rem. 3.1.7(i)): its coarse space is the `x`-line, which does not see
quadratic twists. In Galois form (`CurvesJacobian.Cusp.HemiPi1`), `C_K` is `hemiData E'` for an
elliptic curve `E'` over a number field `K` (`Ω = K(Ē')^alg`, `t = x'`, `H = Gal(Ω / K(x'))`).
Let `M ⊆ k̄` be finite Galois over `K` and `E` an elliptic curve over `M` with
`Ψ₂Sq_{E'} (u2 X + r) = u2³ Ψ₂Sq_E (X)` (`u2 ≠ 0`; e.g. `j(E) = j(E') ∉ {0, 1728}`,
`exists_Ψ₂Sq_comp_xrat₃`), so `x' = u2 x_E + r`. We build `E` inside the same `Ω`:

* generic (`k`, `Ω`, `t`, `M`, a Weierstrass curve `W` over `M`): `xTw = u2⁻¹ (t − r)`
  (transcendental, `transcendental_xTw`), `yTw` a root of the Weierstrass equation of `W` at
  `xTw`, and the injective `twRho : M[W] → Ω` (`twRho_injective`);
* `twGalData`: the Galois data with `H = Gal(Ω / k(t)(M))` (`constFixer₃`) and
  `H_L = Gal(Ω / k(t)(M)(yTw))`; its function field is `k(t)(M) ⊔ k(t)(yTw)` (`twGalData_L`),
  `twREquiv : M[W] ≃ₐ[k] R` (integral closedness of `M[W]`), `[H : H_L] = 2`
  (`relIndex_twGalData_HL`: `yTw ∉ k(t)(M)` since `Ψ₂Sq` has odd degree) and
  `[Gal(Ω / k(t)) : H_L] = 2 · [M : k]` (`index_twGalData_HL`);
* `fix_iff_fix_yTw`: for a curve `E₀` over `k` with `y'` on `E₀` over `t`, `c = ψ₂' / ψ₂`
  satisfies `c² = u2³`, so `c ∈ k̄` and an element acting trivially on `k̄` fixes `y'` iff it
  fixes `yTw`;
* `twInclX`, `twInclC`, `twCEquiv`: maps between `H ⧸ ⟨⟨S⟩⟩` for Galois data with equal inertia.

For `hemiData E'` (`hemiTwData E' M E u2 r`):

* **same inertia** `hemiTwData_S : S(hemiTwData) = S(hemiData E')` (T3);
* `hemiTwCEquiv`: `Π_{C_M}` of `E` and of `E'_M` coincide (T4); `hemiTw_constExt`:
  `Π_{C_M} ↪ Π_C` open, normal, of index `[M : K]`; `hemiTw_orbiIncl`: `Π_{X_M} ↪ Π_{C_M}` of
  index `2`;
* `hemiTwPiXGal : Π_{E ∖ O} ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩` (cj's `arithmeticExt` over `M`), `hemiTwGkEquiv`,
  `hemiTwGkEquiv_pr`, and **`hemiTw_arith_emb`**: `hemiTwEmbC : Π_{E ∖ O} → Π_C` is an open
  embedding of index `2 · [M : K]`, compatible with the projections to `Gal(k̄ / K)`, with image
  inside `Π_{C_M}` (T5);
* `hemiTw_exists_arith_emb`: the combined statement for `j(E) = j(E') ∉ {0, 1728}` (T6).

Note: `H = Gal(Ω / K(x'))` is in general **not** allowed for the twist: `H_L` need not be normal
in `Gal(Ω / K(x'))` (the twist class `u2 ∈ M^×/M^×²` need not be `Gal(M / K)`-invariant), so
the twist lives over `C_M` and `Π_{E ∖ O}` is open, but not necessarily normal, in `Π_C`.
-/
open CategoryTheory AlgebraicGeometry Polynomial Belyi Pi1.Orbifold AffOrbicurve Topology
open WeierstrassCurve.Affine.CoordinateRing

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section TwGeneric

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)
  (M : IntermediateField k (ConstField₂ k Ω))

/-- The `x`-coordinate `x = u2⁻¹ (t − r)` of the twisted curve, for `t = u2 x + r`. -/
def xTw (u2 r : M) : Ω := constι₃ M u2⁻¹ * (t - constι₃ M r)

lemma constι₃_mul_xTw {u2 : M} (hu2 : u2 ≠ 0) (r : M) :
    constι₃ M u2 * xTw t M u2 r + constι₃ M r = t := by
  rw [xTw, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hu2, map_one, one_mul, sub_add_cancel]

lemma isIntegral_constι₃_k (M : IntermediateField k (ConstField₂ k Ω)) (m : M) :
    IsIntegral k (constι₃ M m) :=
  mem_algebraicClosure_iff'.1 (m : ConstField₂ k Ω).2

/-- **`x` is transcendental**: `t = u2 x + r` with `u2, r` algebraic. -/
theorem transcendental_xTw (ht : Transcendental k t) {u2 : M} (hu2 : u2 ≠ 0) (r : M) :
    Transcendental k (xTw t M u2 r) := by
  intro h
  refine ht ?_
  rw [← constι₃_mul_xTw t M hu2 r]
  exact (((isIntegral_constι₃_k M u2).mul h.isIntegral).add
    (isIntegral_constι₃_k M r)).isAlgebraic

lemma eq_zero_of_eval₂_xTw (ht : Transcendental k t) {u2 : M} (hu2 : u2 ≠ 0) (r : M)
    (p : M[X]) (hp : p.eval₂ (constι₃ M) (xTw t M u2 r) = 0) : p = 0 :=
  eq_zero_of_eval₂_constι₃ (transcendental_xTw t M ht hu2 r) M p hp

/-- A root `y` of the Weierstrass equation of `W` over the point `x` exists in `Ω`. -/
lemma exists_eval₂_polynomial_tw [IsAlgClosed Ω] (W : WeierstrassCurve M) (x : Ω) :
    ∃ y : Ω, W.toAffine.polynomial.eval₂ (eval₂RingHom (constι₃ M) x) y = 0 := by
  have hm : (W.toAffine.polynomial.map (eval₂RingHom (constι₃ M) x)).Monic :=
    WeierstrassCurve.Affine.monic_polynomial.map _
  have hd : (W.toAffine.polynomial.map (eval₂RingHom (constι₃ M) x)).natDegree = 2 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.natDegree_map,
      WeierstrassCurve.Affine.natDegree_polynomial]
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (W.toAffine.polynomial.map (eval₂RingHom (constι₃ M) x)) (by
      rw [degree_eq_natDegree hm.ne_zero, hd]
      norm_num)
  exact ⟨y, by rwa [IsRoot, Polynomial.eval_map] at hy⟩

/-- **Quotients of `φ`-values**: the subfield of `z ∈ Ω` with `φ(d) z = φ(b)`, `φ(d) ≠ 0`. -/
def quotSubfieldTw {B : Type*} [CommRing B] (φ : B →+* Ω) : Subfield Ω where
  carrier := {z | ∃ d b : B, φ d ≠ 0 ∧ φ d * z = φ b}
  mul_mem' := by
    rintro z₁ z₂ ⟨d₁, b₁, hd₁, h₁⟩ ⟨d₂, b₂, hd₂, h₂⟩
    refine ⟨d₁ * d₂, b₁ * b₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hd₁ hd₂
    · rw [map_mul, map_mul, ← h₁, ← h₂]
      ring
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [mul_one]⟩
  add_mem' := by
    rintro z₁ z₂ ⟨d₁, b₁, hd₁, h₁⟩ ⟨d₂, b₂, hd₂, h₂⟩
    refine ⟨d₁ * d₂, d₂ * b₁ + d₁ * b₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hd₁ hd₂
    · rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]
      ring
  zero_mem' := ⟨1, 0, by rw [map_one]; exact one_ne_zero, by rw [mul_zero, map_zero]⟩
  neg_mem' := by
    rintro z ⟨d, b, hd, h⟩
    exact ⟨d, -b, hd, by rw [mul_neg, h, map_neg]⟩
  inv_mem' := by
    rintro z ⟨d, b, hd, h⟩
    by_cases hz0 : z = 0
    · refine ⟨1, 0, ?_, ?_⟩
      · rw [map_one]
        exact one_ne_zero
      · rw [hz0, inv_zero, mul_zero, map_zero]
    · have hb : φ b ≠ 0 := by
        rw [← h]
        exact mul_ne_zero hd hz0
      refine ⟨b, d, hb, ?_⟩
      rw [← h, mul_assoc, mul_inv_cancel₀ hz0, mul_one]

lemma map_mem_quotSubfieldTw {B : Type*} [CommRing B] (φ : B →+* Ω) (b : B) :
    φ b ∈ quotSubfieldTw φ :=
  ⟨1, b, by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩

/-- If `k`, `t` and `T` consist of quotients of `φ`-values, so does `k(t)(T)`. -/
lemma mem_quotSubfieldTw_of_mem_adjoin {B : Type*} [CommRing B] (φ : B →+* Ω) (T : Set Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ quotSubfieldTw φ) (htq : t ∈ quotSubfieldTw φ)
    (hT : T ⊆ quotSubfieldTw φ) {z : Ω} (hz : z ∈ IntermediateField.adjoin (K₀ k t) T) :
    z ∈ quotSubfieldTw φ := by
  have hK : ∀ c : K₀ k t, (c : Ω) ∈ quotSubfieldTw φ := by
    rintro ⟨c, hc⟩
    change c ∈ (IntermediateField.adjoin k {t}).toSubfield at hc
    rw [IntermediateField.adjoin_toSubfield] at hc
    refine Subfield.closure_le.2 ?_ hc
    rintro _ (⟨c, rfl⟩ | hw)
    · exact hk c
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact htq
  change z ∈ (IntermediateField.adjoin (K₀ k t) T).toSubfield at hz
  rw [IntermediateField.adjoin_toSubfield] at hz
  refine Subfield.closure_le.2 ?_ hz
  rintro _ (⟨c, rfl⟩ | hw)
  · exact hK c
  · exact hT hw

/-- **`ψ₂² = Ψ₂Sq`** at a point `(x, y)` of a Weierstrass curve:
`(2 y + a₁ x + a₃)² = 4 x³ + b₂ x² + 2 b₄ x + b₆`. -/
lemma sq_psi₂_eval_tw {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    (W : WeierstrassCurve R) (x y : A)
    (h : y ^ 2 + (f W.a₁ * x + f W.a₃) * y -
      (x ^ 3 + f W.a₂ * x ^ 2 + f W.a₄ * x + f W.a₆) = 0) :
    (2 * y + (f W.a₁ * x + f W.a₃)) ^ 2 = W.Ψ₂Sq.eval₂ f x := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, eval₂_ofNat, map_add,
    map_mul, map_pow, map_ofNat]
  linear_combination 4 * h

variable [IsAlgClosed Ω] (W : WeierstrassCurve M) (u2 r : M)

/-- The `y`-coordinate of the twisted curve: a root of the Weierstrass equation of `W` at `xTw`. -/
def yTw : Ω := Classical.choose (exists_eval₂_polynomial_tw M W (xTw t M u2 r))

lemma eval₂_polynomial_yTw :
    W.toAffine.polynomial.eval₂ (eval₂RingHom (constι₃ M) (xTw t M u2 r)) (yTw t M W u2 r) = 0 :=
  Classical.choose_spec (exists_eval₂_polynomial_tw M W (xTw t M u2 r))

/-- The coefficient `a₁ x + a₃` of the Weierstrass equation at `xTw`. -/
abbrev twC1 : Ω := constι₃ M W.a₁ * xTw t M u2 r + constι₃ M W.a₃

/-- The coefficient `x³ + a₂ x² + a₄ x + a₆` of the Weierstrass equation at `xTw`. -/
abbrev twC0 : Ω := xTw t M u2 r ^ 3 + constι₃ M W.a₂ * xTw t M u2 r ^ 2 +
  constι₃ M W.a₄ * xTw t M u2 r + constι₃ M W.a₆

/-- The Weierstrass equation `y² + (a₁ x + a₃) y − (x³ + a₂ x² + a₄ x + a₆) = 0`. -/
lemma yTw_eq : yTw t M W u2 r ^ 2 + twC1 t M W u2 r * yTw t M W u2 r - twC0 t M W u2 r = 0 := by
  have h := eval₂_polynomial_yTw t M W u2 r
  rw [WeierstrassCurve.Affine.polynomial] at h
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom]
    at h
  linear_combination h

/-- **The embedding `ρ : M[W] → Ω`**, `m ↦ m`, `x ↦ xTw`, `y ↦ yTw`. -/
def twRho : W.toAffine.CoordinateRing →+* Ω :=
  AdjoinRoot.lift (eval₂RingHom (constι₃ M) (xTw t M u2 r)) (yTw t M W u2 r)
    (eval₂_polynomial_yTw t M W u2 r)

lemma twRho_of (p : M[X]) :
    twRho t M W u2 r (AdjoinRoot.of W.toAffine.polynomial p) =
      p.eval₂ (constι₃ M) (xTw t M u2 r) :=
  AdjoinRoot.lift_of _

lemma twRho_root :
    twRho t M W u2 r (AdjoinRoot.root W.toAffine.polynomial) = yTw t M W u2 r :=
  AdjoinRoot.lift_root _

/-- **`ρ` is injective** (`xTw` is transcendental over `M`). -/
theorem twRho_injective (ht : Transcendental k t) {u2 : M} (hu2 : u2 ≠ 0) :
    Function.Injective (twRho t M W u2 r) :=
  coordRing_injective₃ _ fun p hp => eq_zero_of_eval₂_xTw t M ht hu2 r p (by
    rw [← twRho_of t M W u2 r p, ← AdjoinRoot.algebraMap_eq]
    exact hp)

end TwGeneric

section TwData

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero k] (t : Ω)
  [IsGalois (K₀ k t) Ω] (M : IntermediateField k (ConstField₂ k Ω)) [FiniteDimensional k M]
  [IsGalois k M] (W : WeierstrassCurve M) (u2 r : M)

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] in
lemma mem_fixingSubgroup_adjoin_singleton_tw (y : Ω) (σ : Ω ≃ₐ[K₀ k t] Ω) :
    σ ∈ (IntermediateField.adjoin (K₀ k t) {y}).fixingSubgroup ↔ σ y = y := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h y (IntermediateField.subset_adjoin _ _ rfl)
  · intro h x hx
    refine (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := K₀ k t) (S := {y})
      σ).2 ?_ x hx
    rintro _ rfl
    exact h

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma fix_constι₃_tw {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ constFixer₃ t M) (m : M) :
    σ (constι₃ M m) = constι₃ M m := by
  have h' : galResConst t σ ∈ M.fixingSubgroup := hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at h'
  exact congrArg Subtype.val (h' m m.2)

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma fix_t_tw (σ : Ω ≃ₐ[K₀ k t] Ω) : σ t = t :=
  σ.commutes ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma fix_xTw {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ constFixer₃ t M) :
    σ (xTw t M u2 r) = xTw t M u2 r := by
  rw [xTw, map_mul, map_sub, fix_constι₃_tw t M hσ, fix_constι₃_tw t M hσ, fix_t_tw]

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma fix_twC1 {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ constFixer₃ t M) :
    σ (twC1 t M W u2 r) = twC1 t M W u2 r := by
  simp only [twC1, map_add, map_mul, fix_constι₃_tw t M hσ, fix_xTw t M u2 r hσ]

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma fix_twC0 {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ constFixer₃ t M) :
    σ (twC0 t M W u2 r) = twC0 t M W u2 r := by
  simp only [twC0, map_add, map_mul, map_pow, fix_constι₃_tw t M hσ, fix_xTw t M u2 r hσ]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
/-- An element of `Gal(Ω / k(t)(M))` maps `yTw` to `yTw` or to `−yTw − a₁ xTw − a₃`. -/
lemma yTw_or {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ constFixer₃ t M) :
    σ (yTw t M W u2 r) = yTw t M W u2 r ∨
      σ (yTw t M W u2 r) = -yTw t M W u2 r - twC1 t M W u2 r := by
  have hz : σ (yTw t M W u2 r) ^ 2 + twC1 t M W u2 r * σ (yTw t M W u2 r) -
      twC0 t M W u2 r = 0 := by
    have h := congrArg σ (yTw_eq t M W u2 r)
    rwa [map_sub, map_add, map_mul, map_pow, map_zero, fix_twC1 t M W u2 r hσ,
      fix_twC0 t M W u2 r hσ] at h
  exact eq_or_eq_neg_sub_of_quadratic₂ (yTw_eq t M W u2 r) hz

omit [CharZero k] [FiniteDimensional k M] [IsGalois k M] in
/-- The function field `k(t)(M)(yTw)` of the twisted curve is finite over `k(t)`, so its fixing
subgroup is open. -/
lemma isOpen_fixingSubgroup_yTw :
    IsOpen ((IntermediateField.adjoin (K₀ k t) {yTw t M W u2 r}).fixingSubgroup :
      Set (Ω ≃ₐ[K₀ k t] Ω)) := by
  haveI := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K₀ k t) (yTw t M W u2 r))
  exact IntermediateField.fixingSubgroup_isOpen _

/-- **The Galois data of the twisted curve** `X_M = W ∖ {O}` inside the orbicurve `C_M`:
`H = Gal(Ω / k(t)(M))`, `H_L = Gal(Ω / k(t)(M)(yTw))`. -/
def twGalData (ht : Transcendental k t) : GaloisData k t where
  H := constFixer₃ t M
  HL := constFixer₃ t M ⊓ (IntermediateField.adjoin (K₀ k t) {yTw t M W u2 r}).fixingSubgroup
  le := inf_le_left
  isOpen_HL := (isOpen_constFixer₃ M).inter (isOpen_fixingSubgroup_yTw t M W u2 r)
  conj_mem := fun h hh n hn => by
    refine ⟨(constFixer₃_normal M).conj_mem n hn.1 h,
      (mem_fixingSubgroup_adjoin_singleton_tw t _ _).2 ?_⟩
    have hn2 : n (yTw t M W u2 r) = yTw t M W u2 r :=
      (mem_fixingSubgroup_adjoin_singleton_tw t _ _).1 hn.2
    have hhi : h (h⁻¹ (yTw t M W u2 r)) = yTw t M W u2 r := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have key : n (h⁻¹ (yTw t M W u2 r)) = h⁻¹ (yTw t M W u2 r) := by
      rcases yTw_or t M W u2 r ((constFixer₃ t M).inv_mem hh) with h1 | h1
      · rw [h1, hn2]
      · rw [h1, map_sub, map_neg, hn2, fix_twC1 t M W u2 r hn.1]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, key, hhi]
  transcendental := ht

variable (ht : Transcendental k t)

lemma twGalData_H : (twGalData t M W u2 r ht).H = constFixer₃ t M := rfl

lemma twGalData_HL : (twGalData t M W u2 r ht).HL =
    constFixer₃ t M ⊓ (IntermediateField.adjoin (K₀ k t) {yTw t M W u2 r}).fixingSubgroup := rfl

/-- **The function field of the twisted curve**: `L = k(t)(M) ⊔ k(t)(yTw)`. -/
theorem twGalData_L : (twGalData t M W u2 r ht).L =
    IntermediateField.adjoin (K₀ k t) (constSet₃ M) ⊔
      IntermediateField.adjoin (K₀ k t) {yTw t M W u2 r} := by
  change IntermediateField.fixedField (constFixer₃ t M ⊓ _) = _
  rw [← fixingSubgroup_adjoin_constSet₃, ← IntermediateField.fixingSubgroup_sup,
    InfiniteGalois.fixedField_fixingSubgroup]

lemma adjoin_constSet₃_le_twL :
    IntermediateField.adjoin (K₀ k t) (constSet₃ M) ≤ (twGalData t M W u2 r ht).L := by
  rw [twGalData_L]
  exact le_sup_left

lemma yTw_mem_twL : yTw t M W u2 r ∈ (twGalData t M W u2 r ht).L := by
  rw [twGalData_L]
  exact (le_sup_right : IntermediateField.adjoin (K₀ k t) {yTw t M W u2 r} ≤ _)
    (IntermediateField.subset_adjoin _ _ rfl)

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma xTw_mem_adjoin_constSet₃ :
    xTw t M u2 r ∈ IntermediateField.adjoin (K₀ k t) (constSet₃ M) :=
  mul_mem (IntermediateField.subset_adjoin _ _ ⟨u2⁻¹, rfl⟩)
    (sub_mem (IntermediateField.algebraMap_mem _
      (⟨t, IntermediateField.mem_adjoin_simple_self k t⟩ : K₀ k t))
      (IntermediateField.subset_adjoin _ _ ⟨r, rfl⟩))

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma isIntegral_t_tw : IsIntegral (A₀ k t) t :=
  isIntegral_algebraMap (R := A₀ k t) (A := Ω)
    (x := (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : A₀ k t))

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma isIntegral_xTw : IsIntegral (A₀ k t) (xTw t M u2 r) :=
  (isIntegral_constι₃ t M _).mul ((isIntegral_t_tw t).sub (isIntegral_constι₃ t M r))

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma isIntegral_twC1 : IsIntegral (A₀ k t) (twC1 t M W u2 r) :=
  ((isIntegral_constι₃ t M _).mul (isIntegral_xTw t M u2 r)).add (isIntegral_constι₃ t M _)

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
lemma isIntegral_twC0 : IsIntegral (A₀ k t) (twC0 t M W u2 r) :=
  ((((isIntegral_xTw t M u2 r).pow 3).add
    ((isIntegral_constι₃ t M _).mul ((isIntegral_xTw t M u2 r).pow 2))).add
      ((isIntegral_constι₃ t M _).mul (isIntegral_xTw t M u2 r))).add (isIntegral_constι₃ t M _)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
/-- `ψ₂ = 2 yTw + a₁ xTw + a₃` is integral over `k[t]` (`ψ₂² = (a₁ x + a₃)² + 4 (x³ + …)`). -/
lemma isIntegral_twψ : IsIntegral (A₀ k t) (2 * yTw t M W u2 r + twC1 t M W u2 r) := by
  have hsq : (2 * yTw t M W u2 r + twC1 t M W u2 r) ^ 2 =
      twC1 t M W u2 r ^ 2 + algebraMap (A₀ k t) Ω 4 * twC0 t M W u2 r := by
    rw [map_ofNat]
    linear_combination 4 * yTw_eq t M W u2 r
  refine IsIntegral.of_pow two_pos ?_
  rw [hsq]
  exact ((isIntegral_twC1 t M W u2 r).pow 2).add
    ((isIntegral_algebraMap (R := A₀ k t) (A := Ω)).mul (isIntegral_twC0 t M W u2 r))

omit [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
lemma isIntegral_yTw : IsIntegral (A₀ k t) (yTw t M W u2 r) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have h2 : IsIntegral (A₀ k t) ((2 : Ω)⁻¹) := by
    have h := isIntegral_algebraMap (R := A₀ k t) (A := Ω) (x := algebraMap k (A₀ k t) 2⁻¹)
    rwa [← IsScalarTower.algebraMap_apply, map_inv₀, map_ofNat] at h
  have he : yTw t M W u2 r = (2 * yTw t M W u2 r + twC1 t M W u2 r - twC1 t M W u2 r) * 2⁻¹ := by
    rw [add_sub_cancel_right, mul_comm, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
  rw [he]
  exact ((isIntegral_twψ t M W u2 r).sub (isIntegral_twC1 t M W u2 r)).mul h2

/-! ### `R ≅ M[W]` -/

/-- The constants `M → R`. -/
def twConstC : M →+* (twGalData t M W u2 r ht).R where
  toFun m := CoordRing.mk (constι₃ M m)
    (adjoin_constSet₃_le_twL t M W u2 r ht (IntermediateField.subset_adjoin _ _ ⟨m, rfl⟩))
    (isIntegral_constι₃ t M m)
  map_one' := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_one])
  map_mul' a b := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_mul])
  map_zero' := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_zero])
  map_add' a b := CoordRing.ext (by simp only [CoordRing.algebraMap_mk, map_add])

/-- The element `xTw ∈ R`. -/
def twXR : (twGalData t M W u2 r ht).R :=
  CoordRing.mk (xTw t M u2 r)
    (adjoin_constSet₃_le_twL t M W u2 r ht (xTw_mem_adjoin_constSet₃ t M u2 r))
    (isIntegral_xTw t M u2 r)

/-- The element `yTw ∈ R`. -/
def twYR : (twGalData t M W u2 r ht).R :=
  CoordRing.mk (yTw t M W u2 r) (yTw_mem_twL t M W u2 r ht) (isIntegral_yTw t M W u2 r)

lemma algebraMap_comp_twConstC :
    (algebraMap (twGalData t M W u2 r ht).R Ω).comp
      (eval₂RingHom (twConstC t M W u2 r ht) (twXR t M W u2 r ht)) =
      eval₂RingHom (constι₃ M) (xTw t M u2 r) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_C, eval₂_C]
    rfl
  · rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_X, eval₂_X]
    rfl

lemma eval₂_polynomial_twYR :
    W.toAffine.polynomial.eval₂ (eval₂RingHom (twConstC t M W u2 r ht) (twXR t M W u2 r ht))
      (twYR t M W u2 r ht) = 0 := by
  apply CoordRing.algebraMap_injective
  rw [hom_eval₂, map_zero, algebraMap_comp_twConstC]
  exact eval₂_polynomial_yTw t M W u2 r

/-- **The map `ψ : M[W] → R`**, `m ↦ m`, `x ↦ xTw`, `y ↦ yTw`. -/
def twPsi : W.toAffine.CoordinateRing →+* (twGalData t M W u2 r ht).R :=
  AdjoinRoot.lift _ _ (eval₂_polynomial_twYR t M W u2 r ht)

/-- `(R ⊆ Ω) ∘ ψ = ρ`. -/
theorem algebraMap_comp_twPsi :
    (algebraMap (twGalData t M W u2 r ht).R Ω).comp (twPsi t M W u2 r ht) = twRho t M W u2 r := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, twPsi, AdjoinRoot.lift_comp_of, algebraMap_comp_twConstC, twRho,
      AdjoinRoot.lift_comp_of]
  · change algebraMap (twGalData t M W u2 r ht).R Ω (AdjoinRoot.lift _ _ _ (AdjoinRoot.root _)) =
      twRho t M W u2 r (AdjoinRoot.root _)
    rw [AdjoinRoot.lift_root, twRho_root]
    rfl

lemma algebraMap_twPsi (a : W.toAffine.CoordinateRing) :
    algebraMap (twGalData t M W u2 r ht).R Ω (twPsi t M W u2 r ht a) = twRho t M W u2 r a :=
  RingHom.congr_fun (algebraMap_comp_twPsi t M W u2 r ht) a

variable {u2} (hu2 : u2 ≠ 0)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
include hu2 in
/-- `t = ρ(u2 x + r)`. -/
lemma twRho_of_t : twRho t M W u2 r (AdjoinRoot.of W.toAffine.polynomial (C u2 * X + C r)) = t := by
  rw [twRho_of, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
  exact constι₃_mul_xTw t M hu2 r

omit [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
include hu2 in
/-- `k[t] ⊆ ρ(M[W])`. -/
lemma algebraMap_A₀_mem_range_twRho (a : A₀ k t) :
    algebraMap (A₀ k t) Ω a ∈ (twRho t M W u2 r).range := by
  obtain ⟨a, ha⟩ := a
  change a ∈ (twRho t M W u2 r).range
  induction ha using Algebra.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact ⟨_, twRho_of_t t M W r hu2⟩
  | algebraMap c =>
    exact ⟨AdjoinRoot.of _ (C (algebraMap k M c)), by rw [twRho_of, eval₂_C]; rfl⟩
  | add w v _ _ hw hv => exact add_mem hw hv
  | mul w v _ _ hw hv => exact mul_mem hw hv

include hu2 in
/-- **Every element of `L` is a quotient of elements of `ρ(M[W])`.** -/
theorem mem_quotSubfieldTw_of_mem_L {z : Ω} (hz : z ∈ (twGalData t M W u2 r ht).L) :
    z ∈ quotSubfieldTw (twRho t M W u2 r) := by
  rw [twGalData_L, ← IntermediateField.adjoin_union] at hz
  refine mem_quotSubfieldTw_of_mem_adjoin t (twRho t M W u2 r) _ (fun c => ?_) ?_ ?_ hz
  · refine ⟨1, AdjoinRoot.of _ (C (algebraMap k M c)), ?_, ?_⟩
    · rw [map_one]
      exact one_ne_zero
    · rw [map_one, one_mul, twRho_of, eval₂_C]
      rfl
  · have h := map_mem_quotSubfieldTw (twRho t M W u2 r)
      (AdjoinRoot.of W.toAffine.polynomial (C u2 * X + C r))
    rw [twRho_of_t t M W r hu2] at h
    exact h
  · rintro _ (⟨m, rfl⟩ | hw)
    · have h : twRho t M W u2 r (AdjoinRoot.of _ (C m)) = ((m : ConstField₂ k Ω) : Ω) := by
        rw [twRho_of, eval₂_C]
        rfl
      change ((m : ConstField₂ k Ω) : Ω) ∈ quotSubfieldTw (twRho t M W u2 r)
      rw [← h]
      exact map_mem_quotSubfieldTw (twRho t M W u2 r) _
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, ← twRho_root t M W u2 r]
      exact map_mem_quotSubfieldTw (twRho t M W u2 r) _

variable [W.IsElliptic]

include hu2 in
/-- **`ψ` is surjective**: `M[W]` is integrally closed (elliptic-curves). -/
theorem twPsi_surjective : Function.Surjective (twPsi t M W u2 r ht) := by
  intro x
  obtain ⟨d, b, hd, hdb⟩ :=
    mem_quotSubfieldTw_of_mem_L t M W r ht hu2 (CoordRing.algebraMap_mem x)
  obtain ⟨y, hy⟩ := mem_range_of_isIntegral₃ (twRho t M W u2 r)
    (twRho_injective t M W r ht hu2) (algebraMap_A₀_mem_range_twRho t M W r hu2)
    (CoordRing.isIntegral_algebraMap x) hd hdb
  exact ⟨y, CoordRing.ext ((algebraMap_twPsi t M W u2 r ht y).trans hy)⟩

omit [W.IsElliptic] in
include hu2 in
theorem twPsi_injective : Function.Injective (twPsi t M W u2 r ht) := fun a b h =>
  twRho_injective t M W r ht hu2 (by
    rw [← algebraMap_twPsi, ← algebraMap_twPsi, h])

omit [W.IsElliptic] in
lemma twPsi_algebraMap (c : k) :
    twPsi t M W u2 r ht (algebraMap k W.toAffine.CoordinateRing c) =
      algebraMap k (twGalData t M W u2 r ht).R c := by
  apply CoordRing.ext
  rw [← IsScalarTower.algebraMap_apply k (twGalData t M W u2 r ht).R Ω, algebraMap_twPsi]
  have h : algebraMap k W.toAffine.CoordinateRing c = AdjoinRoot.of _ (C (algebraMap k M c)) := by
    rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply]
  rw [h, twRho_of, eval₂_C]
  rfl

/-- **`M[W] ≃ₐ[k] R`**: the coordinate ring of the twisted curve `W` is the ring `R` of
`twGalData`, compatible with the embeddings into `Ω` (`algebraMap_twREquiv`). -/
def twREquiv : W.toAffine.CoordinateRing ≃ₐ[k] (twGalData t M W u2 r ht).R :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _
    ⟨twPsi_injective t M W r ht hu2, twPsi_surjective t M W r ht hu2⟩)
    (twPsi_algebraMap t M W r ht)

lemma algebraMap_twREquiv (a : W.toAffine.CoordinateRing) :
    algebraMap (twGalData t M W u2 r ht).R Ω (twREquiv t M W r ht hu2 a) = twRho t M W u2 r a :=
  algebraMap_twPsi t M W u2 r ht a

/-- Constants: `m ↦ m`. -/
lemma algebraMap_twREquiv_C (m : M) :
    algebraMap (twGalData t M W u2 r ht).R Ω
      (twREquiv t M W r ht hu2 (AdjoinRoot.of W.toAffine.polynomial (C m))) =
      ((m : ConstField₂ k Ω) : Ω) := by
  rw [algebraMap_twREquiv, twRho_of, eval₂_C]
  rfl

end TwData

section TwIndex

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero k] (t : Ω)
  [IsGalois (K₀ k t) Ω] (M : IntermediateField k (ConstField₂ k Ω)) [FiniteDimensional k M]
  [IsGalois k M] (W : WeierstrassCurve M) (u2 r : M)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
/-- `ψ₂(xTw, yTw)² = Ψ₂Sq(xTw)`. -/
lemma sq_twψ : (2 * yTw t M W u2 r + twC1 t M W u2 r) ^ 2 =
    W.Ψ₂Sq.eval₂ (constι₃ M) (xTw t M u2 r) :=
  sq_psi₂_eval_tw (constι₃ M) W _ _ (yTw_eq t M W u2 r)

variable (ht : Transcendental k t) {u2} (hu2 : u2 ≠ 0)

omit [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
include ht hu2 in
/-- `ψ₂(xTw, yTw) ≠ 0`: `Ψ₂Sq ≠ 0` and `xTw` is transcendental. -/
lemma twψ_ne_zero : 2 * yTw t M W u2 r + twC1 t M W u2 r ≠ 0 := by
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap k M).injective
  have h4 : (4 : M) ≠ 0 := by norm_num
  intro h0
  have h := sq_twψ t M W u2 r
  rw [h0, zero_pow two_ne_zero] at h
  exact W.Ψ₂Sq_ne_zero h4 (eq_zero_of_eval₂_xTw t M ht hu2 r _ h.symm)

omit [IsGalois (K₀ k t) Ω] [FiniteDimensional k M] [IsGalois k M] in
include ht hu2 in
/-- The two roots `yTw` and `−yTw − a₁ xTw − a₃` are distinct. -/
lemma neg_sub_twC1_ne : -yTw t M W u2 r - twC1 t M W u2 r ≠ yTw t M W u2 r := fun h =>
  twψ_ne_zero t M W r ht hu2 (by linear_combination -h)

omit [FiniteDimensional k M] [IsGalois k M] in
include ht hu2 in
/-- **`yTw ∉ k(t)(M)`**: some element of `Gal(Ω / k(t)(M))` moves `yTw` (otherwise
`ψ₂(xTw, yTw) ∈ M[xTw]` and `Ψ₂Sq` of degree `3` would be a square). -/
theorem exists_constFixer₃_ne_yTw :
    ∃ σ ∈ constFixer₃ t M, σ (yTw t M W u2 r) ≠ yTw t M W u2 r := by
  by_contra hcon
  push Not at hcon
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap k M).injective
  have h4 : (4 : M) ≠ 0 := by norm_num
  have hy : yTw t M W u2 r ∈ IntermediateField.adjoin (K₀ k t) (constSet₃ M) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup
      (IntermediateField.adjoin (K₀ k t) (constSet₃ M)), fixingSubgroup_adjoin_constSet₃]
    exact (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hcon σ hσ
  have hψmem : 2 * yTw t M W u2 r + twC1 t M W u2 r ∈
      IntermediateField.adjoin (K₀ k t) (constSet₃ M) := by
    rw [two_mul]
    exact add_mem (add_mem hy hy) (add_mem (mul_mem
      (IntermediateField.subset_adjoin _ _ ⟨W.a₁, rfl⟩) (xTw_mem_adjoin_constSet₃ t M u2 r))
      (IntermediateField.subset_adjoin _ _ ⟨W.a₃, rfl⟩))
  have hct : (C u2 * X + C r).eval₂ (constι₃ M) (xTw t M u2 r) = t := by
    rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
    exact constι₃_mul_xTw t M hu2 r
  have hq := mem_quotSubfieldTw_of_mem_adjoin t (eval₂RingHom (constι₃ M) (xTw t M u2 r))
    (constSet₃ M) (fun c => ⟨1, C (algebraMap k M c), by rw [map_one]; exact one_ne_zero,
      by rw [map_one, one_mul, coe_eval₂RingHom, eval₂_C]; rfl⟩)
    ⟨1, C u2 * X + C r, by rw [map_one]; exact one_ne_zero,
      by rw [map_one, one_mul, coe_eval₂RingHom, hct]⟩
    (by
      rintro _ ⟨m, rfl⟩
      exact ⟨1, C m, by rw [map_one]; exact one_ne_zero,
        by rw [map_one, one_mul, coe_eval₂RingHom, eval₂_C]; rfl⟩) hψmem
  obtain ⟨d, b, hd, hdb⟩ := hq
  have hinj : Function.Injective (eval₂RingHom (constι₃ M) (xTw t M u2 r)) :=
    (injective_iff_map_eq_zero _).2 fun p hp => eq_zero_of_eval₂_xTw t M ht hu2 r p hp
  have hA : ∀ a : A₀ k t,
      algebraMap (A₀ k t) Ω a ∈ (eval₂RingHom (constι₃ M) (xTw t M u2 r)).range := by
    rintro ⟨a, ha⟩
    change a ∈ (eval₂RingHom (constι₃ M) (xTw t M u2 r)).range
    induction ha using Algebra.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact ⟨C u2 * X + C r, by rw [coe_eval₂RingHom, hct]⟩
    | algebraMap c => exact ⟨C (algebraMap k M c), by rw [coe_eval₂RingHom, eval₂_C]; rfl⟩
    | add w v _ _ hw hv => exact add_mem hw hv
    | mul w v _ _ hw hv => exact mul_mem hw hv
  obtain ⟨q, hq⟩ := mem_range_of_isIntegral₃ (eval₂RingHom (constι₃ M) (xTw t M u2 r)) hinj hA
    (isIntegral_twψ t M W u2 r) hd hdb
  have hsq : eval₂RingHom (constι₃ M) (xTw t M u2 r) (q ^ 2) =
      eval₂RingHom (constι₃ M) (xTw t M u2 r) W.Ψ₂Sq := by
    rw [map_pow, hq, coe_eval₂RingHom]
    exact sq_twψ t M W u2 r
  have hdeg := congrArg natDegree (hinj hsq)
  rw [natDegree_pow, W.natDegree_Ψ₂Sq h4] at hdeg
  omega

include ht hu2 in
/-- **`[Gal(Ω / k(t)(M)) : H_L] = 2`**: `L / k(t)(M)` is quadratic. -/
theorem relIndex_twGalData_HL :
    (twGalData t M W u2 r ht).HL.relIndex (constFixer₃ t M) = 2 := by
  obtain ⟨σ0, hσ0, hmove⟩ := exists_constFixer₃_ne_yTw t M W r ht hu2
  have h0 : σ0 (yTw t M W u2 r) = -yTw t M W u2 r - twC1 t M W u2 r :=
    (yTw_or t M W u2 r hσ0).resolve_left hmove
  have hne := neg_sub_twC1_ne t M W r ht hu2
  have key : ∀ g : constFixer₃ t M, (g : Ω ≃ₐ[K₀ k t] Ω) ∈ (twGalData t M W u2 r ht).HL ↔
      (g : Ω ≃ₐ[K₀ k t] Ω) (yTw t M W u2 r) = yTw t M W u2 r := fun g =>
    ⟨fun h => (mem_fixingSubgroup_adjoin_singleton_tw t _ _).1 h.2,
      fun h => ⟨g.2, (mem_fixingSubgroup_adjoin_singleton_tw t _ _).2 h⟩⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨σ0, hσ0⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, key, key, Subgroup.coe_mul,
    AlgEquiv.mul_apply, Subgroup.coe_mk, h0, map_sub, map_neg, fix_twC1 t M W u2 r b.2]
  rcases yTw_or t M W u2 r b.2 with h1 | h1
  · rw [h1]
    exact Or.inr ⟨rfl, hne⟩
  · rw [h1]
    exact Or.inl ⟨by ring, hne⟩

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] [FiniteDimensional k M]
  [IsGalois k M] in
/-- If the restriction to the constants is surjective, `[Gal(Ω / k(t)) : Gal(Ω / k(t)(M))] =
[M : k]`. -/
lemma index_constFixer₃ [IsAlgClosed Ω] [CharZero k]
    (hs : Function.Surjective (galResConst (k := k) t)) :
    (constFixer₃ t M).index = Module.finrank k M := by
  rw [constFixer₃, Subgroup.index_comap_of_surjective _ hs,
    IntermediateField.finrank_eq_fixingSubgroup_index]

include ht hu2 in
/-- **`[Gal(Ω / k(t)) : H_L] = 2 · [M : k]`**, given surjectivity onto `Gal(k̄ / k)`. -/
theorem index_twGalData_HL (hs : Function.Surjective (galResConst (k := k) t)) :
    (twGalData t M W u2 r ht).HL.index = 2 * Module.finrank k M := by
  have hle : (twGalData t M W u2 r ht).HL ≤ constFixer₃ t M := inf_le_left
  rw [← Subgroup.relIndex_mul_index hle, relIndex_twGalData_HL t M W r ht hu2,
    index_constFixer₃ t M hs]

end TwIndex

section TwFix

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

lemma fix_algebraMap_tw (σ : Ω ≃ₐ[K₀ k t] Ω) (a : k) : σ (algebraMap k Ω a) = algebraMap k Ω a :=
  σ.commutes ⟨algebraMap k Ω a, (K₀ k t).algebraMap_mem a⟩

lemma mem_constFixer₃_of_galResConst_eq_one (M : IntermediateField k (ConstField₂ k Ω))
    {σ : Ω ≃ₐ[K₀ k t] Ω} (h1 : galResConst t σ = 1) : σ ∈ constFixer₃ t M := by
  change galResConst t σ ∈ M.fixingSubgroup
  rw [h1]
  exact one_mem _

end TwFix

section TwCompare

/-! ### Comparison with a Weierstrass curve `E₀` over `k` with `x`-coordinate `t` -/

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero k] (t : Ω)
  (M : IntermediateField k (ConstField₂ k Ω)) (W : WeierstrassCurve M) {u2 : M} (r : M)
  (ht : Transcendental k t) (hu2 : u2 ≠ 0) (E₀ : WeierstrassCurve k) (y' : Ω)
  (hy' : y' ^ 2 + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃) * y' -
    (t ^ 3 + algebraMap k Ω E₀.a₂ * t ^ 2 + algebraMap k Ω E₀.a₄ * t + algebraMap k Ω E₀.a₆) = 0)
  (hΨ : (E₀.baseChange M).Ψ₂Sq.comp (C u2 * X + C r) = C (u2 ^ 3) * W.Ψ₂Sq)

omit [CharZero k] in
include hu2 hy' hΨ in
/-- **`ψ₂'² = u2³ · ψ₂²`** for `ψ₂' = 2 y' + a₁' t + a₃'`, `ψ₂ = 2 yTw + a₁ xTw + a₃` (from
`Ψ₂Sq' (u2 x + r) = u2³ Ψ₂Sq (x)` and `t = u2 xTw + r`). -/
lemma sq_psi'_eq_tw : (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) ^ 2 =
    constι₃ M u2 ^ 3 * (2 * yTw t M W u2 r + twC1 t M W u2 r) ^ 2 := by
  rw [sq_psi₂_eval_tw (algebraMap k Ω) E₀ t y' hy', sq_twψ]
  have h : ((E₀.baseChange M).Ψ₂Sq.comp (C u2 * X + C r)).eval₂ (constι₃ M) (xTw t M u2 r) =
      (C (u2 ^ 3) * W.Ψ₂Sq).eval₂ (constι₃ M) (xTw t M u2 r) := by
    rw [hΨ]
  have hct : (C u2 * X + C r).eval₂ (constι₃ M) (xTw t M u2 r) = t := by
    rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
    exact constι₃_mul_xTw t M hu2 r
  have hb : (E₀.baseChange M).Ψ₂Sq = E₀.Ψ₂Sq.map (algebraMap k M) :=
    WeierstrassCurve.map_Ψ₂Sq E₀ (algebraMap k M)
  rw [eval₂_comp, eval₂_mul, eval₂_C, map_pow, hct, hb, eval₂_map,
    constι₃_comp_algebraMap] at h
  exact h

include ht hu2 hy' hΨ in
/-- **The constant `c = ψ₂' / ψ₂` with `c² = u2³`** is algebraic over `k`, hence fixed by every
`σ` acting trivially on the constants; so such `σ` fixes `y'` iff it fixes `yTw`. -/
theorem fix_iff_fix_yTw {σ : Ω ≃ₐ[K₀ k t] Ω} (h1 : galResConst t σ = 1) :
    σ y' = y' ↔ σ (yTw t M W u2 r) = yTw t M W u2 r := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hσM := mem_constFixer₃_of_galResConst_eq_one t M h1
  have hψ0 := twψ_ne_zero t M W r ht hu2
  have hsq := sq_psi'_eq_tw t M W r hu2 E₀ y' hy' hΨ
  have hψ'0 : 2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, eq_comm, mul_eq_zero] at hsq
    rcases hsq with h | h
    · exact hu2 ((map_eq_zero (constι₃ M)).1 (pow_eq_zero_iff three_ne_zero |>.1 h))
    · exact hψ0 (pow_eq_zero_iff two_ne_zero |>.1 h)
  have hc2 : ((2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
      (2 * yTw t M W u2 r + twC1 t M W u2 r)) ^ 2 = constι₃ M (u2 ^ 3) := by
    rw [div_pow, hsq, mul_div_assoc, div_self (pow_ne_zero 2 hψ0), mul_one, map_pow]
  have hcK : (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
      (2 * yTw t M W u2 r + twC1 t M W u2 r) ∈ ConstField₂ k Ω := by
    refine mem_algebraicClosure_iff'.2 (IsIntegral.of_pow two_pos ?_)
    rw [hc2]
    exact isIntegral_constι₃_k M _
  have hc : σ ((2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
      (2 * yTw t M W u2 r + twC1 t M W u2 r)) =
      (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
        (2 * yTw t M W u2 r + twC1 t M W u2 r) :=
    congrArg (fun g : ConstField₂ k Ω ≃ₐ[k] ConstField₂ k Ω =>
      ((g ⟨_, hcK⟩ : ConstField₂ k Ω) : Ω)) h1
  have hc0 : (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
      (2 * yTw t M W u2 r + twC1 t M W u2 r) ≠ 0 := div_ne_zero hψ'0 hψ0
  have hψ' : 2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃) =
      (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
        (2 * yTw t M W u2 r + twC1 t M W u2 r) * (2 * yTw t M W u2 r + twC1 t M W u2 r) := by
    rw [div_mul_cancel₀ _ hψ0]
  have hσψ' : σ (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) =
      2 * σ y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃) := by
    rw [map_add, map_mul, map_ofNat, map_add, map_mul, fix_algebraMap_tw, fix_algebraMap_tw,
      fix_t_tw]
  have hσψ : σ (2 * yTw t M W u2 r + twC1 t M W u2 r) =
      2 * σ (yTw t M W u2 r) + twC1 t M W u2 r := by
    rw [map_add, map_mul, map_ofNat, fix_twC1 t M W u2 r hσM]
  have hD : 2 * (σ y' - y') = (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
      (2 * yTw t M W u2 r + twC1 t M W u2 r) *
        (2 * (σ (yTw t M W u2 r) - yTw t M W u2 r)) := by
    have e := congrArg σ hψ'
    rw [map_mul, hc, hσψ', hσψ] at e
    linear_combination e - hψ'
  constructor
  · intro h
    have h0 : (2 * y' + (algebraMap k Ω E₀.a₁ * t + algebraMap k Ω E₀.a₃)) /
        (2 * yTw t M W u2 r + twC1 t M W u2 r) *
          (2 * (σ (yTw t M W u2 r) - yTw t M W u2 r)) = 0 := by
      rw [← hD, h, sub_self, mul_zero]
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact absurd h' hc0
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' two_ne_zero
      · exact sub_eq_zero.1 h''
  · intro h
    have h0 : 2 * (σ y' - y') = 0 := by
      rw [hD, h, sub_self, mul_zero, mul_zero]
    rcases mul_eq_zero.1 h0 with h'' | h''
    · exact absurd h'' two_ne_zero
    · exact sub_eq_zero.1 h''

omit [IsAlgClosed Ω] in
/-- **The twist parameters**: for `E` over `M` with `j(E) = j(E₀) ∉ {0, 1728}` there are
`u2 ≠ 0`, `r` in `M` with `Ψ₂Sq_{E₀} (u2 X + r) = u2³ Ψ₂Sq_E (X)` (`exists_Ψ₂Sq_comp_xrat₃`). -/
theorem exists_tw_params [E₀.IsElliptic] (E : WeierstrassCurve M) [E.IsElliptic]
    (hj : E.j = (E₀.baseChange M).j) (h0 : E.j ≠ 0) (h1728 : E.j ≠ 1728) :
    ∃ u2 r : M, u2 ≠ 0 ∧
      (E₀.baseChange M).Ψ₂Sq.comp (C u2 * X + C r) = C (u2 ^ 3) * E.Ψ₂Sq := by
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap k M).injective
  haveI : (E₀.baseChange M).IsElliptic := inferInstanceAs ((E₀.map (algebraMap k M)).IsElliptic)
  exact exists_Ψ₂Sq_comp_xrat₃ E (E₀.baseChange M) hj h0 h1728

omit [IsAlgClosed Ω] [CharZero k] in
/-- `E₀_M` is the trivial twist of itself (`u2 = 1`, `r = 0`). -/
lemma Ψ₂Sq_comp_one_zero_tw :
    (E₀.baseChange M).Ψ₂Sq.comp (C 1 * X + C 0) = C (1 ^ 3) * (E₀.baseChange M).Ψ₂Sq := by
  rw [map_one, one_mul, map_zero, add_zero, comp_X, one_pow, map_one, one_mul]

end TwCompare

section TwIncl

/-! ### Embeddings `H₁ ⧸ ⟨⟨S⟩⟩ → H₂ ⧸ ⟨⟨S⟩⟩` for Galois data with the same inertia -/

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

lemma ambientKernel_eq_of_S_eq_tw (D₁ D₂ : GaloisData k t) (hS : D₁.S = D₂.S) :
    GaloisPi1.ambientKernel D₁.H D₁.S = GaloisPi1.ambientKernel D₂.H D₂.S := by
  unfold GaloisPi1.ambientKernel
  rw [conjSet_S_eq D₁ le_rfl, conjSet_S_eq D₂ le_rfl, hS]

variable [IsGalois (K₀ k t) Ω] (D₁ D₂ : GaloisData k t) (hH : D₁.H ≤ D₂.H) (hS : D₁.S = D₂.S)

/-- `Π_{C₁} = H₁ ⧸ ⟨⟨S⟩⟩ → Π_{C₂} = H₂ ⧸ ⟨⟨S⟩⟩` for `H₁ ≤ H₂` and equal inertia. -/
def twInclC : GaloisPi1.pi1 D₁.H D₁.S D₁.isClosed_H →ₜ* GaloisPi1.pi1 D₂.H D₂.S D₂.isClosed_H where
  toMonoidHom := GaloisPi1.pi1Map D₁.isClosed_H D₂.isClosed_H hH hS.subset
  continuous_toFun := GaloisPi1.continuous_pi1Map _ _ _ _

/-- `Π_{X₁} = H_{L,1} ⧸ ⟨⟨S⟩⟩ → Π_{C₂} = H₂ ⧸ ⟨⟨S⟩⟩` for `H₁ ≤ H₂` and equal inertia. -/
def twInclX :
    GaloisPi1.pi1 D₁.HL D₁.S D₁.isClosed_HL →ₜ* GaloisPi1.pi1 D₂.H D₂.S D₂.isClosed_H where
  toMonoidHom := GaloisPi1.pi1Map D₁.isClosed_HL D₂.isClosed_H (D₁.le.trans hH) hS.subset
  continuous_toFun := GaloisPi1.continuous_pi1Map _ _ _ _

lemma twInclC_orbiIncl (x : GaloisPi1.pi1 D₁.HL D₁.S D₁.isClosed_HL) :
    twInclC D₁ D₂ hH hS (orbiIncl D₁ x) = twInclX D₁ D₂ hH hS x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem isOpenEmbedding_twInclC : IsOpenEmbedding (twInclC D₁ D₂ hH hS) :=
  GaloisPi1.isOpenEmbedding_pi1Map' _ _ _ hS.subset hS.symm.subset D₁.isOpen_H
    fun _ hh _ hs => hS ▸ conj_mem_S D₂ hh (hS ▸ hs)

theorem isOpenEmbedding_twInclX : IsOpenEmbedding (twInclX D₁ D₂ hH hS) :=
  GaloisPi1.isOpenEmbedding_pi1Map' _ _ _ hS.subset hS.symm.subset D₁.isOpen_HL
    fun _ hh _ hs => hS ▸ conj_mem_S D₂ hh (hS ▸ hs)

/-- The image of `H ⧸ ⟨⟨S⟩⟩` in `H₂ ⧸ ⟨⟨S₂⟩⟩` (`H ≤ H₂`, `S ⊆ S₂`). -/
lemma range_pi1Map_tw (H : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (S : Set (Ω ≃ₐ[K₀ k t] Ω))
    (hHc : IsClosed (H : Set (Ω ≃ₐ[K₀ k t] Ω))) (hle : H ≤ D₂.H) (hS' : S ⊆ D₂.S) :
    (GaloisPi1.pi1Map hHc D₂.isClosed_H hle hS').range =
      (H.subgroupOf D₂.H).map (QuotientGroup.mk' (GaloisPi1.kernel D₂.H D₂.S)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨Subgroup.inclusion hle x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk (⟨x, Subgroup.mem_subgroupOf.1 hx⟩ : H), rfl⟩

/-- The index of the image of `H ⧸ ⟨⟨S⟩⟩` is `[H₂ : H]`, if `H` contains the closed normal
subgroup generated by `S₂`. -/
lemma index_range_pi1Map_tw (H : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (S : Set (Ω ≃ₐ[K₀ k t] Ω))
    (hHc : IsClosed (H : Set (Ω ≃ₐ[K₀ k t] Ω))) (hle : H ≤ D₂.H) (hS' : S ⊆ D₂.S)
    (hk : GaloisPi1.ambientKernel D₂.H D₂.S ≤ H) :
    (GaloisPi1.pi1Map hHc D₂.isClosed_H hle hS').range.index = H.relIndex D₂.H := by
  rw [range_pi1Map_tw D₂ H S hHc hle hS', Subgroup.index_map_eq _
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      intro x hx
      rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_subgroupOf.2 (hk hx))]
  rfl

omit [IsGalois (K₀ k t) Ω] in
include hS in
lemma ambientKernel_le_HL_tw : GaloisPi1.ambientKernel D₂.H D₂.S ≤ D₁.HL := by
  rw [← ambientKernel_eq_of_S_eq_tw D₁ D₂ hS]
  exact ambientKernel_le_HL D₁

/-- **`[Π_{C₂} : Π_{X₁}] = [H₂ : H_{L,1}]`.** -/
theorem index_range_twInclX :
    (twInclX D₁ D₂ hH hS).toMonoidHom.range.index = D₁.HL.relIndex D₂.H :=
  index_range_pi1Map_tw D₂ D₁.HL D₁.S D₁.isClosed_HL _ hS.subset
    (ambientKernel_le_HL_tw D₁ D₂ hS)

/-- **`[Π_{C₂} : Π_{C₁}] = [H₂ : H₁]`.** -/
theorem index_range_twInclC :
    (twInclC D₁ D₂ hH hS).toMonoidHom.range.index = D₁.H.relIndex D₂.H :=
  index_range_pi1Map_tw D₂ D₁.H D₁.S D₁.isClosed_H _ hS.subset
    ((ambientKernel_le_HL_tw D₁ D₂ hS).trans D₁.le)

/-- **`Π_{C₁} ⊴ Π_{C₂}`** if `H₁ ⊴ H₂`. -/
theorem range_twInclC_normal (hn : (D₁.H.subgroupOf D₂.H).Normal) :
    (twInclC D₁ D₂ hH hS).toMonoidHom.range.Normal := by
  have h := range_pi1Map_tw D₂ D₁.H D₁.S D₁.isClosed_H hH hS.subset
  have hn' := Subgroup.Normal.map hn (QuotientGroup.mk' (GaloisPi1.kernel D₂.H D₂.S))
    (QuotientGroup.mk'_surjective _)
  rw [← h] at hn'
  exact hn'

/-- **Compatibility with the projections to `Gal(k̄ / k)`.** -/
theorem piConstC_comp_twInclX :
    (piConstC D₂).comp (twInclX D₁ D₂ hH hS).toMonoidHom = piConstX D₁ := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem piConstC_comp_twInclC :
    (piConstC D₂).comp (twInclC D₁ D₂ hH hS).toMonoidHom = piConstC D₁ := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- **Same `H`, same inertia ⟹ same `Π_C`**: `H₁ ⧸ ⟨⟨S₁⟩⟩ ≃ₜ* H₂ ⧸ ⟨⟨S₂⟩⟩` for `H₁ = H₂`,
`S₁ = S₂`. -/
def twCEquiv (hHe : D₁.H = D₂.H) :
    GaloisPi1.pi1 D₁.H D₁.S D₁.isClosed_H ≃ₜ* GaloisPi1.pi1 D₂.H D₂.S D₂.isClosed_H where
  toMulEquiv := MonoidHom.toMulEquiv
    (GaloisPi1.pi1Map D₁.isClosed_H D₂.isClosed_H hHe.le hS.subset)
    (GaloisPi1.pi1Map D₂.isClosed_H D₁.isClosed_H hHe.ge hS.symm.subset)
    (MonoidHom.ext fun x => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      rfl)
    (MonoidHom.ext fun x => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      rfl)
  continuous_toFun := GaloisPi1.continuous_pi1Map _ _ _ _
  continuous_invFun := GaloisPi1.continuous_pi1Map _ _ _ _

end TwIncl

section HemiTw

variable {K : Type u} [Field K] [CharZero K] (E' : WeierstrassCurve K) [E'.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E')))) [FiniteDimensional K M]
  [IsGalois K M] (E : WeierstrassCurve M) (u2 r : M)

/-- **The Galois data of the twist `E` of `E'_M`** inside `Ω = K(Ē')^alg` with `t = x'`:
`H = Gal(Ω / K(x')(M))` (the orbicurve `C_M`), `H_L = Gal(Ω / K(x')(M)(yTw))` (`X_M = E ∖ {O}`,
`x_E = u2⁻¹ (x' − r)`). -/
abbrev hemiTwData : GaloisData K (coordT (xN E')) :=
  twGalData (coordT (xN E')) M E u2 r (hemiData E').transcendental

/-- The `y`-coordinate `y' = ρ(Y)` of `hemiData E'`. -/
abbrev hemiY : FFClosure (curveE E') := hemiRho E' (AdjoinRoot.root E'.toAffine.polynomial)

omit [CharZero K] in
lemma hemiY_eq [CharZero K] : hemiY E' ^ 2 + (algebraMap K (FFClosure (curveE E')) E'.a₁ *
    coordT (xN E') + algebraMap K (FFClosure (curveE E')) E'.a₃) * hemiY E' -
    (coordT (xN E') ^ 3 + algebraMap K (FFClosure (curveE E')) E'.a₂ * coordT (xN E') ^ 2 +
      algebraMap K (FFClosure (curveE E')) E'.a₄ * coordT (xN E') +
      algebraMap K (FFClosure (curveE E')) E'.a₆) = 0 := by
  have h := hemiRho_root_eq E'
  rw [hemiRho_of, hemiRho_of] at h
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X] at h
  linear_combination h

/-- An element of `Gal(Ω / K(x'))` lies in `H_L = Gal(Ω / K(Ē'))` iff it fixes `y'`. -/
theorem mem_hemiHL_iff
    (σ : FFClosure (curveE E') ≃ₐ[K₀ K (coordT (xN E'))] FFClosure (curveE E')) :
    σ ∈ (hemiData E').HL ↔ σ (hemiY E') = hemiY E' := by
  constructor
  · intro h
    rw [← (hemiData E').fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff] at h
    exact h _ (CoordRing.algebraMap_mem (hemiREquiv E' (AdjoinRoot.root E'.toAffine.polynomial)))
  · intro h
    have he : σ.toRingEquiv.toRingHom.comp (hemiRho E') = hemiRho E' :=
      AdjoinRoot.ringHom_ext (RingHom.ext fun q => fix_hemiRho_of E' σ q) h
    rw [← (hemiData E').fixingSubgroup_L]
    refine CoordRing.mem_fixingSubgroup_of_forall _ fun x => ?_
    have hx := RingHom.congr_fun he ((hemiREquiv E').symm x)
    change σ (hemiRho E' _) = hemiRho E' _ at hx
    rwa [hemiRho_apply, AlgEquiv.apply_symm_apply] at hx

variable {u2} (hu2 : u2 ≠ 0)
  (hΨ : (E'.baseChange M).Ψ₂Sq.comp (C u2 * X + C r) = C (u2 ^ 3) * E.Ψ₂Sq)

omit [FiniteDimensional K M] [IsGalois K M] in
include hu2 hΨ in
/-- An element `σ` acting trivially on the constants fixes `y'` iff it fixes `yTw`
(`fix_iff_fix_yTw`). -/
theorem fix_hemiY_iff_fix_yTw
    {σ : FFClosure (curveE E') ≃ₐ[K₀ K (coordT (xN E'))] FFClosure (curveE E')}
    (h1 : galResConst (coordT (xN E')) σ = 1) :
    σ (hemiY E') = hemiY E' ↔
      σ (yTw (coordT (xN E')) M E u2 r) = yTw (coordT (xN E')) M E u2 r :=
  fix_iff_fix_yTw (coordT (xN E')) M E r (hemiData E').transcendental hu2 E' (hemiY E')
    (hemiY_eq E') hΨ h1

include hu2 hΨ in
/-- **Same inertia (T3)**: the inertia elements of the twist `E` (inside `C_M`) are those of the
hemi-elliptic orbicurve of `E'`: `S(hemiTwData) = S(hemiData E')`. -/
theorem hemiTwData_S : (hemiTwData E' M E u2 r).S = (hemiData E').S := by
  ext σ
  constructor
  · rintro ⟨hHL, W, hk, ht, hI⟩
    have h1 := galResConst_eq_one_of_mem_inertia W hk hI
    exact ⟨(mem_hemiHL_iff E' σ).2 ((fix_hemiY_iff_fix_yTw E' M E r hu2 hΨ h1).2
      ((mem_fixingSubgroup_adjoin_singleton_tw _ _ _).1 hHL.2)), W, hk, ht, hI⟩
  · rintro ⟨hHL, W, hk, ht, hI⟩
    have h1 := galResConst_eq_one_of_mem_inertia W hk hI
    exact ⟨⟨mem_constFixer₃_of_galResConst_eq_one _ M h1,
      (mem_fixingSubgroup_adjoin_singleton_tw _ _ _).2
        ((fix_hemiY_iff_fix_yTw E' M E r hu2 hΨ h1).1 ((mem_hemiHL_iff E' σ).1 hHL))⟩,
      W, hk, ht, hI⟩

include hu2 hΨ in
/-- **`Π_{C_M}` does not see the twist (T4)**: the orbicurve groups `H ⧸ ⟨⟨S⟩⟩` of the twist `E`
and of `E'_M` (`u2 = 1`, `r = 0`) are the same (same `H = Gal(Ω / K(x')(M))`, same inertia). -/
def hemiTwCEquiv : GaloisPi1.pi1 (hemiTwData E' M E u2 r).H (hemiTwData E' M E u2 r).S
    (hemiTwData E' M E u2 r).isClosed_H ≃ₜ*
    GaloisPi1.pi1 (hemiTwData E' M (E'.baseChange M) 1 0).H
      (hemiTwData E' M (E'.baseChange M) 1 0).S
      (hemiTwData E' M (E'.baseChange M) 1 0).isClosed_H :=
  twCEquiv _ _ ((hemiTwData_S E' M E r hu2 hΨ).trans
    (hemiTwData_S E' M (E'.baseChange M) 0 one_ne_zero (Ψ₂Sq_comp_one_zero_tw M E')).symm) rfl

include hu2 in
/-- **`Π_{X_M} ↪ Π_{C_M}`** for the twist: an open embedding with normal image of index `2`
(`L / K(x')(M)` is quadratic, `relIndex_twGalData_HL`). -/
theorem hemiTw_orbiIncl :
    IsOpenEmbedding (orbiIncl (hemiTwData E' M E u2 r)) ∧
      (orbiIncl (hemiTwData E' M E u2 r)).toMonoidHom.range.Normal ∧
      (orbiIncl (hemiTwData E' M E u2 r)).toMonoidHom.range.index = 2 :=
  ⟨isOpenEmbedding_orbiIncl _, range_orbiIncl_normal _,
    (index_range_orbiIncl _).trans (relIndex_twGalData_HL _ M E r _ hu2)⟩

end HemiTw

section HemiTwArith

-- The arithmetic part (as `CurvesJacobian.Cusp.HemiConstArith`) uses the default transparency.
set_option backward.isDefEq.respectTransparency true

variable {K : Type u} [Field K] [NumberField K] (E' : WeierstrassCurve K) [E'.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E')))) [FiniteDimensional K M]
  [IsGalois K M] (E : WeierstrassCurve M) [E.IsElliptic] (r : M) {u2 : M} (hu2 : u2 ≠ 0)

/-- **Geometric connectedness of `E' ∖ {O}`**, for `K` a number field: the restriction
`Gal(Ω / K(x')) → Gal(k̄ / K)` is surjective (`range_piConstX_hemi`). -/
theorem galResConst_surjective_hemi :
    Function.Surjective (galResConst (k := K) (coordT (xN E'))) := fun g => by
  have hg : g ∈ (piConstX (hemiData E')).range := by
    rw [range_piConstX_hemi]
    trivial
  obtain ⟨x, hx⟩ := hg
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨σ, hx⟩

omit [E.IsElliptic] in
include hu2 in
/-- **`[Gal(Ω / K(x')) : H_L] = 2 · [M : K]`** for the twist. -/
theorem index_hemiTwData_HL : (hemiTwData E' M E u2 r).HL.index = 2 * Module.finrank K M :=
  index_twGalData_HL _ M E r _ hu2 (galResConst_surjective_hemi E')

/-- **`Γ(E ∖ {O}) ≅ R`** for the twist: `Γ(E ∖ {O}) ≃ M[E] ≃ R` (`sectionsXEHyp₃`,
`twREquiv`). -/
def hemiTwRingEquiv : Γ((hypCurveX E).Xbar, (hypCurveX E).U) ≃+* (hemiTwData E' M E u2 r).R :=
  (sectionsXEHyp₃ E).toRingEquiv.trans
    (twREquiv (coordT (xN E')) M E r (hemiData E').transcendental hu2).toRingEquiv

/-- **Compatibility with `M`**: the `M`-structure of `Γ(E ∖ {O})` is `M ⊆ k̄ ⊆ Ω`. -/
theorem constCompat_hemiTw :
    ConstCompat₃ (hemiTwData E' M E u2 r) M (hypCurveX E) (hemiTwRingEquiv E' M E r hu2) :=
  constCompat_hypCurveX₃ _ M E _ fun m => algebraMap_twREquiv_C _ M E r _ hu2 m

variable (Ω'' : Type u) [Field Ω''] [Algebra M Ω''] [IsAlgClosed Ω''] [Algebra.IsAlgebraic M Ω'']
  [CharZero Ω'']

/-- **`Π_{E ∖ O} ≃ₜ* H_L ⧸ ⟨⟨S⟩⟩`** (cj's arithmetic `π₁` of `E ∖ {O}` over `M`; change of base
point). -/
def hemiTwPiXGal :
    (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).Pi ≃ₜ*
    GaloisPi1.pi1 (hemiTwData E' M E u2 r).HL (hemiTwData E' M E u2 r).S
      (hemiTwData E' M E u2 r).isClosed_HL :=
  piXGalG₃ (hemiTwData E' M E u2 r) M (hypCurveX E) (compl_XE_nonempty E)
    (hemiTwRingEquiv E' M E r hu2) Ω''

/-- **`G_M ≃ₜ* Gal(k̄ / M)`** (induced change of base point). -/
def hemiTwGkEquiv :
    (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).G ≃ₜ*
    (ConstField₂ K (FFClosure (curveE E')) ≃ₐ[M] ConstField₂ K (FFClosure (curveE E'))) :=
  gkEquivG₃ (hemiTwData E' M E u2 r) M (hypCurveX E) (compl_XE_nonempty E)
    (hemiTwRingEquiv E' M E r hu2) (constCompat_hemiTw E' M E r hu2) Ω''

/-- **`pr : Π_{E ∖ O} → G_M` is the restriction to the constants.** -/
theorem hemiTwGkEquiv_pr (γ : (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).Pi) :
    (hemiTwGkEquiv E' M E r hu2 Ω''
      ((arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).pr γ)).restrictScalars K =
      piConstX (hemiTwData E' M E u2 r) (hemiTwPiXGal E' M E r hu2 Ω'' γ) :=
  gkEquivG₃_pr (hemiTwData E' M E u2 r) M (hypCurveX E) (compl_XE_nonempty E)
    (hemiTwRingEquiv E' M E r hu2) (constCompat_hemiTw E' M E r hu2) Ω'' inf_le_left γ

variable (hΨ : (E'.baseChange M).Ψ₂Sq.comp (C u2 * X + C r) = C (u2 ^ 3) * E.Ψ₂Sq)

/-- **`Π_{E ∖ O} → Π_C = H ⧸ ⟨⟨S⟩⟩`** (Galois form; `C = C_K` the hemi-elliptic orbicurve of
`E'`): `hemiTwPiXGal`, then `twInclX` (same inertia, `hemiTwData_S`). -/
def hemiTwEmb :
    (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).Pi →ₜ*
    GaloisPi1.pi1 (hemiData E').H (hemiData E').S (hemiData E').isClosed_H :=
  (twInclX (hemiTwData E' M E u2 r) (hemiData E') le_top
    (hemiTwData_S E' M E r hu2 hΨ)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (hemiTwPiXGal E' M E r hu2 Ω''))

/-- **`Π_{E ∖ O} → Π_C = etalePi1 R A Ω`**: `hemiTwEmb`, then `equivPi1⁻¹`. -/
def hemiTwEmbC :
    (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).Pi →ₜ*
    etalePi1 (hemiData E').R (hemiData E').A (FFClosure (curveE E')) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (hemiData E').equivPi1.symm).comp
    (hemiTwEmb E' M E r hu2 Ω'' hΨ)

lemma range_hemiTwEmbC : (hemiTwEmbC E' M E r hu2 Ω'' hΨ).toMonoidHom.range =
    (twInclX (hemiTwData E' M E u2 r) (hemiData E') le_top
      (hemiTwData_S E' M E r hu2 hΨ)).toMonoidHom.range.map
        ((hemiData E').equivPi1.symm.toMulEquiv : _ →* _) := by
  ext y
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨_, ⟨hemiTwPiXGal E' M E r hu2 Ω'' γ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(hemiTwPiXGal E' M E r hu2 Ω'').symm x, ?_⟩
    change (hemiData E').equivPi1.symm ((twInclX (hemiTwData E' M E u2 r) (hemiData E') le_top
      (hemiTwData_S E' M E r hu2 hΨ)) (hemiTwPiXGal E' M E r hu2 Ω''
        ((hemiTwPiXGal E' M E r hu2 Ω'').symm x))) = _
    exact congrArg (fun z => (hemiData E').equivPi1.symm ((twInclX (hemiTwData E' M E u2 r)
      (hemiData E') le_top (hemiTwData_S E' M E r hu2 hΨ)) z))
        ((hemiTwPiXGal E' M E r hu2 Ω'').apply_symm_apply x)

/-- `piConstC ∘ hemiTwEmbC = (pr, restricted to Gal(k̄ / K))`. -/
lemma piConstC_hemiTwEmbC
    (γ : (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).Pi) :
    piConstC (hemiData E') ((hemiData E').equivPi1 (hemiTwEmbC E' M E r hu2 Ω'' hΨ γ)) =
      (hemiTwGkEquiv E' M E r hu2 Ω''
        ((arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).pr γ)).restrictScalars K := by
  have h1 : (hemiData E').equivPi1 (hemiTwEmbC E' M E r hu2 Ω'' hΨ γ) =
      twInclX (hemiTwData E' M E u2 r) (hemiData E') le_top (hemiTwData_S E' M E r hu2 hΨ)
        (hemiTwPiXGal E' M E r hu2 Ω'' γ) :=
    (hemiData E').equivPi1.apply_symm_apply _
  exact (congrArg (piConstC (hemiData E')) h1).trans
    ((DFunLike.congr_fun (piConstC_comp_twInclX (hemiTwData E' M E u2 r) (hemiData E') le_top
      (hemiTwData_S E' M E r hu2 hΨ)) (hemiTwPiXGal E' M E r hu2 Ω'' γ)).trans
        (hemiTwGkEquiv_pr E' M E r hu2 Ω'' γ).symm)

/-- `hemiTwEmbC` is an open embedding. -/
theorem isOpenEmbedding_hemiTwEmbC : IsOpenEmbedding (hemiTwEmbC E' M E r hu2 Ω'' hΨ) :=
  (hemiData E').equivPi1.symm.toHomeomorph.isOpenEmbedding.comp
    ((isOpenEmbedding_twInclX (hemiTwData E' M E u2 r) (hemiData E') le_top
      (hemiTwData_S E' M E r hu2 hΨ)).comp
      (hemiTwPiXGal E' M E r hu2 Ω'').toHomeomorph.isOpenEmbedding)

/-- `[Π_C : Π_{E ∖ O}] = 2 · [M : K]`. -/
theorem index_range_hemiTwEmbC :
    (hemiTwEmbC E' M E r hu2 Ω'' hΨ).toMonoidHom.range.index = 2 * Module.finrank K M :=
  (congrArg Subgroup.index (range_hemiTwEmbC E' M E r hu2 Ω'' hΨ)).trans
    ((Subgroup.index_map_equiv _ _).trans
      ((index_range_twInclX (hemiTwData E' M E u2 r) (hemiData E') le_top
        (hemiTwData_S E' M E r hu2 hΨ)).trans
        ((Subgroup.relIndex_top_right _).trans (index_hemiTwData_HL E' M E r hu2))))

/-- The image of `Π_{E ∖ O}` lies in the image of `Π_{C_M}`. -/
theorem range_hemiTwEmbC_le : (hemiTwEmbC E' M E r hu2 Ω'' hΨ).toMonoidHom.range ≤
    (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top
      (hemiTwData_S E' M E r hu2 hΨ)).toMonoidHom.range.map
        ((hemiData E').equivPi1.symm.toMulEquiv : _ →* _) := by
  rintro _ ⟨γ, rfl⟩
  exact ⟨twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top (hemiTwData_S E' M E r hu2 hΨ)
    (orbiIncl (hemiTwData E' M E u2 r) (hemiTwPiXGal E' M E r hu2 Ω'' γ)), ⟨_, rfl⟩,
    congrArg (fun z => (hemiData E').equivPi1.symm z)
      (twInclC_orbiIncl _ _ _ (hemiTwData_S E' M E r hu2 hΨ) _)⟩

set_option maxHeartbeats 400000 in
-- Unifying the four conjuncts with the component lemmas unfolds the (large) types of
-- `hemiTwEmbC` once more; this exceeds the default heartbeat budget.
/-- **`Π_{E ∖ O} ↪ Π_C` for a twist `E` of `E'_M` (T5)**, in the normalisation of
`arithmeticExt` for `E ∖ {O}` over `M`: `hemiTwEmbC` is an open embedding with image of index
`2 · [M : K]`, compatible with the projections to `Gal(k̄ / K)`, and its image lies in the
image of `Π_{C_M} = Gal(Ω / K(x')(M)) ⧸ ⟨⟨S⟩⟩`, which is open and normal in `Π_C` of index
`[M : K]` (`hemiTw_constExt`). -/
theorem hemiTw_arith_emb :
    IsOpenEmbedding (hemiTwEmbC E' M E r hu2 Ω'' hΨ) ∧
      (hemiTwEmbC E' M E r hu2 Ω'' hΨ).toMonoidHom.range.index = 2 * Module.finrank K M ∧
      (∀ γ : (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).Pi,
        piConstC (hemiData E') ((hemiData E').equivPi1 (hemiTwEmbC E' M E r hu2 Ω'' hΨ γ)) =
        (hemiTwGkEquiv E' M E r hu2 Ω''
          ((arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).pr γ)).restrictScalars K) ∧
      (hemiTwEmbC E' M E r hu2 Ω'' hΨ).toMonoidHom.range ≤
        (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top
          (hemiTwData_S E' M E r hu2 hΨ)).toMonoidHom.range.map
            ((hemiData E').equivPi1.symm.toMulEquiv : _ →* _) :=
  ⟨isOpenEmbedding_hemiTwEmbC E' M E r hu2 Ω'' hΨ, index_range_hemiTwEmbC E' M E r hu2 Ω'' hΨ,
    piConstC_hemiTwEmbC E' M E r hu2 Ω'' hΨ, range_hemiTwEmbC_le E' M E r hu2 Ω'' hΨ⟩

omit [E.IsElliptic] in
/-- **`Π_{C_M} ↪ Π_C`**: the orbicurve group of the twist (equal to that of `E'_M`,
`hemiTwCEquiv`) is an open normal subgroup of index `[M : K]` of `Π_C`, compatible with the
projections to `Gal(k̄ / K)`. -/
theorem hemiTw_constExt :
    IsOpenEmbedding (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top
      (hemiTwData_S E' M E r hu2 hΨ)) ∧
      (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top
        (hemiTwData_S E' M E r hu2 hΨ)).toMonoidHom.range.Normal ∧
      (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top
        (hemiTwData_S E' M E r hu2 hΨ)).toMonoidHom.range.index = Module.finrank K M ∧
      (piConstC (hemiData E')).comp (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top
        (hemiTwData_S E' M E r hu2 hΨ)).toMonoidHom = piConstC (hemiTwData E' M E u2 r) := by
  refine ⟨isOpenEmbedding_twInclC _ _ _ _, range_twInclC_normal _ _ _ _
      ((constFixer₃_normal M).subgroupOf _), ?_, piConstC_comp_twInclC _ _ _ _⟩
  rw [index_range_twInclC]
  change (constFixer₃ (coordT (xN E')) M).relIndex ⊤ = _
  rw [Subgroup.relIndex_top_right]
  exact index_constFixer₃ _ M (galResConst_surjective_hemi E')

end HemiTwArith

section HemiTwExists

-- The arithmetic part (as `CurvesJacobian.Cusp.HemiConstArith`) uses the default transparency.
set_option backward.isDefEq.respectTransparency true

variable {K : Type u} [Field K] [NumberField K] (E' : WeierstrassCurve K) [E'.IsElliptic]
  (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E')))) [FiniteDimensional K M]
  [IsGalois K M] (E : WeierstrassCurve M) [E.IsElliptic]
  (Ω'' : Type u) [Field Ω''] [Algebra M Ω''] [IsAlgClosed Ω''] [Algebra.IsAlgebraic M Ω'']
  [CharZero Ω'']

/-- **The iut-facing statement (T6)**: for an elliptic curve `E` over `M` with
`j(E) = j(E') ∉ {0, 1728}` (`E` is a quadratic twist of `E'_M`), there are `u2 ≠ 0`, `r` in `M`
with `x' = u2 x_E + r` such that the twist has the same inertia as the hemi-elliptic orbicurve
`C` of `E'`, and cj's arithmetic `π₁` of `E ∖ {O}` over `M` embeds into `Π_C` as an open
subgroup of index `2 · [M : K]`, compatibly with the projections to `Gal(k̄ / K)`, inside the
open normal subgroup `Π_{C_M}` of index `[M : K]`. -/
theorem hemiTw_exists_arith_emb (hj : E.j = (E'.baseChange M).j) (h0 : E.j ≠ 0)
    (h1728 : E.j ≠ 1728) :
    ∃ (u2 r : M) (hu2 : u2 ≠ 0)
      (hΨ : (E'.baseChange M).Ψ₂Sq.comp (C u2 * X + C r) = C (u2 ^ 3) * E.Ψ₂Sq),
      (hemiTwData E' M E u2 r).S = (hemiData E').S ∧
      IsOpenEmbedding (hemiTwEmbC E' M E r hu2 Ω'' hΨ) ∧
      (hemiTwEmbC E' M E r hu2 Ω'' hΨ).toMonoidHom.range.index = 2 * Module.finrank K M ∧
      (∀ γ : (arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).Pi,
        piConstC (hemiData E') ((hemiData E').equivPi1 (hemiTwEmbC E' M E r hu2 Ω'' hΨ γ)) =
        (hemiTwGkEquiv E' M E r hu2 Ω''
          ((arithmeticExt Ω'' (hypCurveX E) (compl_XE_nonempty E)).pr γ)).restrictScalars K) ∧
      (hemiTwEmbC E' M E r hu2 Ω'' hΨ).toMonoidHom.range ≤
        (twInclC (hemiTwData E' M E u2 r) (hemiData E') le_top
          (hemiTwData_S E' M E r hu2 hΨ)).toMonoidHom.range.map
            ((hemiData E').equivPi1.symm.toMulEquiv : _ →* _) := by
  exact (exists_tw_params M E' E hj h0 h1728).elim fun u2 h => h.elim fun r h =>
    ⟨u2, r, h.1, h.2, hemiTwData_S E' M E r h.1 h.2, hemiTw_arith_emb E' M E r h.1 Ω'' h.2⟩

end HemiTwExists

end CurvesJacobian.Cusp
