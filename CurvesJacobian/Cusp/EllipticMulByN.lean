/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticPunctured
import EllipticCurves.FunctionField.MulByNYCoordFormula
import EllipticCurves.Torsion.OmegaChordSum
import EllipticCurves.Torsion.CoprimeAdjacent
import Mathlib.Algebra.DualNumber

/-!
# Multiplication by `N`, `[N] : E ∖ E[N] → E ∖ {O}`, is finite étale

Let `E` be an elliptic curve over a field `K` of characteristic zero, `K[E]` its affine
coordinate ring (`E ∖ {O}`), `N ≥ 1`, `ψ_N ∈ K[E]` the `N`-division polynomial
(`CurvesJacobian.Cusp.psiN`, the image of Mathlib's `WeierstrassCurve.ψ`; `psiN E 2 = psiE E`)
and `B_N = K[E][1/ψ_N]` (`CurvesJacobian.Cusp.coverRingN`, `Γ(E ∖ E[N])`). The formulas

  `x ↦ Φ_N(x)/ψ_N²`, `y ↦ (ε_N preΩ_N(x) - ψ_N (a₁ Φ_N(x) + a₃ ΨSq_N(x))) / (2 ψ_N³)`

(`ε_N = 1` for even `N`, `ε_N = ψ₂` for odd `N`; the `y`-formula is `elliptic-curves`' `omegaY`)
define `[N]^* : K[E] → B_N` (`CurvesJacobian.Cusp.mulByNHom`). Inside `K(E)` it is the
multiplication-by-`N` pullback of `elliptic-curves` (`mulByNCoordHom`, `mulByNEndo`, defined from
`N • 𝒫` in the Mathlib group law): `CurvesJacobian.Cusp.coe_mulByNHom`,
`CurvesJacobian.Cusp.algebraMap_mulByNHom`; well-definedness comes from this.

**Main theorem** (`CurvesJacobian.Cusp.isFiniteEtale_spec_mulByNHom`): `Spec [N]^*` is finite
étale.

* *Finite*: `x` is a root of the monic `Φ_N(T) - [N]^*x · ΨSq_N(T)` (`deg Φ_N = N²`,
  `deg ΨSq_N < N²`), `y` is integral as `ψ₂² = Ψ₂Sq(x)`, and `1/ψ_N² = u(x) [N]^*x + v(x)` for a
  Bézout identity `u Φ_N + v ΨSq_N = 1` (`WeierstrassCurve.Affine.isCoprime_Φ_ΨSq`).
* *Unramified*: `B_N` carries the derivation `δ` with `δ x = ψ₂`, `δ y = -W_X`
  (`CurvesJacobian.Cusp.deltaN`, built from a lift `K[E] → B_N[ε]` to the dual numbers), and every
  `K`-derivation satisfies `d b = δ(b) · ω` with `ω = c dx - e dy`, `c ψ₂ + e W_X = 1`
  (nonsingularity). The Wronskian identity `Φ_N' ΨSq_N - Φ_N ΨSq_N' = N preΨ_N preΩ_N`
  (`WeierstrassCurve.hasWronskianId`) gives `δ([N]^*x) = N [N]^*ψ₂`, and the Weierstrass
  equation at `N • P` gives `δ([N]^*y) = -N [N]^*W_X` (`[N]^*ω = N ω`). As `[N]^*ψ₂`, `[N]^*W_X`
  generate the unit ideal and `N` is invertible, `ω = 0` in `Ω_{B_N/K[E]}`, so it vanishes.
* *Flat*: `K[E]` is a Dedekind domain and `B_N` is a torsion-free domain.

On `curveE E`: `VNE E N` is the basic open `{ψ_N ≠ 0}` of `XE E = E ∖ {O}`, with
`Γ(VNE) ≃ B_N` (`CurvesJacobian.Cusp.sectionsVNEEquiv`), and
`CurvesJacobian.Cusp.mulByNXMor : Spec Γ(VNE) ⟶ Spec Γ(XE)` is finite étale.
-/

open Polynomial AlgebraicGeometry WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate DualNumber

universe u

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] (E : WeierstrassCurve K) (N : ℕ)

section Basic

local notation "A" => E.toAffine.CoordinateRing

/-- The `N`-division polynomial `ψ_N` in `K[E]`. -/
noncomputable def psiN : A := AdjoinRoot.mk E.toAffine.polynomial (E.ψ N)

/-- `Γ(E ∖ E[N]) = K[E][1/ψ_N]`. -/
abbrev coverRingN := Localization.Away (psiN E N)

lemma psiN_two : psiN E 2 = psiE E := by
  rw [psiN, Nat.cast_ofNat, WeierstrassCurve.ψ_two]
  rfl

lemma psiN_sq : psiN E N ^ 2 = algebraMap K[X] A (E.ΨSq N) := by
  rw [psiN, mk_ψ, mk_Ψ_sq]
  rfl

lemma psiN_eq : psiN E N =
    algebraMap K[X] A (E.preΨ N) * (if Even (N : ℤ) then psiE E else 1) := by
  rw [psiN, mk_ψ, WeierstrassCurve.Ψ, map_mul, apply_ite (AdjoinRoot.mk _), map_one]
  rfl

/-- `ε_N = 1` for even `N` and `ε_N = ψ₂` for odd `N`, so that `preΨ_N ψ₂ = ε_N ψ_N`. -/
noncomputable def epsN : A := if Even (N : ℤ) then 1 else psiE E

lemma preΨ_mul_psiE : algebraMap K[X] A (E.preΨ N) * psiE E = epsN E N * psiN E N := by
  rw [psiN_eq, epsN]
  split_ifs <;> ring

lemma algebraMap_polynomial_injective : Function.Injective (algebraMap K[X] A) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
  have h : p • (1 : A) + (0 : K[X]) • AdjoinRoot.mk E.toAffine.polynomial Y = 0 := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one, hp]
  exact (smul_basis_eq_zero h).1

lemma algebraMap_polynomial_eq_aeval_xE (p : K[X]) : algebraMap K[X] A p = aeval (xE E) p := by
  rw [show xE E = algebraMap K[X] A X from rfl, aeval_algebraMap_apply, aeval_X_left_apply]

lemma psiN_ne_zero_of_neZero [CharZero K] [NeZero N] : psiN E N ≠ 0 := by
  intro h
  have h2 := psiN_sq E N
  rw [h, zero_pow two_ne_zero] at h2
  refine E.ΨSq_ne_zero (n := N) ?_
    ((map_eq_zero_iff _ (algebraMap_polynomial_injective E)).1 h2.symm)
  rw [Int.cast_natCast]
  exact Nat.cast_ne_zero.2 (NeZero.ne N)

end Basic

/-! ### The type synonym and the derivation `δ` -/

section Delta

local notation "A" => E.toAffine.CoordinateRing

/-- `K[E][1/ψ_N]`, to be regarded as a `K[E]`-algebra through `[N]^*`. -/
def MulByNB : Type u := coverRingN E N

noncomputable instance : CommRing (MulByNB E N) := inferInstanceAs (CommRing (coverRingN E N))

noncomputable instance : Algebra K (MulByNB E N) := inferInstanceAs (Algebra K (coverRingN E N))

/-- The identity `coverRingN → MulByNB`. -/
noncomputable def toMulByNB : coverRingN E N ≃ₐ[K] MulByNB E N := AlgEquiv.refl

/-- The localisation map `K[E] → MulByNB`. -/
noncomputable def locN : A →ₐ[K] MulByNB E N :=
  (toMulByNB E N).toAlgHom.comp (IsScalarTower.toAlgHom K A (coverRingN E N))

lemma locN_apply (a : A) : locN E N a = toMulByNB E N (algebraMap A (coverRingN E N) a) := rfl

/-- `1/ψ_N` in `MulByNB`. -/
noncomputable abbrev invPsiNM : MulByNB E N :=
  toMulByNB E N (IsLocalization.Away.invSelf (psiN E N))

lemma locN_psiN_mul_invPsiNM : locN E N (psiN E N) * invPsiNM E N = 1 := by
  rw [locN_apply, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

lemma locN_mem_adjoin (a : A) :
    locN E N a ∈ Algebra.adjoin K {locN E N (xE E), locN E N (yE E)} := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C q =>
    rw [show AdjoinRoot.mk E.toAffine.polynomial (C q) = algebraMap K[X] A q from rfl,
      algebraMap_polynomial_eq_aeval_xE, ← aeval_algHom_apply]
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
      (q.aeval_mem_adjoin_singleton K (locN E N (xE E)))
  | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
  | monomial n q h =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul]
    exact mul_mem h (Algebra.subset_adjoin (Set.mem_insert_of_mem _
      (Set.mem_singleton_iff.2 (by rw [AdjoinRoot.mk_X]))))

lemma adjoin_eq_top_mulByNB :
    Algebra.adjoin K {locN E N (xE E), locN E N (yE E), invPsiNM E N} = ⊤ := by
  refine eq_top_iff.2 fun b _ ↦ ?_
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (psiN E N) ((toMulByNB E N).symm b)
  have hb : b = locN E N a * invPsiNM E N ^ n := by
    rw [locN_apply, ← map_pow, ← map_mul, ← h, mul_assoc, ← mul_pow,
      IsLocalization.Away.mul_invSelf, one_pow, mul_one, AlgEquiv.apply_symm_apply]
  rw [hb]
  refine mul_mem (Algebra.adjoin_mono ?_ (locN_mem_adjoin E N a))
    (pow_mem (Algebra.subset_adjoin (by simp)) n)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  tauto

/-- The Weierstrass equation, first-order deformed: if `(x, y)` lies on the curve and
`W_X a + W_Y b = 0`, then `(x + aε, y + bε)` lies on the curve over the dual numbers. -/
lemma weierstrass_dual {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x y a b : R)
    (h : y ^ 2 + a₁ * x * y + a₃ * y - (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) = 0)
    (hd : (a₁ * y - (3 * x ^ 2 + 2 * a₂ * x + a₄)) * a + (2 * y + a₁ * x + a₃) * b = 0) :
    (algebraMap R R[ε] y + algebraMap R R[ε] b * ε) ^ 2 +
      algebraMap R R[ε] a₁ * (algebraMap R R[ε] x + algebraMap R R[ε] a * ε) *
        (algebraMap R R[ε] y + algebraMap R R[ε] b * ε) +
      algebraMap R R[ε] a₃ * (algebraMap R R[ε] y + algebraMap R R[ε] b * ε) -
      ((algebraMap R R[ε] x + algebraMap R R[ε] a * ε) ^ 3 +
        algebraMap R R[ε] a₂ * (algebraMap R R[ε] x + algebraMap R R[ε] a * ε) ^ 2 +
        algebraMap R R[ε] a₄ * (algebraMap R R[ε] x + algebraMap R R[ε] a * ε) +
        algebraMap R R[ε] a₆) = 0 := by
  have h' := congrArg (algebraMap R R[ε]) h
  have hd' := congrArg (algebraMap R R[ε]) hd
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_ofNat] at h' hd'
  set i := algebraMap R R[ε]
  linear_combination h' + (ε : R[ε]) * hd' + (i b ^ 2 + i a₁ * i a * i b - 3 * i x * i a ^ 2 -
    i a₂ * i a ^ 2 - i a ^ 3 * ε) * DualNumber.eps_mul_eps (R := R)

local notation "M" => MulByNB E N

lemma locN_equation : locN E N (yE E) ^ 2 + algebraMap K M E.a₁ * locN E N (xE E) *
    locN E N (yE E) + algebraMap K M E.a₃ * locN E N (yE E) - (locN E N (xE E) ^ 3 +
      algebraMap K M E.a₂ * locN E N (xE E) ^ 2 + algebraMap K M E.a₄ * locN E N (xE E) +
      algebraMap K M E.a₆) = 0 := by
  have h := congrArg (locN E N) (equation_E E)
  simpa only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_zero] using h

lemma locN_psiE : locN E N (psiE E) = 2 * locN E N (yE E) +
    algebraMap K M E.a₁ * locN E N (xE E) + algebraMap K M E.a₃ := by
  rw [psiE_eq']
  simp only [map_add, map_mul, AlgHom.commutes, map_ofNat]

lemma locN_wxE : locN E N (wxE E) = algebraMap K M E.a₁ * locN E N (yE E) -
    (3 * locN E N (xE E) ^ 2 + 2 * algebraMap K M E.a₂ * locN E N (xE E) +
      algebraMap K M E.a₄) := by
  rw [wxE]
  simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_ofNat]

/-- `K[E] → M[ε]`, `x ↦ x + ψ₂ ε`, `y ↦ y - W_X ε`: the tangent vector field dual to the invariant
differential. -/
noncomputable def deltaHomA : A →+* M[ε] :=
  AdjoinRoot.lift (eval₂RingHom ((algebraMap M M[ε]).comp (algebraMap K M))
    (algebraMap M M[ε] (locN E N (xE E)) + algebraMap M M[ε] (locN E N (psiE E)) * ε))
    (algebraMap M M[ε] (locN E N (yE E)) + algebraMap M M[ε] (-locN E N (wxE E)) * ε) (by
      have hd : (algebraMap K M E.a₁ * locN E N (yE E) - (3 * locN E N (xE E) ^ 2 +
          2 * algebraMap K M E.a₂ * locN E N (xE E) + algebraMap K M E.a₄)) *
          locN E N (psiE E) + (2 * locN E N (yE E) + algebraMap K M E.a₁ * locN E N (xE E) +
          algebraMap K M E.a₃) * (-locN E N (wxE E)) = 0 := by
        rw [locN_psiE, locN_wxE]; ring
      have key := weierstrass_dual _ _ _ _ _ _ _ _ _ (locN_equation E N) hd
      rw [eval₂_eval₂RingHom_apply, ← WeierstrassCurve.Affine.map_polynomial]
      change (E.map ((algebraMap M M[ε]).comp (algebraMap K M))).toAffine.Equation _ _
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, RingHom.comp_apply]
      linear_combination key)

lemma deltaHomA_algebraMap (c : K) :
    deltaHomA E N (algebraMap K A c) = algebraMap M M[ε] (algebraMap K M c) := by
  rw [IsScalarTower.algebraMap_apply K K[X] A, AdjoinRoot.algebraMap_eq, deltaHomA,
    AdjoinRoot.lift_of, coe_eval₂RingHom, Polynomial.algebraMap_apply, eval₂_C]
  rfl

lemma deltaHomA_xE : deltaHomA E N (xE E) =
    algebraMap M M[ε] (locN E N (xE E)) + algebraMap M M[ε] (locN E N (psiE E)) * ε := by
  have h : xE E = AdjoinRoot.of E.toAffine.polynomial X := rfl
  rw [h, deltaHomA, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]
  rfl

lemma deltaHomA_yE : deltaHomA E N (yE E) =
    algebraMap M M[ε] (locN E N (yE E)) + algebraMap M M[ε] (-locN E N (wxE E)) * ε := by
  rw [deltaHomA, AdjoinRoot.lift_root]

lemma fst_comp_deltaHomA :
    (TrivSqZeroExt.fstHom K M M).toRingHom.comp (deltaHomA E N) = (locN E N).toRingHom := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change (deltaHomA E N (algebraMap K A c)).fst = locN E N (algebraMap K A c)
      rw [deltaHomA_algebraMap, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl,
        TrivSqZeroExt.fst_inl]
    · change (deltaHomA E N (xE E)).fst = locN E N (xE E)
      rw [deltaHomA_xE]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
  · change (deltaHomA E N (yE E)).fst = locN E N (yE E)
    rw [deltaHomA_yE]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

lemma fst_deltaHomA (a : A) : (deltaHomA E N a).fst = locN E N a :=
  RingHom.congr_fun (fst_comp_deltaHomA E N) a

lemma isUnit_deltaHomA_psiN : IsUnit (deltaHomA E N (psiN E N)) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_deltaHomA]
  exact IsUnit.of_mul_eq_one _ (locN_psiN_mul_invPsiNM E N)

/-- The extension of `deltaHomA` to the localisation. -/
noncomputable def deltaHom : coverRingN E N →+* M[ε] :=
  IsLocalization.Away.lift (psiN E N) (isUnit_deltaHomA_psiN E N)

lemma deltaHom_algebraMap (a : A) :
    deltaHom E N (algebraMap A (coverRingN E N) a) = deltaHomA E N a :=
  IsLocalization.Away.lift_eq _ _ a

lemma fst_deltaHom (b : coverRingN E N) : (deltaHom E N b).fst = toMulByNB E N b := by
  have h : (TrivSqZeroExt.fstHom K M M).toRingHom.comp (deltaHom E N) =
      (toMulByNB E N).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (psiN E N)) ?_
    rw [RingHom.comp_assoc, deltaHom, IsLocalization.Away.lift_comp, fst_comp_deltaHomA]
    rfl
  exact RingHom.congr_fun h b

/-- The additive map underlying `δ`. -/
noncomputable def deltaLin : M →ₗ[K] M where
  toFun b := (deltaHom E N ((toMulByNB E N).symm b)).snd
  map_add' a b := by rw [map_add, map_add, TrivSqZeroExt.snd_add]
  map_smul' c b := by
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, map_mul,
      IsScalarTower.algebraMap_apply K A (coverRingN E N), deltaHom_algebraMap,
      deltaHomA_algebraMap, DualNumber.snd_mul]
    simp [TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def]

/-- **The derivation `δ` of `K[E][1/ψ_N]`** with `δ x = ψ₂`, `δ y = -W_X`
(so `d b = δ(b) · ω` for the invariant differential `ω = dx/ψ₂`). -/
noncomputable def deltaN : Derivation K M M :=
  Derivation.mk' (deltaLin E N) fun a b ↦ by
    change (deltaHom E N ((toMulByNB E N).symm (a * b))).snd =
      a * (deltaHom E N ((toMulByNB E N).symm b)).snd +
        b * (deltaHom E N ((toMulByNB E N).symm a)).snd
    rw [map_mul, map_mul, DualNumber.snd_mul, fst_deltaHom, fst_deltaHom]
    simp only [AlgEquiv.apply_symm_apply]
    ring

lemma deltaN_locN (a : A) : deltaN E N (locN E N a) = (deltaHomA E N a).snd := by
  have h : (toMulByNB E N).symm (locN E N a) = algebraMap A (coverRingN E N) a := by
    rw [locN_apply, AlgEquiv.symm_apply_apply]
  change (deltaHom E N ((toMulByNB E N).symm (locN E N a))).snd = _
  rw [h, deltaHom_algebraMap]

lemma deltaN_xE : deltaN E N (locN E N (xE E)) = locN E N (psiE E) := by
  rw [deltaN_locN, deltaHomA_xE]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

lemma deltaN_yE : deltaN E N (locN E N (yE E)) = -locN E N (wxE E) := by
  rw [deltaN_locN, deltaHomA_yE]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- Every `K`-derivation `d` of `M` is `d b = δ(b) • ω` with `ω = c dx - e dy`. -/
lemma derivation_eq_deltaN_smul {P : Type*} [AddCommGroup P] [Module M P] [Module K P]
    [IsScalarTower K M P] (d : Derivation K M P) {c e : A} (hce : c * psiE E + e * wxE E = 1)
    (b : M) : d b = deltaN E N b •
      (locN E N c • d (locN E N (xE E)) - locN E N e • d (locN E N (yE E))) := by
  have heq0 : locN E N (yE E) * locN E N (yE E) + algebraMap K M E.a₁ * locN E N (xE E) *
      locN E N (yE E) + algebraMap K M E.a₃ * locN E N (yE E) - (locN E N (xE E) *
      locN E N (xE E) * locN E N (xE E) + algebraMap K M E.a₂ * locN E N (xE E) *
      locN E N (xE E) + algebraMap K M E.a₄ * locN E N (xE E) + algebraMap K M E.a₆) = 0 := by
    linear_combination locN_equation E N
  have hrel : locN E N (wxE E) • d (locN E N (xE E)) + locN E N (psiE E) •
      d (locN E N (yE E)) = 0 := by
    have h := congrArg d heq0
    simp only [map_sub, map_add, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
      map_zero] at h
    rw [locN_psiE, locN_wxE]
    linear_combination (norm := module) h
  have hce' := congrArg (locN E N) hce
  simp only [map_add, map_mul, map_one] at hce'
  let d' : Derivation K M P := (LinearMap.toSpanSingleton M P
    (locN E N c • d (locN E N (xE E)) - locN E N e • d (locN E N (yE E)))).compDer (deltaN E N)
  have hd' : ∀ z, d' z = deltaN E N z •
      (locN E N c • d (locN E N (xE E)) - locN E N e • d (locN E N (yE E))) := fun z ↦ rfl
  have hx : d (locN E N (xE E)) = d' (locN E N (xE E)) := by
    rw [hd', deltaN_xE]
    linear_combination (norm := module) (locN E N e) • hrel - hce' • d (locN E N (xE E))
  have hy : d (locN E N (yE E)) = d' (locN E N (yE E)) := by
    rw [hd', deltaN_yE]
    linear_combination (norm := module) (locN E N c) • hrel - hce' • d (locN E N (yE E))
  have hxy : Set.EqOn d d' {locN E N (xE E), locN E N (yE E)} := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hu : d (invPsiNM E N) = d' (invPsiNM E N) := by
    have h1 : invPsiNM E N * locN E N (psiN E N) = 1 := by
      rw [mul_comm]; exact locN_psiN_mul_invPsiNM E N
    rw [Derivation.leibniz_of_mul_eq_one d h1, Derivation.leibniz_of_mul_eq_one d' h1,
      Derivation.eqOn_adjoin hxy (locN_mem_adjoin E N (psiN E N))]
  have heq : d = d' := by
    refine Derivation.ext_of_adjoin_eq_top _ (adjoin_eq_top_mulByNB E N) ?_
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hu
  calc d b = d' b := by rw [heq]
    _ = _ := hd' b

end Delta

/-! ### Elements of `K[E][1/ψ_N]` and the coordinates of `N • P` -/

section Coords

local notation "A" => E.toAffine.CoordinateRing

/-- `x ∈ K[E][1/ψ_N]`. -/
noncomputable abbrev xBN : coverRingN E N := algebraMap A (coverRingN E N) (xE E)

/-- `ψ_N ∈ K[E][1/ψ_N]`. -/
noncomputable abbrev psiNB : coverRingN E N := algebraMap A (coverRingN E N) (psiN E N)

/-- `1/ψ_N ∈ K[E][1/ψ_N]`. -/
noncomputable abbrev invPsiNB : coverRingN E N := IsLocalization.Away.invSelf (psiN E N)

lemma psiNB_mul_invPsiNB : psiNB E N * invPsiNB E N = 1 := IsLocalization.Away.mul_invSelf _

lemma algebraMap_aeval_xE (p : K[X]) :
    algebraMap A (coverRingN E N) (aeval (xE E) p) = aeval (xBN E N) p :=
  (aeval_algHom_apply (IsScalarTower.toAlgHom K A (coverRingN E N)) (xE E) p).symm

lemma psiNB_sq : psiNB E N ^ 2 = aeval (xBN E N) (E.ΨSq N) := by
  rw [← map_pow, psiN_sq, algebraMap_polynomial_eq_aeval_xE, algebraMap_aeval_xE]

/-- The `x`-coordinate of `N • P`: `Φ_N(x)/ψ_N²`. -/
noncomputable def xNB : coverRingN E N := aeval (xBN E N) (E.Φ N) * invPsiNB E N ^ 2

/-- The `y`-coordinate of `N • P`: `(ε_N preΩ_N(x) - ψ_N (a₁ Φ_N(x) + a₃ ΨSq_N(x))) / (2 ψ_N³)`,
where `ε_N = 1` for even `N` and `ε_N = ψ₂` for odd `N` (`elliptic-curves`' `omegaY`). -/
noncomputable def yNB : coverRingN E N :=
  algebraMap K (coverRingN E N) 2⁻¹ * (algebraMap A (coverRingN E N) (epsN E N) *
    aeval (xBN E N) (E.preΩ N) - psiNB E N * (algebraMap K (coverRingN E N) E.a₁ *
      aeval (xBN E N) (E.Φ N) + algebraMap K (coverRingN E N) E.a₃ *
        aeval (xBN E N) (E.ΨSq N))) * invPsiNB E N ^ 3

lemma xNB_mul_psiNB_sq : xNB E N * psiNB E N ^ 2 = aeval (xBN E N) (E.Φ N) := by
  rw [xNB]
  linear_combination aeval (xBN E N) (E.Φ N) * (psiNB E N * invPsiNB E N + 1) *
    psiNB_mul_invPsiNB E N

/-- `1/ψ_N² = u(x) x(N • P) + v(x)` for a Bézout identity `u Φ_N + v ΨSq_N = 1`. -/
lemma exists_invPsiNB_sq [CharZero K] [E.IsElliptic] :
    ∃ a b : K[X], invPsiNB E N ^ 2 = aeval (xBN E N) a * xNB E N + aeval (xBN E N) b := by
  obtain ⟨a, b, hab⟩ :=
    WeierstrassCurve.Affine.isCoprime_Φ_ΨSq (W := E.toAffine) two_ne_zero (N : ℤ)
  have hab' : a * E.Φ N + b * E.ΨSq N = 1 := hab
  refine ⟨a, b, ?_⟩
  have h := congrArg (aeval (xBN E N)) hab'
  rw [map_add, map_mul, map_mul, map_one, ← xNB_mul_psiNB_sq, ← psiNB_sq] at h
  linear_combination (-(invPsiNB E N ^ 2)) * h + (aeval (xBN E N) a * xNB E N +
    aeval (xBN E N) b) * (psiNB E N * invPsiNB E N + 1) * psiNB_mul_invPsiNB E N

end Coords

/-! ### `K[E][1/ψ_N]` inside the function field, and the map `[N]^*` -/

section FunctionField

variable [CharZero K] [NeZero N]

local notation "A" => E.toAffine.CoordinateRing

lemma intCast_N_ne_zero : ((N : ℤ) : K) ≠ 0 := by
  rw [Int.cast_natCast]
  exact Nat.cast_ne_zero.2 (NeZero.ne N)

/-- The inclusion `K[E][1/ψ_N] → K(E)`. -/
noncomputable instance : Algebra (coverRingN E N) E.toAffine.FunctionField :=
  (IsLocalization.Away.lift (psiN E N) (g := algebraMap A E.toAffine.FunctionField)
    (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (psiN_ne_zero_of_neZero E N)))).toAlgebra

instance : IsScalarTower A (coverRingN E N) E.toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq (psiN E N) _ a).symm

instance : IsDomain (coverRingN E N) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (psiN_ne_zero_of_neZero E N))

instance : IsFractionRing (coverRingN E N) E.toAffine.FunctionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (psiN E N)) _ _

lemma algebraMap_coverRingN_injective :
    Function.Injective (algebraMap (coverRingN E N) E.toAffine.FunctionField) :=
  IsFractionRing.injective _ _

local notation "ι" => algebraMap (coverRingN E N) E.toAffine.FunctionField
local notation "φ" => algebraMap K E.toAffine.FunctionField

lemma ιN_algebraMap (a : A) :
    ι (algebraMap A (coverRingN E N) a) = algebraMap A E.toAffine.FunctionField a :=
  (IsScalarTower.algebraMap_apply _ _ _ a).symm

lemma ιN_algebraMap_K (c : K) : ι (algebraMap K (coverRingN E N) c) = φ c := by
  rw [IsScalarTower.algebraMap_apply K A (coverRingN E N), ιN_algebraMap,
    ← IsScalarTower.algebraMap_apply]

instance : IsScalarTower K (coverRingN E N) E.toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (ιN_algebraMap_K E N c).symm

lemma ιN_xBN : ι (xBN E N) = genX E.toAffine := ιN_algebraMap E N _

lemma ιN_aeval (p : K[X]) : ι (aeval (xBN E N) p) = aeval (genX E.toAffine) p := by
  rw [← ιN_xBN E N]
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom K (coverRingN E N)
    E.toAffine.FunctionField) _ p).symm

lemma ιN_psiNB : ι (psiNB E N) =
    ((E.map φ).ψ N).evalEval (genX E.toAffine) (genY E.toAffine) := by
  rw [WeierstrassCurve.map_ψ, ← genPsi_mk_map_evalEval, ιN_algebraMap, psiN]

omit [CharZero K] in
lemma ιN_psiE : algebraMap A E.toAffine.FunctionField (psiE E) =
    2 * genY E.toAffine + φ E.a₁ * genX E.toAffine + φ E.a₃ := by
  rw [psiE_eq']
  simp only [map_add, map_mul, map_ofNat, ← IsScalarTower.algebraMap_apply]
  rfl

lemma ιN_psiNB_mul_invPsiNB : ι (psiNB E N) * ι (invPsiNB E N) = 1 := by
  rw [← map_mul, psiNB_mul_invPsiNB, map_one]

lemma ιN_psiNB_ne_zero : ι (psiNB E N) ≠ 0 := by
  intro h
  simpa [h] using ιN_psiNB_mul_invPsiNB E N

lemma ιN_psiNB_sq : ι (psiNB E N) ^ 2 = aeval (genX E.toAffine) (E.ΨSq N) := by
  rw [← map_pow, psiNB_sq, ιN_aeval]

variable [E.IsElliptic]

/-- `x(N • P)` is transcendental over `K`: the hypothesis of `elliptic-curves`' `mulByNEndo`. -/
lemma transcendental_N : Transcendental K (N • genericPoint (W := E.toAffine)).xCoord :=
  transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero two_ne_zero (intCast_N_ne_zero N)

lemma ιN_xNB : ι (xNB E N) = (N • genericPoint (W := E.toAffine)).xCoord := by
  have h := ιN_psiNB_mul_invPsiNB E N
  have hp := ιN_psiNB_ne_zero E N
  rw [xCoord_nsmul_genericPoint two_ne_zero (intCast_N_ne_zero N), xNB, map_mul, map_pow,
    ιN_aeval]
  change _ = aeval (genX E.toAffine) (E.Φ N) / aeval (genX E.toAffine) (E.ΨSq N)
  rw [← ιN_psiNB_sq, eq_div_iff (pow_ne_zero 2 hp)]
  linear_combination aeval (genX E.toAffine) (E.Φ N) * (ι (psiNB E N) * ι (invPsiNB E N) + 1) * h

lemma ιN_yNB : ι (yNB E N) = (N • genericPoint (W := E.toAffine)).yCoord := by
  have h := ιN_psiNB_mul_invPsiNB E N
  have hp := ιN_psiNB_ne_zero E N
  have h2 : (2 : E.toAffine.FunctionField) ≠ 0 := by
    have := (map_ne_zero φ).2 (two_ne_zero (α := K))
    rwa [map_ofNat] at this
  have hε : ι (algebraMap A (coverRingN E N) (epsN E N)) = if Even (N : ℤ) then 1 else
      2 * genY E.toAffine + (E.map φ).a₁ * genX E.toAffine + (E.map φ).a₃ := by
    rw [ιN_algebraMap, epsN, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    split_ifs
    · exact map_one _
    · exact ιN_psiE E
  rw [yCoord_nsmul_genericPoint two_ne_zero (intCast_N_ne_zero N), WeierstrassCurve.Affine.omegaY,
    ← hε, ← ιN_psiNB, yNB]
  simp only [map_mul, map_sub, map_add, map_pow, ιN_algebraMap_K, ιN_aeval, map_inv₀, map_ofNat,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, WeierstrassCurve.map_Φ,
    WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_preΩ, eval_map, ← aeval_def]
  rw [eq_div_iff (mul_ne_zero h2 (pow_ne_zero 3 hp))]
  field_simp
  linear_combination (ι (algebraMap A (coverRingN E N) (epsN E N)) *
      aeval (genX E.toAffine) (E.preΩ N) -
    ι (psiNB E N) * φ E.a₁ * aeval (genX E.toAffine) (E.Φ N) -
    ι (psiNB E N) * φ E.a₃ * aeval (genX E.toAffine) (E.ΨSq N)) *
      (ι (psiNB E N) ^ 2 * ι (invPsiNB E N) ^ 2 + ι (psiNB E N) * ι (invPsiNB E N) + 1) * h

/-- **The multiplication-by-`N` map** `[N]^* : K[E] → K[E][1/ψ_N]`, `x ↦ x(N • P)`,
`y ↦ y(N • P)`. -/
noncomputable def mulByNHom : A →+* coverRingN E N :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap K (coverRingN E N)) (xNB E N)) (yNB E N) (by
    apply algebraMap_coverRingN_injective E N
    have hc : RingHom.comp ι (eval₂RingHom (algebraMap K (coverRingN E N)) (xNB E N)) =
        eval₂RingHom φ (N • genericPoint (W := E.toAffine)).xCoord := by
      refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
      · simp [ιN_algebraMap_K]
      · simp [ιN_xNB]
    have h0 := congrArg (mulByNCoordHom (W := E.toAffine) N (transcendental_N E N))
      (AdjoinRoot.mk_self (f := E.toAffine.polynomial))
    rw [map_zero, mulByNCoordHom, pointCoordHom, AdjoinRoot.lift_mk] at h0
    rw [map_zero, hom_eval₂, ιN_yNB, hc]
    exact h0)

lemma mulByNHom_x : mulByNHom E N (xE E) = xNB E N := by
  rw [mulByNHom, AdjoinRoot.lift_mk, eval₂_C, coe_eval₂RingHom, eval₂_X]

lemma mulByNHom_y : mulByNHom E N (yE E) = yNB E N := by
  rw [mulByNHom, AdjoinRoot.lift_root]

lemma mulByNHom_algebraMap (c : K) :
    mulByNHom E N (algebraMap K A c) = algebraMap K (coverRingN E N) c := by
  rw [IsScalarTower.algebraMap_apply K K[X] A, AdjoinRoot.algebraMap_eq, mulByNHom,
    AdjoinRoot.lift_of, coe_eval₂RingHom, Polynomial.algebraMap_apply, eval₂_C]
  rfl

/-- `[N]^*` as a `K`-algebra map. -/
noncomputable def mulByNAlgHom : A →ₐ[K] coverRingN E N where
  toRingHom := mulByNHom E N
  commutes' := mulByNHom_algebraMap E N

/-- `[N]^*` followed by `K[E][1/ψ_N] ⊆ K(E)` is the multiplication-by-`N` pullback
`mulByNCoordHom` of `elliptic-curves` (defined from `N • 𝒫` in the Mathlib group law). -/
theorem coe_mulByNHom :
    RingHom.comp ι (mulByNHom E N) = mulByNCoordHom (W := E.toAffine) N (transcendental_N E N) := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change ι (mulByNHom E N (algebraMap K A c)) =
        mulByNCoordHom (W := E.toAffine) N (transcendental_N E N) (algebraMap K A c)
      rw [mulByNHom_algebraMap, mulByNCoordHom, pointCoordHom_algebraMap, ιN_algebraMap_K]
    · change ι (mulByNHom E N (xE E)) =
        mulByNCoordHom (W := E.toAffine) N (transcendental_N E N) (xE E)
      rw [mulByNHom_x, ιN_xNB, mulByNCoordHom, pointCoordHom_X]
  · change ι (mulByNHom E N (yE E)) =
      mulByNCoordHom (W := E.toAffine) N (transcendental_N E N) (yE E)
    rw [mulByNHom_y, ιN_yNB, mulByNCoordHom, pointCoordHom_root]

/-- **Link to the group law**: on `K(E)`, `[N]^*` is `elliptic-curves`' `mulByNEndo N`, the
pullback along `P ↦ N • P`. -/
theorem algebraMap_mulByNHom (a : A) :
    ι (mulByNHom E N a) =
      mulByNEndo (W := E.toAffine) N (transcendental_N E N) (algebraMap A _ a) := by
  rw [← RingHom.comp_apply ι, coe_mulByNHom, mulByNEndo, pointEndo_algebraMap]
  rfl

/-- `[N]^*` is injective (`[N]` is dominant). -/
theorem mulByNHom_injective : Function.Injective (mulByNHom E N) := by
  intro a b h
  have hinj : Function.Injective (mulByNCoordHom (W := E.toAffine) N (transcendental_N E N)) :=
    pointCoordHom_injective _ (transcendental_N E N)
  apply hinj
  rw [← coe_mulByNHom, RingHom.comp_apply, RingHom.comp_apply, h]

omit [CharZero K] [NeZero N] [E.IsElliptic] in
lemma two_inv_mul_two' [CharZero K] :
    algebraMap K (coverRingN E N) 2⁻¹ * 2 = 1 := by
  rw [← map_ofNat (algebraMap K (coverRingN E N)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
    map_one]

/-- `[N]^* ψ₂ = ε_N preΩ_N(x) / ψ_N³` (`= ψ_{2N}/ψ_N⁴`). -/
lemma mulByNHom_psiE : mulByNHom E N (psiE E) = algebraMap A (coverRingN E N) (epsN E N) *
    aeval (xBN E N) (E.preΩ N) * invPsiNB E N ^ 3 := by
  rw [show mulByNHom E N (psiE E) = mulByNHom E N _ from congrArg (mulByNHom E N) (psiE_eq' E),
    map_add, map_add, map_mul, map_mul, mulByNHom_y, mulByNHom_algebraMap,
    mulByNHom_algebraMap, map_ofNat, mulByNHom_x, xNB, yNB]
  linear_combination (algebraMap A (coverRingN E N) (epsN E N) * aeval (xBN E N) (E.preΩ N) -
      psiNB E N * (algebraMap K (coverRingN E N) E.a₁ * aeval (xBN E N) (E.Φ N) +
        algebraMap K (coverRingN E N) E.a₃ * aeval (xBN E N) (E.ΨSq N))) * invPsiNB E N ^ 3 *
      two_inv_mul_two' E N +
    (-(algebraMap K (coverRingN E N) E.a₁ * aeval (xBN E N) (E.Φ N) * invPsiNB E N ^ 2) -
      algebraMap K (coverRingN E N) E.a₃ * (psiNB E N ^ 2 * invPsiNB E N ^ 2 +
        psiNB E N * invPsiNB E N + 1)) * psiNB_mul_invPsiNB E N +
    algebraMap K (coverRingN E N) E.a₃ * psiNB E N * invPsiNB E N ^ 3 * psiNB_sq E N

end FunctionField

/-! ### `K[E][1/ψ_N]` as a `K[E]`-algebra via `[N]^*`: finiteness -/

section MulByNAlgebra

variable [CharZero K] [NeZero N] [E.IsElliptic]

local notation "A" => E.toAffine.CoordinateRing

instance : IsDomain (MulByNB E N) := inferInstanceAs (IsDomain (coverRingN E N))

noncomputable instance : Algebra A (MulByNB E N) := (mulByNHom E N).toAlgebra

instance : IsScalarTower K A (MulByNB E N) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (mulByNHom_algebraMap E N c).symm

lemma algebraMap_mulByNB (a : A) :
    algebraMap A (MulByNB E N) a = toMulByNB E N (mulByNHom E N a) := rfl

lemma isIntegral_algebraMap_K' (c : K) :
    IsIntegral A (toMulByNB E N (algebraMap K _ c)) := by
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply K A (MulByNB E N)]
  exact isIntegral_algebraMap

omit [CharZero K] [NeZero N] [E.IsElliptic] in
lemma toMulByNB_aeval (p : K[X]) :
    toMulByNB E N (aeval (xBN E N) p) = aeval (toMulByNB E N (xBN E N)) p :=
  (aeval_algHom_apply (toMulByNB E N).toAlgHom _ _).symm

lemma isIntegral_xBN : IsIntegral A (toMulByNB E N (xBN E N)) := by
  refine ⟨(E.Φ N).map (algebraMap K A) - C (xE E) * (E.ΨSq N).map (algebraMap K A), ?_, ?_⟩
  · refine Monic.sub_of_left ((show (E.Φ N).Monic from E.leadingCoeff_Φ N).map _) ?_
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    rw [degree_map, degree_map, degree_eq_natDegree (E.Φ_ne_zero N), E.natDegree_Φ,
      Int.natAbs_natCast]
    refine (degree_le_natDegree.trans (WithBot.coe_le_coe.2 (E.natDegree_ΨSq_le N))).trans_lt ?_
    rw [Int.natAbs_natCast]
    exact WithBot.coe_lt_coe.2 (Nat.sub_lt (pow_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 2) one_pos)
  · have hc : ∀ p : K[X], eval₂ (algebraMap K (MulByNB E N)) (toMulByNB E N (xBN E N)) p =
        toMulByNB E N (aeval (xBN E N) p) := fun p ↦ by
      rw [← aeval_def]
      exact aeval_algHom_apply (toMulByNB E N).toAlgHom _ _
    rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_map, eval₂_map, ← IsScalarTower.algebraMap_eq,
      hc, hc, algebraMap_mulByNB, mulByNHom_x, ← map_mul, ← map_sub, ← xNB_mul_psiNB_sq,
      psiNB_sq, sub_self, map_zero]

lemma isIntegral_aeval_xBN (p : K[X]) : IsIntegral A (toMulByNB E N (aeval (xBN E N) p)) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C]; exact isIntegral_algebraMap_K' E N a
  | add p q hp hq => rw [map_add, map_add]; exact hp.add hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, map_mul]
    exact h.mul (isIntegral_xBN E N)

lemma isIntegral_xNB : IsIntegral A (toMulByNB E N (xNB E N)) := by
  rw [← mulByNHom_x, ← algebraMap_mulByNB]
  exact isIntegral_algebraMap

lemma isIntegral_invPsiNB : IsIntegral A (toMulByNB E N (invPsiNB E N)) := by
  obtain ⟨a, b, h⟩ := exists_invPsiNB_sq E N
  refine IsIntegral.of_pow two_pos ?_
  rw [← map_pow, h, map_add, map_mul]
  exact ((isIntegral_aeval_xBN E N a).mul (isIntegral_xNB E N)).add (isIntegral_aeval_xBN E N b)

lemma isIntegral_psiE : IsIntegral A (toMulByNB E N (algebraMap A _ (psiE E))) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [← map_pow, ← map_pow, psi_sq, algebraMap_polynomial_eq_aeval_xE, algebraMap_aeval_xE]
  exact isIntegral_aeval_xBN E N _

lemma isIntegral_yBN : IsIntegral A (toMulByNB E N (algebraMap A _ (yE E))) := by
  have hψ := congrArg (algebraMap A (coverRingN E N)) (psiE_eq' E)
  simp only [map_add, map_mul, map_ofNat, ← IsScalarTower.algebraMap_apply] at hψ
  have h : algebraMap A (coverRingN E N) (yE E) = algebraMap K (coverRingN E N) 2⁻¹ *
      (algebraMap A _ (psiE E) - algebraMap K (coverRingN E N) E.a₁ * xBN E N -
        algebraMap K (coverRingN E N) E.a₃) := by
    rw [hψ]
    linear_combination (-algebraMap A (coverRingN E N) (yE E)) * two_inv_mul_two' E N
  rw [h, map_mul, map_sub, map_sub, map_mul]
  exact (isIntegral_algebraMap_K' E N _).mul (((isIntegral_psiE E N).sub
    ((isIntegral_algebraMap_K' E N _).mul (isIntegral_xBN E N))).sub
      (isIntegral_algebraMap_K' E N _))

/-- The image of `K[E]` in `K[E][1/ψ_N]` is integral over `K[E]` via `[N]^*`. -/
lemma isIntegral_algebraMap_coordinateRing' (a : A) :
    IsIntegral A (toMulByNB E N (algebraMap A (coverRingN E N) a)) := by
  let S := integralClosure A (MulByNB E N)
  let ψ : A →+* MulByNB E N := (toMulByNB E N).toRingHom.comp (algebraMap A (coverRingN E N))
  let f : K[X] →+* S := eval₂RingHom ((algebraMap A S).comp (algebraMap K A))
    ⟨toMulByNB E N (xBN E N), isIntegral_xBN E N⟩
  have h1 : ψ.comp (algebraMap K[X] A) = S.val.toRingHom.comp f := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp only [RingHom.comp_apply, f, coe_eval₂RingHom, eval₂_C]
      change toMulByNB E N (algebraMap A (coverRingN E N) (algebraMap K[X] A (C c))) =
        algebraMap A (MulByNB E N) (algebraMap K A c)
      rw [algebraMap_mulByNB, mulByNHom_algebraMap, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K K[X] (coverRingN E N)]
      rfl
    · simp only [RingHom.comp_apply, f, coe_eval₂RingHom, eval₂_X]
      rfl
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  have h2 : ψ (AdjoinRoot.mk _ p) =
      S.val (p.eval₂ f ⟨toMulByNB E N (algebraMap A _ (yE E)), isIntegral_yBN E N⟩) := by
    rw [← AdjoinRoot.aeval_eq, aeval_def, hom_eval₂, h1]
    exact (hom_eval₂ p f S.val.toRingHom
      ⟨toMulByNB E N (algebraMap A _ (yE E)), isIntegral_yBN E N⟩).symm
  exact h2 ▸ (p.eval₂ f ⟨toMulByNB E N (algebraMap A _ (yE E)), isIntegral_yBN E N⟩).2

instance : Algebra.IsIntegral A (MulByNB E N) := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (psiN E N) ((toMulByNB E N).symm b)
  have hb : (toMulByNB E N).symm b = algebraMap A (coverRingN E N) a * invPsiNB E N ^ n := by
    rw [← h, mul_assoc, ← mul_pow, psiNB_mul_invPsiNB, one_pow, mul_one]
  rw [← (toMulByNB E N).apply_symm_apply b, hb, map_mul, map_pow]
  exact (isIntegral_algebraMap_coordinateRing' E N a).mul ((isIntegral_invPsiNB E N).pow n)

/-- **`[N]` is finite**. -/
instance : Module.Finite A (MulByNB E N) :=
  haveI : Algebra.FiniteType K (MulByNB E N) :=
    inferInstanceAs (Algebra.FiniteType K (coverRingN E N))
  haveI := Algebra.FiniteType.of_restrictScalars_finiteType K A (MulByNB E N)
  Algebra.IsIntegral.finite

end MulByNAlgebra

/-! ### `[N]` is unramified: `[N]^* ω = N ω` -/

section Unramified

variable [CharZero K] [NeZero N] [E.IsElliptic]

local notation "A" => E.toAffine.CoordinateRing
local notation "M" => MulByNB E N

omit [CharZero K] [NeZero N] [E.IsElliptic] in
lemma locN_aeval (p : K[X]) : locN E N (aeval (xE E) p) = aeval (locN E N (xE E)) p :=
  (aeval_algHom_apply (locN E N) _ p).symm

omit [CharZero K] [NeZero N] [E.IsElliptic] in
lemma deltaN_aeval (p : K[X]) : deltaN E N (aeval (locN E N (xE E)) p) =
    aeval (locN E N (xE E)) (derivative p) * locN E N (psiE E) := by
  rw [Derivation.map_aeval, deltaN_xE, smul_eq_mul]

omit [CharZero K] [NeZero N] [E.IsElliptic] in
/-- `δ(Φ_N(x)/ψ_N²) = N ε_N preΩ_N(x)/ψ_N³`: the Wronskian identity
`Φ_N' ΨSq_N - Φ_N ΨSq_N' = N preΨ_N preΩ_N` is `[N]^* ω = N ω`. -/
lemma deltaN_xN : deltaN E N (aeval (locN E N (xE E)) (E.Φ N) * invPsiNM E N ^ 2) =
    N * (locN E N (epsN E N) * aeval (locN E N (xE E)) (E.preΩ N) * invPsiNM E N ^ 3) := by
  rw [sq, Derivation.leibniz, Derivation.leibniz, deltaN_aeval]
  simp only [smul_eq_mul]
  have h1 : locN E N (psiN E N) * invPsiNM E N = 1 := locN_psiN_mul_invPsiNM E N
  have h5 : locN E N (psiN E N) * locN E N (psiN E N) = aeval (locN E N (xE E)) (E.ΨSq N) := by
    rw [← sq, ← map_pow, psiN_sq, algebraMap_polynomial_eq_aeval_xE, locN_aeval]
  have h2 := congrArg (deltaN E N) h5
  rw [Derivation.leibniz, deltaN_aeval, smul_eq_mul] at h2
  have h3 := congrArg (deltaN E N) h1
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h3
  have hW : derivative (E.Φ N) * E.ΨSq N - E.Φ N * derivative (E.ΨSq N) =
      ((N : ℤ) : K[X]) * E.preΨ N * E.preΩ N := E.hasWronskianId N
  have hid := congrArg (aeval (locN E N (xE E))) hW
  simp only [map_sub, map_mul, map_natCast, Int.cast_natCast] at hid
  have hεψ := congrArg (locN E N) (preΨ_mul_psiE E N)
  rw [map_mul, map_mul, algebraMap_polynomial_eq_aeval_xE, locN_aeval] at hεψ
  have hdP2 : 2 * deltaN E N (locN E N (psiN E N)) = aeval (locN E N (xE E))
      (derivative (E.ΨSq N)) * locN E N (psiE E) * invPsiNM E N := by
    linear_combination invPsiNM E N * h2 - 2 * deltaN E N (locN E N (psiN E N)) * h1
  have hdU : deltaN E N (invPsiNM E N) =
      -(invPsiNM E N ^ 2 * deltaN E N (locN E N (psiN E N))) := by
    linear_combination invPsiNM E N * h3 - deltaN E N (invPsiNM E N) * h1
  linear_combination 2 * aeval (locN E N (xE E)) (E.Φ N) * invPsiNM E N * hdU -
    aeval (locN E N (xE E)) (E.Φ N) * invPsiNM E N ^ 3 * hdP2 -
    aeval (locN E N (xE E)) (derivative (E.Φ N)) * locN E N (psiE E) * invPsiNM E N ^ 2 *
      (locN E N (psiN E N) * invPsiNM E N + 1) * h1 +
    aeval (locN E N (xE E)) (derivative (E.Φ N)) * locN E N (psiE E) * invPsiNM E N ^ 4 * h5 +
    locN E N (psiE E) * invPsiNM E N ^ 4 * hid +
    N * invPsiNM E N ^ 4 * aeval (locN E N (xE E)) (E.preΩ N) * hεψ +
    N * locN E N (epsN E N) * aeval (locN E N (xE E)) (E.preΩ N) * invPsiNM E N ^ 3 * h1

lemma algebraMap_mulByNB_xE : algebraMap A M (xE E) =
    aeval (locN E N (xE E)) (E.Φ N) * invPsiNM E N ^ 2 := by
  rw [algebraMap_mulByNB, mulByNHom_x, xNB, map_mul, map_pow, toMulByNB_aeval]
  rfl

lemma algebraMap_mulByNB_psiE : algebraMap A M (psiE E) =
    locN E N (epsN E N) * aeval (locN E N (xE E)) (E.preΩ N) * invPsiNM E N ^ 3 := by
  rw [algebraMap_mulByNB, mulByNHom_psiE, map_mul, map_mul, map_pow, toMulByNB_aeval]
  rfl

/-- `δ([N]^* x) = N [N]^* ψ₂`. -/
lemma deltaN_mulByN_xE : deltaN E N (algebraMap A M (xE E)) = N * algebraMap A M (psiE E) := by
  rw [algebraMap_mulByNB_xE, algebraMap_mulByNB_psiE, deltaN_xN]

lemma algebraMap_mulByNB_injective : Function.Injective (algebraMap A M) :=
  (toMulByNB E N).injective.comp (mulByNHom_injective E N)

/-- `δ([N]^* y) = -N [N]^* W_X`, from the Weierstrass equation at `N • P`. -/
lemma deltaN_mulByN_yE :
    deltaN E N (algebraMap A M (yE E)) = -(N * algebraMap A M (wxE E)) := by
  have heq := congrArg (algebraMap A M) (equation_E E)
  simp only [map_sub, map_add, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply K A M] at heq
  have hd := congrArg (deltaN E N) heq
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, smul_eq_mul, map_zero, nsmul_eq_mul] at hd
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
    pow_one] at hd
  have hψ := congrArg (algebraMap A M) (psiE_eq' E)
  simp only [map_add, map_mul, map_ofNat, ← IsScalarTower.algebraMap_apply K A M] at hψ
  have hwx := congrArg (algebraMap A M) (rfl : wxE E = wxE E)
  conv_rhs at hwx => rw [wxE]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
    ← IsScalarTower.algebraMap_apply K A M] at hwx
  have hx := deltaN_mulByN_xE E N
  have hne : algebraMap A M (psiE E) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_mulByNB_injective E N)).2 (psiE_ne_zero E)
  have key : algebraMap A M (psiE E) * (deltaN E N (algebraMap A M (yE E)) +
      N * algebraMap A M (wxE E)) = 0 := by
    linear_combination hd + deltaN E N (algebraMap A M (yE E)) * hψ -
      (algebraMap K M E.a₁ * algebraMap A M (yE E) - (3 * algebraMap A M (xE E) ^ 2 +
        2 * algebraMap K M E.a₂ * algebraMap A M (xE E) + algebraMap K M E.a₄)) * hx +
      N * algebraMap A M (psiE E) * hwx
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 key).resolve_left hne)

/-- **`[N]` is unramified**: `Ω_{K[E][1/ψ_N]/K[E]} = 0`. -/
instance : Algebra.FormallyUnramified A M := by
  rw [Algebra.formallyUnramified_iff]
  let d : Derivation K M Ω[M⁄A] := (KaehlerDifferential.D A M).restrictScalars K
  obtain ⟨c, e, hce⟩ := exists_mul_psiE_add_mul_wxE E
  have hd : ∀ b, d b = deltaN E N b • (locN E N c • d (locN E N (xE E)) -
      locN E N e • d (locN E N (yE E))) := derivation_eq_deltaN_smul E N d hce
  have hx0 : d (algebraMap A M (xE E)) = 0 := (KaehlerDifferential.D A M).map_algebraMap _
  have hy0 : d (algebraMap A M (yE E)) = 0 := (KaehlerDifferential.D A M).map_algebraMap _
  rw [hd, deltaN_mulByN_xE] at hx0
  rw [hd, deltaN_mulByN_yE] at hy0
  have hce' := congrArg (algebraMap A M) hce
  simp only [map_add, map_mul, map_one] at hce'
  have hN : algebraMap K M (N : K)⁻¹ * (N : M) = 1 := by
    rw [← map_natCast (algebraMap K M), ← map_mul, inv_mul_cancel₀
      (Nat.cast_ne_zero.2 (NeZero.ne N)), map_one]
  have hω : locN E N c • d (locN E N (xE E)) - locN E N e • d (locN E N (yE E)) = 0 := by
    linear_combination (norm := module)
      (algebraMap K M (N : K)⁻¹ * algebraMap A M c) • hx0 +
      (-(algebraMap K M (N : K)⁻¹ * algebraMap A M e)) • hy0 -
      hN • (locN E N c • d (locN E N (xE E)) - locN E N e • d (locN E N (yE E))) -
      hce' • ((algebraMap K M (N : K)⁻¹ * (N : M)) •
        (locN E N c • d (locN E N (xE E)) - locN E N e • d (locN E N (yE E))))
  refine subsingleton_of_forall_eq 0 fun ω ↦ ?_
  have hmem : ω ∈ Submodule.span M (Set.range (KaehlerDifferential.D A M)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction (fun _ ⟨b, hb⟩ ↦ ?_) rfl (fun _ _ _ _ h h' ↦ by
    rw [h, h', add_zero]) (fun a _ _ h ↦ by rw [h, smul_zero]) hmem
  rw [← hb]
  change d b = 0
  rw [hd, hω, smul_zero]

/-- **`[N]` is flat**: `K[E]` is a Dedekind domain and `K[E][1/ψ_N]` is torsion-free. -/
instance : Module.Flat A M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
  refine eq_bot_iff.2 fun b hb ↦ ?_
  obtain ⟨⟨a, ha⟩, hab⟩ := (Submodule.mem_torsion_iff b).1 hb
  rw [Submodule.mem_bot]
  rw [Submonoid.smul_def, Algebra.smul_def] at hab
  refine (mul_eq_zero.1 hab).resolve_left ?_
  exact (map_ne_zero_iff _ (algebraMap_mulByNB_injective E N)).2 (nonZeroDivisors.ne_zero ha)

instance : Algebra.Etale A M :=
  haveI : Algebra.FinitePresentation A M :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  Algebra.Etale.of_formallyUnramified_of_flat

/-- **`[N] : E ∖ E[N] → E ∖ {O}` is finite étale** (`Spec` of `[N]^* : K[E] → K[E][1/ψ_N]`). -/
theorem isFiniteEtale_spec_mulByNHom :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (mulByNHom E N))) := by
  have : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap A M))) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
    exact ⟨⟩
  exact this

end Unramified

/-! ### `E ∖ E[N]` as an open of `curveE E` -/

section Scheme

open CategoryTheory

variable [CharZero K] [NeZero N] [E.IsElliptic]

/-- `ψ_N` as a function on `E ∖ {O}` (`XE E`). -/
noncomputable def psiNX : Γ(curveE E, XE E) := (sectionsXEAlgEquiv E).symm (psiN E N)

/-- **`E ∖ E[N]`**: the basic open `{ψ_N ≠ 0}` of `E ∖ {O}` in `curveE E`. -/
noncomputable abbrev VNE : (curveE E).Opens := (curveE E).basicOpen (psiNX E N)

omit [NeZero N] in
lemma VNE_le_XE : VNE E N ≤ XE E := (curveE E).basicOpen_le _

omit [NeZero N] in
lemma isAffineOpen_VNE : IsAffineOpen (VNE E N) := (isAffineOpen_XE E).basicOpen _

instance : IsLocalization.Away (psiNX E N) Γ(curveE E, VNE E N) :=
  (isAffineOpen_XE E).isLocalization_basicOpen (psiNX E N)

/-- **`Γ(E ∖ E[N]) = K[E][1/ψ_N]`**. -/
noncomputable def sectionsVNEEquiv : Γ(curveE E, VNE E N) ≃+* coverRingN E N :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (psiNX E N))
    (T := Submonoid.powers (psiN E N)) _ _ (sectionsXEAlgEquiv E).toRingEquiv (by
      rw [Submonoid.map_powers]
      congr 1
      exact (sectionsXEAlgEquiv E).apply_symm_apply _)

omit [NeZero N] in
/-- The restriction `Γ(E ∖ {O}) → Γ(E ∖ E[N])` is `K[E] → K[E][1/ψ_N]`. -/
lemma sectionsVNEEquiv_algebraMap (s : Γ(curveE E, XE E)) :
    sectionsVNEEquiv E N (algebraMap _ Γ(curveE E, VNE E N) s) =
      algebraMap _ (coverRingN E N) (sectionsXEAlgEquiv E s) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ s

/-- `[N]^* : Γ(E ∖ {O}) → Γ(E ∖ E[N])`. -/
noncomputable def mulByNXHom : Γ(curveE E, XE E) →+* Γ(curveE E, VNE E N) :=
  (sectionsVNEEquiv E N).symm.toRingHom.comp
    ((mulByNHom E N).comp (sectionsXEAlgEquiv E).toRingEquiv.toRingHom)

/-- `[N] : E ∖ E[N] → E ∖ {O}` over `K`, on the affine opens `VNE E N`, `XE E` of `curveE E`. -/
noncomputable abbrev mulByNXMor : Spec Γ(curveE E, VNE E N) ⟶ Spec Γ(curveE E, XE E) :=
  Spec.map (CommRingCat.ofHom (mulByNXHom E N))

omit [CharZero K] [NeZero N] [E.IsElliptic] in
lemma isFiniteEtale_specMap_ringEquivN {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
  haveI : IsIso (CommRingCat.ofHom e.toRingHom) := (RingEquiv.toCommRingCatIso e).isIso_hom
  MorphismProperty.of_isIso @IsFiniteEtale _

/-- **`[N] : E ∖ E[N] → E ∖ {O}` is finite étale**, as a morphism of affine opens of
`curveE E`. -/
instance isFiniteEtale_mulByNXMor : IsFiniteEtale (mulByNXMor E N) := by
  have heq : mulByNXMor E N =
      Spec.map (CommRingCat.ofHom (sectionsVNEEquiv E N).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (mulByNHom E N)) ≫
          Spec.map (CommRingCat.ofHom (sectionsXEAlgEquiv E).toRingEquiv.toRingHom) := by
    simp only [mulByNXMor, mulByNXHom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [heq]
  have h1 := isFiniteEtale_specMap_ringEquivN (sectionsVNEEquiv E N).symm
  have h3 := isFiniteEtale_specMap_ringEquivN (sectionsXEAlgEquiv E).toRingEquiv
  have h2 := isFiniteEtale_spec_mulByNHom E N
  exact MorphismProperty.comp_mem @IsFiniteEtale _ _ h1 (MorphismProperty.comp_mem _ _ _ h2 h3)

end Scheme

end CurvesJacobian.Cusp
