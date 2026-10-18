/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticPunctured
import CurvesJacobian.Cusp.EllipticBaseChange
import CurvesJacobian.Cusp.BelyiDataExists
import Belyi.P1.AffineMarkedPoint
import Belyi.P1.PolynomialMap

/-!
# IUT's once-punctured elliptic curve is of strictly Belyi type

Let `E` be an elliptic curve over a number field `K` and `X = E ∖ {O}` (`hypCurveX E`). Over a
number field `M ⊇ K` containing the roots `e₁, e₂, e₃` of `g = 4x³ + b₂x² + 2b₄x + b₆` (the
`x`-coordinates of the points of order two), we construct the input of [AbsTopII] Example 3.6
(ii) (`CurvesJacobian.Cusp.StrictlyBelyiInput`):

* `V = E_M ∖ E_M[2]` (`hypCurveV (E.map (algebraMap K M))`);
* `V → X`: `[2] : E_M ∖ E[2] → E_M ∖ {O}` followed by `E_M ∖ {O} → E ∖ {O}`
  (`K[E] → M[E] → M[E][1/ψ]`, `dupHom`, `finiteEtale_coordinateRing_map`);
* `V → Q ⊆ ℙ¹_M ∖ {0, 1, ∞}`: the double cover `x` composed with the Möbius transformation
  `t = (x - e₁)/(e₂ - e₁)`, `Q = 𝔸¹ ∖ {0, 1, λ}`, `λ = (e₃ - e₁)/(e₂ - e₁)`.

**Main results**: `CurvesJacobian.Cusp.strictlyBelyiInputE` and
`CurvesJacobian.Cusp.exists_belyiCandidate_oncePunctured` ([AbsTopII] Cor 3.7 (a) for `X`).
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian
open WeierstrassCurve.Affine.CoordinateRing

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-! ### The roots of `g` are distinct -/

section Roots

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- `g = Ψ₂Sq` has no double root: at a double root `e`, the point `(e, -(a₁e + a₃)/2)` would be
a singular point of `E`. -/
lemma not_double_root_Ψ₂Sq {e : k} (h0 : E.Ψ₂Sq.eval e = 0)
    (h1 : (derivative E.Ψ₂Sq).eval e = 0) : False := by
  set y := -(E.a₁ * e + E.a₃) / 2
  have hy : 2 * y + E.a₁ * e + E.a₃ = 0 := by simp only [y]; ring
  rw [WeierstrassCurve.Ψ₂Sq] at h0 h1
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, derivative_add, derivative_mul,
    derivative_C, derivative_X_pow, derivative_X, zero_mul, zero_add, mul_one,
    Nat.cast_ofNat, add_zero] at h0 h1
  have heq : E.toAffine.Equation e y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₆, WeierstrassCurve.b₄] at h0
    linear_combination (1 / 4 : k) * (2 * y + E.a₁ * e + E.a₃ + 0) * hy - (1 / 4 : k) * h0
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular.1 heq)
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  rcases hns.2 with h | h
  · apply h
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄] at h1
    linear_combination (-1 / 4 : k) * h1 + (E.a₁ / 2) * hy
  · exact h hy

variable {E} {e₁ e₂ e₃ : k} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

include he in
lemma roots_ne₁₂ : e₁ ≠ e₂ := by
  rintro rfl
  refine not_double_root_Ψ₂Sq E (e := e₁) ?_ ?_ <;> rw [he] <;>
    simp [derivative_mul]

include he in
lemma roots_ne₁₃ : e₁ ≠ e₃ := by
  rintro rfl
  refine not_double_root_Ψ₂Sq E (e := e₁) ?_ ?_ <;> rw [he] <;>
    simp [derivative_mul]

include he in
lemma roots_ne₂₃ : e₂ ≠ e₃ := by
  rintro rfl
  refine not_double_root_Ψ₂Sq E (e := e₂) ?_ ?_ <;> rw [he] <;>
    simp [derivative_mul]

end Roots

/-! ### The Möbius transformation `t = (x - e₁)/(e₂ - e₁)` -/

section Mobius

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {e₁ e₂ e₃ : k} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

variable (e₁ e₂ e₃) in
/-- `λ = (e₃ - e₁)/(e₂ - e₁)`. -/
def lamE : k := (e₃ - e₁) / (e₂ - e₁)

variable (e₁ e₂ e₃) in
/-- `t (t - 1) (t - λ)`. -/
def hpolE : k[X] := X * (X - 1) * (X - C (lamE e₁ e₂ e₃))

variable (e₁ e₂ e₃) in
/-- `k[t, 1/(t(t-1)(t-λ))]`: the ring of `ℙ¹ ∖ {0, 1, λ, ∞}`. -/
abbrev QRing : Type u := Localization.Away (hpolE e₁ e₂ e₃)

variable (e₁ e₂) in
/-- `t ↦ (x - e₁)/(e₂ - e₁)`. -/
def mob : k[X] →ₐ[k] k[X] := aeval (C (e₂ - e₁)⁻¹ * (X - C e₁))

variable (e₁ e₂) in
/-- `x ↦ e₁ + (e₂ - e₁) t`. -/
def mobInv : k[X] →ₐ[k] k[X] := aeval (C e₁ + C (e₂ - e₁) * X)

include he in
lemma mobInv_comp_mob : (mobInv e₁ e₂).comp (mob e₁ e₂) = AlgHom.id k k[X] := by
  have h := sub_ne_zero.2 (roots_ne₁₂ he).symm
  refine Polynomial.algHom_ext ?_
  simp only [mob, mobInv, AlgHom.coe_comp, Function.comp_apply, aeval_X, map_mul, map_sub,
    aeval_C, AlgHom.coe_id, id_eq, algebraMap_eq]
  apply Polynomial.funext
  intro x
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X]
  field_simp
  ring

include he in
lemma mob_comp_mobInv : (mob e₁ e₂).comp (mobInv e₁ e₂) = AlgHom.id k k[X] := by
  have h := sub_ne_zero.2 (roots_ne₁₂ he).symm
  refine Polynomial.algHom_ext ?_
  simp only [mob, mobInv, AlgHom.coe_comp, Function.comp_apply, aeval_X, map_mul, map_add,
    map_sub, aeval_C, AlgHom.coe_id, id_eq, algebraMap_eq]
  apply Polynomial.funext
  intro x
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X]
  field_simp
  ring

include he in
/-- `mob (t (t - 1) (t - λ)) · 4 (e₂ - e₁)³ = g`. -/
lemma mob_hpolE : mob e₁ e₂ (hpolE e₁ e₂ e₃) * C (4 * (e₂ - e₁) ^ 3) = gE E := by
  have h := sub_ne_zero.2 (roots_ne₁₂ he).symm
  rw [gE, he]
  apply Polynomial.funext
  intro x
  simp only [hpolE, lamE, mob, map_mul, map_sub, aeval_X, aeval_C, algebraMap_eq, map_one,
    eval_mul, eval_sub, eval_C, eval_X, eval_one]
  field_simp
  ring

include he in
lemma mobInv_gE : mobInv e₁ e₂ (gE E) = hpolE e₁ e₂ e₃ * C (4 * (e₂ - e₁) ^ 3) := by
  rw [← mob_hpolE he, map_mul, ← AlgHom.comp_apply, mobInv_comp_mob he, AlgHom.id_apply, mobInv,
    aeval_C, algebraMap_eq]

include he in
lemma isUnit_C_four_mul : IsUnit (C (4 * (e₂ - e₁) ^ 3) : k[X]) :=
  isUnit_C.2 (Ne.isUnit (mul_ne_zero (by norm_num) (pow_ne_zero 3
    (sub_ne_zero.2 (roots_ne₁₂ he).symm))))

include he in
/-- `k[t, 1/h] → k[x, 1/g]`, `t ↦ (x - e₁)/(e₂ - e₁)`. -/
def mobLoc : QRing e₁ e₂ e₃ →+* lineRingE E :=
  IsLocalization.Away.lift (hpolE e₁ e₂ e₃)
    (g := (algebraMap k[X] (lineRingE E)).comp (mob e₁ e₂).toRingHom) (by
      have hg := IsLocalization.Away.algebraMap_isUnit (S := lineRingE E) (gE E)
      have h2 : algebraMap k[X] (lineRingE E) (mob e₁ e₂ (hpolE e₁ e₂ e₃)) *
          algebraMap k[X] (lineRingE E) (C (4 * (e₂ - e₁) ^ 3)) =
            algebraMap k[X] (lineRingE E) (gE E) := by
        rw [← map_mul, mob_hpolE he]
      rw [← h2] at hg
      exact isUnit_of_mul_isUnit_left hg)

include he in
/-- `k[x, 1/g] → k[t, 1/h]`, `x ↦ e₁ + (e₂ - e₁) t`. -/
def mobLocInv : lineRingE E →+* QRing e₁ e₂ e₃ :=
  IsLocalization.Away.lift (gE E)
    (g := (algebraMap k[X] (QRing e₁ e₂ e₃)).comp (mobInv e₁ e₂).toRingHom) (by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [mobInv_gE he, map_mul]
      exact (IsLocalization.Away.algebraMap_isUnit _).mul ((isUnit_C_four_mul he).map _))

lemma mobLoc_algebraMap (p : k[X]) :
    mobLoc he (algebraMap k[X] (QRing e₁ e₂ e₃) p) = algebraMap k[X] (lineRingE E) (mob e₁ e₂ p) :=
  IsLocalization.Away.lift_eq _ _ _

lemma mobLocInv_algebraMap (p : k[X]) :
    mobLocInv he (algebraMap k[X] (lineRingE E) p) =
      algebraMap k[X] (QRing e₁ e₂ e₃) (mobInv e₁ e₂ p) :=
  IsLocalization.Away.lift_eq _ _ _

/-- **The Möbius transformation identifies `ℙ¹ ∖ {0, 1, λ, ∞}` with `𝔸¹ ∖ {g = 0}`.** -/
def mobEquiv : QRing e₁ e₂ e₃ ≃+* lineRingE E :=
  RingEquiv.ofRingHom (mobLoc he) (mobLocInv he)
    (IsLocalization.ringHom_ext (Submonoid.powers (gE E)) (RingHom.ext fun p ↦ by
      simp only [RingHom.comp_apply, RingHom.id_apply, mobLocInv_algebraMap, mobLoc_algebraMap]
      rw [← AlgHom.comp_apply, mob_comp_mobInv he, AlgHom.id_apply]))
    (IsLocalization.ringHom_ext (Submonoid.powers (hpolE e₁ e₂ e₃)) (RingHom.ext fun p ↦ by
      simp only [RingHom.comp_apply, RingHom.id_apply, mobLocInv_algebraMap, mobLoc_algebraMap]
      rw [← AlgHom.comp_apply, mobInv_comp_mob he, AlgHom.id_apply]))

lemma mobEquiv_apply (q : QRing e₁ e₂ e₃) : mobEquiv he q = mobLoc he q := rfl

lemma mobLoc_algebraMap_K (c : k) :
    mobLoc he (algebraMap k (QRing e₁ e₂ e₃) c) = algebraMap k (lineRingE E) c := by
  rw [IsScalarTower.algebraMap_apply k k[X] (QRing e₁ e₂ e₃), mobLoc_algebraMap,
    IsScalarTower.algebraMap_apply k k[X] (lineRingE E)]
  simp [mob]

end Mobius

/-! ### The open `Q = ℙ¹ ∖ {0, 1, λ, ∞}` -/

section QOpen

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Membership in the ideal of an `R`-valued point of the affine chart.** -/
lemma mem_point_iff (k : Type u) [Field k] {R : Type u} [CommRing R] [Algebra k R] (t : R)
    (z : Spec (.of R)) {n : ℕ} {f : MvPolynomial (Fin 2) k} (hf : f ∈ P1Grading k n) :
    f ∈ ((point k t).base z).asHomogeneousIdeal.toIdeal ↔
      MvPolynomial.aeval ![t, 1] f ∈ z.asIdeal := by
  have hf' : f ∈ P1Grading k (n • 1) := by simpa using hf
  have hpt : (point k t).base z = (Proj.awayι (P1Grading k) (MvPolynomial.X 1)
      (X_mem_P1Grading k 1) one_pos).base ((Spec.map (CommRingCat.ofHom (awayEval k t))).base z) :=
    rfl
  rw [hpt, HomogeneousIdeal.mem_iff,
    ← Proj.awayMk_mem_iff_mem_awayι (P1Grading k) (X_mem_P1Grading k 1) one_pos _ n f hf']
  change _ ∈ (PrimeSpectrum.comap (awayEval k t) z).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, awayEval_mk]

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {e₁ e₂ e₃ : k} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

variable (e₁ e₂ e₃) in
/-- `ℙ¹ ∖ {0, 1, λ, ∞} → ℙ¹`. -/
def qChart : Spec (.of (QRing e₁ e₂ e₃)) ⟶ P1 k :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (QRing e₁ e₂ e₃))) ≫ lineChart k

instance : IsOpenImmersion (qChart e₁ e₂ e₃) := by
  unfold qChart
  infer_instance

omit [CharZero k] in
lemma qChart_eq_point :
    qChart e₁ e₂ e₃ = point k (algebraMap k[X] (QRing e₁ e₂ e₃) X) := by
  unfold qChart lineChart
  exact SpecMap_comp_point _ (fun c ↦ (IsScalarTower.algebraMap_apply _ _ _ c).symm) _

variable (e₁ e₂ e₃) in
/-- The open `Q = ℙ¹ ∖ {0, 1, λ, ∞}`. -/
def QE : (P1 k).Opens := (qChart e₁ e₂ e₃).opensRange

omit [CharZero k] in
lemma isUnit_T : IsUnit (algebraMap k[X] (QRing e₁ e₂ e₃) X) := by
  have h : IsUnit (algebraMap k[X] (QRing e₁ e₂ e₃) (X * (X - 1) * (X - C (lamE e₁ e₂ e₃)))) :=
    IsLocalization.Away.algebraMap_isUnit (S := QRing e₁ e₂ e₃) (hpolE e₁ e₂ e₃)
  rw [map_mul, map_mul] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)

omit [CharZero k] in
lemma isUnit_T_sub_one : IsUnit (algebraMap k[X] (QRing e₁ e₂ e₃) X - 1) := by
  have h : IsUnit (algebraMap k[X] (QRing e₁ e₂ e₃) (X * (X - 1) * (X - C (lamE e₁ e₂ e₃)))) :=
    IsLocalization.Away.algebraMap_isUnit (S := QRing e₁ e₂ e₃) (hpolE e₁ e₂ e₃)
  rw [map_mul, map_mul, map_sub, map_one] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)

omit [CharZero k] in
/-- **`Q ⊆ ℙ¹ ∖ {0, 1, ∞}`.** -/
lemma QE_le_puncturedLine : QE e₁ e₂ e₃ ≤ puncturedLine k := by
  rintro _ ⟨z, rfl⟩
  have hz : ∀ a : QRing e₁ e₂ e₃, IsUnit a → a ∉ z.asIdeal := fun a ha hm ↦
    z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm ha)
  change (qChart e₁ e₂ e₃).base z ∉ markedPoints k
  simp only [markedPoints, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈
        ((qChart e₁ e₂ e₃).base z).asHomogeneousIdeal.toIdeal := by
      rw [h, P1.zero, mkPoint_asIdeal]
      exact Ideal.mem_span_singleton_self _
    rw [qChart_eq_point, mem_point_iff k _ z (X_mem_P1Grading k 0)] at hX0
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at hX0
    exact hz _ isUnit_T hX0
  · have hX : (MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈
        ((qChart e₁ e₂ e₃).base z).asHomogeneousIdeal.toIdeal := by
      rw [h, P1.one, mkPoint_asIdeal]
      exact Ideal.mem_span_singleton_self _
    rw [qChart_eq_point, mem_point_iff k _ z ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      ((MvPolynomial.isHomogeneous_X k 0).sub (MvPolynomial.isHomogeneous_X k 1)))] at hX
    simp only [map_sub, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hX
    exact hz _ isUnit_T_sub_one hX
  · apply infty_not_mem_range_lineChart k
    rw [← h]
    exact ⟨_, rfl⟩

omit [CharZero k] in
lemma hpolE_ne_zero : hpolE e₁ e₂ e₃ ≠ 0 :=
  mul_ne_zero (mul_ne_zero X_ne_zero (by simpa using X_sub_C_ne_zero (1 : k)))
    (X_sub_C_ne_zero _)

instance : IsDomain (QRing e₁ e₂ e₃) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hpolE_ne_zero)

omit [CharZero k] in
lemma QE_nonempty : ((QE e₁ e₂ e₃ : (P1 k).Opens) : Set (P1 k)).Nonempty := by
  obtain ⟨y⟩ : Nonempty (Spec (.of (QRing e₁ e₂ e₃))) := inferInstance
  exact ⟨_, y, rfl⟩

omit [CharZero k] in
lemma qChart_le : (⊤ : (Spec (.of (QRing e₁ e₂ e₃))).Opens) ≤ qChart e₁ e₂ e₃ ⁻¹ᵁ QE e₁ e₂ e₃ :=
  fun y _ ↦ ⟨y, rfl⟩

instance : IsIso ((qChart e₁ e₂ e₃).appLE (QE e₁ e₂ e₃) ⊤ qChart_le) :=
  isIso_appLE_of_isOpenImmersion _ (isAffineOpen_opensRange _) rfl _

/-- `Γ(ℙ¹, Q) ≅ k[t, 1/h]`. -/
def sectionsQIso : Γ(P1 k, QE e₁ e₂ e₃) ≅ .of (QRing e₁ e₂ e₃) :=
  asIso ((qChart e₁ e₂ e₃).appLE (QE e₁ e₂ e₃) ⊤ qChart_le) ≪≫ Scheme.ΓSpecIso _

instance : (Spec (.of (QRing e₁ e₂ e₃))).Over (Spec (.of k)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap k (QRing e₁ e₂ e₃)))⟩

instance : (qChart e₁ e₂ e₃).IsOver (Spec (.of k)) := by
  constructor
  change qChart e₁ e₂ e₃ ≫ (P1 k ↘ Spec (.of k)) = _
  rw [qChart, Category.assoc, lineChart_structMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]
  rfl

omit [CharZero k] in
lemma sectionsQIso_algebraMap (c : k) :
    (sectionsQIso (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)).hom (algebraMap k Γ(P1 k, QE e₁ e₂ e₃) c) =
      algebraMap k (QRing e₁ e₂ e₃) c := by
  have h := congrArg (fun f ↦ f c) (FiniteEtale.appLE_comp_algebraMap (qChart e₁ e₂ e₃) k
    (QE e₁ e₂ e₃) ⊤ qChart_le)
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  change (Scheme.ΓSpecIso _).hom ((qChart e₁ e₂ e₃).appLE _ ⊤ _ _) = _
  rw [h]
  change (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom
    (algebraMap k (QRing e₁ e₂ e₃)))).appTop ((Scheme.ΓSpecIso (.of k)).inv c)) = _
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]
  rfl

end QOpen

/-! ### `E ∖ E[2] → Q` -/

section CoverQ

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {e₁ e₂ e₃ : k} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

/-- `Γ(ℙ¹, Q) → Γ(E ∖ E[2])`: `t ↦ (x - e₁)/(e₂ - e₁)`. -/
def coverQHom : Γ(P1 k, QE e₁ e₂ e₃) →+* Γ(curveE E, VE E) :=
  (sectionsVEEquiv E).symm.toRingHom.comp ((algebraMap (lineRingE E) (coverRingE E)).comp
    ((mobEquiv he).toRingHom.comp sectionsQIso.hom.hom))

lemma coverQHom_algebraMap (c : k) :
    coverQHom he (algebraMap k _ c) = algebraMap k Γ(curveE E, VE E) c := by
  simp only [coverQHom, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [sectionsQIso_algebraMap, mobEquiv_apply, mobLoc_algebraMap_K,
    ← IsScalarTower.algebraMap_apply, RingEquiv.symm_apply_eq, sectionsVEEquiv_algebraMap]

/-- **`x` followed by the Möbius map: `E ∖ E[2] → Q` is finite étale.** -/
lemma isFiniteEtale_coverQ : IsFiniteEtale (Spec.map (CommRingCat.ofHom (coverQHom he))) := by
  have h : CommRingCat.ofHom (coverQHom he) = sectionsQIso.hom ≫
      CommRingCat.ofHom (mobEquiv he).toRingHom ≫
        CommRingCat.ofHom (algebraMap (lineRingE E) (coverRingE E)) ≫
          CommRingCat.ofHom (sectionsVEEquiv E).symm.toRingHom := rfl
  haveI := isFiniteEtale_spec E
  haveI : IsIso (CommRingCat.ofHom (mobEquiv he).toRingHom) :=
    (RingEquiv.toCommRingCatIso (mobEquiv he)).isIso_hom
  haveI : IsIso (CommRingCat.ofHom (sectionsVEEquiv E).symm.toRingHom) :=
    (RingEquiv.toCommRingCatIso (sectionsVEEquiv E).symm).isIso_hom
  have hi : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) [IsIso f], IsFiniteEtale (Spec.map f) :=
    fun f _ ↦ MorphismProperty.of_isIso @IsFiniteEtale _
  haveI := hi (CommRingCat.ofHom (mobEquiv he).toRingHom)
  haveI := hi (CommRingCat.ofHom (sectionsVEEquiv E).symm.toRingHom)
  haveI := hi (sectionsQIso (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)).hom
  rw [h, Spec.map_comp, Spec.map_comp, Spec.map_comp]
  infer_instance

end CoverQ

/-! ### The strictly Belyi input for `E ∖ {O}` -/

section Input

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (M : Type u) [Field M] [NumberField M] [Algebra K M]

local notation "E'" => E.map (algebraMap K M)

/-- `K[E] → M[E]`. -/
abbrev coordMapM : E.toAffine.CoordinateRing →+* (E').toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (algebraMap K M)

/-- `V → X`: `E_M ∖ E[2] ≅ Spec M[E][1/ψ] →[2] Spec M[E] → Spec K[E] ≅ E ∖ {O}`. -/
def coverXMor : Spec Γ(curveE E', VE E') ⟶ Spec Γ(curveE E, XE E) :=
  Spec.map (CommRingCat.ofHom (sectionsVEEquiv E').symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (dupHom E')) ≫ Spec.map (CommRingCat.ofHom (coordMapM E M)) ≫
      Spec.map (CommRingCat.ofHom (sectionsXEAlgEquiv E).toRingEquiv.toRingHom)

lemma isFiniteEtale_specMap_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
  haveI : IsIso (CommRingCat.ofHom e.toRingHom) := (RingEquiv.toCommRingCatIso e).isIso_hom
  MorphismProperty.of_isIso @IsFiniteEtale _

lemma isFiniteEtale_coverXMor : IsFiniteEtale (coverXMor E M) := by
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  have h1 := isFiniteEtale_specMap_of_ringEquiv (sectionsVEEquiv E').symm
  have h4 := isFiniteEtale_specMap_of_ringEquiv (sectionsXEAlgEquiv E).toRingEquiv
  have h2 := isFiniteEtale_spec_dupHom E'
  have h3 : IsFiniteEtale (Spec.map (CommRingCat.ofHom (coordMapM E M))) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom]
    exact finiteEtale_coordinateRing_map E M
  exact MorphismProperty.comp_mem @IsFiniteEtale _ _ h1
    (MorphismProperty.comp_mem _ _ _ h2 (MorphismProperty.comp_mem _ _ _ h3 h4))

lemma coverX_algebraMap (c : K) :
    (sectionsVEEquiv E').symm (dupHom E' (coordMapM E M
      (sectionsXEAlgEquiv E (algebraMap K _ c)))) =
        algebraMap M Γ(curveE E', VE E') (algebraMap K M c) := by
  rw [AlgEquiv.commutes, RingEquiv.symm_apply_eq, sectionsVEEquiv_algebraMap, ← dupHom_algebraMap]
  congr 1
  rw [IsScalarTower.algebraMap_apply K K[X] E.toAffine.CoordinateRing,
    IsScalarTower.algebraMap_apply M M[X] (E').toAffine.CoordinateRing]
  simp [coordMapM, WeierstrassCurve.Affine.CoordinateRing.map, AdjoinRoot.algebraMap_eq]

variable {M} {e₁ e₂ e₃ : M}
  (he : (E.map (algebraMap K M)).Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

lemma coverXMor_comp :
    coverXMor E M ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, XE E))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(curveE E', VE E'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
  simp only [coverXMor, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun c ↦ coverX_algebraMap E M c

include he in
omit [NumberField K] in
lemma coverQ_comp : Spec.map (CommRingCat.ofHom (coverQHom he)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(P1 M, QE e₁ e₂ e₃))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(curveE E', VE E'))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun c ↦ coverQHom_algebraMap he c

/-- **[AbsTopII] Definition 3.5 / Example 3.6 (ii) for IUT's `X = E ∖ {O}`**: over a number field
`M ⊇ K` containing the `x`-coordinates `e₁, e₂, e₃` of the points of order two, `V = E_M ∖ E[2]`
with `[2] : V → X` and `V → Q = ℙ¹ ∖ {0, 1, λ, ∞}`, `t = (x - e₁)/(e₂ - e₁)`. -/
def strictlyBelyiInputE : StrictlyBelyiInput (hypCurveX E) M where
  CV := hypCurveV E'
  hcV := (compl_XE_nonempty E').mono (Set.compl_subset_compl.2 (VE_le_XE E'))
  FV := coverXMor E M
  finFV := isFiniteEtale_coverXMor E M
  hFV := by
    change coverXMor E M ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(curveE E, XE E))) = _
    simp only [coverXMor, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ coverX_algebraMap E M c
  Q := QE e₁ e₂ e₃
  hQ := QE_le_puncturedLine
  hQne := QE_nonempty
  FQ := Spec.map (CommRingCat.ofHom (coverQHom he))
  finFQ := isFiniteEtale_coverQ he
  hFQ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ coverQHom_algebraMap he c

end Input

/-! ### Existence, and [AbsTopII] Corollary 3.7 (a) for `E ∖ {O}` -/

section Exists

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]

omit [E.IsElliptic] in
/-- Over the splitting field of `g`, `g = 4 (x - e₁)(x - e₂)(x - e₃)`. -/
lemma exists_roots_splittingField : ∃ e₁ e₂ e₃ : E.Ψ₂Sq.SplittingField,
    (E.map (algebraMap K E.Ψ₂Sq.SplittingField)).Ψ₂Sq =
      C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)) := by
  set L := E.Ψ₂Sq.SplittingField
  have hs := SplittingField.splits E.Ψ₂Sq
  have h4 : (4 : L) ≠ 0 := by norm_num
  rw [WeierstrassCurve.map_Ψ₂Sq]
  have hdeg : (E.Ψ₂Sq.map (algebraMap K L)).natDegree = 3 := by
    rw [← WeierstrassCurve.map_Ψ₂Sq]; exact WeierstrassCurve.natDegree_Ψ₂Sq _ h4
  have hlc : (E.Ψ₂Sq.map (algebraMap K L)).leadingCoeff = 4 := by
    rw [← WeierstrassCurve.map_Ψ₂Sq]; exact WeierstrassCurve.leadingCoeff_Ψ₂Sq _ h4
  have hcard : (E.Ψ₂Sq.map (algebraMap K L)).roots.card = 3 := by
    rw [← hdeg]; exact splits_iff_card_roots.1 hs
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.1 hcard
  refine ⟨a, b, c, ?_⟩
  conv_lhs => rw [hs.eq_prod_roots, hlc, habc]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
    Multiset.prod_singleton, map_ofNat]
  ring

instance numberField_splittingField : NumberField E.Ψ₂Sq.SplittingField :=
  { to_charZero := charZero_of_injective_algebraMap (algebraMap K _).injective
    to_finiteDimensional := Module.Finite.trans K _ }

/-- **IUT's once-punctured elliptic curve `X = E ∖ {O}` is of strictly Belyi type**
([AbsTopII] Definition 3.5), with the input of Example 3.6 (ii) over the splitting field of the
two-torsion cubic. -/
theorem nonempty_strictlyBelyiInput :
    Nonempty (StrictlyBelyiInput (hypCurveX E) E.Ψ₂Sq.SplittingField) := by
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_roots_splittingField E
  exact ⟨strictlyBelyiInputE E he⟩

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {M : Type u} [Field M] [NumberField M] [Algebra K M] {e₁ e₂ e₃ : M}
  (he : (E.map (algebraMap K M)).Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))
  (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic M Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

open AlgebraicGeometry.FiniteEtale IntermediateField in
include he in
/-- **[AbsTopII] Corollary 3.7 (a) for IUT's `X = E ∖ {O}`**: for every nonempty open
`U_X ⊆ X` there are Belyi data whose run of fillings passes through `U = V ×_X U_X`, and the
corresponding candidate of the Belyi chain is a Belyi cusp. -/
theorem exists_belyiCandidate_oncePunctured (UX : (hypCurveX E).Xbar.Opens)
    (hUX : UX ≤ (hypCurveX E).U) (hUXne : (UX : Set (hypCurveX E).Xbar).Nonempty) :
    ∃ (M' : FinSub M Ω) (D : BelyiData (M := M'.1) (hypCurveX E)) (m : ℕ) (hm : m ≤ D.r)
      (hVa : IsAffineOpen (D.UW (Fin.last D.r))),
      D.UW ⟨D.r - m, by omega⟩ = hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ
        ((isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E)).fromSpec ⁻¹ᵁ UX)) ∧
      PiChain.belyiCandidate (D.isBelyiType Ω (compl_XE_nonempty E))
        (D.terminalIso Ω (compl_XE_nonempty E)) m hm ∈
          belyiCusp (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)) := by
  obtain ⟨M', D, m, hm, hVa, h1, h2, -⟩ := exists_belyiCandidate Ω (compl_XE_nonempty E)
    (strictlyBelyiInputE E he) UX hUX hUXne
  exact ⟨M', D, m, hm, hVa, h1, h2⟩

end Exists

end CurvesJacobian.Cusp
