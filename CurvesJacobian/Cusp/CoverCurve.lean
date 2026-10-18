/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverNormalization
import CurvesJacobian.Scheme.GeomIntegralAlgClosed
import Belyi.Converse.Pi1InvarianceCurve
import Belyi.Curve.SmoothStalk
import Oka.AlgebraicGeometry.SmoothLocus
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Etale.Kaehler

/-!
# The smooth compactification of a finite étale cover of a curve

Let `k` be a field of characteristic zero, `X̄` a curve over `k` (belyi's `IsCurveOver`:
smooth of relative dimension `1`, proper, geometrically integral), `U ⊆ X̄` a nonempty open and
`p : Y ⟶ U` finite étale with `Y` integral. Let `N` be the relative normalisation of `X̄` in `Y`
(along `p ≫ U.ι`), with `q : N ⟶ X̄` and structure morphism `s = q ≫ (X̄ ↘ Spec k)`. We prove:

* `CurvesJacobian.Cusp.isProper_normalization`: `s` is proper;
* `CurvesJacobian.Cusp.smooth_normalization`: `s` is smooth;
* `CurvesJacobian.Cusp.smoothOfRelativeDimension_normalization`: `s` is smooth of relative
  dimension `1`;
* `CurvesJacobian.Cusp.isCurveOver_normalization`: if `k` is algebraically closed, `N` (over
  `Spec k` via `s`, `CurvesJacobian.Cusp.normalizationOver`) is a curve over `k`.

## Proof

* `q` is finite (`CurvesJacobian.Cusp.isFinite_fromNormalization`), hence proper, and the
  structure morphism of `X̄` is proper.
* `s` is locally of finite presentation (finite type over a noetherian base). For smoothness we
  use oka's criterion `Scheme.Hom.mem_smoothLocus_of_ringKrullDim_le_one` (characteristic zero):
  `Γ(N, V)` is an integrally closed domain for affine `V`
  (`CurvesJacobian.Cusp.isIntegrallyClosed_normalization`), and the stalks of `N` have dimension
  `≤ 1`: over an affine `W ⊆ X̄`, `Γ(N, q⁻¹ W)` is integral over `Γ(X̄, W)`, so by
  incomparability the height of a prime of `Γ(N, q⁻¹ W)` is at most the height of its
  contraction, which is the dimension of a stalk of `X̄`, hence `≤ 1`
  (`CurvesJacobian.Cusp.ringKrullDim_stalk_le_of_isFinite`).
* Relative dimension: on every standard-smooth affine chart `V` of the integral scheme `N`, the
  rank of the free module `Ω[Γ(N, V)⁄k]` equals `dim_K Ω[K⁄k]` for the function field `K` of `N`
  (`Ω` commutes with localisation). Hence it is the same on all charts
  (`CurvesJacobian.Cusp.isStandardSmoothOfRelativeDimension_appLE_of_appLE`), and on a chart
  inside the open `Y ⊆ N` (`toNormalization` is an open immersion, base change of `U.ι`) it is
  `1`, as `Y ⟶ Spec k` is étale followed by an open immersion and a curve.
* Over an algebraically closed field, an integral scheme locally of finite type is
  geometrically integral (`CurvesJacobian.geometricallyIntegral_of_isAlgClosed`).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi

universe u

namespace CurvesJacobian.Cusp

/-! ### Kähler differentials and fraction fields -/

/-- If `Ω[B⁄R]` is free over the domain `B` with fraction field `K`, then `Ω[K⁄R]` has the same
rank over `K`. -/
theorem rank_kaehlerDifferential_fractionRing {R B K : Type u} [CommRing R] [CommRing B]
    [IsDomain B] [Field K] [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K]
    [IsFractionRing B K] [Module.Free B Ω[B⁄R]] :
    Module.rank K Ω[K⁄R] = Module.rank B Ω[B⁄R] := by
  have := Module.lift_rank_of_isLocalizedModule_of_free K (nonZeroDivisors B)
    (KaehlerDifferential.map R R B K)
  simpa only [Cardinal.lift_id] using this

/-! ### Relative dimension on an integral scheme -/

section Charts

variable {N S : Scheme.{u}} [IsIntegral N] (s : N ⟶ S) (U : S.Opens)

/-- The maps `Γ(S, U) ⟶ Γ(N, V) ⟶ K(N)` compose to the germ of `Γ(S, U) ⟶ Γ(N, s⁻¹ U)`. -/
lemma appLE_germToFunctionField {V : N.Opens} [Nonempty V] (e : V ≤ s ⁻¹ᵁ U)
    [Nonempty (s ⁻¹ᵁ U)] :
    s.appLE U V e ≫ N.germToFunctionField V = s.app U ≫ N.germToFunctionField (s ⁻¹ᵁ U) := by
  rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-- **The relative dimension of a standard-smooth chart of an integral scheme does not depend on
the chart.** If `Γ(S, U) ⟶ Γ(N, V)` is standard smooth and `Γ(S, U) ⟶ Γ(N, V')` is standard
smooth of relative dimension `n` (`V, V'` nonempty affine), then so is `Γ(S, U) ⟶ Γ(N, V)`:
both ranks of Kähler differentials equal the rank of `Ω[K(N)⁄Γ(S, U)]`. -/
theorem isStandardSmoothOfRelativeDimension_appLE_of_appLE (n : ℕ) {V V' : N.Opens}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') [Nonempty V] [Nonempty V']
    (e : V ≤ s ⁻¹ᵁ U) (e' : V' ≤ s ⁻¹ᵁ U) (hss : (s.appLE U V e).hom.IsStandardSmooth)
    (h' : (s.appLE U V' e').hom.IsStandardSmoothOfRelativeDimension n) :
    (s.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
  haveI : Nonempty (s ⁻¹ᵁ U) := ⟨⟨_, e (Classical.arbitrary V).2⟩⟩
  letI : Algebra Γ(S, U) N.functionField :=
    (s.app U ≫ N.germToFunctionField (s ⁻¹ᵁ U)).hom.toAlgebra
  have key : ∀ (W : N.Opens) (_ : IsAffineOpen W) [Nonempty W] (eW : W ≤ s ⁻¹ᵁ U),
      (s.appLE U W eW).hom.IsStandardSmooth →
        ((s.appLE U W eW).hom.IsStandardSmoothOfRelativeDimension n ↔
          Module.rank N.functionField Ω[N.functionField⁄Γ(S, U)] = n) := by
    intro W hW _ eW hW'
    letI : Algebra Γ(S, U) Γ(N, W) := (s.appLE U W eW).hom.toAlgebra
    haveI : Algebra.IsStandardSmooth Γ(S, U) Γ(N, W) := hW'
    haveI : IsScalarTower Γ(S, U) Γ(N, W) N.functionField := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      exact congrArg CommRingCat.Hom.hom (appLE_germToFunctionField s U eW).symm
    haveI := functionField_isFractionRing_of_isAffineOpen N W hW
    rw [rank_kaehlerDifferential_fractionRing (B := Γ(N, W))]
    exact Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n
  exact (key V hV e hss).2
    ((key V' hV' e' (RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth n _ h')).1 h')

omit [IsIntegral N] in
/-- Standard-smooth charts of relative dimension `n` transfer along open immersions. -/
lemma isStandardSmoothOfRelativeDimension_appLE_image {Y : Scheme.{u}} (j : Y ⟶ N)
    [IsOpenImmersion j] (n : ℕ) {V : Y.Opens} (e : V ≤ (j ≫ s) ⁻¹ᵁ U)
    (h : ((j ≫ s).appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (s.appLE U (j ''ᵁ V) (by rintro _ ⟨y, hy, rfl⟩; exact e hy)).hom := by
  have e₂ : V ≤ j ⁻¹ᵁ j ''ᵁ V := by rw [Scheme.Hom.preimage_image_eq]
  have h₂ : j.appLE (j ''ᵁ V) V e₂ = (j.appIso V).hom := by
    rw [← cancel_epi (j.appIso V).inv, Scheme.Hom.appIso_inv_appLE, Iso.inv_hom_id]
    exact (congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_id _)
  rw [← Scheme.Hom.appLE_comp_appLE j s U (j ''ᵁ V) V
    (by rintro _ ⟨y, hy, rfl⟩; exact e hy) e₂, h₂, CommRingCat.hom_comp] at h
  exact ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_right_isIso
    _ _).mp h

lemma opens_eq_top_of_mem {K : Type u} [Field K] {W : (Spec (.of K)).Opens}
    {z : Spec (.of K)} (hz : z ∈ W) : W = ⊤ :=
  eq_top_iff.2 fun z' _ ↦ (Subsingleton.elim z z') ▸ hz

/-- **Relative dimension of a smooth integral scheme over a field.** A smooth morphism from an
integral scheme to `Spec K` which is smooth of relative dimension `n` on a nonempty open is
smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_isOpenImmersion {K : Type u} [Field K]
    (s : N ⟶ Spec (.of K)) [Smooth s] {Y : Scheme.{u}} [Nonempty Y] (j : Y ⟶ N)
    [IsOpenImmersion j] (n : ℕ) [SmoothOfRelativeDimension n (j ≫ s)] :
    SmoothOfRelativeDimension n s := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨U₀, -, V₀, hV₀, hy, e₀, h₀⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := j ≫ s) y
  obtain rfl : U₀ = ⊤ := opens_eq_top_of_mem (e₀ hy)
  have h' := isStandardSmoothOfRelativeDimension_appLE_image s ⊤ j n e₀ h₀
  haveI : Nonempty (j ''ᵁ V₀) := ⟨⟨j y, y, hy, rfl⟩⟩
  have hV' : IsAffineOpen (j ''ᵁ V₀) := hV₀.image_of_isOpenImmersion j
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U₁, hU₁, V, hV, hx, e, hss⟩ := Smooth.exists_isStandardSmooth s x
  obtain rfl : U₁ = ⊤ := opens_eq_top_of_mem (e hx)
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  exact ⟨⊤, hU₁, V, hV, hx, e,
    isStandardSmoothOfRelativeDimension_appLE_of_appLE s ⊤ n hV hV' e _ hss h'⟩

end Charts

/-! ### Dimension of stalks under finite morphisms -/

/-- **Stalk dimensions do not grow along finite morphisms to affine schemes.** If `f : X ⟶ Y` is
finite, `Y` affine and all stalks of `Y` have dimension `≤ n`, then so do all stalks of `X`
(incomparability for the integral extension `Γ(Y, ⊤) → Γ(X, ⊤)`). -/
theorem ringKrullDim_stalk_le_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [IsAffine Y] {n : WithBot ℕ∞} (h : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ n)
    (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ n := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(Y, ⊤) Γ(X, ⊤) := ⟨f.finite_appTop.to_isIntegral⟩
  let P : PrimeSpectrum Γ(X, ⊤) := (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩
  let g : PrimeSpectrum Γ(X, ⊤) → PrimeSpectrum Γ(Y, ⊤) := fun Q ↦
    ⟨Q.asIdeal.comap (algebraMap Γ(Y, ⊤) Γ(X, ⊤)), inferInstance⟩
  have hg : StrictMono g := fun Q₁ Q₂ hQ ↦ by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hQ ⊢
    exact Ideal.IsIntegral.comap_lt_comap hQ
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  haveI := (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  have hY := h ((isAffineOpen_top Y).fromSpec (g P))
  have hloc := (isAffineOpen_top Y).isLocalization_stalk' (g P) trivial
  rw [@IsLocalization.AtPrime.ringKrullDim_eq_height _ _ (g P).asIdeal _ _ _
    (TopCat.Presheaf.algebra_section_stalk Y.presheaf
      (⟨(isAffineOpen_top Y).fromSpec (g P), trivial⟩ : (⊤ : Y.Opens))) hloc] at hY
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (X.presheaf.stalk x)]
  refine le_trans ?_ hY
  rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
  exact WithBot.coe_le_coe.2 (Order.height_le_height_apply_of_strictMono g hg P)

/-! ### The normalisation of a curve in a finite étale cover -/

/-- A curve is locally noetherian. Not an instance (`k` does not occur in the conclusion); the
statements below use it to form the normalisation (which needs `p ≫ U.ι` quasi-compact). -/
lemma isLocallyNoetherian_of_isCurveOver (k : Type u) [Field k] (Xb : Scheme.{u})
    [Xb.Over (Spec (.of k))] [IsCurveOver k Xb] : IsLocallyNoetherian Xb :=
  LocallyOfFiniteType.isLocallyNoetherian (Xb ↘ Spec (.of k))

section Curve

variable {k : Type u} [Field k] [CharZero k] {Xb : Scheme.{u}} [Xb.Over (Spec (.of k))]
  [IsCurveOver k Xb] {U : Xb.Opens} (hU : (U : Set Xb).Nonempty) {Y : Scheme.{u}}
  (p : Y ⟶ U) [IsFinite p] [Etale p]

include k in
/-- The rings of sections of a curve over affine opens are integrally closed (the hypothesis
`hX` of `CurvesJacobian.Cusp.isFinite_fromNormalization`). -/
lemma isIntegrallyClosed_of_isCurveOver (W : Xb.Opens) (hW : IsAffineOpen W) :
    IsIntegrallyClosed Γ(Xb, W) := by
  haveI := IsCurveOver.isIntegral k Xb
  rcases isEmpty_or_nonempty W with hW0 | hW0
  · obtain rfl : W = ⊥ := TopologicalSpace.Opens.ext
      (Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ hW0.false ⟨x, hx⟩)
    haveI := (algebraMap Γ(Xb, ⊥) (FractionRing Γ(Xb, ⊥))).codomain_trivial
    exact (isIntegrallyClosed_iff (FractionRing Γ(Xb, ⊥))).2 fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  · exact isIntegrallyClosed_of_isAffineOpen hW fun x _ ↦
      IsCurveOver.isIntegrallyClosed_stalk k Xb x

include k hU in
lemma isFinite_fromNormalization_of_isCurveOver :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    IsFinite (p ≫ U.ι).fromNormalization := by
  haveI := IsCurveOver.isIntegral k Xb
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  exact isFinite_fromNormalization (isIntegrallyClosed_of_isCurveOver (k := k)) hU p

include hU in
/-- **The normalisation is proper over `k`.** -/
theorem isProper_normalization :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    IsProper ((p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k))) := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  haveI := isFinite_fromNormalization_of_isCurveOver (k := k) hU p
  infer_instance

include hU in
/-- **The stalks of the normalisation have dimension at most one.** -/
theorem ringKrullDim_stalk_normalization_le :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    ∀ x : (p ≫ U.ι).normalization,
      ringKrullDim ((p ≫ U.ι).normalization.presheaf.stalk x) ≤ 1 := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  intro x
  haveI := IsCurveOver.isIntegral k Xb
  haveI hq := isFinite_fromNormalization_of_isCurveOver (k := k) hU p
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Xb.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((p ≫ U.ι).fromNormalization x)) isOpen_univ
  haveI : IsAffine W := hW
  haveI : IsFinite ((p ≫ U.ι).fromNormalization ∣_ W) := IsZariskiLocalAtTarget.restrict hq W
  have hWdim : ∀ y : W, ringKrullDim ((W : Scheme.{u}).presheaf.stalk y) ≤ 1 := fun y ↦ by
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.Opens.stalkIso W y).commRingCatIsoToRingEquiv]
    simpa using Ring.krullDimLE_iff.1 (krullDimLE_one_stalk_of_isCurveOver k Xb y.1)
  have hx : x ∈ (p ≫ U.ι).fromNormalization ⁻¹ᵁ W := hxW
  have := ringKrullDim_stalk_le_of_isFinite ((p ≫ U.ι).fromNormalization ∣_ W) hWdim ⟨x, hx⟩
  rwa [ringKrullDim_eq_of_ringEquiv
    (((p ≫ U.ι).fromNormalization ⁻¹ᵁ W).stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv] at this

include hU in
/-- **The normalisation is smooth over `k`.** -/
theorem smooth_normalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    Smooth ((p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k))) := by
  haveI := IsCurveOver.isIntegral k Xb
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  haveI := isFinite_fromNormalization_of_isCurveOver (k := k) hU p
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (p ≫ U.ι).normalization.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      isOpen_univ
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI := isIntegrallyClosed_normalization (isIntegrallyClosed_of_isCurveOver (k := k)) hU p hV
  exact Scheme.Hom.mem_smoothLocus_of_ringKrullDim_le_one _ hV hxV
    (ringKrullDim_stalk_normalization_le (k := k) hU p x)

omit [CharZero k] [Etale p] in
variable (k) in
/-- `toNormalization : Y ⟶ N` is an open immersion (the base change of `U.ι` along `q`). -/
theorem isOpenImmersion_toNormalization :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    IsOpenImmersion (p ≫ U.ι).toNormalization :=
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_toNormalization p).flip
    (inferInstance : IsOpenImmersion U.ι)

include hU in
/-- **The normalisation is smooth of relative dimension `1` over `k`.** -/
theorem smoothOfRelativeDimension_normalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    SmoothOfRelativeDimension 1 ((p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k))) := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  haveI := isOpenImmersion_toNormalization k p
  haveI := smooth_normalization (k := k) hU p
  have hjs : (p ≫ U.ι).toNormalization ≫ (p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k)) =
      p ≫ U.ι ≫ (Xb ↘ Spec (.of k)) := by
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, Category.assoc]
  haveI : SmoothOfRelativeDimension 1 ((p ≫ U.ι).toNormalization ≫
      (p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k))) := by
    rw [hjs]
    exact (inferInstance : SmoothOfRelativeDimension (0 + (0 + 1))
      (p ≫ U.ι ≫ (Xb ↘ Spec (.of k))))
  exact smoothOfRelativeDimension_of_isOpenImmersion _ (p ≫ U.ι).toNormalization 1

omit [CharZero k] [IsFinite p] [Etale p] in
variable (k) in
/-- The normalisation as a scheme over `Spec k`, via `q ≫ (X̄ ↘ Spec k)`. -/
noncomputable abbrev normalizationOver :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    (p ≫ U.ι).normalization.Over (Spec (.of k)) :=
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  ⟨(p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k))⟩

include hU in
/-- **The normalisation of a curve in a finite étale cover is a curve** (over an algebraically
closed field of characteristic zero). -/
theorem isCurveOver_normalization [IsAlgClosed k] [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    @IsCurveOver k _ (p ≫ U.ι).normalization (normalizationOver k p) := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  letI := normalizationOver k p
  have h₁ := smoothOfRelativeDimension_normalization (k := k) hU p
  have h₂ := isProper_normalization (k := k) hU p
  haveI := smooth_normalization (k := k) hU p
  have h₃ := geometricallyIntegral_of_isAlgClosed
    ((p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k)))
  exact { toSmoothOfRelativeDimension := h₁, toIsProper := h₂, toGeometricallyIntegral := h₃ }

end Curve

end CurvesJacobian.Cusp
