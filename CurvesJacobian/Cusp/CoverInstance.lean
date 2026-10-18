/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverComparison
import CurvesJacobian.Cusp.CoverHypCurve

/-!
# The chain object of a cover is the arithmetic `π₁` of the cover curve (MR8.3)

[AbsTopI] Definition 4.2 (`Topics in Absolute Anabelian Geometry I.txt`, l.2863–2866,
l.2980–2986) and Remark 4.2.1 (l.3083–3092): a connected finite étale cover `V ⟶ U` of a
hyperbolic curve over `K` is a hyperbolic curve over a finite extension `k'` of `K`, and the open
subgroup `π₁ᵉᵗ(V) ⊆ Π_U` is its arithmetic fundamental group. We instantiate
`CurvesJacobian.Cusp.CoverComparison` with the curve `CurvesJacobian.Cusp.coverHypCurve`.

Setting (`CurvesJacobian.Cusp.coverChainObj`): `C : HypCurve K` over a number field `K` with a
cusp, `f : V ⟶ Spec Γ(X̄, U)` connected finite étale, `η` a geometric point of `V` over the base
point of `Π_U`.

* `CurvesJacobian.Cusp.isIntegral_cover`: `V` is integral (it is the preimage of `U` in the
  normalisation `N` of `X̄` in `V`, whose ring of functions over `U` is a finite product of normal
  domains; `V` is connected).
* `CurvesJacobian.Cusp.coverCurve`: the hyperbolic curve `q⁻¹ U ⊆ N` over
  `k' = CurvesJacobian.Cusp.coverField` (the constant field of `N`), a number field;
  `CurvesJacobian.Cusp.coverCurve_cusp`: it has a cusp.
* `CurvesJacobian.Cusp.coverAlgebra`: the embedding `k' ⊆ Ω` induced by `η`
  (`Spec Ω ⟶ V ⟶ N ⟶ Spec k'`), compatible with `K ⊆ Ω` (`isScalarTower_coverAlgebra`).
* `CurvesJacobian.Cusp.coverIso`: `Spec Γ(N, q⁻¹ U) ≅ V` over `Spec K` (`coverIso_spec`), and
  `η` induces `k' ⊆ Ω` (`coverIso_point`).
* `CurvesJacobian.Cusp.coverCurvePiEquiv`: `Π_{q⁻¹ U} ≃ₜ*` the group of `coverChainObj`, with
  `toG_coverCurvePiEquiv`, `map_Delta_coverCurvePiEquiv` (`Δ` corresponds to `Δ`) and
  `map_pr_coverSubgroup_eq_range` (the image of `π₁ᵉᵗ(V)` in `G_K` is exactly `G_{k'}`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- **A connected ring that is a finite product of normal domains is a domain.** -/
theorem isDomain_of_isFiniteProductOfNormalDomains {R : Type u} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] (hR : IsFiniteProductOfNormalDomains R) : IsDomain R := by
  classical
  obtain ⟨ι, _, D, _, _, _, ⟨e⟩⟩ := hR
  haveI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  have hsub : Subsingleton ι := by
    refine ⟨fun i j ↦ by_contra fun hij ↦ ?_⟩
    let x : R := e.symm (Pi.single i 1)
    have hex : e x = Pi.single i 1 := e.apply_symm_apply _
    have hx : IsIdempotentElem x := by
      change x * x = x
      apply e.injective
      rw [map_mul, hex, ← Pi.single_mul, one_mul]
    have hcl : IsClopen (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) :=
      PrimeSpectrum.isClopen_iff.2 ⟨x, hx, rfl⟩
    rcases _root_.isClopen_iff.1 hcl with h0 | h1
    · obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff x).1
        (TopologicalSpace.Opens.ext h0)
      have := congrArg (fun y ↦ e y i) hn
      simp only [map_pow, hex, map_zero, Pi.pow_apply, Pi.single_eq_same, one_pow,
        Pi.zero_apply] at this
      exact one_ne_zero this
    · have h2 : (PrimeSpectrum.zeroLocus {x} : Set (PrimeSpectrum R)) = ∅ := by
        rw [← compl_compl (PrimeSpectrum.zeroLocus {x}),
          ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, h1, Set.compl_univ]
      have h3 : PrimeSpectrum.basicOpen (1 - x) = ⊥ := by
        refine TopologicalSpace.Opens.ext ?_
        rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem _ hx.one_sub,
          sub_sub_cancel, h2]
        rfl
      obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff _).1 h3
      have := congrArg (fun y ↦ e y j) hn
      simp only [map_pow, map_sub, map_one, hex, map_zero, Pi.pow_apply, Pi.sub_apply,
        Pi.one_apply, Pi.single_eq_of_ne' hij, sub_zero, one_pow, Pi.zero_apply] at this
      exact one_ne_zero this
  have hne : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    obtain ⟨a, b, hab⟩ := exists_pair_ne R
    exact hab (e.injective (Subsingleton.elim _ _))
  obtain ⟨i₀⟩ := hne
  haveI : Unique ι := ⟨⟨i₀⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact (e.trans (RingEquiv.piUnique D)).toMulEquiv.isDomain _

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  {V : Scheme.{u}} (f : V ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale f] [ConnectedSpace V]

/-- The cover `p : V ⟶ U` (identifying `U` with `Spec Γ(X̄, U)`). -/
def coverMap : V ⟶ C.U := f ≫ (isAffineOpen_U C hc).isoSpec.inv

instance : IsFinite (coverMap C hc f) := by
  unfold coverMap
  infer_instance

instance : Etale (coverMap C hc f) := by
  unfold coverMap
  infer_instance

include hc f in
/-- **A connected finite étale cover of `U` is integral.** -/
theorem isIntegral_cover : IsIntegral V := by
  haveI := isLocallyNoetherian_of_isCurveOver K C.Xbar
  haveI := IsCurveOver.isIntegral K C.Xbar
  let p := coverMap C hc f
  have hR := isFiniteProductOfNormalDomains_preimage
    (isIntegrallyClosed_of_isCurveOver (k := K)) C.nonempty p (isAffineOpen_U C hc) C.nonempty
  let E : V ≅ ((p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U : Scheme.{u}) :=
    (isPullback_toNormalization p).isoIsPullback _ _
      (isPullback_morphismRestrict (p ≫ C.U.ι).fromNormalization C.U).flip
  let G : Γ(V, ⊤) ≃+* Γ((p ≫ C.U.ι).normalization, (p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U) :=
    (Scheme.Γ.mapIso E.op).commRingCatIsoToRingEquiv.symm.trans
      ((p ≫ C.U.ι).fromNormalization ⁻¹ᵁ C.U).topIso.commRingCatIsoToRingEquiv
  haveI : IsAffine V := isAffine_of_isAffineHom f
  haveI : ConnectedSpace (Spec Γ(V, ⊤)) :=
    ObjectProperty.prop_of_iso (fun X : Scheme.{u} ↦ ConnectedSpace X) V.isoSpec inferInstance
  haveI : ConnectedSpace (PrimeSpectrum Γ(V, ⊤)) := ‹ConnectedSpace (Spec Γ(V, ⊤))›
  haveI : IsDomain Γ(V, ⊤) := isDomain_of_isFiniteProductOfNormalDomains (hR.of_ringEquiv G)
  exact isIntegral_of_isAffine_of_isDomain V

/-- The normalisation `N` of `X̄` in `V`. -/
def coverNorm : Scheme.{u} :=
  haveI := isLocallyNoetherian_of_isCurveOver K C.Xbar
  (coverMap C hc f ≫ C.U.ι).normalization

instance : IsIntegral (coverNorm C hc f) :=
  haveI := isLocallyNoetherian_of_isCurveOver K C.Xbar
  haveI := isIntegral_cover C hc f
  inferInstanceAs (IsIntegral (coverMap C hc f ≫ C.U.ι).normalization)

instance : (coverNorm C hc f).Over (Spec (.of K)) :=
  normalizationOver K (coverMap C hc f)

/-- `V ⟶ N`. -/
def coverToNorm : V ⟶ coverNorm C hc f :=
  haveI := isLocallyNoetherian_of_isCurveOver K C.Xbar
  (coverMap C hc f ≫ C.U.ι).toNormalization

/-- `q : N ⟶ X̄`. -/
def coverFromNorm : coverNorm C hc f ⟶ C.Xbar :=
  haveI := isLocallyNoetherian_of_isCurveOver K C.Xbar
  (coverMap C hc f ≫ C.U.ι).fromNormalization

omit [ConnectedSpace V] in
lemma coverToNorm_fromNorm :
    coverToNorm C hc f ≫ coverFromNorm C hc f = coverMap C hc f ≫ C.U.ι :=
  haveI := isLocallyNoetherian_of_isCurveOver K C.Xbar
  Scheme.Hom.toNormalization_fromNormalization _

/-- **The constant field `k'` of the cover** (the algebraic closure of `K` in `K(N)`). -/
abbrev coverField : Type u := constField K (coverNorm C hc f)

lemma coverNorm_isIntegrallyClosed :
    ∀ (W : (coverNorm C hc f).Opens), IsAffineOpen W → ∀ [Nonempty W],
      IsIntegrallyClosed Γ(coverNorm C hc f, W) :=
  haveI := isIntegral_cover C hc f
  isIntegrallyClosed_sections_normalization (k := K) C.nonempty (coverMap C hc f)

/-- The structure morphism `N ⟶ Spec k'`. -/
def coverToSpec : coverNorm C hc f ⟶ Spec (.of (coverField C hc f)) :=
  toSpecConstField K (coverNorm C hc f) (coverNorm_isIntegrallyClosed C hc f)

lemma coverToSpec_comp :
    coverToSpec C hc f ≫ Spec.map (CommRingCat.ofHom (algebraMap K (coverField C hc f))) =
      coverFromNorm C hc f ≫ (C.Xbar ↘ Spec (.of K)) :=
  toSpecConstField_comp K _ _

instance : CharZero (coverField C hc f) :=
  charZero_of_injective_algebraMap (algebraMap K (coverField C hc f)).injective

/-- **(i) The constant field of the cover is a number field.** -/
instance : NumberField (coverField C hc f) :=
  haveI := isIntegral_cover C hc f
  haveI : FiniteDimensional K (coverField C hc f) :=
    finiteDimensional_constField_normalization (k := K) C.nonempty (coverMap C hc f)
  { to_finiteDimensional := Module.Finite.trans K (coverField C hc f) }

/-- **The cover as a hyperbolic curve** over its constant field `k'`: the open `q⁻¹ U` of the
normalisation `N` (`CurvesJacobian.Cusp.coverHypCurve`). -/
def coverCurve : HypCurve (coverField C hc f) :=
  haveI := isIntegral_cover C hc f
  coverHypCurve C (coverMap C hc f)

/-- **(iii) The cover curve has a cusp**: `q : N ⟶ X̄` is surjective. -/
theorem coverCurve_cusp :
    ((coverCurve C hc f).U : Set (coverCurve C hc f).Xbar)ᶜ.Nonempty := by
  haveI := isLocallyNoetherian_of_isCurveOver K C.Xbar
  haveI := isIntegral_cover C hc f
  obtain ⟨x, hx⟩ := id hc
  obtain ⟨y, hy⟩ := surjective_fromNormalization (k := K) C.nonempty (coverMap C hc f) x
  exact ⟨y, fun hy' ↦ hx (hy ▸ hy')⟩

/-- `V ≅ q⁻¹ U` (`CurvesJacobian.Cusp.coverOpenIso`). -/
def coverOpen : V ≅ (coverCurve C hc f).U.toScheme :=
  haveI := isIntegral_cover C hc f
  coverOpenIso C (coverMap C hc f)

@[reassoc]
lemma coverOpen_hom_ι : (coverOpen C hc f).hom ≫ (coverCurve C hc f).U.ι = coverToNorm C hc f :=
  haveI := isIntegral_cover C hc f
  coverOpenIso_hom_ι C (coverMap C hc f)

lemma coverOpen_inv_toNorm :
    (coverOpen C hc f).inv ≫ coverToNorm C hc f = (coverCurve C hc f).U.ι :=
  (Iso.inv_comp_eq _).2 (coverOpen_hom_ι C hc f).symm

/-- `V ⟶ N ⟶ Spec k' ⟶ Spec K` is `f` followed by the structure morphism of `U`. -/
lemma coverToNorm_toSpec_comp :
    coverToNorm C hc f ≫ coverToSpec C hc f ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (coverField C hc f))) =
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) := by
  rw [coverToSpec_comp, ← Category.assoc, coverToNorm_fromNorm,
    ← isoSpec_inv_ι_structure K (isAffineOpen_U C hc)]
  simp only [coverMap, Category.assoc]

variable (η : Spec (.of Ω) ⟶ V)

/-- The `Ω`-point of `Spec k'` induced by `η`: `Spec Ω ⟶ V ⟶ N ⟶ Spec k'`. -/
def coverFieldPt : Spec (.of Ω) ⟶ Spec (.of (coverField C hc f)) :=
  η ≫ coverToNorm C hc f ≫ coverToSpec C hc f

/-- **(ii) The embedding `k' ⊆ Ω` induced by `η`.** -/
abbrev coverAlgebra : Algebra (coverField C hc f) Ω :=
  (Spec.preimage (coverFieldPt Ω C hc f η)).hom.toAlgebra

omit [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma specMap_coverAlgebra :
    letI := coverAlgebra Ω C hc f η
    Spec.map (CommRingCat.ofHom (algebraMap (coverField C hc f) Ω)) =
      coverFieldPt Ω C hc f η :=
  Spec.map_preimage _

variable (h : η ≫ f = basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
include h in
/-- The embedding `k' ⊆ Ω` induced by `η` extends `K ⊆ Ω`. -/
theorem isScalarTower_coverAlgebra :
    letI := coverAlgebra Ω C hc f η
    IsScalarTower K (coverField C hc f) Ω := by
  letI := coverAlgebra Ω C hc f η
  refine IsScalarTower.of_algebraMap_eq' ?_
  have key : Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
      Spec.map (CommRingCat.ofHom ((algebraMap (coverField C hc f) Ω).comp
        (algebraMap K (coverField C hc f)))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_coverAlgebra, coverFieldPt,
      Category.assoc, Category.assoc, coverToNorm_toSpec_comp, ← Category.assoc, h]
    exact (basePoint_spec₂ Ω C hc).symm
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

omit [CharZero Ω] in
include h in
lemma isAlgebraic_coverAlgebra :
    letI := coverAlgebra Ω C hc f η
    Algebra.IsAlgebraic (coverField C hc f) Ω :=
  letI := coverAlgebra Ω C hc f η
  haveI := isScalarTower_coverAlgebra Ω C hc f η h
  Algebra.IsAlgebraic.tower_top (K := K) (coverField C hc f)

/-- **(iv) `Spec Γ(N, q⁻¹ U) ≅ V`.** -/
def coverIso : Spec Γ((coverCurve C hc f).Xbar, (coverCurve C hc f).U) ≅ V :=
  (isAffineOpen_U (coverCurve C hc f) (coverCurve_cusp C hc f)).isoSpec.symm ≪≫
    (coverOpen C hc f).symm

/-- **(iv) `e : Spec Γ(N, q⁻¹ U) ≅ V` is compatible with the structure morphisms** to `Spec K`. -/
theorem coverIso_spec :
    (coverIso C hc f).hom ≫ f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap (coverField C hc f)
          Γ((coverCurve C hc f).Xbar, (coverCurve C hc f).U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (coverField C hc f))) := by
  have hU' := isAffineOpen_U (coverCurve C hc f) (coverCurve_cusp C hc f)
  rw [← isoSpec_inv_ι_structure (coverField C hc f) hU', ← coverToNorm_toSpec_comp C hc f]
  simp only [coverIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% coverOpen_inv_toNorm C hc f]
  rfl

omit [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- **`η` induces the embedding `k' ⊆ Ω`** (the hypothesis `hη` of
`CurvesJacobian.Cusp.map_pr_coverSubgroup_of_comp`). -/
theorem coverIso_point :
    letI := coverAlgebra Ω C hc f η
    η ≫ (coverIso C hc f).inv ≫ Spec.map (CommRingCat.ofHom (algebraMap (coverField C hc f)
        Γ((coverCurve C hc f).Xbar, (coverCurve C hc f).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap (coverField C hc f) Ω)) := by
  letI := coverAlgebra Ω C hc f η
  have hU' := isAffineOpen_U (coverCurve C hc f) (coverCurve_cusp C hc f)
  rw [specMap_coverAlgebra, ← isoSpec_inv_ι_structure (coverField C hc f) hU']
  simp only [coverIso, Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]
  rw [coverOpen_hom_ι_assoc]
  rfl

/-- **(v) `Π_{q⁻¹ U} ≃ₜ*` the group of the chain object of the cover `V`**
(`CurvesJacobian.Cusp.coverPiEquiv` for the cover curve). -/
def coverCurvePiEquiv :
    letI := coverAlgebra Ω C hc f η
    haveI := isAlgebraic_coverAlgebra Ω C hc f η h
    (arithmeticExt Ω (coverCurve C hc f) (coverCurve_cusp C hc f)).Pi ≃ₜ*
      (coverChainObj Ω C hc f η h).grp :=
  letI := coverAlgebra Ω C hc f η
  haveI := isAlgebraic_coverAlgebra Ω C hc f η h
  haveI := isScalarTower_coverAlgebra Ω C hc f η h
  coverPiEquiv Ω C hc f η h (coverCurve C hc f) (coverCurve_cusp C hc f) (coverIso C hc f)

/-- **Compatibility with the projections to `G_K`**: `toG (e γ) = g · ι (pr γ) · g⁻¹`. -/
theorem toG_coverCurvePiEquiv :
    letI := coverAlgebra Ω C hc f η
    haveI := isAlgebraic_coverAlgebra Ω C hc f η h
    haveI := isScalarTower_coverAlgebra Ω C hc f η h
    ∀ γ : (arithmeticExt Ω (coverCurve C hc f) (coverCurve_cusp C hc f)).Pi,
      (coverChainObj Ω C hc f η h).toG (coverCurvePiEquiv Ω C hc f η h γ) =
        coverConj Ω C hc f η h (coverCurve C hc f) (coverCurve_cusp C hc f) (coverIso C hc f)
            (coverIso_spec C hc f) *
          galoisMap K (coverField C hc f) Ω
            ((arithmeticExt Ω (coverCurve C hc f) (coverCurve_cusp C hc f)).pr γ) *
          (coverConj Ω C hc f η h (coverCurve C hc f) (coverCurve_cusp C hc f)
            (coverIso C hc f) (coverIso_spec C hc f))⁻¹ :=
  letI := coverAlgebra Ω C hc f η
  haveI := isAlgebraic_coverAlgebra Ω C hc f η h
  haveI := isScalarTower_coverAlgebra Ω C hc f η h
  toG_coverPiEquiv Ω C hc f η h (coverCurve C hc f) (coverCurve_cusp C hc f) (coverIso C hc f)
    (coverIso_spec C hc f)

/-- **`Δ_{q⁻¹ U}` corresponds to `Δ` of the chain object** (`Π_{q⁻¹ U} ∩ Δ_U = Δ_{q⁻¹ U}`). -/
theorem map_Delta_coverCurvePiEquiv :
    letI := coverAlgebra Ω C hc f η
    haveI := isAlgebraic_coverAlgebra Ω C hc f η h
    (arithmeticExt Ω (coverCurve C hc f) (coverCurve_cusp C hc f)).Delta.map
        (coverCurvePiEquiv Ω C hc f η h).toMulEquiv.toMonoidHom =
      (coverChainObj Ω C hc f η h).Delta :=
  letI := coverAlgebra Ω C hc f η
  haveI := isAlgebraic_coverAlgebra Ω C hc f η h
  haveI := isScalarTower_coverAlgebra Ω C hc f η h
  map_Delta_coverPiEquiv Ω C hc f η h (coverCurve C hc f) (coverCurve_cusp C hc f)
    (coverIso C hc f) (coverIso_spec C hc f)

/-- **The image of `π₁ᵉᵗ(V) ⊆ Π_U` in `G_K` is exactly `ι(G_{k'})`** for the embedding
`k' ⊆ Ω` induced by `η`. -/
theorem map_pr_coverSubgroup_eq_range :
    letI := coverAlgebra Ω C hc f η
    haveI := isScalarTower_coverAlgebra Ω C hc f η h
    (coverSubgroup f η h :
        Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))).map
        (projGk Ω C hc).toMonoidHom =
      (galoisMap K (coverField C hc f) Ω).toMonoidHom.range :=
  letI := coverAlgebra Ω C hc f η
  haveI := isAlgebraic_coverAlgebra Ω C hc f η h
  haveI := isScalarTower_coverAlgebra Ω C hc f η h
  map_pr_coverSubgroup_of_comp Ω C hc f η h (coverCurve C hc f) (coverCurve_cusp C hc f)
    (coverIso C hc f) (coverIso_spec C hc f) (coverIso_point Ω C hc f η)

end CurvesJacobian.Cusp
