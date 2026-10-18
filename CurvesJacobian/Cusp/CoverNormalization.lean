/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Analytification.RET.ES.NormalizationInCover
import Belyi.Converse.Normalization

/-!
# The normalisation of a normal scheme in a finite étale cover of a dense open

Let `X` be an integral, locally noetherian scheme such that `Γ(X, W)` is integrally closed for
every affine open `W`, let `U ⊆ X` be a nonempty open and `p : Y ⟶ U` finite étale. Write
`f = p ≫ U.ι` and `q = f.fromNormalization : N ⟶ X` for the relative normalisation of `X` in `Y`.
We prove:

* `CurvesJacobian.Cusp.isFinite_fromNormalization`: `q` is finite;
* `CurvesJacobian.Cusp.isFiniteProductOfNormalDomains_preimage`: for every nonempty affine open
  `W ⊆ X`, the ring `Γ(N, q⁻¹ W)` is a finite product of normal domains;
* `CurvesJacobian.Cusp.isIntegrallyClosed_normalization`: if `Y` is integral, then `N` is
  integral and `Γ(N, V)` is an integrally closed domain for every nonempty affine open `V ⊆ N`;
* `CurvesJacobian.Cusp.isPullback_toNormalization`: `Y = q⁻¹ U` (oka's
  `ComplexAnalytic.isPullback_toNormalization`).

## Proof

For `X` affine with `Γ(X, 𝒪)` a noetherian finite product of normal domains and `U` containing
`D(a)` for a nonzerodivisor `a`, this is oka's `ComplexAnalytic.fromNormalization_properties`,
whose proof uses the codimension-two hypothesis only to produce such an `a`
(`fromNormalization_properties_of_nonZeroDivisor` below repeats the proof with `a` given).

In general, finiteness is local on `X`, so it suffices to treat `q` over a nonempty affine open
`W`. Over `W`, normalisation commutes with the smooth base change `W.ι`
(`Scheme.Hom.normalizationPullback`), and `pullback f W.ι = p' ≫ U'.ι` for `U' = W ∩ U` and the
base change `p'` of `p`, which is finite étale. As `Γ(W, 𝒪)` is a normal domain and `W ∩ U` is
nonempty (`X` is irreducible), any nonzero `a` with `D(a) ⊆ W ∩ U` works.

If `Y` is integral, so is `N`; the domain `Γ(N, q⁻¹ W)` is then a single normal domain, its
localisations (the stalks of `N`) are integrally closed, and hence so is `Γ(N, V)` for every
affine `V` (`AlgebraicGeometry.isIntegrallyClosed_of_isAffineOpen`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry ComplexAnalytic

universe u

namespace CurvesJacobian.Cusp

/-! ### The affine case -/

/-- **Normalisation in a finite étale cover, affine case.** Variant of oka's
`ComplexAnalytic.fromNormalization_properties` with the codimension-two hypothesis replaced by
the existence of a nonzerodivisor `a` with `D(a) ⊆ U`. -/
theorem fromNormalization_properties_of_nonZeroDivisor {X Y : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (hX : IsFiniteProductOfNormalDomains Γ(X, ⊤)) (U : X.Opens)
    (hU : ∃ a ∈ nonZeroDivisors Γ(X, ⊤), X.basicOpen a ≤ U) (p : Y ⟶ U) [IsFinite p] [Etale p]
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] (hf : p ≫ U.ι = f) :
    IsFinite f.fromNormalization ∧ IsFiniteProductOfNormalDomains Γ(f.normalization, ⊤) := by
  classical
  subst hf
  obtain ⟨ι, hι, D, _, _, _, ⟨e⟩⟩ := id hX
  obtain ⟨a, ha, haU⟩ := hU
  let 𝔅 : Set Γ(X, ⊤) := {b | (∃ i d, b = e.symm (Pi.single i d)) ∧ X.basicOpen b ≤ U}
  have hcov : ∀ y : Y, ∃ b ∈ 𝔅, (p ≫ U.ι).base y ∈ X.basicOpen b := fun y ↦ by
    obtain ⟨i, d, h₁, h₂⟩ := exists_single_basicOpen_le e (x := (p ≫ U.ι).base y) (p.base y).2
    exact ⟨_, ⟨⟨i, d, rfl⟩, h₂⟩, h₁⟩
  have hmul : ∀ b ∈ 𝔅, ∀ b' ∈ 𝔅, b * b' ∈ 𝔅 := by
    rintro _ ⟨⟨i, d, rfl⟩, hb⟩ b' -
    refine ⟨⟨i, _, symm_single_mul_eq e i d b'⟩, ?_⟩
    rw [Scheme.basicOpen_mul]
    exact inf_le_left.trans hb
  have hgood : ∀ b ∈ 𝔅, IsEtaleNormalAt (p ≫ U.ι) a b := by
    rintro _ ⟨⟨i, d, rfl⟩, hb⟩
    obtain ⟨h₁, -, h₃⟩ :=
      isAffineOpen_preimage_finite_etale_app p ((isAffineOpen_top X).basicOpen _) hb
    exact ⟨h₁, h₃, subsingleton_or_isDomain_of_isLocalization_single e i d _ ha⟩
  -- the finite étale algebra `Γ(Y, (p ≫ U.ι)⁻¹ D(a))` over `Γ(X, 𝒪)_a`
  obtain ⟨-, hfin, het⟩ :=
    isAffineOpen_preimage_finite_etale_app p ((isAffineOpen_top X).basicOpen a) haU
  letI : Algebra Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    ((p ≫ U.ι).app (X.basicOpen a)).hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    ((algebraMap Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen a))).toAlgebra
  haveI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    .of_algebraMap_eq' rfl
  haveI : Module.Finite Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) := hfin
  haveI : Algebra.Etale Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) := het
  obtain ⟨hB₁, hB₂, -⟩ := finite_isFiniteProductOfNormalDomains_hasGoingDown_integralClosure hX
    ha Γ(X, X.basicOpen a) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a)
  -- restriction identifies the integral closures in `Γ(Y, 𝒪)` and `Γ(Y, (p ≫ U.ι)⁻¹ D(a))`
  letI : Algebra Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ ⊤) := ((p ≫ U.ι).app ⊤).hom.toAlgebra
  have hnat : ∀ r : Γ(X, ⊤), Y.presheaf.map (homOfLE (le_top :
      (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op ((p ≫ U.ι).app ⊤ r) =
      (p ≫ U.ι).app (X.basicOpen a) (X.presheaf.map (homOfLE (le_top :
        X.basicOpen a ≤ ⊤)).op r) := fun r ↦ by
    change ((p ≫ U.ι).app ⊤ ≫ Y.presheaf.map _) r = (X.presheaf.map _ ≫ (p ≫ U.ι).app _) r
    rw [Scheme.Hom.naturality]
    rfl
  let ρ : Γ(Y, (p ≫ U.ι) ⁻¹ᵁ ⊤) →ₐ[Γ(X, ⊤)] Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    { toRingHom := (Y.presheaf.map (homOfLE (le_top :
        (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op).hom
      commutes' := hnat }
  have hρ : Function.Injective ρ := injective_res_preimage_basicOpen (p ≫ U.ι) a hcov hgood
  have hΦ : Function.Bijective ρ.mapIntegralClosure := by
    refine ⟨fun x y hxy ↦ Subtype.ext (hρ (congrArg Subtype.val hxy)), fun x ↦ ?_⟩
    obtain ⟨s, hs⟩ := exists_res_preimage_basicOpen_eq (p ≫ U.ι) a hcov hmul hgood x.1 (by
      obtain ⟨q, hq, hqx⟩ := x.2
      refine ⟨q, hq, ?_⟩
      convert hqx using 2
      ext r
      exact hnat r)
    refine ⟨⟨s, (isIntegral_algHom_iff ρ hρ).1 ?_⟩, Subtype.ext hs⟩
    change IsIntegral _ (ρ s)
    rw [show ρ s = x.1 from hs]
    exact x.2
  let Φ := AlgEquiv.ofBijective _ hΦ
  -- the ring of functions of the normalisation
  let ψ : Γ((p ≫ U.ι).normalization, ⊤) ≃+* integralClosure Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ ⊤) :=
    ((p ≫ U.ι).normalizationObjIso (isAffineOpen_top X)).commRingCatIsoToRingEquiv
  have hψ : ∀ r, ψ ((p ≫ U.ι).fromNormalization.appTop r) = algebraMap _ _ r := fun r ↦ by
    change ((p ≫ U.ι).fromNormalization.app ⊤ ≫
      ((p ≫ U.ι).normalizationObjIso (isAffineOpen_top X)).hom) r = _
    rw [Scheme.Hom.fromNormalization_app _ (isAffineOpen_top X), Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  letI : Algebra Γ(X, ⊤) Γ((p ≫ U.ι).normalization, ⊤) :=
    (p ≫ U.ι).fromNormalization.appTop.hom.toAlgebra
  let Ψ : Γ((p ≫ U.ι).normalization, ⊤) ≃ₐ[Γ(X, ⊤)]
      integralClosure Γ(X, ⊤) Γ(Y, (p ≫ U.ι) ⁻¹ᵁ X.basicOpen a) :=
    { toRingEquiv := ψ.trans Φ.toRingEquiv
      commutes' := fun r ↦ by
        change Φ (ψ ((p ≫ U.ι).fromNormalization.appTop r)) = _
        rw [hψ, AlgEquiv.commutes] }
  haveI : Module.Finite Γ(X, ⊤) Γ((p ≫ U.ι).normalization, ⊤) :=
    Module.Finite.equiv Ψ.symm.toLinearEquiv
  haveI : IsAffine (p ≫ U.ι).normalization := isAffine_of_isAffineHom (p ≫ U.ι).fromNormalization
  refine ⟨?_, hB₂.of_ringEquiv Ψ.toRingEquiv⟩
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
  exact ⟨inferInstance, RingHom.finite_algebraMap.2 inferInstance⟩

/-! ### Ring-theoretic lemmas -/

/-- A domain which is a finite product of normal domains is integrally closed. -/
lemma isIntegrallyClosed_of_isFiniteProductOfNormalDomains {R : Type u} [CommRing R]
    [IsDomain R] (h : IsFiniteProductOfNormalDomains R) : IsIntegrallyClosed R := by
  classical
  obtain ⟨ι, hι, D, _, _, _, ⟨e⟩⟩ := h
  have hsub : Subsingleton ι := ⟨fun i j ↦ by
    by_contra hij
    have h₀ : e.symm (Pi.single i 1) * e.symm (Pi.single j 1) = 0 := by
      apply e.injective
      rw [map_mul, map_zero, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      funext k
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hk : k = i
      · subst hk
        simp [hij]
      · simp [hk]
    rcases mul_eq_zero.1 h₀ with h₁ | h₁
    · have := congrFun (congrArg e h₁) i
      simp at this
    · have := congrFun (congrArg e h₁) j
      simp at this⟩
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact zero_ne_one (e.injective (funext fun i ↦ isEmptyElim i))
  obtain ⟨i₀⟩ := hne
  letI : Unique ι := ⟨⟨i₀⟩, fun j ↦ Subsingleton.elim _ _⟩
  exact IsIntegrallyClosed.of_equiv (e.trans (RingEquiv.piUnique D)).symm

/-! ### Globalisation -/

section Global

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (hX : ∀ W : X.Opens, IsAffineOpen W → IsIntegrallyClosed Γ(X, W))
  {U : X.Opens} (hU : (U : Set X).Nonempty) {Y : Scheme.{u}} (p : Y ⟶ U) [IsFinite p] [Etale p]

include hX hU in
/-- Over a nonempty affine open `W` of `X`, the relative normalisation of `W` in the base change
of `p ≫ U.ι` is finite and its ring of functions is a finite product of normal domains. -/
lemma fromNormalization_pullback_properties {W : X.Opens} (hW : IsAffineOpen W)
    (hWne : (W : Set X).Nonempty) :
    IsFinite (pullback.snd (p ≫ U.ι) W.ι).fromNormalization ∧
      IsFiniteProductOfNormalDomains Γ((pullback.snd (p ≫ U.ι) W.ι).normalization, ⊤) := by
  haveI : IsAffine W := hW
  have hbot : IsPullback (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι U.ι W.ι := isPullback_morphismRestrict W.ι U
  let p' : pullback (p ≫ U.ι) W.ι ⟶ W.ι ⁻¹ᵁ U :=
    hbot.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _) (by rw [Category.assoc,
      pullback.condition])
  have h₁ : p' ≫ W.ι ∣_ U = pullback.fst _ _ ≫ p := hbot.lift_fst _ _ _
  have h₂ : p' ≫ (W.ι ⁻¹ᵁ U).ι = pullback.snd _ _ := hbot.lift_snd _ _ _
  have htop : IsPullback (pullback.fst (p ≫ U.ι) W.ι) p' p (W.ι ∣_ U) :=
    IsPullback.of_bot (by rw [h₂]; exact IsPullback.of_hasPullback _ _) h₁.symm hbot
  haveI : IsFinite p' := MorphismProperty.of_isPullback htop ‹IsFinite p›
  haveI : Etale p' := MorphismProperty.of_isPullback htop ‹Etale p›
  -- the ring of functions of `W`
  let e : Γ(W, ⊤) ≃+* Γ(X, W) := W.topIso.commRingCatIsoToRingEquiv
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI : IsNoetherianRing Γ(W, ⊤) := isNoetherianRing_of_ringEquiv _ e.symm
  obtain ⟨x, hxW, hxU⟩ := nonempty_preirreducible_inter W.isOpen U.isOpen hWne hU
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  haveI : IsDomain Γ(W, ⊤) := e.toMulEquiv.isDomain _
  haveI := hX W hW
  haveI : IsIntegrallyClosed Γ(W, ⊤) := IsIntegrallyClosed.of_equiv e.symm
  -- a nonzero function on `W` whose basic open lies in `W ∩ U`
  have hy : (⟨x, hxW⟩ : W) ∈ W.ι ⁻¹ᵁ U := hxU
  obtain ⟨c, hcU, hyc⟩ := (isAffineOpen_top W).exists_basicOpen_le
    (V := W.ι ⁻¹ᵁ U) ⟨⟨x, hxW⟩, hy⟩ trivial
  have hc : c ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyc
    exact hyc
  exact fromNormalization_properties_of_nonZeroDivisor (.of_isDomain _) (W.ι ⁻¹ᵁ U)
    ⟨c, mem_nonZeroDivisors_of_ne_zero hc, hcU⟩ p' _ h₂

omit [IsIntegral X] [Etale p] in
/-- `q ∣_ W` is `(pullback.snd (p ≫ U.ι) W.ι).fromNormalization` up to isomorphism. -/
lemma morphismRestrict_fromNormalization_eq (W : X.Opens) :
    (p ≫ U.ι).fromNormalization ∣_ W =
      (pullbackRestrictIsoRestrict (p ≫ U.ι).fromNormalization W).inv ≫
        inv ((p ≫ U.ι).normalizationPullback W.ι) ≫
          (pullback.snd (p ≫ U.ι) W.ι).fromNormalization := by
  rw [Iso.eq_inv_comp, pullbackRestrictIsoRestrict_hom_morphismRestrict, IsIso.eq_inv_comp,
    Scheme.Hom.normalizationPullback_snd]

include hX hU in
/-- **The normalisation of `X` in a finite étale cover of a nonempty open is finite over
`X`.** -/
theorem isFinite_fromNormalization : IsFinite (p ≫ U.ι).fromNormalization := by
  have hcov : (⨆ W : {W : X.Opens // IsAffineOpen W ∧ (W : Set X).Nonempty}, W.1) = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, x, hxW⟩, hxW⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov fun W ↦ ?_
  obtain ⟨W, hW, hWne⟩ := W
  haveI := (fromNormalization_pullback_properties hX hU p hW hWne).1
  rw [morphismRestrict_fromNormalization_eq]
  infer_instance

/-- The preimage of `W` in the normalisation is the normalisation of `W` in the base change. -/
noncomputable def normalizationPreimageIso (W : X.Opens) :
    (pullback.snd (p ≫ U.ι) W.ι).normalization ≅
      ((p ≫ U.ι).fromNormalization ⁻¹ᵁ W : Scheme.{u}) :=
  asIso ((p ≫ U.ι).normalizationPullback W.ι) ≪≫
    pullbackRestrictIsoRestrict (p ≫ U.ι).fromNormalization W

include hX hU in
/-- **Over a nonempty affine open `W` of `X`, the ring of functions of the normalisation is a
finite product of normal domains.** -/
theorem isFiniteProductOfNormalDomains_preimage {W : X.Opens} (hW : IsAffineOpen W)
    (hWne : (W : Set X).Nonempty) :
    IsFiniteProductOfNormalDomains
      Γ((p ≫ U.ι).normalization, (p ≫ U.ι).fromNormalization ⁻¹ᵁ W) := by
  let E : Γ((p ≫ U.ι).normalization, (p ≫ U.ι).fromNormalization ⁻¹ᵁ W) ≅
      Γ((pullback.snd (p ≫ U.ι) W.ι).normalization, ⊤) :=
    ((p ≫ U.ι).fromNormalization ⁻¹ᵁ W).topIso.symm ≪≫
      Scheme.Γ.mapIso (normalizationPreimageIso p W).op
  exact (fromNormalization_pullback_properties hX hU p hW hWne).2.of_ringEquiv
    E.commRingCatIsoToRingEquiv

include hX hU in
/-- **If `Y` is integral, the normalisation of `X` in `Y` is integral and its rings of functions
on nonempty affine opens are integrally closed domains.** -/
theorem isIntegrallyClosed_normalization [IsIntegral Y] {V : (p ≫ U.ι).normalization.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ((p ≫ U.ι).normalization, V) := by
  refine isIntegrallyClosed_of_isAffineOpen hV fun x _ ↦ ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((p ≫ U.ι).fromNormalization x)) isOpen_univ
  have hV' : IsAffineOpen ((p ≫ U.ι).fromNormalization ⁻¹ᵁ W) := hW.preimage _
  have hx : x ∈ (p ≫ U.ι).fromNormalization ⁻¹ᵁ W := hxW
  haveI : Nonempty ((p ≫ U.ι).fromNormalization ⁻¹ᵁ W) := ⟨⟨x, hx⟩⟩
  haveI := isIntegrallyClosed_of_isFiniteProductOfNormalDomains
    (isFiniteProductOfNormalDomains_preimage hX hU p hW ⟨_, hxW⟩)
  letI := TopCat.Presheaf.algebra_section_stalk (p ≫ U.ι).normalization.presheaf ⟨x, hx⟩
  haveI := hV'.isLocalization_stalk ⟨x, hx⟩
  exact isIntegrallyClosed_of_isLocalization _ (hV'.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

omit [IsIntegral X] [Etale p] in
/-- **`Y` is the preimage of `U` in the normalisation** (oka's
`ComplexAnalytic.isPullback_toNormalization`). -/
theorem isPullback_toNormalization :
    IsPullback (p ≫ U.ι).toNormalization p (p ≫ U.ι).fromNormalization U.ι :=
  ComplexAnalytic.isPullback_toNormalization U p

end Global

end CurvesJacobian.Cusp
