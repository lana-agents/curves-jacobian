/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.Equalizer
import CurvesJacobian.Picard.FlatAlgebra

/-!
# Computing the rank of a finite flat morphism

Generic results, candidates for upstreaming to Mathlib.

* `Scheme.Hom.finrank_eq_rankAtStalk`: for `f : X ⟶ S` finite flat and an affine open `V ⊆ S`
  containing `s`, `f.finrank s` is the rank at `s` of the `Γ(S, V)`-module `Γ(X, f⁻¹ V)`.
* `Module.rankAtStalk_eq_add_of_exact`: ranks at stalks are additive in short exact sequences
  `0 → M₁ → M₂ → M₃ → 0` with `M₂` finite and `M₃` flat.
* `Module.rankAtStalk_quotient_mul`: if `t₁` is a nonzerodivisor of an `A`-algebra `B`, `B/t₁t₂`
  is `A`-finite and `B/t₁` is `A`-flat, then `rk(B/t₁t₂) = rk(B/t₁) + rk(B/t₂)`.
-/

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The rank of a finite flat morphism at `s` is computed on any affine open `V ∋ s`: it is the
rank at the prime of `s` of the `Γ(S, V)`-module `Γ(X, f⁻¹ V)`. -/
lemma Scheme.Hom.finrank_eq_rankAtStalk (f : X ⟶ S) [Flat f] [IsFinite f] {V : S.Opens}
    (hV : IsAffineOpen V) (s : S) (hs : s ∈ V) :
    letI := (f.app V).hom.toAlgebra
    f.finrank s = Module.rankAtStalk Γ(X, f ⁻¹ᵁ V) (hV.primeIdealOf ⟨s, hs⟩) := by
  letI := (f.app V).hom.toAlgebra
  have : IsAffine V := hV
  have hV' : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have : IsAffine (f ⁻¹ᵁ V) := hV'
  have : IsIso V.toSpecΓ := inferInstanceAs (IsIso hV.isoSpec.hom)
  have : IsIso (f ⁻¹ᵁ V).toSpecΓ := inferInstanceAs (IsIso hV'.isoSpec.hom)
  have : Flat (f ∣_ V) :=
    MorphismProperty.of_isPullback (P := @Flat) (isPullback_morphismRestrict f V).flip ‹_›
  have : IsFinite (f ∣_ V) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict f V).flip ‹_›
  have e : f ∣_ V ≫ V.toSpecΓ = (f ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (f.app V) :=
    (Scheme.Opens.toSpecΓ_naturality f V).symm
  have e' : Spec.map (f.app V) = inv (f ⁻¹ᵁ V).toSpecΓ ≫ f ∣_ V ≫ V.toSpecΓ := by
    rw [e, IsIso.inv_hom_id_assoc]
  have : Flat (Spec.map (f.app V)) := by rw [e']; infer_instance
  have : IsFinite (Spec.map (f.app V)) := by rw [e']; infer_instance
  have : Module.Finite Γ(S, V) Γ(X, f ⁻¹ᵁ V) := (IsFinite.SpecMap_iff _).mp ‹_›
  have : Module.Flat Γ(S, V) Γ(X, f ⁻¹ᵁ V) := Flat.SpecMap_iff.mp ‹_›
  let v : V.toScheme := ⟨s, hs⟩
  have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict f V).flip v
  have h2 := Scheme.Hom.finrank_of_isPullback (𝟙 _) (f ∣_ V) (f ∣_ V ≫ V.toSpecΓ) V.toSpecΓ
    (IsPullback.of_horiz_isIso ⟨by simp⟩) v
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso] at h2
  rw [show finrank f s = finrank f (V.ι v) from rfl, ← h1, h2]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(S, V) Γ(X, f ⁻¹ᵁ V) _

end AlgebraicGeometry

namespace Module

variable {A : Type u} [CommRing A] {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂]
  [AddCommGroup M₃] [Module A M₁] [Module A M₂] [Module A M₃]

/-- Ranks at stalks are additive in short exact sequences `0 → M₁ → M₂ → M₃ → 0` of finite
modules with `M₁` and `M₃` flat. -/
theorem rankAtStalk_eq_add_of_exact [Module.Finite A M₁] [Module.Finite A M₂]
    [Module.Flat A M₁] [Module.Flat A M₃]
    (g : M₁ →ₗ[A] M₂) (f : M₂ →ₗ[A] M₃) (hg : Function.Injective g)
    (hf : Function.Surjective f) (H : Function.Exact g f) (p : PrimeSpectrum A) :
    rankAtStalk M₂ p = rankAtStalk M₁ p + rankAtStalk M₃ p := by
  have : Module.Flat A M₂ := CurvesJacobian.Module.Flat.of_exact g f hg hf H
  have : Module.Finite A M₃ := Module.Finite.of_surjective f hf
  rw [rankAtStalk_eq, rankAtStalk_eq, rankAtStalk_eq]
  let κ := p.asIdeal.ResidueField
  let g' := AlgebraTensorModule.lTensor κ κ g
  let f' := AlgebraTensorModule.lTensor κ κ f
  have hg' : Function.Injective g' :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf g hg H κ
  have hf' : Function.Surjective f' := LinearMap.lTensor_surjective κ hf
  have H' : Function.Exact g' f' := lTensor_exact κ H hf
  rw [← LinearMap.finrank_range_add_finrank_ker f', LinearMap.range_eq_top.mpr hf',
    finrank_top, LinearMap.exact_iff.mp H', LinearMap.finrank_range_of_inj hg', add_comm]

/-- If `t₁` is a nonzerodivisor of an `A`-algebra `B` such that `B/t₁t₂` is `A`-finite and
`B/t₁`, `B/t₂` are `A`-flat, then `rk(B/t₁t₂) = rk(B/t₁) + rk(B/t₂)` at every prime of `A`. -/
theorem rankAtStalk_quotient_mul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {t₁ : B} (ht₁ : IsSMulRegular B t₁) (t₂ : B)
    [Module.Finite A (B ⧸ Ideal.span {t₁ * t₂})] [Module.Flat A (B ⧸ Ideal.span {t₁})]
    [Module.Flat A (B ⧸ Ideal.span {t₂})] (p : PrimeSpectrum A) :
    rankAtStalk (B ⧸ Ideal.span {t₁ * t₂}) p =
      rankAtStalk (B ⧸ Ideal.span {t₁}) p + rankAtStalk (B ⧸ Ideal.span {t₂}) p := by
  have : Module.Finite A (B ⧸ Ideal.span {t₂ * t₁}) := by rwa [mul_comm]
  have : Module.Finite A (B ⧸ Ideal.span {t₂}) := Module.Finite.of_surjective
    ((CurvesJacobian.quotFactor t₂ t₁).restrictScalars A) (CurvesJacobian.quotFactor_surjective _ _)
  rw [rankAtStalk_eq_add_of_exact (((CurvesJacobian.mulQuot t₁ t₂).restrictScalars A))
    ((CurvesJacobian.quotFactor t₁ t₂).restrictScalars A) (CurvesJacobian.mulQuot_injective ht₁ t₂)
    (CurvesJacobian.quotFactor_surjective t₁ t₂) (CurvesJacobian.exact_mulQuot_quotFactor t₁ t₂),
    add_comm]

end Module

/-- A ring isomorphism compatible with given `F`-algebra structures preserves `F`-ranks. -/
lemma Module.finrank_eq_of_ringEquiv {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
    [Algebra F A] (e : A ≃+* B) (φ : F →+* B) (he : ∀ k, e (algebraMap F A k) = φ k) :
    Module.finrank F A = @Module.finrank F B _ _ φ.toAlgebra.toModule :=
  letI := φ.toAlgebra
  (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.finrank_eq

/-- A ring isomorphism compatible with given `F`-algebra structures preserves `F`-finiteness. -/
lemma Module.finite_of_ringEquiv {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
    [Algebra F A] [Module.Finite F A] (e : A ≃+* B) (φ : F →+* B)
    (he : ∀ k, e (algebraMap F A k) = φ k) :
    @Module.Finite F B _ _ φ.toAlgebra.toModule :=
  letI := φ.toAlgebra
  Module.Finite.equiv (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The rank over `Γ(S, ⊤)` of the stalk of `X` at `y`, for a morphism `h : X ⟶ S`
(the `Γ(S, ⊤)`-algebra structure is `Γ(S, ⊤) → 𝒪_{S, h y} → 𝒪_{X, y}`). -/
def Scheme.Hom.stalkRank (h : X ⟶ S) (y : X) : ℕ :=
  @Module.finrank Γ(S, ⊤) (X.presheaf.stalk y) _ _
    (S.presheaf.germ ⊤ (h y) trivial ≫ h.stalkMap y).hom.toAlgebra.toModule

/-- Over an affine base whose ring of global sections is a field, the rank of a finite flat
morphism is the sum of the ranks of the stalks of the source. -/
lemma Scheme.Hom.finrank_eq_finsum_stalkRank [IsAffine S] (hF : IsField Γ(S, ⊤)) (h : X ⟶ S)
    [Flat h] [IsFinite h] (s : S) : h.finrank s = ∑ᶠ y, h.stalkRank y := by
  letI := hF.toField
  letI := (h.app ⊤).hom.toAlgebra
  rw [h.finrank_eq_rankAtStalk (isAffineOpen_top S) s trivial]
  have : Module.Finite Γ(S, ⊤) Γ(X, h ⁻¹ᵁ ⊤) := h.finite_appTop
  have : IsArtinianRing Γ(X, h ⁻¹ᵁ ⊤) := IsArtinianRing.of_finite Γ(S, ⊤) _
  rw [Module.rankAtStalk_eq_finrank_of_free]
  have : IsAffine X := isAffine_of_isAffineHom h
  have hU : IsAffineOpen (h ⁻¹ᵁ ⊤) := isAffineOpen_top X
  letI : Fintype (PrimeSpectrum Γ(X, h ⁻¹ᵁ ⊤)) := Fintype.ofFinite _
  have hbij := PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp
    (inferInstance : DiscreteTopology (PrimeSpectrum Γ(X, h ⁻¹ᵁ ⊤)))
  let e : Γ(X, h ⁻¹ᵁ ⊤) ≃ₗ[Γ(S, ⊤)] PrimeSpectrum.PiLocalization Γ(X, h ⁻¹ᵁ ⊤) :=
    LinearEquiv.ofBijective
      ((PrimeSpectrum.toPiLocalization Γ(X, h ⁻¹ᵁ ⊤)).toLinearMap.restrictScalars _) hbij
  have hloc (p : PrimeSpectrum Γ(X, h ⁻¹ᵁ ⊤)) :
      Module.Finite Γ(S, ⊤) (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective ((Algebra.linearMap Γ(X, h ⁻¹ᵁ ⊤) _).restrictScalars Γ(S, ⊤))
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  let E : PrimeSpectrum Γ(X, h ⁻¹ᵁ ⊤) ≃ X := Equiv.ofBijective hU.fromSpec
    ⟨hU.fromSpec.isOpenEmbedding.injective, fun y ↦
      (Set.ext_iff.mp hU.range_fromSpec y).mpr trivial⟩
  rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hU.fromSpec p, trivial⟩ : (h ⁻¹ᵁ ⊤ : X.Opens))
  have : IsLocalization p.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec p)) :=
    hU.isLocalization_stalk' p trivial
  refine Module.finrank_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (X.presheaf.stalk (hU.fromSpec p))).toRingEquiv _ ?_
  intro k
  rw [IsScalarTower.algebraMap_apply Γ(S, ⊤) Γ(X, h ⁻¹ᵁ ⊤), AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes]
  change X.presheaf.germ (h ⁻¹ᵁ ⊤) _ _ (h.app ⊤ k) = h.stalkMap _ (S.presheaf.germ ⊤ _ _ k)
  rw [Scheme.Hom.germ_stalkMap_apply]

/-- Over an affine base whose ring of global sections is a field, the source of a finite
morphism has finitely many points. -/
lemma Scheme.Hom.finite_of_isField [IsAffine S] (hF : IsField Γ(S, ⊤)) (h : X ⟶ S)
    [IsFinite h] : Finite X := by
  letI := hF.toField
  letI := (h.app ⊤).hom.toAlgebra
  have : Module.Finite Γ(S, ⊤) Γ(X, h ⁻¹ᵁ ⊤) := h.finite_appTop
  have : IsArtinianRing Γ(X, h ⁻¹ᵁ ⊤) := IsArtinianRing.of_finite Γ(S, ⊤) _
  have : IsAffine X := isAffine_of_isAffineHom h
  have hU : IsAffineOpen (h ⁻¹ᵁ ⊤) := isAffineOpen_top X
  have : Finite (Spec Γ(X, h ⁻¹ᵁ ⊤)) := inferInstanceAs (Finite (PrimeSpectrum _))
  exact Finite.of_surjective hU.fromSpec fun y ↦ (Set.ext_iff.mp hU.range_fromSpec y).mpr trivial

/-- Over an affine base whose ring of global sections is a field, the stalks of the source of a
finite morphism are finite-dimensional. -/
lemma Scheme.Hom.finite_stalk [IsAffine S] (hF : IsField Γ(S, ⊤)) (h : X ⟶ S) [IsFinite h]
    (y : X) : @Module.Finite Γ(S, ⊤) (X.presheaf.stalk y) _ _
      (S.presheaf.germ ⊤ (h y) trivial ≫ h.stalkMap y).hom.toAlgebra.toModule := by
  letI := hF.toField
  letI := (h.app ⊤).hom.toAlgebra
  have : Module.Finite Γ(S, ⊤) Γ(X, h ⁻¹ᵁ ⊤) := h.finite_appTop
  have : IsArtinianRing Γ(X, h ⁻¹ᵁ ⊤) := IsArtinianRing.of_finite Γ(S, ⊤) _
  have : IsAffine X := isAffine_of_isAffineHom h
  have hU : IsAffineOpen (h ⁻¹ᵁ ⊤) := isAffineOpen_top X
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := (Set.ext_iff.mp hU.range_fromSpec y).mpr trivial
  have hloc : Module.Finite Γ(S, ⊤) (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective ((Algebra.linearMap Γ(X, h ⁻¹ᵁ ⊤) _).restrictScalars Γ(S, ⊤))
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hU.fromSpec p, trivial⟩ : (h ⁻¹ᵁ ⊤ : X.Opens))
  have : IsLocalization p.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec p)) :=
    hU.isLocalization_stalk' p trivial
  refine Module.finite_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (X.presheaf.stalk (hU.fromSpec p))).toRingEquiv _ ?_
  intro k
  rw [IsScalarTower.algebraMap_apply Γ(S, ⊤) Γ(X, h ⁻¹ᵁ ⊤), AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes]
  change X.presheaf.germ (h ⁻¹ᵁ ⊤) _ _ (h.app ⊤ k) = h.stalkMap _ (S.presheaf.germ ⊤ _ _ k)
  rw [Scheme.Hom.germ_stalkMap_apply]

end AlgebraicGeometry
