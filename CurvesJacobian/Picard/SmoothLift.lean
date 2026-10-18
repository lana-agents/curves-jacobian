/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import CurvesJacobian.Picard.MatLift

/-!
# Smoothness from the infinitesimal lifting property

A morphism of schemes `f : X ⟶ S` has the *infinitesimal lifting property*
(`CurvesJacobian.SmoothLift.LiftProp f`) if for every first-order thickening of affine schemes
`j : T₀ ⟶ T` (surjective on global sections with square-zero kernel) and every commutative
square `x₀ : T₀ ⟶ X`, `g : T ⟶ S` there is a diagonal `x : T ⟶ X`.

* `SmoothLift.smooth_of_liftProp`: if `S` is affine and `f` is locally of finite presentation
  with the infinitesimal lifting property, then `f` is smooth (Stacks, Tag 02H6 for the
  affine case: formally smooth and of finite presentation is smooth, Tag 00TN; smoothness is
  local on the source).

The affine case is `Algebra.FormallySmooth.of_comp_surjective` (the defining lifting property of
formal smoothness) transported through `Spec`; for general `X` the lifts of points of an affine
open `V ⊆ X` land in `V` because a thickening is a homeomorphism.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.SmoothLift

open MatLift

/-- The infinitesimal lifting property of `f` for first-order thickenings of affine schemes. -/
def LiftProp {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (T T₀ : Scheme.{u}) [IsAffine T] [IsAffine T₀] (j : T₀ ⟶ T),
    Function.Surjective j.appTop → SqZero j.appTop.hom → ∀ (g : T ⟶ S) (x₀ : T₀ ⟶ X),
      x₀ ≫ f = j ≫ g → ∃ x : T ⟶ X, x ≫ f = g ∧ j ≫ x = x₀

lemma appTop_spec_map_apply {R R' : CommRingCat.{u}} (φ : R ⟶ R') (a : Γ(Spec R, ⊤)) :
    (Spec.map φ).appTop a = (Scheme.ΓSpecIso R').inv (φ ((Scheme.ΓSpecIso R).hom a)) := by
  have := congr($(Scheme.ΓSpecIso_inv_naturality φ) ((Scheme.ΓSpecIso R).hom a))
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at this
  exact this.symm

lemma surjective_appTop_spec_map {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hs : Function.Surjective φ) : Function.Surjective (Spec.map φ).appTop := by
  intro y
  obtain ⟨b, hb⟩ := hs ((Scheme.ΓSpecIso R').hom y)
  refine ⟨(Scheme.ΓSpecIso R).inv b, ?_⟩
  rw [appTop_spec_map_apply, Iso.inv_hom_id_apply, hb, Iso.hom_inv_id_apply]

lemma sqZero_appTop_spec_map {R R' : CommRingCat.{u}} (φ : R ⟶ R') (hq : SqZero φ.hom) :
    SqZero (Spec.map φ).appTop.hom := by
  intro a b ha hb
  have h0 : ∀ c, (Spec.map φ).appTop c = 0 → φ ((Scheme.ΓSpecIso R).hom c) = 0 := by
    intro c hc
    rw [appTop_spec_map_apply] at hc
    have := congrArg (Scheme.ΓSpecIso R').hom hc
    rwa [Iso.inv_hom_id_apply, map_zero] at this
  have := hq _ _ (h0 a ha) (h0 b hb)
  rw [← map_mul] at this
  have := congrArg (Scheme.ΓSpecIso R).inv this
  rwa [Iso.hom_inv_id_apply, map_zero] at this

/-- **Formally smooth from lifting**, affine case. -/
theorem smooth_of_liftProp_affine {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (H : LiftProp f) : Smooth f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth), RingHom.smooth_def]
  refine ⟨?_, (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp
    inferInstance⟩
  letI := f.appTop.hom.toAlgebra
  change Algebra.FormallySmooth Γ(S, ⊤) Γ(X, ⊤)
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI φ₀ ↦ ?_
  let j : Spec (CommRingCat.of (B ⧸ I)) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let g : Spec (CommRingCat.of B) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv
  let x₀ : Spec (CommRingCat.of (B ⧸ I)) ⟶ X :=
    Spec.map (CommRingCat.ofHom φ₀.toRingHom : Γ(X, ⊤) ⟶ CommRingCat.of (B ⧸ I)) ≫
      X.isoSpec.inv
  have hsq : SqZero (Ideal.Quotient.mk I) := by
    intro a b ha hb
    rw [Ideal.Quotient.eq_zero_iff_mem] at ha hb
    have := Ideal.mul_mem_mul ha hb
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have hcomm : x₀ ≫ f = j ≫ g := by
    simp only [x₀, j, g, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc]
    congr 2
    ext r
    change φ₀ (algebraMap Γ(S, ⊤) Γ(X, ⊤) r) = Ideal.Quotient.mk I (algebraMap Γ(S, ⊤) B r)
    rw [AlgHom.commutes]
    rfl
  obtain ⟨x, hxf, hjx⟩ := H _ _ j (surjective_appTop_spec_map _ Ideal.Quotient.mk_surjective)
    (sqZero_appTop_spec_map _ hsq) g x₀ hcomm
  set θ := Spec.preimage (x ≫ X.isoSpec.hom) with hθ
  have hθmap : Spec.map θ = x ≫ X.isoSpec.hom := Spec.map_preimage _
  have hcomm' : f.appTop ≫ θ = CommRingCat.ofHom (algebraMap Γ(S, ⊤) B) := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hθmap, Category.assoc, Scheme.isoSpec_hom_naturality, reassoc_of% hxf]
    simp [g]
  refine ⟨{ θ.hom with commutes' := fun r ↦ congr($hcomm' r) }, ?_⟩
  have hred : θ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
      (CommRingCat.ofHom φ₀.toRingHom : Γ(X, ⊤) ⟶ CommRingCat.of (B ⧸ I)) := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hθmap, ← Category.assoc]
    change j ≫ x ≫ X.isoSpec.hom = _
    rw [← Category.assoc, hjx]
    simp [x₀]
  ext a
  exact congr($hred a)

lemma surjective_of_thickening {T T₀ : Scheme.{u}} [IsAffine T] [IsAffine T₀] (j : T₀ ⟶ T)
    (hs : Function.Surjective j.appTop) (hq : SqZero j.appTop.hom) :
    Function.Surjective j.base := by
  have key : AlgebraicGeometry.Surjective (Spec.map j.appTop) := by
    rw [surjective_iff]
    intro p
    have hker : RingHom.ker j.appTop.hom ≤ p.asIdeal := fun a ha ↦
      p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hq a a ha ha]; exact p.asIdeal.zero_mem)
    haveI := Ideal.map_isPrime_of_surjective (f := j.appTop.hom) hs hker
    refine ⟨⟨p.asIdeal.map j.appTop.hom, this⟩, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap j.appTop.hom (Ideal.map j.appTop.hom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hker]
  have : AlgebraicGeometry.Surjective j := by
    rwa [MorphismProperty.arrow_mk_iso_iff @AlgebraicGeometry.Surjective
      (arrowIsoSpecΓOfIsAffine j)]
  exact (surjective_iff j).mp this

lemma liftProp_restrict {X S : Scheme.{u}} (f : X ⟶ S) (H : LiftProp f) (V : X.Opens) :
    LiftProp (V.ι ≫ f) := by
  intro T T₀ _ _ j hs hq g x₀ hx₀
  obtain ⟨x, hxf, hjx⟩ := H T T₀ j hs hq g (x₀ ≫ V.ι) (by rw [Category.assoc, hx₀])
  have hrange : Set.range x.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t₀, rfl⟩ := surjective_of_thickening j hs hq t
    refine ⟨x₀.base t₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjx]
  refine ⟨IsOpenImmersion.lift V.ι x hrange, ?_, ?_⟩
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hxf]
  · rw [← cancel_mono V.ι, Category.assoc, IsOpenImmersion.lift_fac, hjx]

/-- **Smoothness from the infinitesimal lifting property**: a morphism to an affine scheme
which is locally of finite presentation and has the infinitesimal lifting property for
first-order thickenings of affine schemes is smooth. -/
theorem smooth_of_liftProp {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (H : LiftProp f) : Smooth f := by
  let O : X.affineOpens → X.Opens := fun V ↦ V.1
  refine IsZariskiLocalAtSource.of_iSup_eq_top O ?_ fun V ↦ ?_
  · refine top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hx⟩
  · haveI : IsAffine (O V) := V.2
    exact smooth_of_liftProp_affine _ (liftProp_restrict f H V.1)

end CurvesJacobian.SmoothLift
