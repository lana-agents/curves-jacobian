/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.SurfaceGroupAnyPoint
import CurvesJacobian.Scheme.CurvePic
import Belyi.Converse.Pi1InvarianceCurve
import Belyi.P1.BaseChangeIso
import Oka.Analytification.Pi1.BranchedCoordinateProper
import Oka.Analytification.GAGA.Proper.CompactSpace

/-!
# `π₁ᵉᵗ` of a complete curve over `ℚ̄` is the profinite closed surface group

Let `X` be a curve over an algebraically closed field `k` of characteristic zero, algebraic over
`ℚ`, of genus `g`. Then for every geometric point `ξ` of `X`,

  `π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`, the profinite completion of `Π_{g,0} = ⟨a, b | ∏[aᵢ,bᵢ]⟩`

(`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero`).

## Proof

Choose a closed point `p` and a Belyi map `f : X ⟶ ℙ¹` with `f⁻¹(∞) = {p}`
(`CurvesJacobian.exists_isBelyiMap_preimage_infty_eq`); `X ∖ {p} = Spec B` with the coordinate
`t = f^*T`, finite over `k[t]` and étale over `𝔸¹ ∖ {0, 1}`. Base change along an embedding
`k ⊆ ℂ`: `X_ℂ` is a smooth proper curve over `ℂ` (`Belyi.isCurveOver_pullback`), so `X_ℂ^an` is
compact; it is Hausdorff because `f_ℂ : X_ℂ ⟶ ℙ¹_ℂ` is finite and `(ℙ¹_ℂ)^an` is Hausdorff;
`Spec (ℂ ⊗ B) ⟶ X_ℂ` is an open immersion onto the complement of the unique point over `p`
(`CurvesJacobian.ClosedSurface.subsingleton_preimage_fst`). Then oka's
`ComplexAnalytic.exists_fundamentalGroup_analytification_specLFT_mulEquiv_surfaceGroup` gives
`π₁(X_ℂ^an) ≃* Π_{g',0}` with `2g' + c₀ + c₁ + d = 2d + 1`, and Riemann–Hurwitz (as in
`CurvesJacobian.exists_etaleFundamentalGroup_lineCover_equiv`) gives `g' = g`. Finally
`π₁ᵉᵗ(X_ℂ) ≅ π₁(X_ℂ^an)^` (oka's comparison theorem) and `π₁ᵉᵗ(X_ℂ) ≅ π₁ᵉᵗ(X)` (belyi's
`AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective'`).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField ComplexAnalytic
open scoped IntermediateField TensorProduct
open Pi1.Profinite

universe u

namespace CurvesJacobian

namespace ClosedSurface

/-- A separated map into a Hausdorff space has Hausdorff source. -/
theorem t2Space_of_isSeparatedMap {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [T2Space B] {f : A → B} (hf : Continuous f) (hs : IsSeparatedMap f) : T2Space A := by
  refine ⟨fun x y hxy ↦ ?_⟩
  by_cases h : f x = f y
  · exact hs x y h hxy
  · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation h
    exact ⟨f ⁻¹' U, f ⁻¹' V, hU.preimage hf, hV.preimage hf, hxU, hyV, hUV.preimage f⟩

/-- In a pullback square with an isomorphism at the bottom and a subsingleton corner, the top
corner is a subsingleton. -/
theorem subsingleton_of_isPullback {A B C D : Scheme.{u}} {fst : A ⟶ B} {snd : A ⟶ C}
    {f : B ⟶ D} {g : C ⟶ D} (H : IsPullback fst snd f g) (hg : IsIso g) (hB : Subsingleton B) :
    Subsingleton A :=
  haveI := H.isIso_fst_of_isIso hg
  (Scheme.homeoOfIso (asIso fst)).injective.subsingleton

section Fibre

variable {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))]

/-- **Over an algebraically closed field, the base change of a closed point is a single point**:
the fibre of `X_Ω ⟶ X` over a closed point `p` of `X` has at most one point. -/
theorem subsingleton_preimage_fst [IsAlgClosed k]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] {p : X} (hp : IsClosed {p}) :
    ((pullback.fst (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k Ω)).base ⁻¹' {p}).Subsingleton
    := by
  set q := X ↘ Spec (CommRingCat.of k)
  have h := (IsPullback.of_hasPullback q (specAlgebraMap k Ω)).flip
  have H := isPullback_fiberToSpecResidueField_of_isPullback h p
  -- `κ(q p) → κ(p)` is an isomorphism
  have hiso : IsIso (Spec.map (q.residueFieldMap p)) := by
    have hc : IsIso (Spec.map (q.residueFieldMap p) ≫
        (Spec (CommRingCat.of k)).fromSpecResidueField (q p)) := by
      rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← SpecMap_residueFieldIsoBase_inv q p hp]
      infer_instance
    haveI : IsSplitEpi ((Spec (CommRingCat.of k)).fromSpecResidueField (q p)) :=
      IsSplitEpi.mk' ⟨inv (Spec.map (q.residueFieldMap p) ≫
        (Spec (CommRingCat.of k)).fromSpecResidueField (q p)) ≫ Spec.map (q.residueFieldMap p),
        by simp⟩
    haveI := isIso_of_mono_of_isSplitEpi ((Spec (CommRingCat.of k)).fromSpecResidueField (q p))
    exact IsIso.of_isIso_comp_right _ ((Spec (CommRingCat.of k)).fromSpecResidueField (q p))
  -- the fibre of `Spec Ω ⟶ Spec k` has at most one point
  haveI : Subsingleton (Spec (CommRingCat.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have hB : Subsingleton ((specAlgebraMap k Ω).fiber (q p)) :=
    ((specAlgebraMap k Ω).fiberHomeo (q p)).injective.subsingleton
  haveI : Subsingleton ((pullback.fst q (specAlgebraMap k Ω)).fiber p) :=
    subsingleton_of_isPullback H hiso hB
  haveI : Subsingleton ((pullback.fst q (specAlgebraMap k Ω)).base ⁻¹' {p}) :=
    ((pullback.fst q (specAlgebraMap k Ω)).fiberHomeo p).symm.injective.subsingleton
  intro a ha b hb
  exact congrArg Subtype.val (Subsingleton.elim (α := (pullback.fst q (specAlgebraMap k Ω)).base ⁻¹'
    {p}) ⟨a, ha⟩ ⟨b, hb⟩)

end Fibre

/-! ### The base change of a curve to `ℂ` as a scheme locally of finite type over `ℂ` -/

section BaseChange

variable (k : Type u) [Field k] [Algebra k (ULift.{u} ℂ)] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]

/-- `X_ℂ = X ×_k ℂ`. -/
noncomputable abbrev curveBC : Scheme.{u} :=
  pullback (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ))

/-- `X_ℂ` as a scheme locally of finite type over `ℂ`. -/
noncomputable def curveLFT : SchemeLFTℂ.{u} :=
  ⟨Over.mk (pullback.snd (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ))),
    show LocallyOfFiniteType (curveBC k X ↘ Spec (CommRingCat.of (ULift.{u} ℂ))) from
      inferInstance⟩

lemma curveLFT_obj_left : (curveLFT k X).obj.left = curveBC k X := rfl

instance : SmoothOfRelativeDimension 1 (curveLFT k X).obj.hom :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (curveBC k X ↘ Spec (CommRingCat.of (ULift.{u} ℂ))))

instance : ConnectedSpace (curveLFT k X).obj.left := by
  haveI := IsCurveOver.isIntegral (ULift.{u} ℂ) (curveBC k X)
  change ConnectedSpace (curveBC k X)
  exact connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ (curveBC k X)).isConnected

instance : CompactSpace (analytification.obj (curveLFT k X)) :=
  IsProperℂ.compactSpace_analytification
    (show IsProper (curveBC k X ↘ Spec (CommRingCat.of (ULift.{u} ℂ))) from inferInstance)

variable {k X} (f : X ⟶ P1 k) [IsFinite f]
  (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
include hfk

/-- The base change `X_ℂ ⟶ (ℙ¹_k)_ℂ` of `f`. -/
noncomputable def mapBC : curveBC k X ⟶
    pullback (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ)) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hfk]) (by simp)

omit [IsCurveOver k X] [IsFinite f] in
lemma isPullback_mapBC : IsPullback (mapBC f hfk) (pullback.fst _ _) (pullback.fst _ _) f := by
  have e : mapBC f hfk ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [mapBC]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_right ?_ (by rw [mapBC]; exact pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (P1 k ↘ Spec (CommRingCat.of k))
      (specAlgebraMap k (ULift.{u} ℂ))).flip
  rw [e, hfk]
  exact (IsPullback.of_hasPullback (X ↘ Spec (CommRingCat.of k))
    (specAlgebraMap k (ULift.{u} ℂ))).flip

instance isFinite_mapBC : IsFinite (mapBC f hfk) :=
  MorphismProperty.of_isPullback (isPullback_mapBC f hfk).flip ‹_›

omit [IsCurveOver k X] hfk in
/-- The canonical isomorphism `ℙ¹_ℂ ≅ (ℙ¹_k)_ℂ` (belyi `Belyi.P1.isIso_toPullback`). -/
noncomputable def toPullbackIso :
    P1 (ULift.{u} ℂ) ≅ pullback (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ)) :=
  @asIso _ _ _ _ (P1.toPullback k (ULift.{u} ℂ)) (P1.isIso_toPullback k (ULift.{u} ℂ))

/-- The base change `f_ℂ : X_ℂ ⟶ ℙ¹_ℂ` as a morphism of schemes over `ℂ`. -/
noncomputable def mapLFT : curveLFT k X ⟶ projectiveSpace.{u} 1 :=
  ObjectProperty.homMk (Over.homMk (mapBC f hfk ≫ (toPullbackIso (k := k)).inv) (by
    change (mapBC f hfk ≫ (toPullbackIso (k := k)).inv) ≫
      (P1 (ULift.{u} ℂ) ↘ Spec (CommRingCat.of (ULift.{u} ℂ))) = pullback.snd _ _
    rw [Category.assoc, ← P1.toPullback_snd k (ULift.{u} ℂ)]
    change mapBC f hfk ≫ (toPullbackIso (k := k)).inv ≫ (toPullbackIso (k := k)).hom ≫
      pullback.snd _ _ = _
    rw [Iso.inv_hom_id_assoc, mapBC]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)))

instance : IsAffineHom (mapLFT f hfk).hom.left :=
  inferInstanceAs (IsAffineHom (mapBC f hfk ≫ (toPullbackIso (k := k)).inv))

/-- `X_ℂ^an` is Hausdorff: `f_ℂ^an` is a separated map to the Hausdorff space `(ℙ¹)^an`. -/
theorem t2Space_analytification_curveLFT : T2Space (analytification.obj (curveLFT k X)) :=
  t2Space_of_isSeparatedMap (analytification.map (mapLFT f hfk)).toLRSHom.base.hom.continuous
    (isSeparatedMap_analytification_map (mapLFT f hfk))

end BaseChange

/-! ### `X ∖ {p} = Spec B` and its base change -/

section Belyi

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Algebra k (ULift.{u} ℂ)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]
  (f : X ⟶ P1 k) [IsFinite f]

/-- The open immersion `Spec B = X ×_{ℙ¹} 𝔸¹ ⟶ X`. -/
noncomputable def lineCoverι : Spec (CommRingCat.of (lineCoverRing f)) ⟶ X :=
  haveI := isAffine_lineCover (f := f)
  (lineCover f).isoSpec.inv ≫ pullback.fst f (lineι k)

instance : IsOpenImmersion (lineCoverι f) := by
  unfold lineCoverι; infer_instance

omit [IsAlgClosed k] [CharZero k] [Algebra k (ULift.{u} ℂ)] [X.Over (Spec (CommRingCat.of k))]
  [IsCurveOver k X] in
lemma range_lineCoverι {p : X} (hD : ∀ x : X, f.base x = P1.infty k ↔ x = p) :
    Set.range (lineCoverι f).base = {p}ᶜ := by
  haveI := isAffine_lineCover (f := f)
  have h := congrArg (fun U : X.Opens ↦ (U : Set X))
    (Scheme.Hom.opensRange_comp_of_isIso (lineCover f).isoSpec.inv (pullback.fst f (lineι k)))
  simp only [Scheme.Hom.coe_opensRange] at h
  rw [lineCoverι, h, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_pullbackFst]
  ext x
  change f.base x ∈ Set.range (lineι k).base ↔ x ∈ ({p}ᶜ : Set X)
  rw [mem_range_lineι_iff, ne_eq, hD, Set.mem_compl_singleton_iff]

variable (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
include hfk

omit [IsAlgClosed k] [CharZero k] [Algebra k (ULift.{u} ℂ)] [IsCurveOver k X] in
lemma lineCoverι_comp_structMap :
    lineCoverι f ≫ (X ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (lineCoverRing f))) := by
  haveI := isAffine_lineCover (f := f)
  rw [lineCoverι, Category.assoc, ← hfk, pullback.condition_assoc, lineι_structMap,
    ← lineCover_isoSpec_hom_comp (f := f), Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- `Spec (ℂ ⊗ B) ⟶ X_ℂ`, the base change of `lineCoverι`. -/
noncomputable def lineCoverιC :
    Spec (CommRingCat.of (ULift.{u} ℂ ⊗[k] lineCoverRing f)) ⟶ curveBC k X :=
  pullback.lift (FiniteEtale.baseChangeSpec k (ULift.{u} ℂ) (lineCoverRing f) ≫ lineCoverι f)
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : ULift.{u} ℂ →ₐ[k] _ ⊗[k] lineCoverRing f).toRingHom))
    (by
      rw [Category.assoc, lineCoverι_comp_structMap f hfk]
      exact (FiniteEtale.isPullback_baseChangeSpec (k := k) (Ω := ULift.{u} ℂ)
        (R := lineCoverRing f)).w)

omit [IsAlgClosed k] [CharZero k] [IsCurveOver k X] in
lemma isPullback_lineCoverιC :
    IsPullback (lineCoverιC f hfk)
      (FiniteEtale.baseChangeSpec k (ULift.{u} ℂ) (lineCoverRing f)) (pullback.fst _ _)
      (lineCoverι f) := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (X ↘ Spec (CommRingCat.of k))
      (specAlgebraMap k (ULift.{u} ℂ))).flip
  rw [lineCoverιC, pullback.lift_snd, lineCoverι_comp_structMap f hfk]
  exact (FiniteEtale.isPullback_baseChangeSpec (k := k) (Ω := ULift.{u} ℂ)
    (R := lineCoverRing f)).flip

instance : IsOpenImmersion (lineCoverιC f hfk) :=
  MorphismProperty.of_isPullback (isPullback_lineCoverιC f hfk).flip inferInstance

omit [IsAlgClosed k] [CharZero k] [IsCurveOver k X] in
lemma range_lineCoverιC :
    Set.range (lineCoverιC f hfk).base =
      (pullback.fst (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ))).base ⁻¹'
        Set.range (lineCoverι f).base := by
  have h := (isPullback_lineCoverιC f hfk).isoPullback_hom_fst
  have hs : Function.Surjective (isPullback_lineCoverιC f hfk).isoPullback.hom.base :=
    fun y ↦ (Scheme.homeoOfIso (isPullback_lineCoverιC f hfk).isoPullback).surjective y
  rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs.range_eq,
    Set.image_univ, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_pullbackFst]
  rfl

/-- `Spec (ℂ ⊗ B) ⟶ X_ℂ` as a morphism of schemes over `ℂ`. -/
noncomputable def lineCoverιLFT :
    specLFT (ULift.{u} ℂ ⊗[k] lineCoverRing f) ⟶ curveLFT k X :=
  ObjectProperty.homMk (Over.homMk (lineCoverιC f hfk) (pullback.lift_snd _ _ _))

instance : IsOpenImmersion (lineCoverιLFT f hfk).hom.left :=
  inferInstanceAs (IsOpenImmersion (lineCoverιC f hfk))

end Belyi

/-! ### `π₁(X_ℂ^an)` -/

section Analytic

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Algebra k (ULift.{u} ℂ)]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]
  {f : X ⟶ P1 k} [IsFinite f]

omit [IsAlgClosed k] [CharZero k] [IsIntegral X] [IsCurveOver k X] [IsFinite f] in
lemma surjective_fst :
    Function.Surjective
      (pullback.fst (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ))).base := by
  haveI : Surjective (specAlgebraMap k (ULift.{u} ℂ)) := by
    refine ⟨fun x ↦ ?_⟩
    haveI : Subsingleton (Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (ULift.{u} ℂ))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (ULift.{u} ℂ)))
    exact ⟨y, Subsingleton.elim _ _⟩
  haveI : Surjective (pullback.fst (X ↘ Spec (CommRingCat.of k))
      (specAlgebraMap k (ULift.{u} ℂ))) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  exact Surjective.surj

/-- **`π₁` of the analytification of `X_ℂ` is the closed surface group of genus `g`**, for a
Belyi map `f` with a single point `p` over `∞`. -/
theorem nonempty_fundamentalGroup_curveLFT_mulEquiv (hf : IsBelyiMap k f)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) {p : X}
    (hp : IsClosed {p}) (hD : ∀ x : X, f.base x = P1.infty k ↔ x = p)
    (hpgen : p ≠ genericPoint X) (y : analytification.obj (curveLFT k X)) :
    Nonempty (FundamentalGroup (analytification.obj (curveLFT k X)) y ≃*
      Pi1.SurfaceGroup (curveGenus k X).toNat 0) := by
  haveI := isDomain_lineCoverRing hf
  haveI := t2Space_analytification_curveLFT f hfk
  haveI : IsDomain (lineCoverRing f ⊗[k] ULift.{u} ℂ) :=
    Converse.isDomain_tensorProduct_of_isAlgClosed
  haveI : IsDomain (ULift.{u} ℂ ⊗[k] lineCoverRing f) :=
    (Algebra.TensorProduct.comm k (ULift.{u} ℂ) (lineCoverRing f)).toMulEquiv.isDomain
  haveI := smoothOfRelativeDimension_lineCoverRing hfk
  haveI := Converse.FiniteCoord.smoothOfRelativeDimension_baseChange (k := k)
    (Ω := ULift.{u} ℂ) (B := lineCoverRing f) (n := 1)
  have het := hf.branchedData.etale_baseChange (Ω := ULift.{u} ℂ)
  rw [← Converse.branchPoly_zero_one] at het
  -- the unique point of `X_ℂ` over `p`
  obtain ⟨q, hq⟩ := surjective_fst (k := k) (X := X) p
  have hfib : (pullback.fst (X ↘ Spec (CommRingCat.of k))
      (specAlgebraMap k (ULift.{u} ℂ))).base ⁻¹' {p} = {q} :=
    (subsingleton_preimage_fst X hp).eq_singleton_of_mem hq
  have hrange : Set.range (lineCoverιLFT f hfk).hom.left.base = {q}ᶜ := by
    change Set.range (lineCoverιC f hfk).base = _
    rw [range_lineCoverιC, range_lineCoverι f hD, Set.preimage_compl, hfib]
    rfl
  -- the numbers
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hpgen ((hD _).1 h).symm
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have h21 : (2 : k) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : k) = ((1 : ℕ) : k) := by exact_mod_cast h
    exact absurd (Nat.cast_injective this) (by norm_num)
  have hinj := (algebraMap k (ULift.{u} ℂ)).injective
  have hc : (algebraMap k (ULift.{u} ℂ) 2).down ∉ ({0, 1} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ h2 (hinj (by rw [map_zero]; exact ULift.ext _ _ h)),
      fun h ↦ h21 (hinj (by rw [map_one]; exact ULift.ext _ _ h))⟩
  obtain ⟨g, ⟨Φ⟩, hcard⟩ := exists_fundamentalGroup_analytification_specLFT_mulEquiv_surfaceGroup
    (A := ULift.{u} ℂ ⊗[k] lineCoverRing f) (lineCoverιLFT f hfk) q hrange
    (1 ⊗ₜ hf.branchedData.t) hf.branchedData.finite_baseChange het hc y
  have e0 : (0 : ℂ) = (algebraMap k (ULift.{u} ℂ) 0).down := by simp
  have e1 : (1 : ℂ) = (algebraMap k (ULift.{u} ℂ) 1).down := by simp
  have et : hf.branchedData.t = (lineCoverCoord f).t := rfl
  rw [et, e0, e1, fiberCard_algebraMap hη hfk, fiberCard_algebraMap hη hfk,
    fiberCard_algebraMap hη hfk] at hcard
  have hunr : ∀ (Q : Place k X.functionField) (a : k), a ≠ 0 → a ≠ 1 →
      Q.ord (coordFun f hη - algebraMap k X.functionField a) ≤ 1 :=
    fun Q a ha0 ha1 ↦ ord_coordFun_sub_le_one hf hη hfk Q a ha0 ha1
  have hd := card_ord_sub_pos_eq_finrank hx 2 (fun Q ↦ hunr Q 2 h2 h21)
  have hgen := genus_belyi hx hunr
  have hpoles := card_ord_coordFun_neg hη hfk {p} (fun x ↦ (hD x).trans Set.mem_singleton_iff.symm)
    (fun x hx ↦ (Set.mem_singleton_iff.1 hx) ▸ hpgen)
  simp only [map_zero, sub_zero, map_one] at hcard
  rw [hd] at hcard
  simp only [← Nat.card_coe_set_eq, Set.coe_setOf] at hgen
  rw [hpoles, Nat.card_unique (α := ({p} : Set X))] at hgen
  have hg : g = (curveGenus k X).toNat := by
    unfold curveGenus
    omega
  exact ⟨hg ▸ Φ⟩

end Analytic

/-! ### The étale fundamental group -/

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- A curve has a closed point other than its generic point. -/
theorem exists_isClosed_ne_genericPoint (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X] :
    ∃ p : X, IsClosed {p} ∧ p ≠ genericPoint X := by
  obtain ⟨Q⟩ : Nonempty (Place k X.functionField) := inferInstance
  let x := (curvePlaceEquiv k X).symm Q
  exact ⟨x.1, isClosed_closedPoint (k := k) X x, x.2⟩

end Main

end ClosedSurface

/-- **`π₁ᵉᵗ` of a complete curve over `ℚ̄` is the profinite closed surface group**: for a curve
`X` over `k` (algebraically closed, characteristic zero, algebraic over `ℚ`) of genus `g` and every
geometric point `ξ : Spec Ω ⟶ X`, `π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat 0)))) := by
  open ClosedSurface in
  letI : Algebra k (ULift.{u} ℂ) :=
    (IsAlgClosed.lift (R := ℚ) (S := k) (M := ULift.{u} ℂ)).toRingHom.toAlgebra
  haveI := Converse.countable_of_isAlgebraic_rat k
  obtain ⟨p, hp, hpgen⟩ := exists_isClosed_ne_genericPoint k (X := X)
  obtain ⟨f, hf, hD, hfk⟩ := exists_isBelyiMap_preimage_infty_eq k X {p} (Set.finite_singleton p)
    (Set.singleton_nonempty p) (fun x hx ↦ (Set.mem_singleton_iff.1 hx) ▸ hpgen)
  haveI := hf.isFinite
  have hD' : ∀ x : X, f.base x = P1.infty k ↔ x = p := fun x ↦ (hD x).trans Set.mem_singleton_iff
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hpgen ((hD' _).1 h).symm
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  set τ := coordFun f hη
  have hτ0 : τ ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  set U := chartOne k X τ
  set U' := chartZero k X τ
  -- a closed point of `X_ℂ` over `U ∩ U'`
  set g := pullback.fst (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ))
  have hne : (g.base ⁻¹' ((U ⊓ U' : X.Opens) : Set X)).Nonempty := by
    obtain ⟨z, hz⟩ := surjective_fst (k := k) (X := X) (genericPoint X)
    exact ⟨z, by rw [Set.mem_preimage, hz]; exact ⟨genericPoint_mem_chartOne τ,
      genericPoint_mem_chartZero hτ0⟩⟩
  haveI : JacobsonSpace (curveBC k X) :=
    @LocallyOfFiniteType.jacobsonSpace _ _ (curveLFT k X).obj.hom (curveLFT k X).property _
  obtain ⟨z, hzU, hzc⟩ := nonempty_inter_closedPoints hne
    ((U ⊓ U').isOpen.preimage g.base.hom.continuous).isLocallyClosed
  obtain ⟨y, hy⟩ := (mem_range_analytificationπ_base_iff (curveLFT k X) z).2 hzc
  set ξC := geometricPoint (curveLFT k X) y
  have hξC : ∀ w, (ξC ≫ g).base w ∈ U ⊓ U' := fun w ↦ by
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    change g.base (ξC.base w) ∈ _
    rw [show ξC.base w = z from (geometricPoint_apply (curveLFT k X) y w).trans hy]
    exact hzU
  have hbij := FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective' k (ULift.{u} ℂ) X U U'
    (isAffineOpen_chartOne hx) (isAffineOpen_chartZero hx) (chartOne_sup_chartZero τ) ξC hξC
  -- `π₁ᵉᵗ(X_ℂ) ≃ₜ* π₁ᵉᵗ(X)`
  let F := FiniteEtale.fundamentalGroupMap g (rfl : ξC ≫ g = _)
  let e : π₁ᵉᵗ(ξC) ≃* π₁ᵉᵗ(ξC ≫ g) := MulEquiv.ofBijective F.toMonoidHom hbij
  let h : π₁ᵉᵗ(ξC) ≃ₜ π₁ᵉᵗ(ξC ≫ g) :=
    Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) F.continuous_toFun
  let E₁ : π₁ᵉᵗ(ξC) ≃ₜ* π₁ᵉᵗ(ξC ≫ g) :=
    { e with continuous_toFun := h.continuous_toFun, continuous_invFun := h.continuous_invFun }
  -- the comparison theorem
  obtain ⟨Φ⟩ := nonempty_fundamentalGroup_curveLFT_mulEquiv hf hfk hp hD' hpgen y
  let E₂ := etaleFundamentalGroupEquivCompletion (X := curveLFT k X) y
  haveI : ConnectedSpace X :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ X).isConnected
  obtain ⟨E₀⟩ := FiniteEtale.nonempty_fundamentalGroup_continuousMulEquiv ξ (ξC ≫ g)
  exact ⟨E₀.trans (E₁.symm.trans (E₂.trans (completionCongr (Φ.trans MulEquiv.ulift.symm))))⟩


/-- **`π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`** with pi1's `Pi1.ProfiniteSurfaceGroup` (universe `0`), at every
geometric point. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero₀ {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{0}}
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat 0) := by
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero (k := k) ξ
  exact ⟨e.trans (Pi1.Profinite.completionCongr MulEquiv.ulift)⟩

end CurvesJacobian
