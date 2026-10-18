/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverOpen
import CurvesJacobian.Cusp.CuspConj
import CurvesJacobian.Cusp.LineCuspInertia
import CurvesJacobian.Galois.BelyiCoordinate
import CurvesJacobian.Galois.NewCoordinate
import Belyi.Converse.PuncturedLineBelyi

/-!
# The part of a curve over `ℙ¹ ∖ {0, 1, ∞}`

Let `f : X ⟶ ℙ¹_k` be a finite morphism from a curve with `f(η_X) ∈ ℙ¹ ∖ {0, 1, ∞}`. Then
`U' = f⁻¹(ℙ¹ ∖ {0, 1, ∞})` (`CurvesJacobian.Cusp.cuspOpen`) maps to
`Spec k[t, 1/(t(t-1))]` (`CurvesJacobian.Cusp.cuspCover`), finitely, and finite étale for a Belyi
map (`CurvesJacobian.Cusp.isFiniteEtale_cuspCover`).

In the Galois model (`D`, `eL`) with coordinate `t_f = eL(f^* t)` (`CurvesJacobian.Cusp.belyiT`):

* `CurvesJacobian.Cusp.genericL_cuspCover`: the geometric generic point of `U'` maps to the
  geometric generic point `lineGen` of the line for the coordinate `t_f`;
* `CurvesJacobian.Cusp.isCentredOn_cuspOpen_iff`: a place `W ⊇ k` is centred on `U'` iff
  `t_f, 1/(t_f (t_f - 1)) ∈ W` (`Γ(U')` is integral over `k[t, 1/(t(t-1))]`);
* `CurvesJacobian.Cusp.fundamentalGroupMap_cuspCover_chartHom`: `π₁ᵉᵗ(U') → π₁ᵉᵗ(line)`
  intertwines the Galois actions of `H = Gal(Ω / L)` and `Gal(Ω / k(t_f))`;
* `CurvesJacobian.Cusp.mem_HL_of_lineGalois_mem_range`: an element of `Gal(Ω / k(t_f))` whose
  image lies in the image of `π₁ᵉᵗ(U')` fixes `L`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve
open Pi1.Orbifold

noncomputable section

namespace CurvesJacobian.Cusp

universe u

section Cover

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ P1 k)

/-- **`U' = f⁻¹(ℙ¹ ∖ {0, 1, ∞})`.** -/
abbrev cuspOpen : X.Opens := f ⁻¹ᵁ (puncturedι k).opensRange

/-- **`U' ⟶ Spec k[t, 1/(t(t-1))]`**, the restriction of `f`. -/
def cuspCover : (cuspOpen f : Scheme.{u}) ⟶ Spec (.of (lineRing k)) :=
  (f ∣_ (puncturedι k).opensRange) ≫ (puncturedι k).isoOpensRange.inv

omit [IsIntegral X] in
@[reassoc]
lemma cuspCover_comp_puncturedι : cuspCover f ≫ puncturedι k = (cuspOpen f).ι ≫ f := by
  rw [cuspCover, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]

omit [IsIntegral X] in
/-- `U'` is finite étale over `ℙ¹ ∖ {0, 1, ∞}` for a Belyi map. -/
lemma isFiniteEtale_cuspCover [CharZero k] [IsAlgClosed k] [X.Over (Spec (.of k))]
    [IsCurveOver k X] (hf : IsBelyiMap k f) : IsFiniteEtale (cuspCover f) := by
  haveI := hf.isFinite
  have he := hf.etale_morphismRestrict_puncturedLine
  rw [← opensRange_puncturedι] at he
  haveI : IsFinite (f ∣_ (puncturedι k).opensRange) :=
    IsZariskiLocalAtTarget.restrict hf.isFinite _
  haveI : Etale (f ∣_ (puncturedι k).opensRange) := he
  haveI : IsFiniteEtale (f ∣_ (puncturedι k).opensRange) := ⟨⟩
  haveI : IsFiniteEtale (puncturedι k).isoOpensRange.inv :=
    MorphismProperty.of_isIso @IsFiniteEtale _
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

variable [Nonempty (cuspOpen f)]

lemma range_fromSpecStalk_comp_subset_puncturedι :
    Set.range (X.fromSpecStalk (genericPoint X) ≫ f).base ⊆ Set.range (puncturedι k).base := by
  rintro _ ⟨z, rfl⟩
  have hz : z = IsLocalRing.closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  rw [hz, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  exact genericPoint_mem_of_nonempty (cuspOpen f)

/-- **`k[t, 1/(t(t-1))] → K(X)`**, `t ↦ f^* t`. -/
def eLine : CommRingCat.of (lineRing k) ⟶ X.functionField :=
  Spec.preimage (IsOpenImmersion.lift (puncturedι k) _
    (range_fromSpecStalk_comp_subset_puncturedι f))

@[reassoc]
lemma spec_map_eLine_comp :
    Spec.map (eLine f) ≫ puncturedι k = X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [eLine, Spec.map_preimage, IsOpenImmersion.lift_fac]

lemma eLine_algebraMap (hη : f.base (genericPoint X) ≠ P1.infty k) :
    CommRingCat.ofHom (algebraMap (Polynomial k) (lineRing k)) ≫ eLine f = coordHom f hη := by
  apply Spec.map_injective
  rw [← cancel_mono (lineι k), Spec.map_comp, Category.assoc,
    ← puncturedι_eq_comp_lineι, spec_map_eLine_comp, spec_map_coordHom_comp_lineι]

lemma eLine_lineT (hη : f.base (genericPoint X) ≠ P1.infty k) :
    (eLine f).hom (lineT k) = coordFun f hη := by
  rw [coordFun, ← eLine_algebraMap f hη]
  rfl

lemma eLine_C [X.Over (Spec (.of k))] (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (c : k) :
    (eLine f).hom (algebraMap k (lineRing k) c) = algebraMap k X.functionField c := by
  rw [← coordHom_C hη hfk c, ← eLine_algebraMap f hη]
  rfl

/-- **`Γ(U')` is finite over `k[t, 1/(t(t-1))]`**, compatibly with `eLine`. -/
lemma exists_finite_lift [IsFinite f] :
    ∃ φ : CommRingCat.of (lineRing k) ⟶ Γ(X, cuspOpen f), φ.hom.Finite ∧
      φ ≫ X.germToFunctionField (cuspOpen f) = eLine f := by
  set U := cuspOpen f with hUdef
  have hU : IsAffineOpen U := (isAffineOpen_opensRange (puncturedι k)).preimage f
  have hr : Set.range (hU.fromSpec ≫ f).base ⊆ Set.range (puncturedι k).base := by
    rintro _ ⟨y, rfl⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    exact hy
  set ρ := IsOpenImmersion.lift (puncturedι k) (hU.fromSpec ≫ f) hr with hρ
  set φ : CommRingCat.of (lineRing k) ⟶ Γ(X, U) := Spec.preimage ρ with hφdef
  have hφ : Spec.map φ = ρ := Spec.map_preimage ρ
  have hgen : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  refine ⟨φ, ?_, ?_⟩
  · have hρ' : ρ = hU.isoSpec.inv ≫ (f ∣_ (puncturedι k).opensRange) ≫
        (puncturedι k).isoOpensRange.inv := by
      rw [← cancel_mono (puncturedι k), IsOpenImmersion.lift_fac, Category.assoc, Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
        IsAffineOpen.isoSpec_inv_ι]
    have : IsFinite ρ := by
      rw [hρ']
      haveI : IsFinite (f ∣_ (puncturedι k).opensRange) :=
        IsZariskiLocalAtTarget.restrict ‹IsFinite f› _
      infer_instance
    rw [← hφ] at this
    exact (IsFinite.SpecMap_iff φ).mp this
  · rw [← Spec.map_inj, Spec.map_comp, hφ, ← cancel_mono (puncturedι k), Category.assoc,
      IsOpenImmersion.lift_fac, spec_map_eLine_comp, ← hU.fromSpecStalk_eq_fromSpecStalk hgen]
    rfl

end Cover

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X] (eL : X.functionField ≃+* D.L)
  (f : X ⟶ P1 k) [Nonempty (cuspOpen f)] (hη : f.base (genericPoint X) ≠ P1.infty k)

/-- **The coordinate `t_f = eL(f^* t) ∈ Ω`.** -/
def belyiT : Ω := ((eL (coordFun f hη) : D.L) : Ω)

omit [X.Over (Spec (.of k))] [Nonempty (cuspOpen f)] in
lemma belyiT_mem : belyiT D eL f hη ∈ D.L := (eL (coordFun f hη)).2

variable (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))

/-- The ring map `k[t, 1/(t(t-1))] → Ω` of the generic point of `U'`. -/
abbrev eLineΩ : lineRing k →+* Ω :=
  (algebraMap D.L Ω).comp (eL.toRingHom.comp (eLine f).hom)

include hk hfk in
lemma eLineΩ_eq (ht : Transcendental k (belyiT D eL f hη)) :
    eLineΩ D eL f = (lineToΩ ht).toRingHom := by
  refine lineRing_ringHom_ext (fun c ↦ ?_) ?_
  · change ((eL ((eLine f).hom (algebraMap k (lineRing k) c)) : D.L) : Ω) = _
    rw [eLine_C f hη hfk, hk]
    exact ((lineToΩ ht).commutes c).symm
  · change ((eL ((eLine f).hom (lineT k)) : D.L) : Ω) = _
    rw [eLine_lineT f hη, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lineToΩ_lineT]
    rfl

include hk hfk in
/-- **The generic point of `U'` lies over the generic point of the line** (coordinate `t_f`). -/
theorem genericL_cuspCover (ht : Transcendental k (belyiT D eL f hη)) :
    (specPoint D.L Ω ≫ genericL D X eL (cuspOpen f)) ≫ cuspCover f = lineGen ht := by
  rw [← cancel_mono (puncturedι k), Category.assoc, cuspCover_comp_puncturedι,
    ← Category.assoc, specPoint_genericL_ι, Category.assoc, genericLX, Category.assoc,
    ← spec_map_eLine_comp, lineGen_eq, ← eLineΩ_eq D eL f hη hk hfk ht]
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

omit [X.Over (Spec (.of k))] in
/-- **Places centred on `U'`**: `W ⊇ k` is centred on `U' = f⁻¹(ℙ¹ ∖ {0, 1, ∞})` iff it contains
the image of `k[t, 1/(t(t-1))]`. -/
theorem isCentredOn_cuspOpen_iff [IsFinite f] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) :
    IsCentredOn D X eL (cuspOpen f) W ↔ ∀ x : lineRing k, eLineΩ D eL f x ∈ W := by
  obtain ⟨φ, hφf, hφ⟩ := exists_finite_lift f
  constructor
  · rintro ⟨-, hW⟩ x
    have := hW (φ.hom x)
    rwa [← CommRingCat.comp_apply, hφ] at this
  · intro hW
    refine ⟨hkW, fun b ↦ ?_⟩
    letI := φ.hom.toAlgebra
    let g : lineRing k →+* W.toSubring := (eLineΩ D eL f).codRestrict W.toSubring hW
    let ψ : Γ(X, cuspOpen f) →+* Ω :=
      (algebraMap D.L Ω).comp (eL.toRingHom.comp (X.germToFunctionField (cuspOpen f)).hom)
    have hcomp : (algebraMap W.toSubring Ω).comp g = ψ.comp (algebraMap (lineRing k) _) := by
      ext x
      change eLineΩ D eL f x = ψ (φ.hom x)
      simp only [ψ, eLineΩ, RingHom.comp_apply, ← hφ]
      rfl
    have hint : IsIntegral (lineRing k) b := hφf.to_isIntegral b
    have hb : IsIntegral W.toSubring (ψ b) := hint.map_of_comp_eq g ψ hcomp
    haveI : IsIntegrallyClosedIn W.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn W Ω)
    obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hb
    change ψ b ∈ W
    rw [← hy]
    exact y.2

end Galois


section Action

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X] (eL : X.functionField ≃+* D.L)
  (f : X ⟶ P1 k) [Nonempty (cuspOpen f)] (hη : f.base (genericPoint X) ≠ P1.infty k)
  [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] (hH : D.H ≤ D.HL)
  (ht : Transcendental k (belyiT D eL f hη)) [IsGalois (K₀ k (belyiT D eL f hη)) Ω]
  (hbase : (specPoint D.L Ω ≫ genericL D X eL (cuspOpen f)) ≫ cuspCover f = lineGen ht)

/-- An element of `H = Gal(Ω / L)` as an automorphism of `Ω` over `k(t_f)`. -/
def toLine (σ : D.H) : Ω ≃ₐ[K₀ k (belyiT D eL f hη)] Ω :=
  AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv)
    (fun c ↦ fix_of_mem_H hH σ (K₀_le_of_mem (belyiT_mem D eL f hη) c.2))

omit [X.Over (Spec (.of k))] [Nonempty (cuspOpen f)] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω]
  [IsGalois (K₀ k (belyiT D eL f hη)) Ω] in
@[simp] lemma toLine_apply (σ : D.H) (x : Ω) :
    toLine D eL f hη hH σ x = (σ : Ω ≃ₐ[K₀ k t] Ω) x := rfl

omit [X.Over (Spec (.of k))] [Nonempty (cuspOpen f)] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω]
  [IsGalois (K₀ k (belyiT D eL f hη)) Ω] in
lemma toLine_mul (σ τ : D.H) :
    toLine D eL f hη hH (σ * τ) = toLine D eL f hη hH σ * toLine D eL f hη hH τ :=
  AlgEquiv.ext fun _ ↦ rfl

omit [X.Over (Spec (.of k))] in
include hbase in
/-- **`π₁ᵉᵗ(U') → π₁ᵉᵗ(line)` intertwines the Galois actions.** -/
theorem fundamentalGroupMap_cuspCover_chartHom (σ : D.H) :
    fundamentalGroupMap (cuspCover f) hbase (D.chartHom hH (genericL D X eL (cuspOpen f)) σ) =
      lineGalois ht (toLine D eL f hη hH σ) := by
  rw [GaloisData.chartHom_apply, fundamentalGroupMap_galoisAction D.L _ (cuspCover f) rfl hbase
    (by rw [← Category.assoc]; exact hbase)]
  exact galoisAction_eq_of_apply_eq D.L _ _ _ _ _ _ fun _ ↦ rfl

omit [X.Over (Spec (.of k))] [IsGalois (K₀ k t) Ω] in
include hbase in
/-- **Galois elements stabilising the generic point of `U'` fix `L`.** If the image of
`σ ∈ Gal(Ω / k(t_f))` in `π₁ᵉᵗ(line)` lies in the image of `π₁ᵉᵗ(U')`, then `σ` fixes `L`. -/
theorem apply_eq_of_lineGalois_mem_range [IsFiniteEtale (cuspCover f)]
    (σ : Ω ≃ₐ[K₀ k (belyiT D eL f hη)] Ω)
    (hσ : lineGalois ht σ ∈ (fundamentalGroupMap (cuspCover f) hbase).toMonoidHom.range)
    (x : D.L) : σ (x : Ω) = x := by
  rw [range_fundamentalGroupMap_of_isFiniteEtale', MulAction.mem_stabilizer_iff] at hσ
  have h1 := congrArg (fun y ↦ (fiberObjEquivHom (lineGen ht) (coverObj (cuspCover f)) y).left) hσ
  change (fiberObjEquivHom _ _ ((lineGalois ht σ).hom.app _ _)).left = _ at h1
  rw [lineGalois, galoisAction_hom_app_left, coverPt, Equiv.apply_symm_apply] at h1
  simp only [Over.homMk_left] at h1
  have h1' : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      (specPoint D.L Ω ≫ genericL D X eL (cuspOpen f)) =
      specPoint D.L Ω ≫ genericL D X eL (cuspOpen f) := h1
  -- compose with `U' ⟶ X` and cancel the monomorphism `Spec K(X) ⟶ X`
  have h2 : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ specPoint D.L Ω ≫
      Spec.map (CommRingCat.ofHom eL.toRingHom) ≫ X.fromSpecStalk (genericPoint X) =
      specPoint D.L Ω ≫ Spec.map (CommRingCat.ofHom eL.toRingHom) ≫
        X.fromSpecStalk (genericPoint X) := by
    have := h1' =≫ (cuspOpen f).ι
    simpa only [Category.assoc, genericL_ι, genericLX] using this
  have h3 : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ specPoint D.L Ω ≫
      Spec.map (CommRingCat.ofHom eL.toRingHom) =
      specPoint D.L Ω ≫ Spec.map (CommRingCat.ofHom eL.toRingHom) := by
    rw [← cancel_mono (X.fromSpecStalk (genericPoint X))]
    simpa only [Category.assoc] using h2
  have h4 : (CommRingCat.ofHom eL.toRingHom ≫ CommRingCat.ofHom (algebraMap D.L Ω)) ≫
      CommRingCat.ofHom (σ : Ω →+* Ω) =
      CommRingCat.ofHom eL.toRingHom ≫ CommRingCat.ofHom (algebraMap D.L Ω) :=
    Spec.map_injective (by simpa only [Spec.map_comp, Category.assoc] using h3)
  have h5 := congrArg (fun φ ↦ φ.hom (eL.symm x)) h4
  simpa using h5

end Action


section Line

open Polynomial

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

lemma lineToK₀_algebraMap (ht : Transcendental k t) (p : k[X]) :
    lineToK₀ ht (algebraMap k[X] (lineRing k) p) = aeval (tK₀ k t) p := by
  have : (lineToK₀ ht).comp (IsScalarTower.toAlgHom k k[X] (lineRing k)) = aeval (tK₀ k t) := by
    refine Polynomial.algHom_ext ?_
    rw [AlgHom.comp_apply, aeval_X]
    exact lineLift_lineT _ _
  exact DFunLike.congr_fun this p

lemma coe_aeval_tK₀ (p : k[X]) : ((aeval (tK₀ k t) p : K₀ k t) : Ω) = aeval t p := by
  have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k (K₀ k t) Ω) (tK₀ k t) p
  exact this.symm

lemma lineToK₀_injective (ht : Transcendental k t) : Function.Injective (lineToK₀ ht) := by
  have hcomap : (RingHom.ker (lineToK₀ ht).toRingHom).comap (algebraMap k[X] (lineRing k)) = ⊥ := by
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      lineToK₀_algebraMap ht, Ideal.mem_bot]
    constructor
    · intro h
      have h' := congrArg (fun z : K₀ k t ↦ (z : Ω)) h
      simp only [coe_aeval_tK₀, ZeroMemClass.coe_zero] at h'
      by_contra hp
      exact ht ⟨p, hp, h'⟩
    · rintro rfl
      simp
  have := IsLocalization.map_under (Submonoid.powers (X * (X - 1) : k[X])) (lineRing k)
    (RingHom.ker (lineToK₀ ht).toRingHom)
  rw [show Ideal.under k[X] (RingHom.ker (lineToK₀ ht).toRingHom) = ⊥ from hcomap,
    Ideal.map_bot] at this
  exact (RingHom.injective_iff_ker_eq_bot _).2 this.symm

variable [IsSepClosed Ω] [IsGalois (K₀ k t) Ω]

/-- Surjectivity of the Galois action does not depend on the name of the geometric point. -/
lemma galoisAction_surjective_congr (F : Type u) [Field F] [Algebra F Ω] [IsGalois F Ω]
    {Y : Scheme.{u}} (j : Spec (.of F) ⟶ Y) {η η' : Spec (.of Ω) ⟶ Y}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η)
    (h' : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η')
    (hs : Function.Surjective (FiniteEtale.galoisAction F j h)) :
    Function.Surjective (FiniteEtale.galoisAction F j h') := by
  obtain rfl : η = η' := h.symm.trans h'
  exact hs

/-- **The Galois action on `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞})` is surjective** (`k[t, 1/(t(t-1))]` is
integrally closed in `k(t)`). -/
theorem lineGalois_surjective (ht : Transcendental k t) : Function.Surjective (lineGalois ht) := by
  letI : Algebra (lineRing k) (K₀ k t) := (lineToK₀ ht).toRingHom.toAlgebra
  letI : Algebra (lineRing k) Ω := (lineToΩ ht).toRingHom.toAlgebra
  haveI : IsScalarTower (lineRing k) (K₀ k t) Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hinj : Function.Injective (algebraMap (lineRing k) (K₀ k t)) := lineToK₀_injective ht
  haveI : FaithfulSMul (lineRing k) (K₀ k t) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (lineRing k) (K₀ k t) := by
    refine IsFractionRing.of_field _ _ fun z ↦ ?_
    obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.1 z.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := hs
    refine ⟨algebraMap k[X] (lineRing k) p, algebraMap k[X] (lineRing k) q, Subtype.ext ?_⟩
    change (z : Ω) = ((lineToK₀ ht (algebraMap _ _ p) / lineToK₀ ht (algebraMap _ _ q) :
      K₀ k t) : Ω)
    rw [IntermediateField.coe_div, lineToK₀_algebraMap, lineToK₀_algebraMap, coe_aeval_tK₀,
      coe_aeval_tK₀]
    exact hrs
  haveI : IsIntegrallyClosed (lineRing k) :=
    isIntegrallyClosed_of_isLocalization (lineRing k) (Submonoid.powers (X * (X - 1) : k[X]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero 1)))
  have hint : ∀ x : K₀ k t, IsIntegral (lineRing k) x →
      x ∈ Set.range (algebraMap (lineRing k) (K₀ k t)) := fun x hx ↦
    (IsIntegrallyClosed.isIntegral_iff (K := K₀ k t)).1 hx
  have hs := FiniteEtale.galoisAction_surjective (F := K₀ k t) (Ω := Ω) (lineRing k) hinj hint
  exact galoisAction_surjective_congr (K₀ k t) _ _ rfl hs

end Line

section LineInertia

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} [IsSepClosed Ω]
  [IsGalois (K₀ k t) Ω]

/-- **Conjugating the inertia group of a place** of `Ω` over `k(t)`. -/
lemma lineInertia_comap (ht : Transcendental k t) (W : ValuationSubring Ω)
    (σ : Ω ≃ₐ[K₀ k t] Ω) :
    lineInertia ht (W.comap (σ.symm : Ω →+* Ω)) =
      (lineInertia ht W).map (MulAut.conj (lineGalois ht σ)).toMonoidHom := by
  rw [lineInertia_eq_map, lineInertia_eq_map, Subgroup.map_map]
  have : GaloisPi1.inertiaSubgroup (P := K₀ k t) (W.comap (σ.symm : Ω →+* Ω)) =
      (GaloisPi1.inertiaSubgroup (P := K₀ k t) W).map (MulAut.conj σ).toMonoidHom := by
    ext τ
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    change τ ∈ GaloisPi1.inertia _ ↔ _
    rw [GaloisPi1.mem_inertia_comap_iff]
    constructor
    · intro h
      exact ⟨σ⁻¹ * τ * σ, h, by group⟩
    · rintro ⟨τ', h, rfl⟩
      change τ' ∈ GaloisPi1.inertia W at h
      simpa [mul_assoc] using h
  rw [this, Subgroup.map_map]
  congr 1
  ext τ
  simp [MulAut.conj_apply, map_mul]

end LineInertia

end CurvesJacobian.Cusp
