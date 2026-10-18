/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiCover
import CurvesJacobian.Cusp.LineS
import CurvesJacobian.Galois.GenericEtale

/-!
# The part of a curve over `𝔸¹ ∖ S` for a finite map to `ℙ¹`

Let `f : X ⟶ ℙ¹_k` be a finite morphism from an integral scheme with `f(η_X) ≠ ∞` and `S ⊆ k` a
finite set. Then `U'_S = f⁻¹(𝔸¹ ∖ S)` (`CurvesJacobian.Cusp.coverOpenS`) maps finitely to
`Spec k[t, 1/P_S(t)]` (`CurvesJacobian.Cusp.coverMapS`, `P_S = ∏_{a ∈ S} (X - a)`). This
generalises `CurvesJacobian/Cusp/BelyiCover.lean` (Belyi maps, `S = {0, 1}`).

* `CurvesJacobian.Cusp.exists_finset_isFiniteEtale_coverMapS`: for `X` a curve over an
  algebraically closed field of characteristic zero, there is a nonempty finite `S₀ ⊆ k` such
  that `U'_T → Spec k[t, 1/P_T(t)]` is finite étale for every `T ⊇ S₀` (generic étaleness,
  `CurvesJacobian.FiniteCoord.exists_etale_branchPolyOf_nonempty`, applied to the affine part
  `f⁻¹(𝔸¹) = Spec B`).

In the Galois model (`D`, `eL`) with coordinate `t_f = eL(f^* t)` (`CurvesJacobian.Cusp.coverT`):

* `CurvesJacobian.Cusp.genericL_coverMapS`: the geometric generic point of `U'_S` maps to the
  geometric generic point `lineGenS` of the line for the coordinate `t_f`;
* `CurvesJacobian.Cusp.isCentredOn_coverOpenS_iff'`: a place `W ⊇ k` is centred on `U'_S` iff
  `t_f ∈ W` and `P_S(t_f)⁻¹ ∈ W`;
* `CurvesJacobian.Cusp.fundamentalGroupMap_coverMapS_chartHom`: `π₁ᵉᵗ(U'_S) → π₁ᵉᵗ(line)`
  intertwines the Galois actions of `H = Gal(Ω / L)` and `Gal(Ω / k(t_f))`;
* `CurvesJacobian.Cusp.apply_eq_of_lineGaloisS_mem_range`: an element of `Gal(Ω / k(t_f))` whose
  image lies in the image of `π₁ᵉᵗ(U'_S)` fixes `L`;
* `CurvesJacobian.Cusp.map_cuspInertia_coverMapS`: the cuspidal inertia groups of `U'_S` are the
  intersections of the inertia groups of the line with the image of `π₁ᵉᵗ(U'_S)`;
* `CurvesJacobian.Cusp.lineGaloisS_surjective`, `CurvesJacobian.Cusp.lineInertiaS_eq_map`,
  `CurvesJacobian.Cusp.lineInertiaS_comap`: the Galois action on `π₁ᵉᵗ(𝔸¹ ∖ S)` is surjective,
  and the inertia groups are images of the Galois inertia groups (and conjugate accordingly).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve
open Pi1.Orbifold

noncomputable section

namespace CurvesJacobian.Cusp

universe u

/-! ### The open immersion `𝔸¹ ∖ S ⟶ ℙ¹` -/

section LineIota

variable (k : Type u) [Field k] (S : Finset k)

/-- **The open immersion `𝔸¹ ∖ S = Spec k[t, 1/P_S(t)] ⟶ ℙ¹`.** -/
def lineSι : Spec (.of (lineRingS S)) ⟶ P1 k :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS S))) ≫ lineι k

lemma lineSι_eq :
    lineSι k S = Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS S))) ≫
      lineι k := rfl

instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial k) (lineRingS S)))) :=
  IsOpenImmersion.of_isLocalization (polyS S)

instance : IsOpenImmersion (lineSι k S) := by
  rw [lineSι_eq]
  infer_instance

/-- A point of `Spec k[t]` lies in `𝔸¹ ∖ S` iff `P_S ∉ 𝔭`. -/
lemma mem_range_specMap_lineRingS_iff (x : PrimeSpectrum (Polynomial k)) :
    x ∈ Set.range (PrimeSpectrum.comap (algebraMap (Polynomial k) (lineRingS S))) ↔
      polyS S ∉ x.asIdeal := by
  rw [PrimeSpectrum.localization_away_comap_range (lineRingS S) (polyS S)]
  rfl

end LineIota

/-! ### The cover `U'_S ⟶ 𝔸¹ ∖ S` -/

section Cover

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ P1 k) (S : Finset k)

/-- **`U'_S = f⁻¹(𝔸¹ ∖ S)`.** -/
abbrev coverOpenS : X.Opens := f ⁻¹ᵁ (lineSι k S).opensRange

/-- **`U'_S ⟶ Spec k[t, 1/P_S(t)]`**, the restriction of `f`. -/
def coverMapS : (coverOpenS f S : Scheme.{u}) ⟶ Spec (.of (lineRingS S)) :=
  (f ∣_ (lineSι k S).opensRange) ≫ (lineSι k S).isoOpensRange.inv

omit [IsIntegral X] in
@[reassoc]
lemma coverMapS_comp_lineSι : coverMapS f S ≫ lineSι k S = (coverOpenS f S).ι ≫ f := by
  rw [coverMapS, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]

omit [IsIntegral X] in
/-- `U'_S ⟶ 𝔸¹ ∖ S` is finite. -/
instance isFinite_coverMapS [IsFinite f] : IsFinite (coverMapS f S) := by
  haveI : IsFinite (f ∣_ (lineSι k S).opensRange) :=
    IsZariskiLocalAtTarget.restrict ‹IsFinite f› _
  rw [coverMapS]
  infer_instance

/-- `U'_S` is nonempty if `f` is dominant (it contains the generic point). -/
lemma genericPoint_mem_coverOpenS [IsDominant f] : genericPoint X ∈ coverOpenS f S := by
  change f.base (genericPoint X) ∈ (lineSι k S).opensRange
  rw [f.base_genericPoint]
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum (lineRingS S)) := inferInstance
  haveI : Nonempty (lineSι k S).opensRange :=
    ⟨⟨(lineSι k S).base (show Spec (.of (lineRingS S)) from x), x, rfl⟩⟩
  exact genericPoint_mem_of_nonempty _

lemma nonempty_coverOpenS [IsDominant f] : Nonempty (coverOpenS f S) :=
  ⟨⟨_, genericPoint_mem_coverOpenS f S⟩⟩

variable [Nonempty (coverOpenS f S)]

lemma range_fromSpecStalk_comp_subset_lineSι :
    Set.range (X.fromSpecStalk (genericPoint X) ≫ f).base ⊆ Set.range (lineSι k S).base := by
  rintro _ ⟨z, rfl⟩
  have hz : z = IsLocalRing.closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  rw [hz, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  exact genericPoint_mem_of_nonempty (coverOpenS f S)

/-- **`k[t, 1/P_S(t)] → K(X)`**, `t ↦ f^* t`. -/
def eLineS : CommRingCat.of (lineRingS S) ⟶ X.functionField :=
  Spec.preimage (IsOpenImmersion.lift (lineSι k S) _
    (range_fromSpecStalk_comp_subset_lineSι f S))

@[reassoc]
lemma spec_map_eLineS_comp :
    Spec.map (eLineS f S) ≫ lineSι k S = X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [eLineS, Spec.map_preimage, IsOpenImmersion.lift_fac]

lemma eLineS_algebraMap (hη : f.base (genericPoint X) ≠ P1.infty k) :
    CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS S)) ≫ eLineS f S =
      coordHom f hη := by
  apply Spec.map_injective
  rw [← cancel_mono (lineι k), Spec.map_comp, Category.assoc, ← lineSι_eq,
    spec_map_eLineS_comp, spec_map_coordHom_comp_lineι]

lemma eLineS_lineTS (hη : f.base (genericPoint X) ≠ P1.infty k) :
    (eLineS f S).hom (lineTS S) = coordFun f hη := by
  rw [coordFun, ← eLineS_algebraMap f S hη]
  rfl

lemma eLineS_C [X.Over (Spec (.of k))] (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (c : k) :
    (eLineS f S).hom (algebraMap k (lineRingS S) c) = algebraMap k X.functionField c := by
  rw [← coordHom_C hη hfk c, ← eLineS_algebraMap f S hη]
  rfl

/-- **`Γ(U'_S)` is finite over `k[t, 1/P_S(t)]`**, compatibly with `eLineS`. -/
lemma exists_finite_liftS [IsFinite f] :
    ∃ φ : CommRingCat.of (lineRingS S) ⟶ Γ(X, coverOpenS f S), φ.hom.Finite ∧
      φ ≫ X.germToFunctionField (coverOpenS f S) = eLineS f S := by
  set U := coverOpenS f S with hUdef
  have hU : IsAffineOpen U := (isAffineOpen_opensRange (lineSι k S)).preimage f
  have hr : Set.range (hU.fromSpec ≫ f).base ⊆ Set.range (lineSι k S).base := by
    rintro _ ⟨y, rfl⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    exact hy
  set ρ := IsOpenImmersion.lift (lineSι k S) (hU.fromSpec ≫ f) hr with hρ
  set φ : CommRingCat.of (lineRingS S) ⟶ Γ(X, U) := Spec.preimage ρ with hφdef
  have hφ : Spec.map φ = ρ := Spec.map_preimage ρ
  have hgen : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  refine ⟨φ, ?_, ?_⟩
  · have hρ' : ρ = hU.isoSpec.inv ≫ (f ∣_ (lineSι k S).opensRange) ≫
        (lineSι k S).isoOpensRange.inv := by
      rw [← cancel_mono (lineSι k S), IsOpenImmersion.lift_fac, Category.assoc, Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
        IsAffineOpen.isoSpec_inv_ι]
    have : IsFinite ρ := by
      rw [hρ']
      haveI : IsFinite (f ∣_ (lineSι k S).opensRange) :=
        IsZariskiLocalAtTarget.restrict ‹IsFinite f› _
      infer_instance
    rw [← hφ] at this
    exact (IsFinite.SpecMap_iff φ).mp this
  · rw [← Spec.map_inj, Spec.map_comp, hφ, ← cancel_mono (lineSι k S), Category.assoc,
      IsOpenImmersion.lift_fac, spec_map_eLineS_comp, ← hU.fromSpecStalk_eq_fromSpecStalk hgen]
    rfl

end Cover

/-! ### Generic étaleness: `U'_S ⟶ 𝔸¹ ∖ S` is finite étale for `S` large -/

section Etale

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ P1 k)

/-- The affine part `f⁻¹(𝔸¹)`. -/
abbrev coverOpenA : X.Opens := f ⁻¹ᵁ (lineι k).opensRange

omit [IsIntegral X] in
lemma isAffineOpen_coverOpenA [IsFinite f] : IsAffineOpen (coverOpenA f) :=
  (isAffineOpen_opensRange (lineι k)).preimage f

omit [IsIntegral X] in
lemma range_fromSpec_coverOpenA_subset [IsFinite f] :
    Set.range ((isAffineOpen_coverOpenA f).fromSpec ≫ f).base ⊆ Set.range (lineι k).base := by
  rintro _ ⟨y, rfl⟩
  have hy : (isAffineOpen_coverOpenA f).fromSpec.base y ∈ coverOpenA f := by
    rw [← SetLike.mem_coe, ← (isAffineOpen_coverOpenA f).range_fromSpec]
    exact ⟨y, rfl⟩
  exact hy

/-- The coordinate `k[t] → B = Γ(f⁻¹(𝔸¹))`. -/
def coverHomA [IsFinite f] : CommRingCat.of (Polynomial k) ⟶ Γ(X, coverOpenA f) :=
  Spec.preimage (IsOpenImmersion.lift (lineι k) _ (range_fromSpec_coverOpenA_subset f))

omit [IsIntegral X] in
lemma spec_map_coverHomA_comp [IsFinite f] :
    Spec.map (coverHomA f) ≫ lineι k = (isAffineOpen_coverOpenA f).fromSpec ≫ f := by
  rw [coverHomA, Spec.map_preimage, IsOpenImmersion.lift_fac]

omit [IsIntegral X] in
/-- `k[t] → B` is finite. -/
lemma coverHomA_finite [IsFinite f] : (coverHomA f).hom.Finite := by
  have hU := isAffineOpen_coverOpenA f
  have hρ' : Spec.map (coverHomA f) = hU.isoSpec.inv ≫ (f ∣_ (lineι k).opensRange) ≫
      (lineι k).isoOpensRange.inv := by
    rw [← cancel_mono (lineι k), spec_map_coverHomA_comp, Category.assoc, Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι]
  have : IsFinite (Spec.map (coverHomA f)) := by
    rw [hρ']
    haveI : IsFinite (f ∣_ (lineι k).opensRange) :=
      IsZariskiLocalAtTarget.restrict ‹IsFinite f› _
    infer_instance
  exact (IsFinite.SpecMap_iff _).mp this

/-- `k[t] → B` is injective (its composite with `B → K(X)` is `t ↦ f^* t`, transcendental). -/
lemma coverHomA_injective [X.Over (Spec (.of k))] [IsFinite f] [IsDominant f]
    (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    Function.Injective (coverHomA f).hom := by
  have hgen : genericPoint X ∈ coverOpenA f := (mem_range_lineι_iff _).2 hη
  haveI : Nonempty (coverOpenA f) := ⟨⟨_, hgen⟩⟩
  have hU := isAffineOpen_coverOpenA f
  have key : coverHomA f ≫ X.germToFunctionField (coverOpenA f) = coordHom f hη := by
    rw [← Spec.map_inj, Spec.map_comp, ← cancel_mono (lineι k), Category.assoc,
      spec_map_coverHomA_comp, spec_map_coordHom_comp_lineι,
      ← hU.fromSpecStalk_eq_fromSpecStalk hgen]
    rfl
  have hinj : Function.Injective (coordHom f hη).hom := by
    have h := transcendental_iff_injective.1 (transcendental_coordFun hη hfk)
    intro p q hpq
    apply h
    rwa [← coordHom_eq_aeval hη hfk, ← coordHom_eq_aeval hη hfk]
  intro a b hab
  apply hinj
  rw [← key, CommRingCat.comp_apply, CommRingCat.comp_apply, hab]

omit [IsIntegral X] in
lemma coverOpenS_le_coverOpenA (S : Finset k) : coverOpenS f S ≤ coverOpenA f := by
  rintro x ⟨y, hy⟩
  exact ⟨_, (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial k) (lineRingS S)))) (lineι k) y).symm.trans hy⟩

omit [IsIntegral X] in
/-- `U'_S ⟶ B` followed by `Spec B ⟶ Spec k[t]` is `U'_S ⟶ 𝔸¹ ∖ S ⟶ 𝔸¹`. -/
lemma homOfLE_isoSpec_spec_map_coverHomA [IsFinite f] (S : Finset k) :
    X.homOfLE (coverOpenS_le_coverOpenA f S) ≫ (isAffineOpen_coverOpenA f).isoSpec.hom ≫
        Spec.map (coverHomA f) =
      coverMapS f S ≫ Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS S))) := by
  rw [← cancel_mono (lineι k), Category.assoc, Category.assoc, spec_map_coverHomA_comp,
    Category.assoc, ← lineSι_eq, coverMapS_comp_lineSι, IsAffineOpen.isoSpec_hom_fromSpec_assoc,
    Scheme.homOfLE_ι_assoc]

/-- **Generic étaleness of a finite map to `ℙ¹`.** For a finite `f : X ⟶ ℙ¹` from a curve over an
algebraically closed field of characteristic zero with `f(η_X) ≠ ∞`, there is a nonempty finite
`S₀ ⊆ k` such that `U'_T = f⁻¹(𝔸¹ ∖ T) ⟶ 𝔸¹ ∖ T` is finite étale for every finite `T ⊇ S₀`. -/
theorem exists_finset_isFiniteEtale_coverMapS [IsAlgClosed k] [CharZero k]
    [X.Over (Spec (.of k))] [IsCurveOver k X] [IsFinite f]
    (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    ∃ S₀ : Finset k, S₀.Nonempty ∧ ∀ T : Finset k, S₀ ⊆ T → IsFiniteEtale (coverMapS f T) := by
  classical
  haveI := Belyi.isDominant_of_isFinite f
  have hgen : genericPoint X ∈ coverOpenA f := (mem_range_lineι_iff _).2 hη
  haveI : Nonempty (coverOpenA f) := ⟨⟨_, hgen⟩⟩
  set ψ := coverHomA f with hψdef
  letI : Algebra k Γ(X, coverOpenA f) := (ψ.hom.comp Polynomial.C).toAlgebra
  let ψa : Polynomial k →ₐ[k] Γ(X, coverOpenA f) := Polynomial.aeval (ψ.hom Polynomial.X)
  have hψa : ψa.toRingHom = ψ.hom :=
    Polynomial.ringHom_ext (fun c ↦ by
      simp only [ψa, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
      rfl) (by simp [ψa])
  have hmv0 : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ ψ.hom Polynomial.X) =
      ψa.comp (finOnePolyEquiv k : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k) :=
    MvPolynomial.algHom_ext fun i ↦ by simp [ψa, finOnePolyEquiv_eq]
  have hψfin : ψa.toRingHom.Finite := by
    rw [hψa]
    exact coverHomA_finite f
  let D : Converse.FiniteCoord k Γ(X, coverOpenA f) :=
    { t := ψ.hom Polynomial.X
      finite := by
        rw [AlgHom.Finite, hmv0]
        exact RingHom.Finite.comp hψfin
          (RingHom.Finite.of_surjective _ (finOnePolyEquiv k).surjective) }
  have hmv : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t) =
      ψa.comp (finOnePolyEquiv k : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k) := hmv0
  have hψinj : Function.Injective ψa := fun a b h ↦
    coverHomA_injective f hη hfk (by rw [← hψa]; exact h)
  have hinj : Function.Injective (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t) := by
    rw [hmv, AlgHom.coe_comp]
    exact hψinj.comp (finOnePolyEquiv k).injective
  obtain ⟨S₀, hS₀, hS⟩ := CurvesJacobian.FiniteCoord.exists_etale_branchPolyOf_nonempty D hinj
  set q := MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ D.t) (Converse.branchPolyOf S₀)
    with hqdef
  have hq : q = ψ.hom (polyS S₀) := by
    rw [hqdef, aeval_branchPolyOf, polyS, map_prod]
    refine Finset.prod_congr rfl fun s _ ↦ ?_
    rw [map_sub]
    rfl
  -- `k[t] → B → B[q⁻¹]` is étale
  have hetR : ((algebraMap Γ(X, coverOpenA f) (Localization.Away q)).comp ψ.hom).Etale := by
    have e1 : (algebraMap Γ(X, coverOpenA f) (Localization.Away q)).comp ψ.hom =
        ((algebraMap Γ(X, coverOpenA f) (Localization.Away q)).comp
          (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t).toRingHom).comp
            (finOnePolyEquiv k).symm.toRingEquiv.toRingHom := by
      refine RingHom.ext fun p ↦ ?_
      simp only [RingHom.comp_apply]
      congr 1
      rw [← hψa, hmv]
      simp
    rw [e1]
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (f := (finOnePolyEquiv k).symm.toRingEquiv.toRingHom)
        (finOnePolyEquiv k).symm.bijective) hS
  set lc := CommRingCat.ofHom (algebraMap Γ(X, coverOpenA f) (Localization.Away q)) with hlc
  haveI : IsOpenImmersion (Spec.map lc) := IsOpenImmersion.of_isLocalization q
  haveI : Etale (Spec.map (ψ ≫ lc)) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 hetR
  refine ⟨S₀, hS₀, fun T hST ↦ ?_⟩
  set e0 := X.homOfLE (coverOpenS_le_coverOpenA f T) ≫ (isAffineOpen_coverOpenA f).isoSpec.hom
    with he0
  have hfac : e0 ≫ Spec.map ψ =
      coverMapS f T ≫ Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS T))) := by
    rw [he0, Category.assoc]
    exact homOfLE_isoSpec_spec_map_coverHomA f T
  -- `U'_T` lands in `D(q) ⊆ Spec B`
  have hrange : Set.range e0.base ⊆ Set.range (Spec.map lc).base := by
    rintro _ ⟨u, rfl⟩
    have h1 : (Spec.map ψ).base (e0.base u) =
        (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS T)))).base
          ((coverMapS f T).base u) := by
      rw [← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply]
    have h2 : polyS T ∉ ((Spec.map ψ).base (e0.base u)).asIdeal := by
      rw [h1, ← mem_range_specMap_lineRingS_iff]
      exact ⟨_, rfl⟩
    change e0.base u ∈ Set.range (PrimeSpectrum.comap
      (algebraMap Γ(X, coverOpenA f) (Localization.Away q)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away q) q]
    change q ∉ (e0.base u).asIdeal
    intro hqmem
    apply h2
    change ψ.hom (polyS T) ∈ (e0.base u).asIdeal
    obtain ⟨c, hc⟩ : polyS S₀ ∣ polyS T := Finset.prod_dvd_prod_of_subset _ _ _ hST
    rw [hc, map_mul, ← hq]
    exact Ideal.mul_mem_right _ _ hqmem
  set e1 := IsOpenImmersion.lift (Spec.map lc) e0 hrange with he1
  have he1' : e1 ≫ Spec.map lc = e0 := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion e0 := by rw [he0]; infer_instance
  haveI : Etale (e1 ≫ Spec.map lc) := by rw [he1']; infer_instance
  haveI : Etale e1 := Etale.of_comp e1 (Spec.map lc)
  have hcomp : coverMapS f T ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS T))) =
        e1 ≫ Spec.map (ψ ≫ lc) := by
    rw [Spec.map_comp, ← Category.assoc, he1', hfac]
  haveI : Etale (coverMapS f T ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS T)))) := by
    rw [hcomp]
    infer_instance
  haveI : Etale (coverMapS f T) := Etale.of_comp _
    (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineRingS T))))
  exact ⟨⟩

end Etale

/-! ### The Galois model -/

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [IsIntegral X] (eL : X.functionField ≃+* D.L)
  (f : X ⟶ P1 k) (hη : f.base (genericPoint X) ≠ P1.infty k)

/-- **The coordinate `t_f = eL(f^* t) ∈ Ω`.** -/
def coverT : Ω := ((eL (coordFun f hη) : D.L) : Ω)

lemma coverT_mem : coverT D eL f hη ∈ D.L := (eL (coordFun f hη)).2

variable (S : Finset k) [Nonempty (coverOpenS f S)] [X.Over (Spec (.of k))]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)

/-- The ring map `k[t, 1/P_S(t)] → Ω` of the generic point of `U'_S`. -/
abbrev eLineΩS : lineRingS S →+* Ω :=
  (algebraMap D.L Ω).comp (eL.toRingHom.comp (eLineS f S).hom)

include hk in
lemma eLineΩS_eq
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (ht : Transcendental k (coverT D eL f hη)) :
    eLineΩS D eL f S = (lineToΩS S ht).toRingHom := by
  refine lineRingS_ringHom_ext (fun c ↦ ?_) ?_
  · change ((eL ((eLineS f S).hom (algebraMap k (lineRingS S) c)) : D.L) : Ω) = _
    rw [eLineS_C f S hη hfk, hk]
    exact ((lineToΩS S ht).commutes c).symm
  · change ((eL ((eLineS f S).hom (lineTS S)) : D.L) : Ω) = _
    rw [eLineS_lineTS f S hη, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lineToΩS_lineTS]
    rfl

include hk in
/-- **The generic point of `U'_S` lies over the generic point of the line** (coordinate
`t_f`). -/
theorem genericL_coverMapS
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (ht : Transcendental k (coverT D eL f hη)) :
    (specPoint D.L Ω ≫ genericL D X eL (coverOpenS f S)) ≫ coverMapS f S = lineGenS S ht := by
  rw [← cancel_mono (lineSι k S), Category.assoc, coverMapS_comp_lineSι,
    ← Category.assoc, specPoint_genericL_ι, Category.assoc, genericLX, Category.assoc,
    ← spec_map_eLineS_comp f S, lineGenS_eq, ← eLineΩS_eq D eL f hη S hk hfk ht]
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

omit [X.Over (Spec (.of k))] in
/-- **Places centred on `U'_S`**: `W ⊇ k` is centred on `U'_S = f⁻¹(𝔸¹ ∖ S)` iff it contains the
image of `k[t, 1/P_S(t)]`. -/
theorem isCentredOn_coverOpenS_iff [IsFinite f] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) :
    IsCentredOn D X eL (coverOpenS f S) W ↔ ∀ x : lineRingS S, eLineΩS D eL f S x ∈ W := by
  obtain ⟨φ, hφf, hφ⟩ := exists_finite_liftS f S
  constructor
  · rintro ⟨-, hW⟩ x
    have := hW (φ.hom x)
    rwa [← CommRingCat.comp_apply, hφ] at this
  · intro hW
    refine ⟨hkW, fun b ↦ ?_⟩
    letI := φ.hom.toAlgebra
    let g : lineRingS S →+* W.toSubring := (eLineΩS D eL f S).codRestrict W.toSubring hW
    let ψ : Γ(X, coverOpenS f S) →+* Ω :=
      (algebraMap D.L Ω).comp (eL.toRingHom.comp (X.germToFunctionField (coverOpenS f S)).hom)
    have hcomp : (algebraMap W.toSubring Ω).comp g = ψ.comp (algebraMap (lineRingS S) _) := by
      ext x
      change eLineΩS D eL f S x = ψ (φ.hom x)
      simp only [ψ, eLineΩS, RingHom.comp_apply, ← hφ]
      rfl
    have hint : IsIntegral (lineRingS S) b := hφf.to_isIntegral b
    have hb : IsIntegral W.toSubring (ψ b) := hint.map_of_comp_eq g ψ hcomp
    haveI : IsIntegrallyClosedIn W.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn W Ω)
    obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hb
    change ψ b ∈ W
    rw [← hy]
    exact y.2

lemma aeval_mem_of_forall_mem {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) {s : Ω} (hs : s ∈ W) (p : Polynomial k) :
    Polynomial.aeval s p ∈ W := by
  induction p using Polynomial.induction_on with
  | C a => simpa using hkW a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a _ =>
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact mul_mem (hkW a) (pow_mem hs _)

include hk in
/-- **Places centred on `U'_S`**, explicitly: `W ⊇ k` is centred on `U'_S` iff `t_f ∈ W` and
`P_S(t_f)⁻¹ ∈ W`. -/
theorem isCentredOn_coverOpenS_iff' [IsFinite f]
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (ht : Transcendental k (coverT D eL f hη)) {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) :
    IsCentredOn D X eL (coverOpenS f S) W ↔
      coverT D eL f hη ∈ W ∧ (Polynomial.aeval (coverT D eL f hη) (polyS S))⁻¹ ∈ W := by
  rw [isCentredOn_coverOpenS_iff D eL f S hkW, eLineΩS_eq D eL f hη S hk hfk ht]
  set tB := coverT D eL f hη with htB
  have hP0 : Polynomial.aeval tB (polyS S) ≠ 0 := fun h ↦ ht ⟨polyS S, polyS_ne_zero S, h⟩
  have hT : (lineToΩS S ht).toRingHom (lineTS S) = tB := lineToΩS_lineTS S ht
  have hS : ∀ p : Polynomial k, (lineToΩS S ht).toRingHom (algebraMap _ (lineRingS S) p) =
      Polynomial.aeval tB p := lineToΩS_algebraMap S ht
  have hinvS : (lineToΩS S ht).toRingHom (IsLocalization.Away.invSelf (polyS S)) =
      (Polynomial.aeval tB (polyS S))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have h := congrArg (lineToΩS S ht).toRingHom
      (IsLocalization.Away.mul_invSelf (S := lineRingS S) (polyS S))
    rw [map_mul, map_one, hS] at h
    rw [mul_comm]
    exact h
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h (lineTS S)
      rwa [hT] at this
    · have := h (IsLocalization.Away.invSelf (polyS S))
      rwa [hinvS] at this
  · rintro ⟨h1, h2⟩ x
    obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (polyS S)) x
    have hspec := congrArg (lineToΩS S ht).toRingHom (IsLocalization.mk'_spec (lineRingS S) p
      (⟨polyS S ^ n, n, rfl⟩ : Submonoid.powers (polyS S)))
    rw [map_mul, hS, hS, map_pow] at hspec
    have hval : (lineToΩS S ht).toRingHom (IsLocalization.mk' (lineRingS S) p
        (⟨polyS S ^ n, n, rfl⟩ : Submonoid.powers (polyS S))) =
        Polynomial.aeval tB p * ((Polynomial.aeval tB (polyS S))⁻¹) ^ n := by
      rw [← hspec, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hP0), mul_one]
    rw [hval]
    exact mul_mem (aeval_mem_of_forall_mem hkW h1 p) (pow_mem h2 n)

end Galois

/-! ### The Galois action on `π₁ᵉᵗ(𝔸¹ ∖ S)` -/

section Line

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (S : Finset k)

lemma lineToK₀S_algebraMap (ht : Transcendental k t) (p : Polynomial k) :
    lineToK₀S S ht (algebraMap (Polynomial k) (lineRingS S) p) = Polynomial.aeval (tK₀ k t) p :=
  lineLiftS_algebraMap _ _ p

lemma lineToK₀S_injective (ht : Transcendental k t) : Function.Injective (lineToK₀S S ht) := by
  have hcomap : (RingHom.ker (lineToK₀S S ht).toRingHom).comap
      (algebraMap (Polynomial k) (lineRingS S)) = ⊥ := by
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      lineToK₀S_algebraMap S ht, Ideal.mem_bot]
    constructor
    · intro h
      have h' := congrArg (fun z : K₀ k t ↦ (z : Ω)) h
      simp only [coe_aeval_tK₀, ZeroMemClass.coe_zero] at h'
      by_contra hp
      exact ht ⟨p, hp, h'⟩
    · rintro rfl
      simp
  have := IsLocalization.map_under (Submonoid.powers (polyS S)) (lineRingS S)
    (RingHom.ker (lineToK₀S S ht).toRingHom)
  rw [show Ideal.under (Polynomial k) (RingHom.ker (lineToK₀S S ht).toRingHom) = ⊥ from hcomap,
    Ideal.map_bot] at this
  exact (RingHom.injective_iff_ker_eq_bot _).2 this.symm

variable [IsSepClosed Ω] [IsGalois (K₀ k t) Ω]

/-- **The Galois action on `π₁ᵉᵗ(𝔸¹ ∖ S)` is surjective** (`k[t, 1/P_S(t)]` is integrally closed
in `k(t)`). -/
theorem lineGaloisS_surjective (ht : Transcendental k t) :
    Function.Surjective (lineGaloisS S ht) := by
  letI : Algebra (lineRingS S) (K₀ k t) := (lineToK₀S S ht).toRingHom.toAlgebra
  letI : Algebra (lineRingS S) Ω := (lineToΩS S ht).toRingHom.toAlgebra
  haveI : IsScalarTower (lineRingS S) (K₀ k t) Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hinj : Function.Injective (algebraMap (lineRingS S) (K₀ k t)) := lineToK₀S_injective S ht
  haveI : FaithfulSMul (lineRingS S) (K₀ k t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (lineRingS S) (K₀ k t) := by
    refine IsFractionRing.of_field _ _ fun z ↦ ?_
    obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.1 z.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := hs
    refine ⟨algebraMap (Polynomial k) (lineRingS S) p,
      algebraMap (Polynomial k) (lineRingS S) q, Subtype.ext ?_⟩
    change (z : Ω) = ((lineToK₀S S ht (algebraMap _ _ p) / lineToK₀S S ht (algebraMap _ _ q) :
      K₀ k t) : Ω)
    rw [IntermediateField.coe_div, lineToK₀S_algebraMap, lineToK₀S_algebraMap, coe_aeval_tK₀,
      coe_aeval_tK₀]
    exact hrs
  haveI : IsIntegrallyClosed (lineRingS S) :=
    isIntegrallyClosed_of_isLocalization (lineRingS S) (Submonoid.powers (polyS S))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (polyS_ne_zero S))
  have hint : ∀ x : K₀ k t, IsIntegral (lineRingS S) x →
      x ∈ Set.range (algebraMap (lineRingS S) (K₀ k t)) := fun x hx ↦
    (IsIntegrallyClosed.isIntegral_iff (K := K₀ k t)).1 hx
  have hs := FiniteEtale.galoisAction_surjective (F := K₀ k t) (Ω := Ω) (lineRingS S) hinj hint
  exact galoisAction_surjective_congr (K₀ k t) _ _ rfl hs

/-- The inertia group in `π₁ᵉᵗ(𝔸¹ ∖ S, η)` is the image of the inertia subgroup. -/
lemma lineInertiaS_eq_map (ht : Transcendental k t) (W : ValuationSubring Ω) :
    lineInertiaS S ht W =
      (GaloisPi1.inertiaSubgroup (P := K₀ k t) W).map (lineGaloisS S ht) := by
  have hcl : Subgroup.closure (lineGaloisS S ht '' GaloisPi1.inertia (P := K₀ k t) W) =
      (GaloisPi1.inertiaSubgroup (P := K₀ k t) W).map (lineGaloisS S ht) := by
    rw [← MonoidHom.map_closure]
    congr 1
    exact Subgroup.closure_eq (GaloisPi1.inertiaSubgroup W)
  rw [lineInertiaS, hcl]
  refine le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl ?_)
    (Subgroup.le_topologicalClosure _)
  rw [Subgroup.coe_map]
  exact ((isClosed_inertia W).isCompact.image (continuous_galoisAction _ _ _)).isClosed

/-- **Conjugating the inertia group of a place** of `Ω` over `k(t)`. -/
lemma lineInertiaS_comap (ht : Transcendental k t) (W : ValuationSubring Ω)
    (σ : Ω ≃ₐ[K₀ k t] Ω) :
    lineInertiaS S ht (W.comap (σ.symm : Ω →+* Ω)) =
      (lineInertiaS S ht W).map (MulAut.conj (lineGaloisS S ht σ)).toMonoidHom := by
  rw [lineInertiaS_eq_map, lineInertiaS_eq_map, Subgroup.map_map]
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

end Line

/-! ### The Galois actions -/

section Action

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [IsIntegral X] (eL : X.functionField ≃+* D.L)
  (f : X ⟶ P1 k) (hη : f.base (genericPoint X) ≠ P1.infty k) (hH : D.H ≤ D.HL)

/-- An element of `H = Gal(Ω / L)` as an automorphism of `Ω` over `k(t_f)`. -/
def toLineS (σ : D.H) : Ω ≃ₐ[K₀ k (coverT D eL f hη)] Ω :=
  AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv)
    (fun c ↦ fix_of_mem_H hH σ (K₀_le_of_mem (coverT_mem D eL f hη) c.2))

@[simp] lemma toLineS_apply (σ : D.H) (x : Ω) :
    toLineS D eL f hη hH σ x = (σ : Ω ≃ₐ[K₀ k t] Ω) x := rfl

lemma toLineS_mul (σ τ : D.H) :
    toLineS D eL f hη hH (σ * τ) = toLineS D eL f hη hH σ * toLineS D eL f hη hH τ :=
  AlgEquiv.ext fun _ ↦ rfl

variable (S : Finset k) [Nonempty (coverOpenS f S)] [IsSepClosed Ω] [IsGalois (K₀ k t) Ω]
  (ht : Transcendental k (coverT D eL f hη)) [IsGalois (K₀ k (coverT D eL f hη)) Ω]
  (hbase : (specPoint D.L Ω ≫ genericL D X eL (coverOpenS f S)) ≫ coverMapS f S = lineGenS S ht)

include hbase in
/-- **`π₁ᵉᵗ(U'_S) → π₁ᵉᵗ(𝔸¹ ∖ S)` intertwines the Galois actions.** -/
theorem fundamentalGroupMap_coverMapS_chartHom (σ : D.H) :
    fundamentalGroupMap (coverMapS f S) hbase
        (D.chartHom hH (genericL D X eL (coverOpenS f S)) σ) =
      lineGaloisS S ht (toLineS D eL f hη hH σ) := by
  rw [GaloisData.chartHom_apply, fundamentalGroupMap_galoisAction D.L _ (coverMapS f S) rfl hbase
    (by rw [← Category.assoc]; exact hbase)]
  exact galoisAction_eq_of_apply_eq D.L _ _ _ _ _ _ fun _ ↦ rfl

omit [IsGalois (K₀ k t) Ω] in
include hbase in
/-- **Galois elements stabilising the generic point of `U'_S` fix `L`.** If the image of
`σ ∈ Gal(Ω / k(t_f))` in `π₁ᵉᵗ(𝔸¹ ∖ S)` lies in the image of `π₁ᵉᵗ(U'_S)`, then `σ` fixes `L`. -/
theorem apply_eq_of_lineGaloisS_mem_range [IsFiniteEtale (coverMapS f S)]
    (σ : Ω ≃ₐ[K₀ k (coverT D eL f hη)] Ω)
    (hσ : lineGaloisS S ht σ ∈ (fundamentalGroupMap (coverMapS f S) hbase).toMonoidHom.range)
    (x : D.L) : σ (x : Ω) = x := by
  rw [range_fundamentalGroupMap_of_isFiniteEtale', MulAction.mem_stabilizer_iff] at hσ
  have h1 := congrArg
    (fun y ↦ (fiberObjEquivHom (lineGenS S ht) (coverObj (coverMapS f S)) y).left) hσ
  change (fiberObjEquivHom _ _ ((lineGaloisS S ht σ).hom.app _ _)).left = _ at h1
  rw [lineGaloisS, galoisAction_hom_app_left, coverPt, Equiv.apply_symm_apply] at h1
  simp only [Over.homMk_left] at h1
  have h1' : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      (specPoint D.L Ω ≫ genericL D X eL (coverOpenS f S)) =
      specPoint D.L Ω ≫ genericL D X eL (coverOpenS f S) := h1
  -- compose with `U'_S ⟶ X` and cancel the monomorphism `Spec K(X) ⟶ X`
  have h2 : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ specPoint D.L Ω ≫
      Spec.map (CommRingCat.ofHom eL.toRingHom) ≫ X.fromSpecStalk (genericPoint X) =
      specPoint D.L Ω ≫ Spec.map (CommRingCat.ofHom eL.toRingHom) ≫
        X.fromSpecStalk (genericPoint X) := by
    have := h1' =≫ (coverOpenS f S).ι
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

include hbase in
/-- **The cuspidal inertia groups of `U'_S` in `π₁ᵉᵗ(𝔸¹ ∖ S)`**: `π₁ᵉᵗ(U'_S) → π₁ᵉᵗ(𝔸¹ ∖ S)`
maps `cuspInertia U'_S W` onto the intersection of the inertia group of `W` with its image
(`t ∈ L`). -/
theorem map_cuspInertia_coverMapS [IsFiniteEtale (coverMapS f S)] {τ₀ : X.functionField}
    (hτ₀ : ((eL τ₀ : D.L) : Ω) = t) (W : ValuationSubring Ω) :
    (cuspInertia D X eL hH (coverOpenS f S) W).map
        (fundamentalGroupMap (coverMapS f S) hbase).toMonoidHom =
      lineInertiaS S ht W ⊓ (fundamentalGroupMap (coverMapS f S) hbase).toMonoidHom.range := by
  -- `cuspInertia_eq_map`, which is stated in universe `0` only
  have hcI : cuspInertia D X eL hH (coverOpenS f S) W =
      ((GaloisPi1.inertiaSubgroup (P := K₀ k t) W).comap D.H.subtype).map
        (D.chartHom hH (genericL D X eL (coverOpenS f S))) := by
    have : (Subtype.val ⁻¹' GaloisPi1.inertia W : Set D.H) =
        ((GaloisPi1.inertiaSubgroup (P := K₀ k t) W).comap D.H.subtype : Set D.H) := rfl
    rw [cuspInertia, this, ← MonoidHom.map_closure, Subgroup.closure_eq]
  rw [hcI, lineInertiaS_eq_map, Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have h := fundamentalGroupMap_coverMapS_chartHom D eL f hη hH S ht hbase σ
    refine ⟨⟨toLineS D eL f hη hH σ, ?_, ?_⟩, ⟨_, rfl⟩⟩
    · intro a ha
      exact hσ a ha
    · exact h.symm
  · rintro ⟨⟨σ', hσ', rfl⟩, hr⟩
    have hfix := apply_eq_of_lineGaloisS_mem_range D eL f hη S ht hbase σ' hr
    have htL : t ∈ D.L := by
      have := (eL τ₀).2
      rwa [hτ₀] at this
    let σ : Ω ≃ₐ[K₀ k t] Ω := AlgEquiv.ofRingEquiv (f := σ'.toRingEquiv)
      (fun c ↦ hfix ⟨_, K₀_le_of_mem htL c.2⟩)
    have hσHL : σ ∈ D.HL := by
      rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hfix ⟨x, hx⟩
    refine ⟨⟨σ, D.le hσHL⟩, ?_, ?_⟩
    · intro a ha
      exact hσ' a ha
    · change fundamentalGroupMap (coverMapS f S) hbase
        (D.chartHom hH (genericL D X eL (coverOpenS f S)) ⟨σ, D.le hσHL⟩) = lineGaloisS S ht σ'
      rw [fundamentalGroupMap_coverMapS_chartHom D eL f hη hH S ht hbase]
      exact congrArg _ (AlgEquiv.ext fun _ ↦ rfl)

end Action

end CurvesJacobian.Cusp
