/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiChainHV
import CurvesJacobian.Cusp.CandidateCover
import CurvesJacobian.Cusp.ConjInducedCusps

/-!
# Model independence of cusps (MR8, round 28, G1)

For a chain object `A` of `Π_X ↠ G_K` (`X` an affine hyperbolic curve over a number field `K`),
any two geometric models `(Y₁, ι₁)`, `(Y₂, ι₂)` of `A` have the same cuspidal inertia groups up to
commensurability inside `A` (**`CurvesJacobian.Cusp.modelCuspIndep₂`**), assuming the rel-isom-DGC
over number fields. This discharges the hypothesis `hMI` of
`PiChain.IsBelyiType.hasInfCusp_V₃`; hence `hV` holds for every Belyi-type chain with a terminal
isomorphism (`PiChain.IsBelyiType.hasInfCusp_V`) and the Belyi candidates are geometric without
the hypothesis `hV` (`PiChain.IsBelyiType.exists_cover_fill'`).

## The argument

* **Sub-models** (`GeomModel.exists_sub_cuspCompat₂`): for an open subgroup `O ⊆ ι(Π_Y)` of `A`
  normalised by `Δ_A`, the connected finite étale cover `C → Y` attached to `ι⁻¹(O)` at a suitable
  point (`exists_isFiniteEtale_range_eq_of_open`; `O` need not be normal) is a model `D'` of `A`
  with image `O`, and the cusps of `D` and `D'` match up to commensurability in both directions:
  preimages of cuspidal inertia groups of `Π_Y` are cuspidal inertia groups of `Π_C`
  (`comap_coverPiEquiv_mem_arithCusps`) and `Π_C` has finite index, while cuspidal inertia groups
  of `Π_C` map with finite index into cuspidal inertia groups of `Π_Y`
  (`exists_arithCusps_map_le_of_conjInduced`).
* **Models with the same image** (`cuspCompat_of_range_eq₂`): `θ = ι₁⁻¹ ∘ ι₂ : Π_{Y₂} ≅ Π_{Y₁}`
  lies over `res` on both sides up to conjugation, so it is induced by an isomorphism of schemes
  `Spec Γ(U₂) ≅ Spec Γ(U₁)` lying over some `Spec α`, `α : M₁ ≃ₐ[K] M₂`
  (`exists_isConjInduced_of_relIsomDGC_field`). Such a map — between curves over **different**
  number fields — maps cuspidal inertia groups into cuspidal inertia groups with finite index
  (`exists_arithCusps_map_le_of_conjInduced`, stated in `CoverCusps`/`ConjInducedCusps` without
  any relation between the two fields of definition).
* For two arbitrary models, compare both with sub-models with image `ι₁(Π_{Y₁}) ∩ ι₂(Π_{Y₂})`
  (`cuspCompat_trans₂`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.Cusp

/-! ### Group-theoretic lemmas -/

section Groups

/-- Images of subgroups mapping with finite index into members of `S` are commensurable with
images of members of `S`. -/
lemma exists_commensurable_map_of_le₂ {P P' G : Type*} [Group P] [Group P'] [Group G]
    (ι : P →* G) (ψ : P' →* P) {S : Set (Subgroup P)} {S' : Set (Subgroup P')}
    (h : ∀ J' ∈ S', ∃ J ∈ S, J'.map ψ ≤ J ∧ (J'.map ψ).relIndex J ≠ 0) :
    ∀ J' ∈ S', ∃ J ∈ S, (J'.map (ι.comp ψ)).Commensurable (J.map ι) := by
  intro J' hJ'
  obtain ⟨J, hJ, hle, hfin⟩ := h J' hJ'
  refine ⟨J, hJ, ?_⟩
  rw [← Subgroup.map_map]
  exact (Subgroup.commensurable_of_le hle hfin).map' ι

/-- Images of members of `S` are commensurable with images of their preimages under a map `ψ`
with image of finite index. -/
lemma exists_commensurable_map_of_comap₂ {P P' G : Type*} [Group P] [Group P'] [Group G]
    (ι : P →* G) (ψ : P' →* P) (hR : ψ.range.index ≠ 0) {S : Set (Subgroup P)}
    {S' : Set (Subgroup P')} (h : ∀ J ∈ S, J.comap ψ ∈ S') :
    ∀ J ∈ S, ∃ J' ∈ S', (J.map ι).Commensurable (J'.map (ι.comp ψ)) := by
  intro J hJ
  refine ⟨J.comap ψ, h J hJ, ?_⟩
  have e : (J.comap ψ).map (ι.comp ψ) = (ψ.range ⊓ J).map ι := by
    rw [← Subgroup.map_map, Subgroup.map_comap_eq]
  rw [e]
  exact ((Subgroup.commensurable_inf_of_index_ne_zero hR J).map' ι).symm

/-- Two continuous embeddings of compact groups into a Hausdorff group with the same image differ
by an isomorphism. -/
lemma exists_equiv_of_range_eq₂ {P₁ P₂ G : Type*} [Group P₁] [TopologicalSpace P₁]
    [IsTopologicalGroup P₁] [CompactSpace P₁] [Group P₂] [TopologicalSpace P₂]
    [IsTopologicalGroup P₂] [CompactSpace P₂] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (ι₁ : P₁ →ₜ* G) (ι₂ : P₂ →ₜ* G)
    (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂) (h : Set.range ι₁ = Set.range ι₂) :
    ∃ θ : P₂ ≃ₜ* P₁, ∀ σ, ι₁ (θ σ) = ι₂ σ := by
  have hm : ∀ x, ι₂ x ∈ (ι₁ : P₁ →* G).range := fun x ↦ by
    have hx : ι₂ x ∈ Set.range ι₁ := by
      rw [h]
      exact Set.mem_range_self x
    exact hx
  let w₁ : P₁ →ₜ* (ι₁ : P₁ →* G).range :=
    ⟨(ι₁ : P₁ →* G).rangeRestrict, Continuous.subtype_mk ι₁.continuous _⟩
  let w₂ : P₂ →ₜ* (ι₁ : P₁ →* G).range :=
    ⟨(ι₂ : P₂ →* G).codRestrict _ hm, Continuous.subtype_mk ι₂.continuous _⟩
  have hw₁ : Function.Bijective w₁ :=
    ⟨fun a b hab ↦ h₁ (congrArg Subtype.val hab), MonoidHom.rangeRestrict_surjective _⟩
  have hw₂ : Function.Bijective w₂ := by
    refine ⟨fun a b hab ↦ h₂ (congrArg Subtype.val hab), fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := y.2
    have hy : ι₁ x ∈ Set.range ι₂ := by
      rw [← h]
      exact Set.mem_range_self x
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, Subtype.ext (hz.trans hx)⟩
  refine ⟨(continuousMulEquivOfBijective w₂ hw₂).trans (continuousMulEquivOfBijective w₁ hw₁).symm,
    fun σ ↦ ?_⟩
  have h1 := congrArg Subtype.val ((continuousMulEquivOfBijective w₁ hw₁).apply_symm_apply
    (continuousMulEquivOfBijective w₂ hw₂ σ))
  exact h1

end Groups

/-! ### Comparison of geometric models -/

section Models

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {A : ChainObj (arithmeticExt Ω CX hcX)}

/-- `CuspCompat₂` is transitive. -/
theorem cuspCompat_trans₂ {D₁ D₂ D₃ : GeomModel Ω CX hcX A} (h₁₂ : CuspCompat₂ D₁ D₂)
    (h₂₃ : CuspCompat₂ D₂ D₃) : CuspCompat₂ D₁ D₃ := by
  intro J₃ hJ₃
  obtain ⟨J₂, hJ₂, h⟩ := h₂₃ J₃ hJ₃
  obtain ⟨J₁, hJ₁, h'⟩ := h₁₂ J₂ hJ₂
  exact ⟨J₁, hJ₁, h.trans h'⟩

set_option maxHeartbeats 400000 in
-- the cover curve, its constant field and `Π_{Y'} ≃ O` are large terms
/-- **Sub-models** (cf. `GeomModel.exists_ofSub`, without normality): for an open subgroup `O` of
`A` contained in `ι(Π_Y)` and normalised by `Δ_A`, there is a model `D'` of `A` with image `O`
(from a connected finite étale cover of `Y`) whose cusps match those of `D` up to
commensurability in both directions. -/
theorem GeomModel.exists_sub_cuspCompat₂ (D : GeomModel Ω CX hcX A) (O : Subgroup A.grp)
    (hO : IsOpen (O : Set A.grp)) (hN : A.Delta ≤ Subgroup.normalizer (O : Set A.grp))
    (hle : (O : Set A.grp) ⊆ Set.range D.ι) :
    ∃ D' : GeomModel Ω CX hcX A, Set.range D'.ι = O ∧ CuspCompat₂ D D' ∧ CuspCompat₂ D' D := by
  haveI := isIntegral_specSections D.Y D.hY
  have hO₁ : IsOpen ((O.comap (D.ι : D.Pi →* A.grp) : Subgroup D.Pi) : Set D.Pi) :=
    hO.preimage D.ι.continuous
  obtain ⟨V, f, hf, ζ, hζ, hV, hrange⟩ := exists_isFiniteEtale_range_eq_of_open
    (basePoint Ω D.Y D.hY ≫ baseChangeSpec D.M Ω Γ(D.Y.Xbar, D.Y.U)) ⟨_, hO₁⟩
  haveI := hf
  haveI := hV
  set M' := coverField D.Y D.hY f
  letI : Algebra M' Ω := coverAlgebra Ω D.Y D.hY f ζ
  haveI : IsScalarTower D.M M' Ω := isScalarTower_coverAlgebra Ω D.Y D.hY f ζ hζ
  haveI : Algebra.IsAlgebraic M' Ω := isAlgebraic_coverAlgebra Ω D.Y D.hY f ζ hζ
  letI : Algebra K M' := ((algebraMap D.M M').comp (algebraMap K D.M)).toAlgebra
  haveI : IsScalarTower K D.M M' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K M' Ω := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq K D.M Ω, IsScalarTower.algebraMap_eq D.M M' Ω,
      RingHom.comp_assoc]
    rfl)
  haveI : FiniteDimensional D.M M' :=
    haveI := isIntegral_cover D.Y D.hY f
    finiteDimensional_constField_normalization (k := D.M) D.Y.nonempty (coverMap D.Y D.hY f)
  haveI : FiniteDimensional K M' := Module.Finite.trans D.M M'
  set e := coverCurvePiEquiv Ω D.Y D.hY f ζ hζ
  set c := coverConj Ω D.Y D.hY f ζ hζ (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f)
    (coverIso D.Y D.hY f) (coverIso_spec D.Y D.hY f)
  -- `Π_{Y'} → ι⁻¹(O) ⊆ Π_Y`
  let j : (coverChainObj Ω D.Y D.hY f ζ hζ).grp →ₜ* D.Pi := coverPiIncl Ω D.Y D.hY f ζ hζ
  have hjO : Set.range j = ((O.comap (D.ι : D.Pi →* A.grp) : Subgroup D.Pi) : Set D.Pi) := by
    have h1 := hrange
    rw [range_fundamentalGroupMap_eq_coverSubgroup] at h1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (SetLike.ext_iff.1 h1 _).1 x.2
    · intro hy
      exact ⟨⟨y, (SetLike.ext_iff.1 h1 y).2 hy⟩, rfl⟩
  have himg : D.ι '' ((O.comap (D.ι : D.Pi →* A.grp) : Subgroup D.Pi) : Set D.Pi) =
      (O : Set A.grp) :=
    Set.image_preimage_eq_of_subset hle
  have hrangeι : Set.range (D.ι.comp (j.comp (ContinuousMonoidHom.toContinuousMonoidHom e))) =
      (O : Set A.grp) := by
    rw [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_comp, Set.range_comp,
      Set.range_comp, ContinuousMonoidHom.coe_coe, e.surjective.range_eq, Set.image_univ, hjO,
      himg]
  have k1 : ∀ σ, toGk A (D.ι (j (e σ))) =
      D.g₀ * resGal K Ω D.M (projGk Ω D.Y D.hY (j (e σ))) * D.g₀⁻¹ := fun σ ↦ D.toG_ι _
  have k2 : ∀ σ, projGk Ω D.Y D.hY (j (e σ)) = (coverChainObj Ω D.Y D.hY f ζ hζ).toG (e σ) :=
    fun σ ↦ rfl
  have k3 : ∀ σ, (coverChainObj Ω D.Y D.hY f ζ hζ).toG (e σ) = c * galoisMap D.M M' Ω
      ((arithmeticExt Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f)).pr σ) * c⁻¹ :=
    toG_coverCurvePiEquiv Ω D.Y D.hY f ζ hζ
  have k4 : ∀ s, resGal K Ω D.M (galoisMap D.M M' Ω s) = resGal K Ω M' s :=
    resGal_galoisMap _ _
  have key : ∀ σ, toGk A (D.ι (j (e σ))) = (D.g₀ * resGal K Ω D.M c) * resGal K Ω M'
      ((arithmeticExt Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f)).pr σ) *
        (D.g₀ * resGal K Ω D.M c)⁻¹ := fun σ ↦ by
    rw [k1, k2, k3, map_mul, map_mul, map_inv, k4]
    group
  have key' : ∀ σ : π₁ᵉᵗ(basePoint Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f) ≫
      baseChangeSpec M' Ω Γ((coverCurve D.Y D.hY f).Xbar, (coverCurve D.Y D.hY f).U)),
      toGk A ((D.ι.comp (j.comp (ContinuousMonoidHom.toContinuousMonoidHom e))) σ) =
        (D.g₀ * resGal K Ω D.M c) *
          resGal K Ω M' (projGk Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f) σ) *
        (D.g₀ * resGal K Ω D.M c)⁻¹ := fun σ ↦ key σ
  have hopen : IsOpen (Set.range (D.ι.comp (j.comp
      (ContinuousMonoidHom.toContinuousMonoidHom e)))) := by
    rw [hrangeι]
    exact hO
  have hnorm : A.Delta ≤ Subgroup.normalizer (Set.range (D.ι.comp (j.comp
      (ContinuousMonoidHom.toContinuousMonoidHom e)))) := by
    rw [hrangeι]
    exact hN
  have hinj' := D.inj.comp (Subtype.val_injective.comp e.injective)
  -- the cover map and its cusp comparisons
  set ψ : (arithmeticExt Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f)).Pi →* D.Pi :=
    (coverPiIncl Ω D.Y D.hY f ζ hζ).toMonoidHom.comp e.toMulEquiv.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  haveI : IsFiniteEtale (coverIso D.Y D.hY f).hom :=
    MorphismProperty.of_isIso @IsFiniteEtale (coverIso D.Y D.hY f).hom
  haveI : IsFiniteEtale ((coverIso D.Y D.hY f).hom ≫ f) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have HC : IsConjInduced ((coverIso D.Y D.hY f).hom ≫ f) ψ :=
    isConjInduced_coverPiEquiv Ω D.Y D.hY (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f)
      f ζ hζ (coverIso D.Y D.hY f)
  have hR : ψ.range.index ≠ 0 :=
    (finiteIndex_range_of_conjInduced_cover Ω D.Y D.hY (coverCurve D.Y D.hY f)
      (coverCurve_cusp D.Y D.hY f) ((coverIso D.Y D.hY f).hom ≫ f) ψ HC).index_ne_zero
  have hcomap : ∀ J ∈ arithCusps Ω D.Y D.hY,
      J.comap ψ ∈ arithCusps Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f) :=
    fun J hJ ↦ comap_coverPiEquiv_mem_arithCusps Ω D.Y D.hY (coverCurve D.Y D.hY f)
      (coverCurve_cusp D.Y D.hY f) f ζ hζ (coverIso D.Y D.hY f) (coverIso_spec D.Y D.hY f) hJ
  have hmap : ∀ J' ∈ arithCusps Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f),
      ∃ J ∈ arithCusps Ω D.Y D.hY, J'.map ψ ≤ J ∧ (J'.map ψ).relIndex J ≠ 0 :=
    fun J' hJ' ↦ exists_arithCusps_map_le_of_conjInduced Ω D.Y D.hY (coverCurve D.Y D.hY f)
      (coverCurve_cusp D.Y D.hY f) ((coverIso D.Y D.hY f).hom ≫ f) ψ HC hJ'
  -- cusp compatibility of the new model
  have hcusp : ∀ I ∈ (arithmeticExt Ω CX hcX).cusps,
      ((A.image I).comap (D.ι.comp (j.comp
        (ContinuousMonoidHom.toContinuousMonoidHom e))).toMonoidHom).Commensurable ⊥ ∨
      ∃ J ∈ arithCusps Ω (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f),
        ((A.image I).comap (D.ι.comp (j.comp
          (ContinuousMonoidHom.toContinuousMonoidHom e))).toMonoidHom).Commensurable J := by
    intro I hI
    have e1 : (A.image I).comap (D.ι.comp (j.comp
        (ContinuousMonoidHom.toContinuousMonoidHom e))).toMonoidHom =
        ((A.image I).comap (D.ι : D.Pi →* A.grp)).comap ψ := rfl
    rw [e1]
    rcases D.cusp I hI with h | ⟨J, hJ, h⟩
    · left
      have h' := h.comap' ψ
      rwa [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff ψ).2 hψ] at h'
    · exact Or.inr ⟨_, hcomap J hJ, h.comap' ψ⟩
  have hb := exists_commensurable_map_of_le₂ (D.ι : D.Pi →* A.grp) ψ hmap
  have ha := exists_commensurable_map_of_comap₂ (D.ι : D.Pi →* A.grp) ψ hR hcomap
  exact ⟨GeomModel.mk M' (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f)
    (D.ι.comp (j.comp (ContinuousMonoidHom.toContinuousMonoidHom e))) hinj' hopen hnorm
    ⟨D.g₀ * resGal K Ω D.M c, key'⟩ hcusp, hrangeι, hb, ha⟩

/-- **Models with the same image have the same cusps** (given the rel-isom-DGC): the
isomorphism `θ : Π_{Y₂} ≅ Π_{Y₁}` with `ι₁ ∘ θ = ι₂` is induced by an isomorphism of schemes
`Spec Γ(U₂) ≅ Spec Γ(U₁)` (`exists_isConjInduced_of_relIsomDGC_field`), which maps cuspidal
inertia groups into cuspidal inertia groups with finite index
(`exists_arithCusps_map_le_of_conjInduced`). -/
theorem cuspCompat_of_range_eq₂ (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    {D₁ D₂ : GeomModel Ω CX hcX A} (h : Set.range D₁.ι = Set.range D₂.ι) :
    CuspCompat₂ D₁ D₂ := by
  obtain ⟨θ, hθ⟩ := exists_equiv_of_range_eq₂ D₁.ι D₂.ι D₁.inj D₂.inj h
  have hφ : ∀ σ, resGal K Ω D₁.M (projGk Ω D₁.Y D₁.hY (θ σ)) =
      (D₁.g₀⁻¹ * D₂.g₀) * resGal K Ω D₂.M (projGk Ω D₂.Y D₂.hY σ) * (D₁.g₀⁻¹ * D₂.g₀)⁻¹ :=
    fun σ ↦ by
      have e1 : toGk A (D₁.ι (θ σ)) =
          D₁.g₀ * resGal K Ω D₁.M (projGk Ω D₁.Y D₁.hY (θ σ)) * D₁.g₀⁻¹ := D₁.toG_ι (θ σ)
      have e2 : toGk A (D₂.ι σ) =
          D₂.g₀ * resGal K Ω D₂.M (projGk Ω D₂.Y D₂.hY σ) * D₂.g₀⁻¹ := D₂.toG_ι σ
      have e3 : D₁.g₀ * resGal K Ω D₁.M (projGk Ω D₁.Y D₁.hY (θ σ)) * D₁.g₀⁻¹ =
          D₂.g₀ * resGal K Ω D₂.M (projGk Ω D₂.Y D₂.hY σ) * D₂.g₀⁻¹ :=
        e1.symm.trans ((congrArg (toGk A) (hθ σ)).trans e2)
      calc resGal K Ω D₁.M (projGk Ω D₁.Y D₁.hY (θ σ)) =
          D₁.g₀⁻¹ * (D₁.g₀ * resGal K Ω D₁.M (projGk Ω D₁.Y D₁.hY (θ σ)) * D₁.g₀⁻¹) * D₁.g₀ := by
            group
        _ = _ := by rw [e3]; group
  obtain ⟨-, F, -, HF⟩ := exists_isConjInduced_of_relIsomDGC_field (hDGC D₂.M) θ _ hφ
  haveI : IsFiniteEtale F.hom := MorphismProperty.of_isIso @IsFiniteEtale F.hom
  intro J₂ hJ₂
  obtain ⟨I, hI, hle, hfin⟩ := exists_arithCusps_map_le_of_conjInduced Ω D₁.Y D₁.hY D₂.Y D₂.hY
    F.hom (θ : D₂.Pi →* D₁.Pi) HF hJ₂
  refine ⟨I, hI, ?_⟩
  have e : J₂.map (D₂.ι : D₂.Pi →* A.grp) =
      (J₂.map (θ : D₂.Pi →* D₁.Pi)).map (D₁.ι : D₁.Pi →* A.grp) := by
    rw [Subgroup.map_map]
    exact congrArg (fun g ↦ J₂.map g) (MonoidHom.ext fun σ ↦ (hθ σ).symm)
  rw [e]
  exact (Subgroup.commensurable_of_le hle hfin).map' _

variable (Ω CX hcX) in
/-- **Model independence of cusps** (discharging the hypothesis `hMI` of
`PiChain.IsBelyiType.hasInfCusp_V₃`): any two geometric models of a chain object of `Π_X ↠ G_K`
have the same cuspidal inertia groups up to commensurability, assuming the rel-isom-DGC over
number fields. Both models are compared with sub-models with image `ι₁(Π_{Y₁}) ∩ ι₂(Π_{Y₂})`. -/
theorem modelCuspIndep₂ (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k) :
    ModelCuspIndep₂ Ω CX hcX := by
  intro A D₁ D₂
  let O : Subgroup A.grp := (D₁.ι : D₁.Pi →* A.grp).range ⊓ (D₂.ι : D₂.Pi →* A.grp).range
  have hO : IsOpen (O : Set A.grp) := D₁.isOpen_range.inter D₂.isOpen_range
  have hN : A.Delta ≤ Subgroup.normalizer (O : Set A.grp) := fun g hg n ↦
    and_congr (D₁.normal hg n) (D₂.normal hg n)
  have hle₁ : (O : Set A.grp) ⊆ Set.range D₁.ι := fun _ hx ↦ by
    obtain ⟨⟨y, hy⟩, -⟩ := hx
    exact ⟨y, hy⟩
  have hle₂ : (O : Set A.grp) ⊆ Set.range D₂.ι := fun _ hx ↦ by
    obtain ⟨-, ⟨y, hy⟩⟩ := hx
    exact ⟨y, hy⟩
  obtain ⟨D₁', hr₁, c₁, -⟩ := D₁.exists_sub_cuspCompat₂ O hO hN hle₁
  obtain ⟨D₂', hr₂, -, c₂⟩ := D₂.exists_sub_cuspCompat₂ O hO hN hle₂
  exact cuspCompat_trans₂ c₁
    (cuspCompat_trans₂ (cuspCompat_of_range_eq₂ hDGC (hr₁.trans hr₂.symm)) c₂)

end Models

/-! ### Belyi-type chains -/

section Belyi

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {c : PiChain (arithmeticExt Ω CX hcX)} {l r : ℕ}

/-- **`Π_V` of a Belyi-type chain with a terminal isomorphism has an infinite cusp image**
(the hypothesis `hV` of `PiChain.IsBelyiType.nonempty_geomModel`, `exists_candidate_fill`,
`exists_cover_fill`), assuming only the rel-isom-DGC over number fields. -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.hasInfCusp_V (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k) :
    (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp :=
  hc.hasInfCusp_V₃ t hDGC (modelCuspIndep₂ Ω CX hcX hDGC)

set_option maxHeartbeats 400000 in
-- the existential statement with the chain indices is slow to elaborate
/-- **[AbsTopII] Cor 3.7 (a), converse, without `hV`**: for a Belyi-type chain with a terminal
isomorphism to the trivial chain and `m ≤ r`, the candidate `Π_U ↠ Π_V ↪ Π_X` is
`Π_Y ↠ Π_{Y'} ↪ Π_X` for a filling `Y ⊆ Y'` of one curve over a number field and a finite étale
`q : Spec Γ(U') ⟶ Spec Γ(X)` (`PiChain.IsBelyiType.exists_cover_fill` with
`PiChain.IsBelyiType.hasInfCusp_V`). -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.exists_cover_fill' (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k) (m : ℕ) (hm : m ≤ r) :
    ∃ D : GeomModel Ω CX hcX (c.objN (l + 3 + (r - m)) (by have := hc.len_eq; omega)),
      Function.Surjective D.ι ∧
      ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
        (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
          2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
        (ε : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
          baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* (PiChain.belyiCandidate hc t m hm).PiV),
        (∀ σ, (PiChain.belyiCandidate hc t m hm).surj (D.ι σ) =
          ε (fillPiHom Ω D.Y D.hY h hc' hyp σ)) ∧
        ∃ (q : Spec Γ(D.Y.Xbar, U') ⟶ Spec Γ(CX.Xbar, CX.U)) (_ : IsFiniteEtale q),
          IsConjInduced q (fun τ ↦ (PiChain.belyiCandidate hc t m hm).emb (ε τ) :
            π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
              baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) →
              π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))) ∧
          q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
            Spec.map (CommRingCat.ofHom (algebraMap D.M Γ(D.Y.Xbar, U'))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap K D.M)) :=
  hc.exists_cover_fill t hDGC (hc.hasInfCusp_V t hDGC) m hm

end Belyi

end CurvesJacobian.Cusp
