/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelStep
import CurvesJacobian.Cusp.CoverInstance

/-!
# Model steps across `⋏` and `⋎`: the geometric part (MR8.5, option (A2'))

For a geometric model `D` of a chain object `A` (`CurvesJacobian.Cusp.GeomModel`), i.e. a
hyperbolic curve `Y` over a number field `K ⊆ M ⊆ Ω` with `ι : Π_Y ↪ A`, and an open normal
subgroup `O ⊆ Π_Y`, the connected finite étale cover `Y' → Y` attached to `O` (Galois
correspondence, `CurvesJacobian.Cusp.exists_isFiniteEtale_range_eq`) is a hyperbolic curve over
its constant field `M'` (`CurvesJacobian.Cusp.coverCurve`), and `Π_{Y'} ≅ O` compatibly with the
projections to `G_K` (`CurvesJacobian.Cusp.toG_coverCurvePiEquiv`). Hence:

* **`GeomModel.exists_ofSub`**: a model `D'` of `A` with `ι'(Π_{Y'}) = ι(O)` (provided `ι(O)` is
  normalised by `Δ_A`); `GeomModel.ofSub` is a choice of it.
* `GeomModel.map`: transport of a model along an open embedding `φ : A ↪ B` compatible with the
  projections to `G` (type `⋎`).
* `GeomModel.comap`: restriction of a model to an open embedding `φ : B ↪ A` whose image contains
  `ι(Π_Y)` (type `⋏`).
* **`GeomModel.ofQuot`** (type `⋎`, `φ : A ↪ B`) and **`GeomModel.ofCover`** (type `⋏`,
  `φ : B ↪ A`): models of the next chain object, with image the normal cores of
  `CurvesJacobian.Cusp.GeomModel.quotCore` resp. `CurvesJacobian.Cusp.GeomModel.coverCore`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Res

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω] (M M' : Type u) [Field M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Field M'] [Algebra K M'] [Algebra M M'] [Algebra M' Ω] [IsScalarTower K M' Ω]
  [IsScalarTower M M' Ω] [IsScalarTower K M M']

omit [IsSepClosed Ω] [IsGalois K Ω] in
/-- **`res_{K,M} ∘ ι_{M,M'} = res_{K,M'}`** (functoriality of `π₁ᵉᵗ` of `Spec`). -/
lemma resGal_galoisMap (s : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M' Ω)))) :
    resGal K Ω M (galoisMap M M' Ω s) = resGal K Ω M' s := by
  have e : sKM K M' = Spec.map (CommRingCat.ofHom (algebraMap M M')) ≫ sKM K M := by
    rw [sKM, sKM, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h3 : Spec.map (CommRingCat.ofHom (algebraMap M' Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M M')) ≫ sKM K M =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [← e]
    exact sM_sKM M'
  have c := DFunLike.congr_fun (fundamentalGroupMap_comp _ _
    (specMap_algebraMap_tower M M' Ω) (sM_sKM M) h3) s
  rw [← fundamentalGroupMap_congr e (sM_sKM M') h3] at c
  exact c.symm

end Res

namespace GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A B : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-! ### Transport along open embeddings -/

lemma range_comp_ι (φ : A.grp →ₜ* B.grp) :
    Set.range (φ.comp D.ι) = (φ : A.grp → B.grp) '' Set.range D.ι := by
  ext b
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨D.ι σ, ⟨σ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, rfl⟩

/-- **Transport of a model along an open embedding `φ : A ↪ B`** compatible with the projections
to `G` (`ι' = φ ∘ ι`). -/
def map (φ : A.grp →ₜ* B.grp) (hinj : Function.Injective φ) (hφ : IsOpen (Set.range φ))
    (hG : ∀ a, B.toG (φ a) = A.toG a) (hN : B.Delta ≤ Subgroup.normalizer (Set.range (φ ∘ D.ι))) :
    GeomModel Ω CX hcX B where
  M := D.M
  Y := D.Y
  hY := D.hY
  ι := φ.comp D.ι
  inj := hinj.comp D.inj
  isOpen_range := by
    have h := isOpen_map_of_isOpen_range φ hφ D.isOpen_rangeι
    rw [Subgroup.coe_map, MonoidHom.coe_range] at h
    convert h using 1
    exact D.range_comp_ι φ
  normal := hN
  toG_eq := ⟨D.g₀, fun σ ↦ by
    change B.toG (φ (D.ι σ)) = _
    rw [hG]
    exact D.toG_ι σ⟩

lemma range_map (φ : A.grp →ₜ* B.grp) (hinj : Function.Injective φ) (hφ : IsOpen (Set.range φ))
    (hG : ∀ a, B.toG (φ a) = A.toG a) (hN : B.Delta ≤ Subgroup.normalizer (Set.range (φ ∘ D.ι))) :
    Set.range (D.map φ hinj hφ hG hN).ι = φ '' Set.range D.ι :=
  D.range_comp_ι φ

/-- `ι` factors through an embedding `φ : B ↪ A` whose image contains `ι(Π_Y)`. -/
def comapFun (φ : B.grp →ₜ* A.grp) (hle : Set.range D.ι ⊆ Set.range φ) (σ : D.Pi) : B.grp :=
  (hle ⟨σ, rfl⟩).choose

lemma φ_comapFun (φ : B.grp →ₜ* A.grp) (hle : Set.range D.ι ⊆ Set.range φ) (σ : D.Pi) :
    φ (D.comapFun φ hle σ) = D.ι σ :=
  (hle ⟨σ, rfl⟩).choose_spec

/-- `ι` factored through `φ : B ↪ A`, as a continuous homomorphism `Π_Y → B`. -/
def comapι (φ : B.grp →ₜ* A.grp) (hinj : Function.Injective φ)
    (hle : Set.range D.ι ⊆ Set.range φ) : D.Pi →ₜ* B.grp where
  toFun := D.comapFun φ hle
  map_one' := hinj (by rw [φ_comapFun, map_one, map_one])
  map_mul' a b := hinj (by rw [φ_comapFun, map_mul, map_mul, φ_comapFun, φ_comapFun])
  continuous_toFun := by
    have hemb : Topology.IsEmbedding φ := (φ.continuous.isClosedEmbedding hinj).isEmbedding
    refine hemb.continuous_iff.2 ?_
    have : (φ ∘ D.comapFun φ hle) = D.ι := funext (D.φ_comapFun φ hle)
    rw [this]
    exact D.ι.continuous

lemma φ_comapι (φ : B.grp →ₜ* A.grp) (hinj : Function.Injective φ)
    (hle : Set.range D.ι ⊆ Set.range φ) (σ : D.Pi) : φ (D.comapι φ hinj hle σ) = D.ι σ :=
  D.φ_comapFun φ hle σ

lemma range_comapι (φ : B.grp →ₜ* A.grp) (hinj : Function.Injective φ)
    (hle : Set.range D.ι ⊆ Set.range φ) :
    Set.range (D.comapι φ hinj hle) = φ ⁻¹' Set.range D.ι := by
  ext b
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, (D.φ_comapι φ hinj hle σ).symm⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, hinj ((D.φ_comapι φ hinj hle σ).trans hσ)⟩

/-- **Restriction of a model to an open embedding `φ : B ↪ A` containing `ι(Π_Y)`**
(`φ ∘ ι' = ι`). -/
def comap (φ : B.grp →ₜ* A.grp) (hinj : Function.Injective φ)
    (hle : Set.range D.ι ⊆ Set.range φ) (hG : ∀ b, A.toG (φ b) = B.toG b)
    (hN : B.Delta ≤ Subgroup.normalizer (φ ⁻¹' Set.range D.ι)) : GeomModel Ω CX hcX B where
  M := D.M
  Y := D.Y
  hY := D.hY
  ι := D.comapι φ hinj hle
  inj := fun a b h ↦ D.inj (by rw [← D.φ_comapι φ hinj hle a, h, D.φ_comapι])
  isOpen_range := by
    rw [range_comapι]
    exact D.isOpen_range.preimage φ.continuous
  normal := by
    rw [range_comapι]
    exact hN
  toG_eq := ⟨D.g₀, fun σ ↦ by
    change B.toG (D.comapι φ hinj hle σ) = _
    rw [← hG, φ_comapι]
    exact D.toG_ι σ⟩

lemma range_comap (φ : B.grp →ₜ* A.grp) (hinj : Function.Injective φ)
    (hle : Set.range D.ι ⊆ Set.range φ) (hG : ∀ b, A.toG (φ b) = B.toG b)
    (hN : B.Delta ≤ Subgroup.normalizer (φ ⁻¹' Set.range D.ι)) :
    Set.range (D.comap φ hinj hle hG hN).ι = φ ⁻¹' Set.range D.ι :=
  D.range_comapι φ hinj hle

/-! ### The cover attached to an open normal subgroup of `Π_Y` -/

lemma range_mk {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω]
    [IsScalarTower K M Ω] [FiniteDimensional K M] (Y : HypCurve M)
    (hY : (Y.U : Set Y.Xbar)ᶜ.Nonempty)
    (ι : π₁ᵉᵗ(basePoint Ω Y hY ≫ baseChangeSpec M Ω Γ(Y.Xbar, Y.U)) →ₜ* A.grp)
    (inj : Function.Injective ι) (ho : IsOpen (Set.range ι))
    (hn : A.Delta ≤ Subgroup.normalizer (Set.range ι))
    (hg : ∃ g₀ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))), ∀ σ,
      toGk A (ι σ) = g₀ * resGal K Ω M (projGk Ω Y hY σ) * g₀⁻¹) :
    Set.range (GeomModel.mk M Y hY ι inj ho hn hg : GeomModel Ω CX hcX A).ι = Set.range ι :=
  rfl

set_option maxHeartbeats 400000 in
-- the cover curve, its constant field and `Π_{Y'} ≃ O` are large terms
/-- **The cover step** ([AbsTopI] Def 4.2 (iii)(a), Remark 4.2.1): for an open normal subgroup
`O ⊆ Π_Y` whose image `ι(O)` is normalised by `Δ_A`, there is a model `D'` of `A` with
`ι'(Π_{Y'}) = ι(O)`: `Y'` is the connected finite étale cover of `Y` attached to `O`, a hyperbolic
curve over its constant field. -/
theorem exists_ofSub (O : Subgroup D.Pi) (hO : IsOpen (O : Set D.Pi)) [O.Normal]
    (hN : A.Delta ≤ Subgroup.normalizer (D.ι '' O)) :
    ∃ D' : GeomModel Ω CX hcX A, Set.range D'.ι = D.ι '' O := by
  haveI := isIntegral_specSections D.Y D.hY
  set η' := basePoint Ω D.Y D.hY ≫ baseChangeSpec D.M Ω Γ(D.Y.Xbar, D.Y.U)
  obtain ⟨V, f, hf, hV, hrange⟩ :=
    exists_isFiniteEtale_range_eq (Ω := Ω) η' ⟨O, hO⟩
  haveI := hV
  haveI : IsConnected (coverObj f) := (isConnected_iff_connectedSpace (coverObj f)).2 hV
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected (fiber η') (coverObj f)
  set ζ := (fiberObjEquivHom η' (coverObj f) x).left
  have hζ : ζ ≫ f = η' := w_left _
  -- the cover curve `Y'` over `M'`
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
  -- `Π_{Y'} → O ⊆ Π_Y`
  let j : (coverChainObj Ω D.Y D.hY f ζ hζ).grp →ₜ* D.Pi :=
    ⟨(coverSubgroup f ζ hζ : Subgroup π₁ᵉᵗ(η')).subtype, continuous_subtype_val⟩
  have hjO : Set.range j = (O : Set D.Pi) := by
    have h1 := hrange ζ hζ
    rw [range_fundamentalGroupMap_eq_coverSubgroup] at h1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (SetLike.ext_iff.1 h1 _).1 x.2
    · intro hy
      exact ⟨⟨y, (SetLike.ext_iff.1 h1 y).2 hy⟩, rfl⟩
  have hrangeι : Set.range (D.ι.comp (j.comp (ContinuousMonoidHom.toContinuousMonoidHom e))) =
      D.ι '' O := by
    rw [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_comp, Set.range_comp,
      Set.range_comp, ContinuousMonoidHom.coe_coe, e.surjective.range_eq, Set.image_univ, hjO]
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
    have h := isOpen_map_of_isOpen_range D.ι D.isOpen_range hO
    rw [Subgroup.coe_map] at h
    convert h using 1
    exact hrangeι
  have hnorm : A.Delta ≤ Subgroup.normalizer (Set.range (D.ι.comp (j.comp
      (ContinuousMonoidHom.toContinuousMonoidHom e)))) := by
    convert hN using 2
  have hinj' := D.inj.comp (Subtype.val_injective.comp e.injective)
  have hR := range_mk (M := M') (coverCurve D.Y D.hY f) (coverCurve_cusp D.Y D.hY f) _
    hinj' hopen hnorm ⟨D.g₀ * resGal K Ω D.M c, key'⟩
  exact ⟨_, hR.trans hrangeι⟩

/-- **The model of the cover attached to `O`** (a choice in `exists_ofSub`). -/
def ofSub (O : Subgroup D.Pi) (hO : IsOpen (O : Set D.Pi)) [O.Normal]
    (hN : A.Delta ≤ Subgroup.normalizer (D.ι '' O)) : GeomModel Ω CX hcX A :=
  (D.exists_ofSub O hO hN).choose

lemma range_ofSub (O : Subgroup D.Pi) (hO : IsOpen (O : Set D.Pi)) [O.Normal]
    (hN : A.Delta ≤ Subgroup.normalizer (D.ι '' O)) :
    Set.range (D.ofSub O hO hN).ι = D.ι '' O :=
  (D.exists_ofSub O hO hN).choose_spec

/-! ### The steps `⋎` and `⋏` -/

/-- A subgroup with normal image is normalised by everything. -/
lemma le_normalizer_of_normal {G : Type*} [Group G] {S : Set G} (H : Subgroup G) [H.Normal]
    (hS : S = H) (L : Subgroup G) : L ≤ Subgroup.normalizer S := by
  subst hS
  rw [Subgroup.normalizer_eq_top]
  exact le_top

lemma image_quotSub (φ : A.grp →ₜ* B.grp) :
    (φ : A.grp → B.grp) '' (D.ι '' (D.quotSub φ : Set D.Pi)) = D.quotCore φ := by
  rw [← D.map_quotSub φ, Subgroup.coe_map, Set.image_image]
  rfl

lemma image_coverSub (φ : B.grp →ₜ* A.grp) :
    D.ι '' (D.coverSub φ : Set D.Pi) = D.coverCore φ := by
  rw [← D.map_coverSub φ, Subgroup.coe_map]
  rfl

lemma image_quotSub_eq_comap (φ : A.grp →ₜ* B.grp) (hinj : Function.Injective φ) :
    D.ι '' (D.quotSub φ : Set D.Pi) = (D.quotCore φ).comap (φ : A.grp →* B.grp) := by
  rw [Subgroup.coe_comap, ← D.image_quotSub φ]
  exact (Set.preimage_image_eq _ hinj).symm

/-- **The model step across `⋎`** (`φ : A ↪ B` open, compatible with the projections to `G`):
a model of `B` with image `core_B(φ(ι Π_Y))` (`GeomModel.quotCore`). -/
def ofQuot (φ : A.grp →ₜ* B.grp) (hinj : Function.Injective φ) (hφ : IsOpen (Set.range φ))
    (hG : ∀ a, B.toG (φ a) = A.toG a) : GeomModel Ω CX hcX B :=
  (D.ofSub (D.quotSub φ) (D.isOpen_quotSub φ hφ)
    (le_normalizer_of_normal _ (D.image_quotSub_eq_comap φ hinj) _)).map φ hinj hφ hG
    (le_normalizer_of_normal (D.quotCore φ) (by
      rw [Set.range_comp, range_ofSub, image_quotSub]) _)

lemma range_ofQuot (φ : A.grp →ₜ* B.grp) (hinj : Function.Injective φ)
    (hφ : IsOpen (Set.range φ)) (hG : ∀ a, B.toG (φ a) = A.toG a) :
    Set.range (D.ofQuot φ hinj hφ hG).ι = D.quotCore φ := by
  rw [ofQuot, range_map, range_ofSub, image_quotSub]

/-- **The model step across `⋏`** (`φ : B ↪ A` open, compatible with the projections to `G`):
a model of `B` with image `coverSubB = φ⁻¹(core_A(ι Π_Y ∩ φ B))` (`GeomModel.coverCore`). -/
def ofCover (φ : B.grp →ₜ* A.grp) (hinj : Function.Injective φ) (hφ : IsOpen (Set.range φ))
    (hG : ∀ b, A.toG (φ b) = B.toG b) : GeomModel Ω CX hcX B :=
  (D.ofSub (D.coverSub φ) (D.isOpen_coverSub φ hφ)
    (le_normalizer_of_normal (D.coverCore φ) (D.image_coverSub φ) A.Delta)).comap φ hinj
    (by
      rw [range_ofSub, image_coverSub]
      intro a ha
      exact (Subgroup.normalCore_le _ ha).2)
    hG
    (le_normalizer_of_normal (D.coverSubB φ) (by rw [range_ofSub, image_coverSub]; ext; rfl) _)

lemma range_ofCover (φ : B.grp →ₜ* A.grp) (hinj : Function.Injective φ)
    (hφ : IsOpen (Set.range φ)) (hG : ∀ b, A.toG (φ b) = B.toG b) :
    Set.range (D.ofCover φ hinj hφ hG).ι = D.coverSubB φ := by
  rw [ofCover, range_comap, range_ofSub, image_coverSub]
  ext
  rfl

end GeomModel

end CurvesJacobian.Cusp
