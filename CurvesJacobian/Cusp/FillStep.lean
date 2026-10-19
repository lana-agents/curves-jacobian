/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FillElemOp

/-!
# Iterated filling of cusps: `•` operations between filled chain objects

[AbsTopI] Definition 4.2 (iii) (c) (`Topics in Absolute Anabelian Geometry I.txt`,
l.3009–3015). `CurvesJacobian.Cusp.fillElemOp` is the operation `Π_U ⇝ Π_{U'}` of type `•`
starting at the trivial chain object `Π₀ = Π_U`. Runs `•, …, •` of [AbsTopII] Example 3.6 and
Corollary 3.7 continue from `Π_{U₁}` (a chain object over `Π_U`, `fillChainObj`): for
`U ⊆ U₁ ⊆ U₂ = U₁ ∪ {x}`, the map `Π_{U₁} → Π_{U₂}` induced by `Spec Γ(U₁) → Spec Γ(U₂)` is an
operation of type `•` between the chain objects `fillChainObj U₁` and `fillChainObj U₂`
(`CurvesJacobian.Cusp.fillStepElemOp`). The cuspidal decomposition group of `Δ_{U₁}` of
condition (3Π) is the image of a cuspidal inertia group of `Π_U` (the cusps of `U₁` are cusps
of `U`).

## Main results

* `exists_conjAut_eq_conj`: two isomorphisms of fibre functors induce isomorphisms of
  automorphism groups which differ by an inner automorphism;
* `fillMap_geomToPi`: `fillMap ∘ geomToPi_U = geomToPiFill ∘ (π₁ᵉᵗ(U_Ω) → π₁ᵉᵗ(U'_Ω))`;
* `fillTransport_geomToPi`: the change of base point `Π_{U'}(basePoint) ≃ Π_{U'}(fillPoint)`
  maps `geomToPi` of the curve `(X̄, U')` to a conjugate of `geomToPiFill`;
* **`exists_mem_arithCusps_map_fillMap`**: every cuspidal inertia group of `Π_{U'}` (transported
  to `fillPoint`) is the image under `fillMap` of a cuspidal inertia group of `Π_U`;
* **`fillStepElemOp`**: the operation `fillChainObj U₁ ⇝ fillChainObj U₂` of type `•`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
open Pi1.Orbifold AffOrbicurve PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section ConjAut

variable {𝒞 : Type*} [Category 𝒞] {X Y : 𝒞}

/-- Two isomorphisms `α, α' : X ≅ Y` conjugate automorphisms of `X` to automorphisms of `Y`
differing by an inner automorphism (by `τ = α⁻¹ ≫ α'`). -/
lemma exists_conjAut_eq_conj (α α' : X ≅ Y) :
    ∃ t : Aut Y, ∀ σ : Aut X, α'.conjAut σ = t * α.conjAut σ * t⁻¹ := by
  refine ⟨α.symm ≪≫ α', fun σ ↦ ?_⟩
  rw [Aut.Aut_mul_def, Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.conjAut_apply, Iso.conjAut_apply]
  ext
  simp

end ConjAut

section Group

variable {G G' : Type*} [Group G] [Group G']

/-- Commensurators are transported along group isomorphisms. -/
lemma commensurator_map_mulEquiv (e : G ≃* G') (H : Subgroup G) :
    (Subgroup.Commensurable.commensurator H).map e.toMonoidHom =
      Subgroup.Commensurable.commensurator (H.map e.toMonoidHom) := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    Subgroup.Commensurable.commensurator_mem_iff, Subgroup.Commensurable.commensurator_mem_iff,
    conjAct_smul_eq_map, conjAct_smul_eq_map]
  have e1 : (H.map e.toMonoidHom).map (MulAut.conj (e y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext q
    simp
  rw [e1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
      exact h1
    · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
      exact h2
  · rintro ⟨h1, h2⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective] at h1 h2
    exact ⟨h1, h2⟩

variable [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']

/-- Closed normal closures are transported along isomorphisms of topological groups. -/
lemma map_topologicalClosure_normalClosure (e : G ≃ₜ* G') (s : Set G) :
    (Subgroup.normalClosure s).topologicalClosure.map e.toMulEquiv.toMonoidHom =
      (Subgroup.normalClosure (e '' s)).topologicalClosure := by
  have hn : (Subgroup.normalClosure s).map e.toMulEquiv.toMonoidHom =
      Subgroup.normalClosure (e '' s) :=
    Subgroup.map_normalClosure s e.toMulEquiv.toMonoidHom e.surjective
  apply SetLike.coe_injective
  rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hn,
    Subgroup.coe_map]
  exact e.toHomeomorph.image_closure _

end Group

/-! ### Cuspidal inertia under filling -/

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens} (h : C.U ≤ U')
  (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

set_option backward.isDefEq.respectTransparency false

omit [NumberField K] [Algebra.IsAlgebraic K Ω] in
/-- Places centred on a smaller open are centred on a larger one. -/
lemma isCentredOn_mono {V V' : (geomCurve Ω C).Opens} [Nonempty V] [Nonempty V'] (hV : V ≤ V')
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) V W) :
    IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) V' W := by
  refine ⟨hW.1, fun a ↦ ?_⟩
  have e : (geomCurve Ω C).germToFunctionField V' a =
      (geomCurve Ω C).germToFunctionField V ((geomCurve Ω C).presheaf.map (homOfLE hV).op a) := by
    change (geomCurve Ω C).presheaf.germ V' _ _ a = (geomCurve Ω C).presheaf.germ V _ _ _
    rw [TopCat.Presheaf.germ_res_apply]
  rw [e]
  exact hW.2 _

variable [Nonempty (baseChangeOpen K Ω U')]

/-- `π₁ᵉᵗ(U_Ω) → π₁ᵉᵗ(U'_Ω)` at the generic geometric points. -/
abbrev geomFill := fundamentalGroupMap
  ((geomCurve Ω C).homOfLE (baseChangeOpen_mono K Ω h))
  (specPoint_genericL_homOfLE (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (baseChangeOpen_mono K Ω h))

omit [Nonempty (baseChangeOpen K Ω U')] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
include hc' in
lemma basePoint_iso_homOfLE :
    (basePoint Ω C hc ≫ (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).hom) ≫
      (geomCurve Ω C).homOfLE (baseChangeOpen_mono K Ω h) = fillPoint Ω C hc h ≫
        (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_of_le C h hc')).hom := by
  rw [Category.assoc, specTensorIso_hom_homOfLE, fillPoint, Category.assoc]

/-- The isomorphism of fibre functors of `U'_Ω` from the generic geometric point to (the image
of) `fillPoint`, induced by `basePointIso` of `U_Ω`. -/
def fillPointIso : fiber (specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
    genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (baseChangeOpen K Ω U')) ≅
    fiber (fillPoint Ω C hc h ≫
      (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_of_le C h hc')).hom) :=
  fiberIsoMap ((geomCurve Ω C).homOfLE (baseChangeOpen_mono K Ω h))
    (specPoint_genericL_homOfLE (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (baseChangeOpen_mono K Ω h))
    (basePoint_iso_homOfLE Ω C hc h hc') (basePointIso Ω C hc)

/-- `π₁ᵉᵗ(U'_Ω, generic point) → Π_{U'}` at the base point `fillPoint` (analogue of
`geomToPi`). -/
def geomToPiFill (g : π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
    genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (baseChangeOpen K Ω U'))) :
    π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')) :=
  fundamentalGroupMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl
    ((fundamentalGroupEquivOfIso (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_of_le C h hc'))
      (fillPoint Ω C hc h)).symm (autContinuousMulEquivOfIso (fillPointIso Ω C hc h hc') g))

omit [Algebra.IsAlgebraic K Ω] in
lemma geomToPiFill_mul (a b) : geomToPiFill Ω C hc h hc' (a * b) =
    geomToPiFill Ω C hc h hc' a * geomToPiFill Ω C hc h hc' b := by
  simp only [geomToPiFill, map_mul]

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Nonempty (baseChangeOpen K Ω U')] in
lemma fillMap_fundamentalGroupMap_baseChangeSpec (δ) :
    fillMap Ω C hc h (fundamentalGroupMap (baseChangeSpec K Ω Γ(C.Xbar, C.U))
      (rfl : basePoint Ω C hc ≫ _ = _) δ) =
    fundamentalGroupMap (baseChangeSpec K Ω Γ(C.Xbar, U')) (rfl : fillPoint Ω C hc h ≫ _ = _)
      (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (tensorRes K Ω h).toRingHom))
        (rfl : basePoint Ω C hc ≫ _ = fillPoint Ω C hc h) δ) := by
  have c1 := fundamentalGroupMap_comp (baseChangeSpec K Ω Γ(C.Xbar, C.U))
    (Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (rfl : basePoint Ω C hc ≫ _ = _)
    (fillPoint_spec Ω C hc h) ((Category.assoc _ _ _).symm.trans (fillPoint_spec Ω C hc h))
  have c2 := fundamentalGroupMap_comp
    (Spec.map (CommRingCat.ofHom (tensorRes K Ω h).toRingHom))
    (baseChangeSpec K Ω Γ(C.Xbar, U')) (rfl : basePoint Ω C hc ≫ _ = fillPoint Ω C hc h) rfl
    (Category.assoc _ _ _).symm
  have c3 := fundamentalGroupMap_congr (specMap_tensorRes_baseChangeSpec K Ω h).symm
    ((Category.assoc (basePoint Ω C hc) _ _).symm.trans (fillPoint_spec Ω C hc h))
    (Category.assoc (basePoint Ω C hc) _ _).symm
  exact congrArg (fun φ : _ →ₜ* _ ↦ φ δ) (c1.symm.trans (c3.trans c2))

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Nonempty (baseChangeOpen K Ω U')] in
lemma fundamentalGroupMap_homOfLE_specTensorIso (δ) :
    fundamentalGroupMap ((geomCurve Ω C).homOfLE (baseChangeOpen_mono K Ω h))
      (basePoint_iso_homOfLE Ω C hc h hc')
      (fundamentalGroupMap (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).hom rfl δ) =
    fundamentalGroupMap (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_of_le C h hc')).hom rfl
      (fundamentalGroupMap (Spec.map (CommRingCat.ofHom (tensorRes K Ω h).toRingHom))
        (rfl : basePoint Ω C hc ≫ _ = fillPoint Ω C hc h) δ) := by
  have c1 := fundamentalGroupMap_comp (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C
      hc)).hom ((geomCurve Ω C).homOfLE (baseChangeOpen_mono K Ω h))
    (rfl : basePoint Ω C hc ≫ (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).hom = _)
    (basePoint_iso_homOfLE Ω C hc h hc')
    ((Category.assoc _ _ _).symm.trans (basePoint_iso_homOfLE Ω C hc h hc'))
  have c2 := fundamentalGroupMap_comp
    (Spec.map (CommRingCat.ofHom (tensorRes K Ω h).toRingHom)) (specTensorIsoBaseChangeOpen K Ω
        (isAffineOpen_of_le C h hc')).hom
    (rfl : basePoint Ω C hc ≫ _ = fillPoint Ω C hc h) rfl (Category.assoc _ _ _).symm
  have c3 := fundamentalGroupMap_congr
    (specTensorIso_hom_homOfLE K Ω (isAffineOpen_U C hc) (isAffineOpen_of_le C h hc') h)
    ((Category.assoc (basePoint Ω C hc) _ _).symm.trans (basePoint_iso_homOfLE Ω C hc h hc'))
    (Category.assoc (basePoint Ω C hc) _ _).symm
  exact congrArg (fun φ : _ →ₜ* _ ↦ φ δ) (c1.symm.trans (c3.trans c2))

/-- **`fillMap ∘ geomToPi = geomToPiFill ∘ geomFill`.** -/
theorem fillMap_geomToPi (g) :
    fillMap Ω C hc h (geomToPi Ω C hc g) = geomToPiFill Ω C hc h hc' (geomFill Ω C h g) := by
  haveI := isIntegral_specSections C hc
  haveI := isIntegral_specTensor Ω C hc
  haveI := isIntegral_specTensor_of_le Ω C h hc'
  rw [geomToPi_eq, fillMap_fundamentalGroupMap_baseChangeSpec, geomToPiFill]
  refine congrArg (fundamentalGroupMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl) ?_
  apply (fundamentalGroupEquivOfIso (specTensorIsoBaseChangeOpen K Ω
    (isAffineOpen_of_le C h hc')) (fillPoint Ω C hc h)).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  change fundamentalGroupMap (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_of_le C h hc')).hom rfl
    _ = _
  refine (fundamentalGroupMap_homOfLE_specTensorIso Ω C hc h hc' _).symm.trans ?_
  change fundamentalGroupMap _ _ ((fundamentalGroupEquivOfIso (specTensorIsoBaseChangeOpen K Ω
    (isAffineOpen_U C hc)) (basePoint Ω C hc)) ((fundamentalGroupEquivOfIso
      (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)) (basePoint Ω C hc)).symm
        (basePointEquiv Ω C hc g))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact fundamentalGroupMap_autContinuousMulEquivOfIso _ _ _ _ g

variable (hyp : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U')

/-- **Base point change and `geomToPi`**: for an isomorphism of fibre functors `α₀` of
`Spec (Ω ⊗ Γ(U'))` from the base point of the curve `(X̄, U')` to `fillPoint`, the induced
isomorphism `Π_{U'}(basePoint) ≃ Π_{U'}(fillPoint)` maps `geomToPi` of `(X̄, U')` to a conjugate
of `geomToPiFill`. -/
theorem fillTransport_geomToPi
    (α₀ : fiber (basePoint Ω (fillCurve C h hyp) hc') ≅ fiber (fillPoint Ω C hc h)) :
    ∃ t : π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')), ∀ g,
      autContinuousMulEquivOfIso
      (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)
        (geomToPi Ω (fillCurve C h hyp) hc' g) = t * geomToPiFill Ω C hc h hc' g * t⁻¹ := by
  haveI := isIntegral_specTensor_of_le Ω C h hc'
  haveI := isIntegral_specTensor Ω (fillCurve C h hyp) hc'
  let e := specTensorIsoBaseChangeOpen K Ω (isAffineOpen_of_le C h hc')
  let α₁ := fiberIsoMap e.hom rfl rfl α₀
  obtain ⟨τ, hτ⟩ := exists_conjAut_eq_conj (fillPointIso Ω C hc h hc')
    (basePointIso Ω (fillCurve C h hyp) hc' ≪≫ α₁)
  let ι' := fundamentalGroupEquivOfIso e (fillPoint Ω C hc h)
  let ι := fundamentalGroupEquivOfIso e (basePoint Ω (fillCurve C h hyp) hc')
  have hι : ∀ y, autContinuousMulEquivOfIso α₀ (ι.symm y) =
      ι'.symm (autContinuousMulEquivOfIso α₁ y) := by
    intro y
    apply ι'.injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    change fundamentalGroupMap e.hom rfl _ = _
    refine (fundamentalGroupMap_autContinuousMulEquivOfIso e.hom rfl rfl α₀ _).trans ?_
    congr 1
    exact ι.apply_symm_apply y
  refine ⟨fundamentalGroupMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl (ι'.symm τ), fun g ↦ ?_⟩
  rw [geomToPi_eq]
  refine (fundamentalGroupMap_autContinuousMulEquivOfIso (baseChangeSpec K Ω Γ(C.Xbar, U'))
    rfl rfl α₀ _).symm.trans ?_
  change fundamentalGroupMap _ rfl (autContinuousMulEquivOfIso α₀ (ι.symm
    (basePointEquiv Ω (fillCurve C h hyp) hc' g))) = _
  rw [hι]
  have e2 : autContinuousMulEquivOfIso α₁ (basePointEquiv Ω (fillCurve C h hyp) hc' g) =
      τ * autContinuousMulEquivOfIso (fillPointIso Ω C hc h hc') g * τ⁻¹ := by
    exact (Iso.trans_conjAut _ _ _).symm.trans (hτ g)
  rw [e2]
  let β'' : π₁ᵉᵗ(fillPoint Ω C hc h ≫ e.hom) →*
      π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')) :=
    (fundamentalGroupMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl).toMonoidHom.comp
      ι'.symm.toMulEquiv.toMonoidHom
  change β'' (τ * _ * τ⁻¹) = β'' τ * β'' _ * (β'' τ)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- **Cuspidal inertia groups of `Π_{U'}` come from `Π_U`**: after the change of base point of
`fillTransport_geomToPi`, every cuspidal inertia group of the curve `(X̄, U')` is the image under
`fillMap : Π_U ↠ Π_{U'}` of a cuspidal inertia group of `Π_U`. -/
theorem exists_mem_arithCusps_map_fillMap
    (α₀ : fiber (basePoint Ω (fillCurve C h hyp) hc') ≅ fiber (fillPoint Ω C hc h))
    {J} (hJ : J ∈ arithCusps Ω (fillCurve C h hyp) hc') :
    ∃ I ∈ arithCusps Ω C hc, I.map (fillMap Ω C hc h).toMonoidHom =
      J.map (autContinuousMulEquivOfIso
        (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)).toMulEquiv.toMonoidHom := by
  obtain ⟨_, ⟨W, hkW, hWU', rfl⟩, g, rfl⟩ := hJ
  obtain ⟨t, ht⟩ := fillTransport_geomToPi Ω C hc h hc' hyp α₀
  let T : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec K Ω Γ(C.Xbar, U')) ≃ₜ*
      π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')) := autContinuousMulEquivOfIso
    (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)
  obtain ⟨s, hs⟩ := fillMap_surjective Ω C hc h hc' (T g * t)
  have hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W :=
    fun hW ↦ hWU' (isCentredOn_mono Ω C (baseChangeOpen_mono K Ω h) hW)
  refine ⟨((geomCuspInertia Ω C W).map (geomToPi Ω C hc)).map (MulAut.conj s).toMonoidHom,
    ⟨_, ⟨W, hkW, hWU, rfl⟩, s, rfl⟩, ?_⟩
  have hmap := map_cuspInertia_homOfLE (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C)) (baseChangeOpen_mono K Ω h) W
  change _ = (((cuspInertia (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C)) (baseChangeOpen K Ω U') W).map
      (geomToPi Ω (fillCurve C h hyp) hc')).map (MulAut.conj g).toMonoidHom).map
        T.toMulEquiv.toMonoidHom
  have hf : ((fillMap Ω C hc h).toMonoidHom.comp (MulAut.conj s).toMonoidHom).comp
      (geomToPi Ω C hc) = ((T.toMulEquiv.toMonoidHom.comp (MulAut.conj g).toMonoidHom).comp
        (geomToPi Ω (fillCurve C h hyp) hc')).comp (geomFill Ω C h).toMonoidHom := by
    refine MonoidHom.ext fun x ↦ ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, ContinuousMonoidHom.coe_toMonoidHom, map_mul, map_inv]
    have e1 := fillMap_geomToPi Ω C hc h hc' x
    have e2 := ht (geomFill Ω C h x)
    have k1 : fillMap Ω C hc h s * fillMap Ω C hc h (geomToPi Ω C hc x) * (fillMap Ω C hc h s)⁻¹ =
        (T g * t) * geomToPiFill Ω C hc h hc' (geomFill Ω C h x) * (T g * t)⁻¹ := by
      rw [hs, e1]
    have k2 : T (g * geomToPi Ω (fillCurve C h hyp) hc' (geomFill Ω C h x) * g⁻¹) =
        T g * (t * geomToPiFill Ω C hc h hc' (geomFill Ω C h x) * t⁻¹) * (T g)⁻¹ := by
      rw [map_mul, map_mul, map_inv, ← e2]
    refine k1.trans (Eq.trans ?_ k2.symm)
    group
  rw [← hmap]
  refine ((Subgroup.map_map _ _ _).trans (Subgroup.map_map _ _ _)).trans
    (Eq.trans ?_ ((Subgroup.map_map _ _ _).trans ((Subgroup.map_map _ _ _).trans
      (Subgroup.map_map _ _ _))).symm)
  exact congrArg (fun f ↦ Subgroup.map f (geomCuspInertia Ω C W)) hf


/-! ### The operation `Π_{U₁} ⇝ Π_{U₂}` of type `•` -/

section Step

omit [NumberField K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  [Nonempty (baseChangeOpen K Ω U')] in
lemma specMap_resAlg_comp {U₁ U₂ : C.Xbar.Opens} (h₁ : C.U ≤ U₁) (h₂ : U₁ ≤ U₂) :
    Spec.map (CommRingCat.ofHom (resAlg K h₁).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (resAlg K h₂).toRingHom) =
    Spec.map (CommRingCat.ofHom (resAlg K (h₁.trans h₂)).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  ext a
  change (Scheme.Hom.appLE (𝟙 C.Xbar) U₂ U₁ h₂ ≫ Scheme.Hom.appLE (𝟙 C.Xbar) U₁ C.U h₁) a =
    Scheme.Hom.appLE (𝟙 C.Xbar) U₂ C.U (h₁.trans h₂) a
  rw [Scheme.Hom.appLE_comp_appLE]
  simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Hom.id_app, Category.id_comp,
    Category.comp_id]

variable {U₁ U₂ : C.Xbar.Opens} (h₁ : C.U ≤ U₁) (h₂ : U₁ ≤ U₂)
  (hc₁ : (U₁ : Set C.Xbar)ᶜ.Nonempty) (hc₂ : (U₂ : Set C.Xbar)ᶜ.Nonempty)
  (hyp₁ : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U₁)
  (hyp₂ : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U₂)

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Nonempty (baseChangeOpen K Ω U')] in
lemma fillPoint_step :
    (fillPoint Ω C hc h₁ ≫ baseChangeSpec K Ω Γ(C.Xbar, U₁)) ≫
        Spec.map (CommRingCat.ofHom (resAlg K h₂).toRingHom) =
      fillPoint Ω C hc (h₁.trans h₂) ≫ baseChangeSpec K Ω Γ(C.Xbar, U₂) := by
  rw [← fillPoint_spec, ← fillPoint_spec, Category.assoc, specMap_resAlg_comp]

/-- **`Π_{U₁} → Π_{U₂}`** for `U ⊆ U₁ ⊆ U₂`, at the base points `fillPoint`. -/
def fillStepMap : π₁ᵉᵗ(fillPoint Ω C hc h₁ ≫ baseChangeSpec K Ω Γ(C.Xbar, U₁)) →ₜ*
    π₁ᵉᵗ(fillPoint Ω C hc (h₁.trans h₂) ≫ baseChangeSpec K Ω Γ(C.Xbar, U₂)) :=
  fundamentalGroupMap (Spec.map (CommRingCat.ofHom (resAlg K h₂).toRingHom))
    (fillPoint_step Ω C hc h₁ h₂)

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Nonempty (baseChangeOpen K Ω U')] in
lemma fillStepMap_fillMap (γ) :
    fillStepMap Ω C hc h₁ h₂ (fillMap Ω C hc h₁ γ) = fillMap Ω C hc (h₁.trans h₂) γ := by
  change ((fillStepMap Ω C hc h₁ h₂).comp (fillMap Ω C hc h₁)) γ = _
  rw [fillStepMap, fillMap, ← fundamentalGroupMap_comp _ _ _ _
    ((Category.assoc _ _ _).symm.trans (by rw [fillPoint_spec]; exact fillPoint_step Ω C hc h₁ h₂))]
  exact congrArg (· γ) (fundamentalGroupMap_congr (specMap_resAlg_comp C h₁ h₂) _ _)

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Nonempty (baseChangeOpen K Ω U')] in
include hc₂ in
lemma fillStepMap_surjective : Function.Surjective (fillStepMap Ω C hc h₁ h₂) := fun y ↦ by
  obtain ⟨γ, rfl⟩ := fillMap_surjective Ω C hc (h₁.trans h₂) hc₂ y
  exact ⟨_, fillStepMap_fillMap Ω C hc h₁ h₂ γ⟩

omit [Nonempty (baseChangeOpen K Ω U')] in
/-- The image of a subgroup of `Π_U` in the chain object `Π_{U'}` is its image under
`fillMap`. -/
lemma image_fillChainObj (hyp : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U') (I) :
    (fillChainObj Ω C hc h hc' hyp).image I = I.map (fillMap Ω C hc h).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨⟨x, _⟩, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

/-- An isomorphism of fibre functors from the base point of the curve `(X̄, U₁)` to `fillPoint`. -/
def fillAlpha : fiber (basePoint Ω (fillCurve C h₁ hyp₁) hc₁) ≅ fiber (fillPoint Ω C hc h₁) :=
  haveI := isIntegral_specTensor_of_le Ω C h₁ hc₁
  haveI := isIntegral_specTensor Ω (fillCurve C h₁ hyp₁) hc₁
  (nonempty_iso_of_fiberFunctor _ _).some

/-- The change of base point `Π_{U₁}(basePoint) ≃ₜ* Π_{U₁}(fillPoint)`. -/
def fillTransport : π₁ᵉᵗ(basePoint Ω (fillCurve C h₁ hyp₁) hc₁ ≫
      baseChangeSpec K Ω Γ(C.Xbar, U₁)) ≃ₜ*
    π₁ᵉᵗ(fillPoint Ω C hc h₁ ≫ baseChangeSpec K Ω Γ(C.Xbar, U₁)) :=
  autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U₁)) rfl rfl
    (fillAlpha Ω C hc h₁ hc₁ hyp₁))

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma ker_projGkFill_eq_map : (projGkFill Ω C hc h₁).toMonoidHom.ker =
    (projGk Ω (fillCurve C h₁ hyp₁) hc₁).toMonoidHom.ker.map
      (fillTransport Ω C hc h₁ hc₁ hyp₁).toMulEquiv.toMonoidHom :=
  ker_fundamentalGroupMap_eq_map (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, U₁))))
    (basePoint_spec₂ Ω (fillCurve C h₁ hyp₁) hc₁) (fillPoint_spec₂ Ω C hc h₁) _

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma fillStepMap_fillTransport (γ) :
    fillStepMap Ω C hc h₁ h₂ (fillTransport Ω C hc h₁ hc₁ hyp₁ γ) =
      autContinuousMulEquivOfIso (fiberIsoMap (Spec.map (CommRingCat.ofHom
        (resAlg K h₂).toRingHom)) (fillPoint_spec Ω (fillCurve C h₁ hyp₁) hc₁ h₂)
          (fillPoint_step Ω C hc h₁ h₂) (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U₁)) rfl rfl
            (fillAlpha Ω C hc h₁ hc₁ hyp₁)))
        (fillMap Ω (fillCurve C h₁ hyp₁) hc₁ h₂ γ) :=
  fundamentalGroupMap_autContinuousMulEquivOfIso _ _ _ _ γ

variable {x : C.Xbar} (hxU₂ : x ∈ U₂) (hxU₁ : x ∉ U₁) (hx : (U₂ : Set C.Xbar) \ U₁ ⊆ {x})
  (hxr : IsIso ((C.Xbar ↘ Spec (.of K)).residueFieldMap x))

/-- The cuspidal decomposition group of `Δ_{U₁}` whose normal closure is `ker(Π_{U₁} ↠ Π_{U₂})`
(the inertia group of the cusp `x`, at the base point `fillPoint`). -/
def fillStepCusp : Subgroup π₁ᵉᵗ(fillPoint Ω C hc h₁ ≫ baseChangeSpec K Ω Γ(C.Xbar, U₁)) :=
  (fillCusp Ω (fillCurve C h₁ hyp₁) hc₁ h₂ hc₂ hxU₂ hxU₁ hx hxr).map
    (fillTransport Ω C hc h₁ hc₁ hyp₁).toMulEquiv.toMonoidHom

lemma ker_fillStepMap : (fillStepMap Ω C hc h₁ h₂).toMonoidHom.ker =
    (fillChainObj Ω C hc h₁ hc₁ hyp₁).deltaNormalClosure
      (fillStepCusp Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hxU₂ hxU₁ hx hxr) := by
  let T := fillTransport Ω C hc h₁ hc₁ hyp₁
  have hker : (fillStepMap Ω C hc h₁ h₂).toMonoidHom.ker =
      (fillMap Ω (fillCurve C h₁ hyp₁) hc₁ h₂).toMonoidHom.ker.map T.toMulEquiv.toMonoidHom := by
    ext y
    obtain ⟨γ, rfl⟩ := T.surjective y
    rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker]
    change fillStepMap Ω C hc h₁ h₂ (T γ) = 1 ↔ fillMap Ω (fillCurve C h₁ hyp₁) hc₁ h₂
      (T.toMulEquiv.symm (T γ)) = 1
    have e1 : T.toMulEquiv.symm (T γ) = γ := T.symm_apply_apply γ
    have e2 := fillStepMap_fillTransport Ω C hc h₁ h₂ hc₁ hyp₁ γ
    constructor
    · intro h1
      have h3 := e2.symm.trans h1
      refine (congrArg _ e1).trans ?_
      exact (EmbeddingLike.map_eq_one_iff (f := autContinuousMulEquivOfIso _)).1 h3
    · intro h1
      have h3 := (congrArg _ e1).symm.trans h1
      exact e2.trans ((congrArg _ h3).trans (map_one _))
  rw [hker, ker_fillMap_eq_fillCusp Ω (fillCurve C h₁ hyp₁) hc₁ h₂ hc₂ hxU₂ hxU₁ hx hxr]
  exact (map_conjClosureIn_equiv T _ _).trans
    (congrArg (conjClosureIn · _) (ker_projGkFill_eq_map Ω C hc h₁ hc₁ hyp₁).symm)

/-- `fillStepCusp` is a cuspidal decomposition group of `Δ_{U₁}` in the sense of [AbsTopI]
Definition 4.2 (iii), (3Π): the commensurator in `Δ_{U₁}` of the (nontrivial) image of a
cuspidal inertia group of `Π_U`. -/
lemma isCuspidal_fillStepCusp :
    (fillChainObj Ω C hc h₁ hc₁ hyp₁).IsCuspidal
      (fillStepCusp Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hxU₂ hxU₁ hx hxr) := by
  haveI : Nonempty (baseChangeOpen K Ω U₁) := nonempty_fillOpen Ω C h₁
  let T := fillTransport Ω C hc h₁ hc₁ hyp₁
  have hJ := fillCusp_mem Ω (fillCurve C h₁ hyp₁) hc₁ h₂ hc₂ hxU₂ hxU₁ hx hxr
  obtain ⟨I, hI, hIJ⟩ := exists_mem_arithCusps_map_fillMap Ω C hc h₁ hc₁ hyp₁
    (fillAlpha Ω C hc h₁ hc₁ hyp₁) hJ
  refine ⟨I, hI, ?_, ?_⟩
  · rw [image_fillChainObj, hIJ, Ne, Subgroup.map_eq_bot_iff_of_injective _ T.injective]
    exact arithCusps_ne_bot Ω (fillCurve C h₁ hyp₁) hc₁
      (one_lt_card_geomOpen_compl Ω (fillCurve C h₁ hyp₁) h₂ hc₂ hxU₂ hxU₁) hJ
  · have hcomm := commensurator_inf_of_mem_arithCusps Ω (fillCurve C h₁ hyp₁) hc₁ hJ
    have k : Subgroup.Commensurable.commensurator ((fillCusp Ω (fillCurve C h₁ hyp₁) hc₁ h₂ hc₂
        hxU₂ hxU₁ hx hxr).map T.toMulEquiv.toMonoidHom) ⊓
          (projGk Ω (fillCurve C h₁ hyp₁) hc₁).toMonoidHom.ker.map T.toMulEquiv.toMonoidHom =
        (fillCusp Ω (fillCurve C h₁ hyp₁) hc₁ h₂ hc₂ hxU₂ hxU₁ hx hxr).map
          T.toMulEquiv.toMonoidHom := by
      rw [← commensurator_map_mulEquiv, ← Subgroup.map_inf_eq _ _ _ T.injective, hcomm]
    rw [image_fillChainObj, hIJ]
    exact k.symm.trans (congrArg _ (ker_projGkFill_eq_map Ω C hc h₁ hc₁ hyp₁).symm)

/-- `fillStepCusp` lies in a normal open torsion-free subgroup of `Δ_{U₁}` (namely `Δ_{U₁}`,
which is torsion-free). -/
lemma inTorsionFreeNormalOpen_fillStepCusp :
    (fillChainObj Ω C hc h₁ hc₁ hyp₁).InTorsionFreeNormalOpen
      (fillStepCusp Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hxU₂ hxU₁ hx hxr) := by
  let T := fillTransport Ω C hc h₁ hc₁ hyp₁
  have hD : (fillChainObj Ω C hc h₁ hc₁ hyp₁).Delta =
      (projGk Ω (fillCurve C h₁ hyp₁) hc₁).toMonoidHom.ker.map T.toMulEquiv.toMonoidHom :=
    ker_projGkFill_eq_map Ω C hc h₁ hc₁ hyp₁
  refine ChainObj.inTorsionFreeNormalOpen_of _ (fun δ hδ hfin ↦ ?_) ?_
  · rw [hD] at hδ
    obtain ⟨δ', hδ', rfl⟩ := hδ
    have hfin' : IsOfFinOrder δ' :=
      (T.toMulEquiv.injective.isOfFinOrder_iff (f := T.toMulEquiv.toMonoidHom)).1 hfin
    have := Delta_eq_one_of_isOfFinOrder Ω (fillCurve C h₁ hyp₁) hc₁ (δ := ⟨δ', hδ'⟩)
      ((Subgroup.subtype_injective _).isOfFinOrder_iff (f := Subgroup.subtype _) |>.1 hfin')
    have h1 : δ' = 1 := congrArg Subtype.val this
    rw [h1]
    exact map_one _
  · rw [hD]
    exact Subgroup.map_mono (arithCusps_le Ω (fillCurve C h₁ hyp₁) hc₁
      (fillCusp_mem Ω (fillCurve C h₁ hyp₁) hc₁ h₂ hc₂ hxU₂ hxU₁ hx hxr))

/-- `fillStepMap` is compatible with the rigidifying homomorphisms `fillMap`. -/
lemma fillStepMap_compat :
    ChainObj.Compat (fillChainObj Ω C hc h₁ hc₁ hyp₁)
      (fillChainObj Ω C hc (h₁.trans h₂) hc₂ hyp₂) (fillStepMap Ω C hc h₁ h₂) :=
  ⟨⊤, le_rfl, le_rfl, fun γ _ ↦ fillStepMap_fillMap Ω C hc h₁ h₂ γ⟩

/-- **Filling in a further cusp is an elementary operation of type `•`** ([AbsTopI] Definition
4.2 (iii) (c)): for `U ⊆ U₁ ⊆ U₂ = U₁ ∪ {x}` with `(X̄, U₁)`, `(X̄, U₂)` hyperbolic with a cusp
`Π_{U₁} ↠ Π_{U₂}` between the chain objects
`fillChainObj U₁` and `fillChainObj U₂` of `Π_U`. -/
def fillStepElemOp :
    ElemOp (fillChainObj Ω C hc h₁ hc₁ hyp₁) (fillChainObj Ω C hc (h₁.trans h₂) hc₂ hyp₂) :=
  .decusp (fillStepMap Ω C hc h₁ h₂) (fillStepMap_surjective Ω C hc h₁ h₂ hc₂)
    (fillStepCusp Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hxU₂ hxU₁ hx hxr)
    (isCuspidal_fillStepCusp Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hxU₂ hxU₁ hx hxr)
    (inTorsionFreeNormalOpen_fillStepCusp Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hxU₂ hxU₁ hx hxr)
    (ker_fillStepMap Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hxU₂ hxU₁ hx hxr)
    (fillStepMap_compat Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hyp₂)

lemma fillStepElemOp_kind :
    (fillStepElemOp Ω C hc h₁ h₂ hc₁ hc₂ hyp₁ hyp₂ hxU₂ hxU₁ hx hxr).kind = .decusp := rfl

end Step

end CurvesJacobian.Cusp
