/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.TwistDGC

/-!
# Conjugation by Galois elements on `G_M ⊆ G_K` is induced by `Spec` of field automorphisms

Let `K → M → Ω` be field extensions with `Ω` separably closed and Galois over `K`, and write
`res : G_M = π₁ᵉᵗ(Spec M) → G_K = π₁ᵉᵗ(Spec K)` (at the points `Spec Ω ⟶ Spec M ⟶ Spec K`).

* `CurvesJacobian.Cusp.res_mulEquivAutFiber`: `res` is the inclusion `Gal(Ω/M) ⊆ Gal(Ω/K)` under
  `Gal ≅ π₁ᵉᵗ` (`AlgebraicGeometry.FiniteEtale.mulEquivAutFiber`); `res` is injective for `M/K`
  finite separable (`resGal_injective`).
* `CurvesJacobian.Cusp.exists_resAut_of_conj_mem_range`: if conjugation by `τ ∈ Gal(Ω/K)` maps
  the image of `res` into itself, then `τ` restricts to a `K`-automorphism `α` of `M`
  (`algebraMap (α x) = τ (algebraMap x)`; Galois correspondence).
* **`CurvesJacobian.Cusp.isConjInduced_of_res_conj`**: if `α` is such a restriction and
  `Θ : G_M → G_M` satisfies `res ∘ Θ = conj(τ⁻¹) ∘ res`, then `Θ` is induced, up to a change of
  base point, by `Spec α : Spec M ⟶ Spec M` (`IsConjInduced`). The change of base point is the
  field change along `τ` (`fieldChangeIso`), and the automorphism of the fibre functor of
  `Spec K` it induces is the Galois element `τ⁻¹` (`fiberIsoMap_fieldChangeIso`).

Together with `CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_twist` this is the
semilinear rel-isom-DGC for isomorphisms lying over conjugation by a Galois element
(`CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_gal`,
`CurvesJacobian.Cusp.eq_of_isConjInduced_of_relIsomDGC_gal`).

Hazard: proofs that rewrite with an `eqToIso` between fibre functors of two equal geometric
points `sM ≫ Spec α = Spec τ ≫ sM` caused kernel deterministic timeouts; the field change is
therefore used directly at the point `Spec τ ≫ sM` (via `isConjInduced_iff`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Res

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω] (M : Type u) [Field M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]

/-- The point `Spec Ω ⟶ Spec K`. -/
local notation "sK" => Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-- The point `Spec Ω ⟶ Spec M`. -/
local notation "sM" => Spec.map (CommRingCat.ofHom (algebraMap M Ω))

variable (K) in
/-- `Spec M ⟶ Spec K`. -/
abbrev sKM : Spec (.of M) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K M))

omit [IsSepClosed Ω] [IsGalois K Ω] in
lemma sM_sKM : sM ≫ sKM K M = sK := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (K Ω) in
/-- `res : G_M → G_K`. -/
abbrev resGal : π₁ᵉᵗ(sM) →ₜ* π₁ᵉᵗ(sK) := fundamentalGroupMap (sKM K M) (sM_sKM M)

omit [IsGalois K Ω] in
/-- `res` is injective (`Spec M ⟶ Spec K` is finite étale for `M/K` finite separable). -/
lemma resGal_injective [FiniteDimensional K M] [Algebra.IsSeparable K M] :
    Function.Injective (resGal K Ω M) := by
  haveI : IsFiniteEtale (sKM K M) := isFiniteEtale_specAlgebraMap (M := K) (M' := M)
  exact fundamentalGroupMap_injective_of_isFiniteEtale' (sKM K M) sM (sM_sKM M)

variable [IsGalois M Ω]

/-- **`res` is the inclusion `Gal(Ω/M) ⊆ Gal(Ω/K)`.** -/
lemma res_mulEquivAutFiber (g : Ω ≃ₐ[M] Ω) :
    resGal K Ω M (mulEquivAutFiber M Ω g) = mulEquivAutFiber K Ω (g.restrictScalars K) := by
  have h1 : resGal K Ω M (mulEquivAutFiber M Ω g) = galoisAction M (sKM K M) (sM_sKM M) g := rfl
  have h2 : mulEquivAutFiber K Ω (g.restrictScalars K) =
      galoisAction K (𝟙 _) (Category.comp_id _) (g.restrictScalars K) := by
    rw [galoisAction, MonoidHom.comp_apply, fundamentalGroupMap_id]
    rfl
  rw [h1, h2]
  refine ext_of_hom_app_left fun A x ↦ ?_
  rw [galoisAction_hom_app_left, galoisAction_hom_app_left]
  rfl

/-- The image of `res` consists of the Galois elements fixing `M`. -/
lemma mem_range_resGal_iff (γ : π₁ᵉᵗ(sK)) :
    γ ∈ (resGal K Ω M).toMonoidHom.range ↔
      ∀ x : M, (mulEquivAutFiber K Ω).symm γ (algebraMap M Ω x) = algebraMap M Ω x := by
  constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨g, rfl⟩ := (mulEquivAutFiber M Ω).surjective σ
    change ∀ x, (mulEquivAutFiber K Ω).symm (resGal K Ω M (mulEquivAutFiber M Ω g)) _ = _
    rw [res_mulEquivAutFiber, MulEquiv.symm_apply_apply]
    exact fun x ↦ g.commutes x
  · intro h
    let g : Ω ≃ₐ[M] Ω := AlgEquiv.ofRingEquiv (f := ((mulEquivAutFiber K Ω).symm γ).toRingEquiv) h
    refine ⟨mulEquivAutFiber M Ω g, ?_⟩
    change resGal K Ω M _ = γ
    rw [res_mulEquivAutFiber]
    rw [show g.restrictScalars K = (mulEquivAutFiber K Ω).symm γ from AlgEquiv.ext fun _ ↦ rfl,
      MulEquiv.apply_symm_apply]

/-- **Galois elements normalising `G_M` restrict to automorphisms of `M`**: if conjugation by
`τ` maps the image of `res : G_M → G_K` into itself, then `τ(M) = M`, i.e. there is a
`K`-automorphism `α` of `M` with `algebraMap (α x) = τ (algebraMap x)`. -/
theorem exists_resAut_of_conj_mem_range [FiniteDimensional K M] (τ : Ω ≃ₐ[K] Ω)
    (h : ∀ γ ∈ (resGal K Ω M).toMonoidHom.range,
      mulEquivAutFiber K Ω τ * γ * (mulEquivAutFiber K Ω τ)⁻¹ ∈ (resGal K Ω M).toMonoidHom.range) :
    ∃ α : M ≃ₐ[K] M, ∀ x, algebraMap M Ω (α x) = τ (algebraMap M Ω x) := by
  set L : IntermediateField K Ω := (IsScalarTower.toAlgHom K M Ω).fieldRange
  have hmemL : ∀ g : Ω ≃ₐ[K] Ω, g ∈ L.fixingSubgroup ↔ ∀ x : M,
      g (algebraMap M Ω x) = algebraMap M Ω x := fun g ↦ by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · exact fun hg x ↦ hg _ ⟨x, rfl⟩
    · rintro hg _ ⟨x, rfl⟩
      exact hg x
  -- `τ G_M τ⁻¹ ⊆ G_M`
  have hfix : ∀ g ∈ L.fixingSubgroup, τ * g * τ⁻¹ ∈ L.fixingSubgroup := fun g hg ↦ by
    have hγ := h (mulEquivAutFiber K Ω g)
      ((mem_range_resGal_iff M _).2 (by simpa using (hmemL g).1 hg))
    rw [← map_inv, ← map_mul, ← map_mul] at hγ
    exact (hmemL _).2 (by simpa using (mem_range_resGal_iff M _).1 hγ)
  -- hence `L ⊆ τ(L)`
  have hle : L ≤ L.map (τ : Ω →ₐ[K] Ω) := by
    intro x hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup (L.map (τ : Ω →ₐ[K] Ω))]
    rintro ⟨g, hg⟩
    have hg' : τ⁻¹ * g * τ ∈ L.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy ↦ by
        have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg (τ y) ⟨y, hy, rfl⟩
        change τ.symm (g (τ y)) = y
        rw [this, AlgEquiv.symm_apply_apply]
    have := hfix _ hg'
    rw [show τ * (τ⁻¹ * g * τ) * τ⁻¹ = g by group] at this
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x hx
  haveI : FiniteDimensional K L :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField
      (IsScalarTower.toAlgHom K M Ω)).toLinearEquiv
  haveI : FiniteDimensional K (L.map (τ : Ω →ₐ[K] Ω)) :=
    LinearEquiv.finiteDimensional (L.equivMap (τ : Ω →ₐ[K] Ω)).toLinearEquiv
  have hL : L.map (τ : Ω →ₐ[K] Ω) = L := (IntermediateField.eq_of_le_of_finrank_eq hle
    (L.equivMap (τ : Ω →ₐ[K] Ω)).toLinearEquiv.finrank_eq).symm
  let e : M ≃ₐ[K] L := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M Ω)
  refine ⟨e.trans (((L.equivMap (τ : Ω →ₐ[K] Ω)).trans (IntermediateField.equivOfEq hL)).trans
    e.symm), fun x ↦ ?_⟩
  have := congrArg Subtype.val (e.apply_symm_apply
    ((IntermediateField.equivOfEq hL) (L.equivMap (τ : Ω →ₐ[K] Ω) (e x))))
  exact this

/-! ### Conjugation by a Galois element is induced by `Spec` of its restriction -/

variable {M}

omit [IsSepClosed Ω] [IsGalois K Ω] [IsGalois M Ω] [IsScalarTower K M Ω] in
lemma sM_specRingEquiv {τ : Ω ≃ₐ[K] Ω} {α : M ≃ₐ[K] M}
    (hα : ∀ x, algebraMap M Ω (α x) = τ (algebraMap M Ω x)) :
    sM ≫ specRingEquiv α.toRingEquiv = specIso τ.toRingEquiv ≫ sM := by
  rw [specIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hα x

omit [IsSepClosed Ω] [IsGalois K Ω] [IsGalois M Ω] [IsScalarTower K M Ω] [Algebra M Ω] in
lemma specRingEquiv_sKM (α : M ≃ₐ[K] M) : specRingEquiv α.toRingEquiv ≫ sKM K M = sKM K M := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  exact α.commutes c

omit [IsSepClosed Ω] [IsGalois K Ω] [IsGalois M Ω] [IsScalarTower K M Ω] [Algebra M Ω]
  [Algebra K M] in
lemma overHomEquiv_left {X : Scheme.{u}} (σ : Ω ≃+* Ω) (η : Spec (.of Ω) ⟶ X) (A : FiniteEtale X)
    (x : Over.mk (specIso σ ≫ η) ⟶ A.toComma) :
    (overHomEquiv σ η A x).left = specIso σ.symm ≫ x.left := rfl

omit [IsGalois K Ω] [IsGalois M Ω] [IsScalarTower K M Ω] [Algebra M Ω] [Algebra K M] in
/-- `fiberIsoMap` on points: the image of a point of the pullback is the projection of its image
under the change of base point upstairs. -/
lemma fiberIsoMap_hom_app_left {X Y : Scheme.{u}} (f : Y ⟶ X) {p₁ p₂ : Spec (.of Ω) ⟶ Y}
    {η η' : Spec (.of Ω) ⟶ X} (h : p₁ ≫ f = η) (h' : p₂ ≫ f = η') (a : fiber p₁ ≅ fiber p₂)
    (A : FiniteEtale X) (y : (fiber p₁).obj ((FiniteEtale.pullback f).obj A)) :
    (fiberObjEquivHom η' A ((fiberIsoMap f h h' a).hom.app A
        ((pullbackFiberIso f h).hom.app A y))).left =
      (fiberObjEquivHom p₂ _ (a.hom.app _ y)).left ≫ Limits.pullback.fst A.hom f := by
  have hy : (pullbackFiberIso f h).inv.app A ((pullbackFiberIso f h).hom.app A y) = y :=
    FintypeCat.hom_inv_id_apply ((pullbackFiberIso f h).app A) y
  rw [← pullbackFiberIso_hom_app_left f h' A]
  change (fiberObjEquivHom η' A ((pullbackFiberIso f h').hom.app A (a.hom.app _
    ((pullbackFiberIso f h).inv.app A ((pullbackFiberIso f h).hom.app A y))))).left = _
  rw [hy]

omit [IsSepClosed Ω] [IsGalois K Ω] [IsGalois M Ω] [IsScalarTower K M Ω] [Algebra M Ω]
  [Algebra K M] in
lemma specIso_inv (τ : Ω ≃ₐ[K] Ω) :
    specIso τ.toRingEquiv.symm = Spec.map (CommRingCat.ofHom ((τ⁻¹ : Ω ≃ₐ[K] Ω) : Ω →+* Ω)) :=
  rfl

omit [IsSepClosed Ω] [IsGalois K Ω] [IsGalois M Ω] in
lemma specIso_sM_sKM (τ : Ω ≃ₐ[K] Ω) : (specIso τ.toRingEquiv ≫ sM) ≫ sKM K M = sK := by
  rw [Category.assoc, sM_sKM, specIso, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  exact τ.commutes c

omit [IsGalois M Ω] in
/-- **The field change along `τ` induces the Galois element `τ⁻¹` on the fibre functor of
`Spec K`.** -/
theorem fiberIsoMap_fieldChangeIso (τ : Ω ≃ₐ[K] Ω) :
    fiberIsoMap (sKM K M) (specIso_sM_sKM (M := M) τ) (sM_sKM M) (fieldChangeIso τ.toRingEquiv sM) =
      mulEquivAutFiber K Ω τ⁻¹ := by
  have hR : mulEquivAutFiber K Ω τ⁻¹ = galoisAction K (𝟙 _) (Category.comp_id _) τ⁻¹ := by
    rw [galoisAction, MonoidHom.comp_apply, fundamentalGroupMap_id]
    rfl
  rw [hR]
  refine ext_of_hom_app_left fun B x ↦ ?_
  rw [galoisAction_hom_app_left]
  obtain ⟨y, rfl⟩ : ∃ y, (pullbackFiberIso (sKM K M) (specIso_sM_sKM (M := M) τ)).hom.app B y = x :=
    ⟨_, FintypeCat.inv_hom_id_apply ((pullbackFiberIso (sKM K M)
      (specIso_sM_sKM (M := M) τ)).app B) x⟩
  rw [fiberIsoMap_hom_app_left, fieldChangeIso_hom_app, overHomEquiv_left,
    pullbackFiberIso_hom_app_left (sKM K M) (specIso_sM_sKM (M := M) τ) B y, specIso_inv]
  exact Category.assoc _ _ _

omit [IsGalois M Ω] in
/-- **Conjugation by a Galois element on `G_M` is induced by `Spec` of its restriction**: if
`α` is the restriction of `τ ∈ Gal(Ω/K)` to `M` and `res ∘ Θ = conj(τ⁻¹) ∘ res`, then `Θ` is
induced by `Spec α` up to a change of base point (the field change along `τ`). -/
theorem isConjInduced_of_res_conj [FiniteDimensional K M] [Algebra.IsSeparable K M]
    {τ : Ω ≃ₐ[K] Ω} {α : M ≃ₐ[K] M} (hα : ∀ x, algebraMap M Ω (α x) = τ (algebraMap M Ω x))
    (Θ : π₁ᵉᵗ(sM) → π₁ᵉᵗ(sM))
    (hΘ : ∀ σ, resGal K Ω M (Θ σ) =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M σ * mulEquivAutFiber K Ω τ) :
    IsConjInduced (specRingEquiv α.toRingEquiv) Θ := by
  refine (isConjInduced_iff _ (sM_specRingEquiv hα) Θ).2
    ⟨fieldChangeIso τ.toRingEquiv sM, fun σ ↦ resGal_injective (K := K) (Ω := Ω) M ?_⟩
  rw [hΘ, fundamentalGroupMap_autContinuousMulEquivOfIso (sKM K M) (specIso_sM_sKM (M := M) τ)
    (sM_sKM M), fiberIsoMap_fieldChangeIso]
  have h3 : sM ≫ specRingEquiv α.toRingEquiv ≫ sKM K M = sK := by
    rw [specRingEquiv_sKM, sM_sKM]
  have c := DFunLike.congr_fun (fundamentalGroupMap_comp (specRingEquiv α.toRingEquiv) (sKM K M)
    (sM_specRingEquiv hα) (specIso_sM_sKM (M := M) τ) h3) σ
  have c' := DFunLike.congr_fun (fundamentalGroupMap_congr (specRingEquiv_sKM α) h3
    (sM_sKM M)) σ
  change _ = (mulEquivAutFiber K Ω τ⁻¹).conjAut
    (fundamentalGroupMap (sKM K M) (specIso_sM_sKM (M := M) τ)
      (fundamentalGroupMap (specRingEquiv α.toRingEquiv) (sM_specRingEquiv hα) σ))
  rw [Aut_conjAut_eq, map_inv, inv_inv]
  exact congrArg (fun s ↦ (mulEquivAutFiber K Ω τ)⁻¹ * s * mulEquivAutFiber K Ω τ)
    (c'.symm.trans c)

end Res

/-! ### The rel-isom-DGC over conjugation by a Galois element -/

section DGC

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] {M : Type u} [Field M] [NumberField M] [Algebra K M]
  [Algebra M Ω] [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {C₁ C₂ : HypCurve M} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

omit [Algebra.IsAlgebraic M Ω] in
include hc₁ in
/-- Auxiliary: the automorphism of `G_M` under an isomorphism over conjugation by `τ⁻¹`. -/
lemma exists_theta_of_res_conj [FiniteDimensional K M]
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U))) (τ : Ω ≃ₐ[K] Ω)
    (hφ : ∀ σ, resGal K Ω M (projGk Ω C₂ hc₂ (φ σ)) =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M (projGk Ω C₁ hc₁ σ) * mulEquivAutFiber K Ω τ) :
    ∃ Θ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M Ω))) →
        π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M Ω))),
      (∀ s, resGal K Ω M (Θ s) =
        (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M s * mulEquivAutFiber K Ω τ) ∧
      ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ) := by
  let Θ := fun s ↦ projGk Ω C₂ hc₂ (φ (projGk_surjective Ω C₁ hc₁ s).choose)
  have hΘ : ∀ s, resGal K Ω M (Θ s) =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M s * mulEquivAutFiber K Ω τ := fun s ↦ by
    change resGal K Ω M (projGk Ω C₂ hc₂ (φ (projGk_surjective Ω C₁ hc₁ s).choose)) = _
    rw [hφ, (projGk_surjective Ω C₁ hc₁ s).choose_spec]
  refine ⟨Θ, hΘ, fun σ ↦ resGal_injective (K := K) (Ω := Ω) M ?_⟩
  rw [hφ, hΘ]

/-- **The rel-isom-DGC over conjugation by a Galois element, existence**: for hyperbolic curves
`C₁, C₂` over a number field `M ⊇ K` with cusps, `τ ∈ Gal(Ω/K)` restricting to `α ∈ Aut_K(M)`,
every continuous isomorphism `φ : Π_{U₁} ≃ₜ* Π_{U₂}` with `res ∘ pr₂ ∘ φ = conj(τ⁻¹) ∘ res ∘ pr₁`
is induced, up to a change of base point, by an isomorphism of schemes
`Spec Γ(U₁) ≅ Spec Γ(U₂)` lying over `Spec α`. -/
theorem exists_isConjInduced_of_relIsomDGC_gal [FiniteDimensional K M] (hDGC : RelIsomDGC.Exists M)
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)))
    {τ : Ω ≃ₐ[K] Ω} {α : M ≃ₐ[K] M} (hα : ∀ x, algebraMap M Ω (α x) = τ (algebraMap M Ω x))
    (hφ : ∀ σ, resGal K Ω M (projGk Ω C₂ hc₂ (φ σ)) =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M (projGk Ω C₁ hc₁ σ) * mulEquivAutFiber K Ω τ) :
    ∃ F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U),
      F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv α.toRingEquiv ∧ IsConjInduced F.hom φ := by
  obtain ⟨Θ, hΘ, hφ'⟩ := exists_theta_of_res_conj φ τ hφ
  exact exists_isConjInduced_of_relIsomDGC_twist Ω α.toRingEquiv hDGC φ Θ
    (isConjInduced_of_res_conj hα Θ hΘ) hφ'

/-- **The rel-isom-DGC over conjugation by a Galois element, uniqueness.** -/
theorem eq_of_isConjInduced_of_relIsomDGC_gal [FiniteDimensional K M]
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)))
    {τ : Ω ≃ₐ[K] Ω} {α : M ≃ₐ[K] M} (hα : ∀ x, algebraMap M Ω (α x) = τ (algebraMap M Ω x))
    (hφ : ∀ σ, resGal K Ω M (projGk Ω C₂ hc₂ (φ σ)) =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M (projGk Ω C₁ hc₁ σ) * mulEquivAutFiber K Ω τ)
    {F G : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)}
    (hF : F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv α.toRingEquiv)
    (hG : G.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv α.toRingEquiv)
    (HF : IsConjInduced F.hom φ) (HG : IsConjInduced G.hom φ) : F = G := by
  obtain ⟨Θ, hΘ, hφ'⟩ := exists_theta_of_res_conj φ τ hφ
  exact eq_of_isConjInduced_of_relIsomDGC_twist Ω α.toRingEquiv φ Θ
    (isConjInduced_of_res_conj hα Θ hΘ) hφ' hF hG HF HG

end DGC

end CurvesJacobian.Cusp
