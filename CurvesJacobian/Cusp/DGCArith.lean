/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverCusps

/-!
# The rel-isom-DGC in the arithmetic model `π₁ᵉᵗ(Spec Γ(U), basePoint)` (MR8.6)

The whitelist statement `Belyi.Anabelian.RelIsomDGC K` ([AbsTopI] Def 4.6 (ii), whitelist entry
for [LocAn] Theorem A) is stated for the open subscheme `U = C.U` of a hyperbolic curve and a
geometric point `ξ : Spec Ω ⟶ U` (`HypCurve.GeomPt`), with "induced up to `Δ₂`-conjugation"
expressed by paths over the trivial path of `Spec K` (`InducedBy`). The group-theoretic
cuspidalisation of curves-jacobian works with `Π_U = π₁ᵉᵗ(Spec Γ(U), x)` at the base point
`x = basePoint ≫ baseChangeSpec` (`CurvesJacobian.Cusp.arithmeticExt`). This file translates.

* `AlgebraicGeometry.FiniteEtale.IsConjInduced h φ`: `φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)` is
  `π₁ᵉᵗ(h)` followed by a change of base point (an isomorphism of fibre functors); stable under
  composition and conjugation (`IsConjInduced.comp`, `IsConjInduced.conj`); for a fixed change of
  base point `γ₀` it means `φ = conj t ∘ γ₀ ∘ π₁ᵉᵗ(h)` for some `t`
  (`isConjInduced_iff_exists_conj`).
* `isPathOverBase_of_isOverGk`: a change of base point realising an isomorphism over `G_K` lies
  over the trivial path of `Spec K` automatically (`G_K` has trivial centre); so `InducedBy` is
  `IsConjInduced` for isomorphisms over `G_K`.
* **`exists_isConjInduced_of_relIsomDGC`, `eq_of_isConjInduced_of_relIsomDGC`** (the DGC in
  the arithmetic model): for hyperbolic curves `C₁, C₂` over a number field `K`, each with a
  cusp, every continuous isomorphism `φ : Π_{U₁} ≃ₜ* Π_{U₂}` over `G_K` is `IsConjInduced` by a
  `K`-isomorphism `Spec Γ(U₁) ≅ Spec Γ(U₂)`, and this isomorphism is unique.
* `eq_refl_of_isConjInduced_conj`: a `K`-automorphism of `Spec Γ(U)` inducing an inner
  automorphism of `Π_U` is the identity.

The DGC enters only as the explicit hypothesis `hDGC : RelIsomDGC K` (`K` a number field, hence
sub-`p`-adic, `Belyi.Anabelian.isSubPAdic_of_numberField`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

section ConjInduced

variable {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- `φ : π₁ᵉᵗ(X, x) → π₁ᵉᵗ(Y, y)` is **induced by `h : X ⟶ Y` up to a change of base point**:
`φ = γ_* ∘ π₁ᵉᵗ(h)` for an isomorphism of fibre functors `γ : fiber (x ≫ h) ≅ fiber y`. -/
def IsConjInduced (h : X ⟶ Y) {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y}
    (φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)) : Prop :=
  ∃ γ : fiber (x ≫ h) ≅ fiber y,
    ∀ σ, φ σ = autContinuousMulEquivOfIso γ (fundamentalGroupMap h rfl σ)

omit [IsSepClosed Ω] in
lemma isConjInduced_iff (h : X ⟶ Y) {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ Y} (hη : x ≫ h = η) (φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)) :
    IsConjInduced h φ ↔ ∃ γ : fiber η ≅ fiber y,
      ∀ σ, φ σ = autContinuousMulEquivOfIso γ (fundamentalGroupMap h hη σ) := by
  subst hη
  rfl

omit [IsSepClosed Ω] in
lemma IsConjInduced.congr_hom {h h' : X ⟶ Y} (e : h = h') {x : Spec (.of Ω) ⟶ X}
    {y : Spec (.of Ω) ⟶ Y} {φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} (H : IsConjInduced h φ) :
    IsConjInduced h' φ := by
  subst e
  exact H

omit [IsSepClosed Ω] in
lemma IsConjInduced.congr_fun {h : X ⟶ Y} {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y}
    {φ ψ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} (H : IsConjInduced h φ) (e : ∀ σ, ψ σ = φ σ) :
    IsConjInduced h ψ := by
  obtain ⟨γ, hγ⟩ := H
  exact ⟨γ, fun σ ↦ (e σ).trans (hγ σ)⟩

omit [IsSepClosed Ω] in
/-- Conjugation by an element of `Aut F` is `conjAut` of that element. -/
lemma Aut_conjAut_eq {F : Type*} [Category F] {A : F} (t s : Aut A) :
    t.conjAut s = t * s * t⁻¹ := by
  rw [Aut.Aut_mul_def, Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.conjAut_apply]

omit [IsSepClosed Ω] in
/-- `IsConjInduced` is stable under inner automorphisms of the target. -/
lemma IsConjInduced.conj {h : X ⟶ Y} {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y}
    {φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} (H : IsConjInduced h φ) (t : π₁ᵉᵗ(y)) :
    IsConjInduced h (fun σ ↦ t * φ σ * t⁻¹) := by
  obtain ⟨γ, hγ⟩ := H
  refine ⟨γ ≪≫ t, fun σ ↦ ?_⟩
  change t * φ σ * t⁻¹ = (γ ≪≫ t).conjAut (fundamentalGroupMap h rfl σ)
  rw [Iso.trans_conjAut, hγ, Aut_conjAut_eq]
  rfl

omit [IsSepClosed Ω] in
/-- **For a fixed change of base point `γ₀`, `IsConjInduced` means `φ = conj t ∘ γ₀ ∘ π₁ᵉᵗ(h)`.** -/
lemma isConjInduced_iff_exists_conj (h : X ⟶ Y) {x : Spec (.of Ω) ⟶ X}
    {y : Spec (.of Ω) ⟶ Y} (γ₀ : fiber (x ≫ h) ≅ fiber y) (φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)) :
    IsConjInduced h φ ↔ ∃ t : π₁ᵉᵗ(y),
      ∀ σ, φ σ = t * autContinuousMulEquivOfIso γ₀ (fundamentalGroupMap h rfl σ) * t⁻¹ := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨t, ht⟩ := CurvesJacobian.Cusp.exists_conjAut_eq_conj γ₀ γ
    exact ⟨t, fun σ ↦ (hγ σ).trans (ht _)⟩
  · rintro ⟨t, ht⟩
    exact (IsConjInduced.conj ⟨γ₀, fun _ ↦ rfl⟩ t).congr_fun ht

omit [IsSepClosed Ω] in
/-- `π₁ᵉᵗ(f)` itself is induced by `f`. -/
lemma isConjInduced_fundamentalGroupMap (h : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) :
    IsConjInduced h (fundamentalGroupMap h (rfl : x ≫ h = _)) :=
  ⟨Iso.refl _, fun σ ↦ by
    change _ = (Iso.refl _).conjAut _
    rw [Iso.conjAut_apply]
    ext
    simp⟩

omit [IsSepClosed Ω] in
/-- `π₁ᵉᵗ(𝟙)` with another target point is a change of base point. -/
lemma fundamentalGroupMap_id_eq {x η : Spec (.of Ω) ⟶ X} (h : x ≫ 𝟙 X = η) (σ : π₁ᵉᵗ(x)) :
    fundamentalGroupMap (𝟙 X) h σ =
      autContinuousMulEquivOfIso (eqToIso (congrArg fiber (by simpa using h))) σ := by
  obtain rfl : η = x := by simpa using h.symm
  rw [fundamentalGroupMap_id]
  change σ = (eqToIso rfl).conjAut σ
  rw [Iso.conjAut_apply]
  ext
  simp

omit [IsSepClosed Ω] in
/-- **Composition of induced maps.** -/
lemma IsConjInduced.comp {f : X ⟶ Y} {g : Y ⟶ Z} {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y}
    {z : Spec (.of Ω) ⟶ Z} {φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} {ψ : π₁ᵉᵗ(y) → π₁ᵉᵗ(z)}
    (Hφ : IsConjInduced f φ) (Hψ : IsConjInduced g ψ) : IsConjInduced (f ≫ g) (ψ ∘ φ) := by
  obtain ⟨γ₁, h₁⟩ := Hφ
  obtain ⟨γ₂, h₂⟩ := Hψ
  have e : x ≫ f ≫ g = (x ≫ f) ≫ g := (Category.assoc _ _ _).symm
  refine (isConjInduced_iff (f ≫ g) e _).2
    ⟨fiberIsoMap g (rfl : (x ≫ f) ≫ g = _) (rfl : y ≫ g = _) γ₁ ≪≫ γ₂, fun σ ↦ ?_⟩
  have c : fundamentalGroupMap g rfl (fundamentalGroupMap f rfl σ) =
      fundamentalGroupMap (f ≫ g) e σ :=
    (DFunLike.congr_fun (fundamentalGroupMap_comp f g rfl rfl e) σ).symm
  rw [Function.comp_apply, h₁, h₂,
    fundamentalGroupMap_autContinuousMulEquivOfIso g (rfl : (x ≫ f) ≫ g = _) rfl γ₁, c]
  change _ = (fiberIsoMap g _ _ γ₁ ≪≫ γ₂).conjAut _
  rw [Iso.trans_conjAut]
  rfl

omit [IsSepClosed Ω] in
/-- **The inverse of `π₁ᵉᵗ(e⁻¹)` is induced by `e`** for an isomorphism of schemes `e`. -/
lemma isConjInduced_hom_of_inv (e : Y ≅ X) (y : Spec (.of Ω) ⟶ X)
    (ψ : π₁ᵉᵗ(y ≫ e.inv) → π₁ᵉᵗ(y))
    (hψ : ∀ σ, ψ (fundamentalGroupMap e.inv (rfl : y ≫ e.inv = _) σ) = σ) :
    IsConjInduced e.hom ψ := by
  have h0 : (y ≫ e.inv) ≫ e.hom = y := by simp
  refine ⟨eqToIso (congrArg fiber h0), fun τ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := (fundamentalGroupMap_bijective_of_isIso e.inv
    (rfl : y ≫ e.inv = _)).2 τ
  rw [hψ]
  have h1 : y ≫ e.inv ≫ e.hom = (y ≫ e.inv) ≫ e.hom := (Category.assoc _ _ _).symm
  have h2 : y ≫ 𝟙 X = (y ≫ e.inv) ≫ e.hom := by simp
  have c : fundamentalGroupMap e.hom rfl (fundamentalGroupMap e.inv rfl σ) =
      fundamentalGroupMap (e.inv ≫ e.hom) h1 σ :=
    (DFunLike.congr_fun (fundamentalGroupMap_comp e.inv e.hom rfl rfl h1) σ).symm
  rw [c, fundamentalGroupMap_congr e.inv_hom_id h1 h2, fundamentalGroupMap_id_eq h2]
  change σ = (eqToIso (congrArg fiber h0)).conjAut ((eqToIso _).conjAut σ)
  rw [← Iso.trans_conjAut, eqToIso_trans, Iso.conjAut_apply]
  ext
  simp

end ConjInduced

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

/-! ### Paths over the base -/

section PathOverBase

open HypCurve

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω] {C₁ C₂ : HypCurve K}

/-- **A change of base point realising an isomorphism over `G_K` lies over the trivial path of
`Spec K`**, provided `Π_{U₁} → G_K` is surjective and `G_K` has trivial centre. -/
theorem isPathOverBase_of_isOverGk (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂)
    {f : C₁.U.toScheme ⟶ C₂.U.toScheme} (hf : f ≫ C₂.toSpec = C₁.toSpec)
    (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) (hφ : IsOverGk ξ₁ ξ₂ φ)
    (γ : fiber (ξ₁.x ≫ f) ≅ fiber ξ₂.x)
    (hγ : ∀ σ, φ σ = autContinuousMulEquivOfIso γ (fundamentalGroupMap f rfl σ))
    (hsurj : Function.Surjective (fundamentalGroupMap C₁.toSpec ξ₁.over))
    (hcen : Subgroup.center π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) = ⊥) :
    IsPathOverBase (comp_over_of_kHom ξ₁ hf) ξ₂.over γ := by
  set δ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    fiberIsoMap C₂.toSpec (comp_over_of_kHom ξ₁ hf) ξ₂.over γ
  have hover : ∀ σ, fundamentalGroupMap C₂.toSpec ξ₂.over (φ σ) =
      fundamentalGroupMap C₁.toSpec ξ₁.over σ := fun σ ↦ by
    have := DFunLike.congr_fun hφ σ
    simp only [toGaloisGroup, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, ContinuousMonoidHom.coe_toMonoidHom] at this
    exact (mulEquivAutFiber K Ω).symm.injective this
  have hfix : ∀ τ, δ.conjAut τ = τ := by
    intro τ
    obtain ⟨σ, rfl⟩ := hsurj τ
    have h3 : ξ₁.x ≫ f ≫ C₂.toSpec = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [hf]
      exact ξ₁.over
    have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp f C₂.toSpec rfl
      (comp_over_of_kHom ξ₁ hf) h3) σ
    rw [fundamentalGroupMap_congr hf h3 ξ₁.over] at c1
    calc δ.conjAut (fundamentalGroupMap C₁.toSpec ξ₁.over σ)
        = autContinuousMulEquivOfIso δ (fundamentalGroupMap C₂.toSpec
            (comp_over_of_kHom ξ₁ hf) (fundamentalGroupMap f rfl σ)) := by rw [c1]; rfl
      _ = fundamentalGroupMap C₂.toSpec ξ₂.over
            (autContinuousMulEquivOfIso γ (fundamentalGroupMap f rfl σ)) :=
          (fundamentalGroupMap_autContinuousMulEquivOfIso _ _ _ γ _).symm
      _ = fundamentalGroupMap C₂.toSpec ξ₂.over (φ σ) := by rw [hγ]
      _ = _ := hover σ
  have hδ : δ = Iso.refl _ := by
    have hc : (δ : Aut _) ∈ Subgroup.center _ := Subgroup.mem_center_iff.2 fun τ ↦ by
      have := hfix τ
      rw [Aut_conjAut_eq] at this
      calc τ * δ = δ * τ * δ⁻¹ * δ := by rw [this]
        _ = δ * τ := by group
    rw [hcen, Subgroup.mem_bot] at hc
    exact hc
  have := congrArg (fun i ↦ pullbackFiberIso C₂.toSpec (comp_over_of_kHom ξ₁ hf) ≪≫ i) hδ
  simp only [δ, fiberIsoMap, transportIso, Iso.self_symm_id_assoc, Iso.trans_refl] at this
  exact this

end PathOverBase

/-! ### The rel-isom-DGC for `Π_U = π₁ᵉᵗ(Spec Γ(U), basePoint)` -/

section Arith

open HypCurve

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω]

/-- The structure morphism `Spec Γ(U) ⟶ Spec K`. -/
abbrev sKU (C : HypCurve K) : Spec Γ(C.Xbar, C.U) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)))

/-- The base point of `Π_U` as a geometric point of the open subscheme `U` (through
`U ≅ Spec Γ(U)`). -/
def arithGeomPt (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) : GeomPt Ω C :=
  ⟨(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≫ (isAffineOpen_U C hc).isoSpec.inv, by
    rw [HypCurve.toSpec, Category.assoc (basePoint Ω C hc ≫ _),
      isoSpec_inv_ι_structure K (isAffineOpen_U C hc)]
    exact basePoint_spec₂ Ω C hc⟩

lemma isoSpec_inv_toSpec (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    (isAffineOpen_U C hc).isoSpec.inv ≫ C.toSpec = sKU C := by
  rw [HypCurve.toSpec]
  exact isoSpec_inv_ι_structure K (isAffineOpen_U C hc)

lemma isoSpec_hom_sKU (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    (isAffineOpen_U C hc).isoSpec.hom ≫ sKU C = C.toSpec := by
  rw [← isoSpec_inv_toSpec C hc, Iso.hom_inv_id_assoc]

/-- `Π_U ≃ₜ* π₁ᵉᵗ(U, arithGeomPt)`. -/
def arithGeomEquiv (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ* π₁ᵉᵗ((arithGeomPt Ω C hc).x) :=
  fundamentalGroupEquivOfIso (isAffineOpen_U C hc).isoSpec.symm _

lemma arithGeomEquiv_apply (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) (σ) :
    arithGeomEquiv Ω C hc σ =
      fundamentalGroupMap (isAffineOpen_U C hc).isoSpec.inv rfl σ := rfl

lemma fundamentalGroupMap_toSpec_arithGeomEquiv (C : HypCurve K)
    (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) (σ) :
    fundamentalGroupMap C.toSpec (arithGeomPt Ω C hc).over (arithGeomEquiv Ω C hc σ) =
      projGk Ω C hc σ := by
  have h : (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≫
      (isAffineOpen_U C hc).isoSpec.inv ≫ C.toSpec =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [← Category.assoc]
    exact (arithGeomPt Ω C hc).over
  have c : fundamentalGroupMap C.toSpec (arithGeomPt Ω C hc).over
      (fundamentalGroupMap (isAffineOpen_U C hc).isoSpec.inv rfl σ) =
        fundamentalGroupMap ((isAffineOpen_U C hc).isoSpec.inv ≫ C.toSpec) h σ :=
    (DFunLike.congr_fun (fundamentalGroupMap_comp _ _ rfl (arithGeomPt Ω C hc).over h) σ).symm
  rw [arithGeomEquiv_apply, c,
    fundamentalGroupMap_congr (isoSpec_inv_toSpec C hc) h (basePoint_spec₂ Ω C hc)]
  rfl

lemma isConjInduced_arithGeomEquiv (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    IsConjInduced (isAffineOpen_U C hc).isoSpec.inv (arithGeomEquiv Ω C hc) :=
  isConjInduced_fundamentalGroupMap _ _

lemma isConjInduced_arithGeomEquiv_symm (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    IsConjInduced (isAffineOpen_U C hc).isoSpec.hom (arithGeomEquiv Ω C hc).symm :=
  isConjInduced_hom_of_inv (isAffineOpen_U C hc).isoSpec _ _ fun σ ↦
    (arithGeomEquiv Ω C hc).symm_apply_apply σ

lemma surjective_toSpec_arithGeomPt (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    Function.Surjective (fundamentalGroupMap C.toSpec (arithGeomPt Ω C hc).over) := fun τ ↦ by
  obtain ⟨σ, rfl⟩ := projGk_surjective Ω C hc τ
  exact ⟨_, fundamentalGroupMap_toSpec_arithGeomEquiv Ω C hc σ⟩

variable [Algebra.IsAlgebraic K Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {C₁ C₂ : HypCurve K} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

/-- The isomorphism `π₁ᵉᵗ(U₁, ξ₁) ≃ₜ* π₁ᵉᵗ(U₂, ξ₂)` corresponding to `φ : Π_{U₁} ≃ₜ* Π_{U₂}`. -/
def dgcTransport (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec K Ω Γ(C₂.Xbar, C₂.U))) :
    π₁ᵉᵗ((arithGeomPt Ω C₁ hc₁).x) ≃ₜ* π₁ᵉᵗ((arithGeomPt Ω C₂ hc₂).x) :=
  (arithGeomEquiv Ω C₁ hc₁).symm.trans (φ.trans (arithGeomEquiv Ω C₂ hc₂))

lemma isOverGk_dgcTransport
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec K Ω Γ(C₂.Xbar, C₂.U)))
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = projGk Ω C₁ hc₁ σ) :
    IsOverGk (arithGeomPt Ω C₁ hc₁) (arithGeomPt Ω C₂ hc₂)
      (dgcTransport Ω φ : π₁ᵉᵗ((arithGeomPt Ω C₁ hc₁).x) →ₜ* π₁ᵉᵗ((arithGeomPt Ω C₂ hc₂).x)) := by
  refine MonoidHom.ext fun σ' ↦ ?_
  obtain ⟨σ, rfl⟩ := (arithGeomEquiv Ω C₁ hc₁).surjective σ'
  have e : dgcTransport Ω φ (arithGeomEquiv Ω C₁ hc₁ σ) = arithGeomEquiv Ω C₂ hc₂ (φ σ) := by
    simp [dgcTransport]
  change (mulEquivAutFiber K Ω).symm (fundamentalGroupMap C₂.toSpec (arithGeomPt Ω C₂ hc₂).over
      (dgcTransport Ω φ (arithGeomEquiv Ω C₁ hc₁ σ))) =
    (mulEquivAutFiber K Ω).symm (fundamentalGroupMap C₁.toSpec (arithGeomPt Ω C₁ hc₁).over
      (arithGeomEquiv Ω C₁ hc₁ σ))
  rw [e, fundamentalGroupMap_toSpec_arithGeomEquiv, fundamentalGroupMap_toSpec_arithGeomEquiv,
    hφ]

/-- **The rel-isom-DGC in the arithmetic model, existence**: every continuous isomorphism
`Π_{U₁} ≃ₜ* Π_{U₂}` over `G_K` is induced, up to a change of base point, by a `K`-isomorphism
`Spec Γ(U₁) ≅ Spec Γ(U₂)`. -/
theorem exists_isConjInduced_of_relIsomDGC (hDGC : RelIsomDGC K)
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec K Ω Γ(C₂.Xbar, C₂.U)))
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = projGk Ω C₁ hc₁ σ) :
    ∃ F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U),
      F.hom ≫ sKU C₂ = sKU C₁ ∧ IsConjInduced F.hom φ := by
  obtain ⟨⟨f, hf⟩, ⟨γ, -, hγ⟩, -⟩ := hDGC Ω C₁ C₂ (arithGeomPt Ω C₁ hc₁) (arithGeomPt Ω C₂ hc₂)
    (dgcTransport Ω φ) (isOverGk_dgcTransport Ω φ hφ)
  set i₁ := (isAffineOpen_U C₁ hc₁).isoSpec
  set i₂ := (isAffineOpen_U C₂ hc₂).isoSpec
  refine ⟨i₁.symm ≪≫ f ≪≫ i₂, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [isoSpec_hom_sKU C₂ hc₂, hf, isoSpec_inv_toSpec C₁ hc₁]
  · have H₁ := isConjInduced_arithGeomEquiv Ω C₁ hc₁
    have H₂ : IsConjInduced f.hom (dgcTransport Ω φ) := ⟨γ, hγ⟩
    have H₃ := isConjInduced_arithGeomEquiv_symm Ω C₂ hc₂
    refine ((H₁.comp H₂).comp H₃).congr_hom
      (by simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]; rfl) |>.congr_fun fun σ ↦ ?_
    simp [dgcTransport]

/-- **The rel-isom-DGC in the arithmetic model, uniqueness**: the `K`-isomorphism inducing a
continuous isomorphism over `G_K` is unique. -/
theorem eq_of_isConjInduced_of_relIsomDGC (hDGC : RelIsomDGC K)
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec K Ω Γ(C₂.Xbar, C₂.U)))
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = projGk Ω C₁ hc₁ σ)
    {F F' : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)}
    (hF : F.hom ≫ sKU C₂ = sKU C₁) (hF' : F'.hom ≫ sKU C₂ = sKU C₁)
    (H : IsConjInduced F.hom φ) (H' : IsConjInduced F'.hom φ) : F = F' := by
  set i₁ := (isAffineOpen_U C₁ hc₁).isoSpec
  set i₂ := (isAffineOpen_U C₂ hc₂).isoSpec
  have hcen := (isSlim_Gk (K := K) Ω).center_eq_bot
  have key : ∀ G : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U), G.hom ≫ sKU C₂ = sKU C₁ →
      IsConjInduced G.hom φ → ∃ hG : (i₁ ≪≫ G ≪≫ i₂.symm).hom ≫ C₂.toSpec = C₁.toSpec,
        InducedBy (arithGeomPt Ω C₁ hc₁) (arithGeomPt Ω C₂ hc₂) ⟨i₁ ≪≫ G ≪≫ i₂.symm, hG⟩
          (dgcTransport Ω φ) := by
    intro G hG HG
    have hG' : (i₁ ≪≫ G ≪≫ i₂.symm).hom ≫ C₂.toSpec = C₁.toSpec := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [isoSpec_inv_toSpec C₂ hc₂, hG, isoSpec_hom_sKU C₁ hc₁]
    refine ⟨hG', ?_⟩
    have H₁ := isConjInduced_arithGeomEquiv_symm Ω C₁ hc₁
    have H₃ := isConjInduced_arithGeomEquiv Ω C₂ hc₂
    obtain ⟨γ, hγ⟩ := (((H₁.comp HG).comp H₃).congr_hom
      (show (i₁.hom ≫ G.hom) ≫ i₂.inv = (i₁ ≪≫ G ≪≫ i₂.symm).hom by simp)).congr_fun
        (ψ := ⇑(dgcTransport Ω φ)) fun _ ↦ rfl
    refine ⟨γ, isPathOverBase_of_isOverGk _ _ hG' _ (isOverGk_dgcTransport Ω φ hφ) γ hγ
      (surjective_toSpec_arithGeomPt Ω C₁ hc₁) hcen, hγ⟩
  obtain ⟨hG, hI⟩ := key F hF H
  obtain ⟨hG', hI'⟩ := key F' hF' H'
  obtain ⟨_, -, huniq⟩ := hDGC Ω C₁ C₂ (arithGeomPt Ω C₁ hc₁) (arithGeomPt Ω C₂ hc₂)
    (dgcTransport Ω φ) (isOverGk_dgcTransport Ω φ hφ)
  have e := (huniq _ hI).trans (huniq _ hI').symm
  have e' : i₁ ≪≫ F ≪≫ i₂.symm = i₁ ≪≫ F' ≪≫ i₂.symm := congrArg Subtype.val e
  ext1
  have := congrArg (fun j ↦ i₁.inv ≫ j.hom ≫ i₂.hom) e'
  simpa using this

variable (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

/-- Conjugation by `t` as a continuous isomorphism. -/
def conjCMEquiv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (t : G) :
    G ≃ₜ* G where
  toMulEquiv := MulAut.conj t
  continuous_toFun := by
    change Continuous fun x ↦ t * x * t⁻¹
    fun_prop
  continuous_invFun := by
    have : ⇑(MulAut.conj t).symm = fun x ↦ t⁻¹ * x * t :=
      funext fun x ↦ MulAut.conj_symm_apply t x
    change Continuous ⇑(MulAut.conj t).symm
    rw [this]
    fun_prop

/-- **A `K`-automorphism of `Spec Γ(U)` inducing an inner automorphism of `Π_U` (over `G_K`) is
the identity** (uniqueness in the rel-isom-DGC). -/
theorem eq_refl_of_isConjInduced_conj (hDGC : RelIsomDGC K)
    (t : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (ht : ∀ σ, projGk Ω C hc (t * σ * t⁻¹) = projGk Ω C hc σ)
    {F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U)} (hF : F.hom ≫ sKU C = sKU C)
    (H : IsConjInduced F.hom fun σ ↦ t * σ * t⁻¹) : F = Iso.refl _ := by
  have Hid : IsConjInduced (Iso.refl (Spec Γ(C.Xbar, C.U))).hom fun σ ↦ t * σ * t⁻¹ :=
    (isConjInduced_iff _ (Category.comp_id _) _).2 ⟨t, fun σ ↦ by
      change _ = t.conjAut (fundamentalGroupMap (𝟙 _) (Category.comp_id _) σ)
      rw [fundamentalGroupMap_id, Aut_conjAut_eq]
      rfl⟩
  exact eq_of_isConjInduced_of_relIsomDGC Ω hDGC (conjCMEquiv t) ht hF (by simp) H Hid

end Arith

end CurvesJacobian.Cusp
