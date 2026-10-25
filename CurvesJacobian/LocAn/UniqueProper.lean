/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.DGCArith
import CurvesJacobian.LocAn.PadicSlim
import CurvesJacobian.LocAn.ExistsAssembly

/-!
# Uniqueness in the rel-isom-DGC for proper curves: the formal reduction (MR7, S8 step R0)

The uniqueness half `Belyi.Anabelian.RelIsomDGC.Unique k` of the whitelist statement for
[LocAn] Theorem A says that two `k`-isomorphisms `U₁ ≅ U₂` inducing the same isomorphism
`Π_{U₁} ≃ Π_{U₂}` over `G_k` (up to `Δ₂`-conjugation, `InducedBy`) are equal. For number fields
and affine curves it is a theorem (`CurvesJacobian.LocAn.innerRigid`,
`LocAn/UniqueReduction.lean`). This file sets up the case of **proper** curves (`U = X̄`, genus
`≥ 2`), the case to which [LocAn] Thm 14.1 reduces the injectivity statement (proof, injectivity
paragraph, l.4019–4032 of `The Local Pro-p Anabelian Geometry of Curves.txt`: "we may assume that
both `U_K` and `Y_K` admit hyperbolic compactifications … (i.e. … are proper hyperbolic curves
over `K`)").

## Main results

* `Belyi.Anabelian.RelIsomDGC.UniqueProper k`: `RelIsomDGC.Unique k` for proper curves, and
  `RelIsomDGC.Unique.uniqueProper`;
* `HypCurve.KIso.refl`, `KIso.comp`, `KIso.symm` and `KIso.ext`;
* paths: `isPathOverBase_iff` (`γ` lies over the base iff its image in the fibre functor of
  `Spec k` is the identity), `FiniteEtale.fiberIsoMap_trans`, `fiberIsoMap_symm`,
  `fiberIsoMap_refl`, `fiberIsoMap_congr`, `fiberIsoMap_fiberIsoMap` (base point changes along
  a composite, via `pullbackFiberIso_comp` and `PreGaloisCategory.transportIso_transportIso`,
  `transportIso_isoWhiskerRight`);
* `InducedByHom.isConjInduced`, `InducedBy.isConjInduced`: forget the over-base condition;
* **`InducedByHom.comp`**, `InducedBy.comp`: composition, with the composite path over the base;
  **`InducedBy.symm`**: the inverse of an isomorphism induced by `f` is induced by `f⁻¹`, with
  the inverse path over the base;
* `CurvesJacobian.LocAn.InnerRigidProper Ω C` (a plain `Prop`, never assumed): a `k`-automorphism
  of `C` inducing the identity of `Π_C` up to a change of base point is the identity;
* **`CurvesJacobian.LocAn.uniqueProper_of_innerRigidProper`**: inner rigidity of every proper
  hyperbolic curve over `k` gives `RelIsomDGC.UniqueProper k` (mirror of
  `eq_of_isConjInduced_of_innerRigid`);
* the `Δ`-element (where slimness of `G_k` enters): `inducedBy_of_isConjInduced` (an
  isomorphism over `G_k` induced up to an arbitrary change of base point is induced up to
  `Δ`-conjugation, given `Π_U ↠ G_k` and `Z(G_k) = 1`), `inducedBy_refl_of_isConjInduced_id`;
  `surjective_fundamentalGroupMap_toSpec` (`Π_U ↠ G_k` at every geometric point, every hyperbolic
  curve); for finite `k/ℚ_p` (`center_Gk_padic`): `isPathOverBase_of_isOverGk_padic`,
  **`inducedBy_iff_isConjInduced_padic`**, `innerRigidProper_iff_padic` (inner rigidity is
  equivalent to its `Δ`-inner form `InducedBy ξ₀ ξ₀ h id → h = id`);
* `UniqueProperMLF p` and `uniqueProperMLF_of_innerRigidProper`.
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian

noncomputable section

/-! ### Base point changes along compositions -/

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {F F' : C ⥤ FintypeCat.{w}} {G G' : D ⥤ FintypeCat.{w}} {K K' : E ⥤ FintypeCat.{w}}

set_option backward.isDefEq.respectTransparency false in
/-- `transportIso` is unchanged when the functor `H` is replaced by an isomorphic one. -/
lemma transportIso_isoWhiskerRight {H H' : D ⥤ C} (c : H' ≅ H) (e : H ⋙ F ≅ G)
    (e' : H ⋙ F' ≅ G') (α : F ≅ F') :
    transportIso (Functor.isoWhiskerRight c F ≪≫ e) (Functor.isoWhiskerRight c F' ≪≫ e') α =
      transportIso e e' α := by
  refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
  simp only [transportIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [α.hom.naturality_assoc, ← F'.map_comp_assoc, Iso.inv_hom_id_app, F'.map_id,
    Category.id_comp]

/-- Transporting twice is transporting along the composite functor. -/
lemma transportIso_transportIso (H₁ : D ⥤ C) (H₂ : E ⥤ D) (e : H₁ ⋙ F ≅ G)
    (e' : H₁ ⋙ F' ≅ G') (d : H₂ ⋙ G ≅ K) (d' : H₂ ⋙ G' ≅ K') (α : F ≅ F') :
    transportIso d d' (transportIso e e' α) =
      transportIso (Functor.associator H₂ H₁ F ≪≫ Functor.isoWhiskerLeft H₂ e ≪≫ d)
        (Functor.associator H₂ H₁ F' ≪≫ Functor.isoWhiskerLeft H₂ e' ≪≫ d') α := by
  ext X
  simp [transportIso]

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {X Y W : Scheme.{u}} {Ω : Type u} [Field Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `pullbackFiberIso` of a composite, componentwise. -/
lemma pullbackFiberIso_comp_hom_app (f : Y ⟶ X) (g : X ⟶ W) {ξ₀ : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : ξ₀ ≫ f = η) (h₂ : η ≫ g = ζ)
    (h : ξ₀ ≫ f ≫ g = ζ) (A : FiniteEtale W) :
    (fiber ξ₀).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
      (pullbackFiberIso f h₁).hom.app ((pullback g).obj A) ≫ (pullbackFiberIso g h₂).hom.app A =
    (pullbackFiberIso (f ≫ g) h).hom.app A := by
  have key : (pullback ξ₀).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
        (MorphismProperty.Over.pullbackComp ξ₀ f η h₁.symm).inv.app ((pullback g).obj A) ≫
        (MorphismProperty.Over.pullbackComp η g ζ h₂.symm).inv.app A =
      (MorphismProperty.Over.pullbackComp ξ₀ (f ≫ g) ζ h.symm).inv.app A := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;> simp [FiniteEtale]
  rw [pullbackFiberIso_hom_app (f ≫ g), ← key, pullbackFiberIso_hom_app f,
    pullbackFiberIso_hom_app g]
  simp only [fiber, Functor.comp_map, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **`pullbackFiberIso` of a composite.** -/
lemma pullbackFiberIso_comp (f : Y ⟶ X) (g : X ⟶ W) {ξ₀ : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : ξ₀ ≫ f = η) (h₂ : η ≫ g = ζ)
    (h : ξ₀ ≫ f ≫ g = ζ) :
    pullbackFiberIso (f ≫ g) h =
      Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp f g) (fiber ξ₀) ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f h₁) ≪≫
        pullbackFiberIso g h₂ := by
  refine Iso.ext (NatTrans.ext (funext fun A ↦ ?_))
  rw [← pullbackFiberIso_comp_hom_app f g h₁ h₂ h A]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  rfl

/-- Base point changes compose. -/
lemma fiberIsoMap_trans (f : Y ⟶ X) {x x' x'' : Spec (.of Ω) ⟶ Y}
    {η η' η'' : Spec (.of Ω) ⟶ X} (h : x ≫ f = η) (h' : x' ≫ f = η') (h'' : x'' ≫ f = η'')
    (α : fiber x ≅ fiber x') (β : fiber x' ≅ fiber x'') :
    fiberIsoMap f h h'' (α ≪≫ β) = fiberIsoMap f h h' α ≪≫ fiberIsoMap f h' h'' β := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- Base point changes commute with inverses. -/
lemma fiberIsoMap_symm (f : Y ⟶ X) {x x' : Spec (.of Ω) ⟶ Y} {η η' : Spec (.of Ω) ⟶ X}
    (h : x ≫ f = η) (h' : x' ≫ f = η') (α : fiber x ≅ fiber x') :
    fiberIsoMap f h' h α.symm = (fiberIsoMap f h h' α).symm := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- The trivial base point change maps to the trivial one. -/
lemma fiberIsoMap_refl (f : Y ⟶ X) {x : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h : x ≫ f = η) : fiberIsoMap f h h (Iso.refl (fiber x)) = Iso.refl _ := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- `fiberIsoMap` only depends on the morphism, not on the proofs of the base point equations. -/
lemma fiberIsoMap_congr {f f' : Y ⟶ X} (e : f = f') {x x' : Spec (.of Ω) ⟶ Y}
    {η η' : Spec (.of Ω) ⟶ X} (h : x ≫ f = η) (h' : x' ≫ f = η') (k : x ≫ f' = η)
    (k' : x' ≫ f' = η') (α : fiber x ≅ fiber x') :
    fiberIsoMap f h h' α = fiberIsoMap f' k k' α := by
  subst e
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Base point changes along a composite**: pushing forward along `f` and then along `g` is
pushing forward along `f ≫ g`. -/
lemma fiberIsoMap_fiberIsoMap (f : Y ⟶ X) (g : X ⟶ W) {x x' : Spec (.of Ω) ⟶ Y}
    {ξ₀ ξ₀' : Spec (.of Ω) ⟶ X} {η η' : Spec (.of Ω) ⟶ W} (h : x ≫ f = ξ₀) (h' : x' ≫ f = ξ₀')
    (k : ξ₀ ≫ g = η) (k' : ξ₀' ≫ g = η') (hk : x ≫ f ≫ g = η) (hk' : x' ≫ f ≫ g = η')
    (α : fiber x ≅ fiber x') :
    fiberIsoMap g k k' (fiberIsoMap f h h' α) = fiberIsoMap (f ≫ g) hk hk' α := by
  simp only [fiberIsoMap]
  rw [pullbackFiberIso_comp f g h k hk, pullbackFiberIso_comp f g h' k' hk',
    transportIso_isoWhiskerRight, transportIso_transportIso]

end AlgebraicGeometry.FiniteEtale

/-! ### `k`-isomorphisms and paths over the base -/

namespace Belyi.Anabelian

open HypCurve in
/-- **Uniqueness half of the rel-isom-DGC for proper hyperbolic curves** over `k`: the statement
of `RelIsomDGC.Unique k` for curves `C₁, C₂` without cusps (`U = X̄`), the case [LocAn] Thm 14.1
reduces injectivity to (proof, l.4019–4032). -/
def RelIsomDGC.UniqueProper (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
    haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
    ∀ (C₁ C₂ : HypCurve k), (C₁.U : Set C₁.Xbar)ᶜ = ∅ → (C₂.U : Set C₂.Xbar)ᶜ = ∅ →
    ∀ (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)),
    IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) →
      ∀ f f' : KIso C₁ C₂, InducedBy ξ₁ ξ₂ f φ → InducedBy ξ₁ ξ₂ f' φ → f = f'

/-- The uniqueness half implies its restriction to proper curves. -/
theorem RelIsomDGC.Unique.uniqueProper {k : Type u} [Field k] [CharZero k]
    (h : RelIsomDGC.Unique k) : RelIsomDGC.UniqueProper k :=
  fun Ω _ _ _ C₁ C₂ _ _ ξ₁ ξ₂ φ hφ ↦ h Ω C₁ C₂ ξ₁ ξ₂ φ hφ

namespace HypCurve.KIso

variable {k : Type u} [Field k] {C₁ C₂ C₃ : HypCurve k}

/-- The identity `k`-isomorphism. -/
def refl (C : HypCurve k) : KIso C C :=
  ⟨Iso.refl _, Category.id_comp _⟩

/-- Composition of `k`-isomorphisms. -/
def comp (f : KIso C₁ C₂) (g : KIso C₂ C₃) : KIso C₁ C₃ :=
  ⟨f.1 ≪≫ g.1, (Category.assoc _ _ _).trans ((congrArg _ g.2).trans f.2)⟩

/-- The inverse of a `k`-isomorphism. -/
def symm (f : KIso C₁ C₂) : KIso C₂ C₁ :=
  ⟨f.1.symm, (Iso.inv_comp_eq _).2 f.2.symm⟩

lemma ext {f g : KIso C₁ C₂} (e : f.1 = g.1) : f = g :=
  Subtype.ext e

@[simp] lemma refl_hom (C : HypCurve k) : (refl C).1.hom = 𝟙 _ := rfl

@[simp] lemma comp_hom (f : KIso C₁ C₂) (g : KIso C₂ C₃) : (f.comp g).1.hom = f.1.hom ≫ g.1.hom :=
  rfl

@[simp] lemma symm_hom (f : KIso C₁ C₂) : f.symm.1.hom = f.1.inv := rfl

lemma inv_toSpec (f : KIso C₁ C₂) : f.1.inv ≫ C₁.toSpec = C₂.toSpec :=
  f.symm.2

end HypCurve.KIso

section Induced

open FiniteEtale HypCurve

variable {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
  [IsGalois k Ω] {C₁ C₂ C₃ : HypCurve k}

omit [IsSepClosed Ω] [IsGalois k Ω] in
/-- **A path lies over the base iff its image in the fibre functor of `Spec k` is trivial.** -/
lemma isPathOverBase_iff {C : HypCurve k} {y₁ y₂ : Spec (.of Ω) ⟶ C.U.toScheme}
    (hy₁ : y₁ ≫ C.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hy₂ : y₂ ≫ C.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (γ : fiber y₁ ≅ fiber y₂) :
    IsPathOverBase hy₁ hy₂ γ ↔ fiberIsoMap C.toSpec hy₁ hy₂ γ = Iso.refl _ := by
  constructor
  · intro H
    rw [fiberIsoMap, transportIso, H, Iso.symm_self_id]
  · intro H
    have := congrArg (fun i ↦ pullbackFiberIso C.toSpec hy₁ ≪≫ i) H
    simpa [fiberIsoMap, transportIso, IsPathOverBase] using this

omit [IsSepClosed Ω] [IsGalois k Ω] in
/-- **Forgetting the over-base condition**: a homomorphism induced by `f` up to
`Δ₂`-conjugation is induced by `f` up to a change of base point. -/
lemma InducedByHom.isConjInduced {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂}
    {f : C₁.U.toScheme ⟶ C₂.U.toScheme} {hf : f ≫ C₂.toSpec = C₁.toSpec}
    {φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)} (H : InducedByHom ξ₁ ξ₂ f hf φ) : IsConjInduced f φ := by
  obtain ⟨γ, -, hγ⟩ := H
  exact ⟨γ, hγ⟩

omit [IsSepClosed Ω] [IsGalois k Ω] in
/-- **Forgetting the over-base condition** for isomorphisms. -/
lemma InducedBy.isConjInduced {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂} {f : KIso C₁ C₂}
    {φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)} (H : InducedBy ξ₁ ξ₂ f φ) : IsConjInduced f.1.hom φ :=
  InducedByHom.isConjInduced H

omit [IsSepClosed Ω] [IsGalois k Ω] in
/-- **Composition of induced homomorphisms, keeping the path over the base**: if `f` induces `φ`
and `g` induces `ψ` up to `Δ`-conjugation, then `f ≫ g` induces `ψ ∘ φ` up to
`Δ₃`-conjugation. -/
theorem InducedByHom.comp {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂} {ξ₃ : GeomPt Ω C₃}
    {f : C₁.U.toScheme ⟶ C₂.U.toScheme} {g : C₂.U.toScheme ⟶ C₃.U.toScheme}
    {hf : f ≫ C₂.toSpec = C₁.toSpec} {hg : g ≫ C₃.toSpec = C₂.toSpec}
    {φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)} {ψ : π₁ᵉᵗ(ξ₂.x) →ₜ* π₁ᵉᵗ(ξ₃.x)}
    (Hφ : InducedByHom ξ₁ ξ₂ f hf φ) (Hψ : InducedByHom ξ₂ ξ₃ g hg ψ) :
    InducedByHom ξ₁ ξ₃ (f ≫ g) (by rw [Category.assoc, hg, hf]) (ψ.comp φ) := by
  obtain ⟨γ₁, hp₁, h₁⟩ := Hφ
  obtain ⟨γ₂, hp₂, h₂⟩ := Hψ
  have e : (ξ₁.x ≫ f) ≫ g = ξ₁.x ≫ f ≫ g := Category.assoc _ _ _
  refine ⟨fiberIsoMap g e (rfl : ξ₂.x ≫ g = _) γ₁ ≪≫ γ₂, ?_, fun σ ↦ ?_⟩
  · rw [isPathOverBase_iff] at hp₁ hp₂ ⊢
    rw [fiberIsoMap_trans _ _ (comp_over_of_kHom ξ₂ hg), hp₂, Iso.trans_refl,
      fiberIsoMap_fiberIsoMap g C₃.toSpec e rfl _ _ (by rw [hg]; exact comp_over_of_kHom ξ₁ hf)
        (by rw [hg]; exact ξ₂.over),
      fiberIsoMap_congr hg _ _ (comp_over_of_kHom ξ₁ hf) ξ₂.over, hp₁]
  · have c : fundamentalGroupMap g e (fundamentalGroupMap f rfl σ) =
        fundamentalGroupMap (f ≫ g) rfl σ :=
      (DFunLike.congr_fun (fundamentalGroupMap_comp f g rfl e rfl) σ).symm
    change ψ (φ σ) = _
    calc ψ (φ σ) = autContinuousMulEquivOfIso γ₂ (fundamentalGroupMap g rfl
          (autContinuousMulEquivOfIso γ₁ (fundamentalGroupMap f rfl σ))) := by
          rw [h₂, h₁]
          rfl
      _ = _ := by
          rw [fundamentalGroupMap_autContinuousMulEquivOfIso g e rfl γ₁, c]
          rw [Iso.trans_conjAut]
          rfl

omit [IsSepClosed Ω] [IsGalois k Ω] in
/-- **Composition of induced isomorphisms, keeping the path over the base.** -/
theorem InducedBy.comp {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂} {ξ₃ : GeomPt Ω C₃}
    {f : KIso C₁ C₂} {g : KIso C₂ C₃} {φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)}
    {ψ : π₁ᵉᵗ(ξ₂.x) ≃ₜ* π₁ᵉᵗ(ξ₃.x)} (Hφ : InducedBy ξ₁ ξ₂ f φ) (Hψ : InducedBy ξ₂ ξ₃ g ψ) :
    InducedBy ξ₁ ξ₃ (f.comp g) (φ.trans ψ) :=
  InducedByHom.comp Hφ Hψ

omit [IsSepClosed Ω] [IsGalois k Ω] in
/-- **The inverse of an induced isomorphism, keeping the path over the base**: if `f` induces
`φ` up to `Δ₂`-conjugation, then `f⁻¹` induces `φ⁻¹` up to `Δ₁`-conjugation. -/
theorem InducedBy.symm {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂} {f : KIso C₁ C₂}
    {φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)} (H : InducedBy ξ₁ ξ₂ f φ) :
    InducedBy ξ₂ ξ₁ f.symm φ.symm := by
  obtain ⟨γ, hp, hγ⟩ := H
  have h0 : (ξ₁.x ≫ f.1.hom) ≫ f.1.inv = ξ₁.x := by simp
  let ε : fiber ξ₁.x ≅ fiber (ξ₂.x ≫ f.1.inv) :=
    fiberIsoMap f.1.inv h0 (rfl : ξ₂.x ≫ f.1.inv = _) γ
  have key : ∀ σ, fundamentalGroupMap f.1.inv rfl (φ σ) = autContinuousMulEquivOfIso ε σ := by
    intro σ
    have h1 : ξ₁.x ≫ f.1.hom ≫ f.1.inv = ξ₁.x := by simp
    have h2 : ξ₁.x ≫ 𝟙 _ = ξ₁.x := Category.comp_id _
    have c : fundamentalGroupMap f.1.inv h0 (fundamentalGroupMap f.1.hom rfl σ) = σ := by
      have := DFunLike.congr_fun (fundamentalGroupMap_comp f.1.hom f.1.inv rfl h0 h1) σ
      rw [fundamentalGroupMap_congr f.1.hom_inv_id h1 h2, fundamentalGroupMap_id] at this
      exact this.symm
    have hσ : φ σ = autContinuousMulEquivOfIso γ (fundamentalGroupMap f.1.hom rfl σ) := hγ σ
    rw [hσ, fundamentalGroupMap_autContinuousMulEquivOfIso f.1.inv h0 rfl γ, c]
  refine ⟨ε.symm, ?_, fun τ ↦ ?_⟩
  · rw [isPathOverBase_iff] at hp ⊢
    have hover : (ξ₂.x ≫ f.1.inv) ≫ C₁.toSpec =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := comp_over_of_kHom ξ₂ f.inv_toSpec
    change fiberIsoMap C₁.toSpec hover ξ₁.over ε.symm = _
    rw [fiberIsoMap_symm C₁.toSpec ξ₁.over hover,
      fiberIsoMap_fiberIsoMap f.1.inv C₁.toSpec h0 rfl ξ₁.over hover
        (by rw [f.inv_toSpec]; exact comp_over_of_kHom ξ₁ f.2)
        (by rw [f.inv_toSpec]; exact ξ₂.over),
      fiberIsoMap_congr f.inv_toSpec _ _ (comp_over_of_kHom ξ₁ f.2) ξ₂.over, hp, Iso.refl_symm]
  · obtain ⟨σ, rfl⟩ := φ.surjective τ
    change φ.symm (φ σ) = ε.symm.conjAut (fundamentalGroupMap f.1.inv rfl (φ σ))
    rw [ContinuousMulEquiv.symm_apply_apply, key]
    change σ = ε.symm.conjAut (ε.conjAut σ)
    rw [← Iso.trans_conjAut, Iso.self_symm_id, Iso.conjAut_apply]
    simp

end Induced

end Belyi.Anabelian

namespace CurvesJacobian.LocAn

open HypCurve

variable {k : Type u} [Field k]

/-! ### Inner rigidity of proper curves and uniqueness -/

/-- **Inner rigidity of a hyperbolic curve** `C` (stated for every geometric point): a
`k`-automorphism of `U` inducing the identity of `π₁ᵉᵗ(U, ξ₀)` up to a change of base point is the
identity. A plain proposition (the content of the MR7 proper-curve uniqueness route: Thm C over
finite extensions, `LocAn/EqOfClosedPoints.lean`); it is never assumed. -/
def InnerRigidProper (Ω : Type u) [Field Ω] [Algebra k Ω] [IsSepClosed Ω] (C : HypCurve k) :
    Prop :=
  ∀ (ξ₀ : GeomPt Ω C) (h : KIso C C),
    IsConjInduced h.1.hom (id : π₁ᵉᵗ(ξ₀.x) → π₁ᵉᵗ(ξ₀.x)) → h = KIso.refl C

section General

variable {Ω : Type u} [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {C₁ C₂ : HypCurve k}

/-- **Uniqueness from inner rigidity**: if `U₁` is inner rigid, two `k`-isomorphisms `U₁ ≅ U₂`
inducing the same `φ : π₁ᵉᵗ(U₁, ξ₁) ≃ π₁ᵉᵗ(U₂, ξ₂)` up to a change of base point are equal. -/
theorem eq_of_isConjInduced_of_innerRigidProper (hR : InnerRigidProper Ω C₁) {ξ₁ : GeomPt Ω C₁}
    {ξ₂ : GeomPt Ω C₂} (φ : π₁ᵉᵗ(ξ₁.x) ≃* π₁ᵉᵗ(ξ₂.x)) {f f' : KIso C₁ C₂}
    (H : IsConjInduced f.1.hom φ) (H' : IsConjInduced f'.1.hom φ) : f = f' := by
  have H'' := IsConjInduced.symm_of_iso f'.1 φ H'
  have Hc : IsConjInduced (f.comp f'.symm).1.hom (id : π₁ᵉᵗ(ξ₁.x) → π₁ᵉᵗ(ξ₁.x)) :=
    (H.comp H'').congr_fun fun σ ↦ by simp
  have e := hR ξ₁ _ Hc
  refine KIso.ext (Iso.ext ?_)
  have := congrArg (fun g : KIso C₁ C₁ ↦ g.1.hom ≫ f'.1.hom) e
  simpa [KIso.comp, KIso.symm, KIso.refl] using this

/-- **`RelIsomDGC.UniqueProper` from inner rigidity of proper curves**: if every proper
hyperbolic curve over `k` is inner rigid (at every geometric point over every algebraic closure),
then the uniqueness half of the rel-isom-DGC holds for proper curves over `k`. -/
theorem uniqueProper_of_innerRigidProper (k : Type u) [Field k] [CharZero k]
    (hR : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
      haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
      ∀ C : HypCurve k, (C.U : Set C.Xbar)ᶜ = ∅ → InnerRigidProper Ω C) :
    RelIsomDGC.UniqueProper k := by
  intro Ω _ _ _ C₁ C₂ hC₁ _ ξ₁ ξ₂ φ _ f f' H H'
  haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
  exact eq_of_isConjInduced_of_innerRigidProper (hR Ω C₁ hC₁) φ.toMulEquiv H.isConjInduced
    H'.isConjInduced

/-! ### The `Δ`-element: induced up to a change of base point vs up to `Δ`-conjugation -/

/-- **`Π_U ↠ G_k` at every geometric point**: `U` is geometrically connected over `k`. -/
theorem surjective_fundamentalGroupMap_toSpec (C : HypCurve k) (ξ₀ : GeomPt Ω C) :
    Function.Surjective (fundamentalGroupMap C.toSpec ξ₀.over) := by
  haveI := IsCurveOver.isIntegral k C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  haveI hsurj : Surjective C.toSpec :=
    ⟨fun y ↦ ⟨Classical.arbitrary C.U.toScheme, Subsingleton.elim _ _⟩⟩
  haveI : GeometricallyIrreducible C.toSpec := by
    rw [HypCurve.toSpec]
    infer_instance
  haveI : UniversallyOpen C.toSpec := by
    rw [HypCurve.toSpec]
    infer_instance
  exact fundamentalGroupMap_surjective_of_geometricallyConnected _ _

variable [IsGalois k Ω]

/-- **The `Δ`-element** (where `Z(G_k) = 1` enters): an isomorphism over `G_k` induced by `f` up
to an arbitrary change of base point is induced by `f` up to `Δ₂`-conjugation. -/
theorem inducedBy_of_isConjInduced {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂} (f : KIso C₁ C₂)
    (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)) (hφ : IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)))
    (H : IsConjInduced f.1.hom φ)
    (hcen : Subgroup.center π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap k Ω))) = ⊥) :
    InducedBy ξ₁ ξ₂ f φ := by
  obtain ⟨γ, hγ⟩ := H
  exact ⟨γ, CurvesJacobian.Cusp.isPathOverBase_of_isOverGk ξ₁ ξ₂ f.2 _ hφ γ hγ
    (surjective_fundamentalGroupMap_toSpec C₁ ξ₁) hcen, hγ⟩

/-- `InducedBy ↔ IsConjInduced` for isomorphisms over `G_k`, when `Z(G_k) = 1`. -/
theorem inducedBy_iff_isConjInduced {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂} (f : KIso C₁ C₂)
    (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)) (hφ : IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)))
    (hcen : Subgroup.center π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap k Ω))) = ⊥) :
    InducedBy ξ₁ ξ₂ f φ ↔ IsConjInduced f.1.hom φ :=
  ⟨InducedBy.isConjInduced, (inducedBy_of_isConjInduced f φ hφ · hcen)⟩

/-- **The `Δ`-element for an automorphism inducing an inner automorphism**: if `h` induces the
identity up to a change of base point, the path lies over the base, i.e. `h` induces the identity
up to `Δ`-conjugation. -/
theorem inducedBy_refl_of_isConjInduced_id {C : HypCurve k} (ξ₀ : GeomPt Ω C) (h : KIso C C)
    (H : IsConjInduced h.1.hom (id : π₁ᵉᵗ(ξ₀.x) → π₁ᵉᵗ(ξ₀.x)))
    (hcen : Subgroup.center π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap k Ω))) = ⊥) :
    InducedBy ξ₀ ξ₀ h (ContinuousMulEquiv.refl _) :=
  inducedBy_of_isConjInduced h _ rfl H hcen

/-- Inner rigidity is equivalent to its `Δ`-inner form when `Z(G_k) = 1`. -/
theorem innerRigidProper_iff {C : HypCurve k}
    (hcen : Subgroup.center π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap k Ω))) = ⊥) :
    InnerRigidProper Ω C ↔ ∀ (ξ₀ : GeomPt Ω C) (h : KIso C C),
      InducedBy ξ₀ ξ₀ h (ContinuousMulEquiv.refl _) → h = KIso.refl C :=
  ⟨fun hR ξ₀ h H ↦ hR ξ₀ h H.isConjInduced,
    fun hR ξ₀ h H ↦ hR ξ₀ h (inducedBy_refl_of_isConjInduced_id ξ₀ h H hcen)⟩

end General

/-! ### Over finite extensions of `ℚ_p` -/

section Padic

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [Algebra.IsAlgebraic K Ω] [IsGalois K Ω] {C₁ C₂ : HypCurve K}

include p in
/-- **Over a finite extension of `ℚ_p`, a change of base point realising an isomorphism over
`G_K` lies over the base** (`G_K` has trivial centre, `center_Gk_padic`). -/
theorem isPathOverBase_of_isOverGk_padic (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂)
    {f : C₁.U.toScheme ⟶ C₂.U.toScheme} (hf : f ≫ C₂.toSpec = C₁.toSpec)
    (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) (hφ : IsOverGk ξ₁ ξ₂ φ)
    (γ : fiber (ξ₁.x ≫ f) ≅ fiber ξ₂.x)
    (hγ : ∀ σ, φ σ = autContinuousMulEquivOfIso γ (fundamentalGroupMap f rfl σ)) :
    IsPathOverBase (comp_over_of_kHom ξ₁ hf) ξ₂.over γ :=
  CurvesJacobian.Cusp.isPathOverBase_of_isOverGk ξ₁ ξ₂ hf φ hφ γ hγ
    (surjective_fundamentalGroupMap_toSpec C₁ ξ₁) (center_Gk_padic p Ω)

include p in
/-- **Over a finite extension of `ℚ_p`, `InducedBy ↔ IsConjInduced`** for isomorphisms over
`G_K`. -/
theorem inducedBy_iff_isConjInduced_padic {ξ₁ : GeomPt Ω C₁} {ξ₂ : GeomPt Ω C₂}
    (f : KIso C₁ C₂) (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x))
    (hφ : IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x))) :
    InducedBy ξ₁ ξ₂ f φ ↔ IsConjInduced f.1.hom φ :=
  inducedBy_iff_isConjInduced f φ hφ (center_Gk_padic p Ω)

include p in
/-- Over a finite extension of `ℚ_p`, inner rigidity is equivalent to its `Δ`-inner form. -/
theorem innerRigidProper_iff_padic {C : HypCurve K} :
    InnerRigidProper Ω C ↔ ∀ (ξ₀ : GeomPt Ω C) (h : KIso C C),
      InducedBy ξ₀ ξ₀ h (ContinuousMulEquiv.refl _) → h = KIso.refl C :=
  innerRigidProper_iff (center_Gk_padic p Ω)

end Padic

/-- **Uniqueness for proper curves over every finite extension of `ℚ_p`** (a statement; the
S8 sub-task "uniqueness for proper curves over MLFs"). -/
def UniqueProperMLF (p : ℕ) [Fact p.Prime] : Prop :=
  ForallMLF.{u} p fun L _ _ ↦ RelIsomDGC.UniqueProper L

/-- `UniqueProperMLF` from inner rigidity of every proper hyperbolic curve over every finite
extension of `ℚ_p`. -/
theorem uniqueProperMLF_of_innerRigidProper (p : ℕ) [Fact p.Prime]
    (hR : ∀ (L : Type u) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
      (Ω : Type u) [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω],
      haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω)
      ∀ C : HypCurve L, (C.U : Set C.Xbar)ᶜ = ∅ → InnerRigidProper Ω C) :
    UniqueProperMLF.{u} p := fun L _ _ _ ↦
  @uniqueProper_of_innerRigidProper L _ (charZero_of_padic p L) (hR L)

end CurvesJacobian.LocAn
