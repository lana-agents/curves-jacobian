/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BasePointChange

/-!
# Base point changes along morphisms: composition API for `fiberIsoMap`

`AlgebraicGeometry.FiniteEtale.fiberIsoMap f h h' α` pushes a path `α : fiber q ≅ fiber q'`
between geometric points of `Y` (with possibly different fields `Ω`, `Ω'`) forward along
`f : Y ⟶ X` (`CurvesJacobian/Cusp/BasePointChange.lean`). This file collects its functoriality:

* `CategoryTheory.PreGaloisCategory.transportIso_isoWhiskerRight`, `transportIso_transportIso`;
* `AlgebraicGeometry.FiniteEtale.pullbackFiberIso_comp(_hom_app)`: `pullbackFiberIso` of a
  composite;
* `fiberIsoMap_trans`, `fiberIsoMap_symm`, `fiberIsoMap_refl`, `fiberIsoMap_eqToIso`,
  `fiberIsoMap_congr`, `fiberIsoMap_fiberIsoMap` (`g_*(f_* α) = (f ≫ g)_* α`);
* `fundamentalGroupMap_eq_fiberIsoMap`: `fundamentalGroupMap f h σ = fiberIsoMap f h h σ`.

(Merged from the single-field copies in `LocAn/UniqueProper.lean` and the multi-field copies in
`LocAn/SectionBridgeAut.lean`.)
-/

open CategoryTheory Functor

universe u u₁ u₂ u₃ u₄ u₅ u₆ w

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]
  {E : Type u₅} [Category.{u₆} E]
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

open PreGaloisCategory

variable {X Y W : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `pullbackFiberIso` of a composite, componentwise. -/
lemma pullbackFiberIso_comp_hom_app (f : Y ⟶ X) (g : X ⟶ W) {q : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : q ≫ f = η) (h₂ : η ≫ g = ζ)
    (h : q ≫ f ≫ g = ζ) (A : FiniteEtale W) :
    (fiber q).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
      (pullbackFiberIso f h₁).hom.app ((pullback g).obj A) ≫ (pullbackFiberIso g h₂).hom.app A =
    (pullbackFiberIso (f ≫ g) h).hom.app A := by
  have key : (pullback q).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
        (MorphismProperty.Over.pullbackComp q f η h₁.symm).inv.app ((pullback g).obj A) ≫
        (MorphismProperty.Over.pullbackComp η g ζ h₂.symm).inv.app A =
      (MorphismProperty.Over.pullbackComp q (f ≫ g) ζ h.symm).inv.app A := by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext <;> simp [FiniteEtale]
  rw [pullbackFiberIso_hom_app (f ≫ g), ← key, pullbackFiberIso_hom_app f,
    pullbackFiberIso_hom_app g]
  simp only [fiber, Functor.comp_map, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- `pullbackFiberIso` of a composite. -/
lemma pullbackFiberIso_comp (f : Y ⟶ X) (g : X ⟶ W) {q : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : q ≫ f = η) (h₂ : η ≫ g = ζ)
    (h : q ≫ f ≫ g = ζ) :
    pullbackFiberIso (f ≫ g) h =
      Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp f g) (fiber q) ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f h₁) ≪≫
        pullbackFiberIso g h₂ := by
  refine Iso.ext (NatTrans.ext (funext fun A ↦ ?_))
  rw [← pullbackFiberIso_comp_hom_app f g h₁ h₂ h A]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  rfl

/-- Base point changes compose (geometric points with different fields). -/
lemma fiberIsoMap_trans (f : Y ⟶ X) {q : Spec (.of Ω) ⟶ Y} {q' : Spec (.of Ω') ⟶ Y}
    {q'' : Spec (.of Ω'') ⟶ Y} {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X}
    {η'' : Spec (.of Ω'') ⟶ X} (h : q ≫ f = η) (h' : q' ≫ f = η') (h'' : q'' ≫ f = η'')
    (α : fiber q ≅ fiber q') (β : fiber q' ≅ fiber q'') :
    fiberIsoMap f h h'' (α ≪≫ β) = fiberIsoMap f h h' α ≪≫ fiberIsoMap f h' h'' β := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- Base point changes commute with inverses (geometric points with different fields). -/
lemma fiberIsoMap_symm (f : Y ⟶ X) {q : Spec (.of Ω) ⟶ Y} {q' : Spec (.of Ω') ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X} (h : q ≫ f = η) (h' : q' ≫ f = η')
    (α : fiber q ≅ fiber q') :
    fiberIsoMap f h' h α.symm = (fiberIsoMap f h h' α).symm := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- `fiberIsoMap` of the identification of the fibres at equal geometric points. -/
lemma fiberIsoMap_eqToIso (f : Y ⟶ X) {q q' : Spec (.of Ω) ⟶ Y} (hq : q = q')
    {η η' : Spec (.of Ω) ⟶ X} (h : q ≫ f = η) (h' : q' ≫ f = η') (hη : η = η') :
    fiberIsoMap f h h' (eqToIso (congrArg fiber hq)) = eqToIso (congrArg fiber hη) := by
  subst hq h h'
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- `fiberIsoMap` only depends on the morphism (geometric points with different fields). -/
lemma fiberIsoMap_congr {f f' : Y ⟶ X} (hf : f = f') {q : Spec (.of Ω) ⟶ Y}
    {q' : Spec (.of Ω') ⟶ Y} {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X} (h : q ≫ f = η)
    (h' : q' ≫ f = η') (k : q ≫ f' = η) (k' : q' ≫ f' = η') (α : fiber q ≅ fiber q') :
    fiberIsoMap f h h' α = fiberIsoMap f' k k' α := by
  subst hf
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Base point changes along a composite** (geometric points with different fields):
`g_*(f_* α) = (f ≫ g)_* α`. -/
lemma fiberIsoMap_fiberIsoMap (f : Y ⟶ X) (g : X ⟶ W)
    {q : Spec (.of Ω) ⟶ Y} {q' : Spec (.of Ω') ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    {η' : Spec (.of Ω') ⟶ X} {ζ : Spec (.of Ω) ⟶ W} {ζ' : Spec (.of Ω') ⟶ W}
    (h₁ : q ≫ f = η) (h₁' : q' ≫ f = η') (h₂ : η ≫ g = ζ) (h₂' : η' ≫ g = ζ')
    (h : q ≫ f ≫ g = ζ) (h' : q' ≫ f ≫ g = ζ') (α : fiber q ≅ fiber q') :
    fiberIsoMap g h₂ h₂' (fiberIsoMap f h₁ h₁' α) = fiberIsoMap (f ≫ g) h h' α := by
  simp only [fiberIsoMap]
  rw [pullbackFiberIso_comp f g h₁ h₂ h, pullbackFiberIso_comp f g h₁' h₂' h',
    transportIso_isoWhiskerRight, transportIso_transportIso]

/-- The trivial base point change maps to the trivial one. -/
lemma fiberIsoMap_refl (f : Y ⟶ X) {q : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    (h : q ≫ f = η) : fiberIsoMap f h h (Iso.refl (fiber q)) = Iso.refl _ := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- **`fundamentalGroupMap` is a base point change**: `f_* σ = fiberIsoMap f σ`. -/
lemma fundamentalGroupMap_eq_fiberIsoMap [IsSepClosed Ω] (f : Y ⟶ X) {q : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} (h : q ≫ f = η) (σ : π₁ᵉᵗ(q)) :
    (fundamentalGroupMap f h σ : fiber η ≅ fiber η) = fiberIsoMap f h h σ := by
  refine Iso.ext (NatTrans.ext (funext fun A ↦ FintypeCat.hom_ext _ _ fun z ↦ ?_))
  rw [fundamentalGroupMap_apply, fiberAutMap_hom_app_apply]
  rfl

end AlgebraicGeometry.FiniteEtale
