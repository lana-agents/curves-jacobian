/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FieldChange
import CurvesJacobian.Cusp.BasePointChange

/-!
# Extending the field of a geometric point

For a geometric point `η : Spec Ω ⟶ X` of a connected scheme and an embedding `ι : Ω → Ω'` of
separably closed fields, the geometric point `η' = Spec ι ≫ η` has an isomorphic fibre functor:
`AlgebraicGeometry.FiniteEtale.fieldExtIso ι η : fiber η ≅ fiber (Spec ι ≫ η)`, a point
`x : Spec Ω ⟶ A` over `η` going to `Spec ι ≫ x` (this is a morphism of fibre functors, hence an
isomorphism). This generalises `AlgebraicGeometry.FiniteEtale.fieldChangeIso` (`ι` bijective).

Under the induced `π₁ᵉᵗ(η) ≃ₜ* π₁ᵉᵗ(η')`, the Galois action through a field-valued point
`j : Spec F ⟶ X` of `g ∈ Gal(Ω/F)` goes to the action through `j' : Spec F' ⟶ X` of any
`g' ∈ Gal(Ω'/F')` extending `g` (`galoisAction_fieldExt`), and inertia groups of a valuation ring
`W' ⊆ Ω'` go into inertia groups of `W' ∩ Ω` (`galInertia_le_map_fieldExt`).
-/

open CategoryTheory Limits PreGaloisCategory

universe u

noncomputable section

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category.{u} C] [GaloisCategory C] (F G : C ⥤ FintypeCat.{u})
  [FiberFunctor F] [FiberFunctor G]

/-- **Every morphism of fibre functors is an isomorphism.** -/
lemma isIso_of_fiberFunctor (f : F ⟶ G) : IsIso f := by
  obtain ⟨g⟩ := nonempty_hom_of_fiberFunctor G F
  haveI : IsIso (f ≫ g) := FibreFunctor.end_isIso F (f ≫ g)
  haveI : IsIso (g ≫ f) := FibreFunctor.end_isIso G (g ≫ f)
  have hr : f ≫ (g ≫ inv (f ≫ g)) = 𝟙 F := by
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hl : (inv (g ≫ f) ≫ g) ≫ f = 𝟙 G := by
    rw [Category.assoc, IsIso.inv_hom_id]
  have heq : inv (g ≫ f) ≫ g = g ≫ inv (f ≫ g) := by
    calc inv (g ≫ f) ≫ g = (inv (g ≫ f) ≫ g) ≫ f ≫ (g ≫ inv (f ≫ g)) := by
          rw [hr, Category.comp_id]
      _ = g ≫ inv (f ≫ g) := by rw [← Category.assoc, hl, Category.id_comp]
  exact ⟨⟨g ≫ inv (f ≫ g), hr, heq ▸ hl⟩⟩

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
  (ι : Ω →+* Ω') (η : Spec (.of Ω) ⟶ X)

/-- `Spec ι : Spec Ω' ⟶ Spec Ω`. -/
abbrev specHom : Spec (.of Ω') ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom ι)

/-- Points over `η` give points over `Spec ι ≫ η` (precomposition with `Spec ι`). -/
def overHomExt (A : FiniteEtale X) (y : Over.mk η ⟶ A.toComma) :
    Over.mk (specHom ι ≫ η) ⟶ A.toComma :=
  Over.homMk (specHom ι ≫ y.left) (by
    have h1 : y.left ≫ A.toComma.hom = η := Over.w y
    change (specHom ι ≫ y.left) ≫ A.toComma.hom = specHom ι ≫ η
    exact (Category.assoc _ _ _).trans (congrArg (specHom ι ≫ ·) h1))

/-- **The morphism of fibre functors** `fiber η ⟶ fiber (Spec ι ≫ η)`. -/
def fieldExtHom : fiber η ⟶ fiber (specHom ι ≫ η) where
  app A := FintypeCat.homMk fun x ↦
    (fiberObjEquivHom _ A).symm (overHomExt ι η A (fiberObjEquivHom η A x))
  naturality {A B} f := by
    ext x
    change (fiberObjEquivHom _ B).symm (overHomExt ι η B
        (fiberObjEquivHom η B ((fiber η).map f x))) =
      (fiber _).map f ((fiberObjEquivHom _ A).symm
        (overHomExt ι η A (fiberObjEquivHom η A x)))
    rw [fiberObjEquivHom_symm_naturality, ← fiberObjEquivHom_naturality]
    congr 1

lemma fieldExtHom_app (A : FiniteEtale X) (x : (fiber η).obj A) :
    (fiberObjEquivHom _ A ((fieldExtHom ι η).app A x)).left =
      specHom ι ≫ (fiberObjEquivHom η A x).left := by
  change (fiberObjEquivHom _ A ((fiberObjEquivHom _ A).symm
    (overHomExt ι η A (fiberObjEquivHom η A x)))).left = _
  rw [Equiv.apply_symm_apply]
  rfl

instance [ConnectedSpace X] : IsIso (fieldExtHom ι η) :=
  isIso_of_fiberFunctor _ _ _

/-- **Extending the field of a geometric point**: `fiber η ≅ fiber (Spec ι ≫ η)` for an
embedding `ι : Ω → Ω'` of separably closed fields (`X` connected). -/
def fieldExtIso [ConnectedSpace X] : fiber η ≅ fiber (specHom ι ≫ η) :=
  asIso (fieldExtHom ι η)

/-- `π₁ᵉᵗ(η) ≃ₜ* π₁ᵉᵗ(Spec ι ≫ η)`. -/
def fieldExtEquiv [ConnectedSpace X] : π₁ᵉᵗ(η) ≃ₜ* π₁ᵉᵗ(specHom ι ≫ η) :=
  autContinuousMulEquivOfIso (fieldExtIso ι η)

section Galois

variable [ConnectedSpace X] (F F' : Type u) [Field F] [Field F'] [Algebra F Ω] [Algebra F' Ω']
  [IsGalois F Ω] [IsGalois F' Ω'] (j : Spec (.of F) ⟶ X) (j' : Spec (.of F') ⟶ X)
  (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η)
  (h' : Spec.map (CommRingCat.ofHom (algebraMap F' Ω')) ≫ j' = specHom ι ≫ η)

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specHom_comp_specMap {g : Ω →+* Ω} {g' : Ω' →+* Ω'} (hg : ∀ z, ι (g z) = g' (ι z)) :
    specHom ι ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom g') ≫ specHom ι := by
  rw [specHom, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext z
  exact hg z

/-- **The Galois action under an extension of the field**: `g ∈ Gal(Ω/F)` acting through `j`
goes to `g' ∈ Gal(Ω'/F')` acting through `j'` if `ι ∘ g = g' ∘ ι`. -/
theorem galoisAction_fieldExt (g : Ω ≃ₐ[F] Ω) (g' : Ω' ≃ₐ[F'] Ω')
    (hg : ∀ z, ι (g z) = g' (ι z)) :
    fieldExtEquiv ι η (galoisAction F j h g) = galoisAction F' j' h' g' := by
  refine ext_of_hom_app_left fun A x' ↦ ?_
  rw [galoisAction_hom_app_left]
  set e := fieldExtIso ι η
  obtain ⟨x, rfl⟩ : ∃ x, e.hom.app A x = x' :=
    ⟨e.inv.app A x', FintypeCat.inv_hom_id_apply (e.app A) x'⟩
  change (fiberObjEquivHom _ A (e.hom.app A ((galoisAction F j h g).hom.app A
    (e.inv.app A (e.hom.app A x))))).left = _
  rw [show e.inv.app A (e.hom.app A x) = x from FintypeCat.hom_inv_id_apply (e.app A) x]
  change (fiberObjEquivHom _ A ((fieldExtHom ι η).app A ((galoisAction F j h g).hom.app A
    x))).left = Spec.map (CommRingCat.ofHom (g' : Ω' →+* Ω')) ≫
      (fiberObjEquivHom _ A ((fieldExtHom ι η).app A x)).left
  rw [fieldExtHom_app, fieldExtHom_app, galoisAction_hom_app_left, ← Category.assoc,
    specHom_comp_specMap ι (g := (g : Ω →+* Ω)) (g' := (g' : Ω' →+* Ω'))
    (fun z ↦ hg z), Category.assoc]

omit [IsSepClosed Ω] [IsSepClosed Ω'] [IsGalois F Ω] [IsGalois F' Ω'] [ConnectedSpace X] in
/-- Inertia restricts to inertia: if `ι ∘ g = g' ∘ ι` and `g'` is in the inertia group of
`W' ⊆ Ω'`, then `g` is in the inertia group of `ι⁻¹(W')`. -/
lemma mem_inertia_comap_of_mem {W' : ValuationSubring Ω'} {g : Ω ≃ₐ[F] Ω} {g' : Ω' ≃ₐ[F'] Ω'}
    (hg : ∀ z, ι (g z) = g' (ι z)) (hg' : g' ∈ GaloisPi1.inertia W') :
    g ∈ GaloisPi1.inertia (W'.comap ι) := by
  intro a ha
  have key : (W'.comap ι).valuation (g a - a) < 1 ↔ W'.valuation (ι (g a - a)) < 1 := by
    rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap, map_inv₀,
      map_eq_zero_iff ι ι.injective]
  rw [key, map_sub, hg]
  exact hg' _ ha

/-- **Inertia groups under an extension of the field**: the inertia subgroup of `W' ⊆ Ω'` (through
`j'`) is contained in the image of the inertia subgroup of `ι⁻¹(W') ⊆ Ω` (through `j`), given a
restriction `res : Gal(Ω'/F') → Gal(Ω/F)` with `ι ∘ res g' = g' ∘ ι`. -/
theorem galInertia_le_map_fieldExt (res : (Ω' ≃ₐ[F'] Ω') → (Ω ≃ₐ[F] Ω))
    (hres : ∀ g' z, ι (res g' z) = g' (ι z)) (W' : ValuationSubring Ω') :
    galInertia (specHom ι ≫ η) F' j' h' W' ≤
      (galInertia η F j h (W'.comap ι)).map (fieldExtEquiv ι η).toMulEquiv.toMonoidHom := by
  rw [galInertia, Subgroup.closure_le]
  rintro _ ⟨g', hg', rfl⟩
  rw [← galoisAction_fieldExt ι η F F' j j' h h' (res g') g' (hres g')]
  exact ⟨_, Subgroup.subset_closure ⟨res g', mem_inertia_comap_of_mem ι F F' (hres g') hg', rfl⟩,
    rfl⟩

end Galois

/-- `fieldExtIso` is compatible with `f : Y ⟶ X`: the transported isomorphism is `fieldExtIso`. -/
lemma fiberIsoMap_fieldExtIso {Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h' : (specHom ι ≫ y) ≫ f = specHom ι ≫ (y ≫ f)) :
    fiberIsoMap f rfl h' (fieldExtIso ι y) = fieldExtIso ι (y ≫ f) := by
  refine Iso.ext (NatTrans.ext (funext fun A ↦ FintypeCat.hom_ext _ _ fun x ↦ ?_))
  refine (fiberObjEquivHom _ A).injective (Over.OverMorphism.ext ?_)
  change (fiberObjEquivHom _ A ((pullbackFiberIso f h').hom.app A ((fieldExtIso ι y).hom.app
    ((pullback f).obj A) ((pullbackFiberIso f rfl).inv.app A x)))).left =
      (fiberObjEquivHom _ A ((fieldExtHom ι (y ≫ f)).app A x)).left
  rw [pullbackFiberIso_hom_app_left, fieldExtIso]
  change (fiberObjEquivHom _ _ ((fieldExtHom ι y).app ((pullback f).obj A)
    ((pullbackFiberIso f rfl).inv.app A x))).left ≫ _ = _
  have key := pullbackFiberIso_hom_app_left f (rfl : y ≫ f = y ≫ f) A
    ((pullbackFiberIso f rfl).inv.app A x)
  rw [show (pullbackFiberIso f rfl).hom.app A ((pullbackFiberIso f rfl).inv.app A x) = x from
    FintypeCat.inv_hom_id_apply ((pullbackFiberIso f rfl).app A) x] at key
  rw [fieldExtHom_app, fieldExtHom_app, key]
  exact Category.assoc _ _ _

/-- **Naturality of `fieldExtEquiv`** along `f : Y ⟶ X`. -/
lemma fundamentalGroupMap_fieldExtEquiv {Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h' : (specHom ι ≫ y) ≫ f = specHom ι ≫ (y ≫ f))
    (γ : π₁ᵉᵗ(y)) :
    fundamentalGroupMap f h' (fieldExtEquiv ι y γ) =
      fieldExtEquiv ι (y ≫ f) (fundamentalGroupMap f rfl γ) := by
  rw [fieldExtEquiv, fundamentalGroupMap_autContinuousMulEquivOfIso f rfl h',
    fiberIsoMap_fieldExtIso ι f y h']
  rfl

end AlgebraicGeometry.FiniteEtale
