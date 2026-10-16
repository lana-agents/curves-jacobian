/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.Algebra.Colimit.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.AlgebraicGeometry.Modules.Sheaf


/-!
# The tensor product of sheaves of modules on a scheme

Mathlib has the (objectwise) monoidal structure on presheaves of modules over a presheaf of
commutative rings, and the sheafification functor from presheaves of modules to sheaves of
modules, which is a localization with respect to the class `W` of morphisms whose underlying
morphism of abelian presheaves is locally bijective. We show that `W` is stable under tensoring
with an arbitrary presheaf of modules (`PresheafOfModules.isMonoidal_W`); Mathlib's localization
machinery (`LocalizedMonoidal`) then gives a symmetric monoidal structure on `X.Modules` for a
scheme `X` (`AlgebraicGeometry.Scheme.Modules.monoidalCategory`), for which sheafification is a
monoidal functor. The tensor product `M ⊗ N` is the sheafification of the presheaf
`U ↦ M(U) ⊗_{𝒪(U)} N(U)` (Stacks, Tag 01CA for ringed spaces).

The key algebraic input (`isLocallyInjective_whiskerRight`) is that tensoring with `Q` preserves
locally injective + locally surjective morphisms: local surjectivity is clear on pure tensors;
for local injectivity we factor `f` through its image, use right exactness of `⊗` for the
surjective part, and for the injective part the fact that a relation in `M' ⊗ Q` already holds in
`N' ⊗ Q` for a finitely generated `N' ⊆ M'` (Mathlib's
`Submodule.FG.exists_rTensor_fg_inclusion_eq`), whose finitely many generators lie locally in
the image.
-/

open CategoryTheory MonoidalCategory Limits Opposite
open scoped TensorProduct

universe v₁ u₁ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable {P P' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  (Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- An element of `P.obj U`, seen as a section of the underlying abelian presheaf. -/
abbrev el {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} {U : Cᵒᵖ}
    (x : M.obj U) : ToType (((toPresheaf _).obj M).obj U) := x

/-- An element of `P.obj U ⊗ Q.obj U`, seen as a section of `P ⊗ Q`. -/
abbrev elT {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} {U : Cᵒᵖ}
    (x : M.obj U ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj U] N.obj U) :
    ToType (((toPresheaf _).obj (M ⊗ N)).obj U) := x

section Elements

variable (f : P ⟶ P')

lemma tensor_map_tmul {U V : Cᵒᵖ} (g : U ⟶ V) (p : P.obj U) (q : Q.obj U) :
    ((toPresheaf _).obj (P ⊗ Q)).map g (elT (p ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj U] q)) =
      elT (P.map g p ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj V] Q.map g q) := rfl

lemma whiskerRight_app_tmul (U : Cᵒᵖ) (p : P.obj U) (q : Q.obj U) :
    ((toPresheaf _).map (f ▷ Q)).app U (elT (p ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj U] q)) =
      elT (f.app U p ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj U] q) := rfl

lemma toPresheaf_map_apply {U V : Cᵒᵖ} (g : U ⟶ V) (p : P.obj U) :
    ((toPresheaf _).obj P).map g (el p) = el (P.map g p) := rfl

lemma toPresheaf_app_apply (U : Cᵒᵖ) (p : P.obj U) :
    ((toPresheaf _).map f).app U (el p) = el (f.app U p) := rfl

end Elements


section Covering

/-- A finite family of covering sieves has a common covering refinement. -/
lemma exists_covering_forall_finset {X : C} {ι : Type*} (S : Finset ι) (F : ι → Sieve X)
    (h : ∀ i ∈ S, F i ∈ J X) :
    ∃ T ∈ J X, ∀ {Y : C} (g : Y ⟶ X), T g → ∀ i ∈ S, F i g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, J.top_mem X, fun _ _ _ ↦ by simp⟩
  | insert a S ha ih =>
    obtain ⟨T, hT, hT'⟩ := ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    refine ⟨T ⊓ F a, J.intersection_covering hT (h a (Finset.mem_insert_self a S)), ?_⟩
    rintro Y g ⟨hg₁, hg₂⟩ i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg₂
    · exact hT' g hg₁ i hi

end Covering

lemma isLocallyInjective_iff_of_additive {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : F ⟶ G) :
    Presheaf.IsLocallyInjective J φ ↔ ∀ (U : Cᵒᵖ) (x : ToType (F.obj U)), φ.app U x = 0 →
      Presheaf.equalizerSieve x 0 ∈ J U.unop := by
  constructor
  · intro h U x hx
    exact Presheaf.equalizerSieve_mem J φ x 0 (by rw [hx, map_zero])
  · intro h
    refine ⟨fun {U} x y hxy ↦ ?_⟩
    have := h U (x - y) (by rw [map_sub, hxy, sub_self])
    convert this using 1
    ext V g
    simp only [Presheaf.equalizerSieve_apply, map_sub, map_zero, sub_eq_zero]

section Surjective

variable (f : P ⟶ P')

lemma isLocallySurjective_whiskerRight
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)] :
    Presheaf.IsLocallySurjective J ((toPresheaf _).map (f ▷ Q)) where
  imageSieve_mem {U} s := by
    obtain ⟨t, rfl⟩ : ∃ t : P'.obj (op U) ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj (op U)]
      Q.obj (op U), elT t = s := ⟨s, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero =>
      apply J.superset_covering _ (J.top_mem U)
      intro V g _
      exact ⟨0, by rw [map_zero]; exact (map_zero _).symm⟩
    | tmul p' q =>
      apply J.superset_covering _
        (Presheaf.imageSieve_mem J ((toPresheaf _).map f) (el (U := op U) p'))
      rintro V g ⟨p, hp⟩
      refine ⟨elT (U := op V) ((show P.obj (op V) from p) ⊗ₜ
        (show Q.obj (op V) from Q.map g.op q)), ?_⟩
      change f.app _ p = P'.map g.op p' at hp
      change elT (U := op V) ((show P'.obj (op V) from f.app _ p) ⊗ₜ
        (show Q.obj (op V) from Q.map g.op q)) =
        elT (U := op V) ((show P'.obj (op V) from P'.map g.op p') ⊗ₜ
        (show Q.obj (op V) from Q.map g.op q))
      rw [hp]
    | add a b ha hb =>
      apply J.superset_covering _ (J.intersection_covering ha hb)
      rintro V g ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      refine ⟨x + y, ?_⟩
      rw [map_add, hx, hy]
      exact (map_add _ _ _).symm

end Surjective

section Image

variable (f : P ⟶ P')

/-- The image of a morphism of presheaves of modules, as a subpresheaf. -/
noncomputable def imageSub : P'.Submodule where
  obj U := LinearMap.range (f.app U).hom
  map {U V} g := by
    rintro _ ⟨x, rfl⟩
    exact ⟨P.map g x, naturality_apply f g x⟩

/-- The corestriction of `f` to its image. -/
noncomputable def toImageSub : P ⟶ (imageSub f).toPresheafOfModules where
  app U := ModuleCat.ofHom (f.app U).hom.rangeRestrict
  naturality {U V} g := by
    ext x
    exact Subtype.ext (naturality_apply f g x)

lemma toImageSub_ι : toImageSub f ≫ (imageSub f).ι = f := rfl

end Image

section Injective

variable (f : P ⟶ P')

lemma isLocallyInjective_whiskerRight_toImageSub
    [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)] :
    Presheaf.IsLocallyInjective J ((toPresheaf _).map (toImageSub f ▷ Q)) := by
  rw [isLocallyInjective_iff_of_additive]
  intro U x hx
  obtain ⟨x, rfl⟩ : ∃ t : P.obj U ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj U] Q.obj U,
    elT t = x := ⟨x, rfl⟩
  change ((f.app U).hom.rangeRestrict.rTensor (Q.obj U)) x = 0 at hx
  have hex := rTensor_exact (Q.obj U) (f.app U).hom.rangeRestrict.exact_subtype_ker_map
    (f.app U).hom.surjective_rangeRestrict
  obtain ⟨y, rfl⟩ := (hex x).mp hx
  clear hx hex
  induction y using TensorProduct.induction_on with
  | zero =>
    apply J.superset_covering _ (J.top_mem U.unop)
    intro V g _
    exact map_zero _
  | tmul k q =>
    have hk : f.app U k.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp k.2)
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J ((toPresheaf _).map f) (el k.1)
      (el 0) (by rw [toPresheaf_app_apply, toPresheaf_app_apply, hk, map_zero]))
    intro V g hg
    simp only [Presheaf.equalizerSieve_apply, map_zero] at hg ⊢
    have hk' : (P.map g.op k.1 : P.obj (op V)) = 0 := hg.trans (map_zero _)
    change elT (U := op V) (M := P) (N := Q) ((P.map g.op k.1 : P.obj (op V)) ⊗ₜ[
      (R ⋙ forget₂ CommRingCat RingCat).obj (op V)] (Q.map g.op q : Q.obj (op V))) = 0
    rw [hk']
    exact TensorProduct.zero_tmul _ _
  | add a b ha hb =>
    apply J.superset_covering _ (J.intersection_covering ha hb)
    rintro V g ⟨ha', hb'⟩
    simp only [Presheaf.equalizerSieve_apply, map_zero] at ha' hb' ⊢
    rw [show elT (M := P) (N := Q)
        (LinearMap.rTensor (Q.obj U) (f.app U).hom.rangeRestrict.ker.subtype (a + b)) =
      elT (LinearMap.rTensor (Q.obj U) (f.app U).hom.rangeRestrict.ker.subtype a) +
      elT (LinearMap.rTensor (Q.obj U) (f.app U).hom.rangeRestrict.ker.subtype b) from
        map_add _ _ _]
    have := map_add (ConcreteCategory.hom (((toPresheaf _).obj (P ⊗ Q)).map g.op))
      (elT (LinearMap.rTensor (Q.obj U) (f.app U).hom.rangeRestrict.ker.subtype a))
      (elT (LinearMap.rTensor (Q.obj U) (f.app U).hom.rangeRestrict.ker.subtype b))
    rw [ha', hb', add_zero] at this
    exact this

lemma isLocallyInjective_whiskerRight_ι (N : P'.Submodule)
    (hN : ∀ (U : Cᵒᵖ) (y : P'.obj U), ∃ T ∈ J U.unop,
      ∀ {V : C} (g : V ⟶ U.unop), T g → P'.map g.op y ∈ N.obj (op V)) :
    Presheaf.IsLocallyInjective J ((toPresheaf _).map (N.ι ▷ Q)) := by
  rw [isLocallyInjective_iff_of_additive]
  intro U x hx
  obtain ⟨x, rfl⟩ : ∃ t : N.toPresheafOfModules.obj U ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj U]
    Q.obj U, elT t = x := ⟨x, rfl⟩
  change ((N.obj U).subtype.rTensor (Q.obj U)) x = 0 at hx
  obtain ⟨J₀, hJ₀, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype x
  let K : _root_.Submodule ((R ⋙ forget₂ CommRingCat RingCat).obj U) (P'.obj U) :=
    J₀.map (N.obj U).subtype
  have hK : K.FG := hJ₀.map _
  let e : J₀ →ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj U] K := (N.obj U).subtype.submoduleMap J₀
  have h0 : K.subtype.rTensor (Q.obj U) (e.rTensor (Q.obj U) y) =
      K.subtype.rTensor (Q.obj U) 0 := by
    rw [map_zero, ← hx, ← LinearMap.rTensor_comp_apply]
    erw [← LinearMap.rTensor_comp_apply]
    rfl
  obtain ⟨K', hK', hKK', hy⟩ := hK.exists_rTensor_fg_inclusion_eq h0
  rw [map_zero] at hy
  obtain ⟨S, hS⟩ := hK'
  choose T hT hT' using fun s : P'.obj U ↦ hN U s
  obtain ⟨T₀, hT₀, hT₀'⟩ :=
    exists_covering_forall_finset (J := J) S (fun s ↦ T s) (fun s _ ↦ hT s)
  apply J.superset_covering _ hT₀
  intro V g hg
  have hmem : ∀ k ∈ K', P'.map g.op k ∈ N.obj (op V) := by
    intro k hk
    rw [← hS] at hk
    induction hk using Submodule.span_induction with
    | mem s hs => exact hT' s g (hT₀' g hg s hs)
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r a _ ha =>
      have := P'.map_smul g.op r a
      erw [this]
      exact Submodule.smul_mem _ _ ha
  let ρ : K' →ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj U] (ModuleCat.restrictScalars
      ((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom).obj
        (N.toPresheafOfModules.obj (op V)) :=
    { toFun := fun k ↦ (⟨P'.map g.op k.1, hmem k.1 k.2⟩ : N.obj (op V))
      map_add' := fun a b ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun r a ↦ Subtype.ext (P'.map_smul g.op r a.1) }
  let bil : K' → Q.obj U →
      ↑(MonoidalCategory.tensorObj (N.toPresheafOfModules.obj (op V)) (Q.obj (op V))) :=
    fun k q ↦ (show N.toPresheafOfModules.obj (op V) from ρ k) ⊗ₜ[
      (R ⋙ forget₂ CommRingCat RingCat).obj (op V)] (show Q.obj (op V) from Q.map g.op q)
  let Φ : K' ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj U] Q.obj U →ₗ[
      (R ⋙ forget₂ CommRingCat RingCat).obj U]
      (ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom).obj
        (N.toPresheafOfModules.obj (op V) ⊗ Q.obj (op V)) :=
    TensorProduct.lift (LinearMap.mk₂ _ bil
      (fun a b q ↦ by simp only [bil]; rw [map_add]; exact TensorProduct.add_tmul _ _ _)
      (fun r a q ↦ by
        simp only [bil]; rw [map_smul]
        exact (TensorProduct.smul_tmul' (((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom r)
          (show N.toPresheafOfModules.obj (op V) from ρ a)
          (show Q.obj (op V) from Q.map g.op q)).symm)
      (fun a q q' ↦ by simp only [bil]; rw [map_add]; exact TensorProduct.tmul_add _ _ _)
      (fun r a q ↦ by
        simp only [bil]
        rw [map_smul]
        exact TensorProduct.tmul_smul (((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom r)
          (show N.toPresheafOfModules.obj (op V) from ρ a)
          (show Q.obj (op V) from Q.map g.op q)))
  have key : ∀ z : J₀ ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj U] Q.obj U,
      (N.toPresheafOfModules ⊗ Q).map g.op (J₀.subtype.rTensor (Q.obj U) z) =
        Φ ((K.inclusion hKK').rTensor (Q.obj U) (e.rTensor (Q.obj U) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact map_zero _
    | tmul j q =>
      simp only [LinearMap.rTensor_tmul]
      erw [Monoidal.tensorObj_map_tmul]
    | add a b ha hb =>
      simp only [map_add]
      rw [← ha, ← hb]
      exact map_add _ _ _
  simp only [Presheaf.equalizerSieve_apply, map_zero]
  change (N.toPresheafOfModules ⊗ Q).map g.op (J₀.subtype.rTensor (Q.obj U) y) = 0
  rw [key, hy, map_zero]
  rfl

end Injective

section Monoidal

variable (J) in
lemma isLocallyInjective_whiskerRight (f : P ⟶ P')
    [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)] :
    Presheaf.IsLocallyInjective J ((toPresheaf _).map (f ▷ Q)) := by
  have h1 := isLocallyInjective_whiskerRight_toImageSub (J := J) Q f
  have h2 := isLocallyInjective_whiskerRight_ι (J := J) Q (imageSub f) (fun U y ↦
    ⟨_, Presheaf.imageSieve_mem J ((toPresheaf _).map f) (el y), fun g ⟨x, hx⟩ ↦ ⟨x, hx⟩⟩)
  rw [← toImageSub_ι f, MonoidalCategory.comp_whiskerRight, Functor.map_comp]
  infer_instance

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify J AddCommGrpCat.{u}] in
lemma W_whiskerRight {f : P ⟶ P'} (hf : J.W ((toPresheaf _).map f)) :
    J.W ((toPresheaf _).map (f ▷ Q)) := by
  rw [J.W_iff_isLocallyBijective] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  exact ⟨isLocallyInjective_whiskerRight J Q f, isLocallySurjective_whiskerRight Q f⟩

instance isMonoidal_W :
    (J.W.inverseImage (toPresheaf (R ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerRight f hf Y := W_whiskerRight Y hf
  whiskerLeft X Y₁ Y₂ g hg := by
    have e : X ◁ g = (β_ X Y₁).hom ≫ (g ▷ X ≫ (β_ X Y₂).inv) := by
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality_right, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (MorphismProperty.RespectsIso.postcomp _ _ _ (W_whiskerRight X hg))

end Monoidal

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open PresheafOfModules

variable (X : Scheme.{u})

noncomputable instance : MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory
    (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

noncomputable instance : SymmetricCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (SymmetricCategory
    (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- The class of morphisms of presheaves of modules on `X` which become isomorphisms after
sheafification. -/
abbrev sheafificationW : MorphismProperty (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  (Opens.grothendieckTopology X).W.inverseImage
    (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

instance : (sheafificationW X).IsMonoidal :=
  inferInstanceAs (((Opens.grothendieckTopology X).W.inverseImage
    (_root_.PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat))).IsMonoidal)

/-- Sheafification of presheaves of modules on a scheme. -/
noncomputable abbrev sheafificationFunctor :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  PresheafOfModules.sheafification.{u} (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

instance : (sheafificationFunctor X).IsLocalization (sheafificationW X) := by
  unfold sheafificationFunctor sheafificationW
  infer_instance

/-- The symmetric monoidal structure on `X.Modules`: the tensor product is the sheafification
of the presheaf tensor product (obtained by localization). -/
noncomputable instance monoidalCategory : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal (sheafificationFunctor X)
    (sheafificationW X) (Iso.refl _)))

noncomputable instance symmetricCategory : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal (sheafificationFunctor X)
    (sheafificationW X) (Iso.refl _)))

/-- Sheafification of presheaves of modules, as a functor to `X.Modules`. -/
noncomputable def sheafify : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  sheafificationFunctor X

noncomputable instance : (sheafify X).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory (sheafificationFunctor X)
    (sheafificationW X) (Iso.refl _)).Monoidal

end AlgebraicGeometry.Scheme.Modules
