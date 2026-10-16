/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.MorphismProperty.CommaSites

/-!
# The multiplicative group `𝔾ₘ` on the étale site

* `CurvesJacobian.isSheaf_gammaType`: the presheaf `U ↦ Γ(U, 𝒪_U)` on `Scheme` is a sheaf for the
  (big) étale topology; it is represented by `Spec ℤ[T]` and the étale topology is subcanonical
  (it is coarser than the fpqc topology, Mathlib's `fpqcTopology.Subcanonical`).
* `CurvesJacobian.isSheaf_units`: the units of a sheaf of commutative rings form a sheaf.
* `CurvesJacobian.gmBig`: `U ↦ Γ(U, 𝒪_U)ˣ` (written additively), an étale sheaf of abelian
  groups on `Scheme` (`CurvesJacobian.isSheaf_gmBig`).
* `CurvesJacobian.etaleForget`: the functor from the small étale site `X.Etale` to `Scheme`; it is
  continuous (`X.smallEtaleTopology → etaleTopology`).
* `CurvesJacobian.Gm X : Sheaf X.smallEtaleTopology Ab`: the sheaf `𝔾ₘ` on the small étale site.
-/

open CategoryTheory Opposite Limits AlgebraicGeometry

namespace CurvesJacobian

universe u

instance etaleTopology_subcanonical : Scheme.etaleTopology.{u}.Subcanonical :=
  .of_le (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology)

/-- The type-valued presheaf `U ↦ Γ(U, ⊤)` on schemes. -/
abbrev gammaType : Scheme.{u}ᵒᵖ ⥤ Type u := Scheme.Γ ⋙ forget CommRingCat

/-- The ring `ℤ[T]` (as in `AffineSpace`). -/
noncomputable abbrev intPoly : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))

/-- `(U ⟶ Spec ℤ[T]) ≃ Γ(U, ⊤)`. -/
noncomputable def toSpecIntPolyEquiv (U : Scheme.{u}) : (U ⟶ Spec intPoly.{u}) ≃ Γ(U, ⊤) :=
  (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (X := U)).trans (Equiv.funUnique _ _)

/-- `Γ(-, ⊤)` is represented by `Spec ℤ[T]`. -/
noncomputable def gammaTypeIso : yoneda.obj (Spec intPoly.{u}) ≅ gammaType.{u} :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso (toSpecIntPolyEquiv U.unop))
    (by intro U V f; ext g; rfl)

lemma isSheaf_gammaType : Presheaf.IsSheaf Scheme.etaleTopology gammaType.{u} := by
  rw [← Presheaf.isSheaf_of_iso_iff gammaTypeIso, isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

section Units

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

/-- The presheaf of units of a presheaf of commutative rings, as a presheaf of types. -/
@[simps]
def unitsPresheaf (P : Cᵒᵖ ⥤ CommRingCat.{u}) : Cᵒᵖ ⥤ Type u where
  obj U := (P.obj U)ˣ
  map f := ↾fun u ↦ Units.map (P.map f).hom.toMonoidHom u
  map_id U := by ext u; simp
  map_comp f g := by ext u; simp

/-- **The units of a sheaf of commutative rings form a sheaf.** -/
theorem isSheaf_units (P : Cᵒᵖ ⥤ CommRingCat.{u})
    (hP : Presieve.IsSheaf J (P ⋙ forget CommRingCat)) :
    Presieve.IsSheaf J (unitsPresheaf P) := by
  intro X S hS x hx
  have hsh := hP S hS
  let xu : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S.arrows f → (P.obj (op Y))ˣ := fun _ f hf ↦ x f hf
  have hxu : ∀ ⦃Y₁ Y₂ Z : C⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
      (h₁ : S.arrows f₁) (h₂ : S.arrows f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
      Units.map (P.map g₁.op).hom.toMonoidHom (xu f₁ h₁) =
        Units.map (P.map g₂.op).hom.toMonoidHom (xu f₂ h₂) :=
    fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w ↦ hx g₁ g₂ h₁ h₂ w
  -- the families of values and of inverses
  let xv : Presieve.FamilyOfElements (P ⋙ forget CommRingCat) S.arrows :=
    fun _ f hf ↦ ((xu f hf : (P.obj (op _))ˣ) : P.obj (op _))
  let xi : Presieve.FamilyOfElements (P ⋙ forget CommRingCat) S.arrows :=
    fun _ f hf ↦ (((xu f hf)⁻¹ : (P.obj (op _))ˣ) : P.obj (op _))
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact congrArg Units.val (hxu g₁ g₂ f₁ f₂ h₁ h₂ w)
  have hxi : xi.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have := congrArg (fun v : (P.obj (op Z))ˣ ↦ ((v⁻¹ : (P.obj (op Z))ˣ) : P.obj (op Z)))
      (hxu g₁ g₂ f₁ f₂ h₁ h₂ w)
    simp only [← map_inv] at this
    exact this
  let a : P.obj (op X) := hsh.amalgamate xv hxv
  let b : P.obj (op X) := hsh.amalgamate xi hxi
  have ha : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : S.arrows f),
      (P.map f.op).hom a = (xu f hf : P.obj (op Y)) := fun _ f hf ↦ hsh.isAmalgamation hxv f hf
  have hb : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : S.arrows f),
      (P.map f.op).hom b = ((xu f hf)⁻¹ : (P.obj (op Y))ˣ) :=
    fun _ f hf ↦ hsh.isAmalgamation hxi f hf
  have hsep : ∀ t₁ t₂ : P.obj (op X),
      (∀ ⦃Y : C⦄ (f : Y ⟶ X), S.arrows f → (P.map f.op).hom t₁ = (P.map f.op).hom t₂) →
        t₁ = t₂ := fun t₁ t₂ h ↦ hsh.isSeparatedFor.ext h
  have hab : a * b = 1 := by
    refine hsep _ _ fun Y f hf ↦ ?_
    rw [map_mul, map_one, ha f hf, hb f hf]
    exact (xu f hf).mul_inv
  refine ⟨(⟨a, b, hab, by rw [mul_comm]; exact hab⟩ : (P.obj (op X))ˣ), fun Y f hf ↦ ?_, ?_⟩
  · change Units.map (P.map f.op).hom.toMonoidHom _ = xu f hf
    exact Units.ext (ha f hf)
  · intro u hu
    have hu' : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : S.arrows f),
        Units.map (P.map f.op).hom.toMonoidHom (u : (P.obj (op X))ˣ) = xu f hf :=
      fun _ f hf ↦ hu f hf
    refine Units.ext (hsep _ _ fun Y f hf ↦ ?_)
    rw [ha f hf]
    exact congrArg Units.val (hu' f hf)

end Units

/-- `𝔾ₘ` on the big site: `U ↦ Γ(U, ⊤)ˣ`, written additively. -/
@[simps]
noncomputable def gmBig : Scheme.{u}ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (Additive (Γ(U.unop, ⊤))ˣ)
  map f := AddCommGrpCat.ofHom (MonoidHom.toAdditive (Units.map (Scheme.Γ.map f).hom.toMonoidHom))
  map_id U := by
    ext u
    exact Units.ext (congrArg (fun φ : Γ(U.unop, ⊤) ⟶ Γ(U.unop, ⊤) ↦
      φ.hom (Additive.toMul u : (Γ(U.unop, ⊤))ˣ).val) (Scheme.Γ.map_id U))
  map_comp f g := by
    ext u
    exact Units.ext (congrArg (fun φ ↦ φ.hom (Additive.toMul u : (Γ(_, ⊤))ˣ).val)
      (Scheme.Γ.map_comp f g))

/-- **`𝔾ₘ` is a sheaf for the étale topology.** -/
theorem isSheaf_gmBig : Presheaf.IsSheaf Scheme.etaleTopology gmBig.{u} := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  rw [isSheaf_iff_isSheaf_of_type]
  have h := isSheaf_units Scheme.etaleTopology Scheme.Γ
    ((isSheaf_iff_isSheaf_of_type _ _).1 isSheaf_gammaType)
  exact h

/-- The functor from the small étale site to schemes. -/
abbrev etaleForget (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

instance (X : Scheme.{u}) :
    (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology (Scheme.etaleTopology.over X) := by
  have H : Scheme.precoverage @Etale ≤ MorphismProperty.precoverage @Etale := inf_le_right
  have h := MorphismProperty.isContinuous_comap_forget (P := @Etale) (S := X)
    (Scheme.precoverage @Etale) H
  rw [MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _ H] at h
  exact h

instance (X : Scheme.{u}) :
    (etaleForget X).IsContinuous X.smallEtaleTopology Scheme.etaleTopology :=
  Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over X) _

/-- **`𝔾ₘ` on the small étale site** of `X`. -/
noncomputable def Gm (X : Scheme.{u}) : Sheaf X.smallEtaleTopology Ab.{u} :=
  ⟨(etaleForget X).op ⋙ gmBig, (etaleForget X).op_comp_isSheaf_of_isSheaf _ _ _ isSheaf_gmBig⟩

end CurvesJacobian
