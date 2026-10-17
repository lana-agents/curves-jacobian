/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Presheaves on `Over S` as presheaves on the ambient category

This file is generic. For a presheaf `F` on `Over S`, `overSigma F` is the presheaf on the
ambient category given by `T ↦ Σ (g : T ⟶ S), F(T, g)`. This is how functors on `(Sch/S)`
(such as the Picard functor of Stacks, Chapter 44) are viewed as functors on all schemes, to
which representability criteria such as `AlgebraicGeometry.Scheme.LocalRepresentability` apply.
-/

open CategoryTheory Opposite

universe w v u

namespace CurvesJacobian

variable {C : Type u} [Category.{v} C] {S : C} (F : (Over S)ᵒᵖ ⥤ Type w)

lemma heq_map_homMk {T : C} {g₁ g₂ : T ⟶ S} (e : g₁ = g₂) {V : Over S} (a : T ⟶ V.left)
    (w₁ : a ≫ V.hom = g₁) (w₂ : a ≫ V.hom = g₂) (x : F.obj (op V)) :
    HEq (F.map (Over.homMk a w₁ : Over.mk g₁ ⟶ V).op x)
      (F.map (Over.homMk a w₂ : Over.mk g₂ ⟶ V).op x) := by
  subst e
  rfl

/-- The presheaf `T ↦ Σ (g : T ⟶ S), F(T, g)` on `C` attached to a presheaf `F` on `Over S`. -/
def overSigma : Cᵒᵖ ⥤ Type (max v w) where
  obj T := Σ g : T.unop ⟶ S, F.obj (op (Over.mk g))
  map {T T'} h := TypeCat.ofHom fun x ↦ ⟨h.unop ≫ x.1,
    F.map (Over.homMk h.unop rfl : Over.mk (h.unop ≫ x.1) ⟶ Over.mk x.1).op x.2⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨g, y⟩ := x
    refine Sigma.ext (Category.id_comp g) ?_
    refine (heq_map_homMk F (Category.id_comp g) _ rfl (Category.id_comp g) y).trans ?_
    have : (Over.homMk (𝟙 T.unop) (Category.id_comp g) : Over.mk g ⟶ Over.mk g) = 𝟙 _ :=
      rfl
    change HEq (F.map (Over.homMk (𝟙 T.unop) _ : Over.mk g ⟶ Over.mk g).op y) y
    rw [this, op_id, F.map_id]
    rfl
  map_comp h h' := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨g, y⟩ := x
    refine Sigma.ext (Category.assoc _ _ _) ?_
    refine (heq_map_homMk F (Category.assoc _ _ _) _ rfl (Category.assoc _ _ _) y).trans ?_
    have : (Over.homMk (h'.unop ≫ h.unop) (Category.assoc _ _ _) :
        Over.mk (h'.unop ≫ h.unop ≫ g) ⟶ Over.mk g) =
        (Over.homMk h'.unop rfl : Over.mk (h'.unop ≫ h.unop ≫ g) ⟶ Over.mk (h.unop ≫ g)) ≫
          (Over.homMk h.unop rfl : Over.mk (h.unop ≫ g) ⟶ Over.mk g) :=
      rfl
    change HEq (F.map (Over.homMk (h'.unop ≫ h.unop) _ :
      Over.mk (h'.unop ≫ h.unop ≫ g) ⟶ Over.mk g).op y) _
    rw [this, op_comp, F.map_comp]
    rfl

@[simp]
lemma overSigma_map_mk {T T' : C} (h : T' ⟶ T) (g : T ⟶ S) (y : F.obj (op (Over.mk g))) :
    (overSigma F).map h.op ⟨g, y⟩ =
      ⟨h ≫ g, F.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g).op y⟩ :=
  rfl

/-- Two elements of `overSigma F` over equal morphisms `g₁ = g₂` agree iff their second
components agree after transport. -/
lemma overSigma_mk_eq_iff {T : C} {g₁ g₂ : T ⟶ S} (e : g₁ = g₂) (y₁ : F.obj (op (Over.mk g₁)))
    (y₂ : F.obj (op (Over.mk g₂))) :
    (⟨g₁, y₁⟩ : (overSigma F).obj (op T)) = ⟨g₂, y₂⟩ ↔
      F.map (Over.homMk (𝟙 T) ((Category.id_comp _).trans e) :
        Over.mk g₂ ⟶ Over.mk g₁).op y₁ = y₂ := by
  subst e
  have : (Over.homMk (𝟙 T) (Category.id_comp _) : Over.mk g₁ ⟶ Over.mk g₁) = 𝟙 _ := rfl
  rw [this, op_id, F.map_id]
  exact ⟨fun h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2, fun h ↦ by subst h; rfl⟩

end CurvesJacobian
