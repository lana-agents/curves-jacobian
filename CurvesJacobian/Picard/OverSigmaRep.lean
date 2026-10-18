/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.OverSigma
import Mathlib.CategoryTheory.Yoneda

/-!
# Representability of `overSigma F` and of `F`

This file is generic. Let `F` be a presheaf on `Over S`. If the presheaf
`overSigma F : T ↦ Σ (g : T ⟶ S), F(T, g)` on the ambient category is represented by `X`, then
the first component of the universal element is a morphism `X ⟶ S`, and `F` itself is
represented by `X` as an object of `Over S` (`CurvesJacobian.OverSigmaRep.representableBy`).
This is how a scheme representing the Picard functor viewed on all schemes becomes a scheme over
the base representing the Picard functor on `(Sch/S)`.
-/

open CategoryTheory Opposite

universe v u

namespace CurvesJacobian

/-- The element of `overSigma F` over `T'.left` attached to the pullback of `y ∈ F(T)` along
`a : T' ⟶ T` is the pullback of `⟨T.hom, y⟩` along `a.left`. -/
lemma overSigma_mk_map {C : Type u} [Category.{v} C] {S : C} (F : (Over S)ᵒᵖ ⥤ Type v)
    {T T' : Over S} (a : T' ⟶ T) (y : F.obj (op T)) :
    (⟨T'.hom, F.map a.op y⟩ : (overSigma F).obj (op T'.left)) =
      (overSigma F).map a.left.op ⟨T.hom, y⟩ := by
  refine Eq.trans ?_ (overSigma_map_mk F a.left T.hom y).symm
  refine (overSigma_mk_eq_iff F (Over.w a).symm _ _).mpr ?_
  refine (Functor.map_comp_apply F _ _ _).symm.trans ?_
  exact congrArg (fun φ : Over.mk (a.left ≫ T.hom) ⟶ T ↦ F.map φ.op y)
    (Over.OverMorphism.ext (Category.id_comp _))

namespace OverSigmaRep

variable {C : Type u} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v} {X : C}
  (e : (overSigma F).RepresentableBy X)

/-- The structure morphism `X ⟶ S`: the first component of the universal element. -/
def base : X ⟶ S := (e.homEquiv (𝟙 X)).1

/-- `X` as an object of `Over S`. -/
abbrev over : Over S where
  left := X
  right := ⟨⟨⟩⟩
  hom := base e

/-- The universal element of `F`. -/
def univ : F.obj (op (over e)) := (e.homEquiv (𝟙 X)).2

lemma homEquiv_eq {T : C} (h : T ⟶ X) :
    e.homEquiv h = (overSigma F).map h.op ⟨base e, univ e⟩ := by
  have := e.homEquiv_comp h (𝟙 X)
  rw [Category.comp_id] at this
  exact this

lemma homEquiv_eq_mk {T : C} (h : T ⟶ X) :
    e.homEquiv h = ⟨h ≫ base e,
      F.map (Over.homMk h rfl : Over.mk (h ≫ base e) ⟶ over e).op (univ e)⟩ :=
  homEquiv_eq e h

lemma homEquiv_symm_comp_base (Y : Over S) (y : F.obj (op Y)) :
    e.homEquiv.symm ⟨Y.hom, y⟩ ≫ base e = Y.hom := by
  have h := homEquiv_eq_mk e (e.homEquiv.symm ⟨Y.hom, y⟩)
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg Sigma.fst h).symm

lemma map_homMk_homEquiv_symm (Y : Over S) (y : F.obj (op Y)) :
    F.map (Over.homMk (e.homEquiv.symm ⟨Y.hom, y⟩) (homEquiv_symm_comp_base e Y y) :
      Y ⟶ over e).op (univ e) = y := by
  have h := homEquiv_eq_mk e (e.homEquiv.symm ⟨Y.hom, y⟩)
  rw [Equiv.apply_symm_apply] at h
  have h' := (overSigma_mk_eq_iff F (homEquiv_symm_comp_base e Y y) _ _).mp h.symm
  refine Eq.trans ?_ ((Functor.map_comp_apply F _ _ _).trans h')
  exact congrArg (fun φ : Y ⟶ over e ↦ F.map φ.op (univ e))
    (Over.OverMorphism.ext (Category.id_comp _).symm)

/-- **`F` is represented by `X` over `S`.** -/
def representableBy : F.RepresentableBy (over e) where
  homEquiv {Y} :=
    { toFun a := F.map a.op (univ e)
      invFun y := Over.homMk (e.homEquiv.symm ⟨Y.hom, y⟩) (homEquiv_symm_comp_base e Y y)
      left_inv a := by
        apply Over.OverMorphism.ext
        change e.homEquiv.symm ⟨Y.hom, F.map a.op (univ e)⟩ = a.left
        rw [Equiv.symm_apply_eq, homEquiv_eq_mk]
        refine ((overSigma_mk_eq_iff F (Over.w a) _ _).mpr ?_).symm
        refine (Functor.map_comp_apply F _ _ _).symm.trans ?_
        exact congrArg (fun φ : Y ⟶ over e ↦ F.map φ.op (univ e))
          (Over.OverMorphism.ext (Category.id_comp _))
      right_inv y := map_homMk_homEquiv_symm e Y y }
  homEquiv_comp f a := Functor.map_comp_apply F a.op f.op (univ e)

lemma representableBy_homEquiv {Y : Over S} (a : Y ⟶ over e) :
    (representableBy e).homEquiv a = F.map a.op (univ e) := rfl

/-- The element of `overSigma F` attached to a morphism over `S` is the pullback of the
universal element. -/
lemma mk_representableBy_homEquiv {Y : Over S} (a : Y ⟶ over e) :
    (⟨Y.hom, (representableBy e).homEquiv a⟩ : (overSigma F).obj (op Y.left)) =
      (overSigma F).map a.left.op ⟨base e, univ e⟩ :=
  overSigma_mk_map F a (univ e)

end OverSigmaRep

end CurvesJacobian
