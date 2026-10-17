/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.OverSigma
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The Zariski sheaf condition for `overSigma F`

This file is generic. For a presheaf `F` on `Over S` (`S` a scheme), the presheaf
`overSigma F : T ↦ Σ (g : T ⟶ S), F(T, g)` on all schemes is a Zariski sheaf as soon as `F`
satisfies the sheaf condition for open covers of objects of `Over S`
(`isSheaf_overSigma`): the structure morphisms glue because schemes form a Zariski sheaf
(`Scheme.Cover.glueMorphisms`). The compatibility on overlaps is phrased with the single object
`U_a ×_T U_b ⟶ S` (through `U_a`) and the morphisms `fst`, `snd` to `U_a`, `U_b` over `S`
(`IsSheafOver`).

This reduces the Zariski sheaf property of `Pic_{X/S,σ}` (`CurvesJacobian.picSigmaSch`) and of
similar functors on `(Sch/S)` to a statement about a fixed `g : T ⟶ S`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe v u

namespace CurvesJacobian

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)

/-- The sheaf condition for `F` with respect to an open cover `𝓤` of `T` over `g : T ⟶ S`. -/
def IsSheafOver : Prop :=
  ∀ (T : Scheme.{u}) (g : T ⟶ S) (𝓤 : Scheme.OpenCover.{v} T)
    (y : ∀ a, F.obj (op (Over.mk (𝓤.f a ≫ g)))),
    (∀ a b, F.map (Over.homMk (pullback.fst (𝓤.f a) (𝓤.f b)) rfl :
        Over.mk (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a ≫ g) ⟶ Over.mk (𝓤.f a ≫ g)).op (y a) =
      F.map (Over.homMk (pullback.snd (𝓤.f a) (𝓤.f b))
          (by exact (pullback.condition_assoc g).symm) :
        Over.mk (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a ≫ g) ⟶ Over.mk (𝓤.f b ≫ g)).op (y b)) →
    ∃! z : F.obj (op (Over.mk g)),
      ∀ a, F.map (Over.homMk (𝓤.f a) rfl : Over.mk (𝓤.f a ≫ g) ⟶ Over.mk g).op z = y a

lemma map_homMk_id_map {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (e : g₁ = g₂) {V : Over S}
    (a : T ⟶ V.left) (w : a ≫ V.hom = g₂) (x : F.obj (op V)) :
    F.map (Over.homMk (𝟙 T) ((Category.id_comp _).trans e.symm) :
        Over.mk g₁ ⟶ Over.mk g₂).op (F.map (Over.homMk a w : Over.mk g₂ ⟶ V).op x) =
      F.map (Over.homMk a (w.trans e.symm) : Over.mk g₁ ⟶ V).op x := by
  have : (Over.homMk (𝟙 T) ((Category.id_comp _).trans e.symm) : Over.mk g₁ ⟶ Over.mk g₂) ≫
      (Over.homMk a w : Over.mk g₂ ⟶ V) = Over.homMk a (w.trans e.symm) := by
    ext
    exact Category.id_comp a
  rw [← this, op_comp, Functor.map_comp_apply]

variable {F}

/-- The sheaf condition of `overSigma F` for an open cover. -/
lemma isSheafFor_overSigma (hF : IsSheafOver.{v} F) {T : Scheme.{u}}
    (𝓤 : Scheme.OpenCover.{v} T) :
    Presieve.IsSheafFor (overSigma F) (Presieve.ofArrows 𝓤.X 𝓤.f) := by
  intro x hx
  let g₀ : ∀ i, 𝓤.X i ⟶ S := fun i ↦ (x (𝓤.f i) (.mk i)).1
  have hg₀ : ∀ i j, pullback.fst (𝓤.f i) (𝓤.f j) ≫ g₀ i = pullback.snd _ _ ≫ g₀ j :=
    fun i j ↦ congrArg Sigma.fst (hx (pullback.fst (𝓤.f i) (𝓤.f j)) (pullback.snd _ _)
      (.mk i) (.mk j) pullback.condition)
  let g : T ⟶ S := 𝓤.glueMorphisms g₀ hg₀
  have hg : ∀ i, 𝓤.f i ≫ g = g₀ i := 𝓤.ι_glueMorphisms g₀ hg₀
  let y : ∀ i, F.obj (op (Over.mk (𝓤.f i ≫ g))) := fun i ↦
    F.map (Over.homMk (𝟙 _) ((Category.id_comp _).trans (hg i).symm) :
      Over.mk (𝓤.f i ≫ g) ⟶ Over.mk (g₀ i)).op (x (𝓤.f i) (.mk i)).2
  have hxy : ∀ i, x (𝓤.f i) (.mk i) = ⟨𝓤.f i ≫ g, y i⟩ := fun i ↦
    (overSigma_mk_eq_iff F (hg i).symm _ _).2 rfl
  have hcompat : ∀ a b, F.map (Over.homMk (pullback.fst (𝓤.f a) (𝓤.f b)) rfl :
        Over.mk (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a ≫ g) ⟶ Over.mk (𝓤.f a ≫ g)).op (y a) =
      F.map (Over.homMk (pullback.snd (𝓤.f a) (𝓤.f b))
          (by exact (pullback.condition_assoc g).symm) :
        Over.mk (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a ≫ g) ⟶ Over.mk (𝓤.f b ≫ g)).op (y b) := by
    intro a b
    have h := hx (pullback.fst (𝓤.f a) (𝓤.f b)) (pullback.snd _ _) (.mk a) (.mk b)
      pullback.condition
    rw [hxy a, hxy b, overSigma_map_mk, overSigma_map_mk] at h
    have e : pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a ≫ g =
        pullback.snd (𝓤.f a) (𝓤.f b) ≫ 𝓤.f b ≫ g := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    have h' := (overSigma_mk_eq_iff F e _ _).1 h
    rw [← map_homMk_id_map F e (pullback.snd _ _) rfl (y b), ← h', map_homMk_id_map,
      map_homMk_id_map]
    all_goals first | rfl | exact e
  obtain ⟨z, hz, huniq⟩ := hF T g 𝓤 y hcompat
  refine ⟨⟨g, z⟩, ?_, ?_⟩
  · rintro _ _ ⟨i⟩
    rw [hxy i, overSigma_map_mk, hz i]
  · rintro ⟨g', z'⟩ ht
    have e : ∀ i, (⟨𝓤.f i ≫ g', F.map (Over.homMk (𝓤.f i) rfl :
        Over.mk (𝓤.f i ≫ g') ⟶ Over.mk g').op z'⟩ : (overSigma F).obj (op (𝓤.X i))) =
          ⟨𝓤.f i ≫ g, y i⟩ := fun i ↦ by
      rw [← overSigma_map_mk, ht _ (.mk i), hxy i]
    obtain rfl : g' = g := 𝓤.hom_ext _ _ fun i ↦ congrArg Sigma.fst (e i)
    refine congrArg (Sigma.mk g) (huniq z' fun i ↦ ?_)
    exact eq_of_heq (Sigma.mk.inj_iff.mp (e i)).2

/-- **`overSigma F` is a Zariski sheaf** if `F` satisfies the sheaf condition for open covers
over `S`. -/
theorem isSheaf_overSigma (hF : IsSheafOver.{u + 1} F) :
    Presieve.IsSheaf Scheme.zariskiTopology (overSigma F) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro T R hR
  obtain ⟨(𝓤 : Scheme.OpenCover T), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hR
  exact isSheafFor_overSigma hF 𝓤

end CurvesJacobian
