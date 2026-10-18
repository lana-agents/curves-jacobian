/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.OverSigmaSheaf

/-!
# The sheaf condition over `S` for small covers suffices

This file is generic. `CurvesJacobian.isSheaf_overSigma` asks for the sheaf condition
`IsSheafOver.{u + 1} F` for open covers indexed in the large universe `u + 1`. We show that the
sheaf condition for covers indexed in `Type u` implies it for covers indexed in any universe `v`
(`IsSheafOver.of_small`): a `v`-cover `𝓤` of `T` is refined by the `u`-cover
`Scheme.Cover.ulift 𝓤` (indexed by the points of `T`), and to compare a glued section with the
given section on `𝓤.X a` one uses the `u`-cover `(Scheme.Cover.ulift 𝓤).pullback₁ (𝓤.f a)` of
`𝓤.X a`. Consequently `overSigma F` is a Zariski sheaf as soon as `IsSheafOver.{u} F`
(`isSheaf_overSigma_of_small`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe v u

namespace CurvesJacobian

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)

/-- Two restrictions along composites `A ⟶ B ⟶ C` and `A ⟶ B' ⟶ C` of morphisms over `S`
agree when the composites agree. -/
lemma map_homMk_comp_eq {A B B' C : Scheme.{u}} {gA : A ⟶ S} {gB : B ⟶ S} {gB' : B' ⟶ S}
    {gC : C ⟶ S} (f₁ : A ⟶ B) (f₂ : B ⟶ C) (f₁' : A ⟶ B') (f₂' : B' ⟶ C)
    (e : f₁ ≫ f₂ = f₁' ≫ f₂') (h₁ : f₁ ≫ gB = gA) (h₂ : f₂ ≫ gC = gB)
    (h₁' : f₁' ≫ gB' = gA) (h₂' : f₂' ≫ gC = gB') (x : F.obj (op (Over.mk gC))) :
    F.map (Over.homMk f₁ h₁ : Over.mk gA ⟶ Over.mk gB).op
        (F.map (Over.homMk f₂ h₂ : Over.mk gB ⟶ Over.mk gC).op x) =
      F.map (Over.homMk f₁' h₁' : Over.mk gA ⟶ Over.mk gB').op
        (F.map (Over.homMk f₂' h₂' : Over.mk gB' ⟶ Over.mk gC).op x) := by
  have : (Over.homMk f₁ h₁ : Over.mk gA ⟶ Over.mk gB) ≫
        (Over.homMk f₂ h₂ : Over.mk gB ⟶ Over.mk gC) =
      (Over.homMk f₁' h₁' : Over.mk gA ⟶ Over.mk gB') ≫
        (Over.homMk f₂' h₂' : Over.mk gB' ⟶ Over.mk gC) := by
    ext
    exact e
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, this]

variable {F}

/-- The sheaf condition over `S` for covers indexed in `Type u` implies it for covers indexed
in any universe `v`. -/
theorem IsSheafOver.of_small (hF : IsSheafOver.{u} F) : IsSheafOver.{v} F := by
  intro T g 𝓤 y hy
  let 𝓥 : T.OpenCover := Scheme.Cover.ulift 𝓤
  obtain ⟨z, hz, huniq⟩ := hF T g 𝓥 (fun x ↦ y (𝓤.idx x)) (fun x x' ↦ hy _ _)
  have key : ∀ z' : F.obj (op (Over.mk g)), (∀ x, F.map (Over.homMk (𝓤.f (𝓤.idx x)) rfl :
      Over.mk (𝓤.f (𝓤.idx x) ≫ g) ⟶ Over.mk g).op z' = y (𝓤.idx x)) →
      ∀ a, F.map (Over.homMk (𝓤.f a) rfl : Over.mk (𝓤.f a ≫ g) ⟶ Over.mk g).op z' = y a := by
    intro z' hz' a
    let 𝓦 : (𝓤.X a).OpenCover := 𝓥.pullback₁ (𝓤.f a)
    let y' : ∀ x, F.obj (op (Over.mk (𝓦.f x ≫ 𝓤.f a ≫ g))) := fun x ↦
      F.map (Over.homMk (𝓦.f x) rfl :
        Over.mk (𝓦.f x ≫ 𝓤.f a ≫ g) ⟶ Over.mk (𝓤.f a ≫ g)).op (y a)
    obtain ⟨_, _, hu⟩ := hF _ (𝓤.f a ≫ g) 𝓦 y' fun x x' ↦
      map_homMk_comp_eq F _ _ _ _ pullback.condition _ _ _ _ _
    refine (hu _ fun (x : T) ↦ ?_).trans (hu _ fun x ↦ rfl).symm
    refine (map_homMk_comp_eq F _ _ (pullback.snd (𝓤.f a) (𝓤.f (𝓤.idx x)))
      (𝓤.f (𝓤.idx x)) pullback.condition _ _ (pullback.condition_assoc g).symm rfl z').trans ?_
    exact (congrArg _ (hz' x)).trans (hy a (𝓤.idx x)).symm
  refine ⟨z, key z hz, fun z' hz' ↦ huniq z' fun x ↦ hz' _⟩

/-- **`overSigma F` is a Zariski sheaf** if `F` satisfies the sheaf condition for open covers
over `S` indexed in `Type u`. -/
theorem isSheaf_overSigma_of_small (hF : IsSheafOver.{u} F) :
    Presieve.IsSheaf Scheme.zariskiTopology (overSigma F) :=
  isSheaf_overSigma hF.of_small

end CurvesJacobian
