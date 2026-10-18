/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Group schemes with closed unit section are separated

For a group object `G` in schemes over `S` whose unit section `η : S ⟶ G` is a closed
immersion, the structure morphism `G ⟶ S` is separated
(`CurvesJacobian.isSeparated_of_grpObj`). In particular every group scheme over a field is
separated (`CurvesJacobian.isSeparated_of_grpObj_field`; the unit section of a group scheme
over a field is a closed immersion, `AlgebraicGeometry` instance in
`Mathlib.AlgebraicGeometry.Group.Abelian`).

Proof: the shear map `ψ : G ×_S G ⟶ G ×_S G`, `(x, y) ↦ (x y⁻¹, y)`, is an isomorphism and
carries the diagonal to `y ↦ (1, y)`, which is the base change of `η` along the first projection
(`CurvesJacobian.isPullback_lift_comp_id`).
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

noncomputable section

namespace CurvesJacobian

section Pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X S : C} (p : X ⟶ S) (e : S ⟶ X)
  (he : e ≫ p = 𝟙 S)

include he in
/-- For a section `e` of `p : X ⟶ S`, the map `x ↦ (e (p x), x) : X ⟶ X ×_S X` is the base
change of `e` along the first projection. -/
lemma isPullback_lift_comp_id :
    IsPullback (pullback.lift (p ≫ e) (𝟙 X) (by simp [he])) p (pullback.fst p p) e := by
  refine IsPullback.of_isLimit' ⟨pullback.lift_fst _ _ _⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ s.fst ≫ pullback.snd p p) ?_ ?_ ?_)
  · intro s
    have hc : s.fst ≫ pullback.fst p p = s.snd ≫ e := s.condition
    have h1 : s.fst ≫ pullback.snd p p ≫ p ≫ e = s.fst ≫ pullback.fst p p := by
      rw [← pullback.condition_assoc, reassoc_of% hc, ← Category.assoc e p e, he,
        Category.id_comp, hc]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact h1
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  · intro s
    have hc : s.fst ≫ pullback.fst p p = s.snd ≫ e := s.condition
    simp only [Category.assoc]
    rw [← pullback.condition, reassoc_of% hc, he, Category.comp_id]
  · intro s m h₁ _
    have := congrArg (· ≫ pullback.snd p p) h₁
    simpa only [Category.assoc, pullback.lift_snd, Category.comp_id] using this

end Pullback

open AlgebraicGeometry

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The shear map `(x, y) ↦ (x y⁻¹, y)`. -/
def shear : G ⊗ G ⟶ G ⊗ G := lift (fst G G / snd G G) (snd G G)

/-- The inverse shear map `(z, y) ↦ (z y, y)`. -/
def shearInv : G ⊗ G ⟶ G ⊗ G := lift (fst G G * snd G G) (snd G G)

lemma shear_shearInv : shear G ≫ shearInv G = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [shear, shearInv, Category.assoc, lift_fst, lift_snd, MonObj.comp_mul,
      div_mul_cancel, Category.id_comp]

lemma shearInv_shear : shearInv G ≫ shear G = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [shear, shearInv, Category.assoc, lift_fst, lift_snd, GrpObj.comp_div,
      mul_div_cancel_right, Category.id_comp]

instance : IsIso (shear G) := ⟨⟨shearInv G, shear_shearInv G, shearInv_shear G⟩⟩

lemma lift_id_shear : lift (𝟙 G) (𝟙 G) ≫ shear G = lift (toUnit G ≫ η) (𝟙 G) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [shear, Category.assoc, lift_fst, lift_snd, GrpObj.comp_div, div_self',
      Hom.one_def]

/-- **A group scheme whose unit section is a closed immersion is separated.** -/
theorem isSeparated_of_grpObj [IsClosedImmersion η[G].left] : IsSeparated G.hom := by
  obtain ⟨e, he⟩ : ∃ e : S ⟶ G.left, e = η[G].left := ⟨η[G].left, rfl⟩
  have hη : e ≫ G.hom = 𝟙 S := by
    rw [he]
    exact Over.w η[G]
  haveI : IsClosedImmersion e := by
    subst he
    assumption
  have hw : (G.hom ≫ e) ≫ G.hom = 𝟙 G.left ≫ G.hom := by
    rw [Category.assoc, hη, Category.comp_id, Category.id_comp]
  haveI h1 : IsClosedImmersion (pullback.lift (G.hom ≫ e) (𝟙 G.left) hw) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_lift_comp_id G.hom e hη).flip inferInstance
  have h2 : (lift (𝟙 G) (𝟙 G) ≫ shear G).left = pullback.lift (G.hom ≫ e) (𝟙 G.left) hw := by
    rw [lift_id_shear]
    apply pullback.hom_ext <;>
      simp [pullback.lift_fst, pullback.lift_snd, he]
  have h3 : pullback.diagonal G.hom = (lift (𝟙 G) (𝟙 G) ≫ shear G ≫ inv (shear G)).left := by
    rw [IsIso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd]
  haveI : IsIso (inv (shear G)).left :=
    (inferInstance : IsIso ((Over.forget S).map (inv (shear G))))
  refine ⟨?_⟩
  rw [h3, ← Category.assoc, Over.comp_left, h2]
  have h4 : IsClosedImmersion (inv (shear G)).left := inferInstance
  exact MorphismProperty.comp_mem (@IsClosedImmersion) _ _ h1 h4

/-- **Group schemes over a field are separated.** -/
instance isSeparated_of_grpObj_field {K : Type u} [Field K] (G : Over (Spec (.of K)))
    [GrpObj G] : IsSeparated G.hom :=
  isSeparated_of_grpObj G

end CurvesJacobian
