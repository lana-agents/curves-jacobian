/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.FundamentalGroup.FiberFunctorIso
import Pi1.FundamentalGroup.Functoriality

/-!
# Changing base points compatibly with maps of fundamental groups (MR8.3, task 2 (iv))

An isomorphism of fibre functors `α : F ≅ F'` on `C` and a functor `H : D ⥤ C` with
`e : H ⋙ F ≅ G`, `e' : H ⋙ F' ≅ G'` give an isomorphism `G ≅ G'` (`transportIso e e' α`), and
the maps `fiberAutMap` commute with the conjugations (`fiberAutMap_conjAut`). For étale
fundamental groups (`H` = pullback along `f : Y ⟶ X`): a change of base point on `Y` given by an
isomorphism of fibre functors induces one on `X`, compatibly with `fundamentalGroupMap f`
(`AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_autContinuousMulEquivOfIso`); hence the
kernel of `π₁ᵉᵗ(Y, ξ') → π₁ᵉᵗ(X, ξ' ≫ f)` is the image of the kernel at `ξ`
(`ker_fundamentalGroupMap_eq_map`).

This is used to move the kernel formula for filling in cusps
(`CurvesJacobian.Cusp.ker_fundamentalGroupMap_homOfLE_eq_normalClosure`, at the generic point)
to arbitrary base points, in particular to the base point of the arithmetic fundamental group.
Note that an *arbitrary* isomorphism `π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ')` need not have this property; those
coming from isomorphisms of fibre functors do (they are canonical up to inner automorphisms).
-/

open CategoryTheory Functor

universe u u₁ u₂ u₃ u₄ w

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]
  {F F' : C ⥤ FintypeCat.{w}} {G G' : D ⥤ FintypeCat.{w}} {H : D ⥤ C}

/-- The isomorphism `G ≅ G'` induced by `α : F ≅ F'` along `e : H ⋙ F ≅ G`, `e' : H ⋙ F' ≅ G'`. -/
noncomputable def transportIso (e : H ⋙ F ≅ G) (e' : H ⋙ F' ≅ G') (α : F ≅ F') : G ≅ G' :=
  e.symm ≪≫ isoWhiskerLeft H α ≪≫ e'

/-- `fiberAutMap` commutes with changing the fibre functor. -/
lemma fiberAutMap_conjAut (e : H ⋙ F ≅ G) (e' : H ⋙ F' ≅ G') (α : F ≅ F') (σ : Aut F) :
    fiberAutMap e' (α.conjAut σ) = (transportIso e e' α).conjAut (fiberAutMap e σ) := by
  refine Iso.ext (NatTrans.ext (funext fun A ↦ FintypeCat.hom_ext _ _ fun x ↦ ?_))
  simp [fiberAutMap_hom_app_apply, transportIso, Iso.conjAut_apply]
  rfl

/-- The kernel of `fiberAutMap` after changing the fibre functor. -/
lemma ker_fiberAutMap_conjAut (e : H ⋙ F ≅ G) (e' : H ⋙ F' ≅ G') (α : F ≅ F') :
    (fiberAutMap e').ker = (fiberAutMap e).ker.map α.conjAut.toMonoidHom := by
  ext τ
  rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker]
  conv_lhs => rw [← α.conjAut.apply_symm_apply τ]
  rw [fiberAutMap_conjAut, MulEquiv.map_eq_one_iff]

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

open PreGaloisCategory

variable {X Y : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']

/-- **A change of base point on `Y` induces one on `X`**, compatibly with `f : Y ⟶ X`. -/
noncomputable def fiberIsoMap (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y} {ξ' : Spec (.of Ω') ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X}
    (h : ξ ≫ f = η) (h' : ξ' ≫ f = η') (α : fiber ξ ≅ fiber ξ') : fiber η ≅ fiber η' :=
  transportIso (pullbackFiberIso f h) (pullbackFiberIso f h') α

/-- **Naturality of base point changes**: `f_* ∘ α_* = (fiberIsoMap α)_* ∘ f_*`. -/
lemma fundamentalGroupMap_autContinuousMulEquivOfIso (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y}
    {ξ' : Spec (.of Ω') ⟶ Y} {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X} (h : ξ ≫ f = η)
    (h' : ξ' ≫ f = η') (α : fiber ξ ≅ fiber ξ')
    (σ : π₁ᵉᵗ(ξ)) :
    fundamentalGroupMap f h' (autContinuousMulEquivOfIso α σ) =
      autContinuousMulEquivOfIso (fiberIsoMap f h h' α) (fundamentalGroupMap f h σ) :=
  fiberAutMap_conjAut _ _ α σ

/-- **The kernel of `π₁ᵉᵗ(Y) → π₁ᵉᵗ(X)` does not depend on the base point**, up to the change of
base point given by an isomorphism of fibre functors. -/
theorem ker_fundamentalGroupMap_eq_map (f : Y ⟶ X) {ξ : Spec (.of Ω) ⟶ Y}
    {ξ' : Spec (.of Ω') ⟶ Y} {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X} (h : ξ ≫ f = η)
    (h' : ξ' ≫ f = η') (α : fiber ξ ≅ fiber ξ') :
    (fundamentalGroupMap f h').toMonoidHom.ker =
      (fundamentalGroupMap f h).toMonoidHom.ker.map
        (autContinuousMulEquivOfIso α).toMulEquiv.toMonoidHom :=
  ker_fiberAutMap_conjAut _ _ α

end AlgebraicGeometry.FiniteEtale
