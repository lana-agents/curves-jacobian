/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.OpenSubfunctor

/-!
# Representing elements locally

Let `F` be a Zariski sheaf on schemes and `ξ ∈ F(Y)` such that `a ↦ ξ|_a` is injective on
`T`-points for affine `T`. If an element `x ∈ F(T)` is, locally on `T`, of the form `ξ|_a`, then
it is globally of this form (`AlgebraicGeometry.Scheme.OpenSubfunctor.exists_of_locally`): the
local morphisms agree on overlaps by injectivity and glue.
-/

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.OpenSubfunctor

variable {F : Sheaf Scheme.zariskiTopology.{u} (Type u)} {Y : Scheme.{u}} (ξ : F.obj.obj (op Y))

/-- If `x ∈ F(T)` is locally of the form `ξ|_a`, then it is globally of this form. -/
theorem exists_of_locally
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y ↦ F.obj.map a.op ξ)
    {T : Scheme.{u}} (x : F.obj.obj (op T))
    (hloc : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      ∃ a : (U : Scheme.{u}) ⟶ Y, F.obj.map a.op ξ = F.obj.map U.ι.op x) :
    ∃ a : T ⟶ Y, F.obj.map a.op ξ = x := by
  choose U hU a ha using hloc
  have hcov : TopologicalSpace.IsOpenCover U := by
    change iSup U = ⊤
    refine eq_top_iff.mpr fun t _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨t, hU t⟩
  let 𝒰 := T.openCoverOfIsOpenCover U hcov
  refine ⟨𝒰.glueMorphisms a fun i j ↦ injective_of_isAffine ξ hinj _ ?_, ?_⟩
  · change F.obj.map (pullback.fst (U i).ι (U j).ι ≫ a i).op ξ =
      F.obj.map (pullback.snd (U i).ι (U j).ι ≫ a j).op ξ
    rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ha, ha,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      pullback.condition]
  · refine ext_of_openCover 𝒰 fun i ↦ ?_
    rw [← Functor.map_comp_apply, ← op_comp, Scheme.Cover.ι_glueMorphisms]
    exact ha i

end AlgebraicGeometry.Scheme.OpenSubfunctor
