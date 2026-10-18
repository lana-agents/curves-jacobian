/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# Profinite completions of isomorphic groups in different universes

`Pi1.Profinite.completionCongr` turns a group isomorphism `G ≃* H` into an isomorphism of
profinite completions, but only for `G` and `H` in the same universe (it goes through the
functor `profiniteCompletion : GrpCat.{u} ⥤ ProfiniteGrp.{u}`). Here we work directly with
Mathlib's concrete model of the completion (compatible families indexed by finite-index normal
subgroups) and allow `G : Type u`, `H : Type v`.

## Main definitions and results

* `CurvesJacobian.Cusp.completionMap'`: the continuous homomorphism `Ĝ →* Ĥ` induced by a
  homomorphism `f : G →* H` (any universes); `completionMap'_etaFn` says that it extends `f`.
* `CurvesJacobian.Cusp.completionCongr'`: a group isomorphism `e : G ≃* H` induces an
  isomorphism of topological groups `Ĝ ≃ₜ* Ĥ`, with `completionCongr'_etaFn` and
  `completionCongr'_symm_etaFn`.
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

universe u v

namespace CurvesJacobian.Cusp

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The map `G ⧸ f⁻¹(N) →* H ⧸ N` induced by `f : G →* H`. -/
noncomputable abbrev quotMap (f : G →* H) (N : FiniteIndexNormalSubgroup H) :
    G ⧸ (N.comap f).toSubgroup →* H ⧸ N.toSubgroup :=
  QuotientGroup.map _ _ f (FiniteIndexNormalSubgroup.toSubgroup_comap f N).le

/-- The value of the induced map `Ĝ → Ĥ` at the component `N` (a family of compatible elements
of the finite quotients of `G` is sent to a family for `H`). -/
noncomputable def completionMapFn (f : G →* H) (z : completion (GrpCat.of G)) :
    completion (GrpCat.of H) :=
  ⟨fun N ↦ (quotMap f N
      (z.val (N.comap f) : G ⧸ (N.comap f).toSubgroup) : H ⧸ N.toSubgroup), by
    intro N M π
    have hz := z.prop (homOfLE (FiniteIndexNormalSubgroup.comap_mono f π.le))
    dsimp only
    rw [← hz]
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
      (z.val (N.comap f) : G ⧸ (N.comap f).toSubgroup)
    rw [← hg]
    rfl⟩

theorem completionMapFn_val (f : G →* H) (z : completion (GrpCat.of G))
    (N : FiniteIndexNormalSubgroup (GrpCat.of H)) :
    ((completionMapFn f z).val N : H ⧸ N.toSubgroup) =
      quotMap f N
        (z.val (N.comap f) : G ⧸ (N.comap f).toSubgroup) := rfl

/-- **The continuous homomorphism `Ĝ →* Ĥ` induced by `f : G →* H`**, for `G` and `H` in
possibly different universes. -/
noncomputable def completionMap' (f : G →* H) :
    completion (GrpCat.of G) →ₜ* completion (GrpCat.of H) where
  toFun := completionMapFn f
  map_one' := by
    refine Subtype.ext (funext fun N ↦ ?_)
    exact map_one (quotMap f N)
  map_mul' x y := by
    refine Subtype.ext (funext fun N ↦ ?_)
    exact map_mul (quotMap f N) _ _
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun N ↦ ?_) _
    haveI : DiscreteTopology ((diagram (GrpCat.of G)).obj (N.comap f)) := ⟨rfl⟩
    have hc : Continuous fun z : completion (GrpCat.of G) ↦ z.val (N.comap f) :=
      (continuous_apply (N.comap f)).comp continuous_subtype_val
    exact (continuous_of_discreteTopology (α := (diagram (GrpCat.of G)).obj (N.comap f))
      (β := (diagram (GrpCat.of H)).obj N) (f := quotMap f N)).comp hc

@[simp]
theorem completionMap'_apply (f : G →* H) (z : completion (GrpCat.of G)) :
    completionMap' f z = completionMapFn f z := rfl

/-- `completionMap' f` extends `f`. -/
@[simp]
theorem completionMap'_etaFn (f : G →* H) (x : G) :
    completionMap' f (etaFn (GrpCat.of G) x) = etaFn (GrpCat.of H) (f x) := rfl

/-- `completionMap' e.symm` is a left inverse of `completionMap' e` for `e : G ≃* H`. -/
theorem completionMap'_symm_apply_apply (e : G ≃* H) (z : completion (GrpCat.of G)) :
    completionMap' e.symm.toMonoidHom (completionMap' e.toMonoidHom z) = z := by
  refine Subtype.ext (funext fun N ↦ ?_)
  have hle : N ≤ (N.comap e.symm.toMonoidHom).comap e.toMonoidHom := fun g hg ↦
    show e.symm (e g) ∈ N.toSubgroup by
      simpa [FiniteIndexNormalSubgroup.mem_toSubgroup_iff] using hg
  have hz := z.prop (homOfLE hle)
  change (QuotientGroup.map _ _ _ _ (QuotientGroup.map _ _ _ _
    (z.val ((N.comap e.symm.toMonoidHom).comap e.toMonoidHom))) : G ⧸ N.toSubgroup) = z.val N
  rw [← hz]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (z.val N : G ⧸ N.toSubgroup)
  rw [← hg]
  change (QuotientGroup.mk (e.symm (e g)) : G ⧸ N.toSubgroup) = QuotientGroup.mk g
  rw [MulEquiv.symm_apply_apply]

/-- **A group isomorphism `G ≃* H` induces an isomorphism of profinite completions**, for `G`
and `H` in possibly different universes (cf. `Pi1.Profinite.completionCongr`). -/
noncomputable def completionCongr' (e : G ≃* H) :
    completion (GrpCat.of G) ≃ₜ* completion (GrpCat.of H) where
  toFun := completionMap' e.toMonoidHom
  invFun := completionMap' e.symm.toMonoidHom
  left_inv := completionMap'_symm_apply_apply e
  right_inv z := by
    simpa using completionMap'_symm_apply_apply e.symm z
  map_mul' := map_mul (completionMap' e.toMonoidHom)
  continuous_toFun := (completionMap' e.toMonoidHom).continuous
  continuous_invFun := (completionMap' e.symm.toMonoidHom).continuous

theorem completionCongr'_apply (e : G ≃* H) (z : completion (GrpCat.of G)) :
    completionCongr' e z = completionMap' e.toMonoidHom z := rfl

theorem completionCongr'_symm_apply (e : G ≃* H) (z : completion (GrpCat.of H)) :
    (completionCongr' e).symm z = completionMap' e.symm.toMonoidHom z := rfl

/-- `completionCongr' e` extends `e`. -/
@[simp]
theorem completionCongr'_etaFn (e : G ≃* H) (x : G) :
    completionCongr' e (etaFn (GrpCat.of G) x) = etaFn (GrpCat.of H) (e x) := rfl

/-- `(completionCongr' e).symm` extends `e.symm`. -/
@[simp]
theorem completionCongr'_symm_etaFn (e : G ≃* H) (y : H) :
    (completionCongr' e).symm (etaFn (GrpCat.of H) y) = etaFn (GrpCat.of G) (e.symm y) := rfl

end CurvesJacobian.Cusp
