/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Scheme.CurveFunctionField
import Belyi.Curve.GeomIntegralTensorDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The base field is algebraically closed in the function field

Let `X` be geometrically integral over a field `k` (structure morphism
`X ↘ Spec k`), with function field `K(X)` and belyi's `k`-algebra structure on it.

* `CurvesJacobian.sectionsAlgebra`: the `k`-algebra structure on `Γ(X, V)`, compatible with the
  one on `K(X)` (`CurvesJacobian.algebraMap_functionField_eq_germ`).
* `CurvesJacobian.mem_range_algebraMap_of_isAlgebraic`: every element of `K(X)` algebraic over
  `k` lies in `k`, i.e. `k` is algebraically closed in `K(X)`.

Proof: write `α ∈ K(X)` as the germ of `s ∈ A = Γ(X, V)` on an affine open `V`; let
`L = k[T]/(minpoly α)`, a field, embedded in `A` by `T ↦ s`. Geometric integrality gives that
`L ⊗_k A` is a domain (belyi's `isDomain_tensorProduct_of_geometricallyIntegral`), hence so is
`L ⊗_k L` (flatness over a field). A finite-dimensional domain over `k` is a field, so the
surjection `L ⊗_k L → L` is an isomorphism and `[L : k]² = [L : k]`, i.e. `deg minpoly α = 1`.

Consequently, for a curve `X/k` (`IsCurveOver`, `k` perfect), `k` is the full constant field of
`K(X)` and `curveGenus k X` is the genus of `K(X)` in the usual sense (Stichtenoth's
convention, as used by weil-curves).
-/

open CategoryTheory AlgebraicGeometry Belyi TensorProduct

namespace CurvesJacobian

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

/-- The `k`-algebra structure on the sections over `V`, via `X ↘ Spec k`. -/
noncomputable abbrev sectionsAlgebra (V : X.Opens) : Algebra k Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (X ↘ Spec (CommRingCat.of k)).appLE ⊤ V (by simp)).hom.toAlgebra

lemma algebraMap_functionField_eq_germ [IsIntegral X] (V : X.Opens) [Nonempty V] (c : k) :
    algebraMap k X.functionField c =
      X.germToFunctionField V (letI := sectionsAlgebra k X V; algebraMap k Γ(X, V) c) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) c =
    X.germToFunctionField V (((X ↘ Spec (CommRingCat.of k)).appLE ⊤ V (by simp))
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
  rw [Scheme.germToFunctionField, Scheme.Hom.appLE]
  simp only [CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

lemma fromSpec_comp_structure {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ (X ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (letI := sectionsAlgebra k X V; algebraMap k Γ(X, V))) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (CommRingCat.of k))
    (isAffineOpen_top _) hV (by simp), IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  rfl

/-- **`k` is algebraically closed in the function field of a geometrically integral
`k`-scheme.** -/
theorem mem_range_algebraMap_of_isAlgebraic [IsIntegral X]
    [GeometricallyIntegral (X ↘ Spec (CommRingCat.of k))] {α : X.functionField}
    (hα : IsAlgebraic k α) : α ∈ (algebraMap k X.functionField).range := by
  -- `α` is the germ of a section `s` over an affine open `V`
  obtain ⟨U, hU, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) α
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hU U.2
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  let s : Γ(X, V) := X.presheaf.map (homOfLE hVU).op s₀
  have hs : X.germToFunctionField V s = α := by
    rw [← hs₀]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  letI := sectionsAlgebra k X V
  -- the `k`-algebra map `Γ(X, V) → K(X)`
  let γ : Γ(X, V) →ₐ[k] X.functionField :=
    { (X.germToFunctionField V).hom with
      commutes' := fun c ↦ (algebraMap_functionField_eq_germ k X V c).symm }
  have hγ : Function.Injective γ := X.germToFunctionField_injective V
  -- `L = k[T]/(minpoly α)`
  have hint : IsIntegral k α := hα.isIntegral
  let f := minpoly k α
  haveI : Fact (Irreducible f) := ⟨minpoly.irreducible hint⟩
  let L := AdjoinRoot f
  have hfs : Polynomial.aeval s f = 0 := by
    apply hγ
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    change Polynomial.aeval (X.germToFunctionField V s) f = 0
    rw [hs]
    exact minpoly.aeval k α
  let ι : L →ₐ[k] Γ(X, V) := AdjoinRoot.liftAlgHom f (Algebra.ofId k Γ(X, V)) s (by
    exact hfs)
  have hι : Function.Injective ι := ι.toRingHom.injective
  -- geometric integrality: `L ⊗[k] Γ(X, V)` is a domain
  haveI : Nonempty (Spec (CommRingCat.of Γ(X, V))) := inferInstance
  haveI : IsDomain (L ⊗[k] Γ(X, V)) :=
    isDomain_tensorProduct_of_geometricallyIntegral (K := L) (X ↘ Spec (CommRingCat.of k))
      hV.fromSpec (fromSpec_comp_structure k X hV)
  -- hence `L ⊗[k] L` is a domain
  let τ : L ⊗[k] L →ₐ[k] L ⊗[k] Γ(X, V) := Algebra.TensorProduct.map (AlgHom.id k L) ι
  have hτ : Function.Injective τ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) ι.toLinearMap hι
  haveI : IsDomain (L ⊗[k] L) := hτ.isDomain τ.toRingHom
  -- finite-dimensional, so a field
  have hpb := AdjoinRoot.powerBasis (K := k) (f := f) (minpoly.ne_zero hint)
  haveI : Module.Finite k L := hpb.finite
  haveI : Algebra.IsIntegral k (L ⊗[k] L) := inferInstance
  have hfield : IsField (L ⊗[k] L) := isField_of_isIntegral_of_isField' (Field.toIsField k)
  letI := hfield.toField
  -- the multiplication map `L ⊗ L → L` is bijective
  let μ := Algebra.TensorProduct.lmul' (R := k) (S := L)
  have hμs : Function.Surjective μ := fun x ↦ ⟨x ⊗ₜ 1, by simp [μ]⟩
  have hμi : Function.Injective μ := μ.toRingHom.injective
  have hrank : Module.finrank k (L ⊗[k] L) = Module.finrank k L :=
    (LinearEquiv.ofBijective μ.toLinearMap ⟨hμi, hμs⟩).finrank_eq
  rw [Module.finrank_tensorProduct] at hrank
  have hpos : 0 < Module.finrank k L := Module.finrank_pos
  have hd : Module.finrank k L = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (hrank.trans (one_mul _).symm)
    exact this
  rw [(AdjoinRoot.powerBasis (K := k) (minpoly.ne_zero hint)).finrank,
    AdjoinRoot.powerBasis_dim] at hd
  exact (minpoly.natDegree_eq_one_iff).1 hd

/-- For a curve `X` over a perfect field `k`, the constant field of `K(X)` is `k`. -/
theorem curve_mem_range_algebraMap_of_isAlgebraic [PerfectField k] [IsCurveOver k X]
    [IsIntegral X] {α : X.functionField} (hα : IsAlgebraic k α) :
    α ∈ (algebraMap k X.functionField).range :=
  mem_range_algebraMap_of_isAlgebraic k X hα

end CurvesJacobian
