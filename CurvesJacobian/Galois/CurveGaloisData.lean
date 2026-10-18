/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.EtalePi1
import CurvesJacobian.Scheme.CurveFunctionField

/-!
# Galois data for a curve

The Galois-theoretic files (`Galois/EtalePi1.lean`, `Galois/EtalePi1Open.lean`,
`Galois/PicTorsion.lean`, `Cusp/Inertia.lean`, ...) work with pi1's Galois data
`D : GaloisData k t` together with an isomorphism `eL : K(X) ≃ L = Ω^{H_L}` sending a rational
function `τ` to `t`, and `H = H_L`. Here we construct such data for every curve `X` over a field
`k` of characteristic `0`: `Ω` is an algebraic closure of `K(X)`, `t` the image of a
transcendental `τ ∈ K(X)`, `L ⊆ Ω` the image of `K(X)` and `H = H_L = Gal(Ω/L)`
(open since `L/k(t)` is finite).

* `CurvesJacobian.exists_curveGaloisData`.
-/

open CategoryTheory AlgebraicGeometry Belyi Pi1.Orbifold AffOrbicurve WeilCurves.FunctionField
open scoped IntermediateField

universe u

namespace CurvesJacobian

variable {k : Type u} [Field k]

section Field

variable {K : Type u} [Field K] [Algebra k K] {τ : K}

/-- The image of `K` in its algebraic closure, as an intermediate field over `k`. -/
noncomputable abbrev imageK (k K : Type u) [Field k] [Field K] [Algebra k K] :
    IntermediateField k (AlgebraicClosure K) :=
  (IsScalarTower.toAlgHom k K (AlgebraicClosure K)).fieldRange

lemma K₀_le_imageK (τ : K) :
    K₀ k (algebraMap K (AlgebraicClosure K) τ) ≤ imageK k K :=
  IntermediateField.adjoin_simple_le_iff.2 ⟨τ, rfl⟩

/-- The image of `K` in its algebraic closure, as an intermediate field over `k(τ)`. -/
noncomputable abbrev imageL (τ : K) :
    IntermediateField (K₀ k (algebraMap K (AlgebraicClosure K) τ)) (AlgebraicClosure K) :=
  IntermediateField.extendScalars (K₀_le_imageK (k := k) τ)

lemma mem_imageL_iff (x : AlgebraicClosure K) :
    x ∈ imageL (k := k) τ ↔ x ∈ Set.range (algebraMap K (AlgebraicClosure K)) := Iff.rfl

/-- `K ≃ L`. -/
noncomputable def equivImageL (τ : K) : K ≃+* imageL (k := k) τ :=
  ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k K (AlgebraicClosure K))).toRingEquiv.trans
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl })

@[simp] lemma coe_equivImageL (z : K) :
    ((equivImageL (k := k) τ z : imageL (k := k) τ) : AlgebraicClosure K) =
      algebraMap K (AlgebraicClosure K) z :=
  rfl

lemma transcendental_image (hτ : Transcendental k τ) :
    Transcendental k (algebraMap K (AlgebraicClosure K) τ) := by
  exact (transcendental_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).2 hτ

/-- `L` is finite over `k(t)`. -/
lemma finiteDimensional_imageL [IsFunctionField k K] (hτ : Transcendental k τ) :
    FiniteDimensional (K₀ k (algebraMap K (AlgebraicClosure K) τ)) (imageL (k := k) τ) := by
  haveI := finiteDimensional_adjoin hτ
  set j := IsScalarTower.toAlgHom k K (AlgebraicClosure K)
  have hmap : (k⟮τ⟯).map j = K₀ k (algebraMap K (AlgebraicClosure K) τ) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e₁ : k⟮τ⟯ ≃+* K₀ k (algebraMap K (AlgebraicClosure K) τ) :=
    ((IntermediateField.equivMap k⟮τ⟯ j).trans (IntermediateField.equivOfEq hmap)).toRingEquiv
  refine Module.Finite.of_equiv_equiv e₁ (equivImageL τ) ?_
  ext x
  rfl

theorem isGalois_K₀_algebraicClosure [CharZero k] [IsFunctionField k K] (τ : K)
    (hτ : Transcendental k τ) :
    IsGalois (K₀ k (algebraMap K (AlgebraicClosure K) τ)) (AlgebraicClosure K) := by
  set K₀' := K₀ k (algebraMap K (AlgebraicClosure K) τ)
  haveI := finiteDimensional_imageL (k := k) hτ
  haveI : Algebra.IsAlgebraic (imageL (k := k) τ) (AlgebraicClosure K) := by
    refine ⟨fun x ↦ ?_⟩
    have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    have := hx.map_of_comp_eq (equivImageL (k := k) τ).toRingHom (RingHom.id _) (by ext; rfl)
    exact this.isAlgebraic
  haveI : Algebra.IsAlgebraic K₀' (imageL (k := k) τ) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic K₀' (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans K₀' (imageL (k := k) τ) (AlgebraicClosure K)
  haveI : IsAlgClosure K₀' (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  exact isGalois_iff.2 ⟨inferInstance, IsAlgClosure.normal _ _⟩

end Field

/-- **Galois data for a curve**: for an integral `k`-scheme `X` whose function field is a
function field of one variable over `k` (`char k = 0`), there are an algebraically closed field
`Ω`, Galois over `k(t)`, Galois data `D : GaloisData k t` with `H = H_L`, an isomorphism
`eL : K(X) ≃ L` over `k`, and a rational function `τ` with `eL τ = t`. -/
theorem exists_curveGaloisData [CharZero k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsFunctionField k X.functionField] :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (t : Ω)
      (_ : IsGalois (K₀ k t) Ω) (D : GaloisData k t) (eL : X.functionField ≃+* D.L)
      (τ : X.functionField),
      (∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c) ∧
      ((eL τ : D.L) : Ω) = t ∧ D.H ≤ D.HL := by
  obtain ⟨τ, hτ⟩ := exists_transcendental k X.functionField
  haveI := isGalois_K₀_algebraicClosure (k := k) τ hτ
  haveI := finiteDimensional_imageL (k := k) hτ
  let D : GaloisData k (algebraMap X.functionField (AlgebraicClosure X.functionField) τ) :=
    { H := (imageL (k := k) τ).fixingSubgroup
      HL := (imageL (k := k) τ).fixingSubgroup
      le := le_rfl
      isOpen_HL := (imageL (k := k) τ).fixingSubgroup_isOpen
      conj_mem := fun h hh n hn ↦ mul_mem (mul_mem hh hn) (inv_mem hh)
      transcendental := transcendental_image hτ }
  have hDL : D.L = imageL (k := k) τ := InfiniteGalois.fixedField_fixingSubgroup _
  let eL : X.functionField ≃+* D.L :=
    (equivImageL (k := k) τ).trans (IntermediateField.equivOfEq hDL.symm)
  refine ⟨AlgebraicClosure X.functionField, inferInstance, inferInstance, inferInstance, _,
    inferInstance, D, eL, τ, fun c ↦ ?_, rfl, le_rfl⟩
  exact (IsScalarTower.algebraMap_apply k X.functionField (AlgebraicClosure X.functionField) c).symm

end CurvesJacobian
