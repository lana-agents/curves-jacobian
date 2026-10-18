/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.CountableSubfield
import CurvesJacobian.Galois.SmoothDescent
import CurvesJacobian.Galois.MaxSpecBaseChange
import Belyi.Converse.BranchedPi1
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Countable models of affine algebras with a coordinate

Let `k` be an algebraically closed field, `B` a finitely generated `k`-algebra and `t ∈ B`.
Then `(B, t)` is defined over a countable algebraically closed subfield `k₀ ⊆ k`: there are a
finitely generated `k₀`-algebra `B₀`, `t₀ ∈ B₀` and a `k`-algebra isomorphism
`e : k ⊗[k₀] B₀ ≃ₐ[k] B` with `e (1 ⊗ t₀) = t` (`CurvesJacobian.exists_countable_model`;
take `k₀` algebraically closed, countable and containing the coefficients of a finite
presentation of `B` and of a polynomial expression of `t`, and `B₀` the model of the
presentation over `k₀`, `Algebra.Presentation.ModelOfHasCoeffs`).

Properties of the model, for any field extension `k₀ ⊆ k` and `e` as above:
* `CurvesJacobian.isDomain_of_tensor_equiv`: `B₀` is a domain if `B` is;
* `CurvesJacobian.finite_of_baseChange`: `k₀[X] → B₀`, `X ↦ t₀`, is finite if
  `k[X] → k ⊗ B₀`, `X ↦ 1 ⊗ t₀`, is (finiteness descends along the faithfully flat
  `k₀[X] → k[X]`);
* `CurvesJacobian.smoothOfRelativeDimension_of_tensor_equiv`: `Spec B₀ → Spec k₀` is smooth of
  relative dimension `n` if `Spec B → Spec k` is
  (`CurvesJacobian.smoothOfRelativeDimension_of_baseChange`).
-/

open CategoryTheory TensorProduct AlgebraicGeometry

universe u

namespace CurvesJacobian

noncomputable section

/-- **Countable models.** A finitely generated algebra `B` over an algebraically closed field `k`,
with an element `t`, is the base change of a finitely generated algebra `B₀` over a countable
algebraically closed subfield `k₀ ⊆ k` containing a given finite set `s`, with `t` coming from
`t₀ ∈ B₀`. -/
theorem exists_countable_model {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] (t : B) (s : Set k) (hs : s.Finite) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : IsAlgClosed k₀) (_ : Countable k₀) (_ : Algebra k₀ k)
      (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra k₀ B₀) (_ : Algebra.FiniteType k₀ B₀)
      (t₀ : B₀) (e : k ⊗[k₀] B₀ ≃ₐ[k] B),
      e (1 ⊗ₜ t₀) = t ∧ s ⊆ Set.range (algebraMap k₀ k) := by
  classical
  haveI : Algebra.FinitePresentation k B := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  let P := Algebra.Presentation.ofFinitePresentation k B
  obtain ⟨pt, hpt⟩ := P.algebraMap_surjective t
  let s' : Set k := P.coeffs ∪ (pt.coeffs : Set k) ∪ s
  have hs' : s'.Countable :=
    ((P.finite_coeffs.union pt.coeffs.finite_toSet).union hs).countable
  obtain ⟨k₀, _, _, hk₀, _, hsub⟩ := exists_countable_isAlgClosed_subfield k s' hs'
  letI : Algebra k₀ B := ((algebraMap k B).comp (algebraMap k₀ k)).toAlgebra
  haveI : IsScalarTower k₀ k B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : P.HasCoeffs k₀ := ⟨fun x hx ↦ hsub (Or.inl (Or.inl hx))⟩
  have hpt₀ : pt ∈ Set.range (MvPolynomial.map (algebraMap k₀ k)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    exact fun x hx ↦ hsub (Or.inl (Or.inr hx))
  obtain ⟨pt₀, hpt₀⟩ := hpt₀
  refine ⟨k₀, inferInstance, inferInstance, hk₀, inferInstance, P.ModelOfHasCoeffs k₀,
    inferInstance, inferInstance, inferInstance, Ideal.Quotient.mk _ pt₀,
    P.tensorModelOfHasCoeffsEquiv k₀, ?_, fun x hx ↦ hsub (Or.inr hx)⟩
  rw [← hpt]
  change P.tensorModelOfHasCoeffsEquiv k₀ ((1 : k) ⊗ₜ pt₀) = _
  rw [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul, ← hpt₀,
    Algebra.Generators.algebraMap_apply, MvPolynomial.aeval_map_algebraMap]

section Transfer

variable {k₀ k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {B₀ : Type u} [CommRing B₀]
  [Algebra k₀ B₀] {B : Type u} [CommRing B] [Algebra k B] (e : k ⊗[k₀] B₀ ≃ₐ[k] B)

/-- The map `B₀ → B`, `b ↦ e (1 ⊗ b)`, is injective. -/
lemma injective_of_tensor_equiv :
    Function.Injective fun b : B₀ ↦ e (1 ⊗ₜ b) :=
  e.injective.comp (Algebra.TensorProduct.includeRight_injective (algebraMap k₀ k).injective)

include e in
/-- **The model of a domain is a domain.** -/
lemma isDomain_of_tensor_equiv [IsDomain B] : IsDomain B₀ := by
  haveI : Nontrivial B₀ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : (1 : k ⊗[k₀] B₀) = 0 := by
      rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : B₀) 0, tmul_zero]
    exact one_ne_zero (by rw [← map_one e, h1, map_zero] : (1 : B) = 0)
  let φ : B₀ →+* B := e.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B₀ →ₐ[k₀] k ⊗[k₀] B₀).toRingHom
  exact Function.Injective.isDomain φ (injective_of_tensor_equiv e)

include e in
/-- **The model of a smooth curve is smooth**: `Spec B₀ → Spec k₀` is smooth of relative
dimension `n` if `Spec B → Spec k` is (`B₀` a domain). -/
theorem smoothOfRelativeDimension_of_tensor_equiv [IsDomain B₀] {n : ℕ}
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k B)))] :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k₀ B₀))) := by
  apply smoothOfRelativeDimension_of_baseChange (K := k)
  have h : algebraMap k (k ⊗[k₀] B₀) = e.symm.toRingEquiv.toRingHom.comp (algebraMap k B) := by
    ext c
    simp
  rw [h, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
    inferInstanceAs (IsIso e.symm.toRingEquiv.toCommRingCatIso.hom)
  haveI h0 := smoothOfRelativeDimension_comp 0 n
    (Spec.map (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  rwa [zero_add] at h0

end Transfer

section Finite

variable {k₀ k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {B₀ : Type u} [CommRing B₀]
  [Algebra k₀ B₀]

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

/-- **Finiteness of a coordinate descends along field extensions**: if `k[X] → k ⊗[k₀] B₀`,
`X ↦ 1 ⊗ t₀`, is finite, so is `k₀[X] → B₀`, `X ↦ t₀` (the square `k₀[X] → B₀`,
`k[X] → k ⊗ B₀` is a pushout and `k₀[X] → k[X]` is faithfully flat). -/
theorem finite_of_baseChange (t₀ : B₀)
    (h : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ (1 ⊗ₜ t₀ : k ⊗[k₀] B₀)).Finite) :
    (MvPolynomial.aeval (R := k₀) fun _ : Fin 1 ↦ t₀).Finite := by
  letI : Algebra (MvPolynomial (Fin 1) k₀) B₀ :=
    (MvPolynomial.aeval (R := k₀) fun _ : Fin 1 ↦ t₀).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin 1) k) (k ⊗[k₀] B₀) :=
    (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ (1 ⊗ₜ t₀ : k ⊗[k₀] B₀)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin 1) k₀) (k ⊗[k₀] B₀) :=
    ((algebraMap B₀ (k ⊗[k₀] B₀)).comp
      (MvPolynomial.aeval (R := k₀) fun _ : Fin 1 ↦ t₀).toRingHom).toAlgebra
  haveI : IsScalarTower k₀ (MvPolynomial (Fin 1) k₀) B₀ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k₀ B₀ r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower (MvPolynomial (Fin 1) k₀) B₀ (k ⊗[k₀] B₀) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (MvPolynomial (Fin 1) k₀) (MvPolynomial (Fin 1) k) (k ⊗[k₀] B₀) :=
    IsScalarTower.of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun r ↦ by
      change algebraMap B₀ (k ⊗[k₀] B₀) (MvPolynomial.aeval _ (MvPolynomial.C r)) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap k₀ k) (MvPolynomial.C r))
      rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.aeval_C]
      change (1 : k) ⊗ₜ algebraMap k₀ B₀ r = algebraMap k₀ k r ⊗ₜ (1 : B₀)
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply'])
      (fun i ↦ by
        change algebraMap B₀ (k ⊗[k₀] B₀) (MvPolynomial.aeval _ (MvPolynomial.X i)) =
          MvPolynomial.aeval _ (MvPolynomial.map (algebraMap k₀ k) (MvPolynomial.X i))
        rw [MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.aeval_X]
        rfl))
  haveI : IsScalarTower k₀ (MvPolynomial (Fin 1) k) (k ⊗[k₀] B₀) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k₀ (k ⊗[k₀] B₀) r =
        MvPolynomial.aeval _ (MvPolynomial.C (algebraMap k₀ k r))
      rw [MvPolynomial.aeval_C]
      rfl
  haveI : IsScalarTower k (MvPolynomial (Fin 1) k) (k ⊗[k₀] B₀) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k (k ⊗[k₀] B₀) r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower k₀ B₀ (k ⊗[k₀] B₀) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k (k ⊗[k₀] B₀) (algebraMap k₀ k r) = (1 : k) ⊗ₜ algebraMap k₀ B₀ r
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  haveI : Algebra.IsPushout k₀ B₀ k (k ⊗[k₀] B₀) := TensorProduct.isPushout'
  haveI : Algebra.IsPushout (MvPolynomial (Fin 1) k₀) B₀ (MvPolynomial (Fin 1) k)
      (k ⊗[k₀] B₀) :=
    (Algebra.IsPushout.comp_iff k₀ (MvPolynomial (Fin 1) k₀) k (S' := MvPolynomial (Fin 1) k)
      (T := B₀) (T' := k ⊗[k₀] B₀)).1 inferInstance
  have hFF : (algebraMap (MvPolynomial (Fin 1) k₀) (MvPolynomial (Fin 1) k)).FaithfullyFlat :=
    RingHom.FaithfullyFlat.isStableUnderBaseChange k₀ k (MvPolynomial (Fin 1) k₀)
      (MvPolynomial (Fin 1) k) ((RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)
  exact RingHom.Finite.codescendsAlong_faithfullyFlat (R := MvPolynomial (Fin 1) k₀) (S := B₀)
    (R' := MvPolynomial (Fin 1) k) (S' := k ⊗[k₀] B₀) hFF h

end Finite

end

end CurvesJacobian
