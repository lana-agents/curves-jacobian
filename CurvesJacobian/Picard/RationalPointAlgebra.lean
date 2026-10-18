/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Rational points avoiding a function (algebra for Stacks, Lemma 44.6.5, Tag 0B9Y)

* `CurvesJacobian.exists_algHom_ne_zero` (**Nullstellensatz**): if `k` is algebraically closed
  and `A` a finitely generated `k`-algebra which is a domain, every `r ≠ 0` in `A` is nonzero at
  some `k`-point `x : A →ₐ[k] k`. (A finitely generated `k`-algebra is Jacobson
  (Stacks, Tag 00GB), and its residue fields at maximal ideals are finite over `k`
  (Zariski's lemma, Stacks, Tag 00GB / 0CY7).)
* `CurvesJacobian.exists_algHom_evalTensor_ne_zero`: for a field extension `F ⊇ k`, every
  nonzero `a ∈ F ⊗_k A` stays nonzero under `id_F ⊗ x : F ⊗_k A → F` for some `k`-point `x`.
  This is the density of `C(k)` used in the proof of Stacks, Lemma 44.6.5 (Tag 0B9Y): a nonzero
  section of a line bundle on `C_F` does not vanish at some `k`-point of `C`.
-/

open TensorProduct

universe u v w

namespace CurvesJacobian

section Nullstellensatz

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A]

/-- **Nullstellensatz**: a nonzero element of a finitely generated domain over an algebraically
closed field `k` is nonzero at some `k`-point. -/
theorem exists_algHom_ne_zero {r : A} (hr : r ≠ 0) : ∃ x : A →ₐ[k] k, x r ≠ 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out' (⊥ : Ideal A) (Ideal.isRadical_bot_of_noZeroDivisors)
  have hr' : r ∉ (⊥ : Ideal A).jacobson := by rw [hj]; exact hr
  rw [Ideal.jacobson, Submodule.mem_sInf] at hr'
  push Not at hr'
  obtain ⟨m, ⟨-, hm⟩, hrm⟩ := hr'
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (A ⧸ m) := Algebra.FiniteType.trans (S := A) inferInstance
    inferInstance
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k (A ⧸ m)
  have hsurj : Function.Surjective (algebraMap k (A ⧸ m)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
  let e : k ≃ₐ[k] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m))
    ⟨(algebraMap k (A ⧸ m)).injective, hsurj⟩
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  intro h0
  apply hrm
  have : Ideal.Quotient.mk m r = 0 := by
    have := congrArg e h0
    simpa using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end Nullstellensatz

section Tensor

variable {k : Type u} [Field k] {F : Type v} [Field F] [Algebra k F] {A : Type w} [CommRing A]
  [Algebra k A]

/-- `id_F ⊗ x : F ⊗_k A → F` for a `k`-point `x : A →ₐ[k] k`. -/
noncomputable def evalTensor (x : A →ₐ[k] k) : F ⊗[k] A →ₗ[k] F :=
  (TensorProduct.rid k F).toLinearMap ∘ₗ LinearMap.lTensor F x.toLinearMap

@[simp] lemma evalTensor_tmul (x : A →ₐ[k] k) (f : F) (a : A) :
    evalTensor x (f ⊗ₜ a) = x a • f := by
  simp [evalTensor]

lemma evalTensor_comm (x : A →ₐ[k] k) (ℓ : Module.Dual k F) (a : F ⊗[k] A) :
    ℓ (evalTensor x a) = x (TensorProduct.lid k A (LinearMap.rTensor A ℓ a)) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul f a => simp [mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **Density of rational points**: a nonzero element of `F ⊗_k A` is nonzero under
`id_F ⊗ x` for some `k`-point `x` of `A` (`k` algebraically closed, `A` a finitely generated
domain). -/
theorem exists_algHom_evalTensor_ne_zero [IsAlgClosed k] [IsDomain A] [Algebra.FiniteType k A]
    {a : F ⊗[k] A} (ha : a ≠ 0) : ∃ x : A →ₐ[k] k, evalTensor x a ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k F
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := A) b
  have hea : e a ≠ 0 := by
    intro h; apply ha; rw [← e.symm_apply_apply a, h, map_zero]
  obtain ⟨i, hi⟩ : ∃ i, e a i ≠ 0 := by
    by_contra h
    push Not at h
    exact hea (Finsupp.ext h)
  have hcoord : ∀ a' : F ⊗[k] A,
      e a' i = TensorProduct.lid k A (LinearMap.rTensor A (b.coord i) a') := by
    intro a'
    induction a' using TensorProduct.induction_on with
    | zero => simp
    | tmul f r =>
      simp [e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
    | add a₁ a₂ h₁ h₂ => simp only [map_add, Finsupp.add_apply, h₁, h₂]
  obtain ⟨x, hx⟩ := exists_algHom_ne_zero (k := k) hi
  refine ⟨x, fun h0 ↦ hx ?_⟩
  rw [hcoord a, ← evalTensor_comm x (b.coord i) a, h0, map_zero]

end Tensor

end CurvesJacobian
