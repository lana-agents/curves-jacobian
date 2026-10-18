/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import FormalSchemes.TwoCech

/-!
# Algebra for the degree of the zero scheme of a section

Generic algebraic inputs for Stacks, Lemma 44.6.4 (Tag 0B9X):

* `CurvesJacobian.rankAtStalk_eq_of_invertible`: if `B` is a finite flat `A`-algebra and `P` an
  invertible `B`-module, then `P` and `B` have the same rank at every prime of `A` (the fibre
  `κ(p) ⊗_A B` is Artinian, hence semilocal, so its Picard group is trivial).
* `CurvesJacobian.Invertible.apply_smul_eq`, `CurvesJacobian.Invertible.range_eval_smul_top`:
  for an invertible module `M` and `s ∈ M`, the content ideal `I = {φ(s) : φ ∈ Mᵛ}` satisfies
  `I • M = R ∙ s`.
* `CurvesJacobian.IsBaseChange.surjective_and_ker_eq`: a base change along a surjective ring map
  `R → R/I` is surjective with kernel `I • M`.
* `TwoCech.δ_bijective`: for a short exact sequence of two-set Čech data, the connecting map
  `H⁰'' → H¹'` is bijective if `H⁰' → H⁰` is surjective and `H¹ = 0`.
-/

open TensorProduct Module Function

universe u

noncomputable section

namespace CurvesJacobian

section Rank

variable {A B P : Type u} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup P] [Module A P]
  [Module B P] [IsScalarTower A B P]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- For a `B`-module `P` and an `A`-algebra `K`, `K ⊗_A P ≃ (K ⊗_A B) ⊗_B P`, `K`-linearly. -/
def tensorBaseChangeEquiv (K : Type u) [CommRing K] [Algebra A K] :
    K ⊗[A] P ≃ₗ[K] (K ⊗[A] B) ⊗[B] P := by
  let j : P →ₗ[A] (K ⊗[A] B) ⊗[B] P :=
    (TensorProduct.mk B (K ⊗[A] B) P 1).restrictScalars A
  let F : K ⊗[A] P →ₗ[K] (K ⊗[A] B) ⊗[B] P := j.liftBaseChange K
  have hf := (inferInstance : Algebra.IsPushout A B K (K ⊗[A] B)).out
  let e : K ⊗[A] P ≃ₗ[A] (K ⊗[A] B) ⊗[B] P :=
    ((TensorProduct.comm A K P).trans
      ((hf.tensorEquiv P).restrictScalars A).symm).trans
      ((TensorProduct.comm B P (K ⊗[A] B)).restrictScalars A)
  have hFe : ∀ x, F x = e x := fun x ↦ by
    induction x with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul c p =>
      have h2 : hf.equiv.symm (c ⊗ₜ[A] (1 : B)) = 1 ⊗ₜ c := hf.equiv_symm_apply c
      have key : (hf.tensorEquiv P) (p ⊗ₜ[B] (c ⊗ₜ[A] (1 : B))) = p ⊗ₜ[A] c := by
        simp only [IsBaseChange.tensorEquiv, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul]
        rw [h2, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
      change c • ((1 : K ⊗[A] B) ⊗ₜ[B] p) =
        TensorProduct.comm B P (K ⊗[A] B) ((hf.tensorEquiv P).symm (p ⊗ₜ[A] c))
      rw [← key, LinearEquiv.symm_apply_apply, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
        Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact LinearEquiv.ofBijective F (by
    rw [show (F : K ⊗[A] P → (K ⊗[A] B) ⊗[B] P) = e from funext hFe]
    exact e.bijective)

/-- **Rank of an invertible module over a finite flat algebra**: if `B` is a finite flat
`A`-algebra and `P` an invertible `B`-module, then `P` and `B` have the same rank at every prime
of `A`. -/
theorem rankAtStalk_eq_of_invertible [Module.Finite A B] [Module.Flat A B]
    [Module.Invertible B P] (p : PrimeSpectrum A) : rankAtStalk P p = rankAtStalk B p := by
  haveI : Module.Finite A P := Module.Finite.trans B P
  haveI : Module.Flat A P := Module.Flat.trans A B P
  rw [rankAtStalk_eq, rankAtStalk_eq]
  let K := p.asIdeal.ResidueField
  change finrank K (K ⊗[A] P) = finrank K (K ⊗[A] B)
  rw [(tensorBaseChangeEquiv (B := B) K).finrank_eq]
  haveI : IsArtinianRing (K ⊗[A] B) := IsArtinianRing.of_finite K (K ⊗[A] B)
  haveI : Module.Free (K ⊗[A] B) ((K ⊗[A] B) ⊗[B] P) := inferInstance
  by_cases h : Nontrivial (K ⊗[A] B)
  · obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := K ⊗[A] B)
      (M := (K ⊗[A] B) ⊗[B] P)).mp inferInstance
    exact (e.restrictScalars K).finrank_eq
  · rw [not_nontrivial_iff_subsingleton] at h
    haveI : Subsingleton ((K ⊗[A] B) ⊗[B] P) := by
      refine ⟨fun x y ↦ ?_⟩
      rw [← one_smul (K ⊗[A] B) x, ← one_smul (K ⊗[A] B) y, Subsingleton.elim (1 : K ⊗[A] B) 0,
        zero_smul, zero_smul]
    rw [finrank_zero_of_subsingleton, finrank_zero_of_subsingleton]

end Rank

section Content

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Invertible R M]

/-- In an invertible module, `φ(s) • m = φ(m) • s` for every linear form `φ`. -/
lemma Invertible.apply_smul_eq (φ : Module.Dual R M) (s m : M) : φ s • m = φ m • s := by
  have h := congrArg (fun x ↦ TensorProduct.lid R M (φ.rTensor M x))
    (Module.Invertible.tmul_comm (R := R) (m₁ := s) (m₂ := m))
  simpa using h

/-- **The content ideal of a section of an invertible module**: for `s ∈ M`, the ideal
`I = {φ(s) : φ ∈ Mᵛ}` satisfies `I • M = R ∙ s`. -/
lemma Invertible.range_eval_smul_top (s : M) :
    LinearMap.range (Module.Dual.eval R M s) • (⊤ : Submodule R M) = R ∙ s := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    rintro _ ⟨φ, rfl⟩ m -
    rw [Module.Dual.eval_apply, apply_smul_eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)
  · rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨t, ht⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
    have hs : Finsupp.linearCombination R id (t s) = s := LinearMap.congr_fun ht s
    have key : Finsupp.linearCombination R id (t s) ∈
        LinearMap.range (Module.Dual.eval R M s) • (⊤ : Submodule R M) := by
      rw [Finsupp.linearCombination_apply]
      exact Submodule.sum_mem _ fun y _ ↦
        Submodule.smul_mem_smul ⟨Finsupp.lapply y ∘ₗ t, rfl⟩ Submodule.mem_top
    rwa [hs] at key

end Content

section BaseChange

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- A base change along a surjective ring map `R → S` is surjective, with kernel
`ker(R → S) • M`. -/
lemma IsBaseChange.surjective_and_ker_eq {f : M →ₗ[R] N} (h : IsBaseChange S f)
    (hS : Surjective (algebraMap R S)) :
    Surjective f ∧ LinearMap.ker f = (RingHom.ker (algebraMap R S)) • (⊤ : Submodule R M) := by
  constructor
  · intro n
    refine h.inductionOn n (fun n ↦ n ∈ LinearMap.range f) (zero_mem _) (fun m ↦ ⟨m, rfl⟩) ?_
      (fun _ _ ↦ add_mem)
    rintro s _ ⟨m, rfl⟩
    obtain ⟨r, rfl⟩ := hS s
    exact ⟨r • m, by rw [map_smul, algebraMap_smul]⟩
  · apply le_antisymm
    · intro m hm
      let I := RingHom.ker (algebraMap R S)
      let e : (R ⧸ I) ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hS
      let ψ : S ⊗[R] M →ₗ[R] M ⧸ I • (⊤ : Submodule R M) :=
        (quotTensorEquivQuotSMul M I).toLinearMap ∘ₗ (e.symm.toLinearMap.rTensor M)
      have h1 : h.equiv.symm (f m) = 1 ⊗ₜ m := h.equiv_symm_apply m
      rw [LinearMap.mem_ker.mp hm, map_zero] at h1
      have h2 : ψ (1 ⊗ₜ m) = Submodule.Quotient.mk m := by
        simp only [ψ, LinearMap.coe_comp, comp_apply, LinearMap.rTensor_tmul,
          AlgEquiv.toLinearMap_apply, map_one, LinearEquiv.coe_coe]
        exact quotTensorEquivQuotSMul_mk_one_tmul I m
      rw [← h1, map_zero] at h2
      exact (Submodule.Quotient.mk_eq_zero _).mp h2.symm
    · rw [Submodule.smul_le]
      intro r hr m _
      rw [LinearMap.mem_ker, map_smul, ← algebraMap_smul S, RingHom.mem_ker.mp hr, zero_smul]

end BaseChange

end CurvesJacobian

namespace TwoCech

variable {A : Type*} [CommRing A]
variable {P Q R : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  [AddCommGroup R] [Module A R]
variable {P' Q' R' : Type*} [AddCommGroup P'] [Module A P'] [AddCommGroup Q'] [Module A Q']
  [AddCommGroup R'] [Module A R']
variable {f : P →ₗ[A] R} {g : Q →ₗ[A] R} {f' : P' →ₗ[A] R'} {g' : Q' →ₗ[A] R'}
variable {P'' Q'' R'' : Type*} [AddCommGroup P''] [Module A P''] [AddCommGroup Q'']
  [Module A Q''] [AddCommGroup R''] [Module A R'']
  {f'' : P'' →ₗ[A] R''} {g'' : Q'' →ₗ[A] R''}
  (α₁ : P' →ₗ[A] P) (β₁ : Q' →ₗ[A] Q) (γ₁ : R' →ₗ[A] R)
  (α₂ : P →ₗ[A] P'') (β₂ : Q →ₗ[A] Q'') (γ₂ : R →ₗ[A] R'')
  (hf₁ : f ∘ₗ α₁ = γ₁ ∘ₗ f') (hg₁ : g ∘ₗ β₁ = γ₁ ∘ₗ g')
  (hf₂ : f'' ∘ₗ α₂ = γ₂ ∘ₗ f) (hg₂ : g'' ∘ₗ β₂ = γ₂ ∘ₗ g)
  (hα : Exact α₁ α₂) (hβ : Exact β₁ β₂) (hγ : Exact γ₁ γ₂)
  (hα₂ : Surjective α₂) (hβ₂ : Surjective β₂) (hγ₁ : Injective γ₁)

/-- **The connecting map is an isomorphism** if `H⁰' → H⁰` is surjective and `H¹ = 0`: then
`H⁰'' ≅ H¹'` (from the six-term exact sequence). -/
theorem δ_bijective (h0 : Surjective (mapH0 α₁ β₁ γ₁ hf₁ hg₁)) (h1 : Subsingleton (H1 f g)) :
    Bijective (δ α₁ β₁ γ₁ α₂ β₂ γ₂ hf₁ hg₁ hf₂ hg₂ hα hβ hγ hα₂ hβ₂ hγ₁) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ :=
      (exact_mapH0_δ α₁ β₁ γ₁ α₂ β₂ γ₂ hf₁ hg₁ hf₂ hg₂ hα hβ hγ hα₂ hβ₂ hγ₁ x).mp hx
    obtain ⟨z, rfl⟩ := h0 y
    exact (exact_mapH0 α₁ β₁ γ₁ α₂ β₂ γ₂ hf₁ hg₁ hf₂ hg₂ hα hβ hγ₁).apply_apply_eq_zero z
  · intro y
    exact (exact_δ_mapH1 α₁ β₁ γ₁ α₂ β₂ γ₂ hf₁ hg₁ hf₂ hg₂ hα hβ hγ hα₂ hβ₂ hγ₁ y).mp
      (Subsingleton.elim _ _)

end TwoCech
