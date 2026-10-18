/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Galois descent for algebras with a semilinear Galois action

Let `L / k` be a finite Galois extension with group `G = Gal(L/k)` and `A` an `L`-algebra on which
`G` acts by ring automorphisms `ρ g`, semilinearly: `ρ g (l • a) = g l • ρ g a`. Let
`A^G = fixedAlg ρ hρ` be the `k`-subalgebra of invariants.

* `CurvesJacobian.GaloisDescent.sum_traceDual_mul`: for a `k`-basis `b` of `L` with trace-dual basis
  `b*`, `∑ᵢ g(b*ᵢ) bᵢ = δ_{g,1}` (Dedekind's independence of characters).
* `CurvesJacobian.GaloisDescent.eq_sum_traceSum`: `a = ∑ᵢ bᵢ • T(b*ᵢ • a)` with `T = ∑_g ρ g`.
* `CurvesJacobian.GaloisDescent.mem_fixedAlg_iff_exists_traceSum`: `A^G = T(A)`.
* **`CurvesJacobian.GaloisDescent.descentEquiv`** (Speiser): `L ⊗_k A^G ≃ₐ[L] A`,
  `l ⊗ a ↦ l • a`.
* `CurvesJacobian.GaloisDescent.mem_fixedAlg_tensor_iff`: for a `k`-algebra `R`, the invariants of
  `L ⊗_k R` under `g ⊗ id` (`tensorAction`) are `1 ⊗ R`.
-/

open TensorProduct

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]

open Classical in
/-- **Dedekind**: for a `k`-basis `b` of `L` with trace-dual basis `b*`,
`∑ᵢ g(b*ᵢ) bᵢ = 1` if `g = 1` and `= 0` otherwise. -/
theorem sum_traceDual_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k L)
    (g : Gal(L/k)) :
    ∑ i, g (b.traceDual i) * b i = if g = 1 then 1 else 0 := by
  classical
  -- `x = ∑_g g(x) c_g` with `c_g = ∑ᵢ g(b*ᵢ) bᵢ`
  have hx : ∀ x : L, x = ∑ h : Gal(L/k), (∑ i, h (b.traceDual i) * b i) * h x := by
    intro x
    have h1 : x = ∑ i, Algebra.trace k L (x * b.traceDual i) • b i := by
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      have := b.traceDual.traceDual_repr_apply x i
      rw [Module.Basis.traceDual_traceDual] at this
      rw [this]
      rfl
    have h2 : ∀ i, Algebra.trace k L (x * b.traceDual i) • b i =
        ∑ h : Gal(L/k), h (b.traceDual i) * b i * h x := by
      intro i
      rw [Algebra.smul_def, trace_eq_sum_automorphisms, Finset.sum_mul]
      refine Finset.sum_congr rfl fun h _ ↦ ?_
      rw [map_mul]
      ring
    conv_lhs => rw [h1]
    rw [Finset.sum_congr rfl fun i _ ↦ h2 i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [Finset.sum_mul]
  -- linear independence of the automorphisms over `L`
  let f : Gal(L/k) → (L →ₗ[k] L) := fun h ↦ (h : L →ₐ[k] L).toLinearMap
  have hli : LinearIndependent L f :=
    (linearIndependent_toLinearMap k L L).comp (fun h : Gal(L/k) ↦ (h : L →ₐ[k] L))
      fun h₁ h₂ e ↦ AlgEquiv.coe_toAlgHom_injective e
  have hsum : ∑ h : Gal(L/k), ((∑ i, h (b.traceDual i) * b i) - if h = 1 then 1 else 0) • f h =
      0 := by
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simp only [LinearMap.smul_apply, f, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
      smul_eq_mul, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, AlgEquiv.one_apply]
    rw [← hx x, sub_self]
  have := (Fintype.linearIndependent_iff.mp hli) _ hsum g
  exact sub_eq_zero.mp this

section Descent

variable {A : Type*} [CommRing A] [Algebra L A] [Algebra k A] [IsScalarTower k L A]
  (ρ : Gal(L/k) →* RingAut A) (hρ : ∀ g l, ρ g (algebraMap L A l) = algebraMap L A (g l))

omit [FiniteDimensional k L] [IsGalois k L] [Algebra k A] [IsScalarTower k L A] in
include hρ in
/-- The action is semilinear. -/
lemma map_smul' (g : Gal(L/k)) (l : L) (a : A) : ρ g (l • a) = g l • ρ g a := by
  rw [Algebra.smul_def, map_mul, hρ, ← Algebra.smul_def]

include hρ in
/-- **The `k`-algebra of invariants** `A^G`. -/
def fixedAlg : Subalgebra k A where
  carrier := {a | ∀ g, ρ g a = a}
  mul_mem' {a b} ha hb g := by simp only [map_mul, ha g, hb g]
  add_mem' {a b} ha hb g := by simp only [map_add, ha g, hb g]
  algebraMap_mem' c g := by
    rw [IsScalarTower.algebraMap_apply k L A, hρ, AlgEquiv.commutes]

omit [FiniteDimensional k L] [IsGalois k L] in
lemma mem_fixedAlg {a : A} : a ∈ fixedAlg ρ hρ ↔ ∀ g, ρ g a = a := Iff.rfl

/-- The trace `T(a) = ∑_g ρ g a`. -/
def traceSum (a : A) : A := ∑ g : Gal(L/k), ρ g a

omit [IsGalois k L] in
lemma traceSum_mem (a : A) : traceSum ρ a ∈ fixedAlg ρ hρ := fun h ↦ by
  simp only [traceSum, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g ↦ by
    rw [Equiv.coe_mulLeft, map_mul, RingAut.mul_apply]

omit [IsGalois k L] [Algebra L A] [Algebra k A] [IsScalarTower k L A] in
lemma traceSum_add (a a' : A) : traceSum ρ (a + a') = traceSum ρ a + traceSum ρ a' := by
  simp only [traceSum, map_add, Finset.sum_add_distrib]

include hρ in
/-- For `β ∈ A^G`, `T(l • β) = Tr_{L/k}(l) • β`. -/
lemma traceSum_smul_of_mem (l : L) {β : A} (hβ : β ∈ fixedAlg ρ hρ) :
    traceSum ρ (l • β) = Algebra.trace k L l • β := by
  simp only [traceSum, map_smul' ρ hρ]
  rw [Finset.sum_congr rfl fun g _ ↦ by rw [hβ g], ← Finset.sum_smul,
    ← trace_eq_sum_automorphisms, algebraMap_smul]

omit [Algebra k A] [IsScalarTower k L A] in
include hρ in
/-- **Every element is a combination of invariants**: `a = ∑ᵢ bᵢ • T(b*ᵢ • a)`. -/
theorem eq_sum_traceSum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k L)
    (a : A) : a = ∑ i, b i • traceSum ρ (b.traceDual i • a) := by
  classical
  simp only [traceSum, map_smul' ρ hρ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have h : ∀ g : Gal(L/k), (∑ i, b i * g (b.traceDual i)) • ρ g a =
      if g = 1 then a else 0 := by
    intro g
    rw [show ∑ i, b i * g (b.traceDual i) = ∑ i, g (b.traceDual i) * b i from
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _, sum_traceDual_mul b g]
    split_ifs with hg
    · rw [hg, one_smul, map_one, RingAut.one_apply]
    · rw [zero_smul]
  rw [Finset.sum_congr rfl fun g _ ↦ h g, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

include hρ in
/-- An invariant element is a trace: `β = T(l₀ • β)` for any `l₀` with `Tr_{L/k}(l₀) = 1`. -/
lemma eq_traceSum_of_mem {β : A} (hβ : β ∈ fixedAlg ρ hρ) {l₀ : L}
    (hl₀ : Algebra.trace k L l₀ = 1) : β = traceSum ρ (l₀ • β) := by
  rw [traceSum_smul_of_mem ρ hρ l₀ hβ, hl₀, one_smul]

/-- **The invariants are exactly the traces**: `A^G = T(A)`. -/
lemma mem_fixedAlg_iff_exists_traceSum {β : A} :
    β ∈ fixedAlg ρ hρ ↔ ∃ a, traceSum ρ a = β := by
  refine ⟨fun hβ ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ traceSum_mem ρ hρ a⟩
  obtain ⟨l₀, hl₀⟩ := Algebra.trace_surjective k L 1
  exact ⟨l₀ • β, (eq_traceSum_of_mem ρ hρ hβ hl₀).symm⟩

/-- The multiplication map `L ⊗_k A^G ⟶ A`, `l ⊗ a ↦ l • a`. -/
def descentHom : L ⊗[k] fixedAlg ρ hρ →ₐ[L] A :=
  Algebra.TensorProduct.lift (Algebra.ofId L A) (fixedAlg ρ hρ).val fun _ _ ↦ Commute.all _ _

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
lemma descentHom_tmul (l : L) (β : fixedAlg ρ hρ) :
    descentHom ρ hρ (l ⊗ₜ β) = l • (β : A) := by
  rw [descentHom, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

lemma surjective_descentHom : Function.Surjective (descentHom ρ hρ) := by
  classical
  intro a
  let b := Module.finBasis k L
  refine ⟨∑ i, b i ⊗ₜ ⟨traceSum ρ (b.traceDual i • a), traceSum_mem ρ hρ _⟩, ?_⟩
  rw [map_sum]
  simp only [descentHom_tmul]
  exact (eq_sum_traceSum ρ hρ b a).symm

lemma injective_descentHom : Function.Injective (descentHom ρ hρ) := by
  classical
  let b := Module.finBasis k L
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := fixedAlg ρ hρ) b
  have key : ∀ (z : L ⊗[k] fixedAlg ρ hρ) (j : Fin (Module.finrank k L)),
      ((E z j : fixedAlg ρ hρ) : A) = traceSum ρ (b.traceDual j • descentHom ρ hρ z) := by
    intro z j
    induction z with
    | zero => simp [traceSum]
    | tmul l β =>
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, descentHom_tmul, smul_smul,
        traceSum_smul_of_mem ρ hρ _ β.2, Subalgebra.coe_smul]
      congr 1
      have := b.traceDual.traceDual_repr_apply l j
      rw [Module.Basis.traceDual_traceDual] at this
      rw [this, mul_comm]
      rfl
    | add z z' hz hz' =>
      rw [map_add, Finsupp.add_apply, Subalgebra.coe_add, hz, hz', map_add, smul_add,
        traceSum_add]
  refine (injective_iff_map_eq_zero (descentHom ρ hρ)).mpr fun z hz' ↦ ?_
  apply E.injective
  rw [map_zero]
  ext j
  rw [Finsupp.zero_apply, key, hz', smul_zero]
  simp [traceSum]

/-- **Galois descent for algebras** (Speiser): `L ⊗_k A^G ≃ₐ[L] A`. -/
def descentEquiv : L ⊗[k] fixedAlg ρ hρ ≃ₐ[L] A :=
  AlgEquiv.ofBijective (descentHom ρ hρ) ⟨injective_descentHom ρ hρ, surjective_descentHom ρ hρ⟩

@[simp]
lemma descentEquiv_tmul (l : L) (β : fixedAlg ρ hρ) :
    descentEquiv ρ hρ (l ⊗ₜ β) = l • (β : A) :=
  descentHom_tmul ρ hρ l β

end Descent

section Tensor

variable (R : Type*) [CommRing R] [Algebra k R]

/-- The action `g ⊗ id` of `Gal(L/k)` on `L ⊗_k R`. -/
def tensorAction : Gal(L/k) →* RingAut (L ⊗[k] R) where
  toFun g := (Algebra.TensorProduct.congr g (AlgEquiv.refl : R ≃ₐ[k] R)).toRingEquiv
  map_one' := by
    apply RingEquiv.ext
    intro x
    change Algebra.TensorProduct.congr (1 : Gal(L/k)) AlgEquiv.refl x = x
    rw [show (1 : Gal(L/k)) = AlgEquiv.refl from rfl, Algebra.TensorProduct.congr_refl]
    rfl
  map_mul' g h := by
    apply RingEquiv.ext
    intro x
    change Algebra.TensorProduct.congr (g * h) AlgEquiv.refl x =
      Algebra.TensorProduct.congr g AlgEquiv.refl (Algebra.TensorProduct.congr h AlgEquiv.refl x)
    rw [show g * h = h.trans g from rfl, show (AlgEquiv.refl : R ≃ₐ[k] R) =
      AlgEquiv.refl.trans AlgEquiv.refl from rfl, Algebra.TensorProduct.congr_trans]
    rfl

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
lemma tensorAction_tmul (g : Gal(L/k)) (l : L) (r : R) :
    tensorAction R g (l ⊗ₜ r) = g l ⊗ₜ r := rfl

omit [FiniteDimensional k L] [IsGalois k L] in
lemma tensorAction_algebraMap (g : Gal(L/k)) (l : L) :
    tensorAction R g (algebraMap L (L ⊗[k] R) l) = algebraMap L (L ⊗[k] R) (g l) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    tensorAction_tmul]
  rfl

/-- **The invariants of `L ⊗_k R` are `R`**: `z` is `Gal(L/k)`-invariant iff `z = 1 ⊗ r`. -/
theorem mem_fixedAlg_tensor_iff (z : L ⊗[k] R) :
    z ∈ fixedAlg (tensorAction R) (tensorAction_algebraMap R) ↔ ∃ r : R, z = 1 ⊗ₜ r := by
  constructor
  · intro hz
    obtain ⟨a, rfl⟩ := (mem_fixedAlg_iff_exists_traceSum _ _).mp hz
    induction a with
    | zero => exact ⟨0, by simp [traceSum]⟩
    | tmul l r =>
      refine ⟨Algebra.trace k L l • r, ?_⟩
      simp only [traceSum, tensorAction_tmul]
      rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | add a a' ha ha' =>
      obtain ⟨r, hr⟩ := ha (traceSum_mem _ _ a)
      obtain ⟨r', hr'⟩ := ha' (traceSum_mem _ _ a')
      exact ⟨r + r', by rw [traceSum_add, hr, hr', TensorProduct.tmul_add]⟩
  · rintro ⟨r, rfl⟩ g
    rw [tensorAction_tmul, map_one]

end Tensor

end CurvesJacobian.GaloisDescent
