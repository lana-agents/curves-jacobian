/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Flat.Stability


/-!
# Fibrewise injectivity of `r ↦ r • s` is universal

Let `R` be a commutative ring which is a finite projective `A[X]`-algebra, `M` an invertible
`R`-module and `s : M`. Write `smulS s : R →ₗ[A] M` for `r ↦ r • s`. This file proves, by
pure commutative algebra, the algebraic input for showing that the zero scheme of a section of an
invertible sheaf on a relative curve is a relative effective Cartier divisor (used in the proof of
Stacks, Tag 0B9X); it replaces the fibrewise flatness criterion, which is not in Mathlib.

* `injective_lTensor_of_fibres`: if `smulS s` is injective after `κ(p) ⊗[A] -` for every prime
  `p` of `A`, then it is injective after `N ⊗[A] -` for every `A`-module `N`;
* `smul_injective_of_fibres`: hence `s` is a nonzerodivisor;
* `flat_quotient_of_fibres`: hence `M ⧸ R s` is flat over `A`;
* `injective_lTensor_of_isDomain`: the fibre hypothesis holds when `K ⊗[A] R` is a domain and
  `1 ⊗ s ≠ 0` (only `M` projective over `R` is needed).

## Proof

Let `x` be in the kernel of `R ⊗[A] N → M ⊗[A] N` and `p` a prime of `A`. Localising at the
prime `P = p A[X]` (the generic point of `𝔸¹_{κ(p)}`), `R_P` is finite over the local ring
`A[X]_P`, hence semilocal, so `M_P ≅ R_P` and `s = t • e`. The fibre hypothesis and Nakayama
show that `t` is a unit of `R_P` (`isUnit_of_injective_rTensor`), so `x` is killed by some
`b ∉ P`. A localised McCoy theorem for modules (`exists_smul_eq_zero_of_projective`, proved via
`TrivSqZeroExt` and `Polynomial.eq_zero_of_mul_eq_zero_of_smul`) turns `b` into some `a ∈ A \ p`
with `a • x = 0`. As `p` is arbitrary, `x = 0`.
-/

open Polynomial TensorProduct

namespace CurvesJacobian.FibreFlat

universe u

section McCoy

variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]

/-- McCoy's theorem, localised at a prime: if some coefficient of `d : A[X]` lies outside `p` and
`d * g = 0` in `T[X]` for an `A`-algebra `T`, then `g` is killed by an element of `A \ p`. -/
theorem exists_smul_eq_zero_of_mul_eq_zero {T : Type u} [CommRing T] [Algebra A T] {d : A[X]}
    {i : ℕ} (hi : d.coeff i ∉ p) {g : T[X]} (hg : d.map (algebraMap A T) * g = 0) :
    ∃ a ∉ p, a • g = 0 := by
  classical
  let S := Algebra.algebraMapSubmonoid T p.primeCompl
  let T' := Localization S
  have hmap : (d.map (algebraMap A T')) * g.map (algebraMap T T') = 0 := by
    rw [IsScalarTower.algebraMap_eq A T T', ← Polynomial.map_map, ← Polynomial.map_mul, hg,
      Polynomial.map_zero]
  have hunit : IsUnit (algebraMap A T' (d.coeff i)) := by
    rw [IsScalarTower.algebraMap_apply A T T']
    exact IsLocalization.map_units T' (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
      (⟨d.coeff i, hi⟩ : p.primeCompl)⟩ : S)
  have h0 := Polynomial.eq_zero_of_mul_eq_zero_of_smul _ (fun r hr ↦ by
    have := congr($hr |>.coeff i)
    rw [coeff_smul, coeff_map, smul_eq_mul, coeff_zero] at this
    exact (hunit.mul_left_eq_zero).mp this) _ hmap
  have hc : ∀ n, ∃ a ∉ p, algebraMap A T a * g.coeff n = 0 := by
    intro n
    have : algebraMap T T' (g.coeff n) = 0 := by simpa using congr($h0 |>.coeff n)
    obtain ⟨⟨_, a, ha, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff S T' _).mp this
    exact ⟨a, ha, h⟩
  choose a ha hag using hc
  refine ⟨∏ n ∈ g.support, a n, ?_, ?_⟩
  · exact Ideal.IsPrime.prod_mem_iff.not.mpr (by simpa using fun n _ ↦ ha n)
  · ext n
    rw [coeff_smul, coeff_zero, Algebra.smul_def, map_prod]
    by_cases hn : n ∈ g.support
    · rw [← Finset.prod_erase_mul _ _ hn, mul_assoc, hag, mul_zero]
    · rw [notMem_support_iff.mp hn, mul_zero]

/-- McCoy's theorem for modules, localised at a prime: if some coefficient of `d : A[X]` lies
outside `p` and `d • y = 0` for `y : A[X] ⊗[A] N`, then `y` is killed by an element of
`A \ p`. -/
theorem exists_smul_eq_zero_tensor {N : Type u} [AddCommGroup N] [Module A N] {d : A[X]}
    {i : ℕ} (hi : d.coeff i ∉ p) {y : A[X] ⊗[A] N} (hy : d • y = 0) :
    ∃ a ∉ p, a • y = 0 := by
  letI : Module Aᵐᵒᵖ N := Module.compHom N (RingEquiv.toOpposite A).symm.toRingHom
  haveI : IsCentralScalar A N := ⟨fun _ _ ↦ rfl⟩
  let T := TrivSqZeroExt A N
  let ι : N →ₗ[A] T := TrivSqZeroExt.inrHom A N
  let e := (polyEquivTensor A T).symm
  let Ψ : A[X] ⊗[A] N →ₗ[A] T[X] :=
    e.toLinearMap ∘ₗ (TensorProduct.comm A A[X] T).toLinearMap ∘ₗ ι.lTensor A[X]
  have hΨ : Function.Injective Ψ := by
    have h1 : Function.Injective (ι.lTensor A[X]) := by
      refine Function.LeftInverse.injective
        (g := (TrivSqZeroExt.sndHom A N).lTensor A[X]) fun z ↦ ?_
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have : (TrivSqZeroExt.sndHom A N).comp ι = LinearMap.id := by ext n; simp [ι]
      rw [this, LinearMap.lTensor_id, LinearMap.id_apply]
    exact e.injective.comp ((TensorProduct.comm A A[X] T).injective.comp h1)
  have hmul : ∀ z : A[X] ⊗[A] N, Ψ (d • z) = d.map (algebraMap A T) * Ψ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul f n =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      simp only [Ψ, e, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.comm_tmul, AlgEquiv.toLinearMap_apply,
        polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.map_mul, mul_smul_comm]
    | add z w hz hw => simp only [smul_add, map_add, hz, hw, mul_add]
  obtain ⟨a, ha, h⟩ := exists_smul_eq_zero_of_mul_eq_zero p hi (by rw [← hmul, hy, map_zero])
  exact ⟨a, ha, hΨ (by rw [map_smul, h, map_zero])⟩

/-- McCoy's theorem for `R ⊗[A] N` with `R` projective over `A[X]`. -/
theorem exists_smul_eq_zero_of_projective {N : Type u} [AddCommGroup N] [Module A N]
    (R : Type u) [AddCommGroup R] [Module A[X] R] [Module A R] [IsScalarTower A A[X] R]
    [Module.Projective A[X] R] {d : A[X]} {i : ℕ} (hi : d.coeff i ∉ p) {x : R ⊗[A] N}
    (hx : d • x = 0) : ∃ a ∉ p, a • x = 0 := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A[X] R›
  let σ : R ⊗[A] N →ₗ[A[X]] R →₀ (A[X] ⊗[A] N) :=
    (TensorProduct.finsuppLeft A A[X] A[X] N R).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.rTensor A N s
  have hσ : Function.Injective σ := by
    refine (TensorProduct.finsuppLeft A A[X] A[X] N R).injective.comp ?_
    refine Function.LeftInverse.injective (g := TensorProduct.AlgebraTensorModule.rTensor A N
      (Finsupp.linearCombination A[X] id)) fun z ↦ ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r n =>
      rw [TensorProduct.AlgebraTensorModule.rTensor_tmul,
        TensorProduct.AlgebraTensorModule.rTensor_tmul, ← LinearMap.comp_apply
        (Finsupp.linearCombination A[X] id) s, hs, LinearMap.id_apply]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  have hc : ∀ r, ∃ a ∉ p, a • σ x r = 0 := fun r ↦
    exists_smul_eq_zero_tensor p hi (by
      rw [← Finsupp.smul_apply, ← map_smul, hx, map_zero, Finsupp.zero_apply])
  choose a ha hax using hc
  refine ⟨∏ r ∈ (σ x).support, a r, ?_, hσ ?_⟩
  · exact Ideal.IsPrime.prod_mem_iff.not.mpr (by simpa using fun r _ ↦ ha r)
  · rw [LinearMap.map_smul_of_tower, map_zero]
    ext r
    rw [Finsupp.smul_apply, Finsupp.zero_apply]
    by_cases hr : r ∈ (σ x).support
    · rw [← Finset.prod_erase_mul _ _ hr, mul_smul, hax, smul_zero]
    · rw [Finsupp.notMem_support_iff.mp hr, smul_zero]

end McCoy

/-- A finite algebra over a local ring is semilocal. -/
theorem finite_maximalSpectrum_of_finite (B S : Type*) [CommRing B] [IsLocalRing B] [CommRing S]
    [Algebra B S] [Module.Finite B S] : Finite (MaximalSpectrum S) := by
  have := (Algebra.QuasiFinite.finite_primesOver (R := B) (S := S)
    (IsLocalRing.maximalIdeal B)).to_subtype
  refine Finite.of_injective (fun Q : MaximalSpectrum S ↦
    (⟨Q.asIdeal, Q.isMaximal.isPrime, ⟨?_⟩⟩ : (IsLocalRing.maximalIdeal B).primesOver S)) ?_
  · have := Q.isMaximal
    exact (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under B Q.asIdeal)).symm
  · intro Q Q' h
    exact MaximalSpectrum.ext (congr_arg Subtype.val h)


open TensorProduct.AlgebraTensorModule in
/-- A Nakayama-type step: let `B` be a local `A`-algebra, `R` a finite flat `B`-algebra and `K` an
`A`-algebra such that `B ⊗[A] K` is nonzero and the maximal ideal of `B` dies in it. If `t : R`
acts injectively on `R ⊗[A] K`, then `t` is a unit. -/
theorem isUnit_of_injective_rTensor {A B R K : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
    [CommRing R] [CommRing K] [Algebra A B] [Algebra B R] [Algebra A R] [IsScalarTower A B R]
    [Algebra A K] [Module.Finite B R] [Module.Flat B R]
    (hker : ∀ b ∈ IsLocalRing.maximalIdeal B, algebraMap B (B ⊗[A] K) b = 0)
    (hD : Nontrivial (B ⊗[A] K)) {t : R}
    (ht : Function.Injective ((LinearMap.mulLeft A t).rTensor K)) : IsUnit t := by
  let j : IsLocalRing.ResidueField B →ₐ[B] B ⊗[A] K :=
    Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal B) (Algebra.ofId B _) hker
  have hj : Function.Injective j := j.toRingHom.injective
  let χ : IsLocalRing.ResidueField B ⊗[B] R →ₗ[B] R ⊗[A] K :=
    (cancelBaseChange A B B R K).toLinearMap ∘ₗ
      (TensorProduct.comm B (B ⊗[A] K) R).toLinearMap ∘ₗ (j.toLinearMap.rTensor R)
  have hχ : Function.Injective χ :=
    (cancelBaseChange A B B R K).injective.comp
      ((TensorProduct.comm B (B ⊗[A] K) R).injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap _ hj))
  have hcomm : ∀ z, χ ((LinearMap.mulLeft B t).baseChange (IsLocalRing.ResidueField B) z) =
      (LinearMap.mulLeft A t).rTensor K (χ z) := fun z ↦ by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul f r =>
      simp only [χ, LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.comm_tmul, LinearMap.mulLeft_apply]
      generalize j.toLinearMap f = w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b k => simp [cancelBaseChange_tmul]
      | add w w' hw hw' =>
        rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, map_add, hw, hw']
    | add z w hz hw => simp only [map_add, hz, hw]
  have htF : Function.Surjective
      ((LinearMap.mulLeft B t).baseChange (IsLocalRing.ResidueField B)) := by
    refine LinearMap.injective_iff_surjective.mp fun z z' hzz ↦ hχ (ht ?_)
    rw [← hcomm, ← hcomm, hzz]
  have hrange : LinearMap.range (LinearMap.mulLeft B t) = ⊤ := by
    rw [← IsLocalRing.map_tensorProduct_mk_eq_top, eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := htF z
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f r =>
      obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective f
      rw [LinearMap.baseChange_tmul]
      have : IsLocalRing.residue B b ⊗ₜ[B] (LinearMap.mulLeft B t r) =
          b • TensorProduct.mk B (IsLocalRing.ResidueField B) R 1 (LinearMap.mulLeft B t r) := by
        rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem ⟨r, rfl⟩)
    | add z w hz hw =>
      rw [map_add]
      exact Submodule.add_mem _ (hz Submodule.mem_top) (hw Submodule.mem_top)
  obtain ⟨u, hu⟩ := LinearMap.range_eq_top.mp hrange 1
  exact ⟨⟨t, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩

section Main

variable {A : Type u} [CommRing A] {R : Type u} [CommRing R] [Algebra A R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] (s : M)

/-- `r ↦ r • s`, as an `A`-linear map `R → M`. -/
abbrev smulS : R →ₗ[A] M := (LinearMap.toSpanSingleton R M s).restrictScalars A

theorem lTensor_eq_comm (N : Type u) [AddCommGroup N] [Module A N] :
    (smulS (A := A) (R := R) s).lTensor N = (TensorProduct.comm A M N).toLinearMap ∘ₗ
      (smulS (A := A) (R := R) s).rTensor N ∘ₗ (TensorProduct.comm A N R).toLinearMap :=
  (LinearMap.comm_comp_rTensor_comp_comm_eq _).symm

theorem injective_lTensor_iff (N : Type u) [AddCommGroup N] [Module A N] :
    Function.Injective ((smulS (A := A) (R := R) s).lTensor N) ↔
      Function.Injective ((smulS (A := A) (R := R) s).rTensor N) := by
  rw [lTensor_eq_comm, LinearMap.coe_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]

variable [Algebra A[X] R] [IsScalarTower A A[X] R] [Module.Finite A[X] R]
  [Module.Projective A[X] R] [Module.Invertible R M]

set_option maxHeartbeats 1000000 in
-- elaborating `(LinearMap.mulLeft A t).rTensor K` on `R' = B' ⊗[A[X]] R` is slow
open TensorProduct.AlgebraTensorModule in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The local step: if the fibre of `r ↦ r • s` over `p` is injective, then every element of the
kernel of `R ⊗[A] N → M ⊗[A] N` is killed by some `b ∈ A[X] \ p A[X]`. The proof shows that
`s` generates `M` at the generic point `p A[X]` of the fibre `𝔸¹_{κ(p)}`. -/
theorem exists_smul_eq_zero_of_rTensor_residueField (p : Ideal A) [p.IsPrime]
    (hfib : Function.Injective ((smulS (A := A) (R := R) s).rTensor p.ResidueField))
    {N : Type u} [AddCommGroup N] [Module A N] {x : R ⊗[A] N}
    (hx : (smulS (A := A) (R := R) s).rTensor N x = 0) :
    ∃ b : A[X], b ∉ p.map C ∧ b • x = 0 := by
  set P : Ideal A[X] := p.map C
  let B' := Localization.AtPrime P
  let R' := B' ⊗[A[X]] R
  let S := Algebra.algebraMapSubmonoid R P.primeCompl
  have : IsLocalization S R' := IsLocalization.tensorRight _ _
  haveI : IsScalarTower A R R' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply A A[X] B',
      Algebra.algebraMap_eq_smul_one (algebraMap A A[X] a), TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]
    rfl
  have : Finite (MaximalSpectrum R') := finite_maximalSpectrum_of_finite B' R'
  let e : R' ⊗[R] M ≃ₗ[R'] R' :=
    (Module.Invertible.free_iff_linearEquiv.mp inferInstance).some
  let h : M →ₗ[R] R' := (e.toLinearMap.restrictScalars R) ∘ₗ TensorProduct.mk R R' M 1
  set t : R' := h s with ht
  have hh : ∀ r : R, h (r • s) = t * algebraMap R R' r := fun r ↦ by
    rw [map_smul, Algebra.smul_def, mul_comm]
  -- Step 1: `t` acts injectively on `R' ⊗[A] κ(p)`.
  let K := p.ResidueField
  let tK := rTensor A K (LinearMap.mulLeft R t)
  have htK : Function.Injective tK := by
    let ιRK := rTensor A K (Algebra.linearMap R R')
    let ιMK := rTensor A K (TensorProduct.mk R R' M 1)
    let φK := rTensor A K (LinearMap.toSpanSingleton R M s)
    let eK := rTensor A K (e.toLinearMap.restrictScalars R)
    have hφK : ∀ z, φK z = (smulS (A := A) (R := R) s).rTensor K z := fun z ↦ by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r k => rfl
      | add z w hz hw => rw [map_add, map_add, hz, hw]
    have comm1 : ∀ z, tK (ιRK z) = eK (ιMK (φK z)) := fun z ↦ by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r k =>
        simp only [tK, ιRK, ιMK, φK, eK, rTensor_tmul, LinearMap.mulLeft_apply,
          Algebra.linearMap_apply, LinearMap.toSpanSingleton_apply, TensorProduct.mk_apply,
          LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
        rw [← hh r]
        rfl
      | add z w hz hw => simp only [map_add, hz, hw]
    have heK : Function.Injective eK := Function.LeftInverse.injective
      (g := rTensor A K (e.symm.toLinearMap.restrictScalars R)) fun z ↦ by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul r k => simp [eK]
        | add z w hz hw => rw [map_add, map_add, hz, hw]
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨y0, c⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S ιRK y
    have h1 : tK (ιRK y0) = 0 := by
      rw [← IsLocalizedModule.mk'_cancel' ιRK y0 c, Submonoid.smul_def, map_smul]
      simp only [Function.uncurry_apply_pair] at hy
      rw [hy, smul_zero]
    rw [comm1] at h1
    obtain ⟨c', hc'⟩ := (IsLocalizedModule.eq_zero_iff S ιMK).mp (heK (by rw [h1, map_zero]))
    have h3 : c' • y0 = 0 := by
      apply hfib
      rw [← hφK, Submonoid.smul_def, map_smul, ← Submonoid.smul_def, hc', map_zero]
    exact (IsLocalizedModule.mk'_eq_zero' ιRK c).mpr ⟨c', h3⟩
  -- Step 2: `D = B' ⊗[A] κ(p)` is nonzero and receives `B' ⧸ 𝔪`; so `t` is a unit.
  let F := IsLocalRing.ResidueField B'
  let D := B' ⊗[A] K
  have hP : IsLocalRing.maximalIdeal B' = p.map (algebraMap A B') := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P B', Ideal.map_map,
      ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hker : ∀ b ∈ IsLocalRing.maximalIdeal B', algebraMap B' D b = 0 := by
    rw [hP]
    intro b hb
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ h1 h2 ↦ by rw [map_add, h1, h2, add_zero])
      (fun c _ _ h ↦ by rw [smul_eq_mul, map_mul, h, mul_zero]) hb
    rintro _ ⟨a, ha, rfl⟩
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.TensorProduct.one_def,
      ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one,
      Ideal.algebraMap_residueField_eq_zero.mpr ha, TensorProduct.tmul_zero]
  have hD : Nontrivial D := by
    have hunit : ∀ a ∉ p, IsUnit (algebraMap A F a) := fun a ha ↦ by
      have hCa : C a ∈ P.primeCompl := fun hCa ↦
        ha (by simpa using Ideal.mem_map_C_iff.mp hCa 0)
      rw [IsScalarTower.algebraMap_apply A B' F, IsScalarTower.algebraMap_apply A A[X] B',
        Polynomial.algebraMap_eq]
      exact (IsLocalization.map_units B' (⟨C a, hCa⟩ : P.primeCompl)).map (algebraMap B' F)
    let g : K →ₐ[A] F := Ideal.ResidueField.liftₐ p (Algebra.ofId A F)
      (fun a ha ↦ by
        change algebraMap A F a = 0
        rw [IsScalarTower.algebraMap_apply A B' F, IsLocalRing.ResidueField.algebraMap_eq,
          IsLocalRing.residue_eq_zero_iff, hP]
        exact Ideal.mem_map_of_mem _ ha)
      (fun a ha ↦ hunit a ha)
    exact (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A B' F) g
      fun _ _ ↦ Commute.all _ _).toRingHom.domain_nontrivial
  have htK' : Function.Injective ((LinearMap.mulLeft A t).rTensor K) := by
    have : ∀ z, (LinearMap.mulLeft A t).rTensor K z = tK z := fun z ↦ by
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul r k => rfl
      | add z w hz hw => rw [map_add, map_add, hz, hw]
    intro z z' hzz
    exact htK (by rw [← this, ← this, hzz])
  obtain ⟨u, hu⟩ := (isUnit_of_injective_rTensor (B := B') hker hD htK').exists_right_inv
  -- Step 5: conclude.
  let ιN := rTensor A N (Algebra.linearMap R R')
  have hxN : rTensor A N (LinearMap.mulLeft R t) (ιN x) = 0 := by
    have : ∀ z, rTensor A N (LinearMap.mulLeft R t) (ιN z) =
        rTensor A N h ((smulS (A := A) (R := R) s).rTensor N z) := fun z ↦ by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r n =>
        simp only [ιN, rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply,
          Algebra.linearMap_apply, LinearMap.restrictScalars_apply,
          LinearMap.toSpanSingleton_apply, hh]
      | add z w hz hw => simp only [map_add, hz, hw]
    rw [this, hx, map_zero]
  have hιN : ιN x = 0 := by
    have : ∀ z, rTensor A N (LinearMap.mulLeft R u) (rTensor A N (LinearMap.mulLeft R t) z) = z :=
      fun z ↦ by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul r n => simp [rTensor_tmul, ← mul_assoc, mul_comm u t, hu]
        | add z w hz hw => rw [map_add, map_add, hz, hw]
    rw [← this (ιN x), hxN, map_zero]
  obtain ⟨⟨c, hc⟩, hcx⟩ := (IsLocalizedModule.eq_zero_iff S ιN).mp hιN
  obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hc
  exact ⟨b, hb, by rw [← algebraMap_smul R b x]; exact hcx⟩


/-- **Fibrewise criterion** (part of Stacks, Tag 0B9X): if `r ↦ r • s` is injective on every
fibre `κ(p) ⊗[A] R → κ(p) ⊗[A] M`, then it stays injective after tensoring with any
`A`-module. -/
theorem injective_lTensor_of_fibres
    (hfib : ∀ (p : Ideal A) [p.IsPrime],
      Function.Injective ((smulS (A := A) (R := R) s).lTensor p.ResidueField))
    (N : Type u) [AddCommGroup N] [Module A N] :
    Function.Injective ((smulS (A := A) (R := R) s).lTensor N) := by
  rw [injective_lTensor_iff, injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  let I : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A (R ⊗[A] N) x)
  have hI : I ≠ ⊤ := fun h ↦ hx0 (by
    simpa [I] using (LinearMap.mem_ker (f := LinearMap.toSpanSingleton A (R ⊗[A] N) x)).mp
      (h ▸ Submodule.mem_top : (1 : A) ∈ I))
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨b, hb, hbx⟩ := exists_smul_eq_zero_of_rTensor_residueField s p
    ((injective_lTensor_iff s _).mp (hfib p)) hx
  obtain ⟨i, hi⟩ : ∃ i, b.coeff i ∉ p := by
    by_contra! h
    exact hb (Ideal.mem_map_C_iff.mpr h)
  obtain ⟨a, ha, hax⟩ := exists_smul_eq_zero_of_projective p R hi hbx
  exact ha (hIp (by simpa [I] using hax))

/-- Under the fibre hypothesis, `s` is a nonzerodivisor: `r ↦ r • s` is injective. -/
theorem smul_injective_of_fibres
    (hfib : ∀ (p : Ideal A) [p.IsPrime],
      Function.Injective ((smulS (A := A) (R := R) s).lTensor p.ResidueField)) :
    Function.Injective fun r : R ↦ r • s := by
  intro r r' h
  have := injective_lTensor_of_fibres s hfib A
    (show (smulS (A := A) (R := R) s).lTensor A ((1 : A) ⊗ₜ r) =
      (smulS (A := A) (R := R) s).lTensor A ((1 : A) ⊗ₜ r') by
      simpa using congr((1 : A) ⊗ₜ[A] $h))
  simpa using congr(TensorProduct.lid A R $this)

/-- Under the fibre hypothesis, `M ⧸ R s` is flat over `A`. -/
theorem flat_quotient_of_fibres
    (hfib : ∀ (p : Ideal A) [p.IsPrime],
      Function.Injective ((smulS (A := A) (R := R) s).lTensor p.ResidueField)) :
    Module.Flat A (M ⧸ (R ∙ s)) := by
  have hinj : ∀ (N : Type u) [AddCommGroup N] [Module A N],
      Function.Injective ((smulS (A := A) (R := R) s).rTensor N) := fun N _ _ ↦
    (injective_lTensor_iff s N).mp (injective_lTensor_of_fibres s hfib N)
  haveI : Module.Flat A R := Module.Flat.trans A A[X] R
  haveI : Module.Flat A M := Module.Flat.trans A R M
  let ψ := smulS (A := A) (R := R) s
  let π : M →ₗ[A] M ⧸ (R ∙ s) := (Submodule.mkQ (R ∙ s)).restrictScalars A
  have hπ : Function.Surjective π := fun y ↦ by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨m, rfl⟩
  have hex : Function.Exact ψ π := fun y ↦ by
    change Submodule.Quotient.mk y = 0 ↔ y ∈ LinearMap.range ψ
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton, LinearMap.mem_range]
    rfl
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  let f := J.subtype
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨m1, rfl⟩ := LinearMap.rTensor_surjective J hπ q
  have h2 : π.rTensor A (f.lTensor M m1) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hq]
  obtain ⟨r2, hr2⟩ := (rTensor_exact A hex hπ _).mp h2
  let g := (LinearMap.range f).mkQ
  have hfg : Function.Exact f g := LinearMap.exact_map_mkQ_range f
  have hr3 : ψ.rTensor _ (g.lTensor R r2) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hr2, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp,
      hfg.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨r1, rfl⟩ := (lTensor_exact R hfg (Submodule.mkQ_surjective _) _).mp
    (hinj _ (hr3.trans (map_zero _).symm))
  have hm1 : m1 = ψ.rTensor J r1 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap f Subtype.val_injective
    rw [← hr2, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  rw [hm1, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hex.linearMap_comp_eq_zero,
    LinearMap.rTensor_zero, LinearMap.zero_apply]

end Main

/-- The fibre hypothesis holds when the fibre ring is a domain and `s` does not vanish there. -/
theorem injective_lTensor_of_isDomain {A : Type u} [CommRing A] {R : Type u} [CommRing R]
    [Algebra A R] {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    [Module.Projective R M] (s : M) (K : Type u) [CommRing K] [Algebra A K]
    [IsDomain (K ⊗[A] R)] (hs : (1 : K) ⊗ₜ[A] s ≠ 0) :
    Function.Injective ((smulS (A := A) (R := R) s).lTensor K) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra hz0
  obtain ⟨σ, hσ⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  have key : ∀ f : M →ₗ[R] R, (1 : K) ⊗ₜ[A] f s = 0 := by
    intro f
    have hw : ∀ w : K ⊗[A] R, w * ((1 : K) ⊗ₜ[A] f s) =
        (f.restrictScalars A).lTensor K ((smulS (A := A) (R := R) s).lTensor K w) := fun w ↦ by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul k r => simp
      | add w w' hw hw' => rw [add_mul, hw, hw', map_add, map_add]
    have := hw z
    rw [hz, map_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hz0
  apply hs
  have hs' : s = (σ s).sum fun m r ↦ r • m := by
    simpa [Finsupp.linearCombination_apply] using congr($hσ s).symm
  rw [hs', Finsupp.sum, TensorProduct.tmul_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  have : (1 : K) ⊗ₜ[A] (σ s m) = 0 := key ((Finsupp.lapply m) ∘ₗ σ)
  calc (1 : K) ⊗ₜ[A] (σ s m • m)
      = ((LinearMap.toSpanSingleton R M m).restrictScalars A).lTensor K
          ((1 : K) ⊗ₜ[A] σ s m) := rfl
    _ = 0 := by rw [this, map_zero]

end CurvesJacobian.FibreFlat
