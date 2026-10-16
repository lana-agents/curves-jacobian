/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Belyi.KaehlerRank
import WeilCurves.FunctionField.Basic

/-!
# Function fields of smooth curves are function fields of one variable

Let `k` be a perfect field and `A` a domain which is a standard smooth `k`-algebra of relative
dimension `1` (the coordinate ring of an affine chart of a smooth curve). Then:

* `CurvesJacobian.krullDimLE_one_of_smooth`: `dim A ≤ 1` (via belyi's
  `krullDimLE_one_of_standardSmooth_localization` at every maximal ideal);
* `CurvesJacobian.exists_transcendental_of_smooth`: some `a ∈ A` is transcendental over `k`
  (otherwise `A` is a finite separable field extension of `k`, so `Ω_{A/k} = 0`, contradicting
  `rank Ω_{A/k} = 1`);
* `CurvesJacobian.exists_finite_injective_mvPolynomial_fin_one`: Noether normalisation of `A`
  has exactly one variable (a second one would give a chain `0 ⊊ Q₁ ⊊ Q₂` by going-up);
* `CurvesJacobian.isFunctionField_of_smooth`: the fraction field `K` of `A` is a function field
  of one variable over `k` in the sense of weil-curves (`IsFunctionField k K`: finite over
  `k⟮t⟯` for a transcendental `t`).
-/

open Algebra IsLocalRing MvPolynomial
open scoped IntermediateField

namespace CurvesJacobian

universe u v

variable (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [IsDomain A]
  [Algebra k A] [IsStandardSmoothOfRelativeDimension 1 k A]

include k in
/-- A smooth curve chart has Krull dimension `≤ 1`. -/
theorem krullDimLE_one_of_smooth : Ring.KrullDimLE 1 A := by
  haveI : IsStandardSmooth k A := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [Ring.krullDimLE_iff, ringKrullDim_le_iff_isMaximal_height_le]
  intro m hm
  let B := Localization.AtPrime m
  haveI : Algebra.EssFiniteType A B :=
    Algebra.EssFiniteType.of_isLocalization (S := B) m.primeCompl
  haveI : Algebra.EssFiniteType k B := Algebra.EssFiniteType.comp k A B
  haveI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing k B
  haveI : Algebra.EssFiniteType k (ResidueField B) :=
    inferInstanceAs (Algebra.EssFiniteType k (B ⧸ maximalIdeal B))
  haveI : Algebra.FormallySmooth k (ResidueField B) := inferInstance
  haveI : Ring.KrullDimLE 1 B :=
    Belyi.krullDimLE_one_of_standardSmooth_localization k A m.primeCompl B
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height m B]
  exact Ring.krullDimLE_iff.1 this

/-- A smooth curve chart contains an element transcendental over `k`. -/
theorem exists_transcendental_of_smooth : ∃ a : A, Transcendental k a := by
  by_contra h
  push Not at h
  haveI : Algebra.IsAlgebraic k A := ⟨fun a ↦ by simpa [Transcendental] using h a⟩
  have hf : IsField A := isField_of_isIntegral_of_isField' (Field.toIsField k)
  letI := hf.toField
  haveI : Algebra.IsSeparable k A := inferInstance
  haveI := FormallyUnramified.of_isSeparable k A
  have h1 := Belyi.finrank_kaehler_of_standardSmooth k A 1
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

/-- **Noether normalisation of a smooth curve chart has one variable.** -/
theorem exists_finite_injective_mvPolynomial_fin_one :
    ∃ g : MvPolynomial (Fin 1) k →ₐ[k] A, Function.Injective g ∧ g.Finite := by
  haveI : IsStandardSmooth k A := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := inferInstance
  rcases (show s = 0 ∨ s = 1 ∨ 2 ≤ s by omega) with rfl | rfl | hs
  · -- `s = 0`: `A` would be integral over `k`
    exfalso
    obtain ⟨a, ha⟩ := exists_transcendental_of_smooth k A
    apply ha
    have hint : IsIntegral (MvPolynomial (Fin 0) k) a := Algebra.IsIntegral.isIntegral a
    have := IsIntegral.map_of_comp_eq (constantCoeff (σ := Fin 0) (R := k)) (RingHom.id A)
      (by
        ext p
        · simp [RingHom.algebraMap_toAlgebra]
        · exact (Fin.elim0 ‹_›)) hint
    exact this.isAlgebraic
  · exact ⟨g, hinj, hfin⟩
  · -- `s ≥ 2`: a chain `⊥ < Q₁ < Q₂` of primes of `A` by going-up
    exfalso
    haveI := krullDimLE_one_of_smooth k A
    let i0 : Fin s := ⟨0, by omega⟩
    let i1 : Fin s := ⟨1, by omega⟩
    have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    let e1 : MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
      aeval fun i ↦ if i = i0 then 0 else X i
    let e2 : MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
      aeval fun i ↦ if i = i0 ∨ i = i1 then 0 else X i
    have he : e2.comp e1 = e2 := by
      ext i
      by_cases h : i = i0 <;> simp [e1, e2, h]
    let P1 := RingHom.ker e1.toRingHom
    let P2 := RingHom.ker e2.toRingHom
    haveI : P1.IsPrime := RingHom.ker_isPrime _
    haveI : P2.IsPrime := RingHom.ker_isPrime _
    have hP12 : P1 ≤ P2 := by
      intro p hp
      simp only [P1, P2, RingHom.mem_ker] at hp ⊢
      rw [← he]
      change e2 (e1 p) = 0
      rw [show e1 p = 0 from hp, map_zero]
    have hX1 : X i1 ∈ P2 := by simp [P2, e2]
    have hX1' : X i1 ∉ P1 := by simp [P1, e1, hi.symm, X_ne_zero]
    have hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) k) A) ≤ P1 := by
      intro p hp
      rw [RingHom.mem_ker] at hp
      have : p = 0 := hinj (by rw [map_zero]; exact hp)
      rw [this]; exact zero_mem _
    obtain ⟨Q1, hQ1, hQ1c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain P1 hker
    obtain ⟨Q2, hQ12, hQ2, hQ2c⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P2 Q1 (hQ1c ▸ hP12)
    have hQ1ne : Q1 ≠ ⊥ := by
      rintro rfl
      have hX0 : X i0 ∈ P1 := by simp [P1, e1]
      rw [← hQ1c] at hX0
      simp only [Ideal.mem_comap, Ideal.mem_bot] at hX0
      exact X_ne_zero i0 (hinj (by rw [map_zero]; exact hX0))
    have hmax := hQ1.isMaximal_of_ne_bot hQ1ne
    have hQ : Q1 = Q2 := hmax.eq_of_le hQ2.ne_top hQ12
    apply hX1'
    rw [← hQ1c, hQ, hQ2c]
    exact hX1

/-- **The fraction field of a smooth curve chart over a perfect field is a function field of one
variable.** -/
theorem isFunctionField_of_smooth (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra k K] [IsScalarTower k A K] : WeilCurves.FunctionField.IsFunctionField k K := by
  haveI : IsStandardSmooth k A := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  obtain ⟨g, hinj, hfin⟩ := exists_finite_injective_mvPolynomial_fin_one k A
  letI : Algebra (MvPolynomial (Fin 1) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin 1) k) A := hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin 1) k) A := inferInstance
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  set t : K := algebraMap A K (g (X 0)) with ht_def
  have ht : Transcendental k t := by
    rw [ht_def, transcendental_algebraMap_iff hAK]
    exact fun h ↦ transcendental_X (R := k) (0 : Fin 1) ((isAlgebraic_algHom_iff g hinj).1 h)
  refine ⟨⟨t, ht, ?_⟩⟩
  -- the image of `k[X₀]` lies in `k⟮t⟯`
  have hmem : ∀ c : MvPolynomial (Fin 1) k, algebraMap A K (g c) ∈ k⟮t⟯ := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ a
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul, Fin.fin_one_eq_zero i]
      exact mul_mem hp (IntermediateField.mem_adjoin_simple_self k t)
  -- every element of `A` is integral over `k⟮t⟯`
  have hint : ∀ a : A, IsIntegral k⟮t⟯ (algebraMap A K a) := by
    intro a
    refine IsIntegral.map_of_comp_eq
      ((algebraMap A K).comp g.toRingHom |>.codRestrict k⟮t⟯ hmem) (algebraMap A K) ?_
      (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin 1) k) a)
    ext p <;> rfl
  -- a finite generating set of `A` over `k`
  obtain ⟨sA, hsA⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  let S : Set K := algebraMap A K '' (sA : Set A)
  haveI : Finite S := (sA.finite_toSet.image _).to_subtype
  have hS : ∀ y ∈ S, IsIntegral k⟮t⟯ y := by
    rintro _ ⟨a, -, rfl⟩
    exact hint a
  have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin k⟮t⟯ S := by
    intro a
    have ha : a ∈ Algebra.adjoin k (sA : Set A) := hsA ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap c =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k k⟮t⟯ K]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin k⟮t⟯ S = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    exact div_mem (hA a) (hA b)
  haveI := IntermediateField.finiteDimensional_adjoin hS
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end CurvesJacobian
