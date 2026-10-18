/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.BranchedCurve
import Belyi.Converse.BranchedPi1
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.RingHom.Etale

/-!
# Generic étaleness of a finite coordinate in characteristic zero

Let `k` be an algebraically closed field of characteristic zero, `B` a domain over `k` and
`t ∈ B` such that `k[t] → B` is finite and injective (a `Belyi.Converse.FiniteCoord`). Then
`k[t] → B` is étale away from finitely many values of `t`: there is a finite `S ⊆ k` such that
`k[X] → B[P_S(t)⁻¹]` is étale, `P_S = ∏_{s ∈ S} (X - s)` (`Belyi.Converse.branchPolyOf`)
(`CurvesJacobian.FiniteCoord.exists_etale_branchPolyOf`).

Proof. In characteristic zero the generic point of `Spec B` is unramified over `k[X]`
(`Algebra.isUnramifiedAt_bot`: `Frac B / k(X)` is separable), and the unramified locus is open
(`Algebra.exists_formallyUnramified_of_isUnramifiedAt`), so `B_b` is formally unramified over
`k[X]` for some `b ≠ 0`. As `B` is integral over `k[X]`, `b` divides a nonzero `p(t)`,
`p ∈ k[X]`; with `S` the roots of `p`, `D(P_S(t)) ⊆ D(p(t)) ⊆ D(b)`, so `B[P_S(t)⁻¹]` is formally
unramified (`Algebra.basicOpen_subset_unramifiedLocus_iff`). It is flat (torsion-free over the
principal ideal domain `k[X]`) and of finite presentation, hence étale
(`RingHom.Etale.iff_flat_and_formallyUnramified`).
-/

open Belyi Belyi.Converse

universe u

namespace CurvesJacobian

noncomputable section

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

/-- `P_S(t) = ∏_{s ∈ S} (t - s)`. -/
lemma aeval_branchPolyOf (t : B) (S : Finset k) :
    MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ t) (branchPolyOf S) =
      ∏ s ∈ S, (t - algebraMap k B s) := by
  simp [branchPolyOf, map_prod]

/-- `aeval t` on `MvPolynomial (Fin 1) k` is `aeval t` on `k[X]` through `finOnePolyEquiv`. -/
lemma mvAeval_eq_aeval_finOnePolyEquiv (t : B) (p : MvPolynomial (Fin 1) k) :
    MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ t) p =
      Polynomial.aeval t (finOnePolyEquiv k p) := by
  rw [← AlgEquiv.coe_toAlgHom, finOnePolyEquiv_eq, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp

variable [IsDomain B] [IsAlgClosed k] [CharZero k]

/-- **Generic étaleness**: a finite injective coordinate `t` on a domain `B` over an
algebraically closed field of characteristic zero is étale over `𝔸¹ ∖ S` for a finite `S ⊆ k`:
`k[X] → B[P_S(t)⁻¹]` is étale. -/
theorem FiniteCoord.exists_etale_branchPolyOf (D : FiniteCoord k B)
    (hinj : Function.Injective (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t)) :
    ∃ S : Finset k, ((algebraMap B (Localization.Away
      (MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ D.t) (branchPolyOf S)))).comp
        (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t).toRingHom).Etale := by
  classical
  let R := MvPolynomial (Fin 1) k
  let φ : R →ₐ[k] B := MvPolynomial.aeval fun _ : Fin 1 ↦ D.t
  letI : Algebra R B := φ.toRingHom.toAlgebra
  haveI : Module.Finite R B := D.finite
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).2 hinj
  haveI : Algebra.FiniteType R B := inferInstance
  haveI : Algebra.IsUnramifiedAt R (⊥ : Ideal B) := Algebra.isUnramifiedAt_bot
  obtain ⟨b, hb, hU⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) (⊥ : Ideal B)
  have hb0 : b ≠ 0 := by simpa using hb
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := R) (I := Ideal.span {b}) hb0
    (Ideal.mem_span_singleton_self b) (Algebra.IsIntegral.isIntegral b)
  obtain ⟨p, hpmem, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hpmem
  set P : Polynomial k := finOnePolyEquiv k p with hP
  have hP0 : P ≠ 0 := by
    rw [hP, Ne, map_eq_zero_iff _ (finOnePolyEquiv k).injective]
    exact hp0
  set S := P.roots.toFinset
  refine ⟨S, ?_⟩
  set q : B := MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ D.t) (branchPolyOf S) with hq
  have hpP : algebraMap R B p = Polynomial.aeval D.t P := mvAeval_eq_aeval_finOnePolyEquiv D.t p
  -- `D(q) ⊆ D(b)`
  have hsub : (PrimeSpectrum.basicOpen q : Set (PrimeSpectrum B)) ⊆
      PrimeSpectrum.basicOpen b := by
    intro 𝔭 h𝔭
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at h𝔭 ⊢
    intro hb𝔭
    apply h𝔭
    have hp𝔭 : Polynomial.aeval D.t P ∈ 𝔭.asIdeal := by
      rw [← hpP]
      obtain ⟨c, hc⟩ := hpmem
      rw [hc]
      exact 𝔭.asIdeal.mul_mem_right _ hb𝔭
    rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P)
      IsAlgClosed.card_roots_eq_natDegree,
      map_mul, Polynomial.aeval_C] at hp𝔭
    rcases 𝔭.isPrime.mem_or_mem hp𝔭 with h | h
    · exact absurd h (𝔭.isPrime.ne_top' ∘ fun h' ↦ (Ideal.eq_top_of_isUnit_mem _ h'
        ((Polynomial.leadingCoeff_ne_zero.2 hP0).isUnit.map _)))
    · rw [map_multiset_prod, Multiset.map_map] at h
      obtain ⟨y, hy, hy𝔭⟩ := (𝔭.isPrime.multiset_prod_mem_iff_exists_mem _).1 h
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hy
      have haS : a ∈ S := Multiset.mem_toFinset.2 ha
      rw [hq, aeval_branchPolyOf]
      rw [← Finset.mul_prod_erase S _ haS]
      exact Ideal.mul_mem_right _ _ (by simpa using hy𝔭)
  have hUq : Algebra.FormallyUnramified R (Localization.Away q) :=
    Algebra.basicOpen_subset_unramifiedLocus_iff.1
      (hsub.trans (Algebra.basicOpen_subset_unramifiedLocus_iff.2 hU))
  -- `q ≠ 0`
  have hq0 : q ≠ 0 := by
    rw [hq, aeval_branchPolyOf, Finset.prod_ne_zero_iff]
    intro s _ h
    have h' : (MvPolynomial.X 0 - MvPolynomial.C s : R) = 0 := hinj (by simpa using h)
    have := congrArg (MvPolynomial.eval fun _ : Fin 1 ↦ s + 1) h'
    simp at this
  haveI : IsDomain (Localization.Away q) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hq0)
  have hinjq : Function.Injective (algebraMap R (Localization.Away q)) := by
    rw [IsScalarTower.algebraMap_eq R B (Localization.Away q)]
    exact (IsLocalization.injective (Localization.Away q)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hq0)).comp hinj
  haveI : FaithfulSMul R (Localization.Away q) :=
    (faithfulSMul_iff_algebraMap_injective R _).2 hinjq
  haveI : IsPrincipalIdealRing R :=
    IsPrincipalIdealRing.of_surjective ((finOnePolyEquiv k).symm : Polynomial k →+* R)
      (finOnePolyEquiv k).symm.surjective
  haveI : Algebra.FiniteType R (Localization.Away q) :=
    Algebra.FiniteType.trans (S := B) inferInstance
      (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers q) _)
  haveI : Algebra.FinitePresentation R (Localization.Away q) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have e : (algebraMap B (Localization.Away q)).comp φ.toRingHom =
      algebraMap R (Localization.Away q) := (IsScalarTower.algebraMap_eq R B _).symm
  rw [e, RingHom.Etale.iff_flat_and_formallyUnramified, RingHom.flat_algebraMap_iff,
    RingHom.formallyUnramified_algebraMap, RingHom.finitePresentation_algebraMap]
  exact ⟨inferInstance, hUq, inferInstance⟩

end

end CurvesJacobian
