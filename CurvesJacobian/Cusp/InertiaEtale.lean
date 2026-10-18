/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Orbicurve.EtaleInertia
import Pi1.Orbicurve.CoreCriterion
import Mathlib.RingTheory.RingHom.Etale

/-!
# A finite extension fixed by an inertia group is étale near the centre

Let `k` be a field of characteristic `0`, `u ∈ Ω` transcendental over `k` with `Ω / k(u)` Galois,
and `W` a valuation subring of `Ω` centred on the `u`-line (`k ⊆ W`, `u ∈ W`). For a finite
extension `N / k(u)` inside `Ω` fixed by the inertia group `I_W`, the normalization
`coordRing k u N` of `k[u]` in `N` is étale over `k[u]` at the centre `u_W(N)` of `W`
(`CurvesJacobian.Cusp.exists_etale_away_of_inertia_le`): the ramification index of `u_W(N)` over
`k[u]` is `|I_{u_W(M)}(M/k(u))| / |I_{u_W(M)}(M/N)| = 1` in the Galois closure `M` (pi1's
`AffOrbicurve.ramificationIdx_eq_one_iff`, using surjectivity of inertia
`AffOrbicurve.exists_mem_inertia_fixingSubgroup_restrictNormal_eq`), so `u_W(N)` is unramified,
hence étale (flatness over the Dedekind domain `k[u]`), and the étale locus is open.

This is the Galois-side input for comparing Galois inertia groups with topological loops around
punctures: an unramified point over a puncture lifts a small loop around it.
-/

open AffOrbicurve IntermediateField Polynomial

universe u

namespace CurvesJacobian.Cusp

variable {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- The inclusion `k[X] ≅ k[t] → coordRing k t N`. -/
noncomputable def coordRingMap (ht : Transcendental k t) (N : IntermediateField (K₀ k t) Ω) :
    k[X] →+* coordRing k t N :=
  (ringMap t (bot_le : (⊥ : IntermediateField (K₀ k t) Ω) ≤ N)).toRingHom.comp
    (coordRingBotEquiv ht).toRingHom

omit [CharZero k] in
lemma coordRingMap_apply (ht : Transcendental k t) (N : IntermediateField (K₀ k t) Ω)
    (p : k[X]) : (((coordRingMap ht N p : coordRing k t N) : N) : Ω) = aeval t p := by
  change (((coordRingBotEquiv ht p : coordRing k t (⊥ : IntermediateField (K₀ k t) Ω)) :
    (⊥ : IntermediateField (K₀ k t) Ω)) : Ω) = _
  exact coe_coordRingBotEquiv ht p

variable [IsGalois (K₀ k t) Ω]

set_option maxHeartbeats 1000000 in
-- the algebra structure `algRing` makes instance search and unification slow
set_option synthInstance.maxHeartbeats 400000 in
/-- **Fixed by inertia implies étale at the centre.** If `I_W` fixes the finite extension
`N / k(t)` (`W` centred on the `t`-line, with nonzero centre on `N`), then `u_W(N)` lies in the
étale locus of `k[t] → coordRing k t N`: for every `g ∉ u_W(N)` some `f ∉ u_W(N)` makes
`coordRing k t N [1/f]` étale over `k[X] ≅ k[t]`, with `g` invertible in it. -/
theorem exists_etale_away_of_inertia_le (ht : Transcendental k t) {W : ValuationSubring Ω}
    (hW : IsCentered k t W) (N : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) N]
    (hne : centerIdeal hW N ≠ ⊥)
    (hfix : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, σ ∈ N.fixingSubgroup)
    (g : coordRing k t N) (hg : g ∉ centerIdeal hW N) :
    ∃ f ∉ centerIdeal hW N, IsUnit (algebraMap (coordRing k t N) (Localization.Away f) g) ∧
      ((algebraMap (coordRing k t N) (Localization.Away f)).comp (coordRingMap ht N)).Etale := by
  haveI := isSeparable_of_charZero N
  let M := normalClosure (K₀ k t) N Ω
  haveI : FiniteDimensional (K₀ k t) M := normalClosure.is_finiteDimensional _ _ _
  haveI : IsGalois (K₀ k t) M := IsGalois.normalClosure _ _ _
  haveI := isSeparable_of_charZero M
  have hNM : N ≤ M := IntermediateField.le_normalClosure N
  have hneM : centerIdeal hW M ≠ ⊥ := by
    intro h
    apply hne
    rw [← comap_centerIdeal hW hNM, h]
    exact Ideal.comap_bot_of_injective _ (ringMap_injective t hNM)
  haveI := isMaximal_centerIdeal ht hW M hneM
  haveI := isMaximal_centerIdeal ht hW N hne
  have hbot : (⊥ : IntermediateField (K₀ k t) Ω) ≤ N := bot_le
  have he := (ramificationIdx_eq_one_iff t ht hbot hNM (centerIdeal hW M)).2 (by
    intro τ hτ
    obtain ⟨σ, hσ, hσL, rfl⟩ :=
      exists_mem_inertia_fixingSubgroup_restrictNormal_eq ht hW (bot_le.trans hNM) hneM τ hτ
    exact restrictNormal_mem_fixSub M (hfix σ hσ))
  rw [comap_centerIdeal hW hNM] at he
  letI iR := algRing t hbot
  letI : Module (coordRing k t ⊥) (coordRing k t N) := iR.toModule
  haveI hfin := module_finite_ringMap t ht hbot
  haveI : Algebra.IsIntegral (coordRing k t ⊥) (coordRing k t N) :=
    ⟨ringMap_isIntegral t hbot⟩
  haveI : Module.IsTorsionFree (coordRing k t ⊥) (coordRing k t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t hbot
  haveI := isDedekindDomain_ring t ht (⊥ : IntermediateField (K₀ k t) Ω)
  haveI : IsNoetherianRing (coordRing k t ⊥) := IsDedekindRing.toIsNoetherian
  haveI : Algebra.FinitePresentation (coordRing k t ⊥) (coordRing k t N) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : CharZero ((centerIdeal hW N).under (coordRing k t ⊥)).ResidueField :=
    charZero_of_injective_algebraMap
      (algebraMap k ((centerIdeal hW N).under (coordRing k t ⊥)).ResidueField).injective
  haveI : PerfectField ((centerIdeal hW N).under (coordRing k t ⊥)).ResidueField :=
    PerfectField.ofCharZero
  haveI : Algebra.IsUnramifiedAt (coordRing k t ⊥) (centerIdeal hW N) :=
    Ideal.ramificationIdx_eq_one_iff.mp he
  haveI : Algebra.IsEtaleAt (coordRing k t ⊥) (centerIdeal hW N) :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat _
  have hP : (⟨centerIdeal hW N, inferInstance⟩ : PrimeSpectrum (coordRing k t N)) ∈
      Algebra.etaleLocus (coordRing k t ⊥) (coordRing k t N) ∩
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (coordRing k t N))) :=
    ⟨‹Algebra.IsEtaleAt (coordRing k t ⊥) (centerIdeal hW N)›, hg⟩
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hPf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hP
      (Algebra.isOpen_etaleLocus.inter (PrimeSpectrum.basicOpen g).2)
  haveI het : Algebra.Etale (coordRing k t ⊥) (Localization.Away f) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp (fun q hq ↦ (hf hq).1)
  refine ⟨f, hPf, (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit).mp
    (fun q hq ↦ (hf hq).2), ?_⟩
  have h1 : (algebraMap (coordRing k t ⊥) (Localization.Away f)).Etale :=
    RingHom.etale_algebraMap.2 het
  have h2 : (coordRingBotEquiv ht).toRingHom.Etale :=
    RingHom.Etale.of_bijective (coordRingBotEquiv ht).bijective
  have e : (algebraMap (coordRing k t N) (Localization.Away f)).comp (coordRingMap ht N) =
      (algebraMap (coordRing k t ⊥) (Localization.Away f)).comp
        (coordRingBotEquiv ht).toRingHom := by
    rw [IsScalarTower.algebraMap_eq (coordRing k t ⊥) (coordRing k t N) (Localization.Away f),
      RingHom.comp_assoc]
    rfl
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ h2 h1

end CurvesJacobian.Cusp
