/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# An invariant coordinate on an affine curve with a finite group action

Let `K` be a field, `R` a finitely generated `K`-algebra which is a domain of transcendence
degree one, and `ρ : G →* (R ≃ₐ[K] R)` an action of a finite group. We show:

* `CurvesJacobian.Cusp.exists_invariant_finite`: there is a `G`-invariant `t : R`,
  transcendental over `K`, such that `K[X] → R`, `X ↦ t`, is finite. The coefficients of the
  polynomials `∏_g (X - ρ g b)` (`b` running over generators of `R`) generate a finitely
  generated invariant subalgebra `T` over which `R` is integral; Noether normalisation of `T`
  gives `t`.
* `CurvesJacobian.Cusp.exists_etale_away` (generic étaleness, characteristic zero): for such a
  `t` there is `h ≠ 0` in `K[X]` with `K[X]_h → R_h` finite étale. The generic point of `Spec R`
  is unramified over `K[X]` (`Algebra.isUnramifiedAt_bot`), `R` is flat over the Dedekind
  domain `K[X]`, so the generic point lies in the (open) étale locus; a basic open `D(f)` in it
  contains `D(h)` for a nonzero `h ∈ K[X] ∩ f R`.
* `CurvesJacobian.Cusp.awayAut`: for `t` invariant, the action extends to
  `G →* (R_h ≃ₐ[K[X]_h] R_h)`.

The hypothesis `Algebra.trdeg K R = 1` is the algebraic form of "`Spec R` is a curve": it says
exactly that the Noether normalisation of `R` has one variable. The Krull-dimension form follows:
`CurvesJacobian.Cusp.trdeg_eq_one_of_ringKrullDim_eq_one` (`ringKrullDim R = 1` implies
`Algebra.trdeg K R = 1`, by going up and incomparability for the Noether normalisation) and
`CurvesJacobian.Cusp.exists_invariant_finite_of_ringKrullDim`.
-/

open Polynomial

universe u

namespace CurvesJacobian.Cusp

variable {K R : Type u} [Field K] [CommRing R] [IsDomain R] [Algebra K R]

omit [IsDomain R] in
variable (K) in
/-- The ring map `K[X] → R`, `X ↦ t`. -/
noncomputable def lineHom (t : R) : K[X] →+* R := (aeval t).toRingHom

/-- Transcendence degree is unchanged along an injective integral extension of domains. -/
lemma trdeg_eq_of_isIntegral {S A : Type u} [CommRing S] [IsDomain S] [CommRing A]
    [IsDomain A]
    [Algebra K S] [Algebra K A] [Algebra S A] [IsScalarTower K S A] [FaithfulSMul S A]
    [Algebra.IsIntegral S A] : Algebra.trdeg K A = Algebra.trdeg K S := by
  rw [← trdeg_add_eq (R := K) (S := S) (A := A), trdeg_eq_zero (R := S) (A := A), add_zero]

/-- A domain finite over a polynomial ring `K[X₁, …, Xₙ] ⊆ A` has transcendence degree `n`. -/
lemma trdeg_eq_of_finite_injective {A : Type u} [CommRing A] [IsDomain A] [Algebra K A] {n : ℕ}
    (g : MvPolynomial (Fin n) K →ₐ[K] A) (hg : Function.Injective g) (hgf : g.Finite) :
    Algebra.trdeg K A = n := by
  letI : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin n) K) A :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  haveI : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Module.Finite (MvPolynomial (Fin n) K) A := hgf
  rw [trdeg_eq_of_isIntegral (S := MvPolynomial (Fin n) K), MvPolynomial.trdeg_of_isDomain,
    Cardinal.mk_fin, Cardinal.lift_natCast]

omit [IsDomain R] in
lemma lineHom_apply (t : R) (p : K[X]) : lineHom K t p = aeval t p := rfl

omit [IsDomain R] in
variable (K) in
/-- The `K[X]`-algebra structure on `R` given by `X ↦ t` (not an instance). -/
noncomputable abbrev lineAlgebra (t : R) : Algebra K[X] R := (lineHom K t).toAlgebra

section Invariant

variable {G : Type*} [Group G] [Finite G] (ρ : G →* (R ≃ₐ[K] R))

omit [IsDomain R] in
open MulSemiringAction in
/-- A finitely generated `G`-invariant subalgebra `T ⊆ R` over which `R` is integral. -/
lemma exists_fg_subalgebra_invariant [Algebra.FiniteType K R] :
    ∃ T : Subalgebra K R, T.FG ∧ (∀ x ∈ T, ∀ g, ρ g x = x) ∧ ∀ r : R, IsIntegral T r := by
  classical
  letI : MulSemiringAction G R := MulSemiringAction.compHom R ρ
  cases nonempty_fintype G
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra K R).FG)
  let C : Finset R := s.biUnion fun b ↦ (charpoly G b).coeffs
  refine ⟨Algebra.adjoin K (C : Set R), Subalgebra.fg_adjoin_finset C, ?_, ?_⟩
  · intro x hx g
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
      obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hb
      exact smul_coeff_charpoly b n g
    | algebraMap r => exact (ρ g).commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · have key : ∀ b ∈ s, IsIntegral (Algebra.adjoin K (C : Set R)) b := by
      intro b hb
      have hlift : charpoly G b ∈
          Polynomial.lifts (algebraMap (Algebra.adjoin K (C : Set R)) R) := by
        refine (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
        by_cases hn : (charpoly G b).coeff n = 0
        · exact ⟨0, by rw [hn, map_zero]⟩
        · exact ⟨⟨_, Algebra.subset_adjoin (Finset.mem_coe.mpr
            (Finset.mem_biUnion.mpr ⟨b, hb, coeff_mem_coeffs hn⟩))⟩, rfl⟩
      obtain ⟨p, hp1, -, hp2⟩ := lifts_and_natDegree_eq_and_monic hlift (monic_charpoly G b)
      exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩
    intro r
    have h2 : Algebra.adjoin K (s : Set R) ≤
        (integralClosure (Algebra.adjoin K (C : Set R)) R).restrictScalars K :=
      Algebra.adjoin_le fun b hb ↦ key b hb
    exact h2 (hs ▸ Algebra.mem_top)

/-- **An invariant coordinate.** For a finitely generated `K`-domain `R` of transcendence degree
one with an action of a finite group `G`, there is a `G`-invariant `t : R`, transcendental over
`K`, making `R` finite over `K[t]`. -/
theorem exists_invariant_finite [Algebra.FiniteType K R] (hR : Algebra.trdeg K R = 1) :
    ∃ t : R, (∀ g, ρ g t = t) ∧ Transcendental K t ∧ (lineHom K t).Finite := by
  obtain ⟨T, hTfg, hTinv, hTint⟩ := exists_fg_subalgebra_invariant ρ
  haveI : Algebra.FiniteType K T := (Subalgebra.fg_iff_finiteType T).mp hTfg
  haveI : Algebra.IsIntegral T R := ⟨hTint⟩
  haveI : Algebra.FiniteType T R := Algebra.FiniteType.of_restrictScalars_finiteType K T R
  haveI : Module.Finite T R := Algebra.IsIntegral.finite
  have hTR : (algebraMap T R).Finite := RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨n, g, hg, hgf⟩ := exists_finite_inj_algHom_of_fg K T
  haveI : FaithfulSMul T R :=
    (faithfulSMul_iff_algebraMap_injective T R).mpr Subtype.val_injective
  have hn : ((n : ℕ) : Cardinal.{u}) = 1 := by
    rw [← trdeg_eq_of_finite_injective g hg hgf, ← hR]
    exact (trdeg_eq_of_isIntegral (S := T) (A := R)).symm
  obtain rfl : n = 1 := by exact_mod_cast hn
  let e : K[X] ≃ₐ[K] MvPolynomial (Fin 1) K := (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm
  let φ : K[X] →ₐ[K] R := T.val.comp (g.comp e.toAlgHom)
  have hφ : aeval (φ X) = φ := Polynomial.algHom_ext (by simp)
  refine ⟨φ X, fun g' ↦ hTinv _ (g _).2 g', ?_, ?_⟩
  · rw [transcendental_iff_injective, hφ]
    exact Subtype.val_injective.comp (hg.comp e.injective)
  · change (aeval (φ X) : K[X] →ₐ[K] R).toRingHom.Finite
    rw [hφ]
    exact hTR.comp (hgf.comp (RingHom.Finite.of_surjective _ e.surjective))

end Invariant

section KrullDim

/-- **Going up for chains.** Along an injective integral ring map every chain of primes lifts to a
chain of the same length. -/
lemma exists_ltSeries_lift {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    (l : LTSeries (PrimeSpectrum A)) :
    ∃ L : LTSeries (PrimeSpectrum B), L.length = l.length ∧
      L.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal := by
  induction l using RelSeries.inductionOn' with
  | singleton p =>
    obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal B)
      (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, by simpa [RelSeries.last_singleton] using hQp⟩
  | snoc l q hlq ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    obtain ⟨Q, hLQ, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      q.asIdeal L.last.asIdeal (by rw [hlast]; exact le_of_lt hlq)
    have hlt : L.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hLQ) fun he ↦ ?_
      refine (ne_of_lt hlq) (PrimeSpectrum.ext ?_)
      exact hlast.symm.trans
        ((congrArg (fun P : PrimeSpectrum B ↦ P.asIdeal.comap (algebraMap A B)) he).trans hQq)
    exact ⟨L.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], by simpa using hQq⟩

/-- Krull dimension does not drop along an injective integral extension (going up). -/
lemma ringKrullDim_le_of_isIntegral {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim A ≤ ringKrullDim B := by
  refine iSup_le fun l ↦ ?_
  obtain ⟨L, hL, -⟩ := exists_ltSeries_lift hinj l
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- Krull dimension does not grow along an integral extension (incomparability). -/
lemma ringKrullDim_le_of_isIntegral' {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A := by
  let g : PrimeSpectrum B → PrimeSpectrum A := fun Q ↦
    ⟨Q.asIdeal.comap (algebraMap A B), inferInstance⟩
  have hg : StrictMono g := fun Q₁ Q₂ hQ ↦ by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hQ ⊢
    exact Ideal.IsIntegral.comap_lt_comap hQ
  exact Order.krullDim_le_of_strictMono g hg

/-- For a finitely generated `K`-domain, Krull dimension one implies transcendence degree one
(Noether normalisation, going up and incomparability). -/
theorem trdeg_eq_one_of_ringKrullDim_eq_one [Algebra.FiniteType K R]
    (hR : ringKrullDim R = 1) : Algebra.trdeg K R = 1 := by
  obtain ⟨n, g, hg, hgf⟩ := exists_finite_inj_algHom_of_fg K R
  letI : Algebra (MvPolynomial (Fin n) K) R := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin n) K) R := hgf
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) K) R) := hg
  have hdim : ringKrullDim (MvPolynomial (Fin n) K) = n := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have h1 : (n : WithBot ℕ∞) = 1 := by
    rw [← hdim, ← hR]
    exact le_antisymm (ringKrullDim_le_of_isIntegral hinj) ringKrullDim_le_of_isIntegral'
  have hn : n = 1 := by exact_mod_cast h1
  rw [trdeg_eq_of_finite_injective g hg hgf, hn, Nat.cast_one]

/-- `CurvesJacobian.Cusp.exists_invariant_finite` under the hypothesis `ringKrullDim R = 1`. -/
theorem exists_invariant_finite_of_ringKrullDim {G : Type*} [Group G] [Finite G]
    (ρ : G →* (R ≃ₐ[K] R)) [Algebra.FiniteType K R] (hR : ringKrullDim R = 1) :
    ∃ t : R, (∀ g, ρ g t = t) ∧ Transcendental K t ∧ (lineHom K t).Finite :=
  exists_invariant_finite ρ (trdeg_eq_one_of_ringKrullDim_eq_one hR)

end KrullDim

section Etale

variable [CharZero K]

/-- **Generic étaleness.** In characteristic zero, if `t : R` is transcendental and `R` is finite
over `K[t]`, then `K[X]_h → R_h` is finite étale for some nonzero `h ∈ K[X]`. -/
theorem exists_etale_away (t : R) (ht : Transcendental K t) (hfin : (lineHom K t).Finite) :
    ∃ h : K[X], h ≠ 0 ∧ (Localization.awayMap (lineHom K t) h).Etale ∧
      (Localization.awayMap (lineHom K t) h).Finite := by
  letI := lineAlgebra K t
  haveI : Module.Finite K[X] R := hfin
  haveI : Module.IsTorsionFree K[X] R := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact transcendental_iff_injective.mp ht
  haveI : Algebra.FinitePresentation K[X] R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.IsUnramifiedAt K[X] (⊥ : Ideal R) := Algebra.isUnramifiedAt_bot
  haveI : Algebra.IsEtaleAt K[X] (⊥ : Ideal R) := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat _
  have hP : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Algebra.etaleLocus K[X] R :=
    ‹Algebra.IsEtaleAt K[X] (⊥ : Ideal R)›
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hPf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hP Algebra.isOpen_etaleLocus
  have hf0 : f ≠ 0 := hPf
  obtain ⟨h, hmem, hh⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self f)
      (Algebra.IsIntegral.isIntegral (R := K[X]) f))
  have hsub : (PrimeSpectrum.basicOpen (algebraMap K[X] R h) : Set (PrimeSpectrum R)) ⊆
      Algebra.etaleLocus K[X] R := fun q hq ↦ hf fun hfq ↦
    hq ((Ideal.span_singleton_le_iff_mem _).mpr hfq hmem)
  haveI : Algebra.Etale K[X] (Localization.Away (algebraMap K[X] R h)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hsub
  haveI : Algebra.Etale K[X] (Localization.Away h) := Algebra.Etale.of_isLocalizationAway h
  letI : Algebra (Localization.Away h) (Localization.Away (algebraMap K[X] R h)) :=
    (Localization.awayMap (lineHom K t) h).toAlgebra
  haveI : IsScalarTower K[X] (Localization.Away h) (Localization.Away (algebraMap K[X] R h)) :=
    IsScalarTower.of_algebraMap_eq fun p ↦ by
      change _ = Localization.awayMap (lineHom K t) h (algebraMap K[X] (Localization.Away h) p)
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
        IsScalarTower.algebraMap_apply K[X] R]
      rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R (Submonoid.powers h))
      (Localization.Away (algebraMap K[X] R h)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact Localization.isLocalization
  refine ⟨h, hh, ?_, ?_⟩
  · exact Algebra.Etale.of_restrictScalars K[X] (Localization.Away h) _
  · exact Module.Finite.of_isLocalization K[X] R (Submonoid.powers h)

end Etale

section Equivariant

variable {G : Type*} [Group G] (ρ : G →* (R ≃ₐ[K] R))

omit [IsDomain R] in
/-- The `K[X]_h`-algebra structure on `R_h = R[1/h(t)]` (not an instance). -/
noncomputable abbrev lineAwayAlgebra (t : R) (h : K[X]) :
    Algebra (Localization.Away h) (Localization.Away (lineHom K t h)) :=
  (Localization.awayMap (lineHom K t) h).toAlgebra

attribute [local instance] lineAwayAlgebra

omit [IsDomain R] in
lemma map_lineHom_of_fix {σ : R ≃ₐ[K] R} {t : R} (hσ : σ t = t) (p : K[X]) :
    σ (lineHom K t p) = lineHom K t p := by
  rw [lineHom_apply, ← Polynomial.aeval_algHom_apply]
  exact congrArg (fun x ↦ aeval x p) hσ

omit [IsDomain R] in
lemma map_powers_lineHom {σ : R ≃ₐ[K] R} {t : R} (hσ : σ t = t) (h : K[X]) :
    Submonoid.map σ.toRingEquiv.toMonoidHom (Submonoid.powers (lineHom K t h)) =
      Submonoid.powers (lineHom K t h) := by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (map_lineHom_of_fix hσ h)

omit [IsDomain R] in
/-- The extension of an automorphism `σ` of `R` fixing `t` to `R_h`, as a ring isomorphism. -/
noncomputable def awayRingEquiv {σ : R ≃ₐ[K] R} {t : R} (hσ : σ t = t) (h : K[X]) :
    Localization.Away (lineHom K t h) ≃+* Localization.Away (lineHom K t h) :=
  IsLocalization.ringEquivOfRingEquiv _ _ σ.toRingEquiv (map_powers_lineHom hσ h)

omit [IsDomain R] in
@[simp]
lemma awayRingEquiv_algebraMap {σ : R ≃ₐ[K] R} {t : R} (hσ : σ t = t) (h : K[X]) (r : R) :
    awayRingEquiv hσ h (algebraMap R _ r) = algebraMap R _ (σ r) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ r

omit [IsDomain R] in
lemma ringHom_ext_away {t : R} {h : K[X]}
    {φ ψ : Localization.Away (lineHom K t h) →+* Localization.Away (lineHom K t h)}
    (e : ∀ r : R, φ (algebraMap R _ r) = ψ (algebraMap R _ r)) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers (lineHom K t h)) (RingHom.ext e)

omit [IsDomain R] in
/-- The extension of an automorphism `σ` of `R` fixing `t` to a `K[X]_h`-algebra automorphism
of `R_h`. -/
noncomputable def awayAlgEquiv {σ : R ≃ₐ[K] R} {t : R} (hσ : σ t = t) (h : K[X]) :
    Localization.Away (lineHom K t h) ≃ₐ[Localization.Away h]
      Localization.Away (lineHom K t h) :=
  AlgEquiv.ofRingEquiv (f := awayRingEquiv hσ h) fun a ↦ by
    have key : (awayRingEquiv hσ h).toRingHom.comp (Localization.awayMap (lineHom K t) h) =
        Localization.awayMap (lineHom K t) h := by
      refine IsLocalization.ringHom_ext (Submonoid.powers h) (RingHom.ext fun p ↦ ?_)
      simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        awayRingEquiv_algebraMap, map_lineHom_of_fix hσ]
    exact DFunLike.congr_fun key a

omit [IsDomain R] in
@[simp]
lemma awayAlgEquiv_apply {σ : R ≃ₐ[K] R} {t : R} (hσ : σ t = t) (h : K[X])
    (y : Localization.Away (lineHom K t h)) : awayAlgEquiv hσ h y = awayRingEquiv hσ h y :=
  rfl

omit [IsDomain R] in
/-- **Equivariance on `R_h`.** If `t` is `G`-invariant, the action `ρ` of `G` on `R` extends to
an action on `R_h = R[1/h(t)]` by `K[X]_h`-algebra automorphisms. -/
noncomputable def awayAut {t : R} (ht : ∀ g, ρ g t = t) (h : K[X]) :
    G →* (Localization.Away (lineHom K t h) ≃ₐ[Localization.Away h]
      Localization.Away (lineHom K t h)) where
  toFun g := awayAlgEquiv (ht g) h
  map_one' := AlgEquiv.ext fun y ↦ by
    have : (awayRingEquiv (ht 1) h).toRingHom = RingHom.id _ :=
      ringHom_ext_away fun r ↦ (awayRingEquiv_algebraMap (ht 1) h r).trans
        (by rw [map_one, AlgEquiv.one_apply]; rfl)
    change awayRingEquiv (ht 1) h y = y
    exact DFunLike.congr_fun this y
  map_mul' g g' := AlgEquiv.ext fun y ↦ by
    have : (awayRingEquiv (ht (g * g')) h).toRingHom =
        (awayRingEquiv (ht g) h).toRingHom.comp (awayRingEquiv (ht g') h).toRingHom :=
      ringHom_ext_away fun r ↦ (awayRingEquiv_algebraMap (ht (g * g')) h r).trans <|
        (congrArg (algebraMap R _) (by rw [map_mul, AlgEquiv.mul_apply])).trans <|
          (awayRingEquiv_algebraMap (ht g) h _).symm.trans <|
            congrArg (awayRingEquiv (ht g) h) (awayRingEquiv_algebraMap (ht g') h r).symm
    change awayRingEquiv (ht (g * g')) h y = awayRingEquiv (ht g) h (awayRingEquiv (ht g') h y)
    exact DFunLike.congr_fun this y

omit [IsDomain R] in
@[simp]
lemma awayAut_algebraMap {t : R} (ht : ∀ g, ρ g t = t) (h : K[X]) (g : G) (r : R) :
    awayAut ρ ht h g (algebraMap R _ r) = algebraMap R _ (ρ g r) :=
  awayRingEquiv_algebraMap (ht g) h r

end Equivariant

end CurvesJacobian.Cusp
