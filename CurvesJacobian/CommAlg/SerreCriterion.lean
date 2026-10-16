/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.Submodule

/-!
# Serre's criterion for normality of Noetherian domains

Let `A` be a Noetherian domain. We prove (Stacks Project, Lemma 10.157.4 = Tag 031S and
Lemma 10.157.6 = Tag 031T, specialised to domains):

* `CurvesJacobian.isIntegrallyClosed_iff_regularInCodimOne_and_assPrimes`:
  `A` is integrally closed iff
  - (R₁) `A_𝔭` is a discrete valuation ring for every prime `𝔭` of height one, and
  - (S₂) every associated prime of `A ⧸ (a)`, `a ≠ 0`, has height one.
* `CurvesJacobian.mem_range_of_forall_height_eq_one`: under (S₂), an element of the fraction
  field lying in `A_𝔭` for every height-one prime `𝔭` lies in `A`, i.e. `A = ⋂_{ht 𝔭 = 1} A_𝔭`.

The (S₂)-condition is stated in its associated-primes form (for a Noetherian domain this is
equivalent to depth `A_𝔭 ≥ min(2, dim A_𝔭)`, Stacks Def. 10.157.1; depth is not in Mathlib).
[LocAn] (Mochizuki, *The Local Pro-p Anabelian Geometry of Curves*, Lemma 13.3) uses the
criterion in the form "the conditions R1 and S2 of Serre ([Mats], Ch. 7, §17.I, Thm 39)
are satisfied, so … is normal".
-/

open IsLocalRing

namespace CurvesJacobian

variable (A : Type*) [CommRing A] [IsDomain A]

/-- Serre's condition (S₂) for a domain, in the form used for Noetherian domains:
every associated prime of `A ⧸ (a)` with `a ≠ 0` has height one. -/
def AssPrimesHeightOne : Prop :=
  ∀ a : A, a ≠ 0 → ∀ q ∈ associatedPrimes A (A ⧸ Ideal.span {a}), q.height = 1

/-- Serre's condition (R₁) for a domain: the localisation at every height-one prime is a
discrete valuation ring. -/
def RegularInCodimOne : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → IsDiscreteValuationRing (Localization.AtPrime p)

variable {A}

/-- If `y / a` (in the fraction field) lies in `A_q`, then some `s ∉ q` satisfies
`s * b ∈ (a)`. -/
lemma exists_mul_mem_span_of_mk'_mem (q : Ideal A) [q.IsPrime] (b : A) (a : nonZeroDivisors A)
    (y : Localization.AtPrime q)
    (hy : algebraMap (Localization.AtPrime q) (FractionRing A) y =
      IsLocalization.mk' (FractionRing A) b a) :
    ∃ s ∉ q, s * b ∈ Ideal.span {(a : A)} := by
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
  refine ⟨s, s.2, ?_⟩
  rw [Ideal.mem_span_singleton']
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  have h1 := congrArg (algebraMap (Localization.AtPrime q) (FractionRing A))
    (IsLocalization.mk'_spec (Localization.AtPrime q) c s)
  have h2 := IsLocalization.mk'_spec (FractionRing A) b a
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at h1
  rw [hy] at h1
  simp only [map_mul]
  rw [← h1, ← h2]
  ring

/-- **`A = ⋂_{ht 𝔭 = 1} A_𝔭`** under (S₂) (Stacks, Lemma 10.157.6 (2), argument of loc. cit.). -/
theorem mem_range_of_forall_height_eq_one [IsNoetherianRing A] (hS : AssPrimesHeightOne A)
    (x : FractionRing A)
    (hx : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      x ∈ Set.range (algebraMap (Localization.AtPrime p) (FractionRing A))) :
    x ∈ Set.range (algebraMap A (FractionRing A)) := by
  obtain ⟨⟨b, a⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  have ha : (a : A) ≠ 0 := nonZeroDivisors.ne_zero a.2
  by_contra hne
  set m : A ⧸ Ideal.span {(a : A)} := Ideal.Quotient.mk _ b with hm_def
  have hm : m ≠ 0 := by
    intro h0
    rw [hm_def, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
    obtain ⟨c, rfl⟩ := h0
    exact hne ⟨c, by rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul]⟩
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A m hm
  haveI := hq.isPrime
  obtain ⟨y, hy⟩ := hx q (hS a ha q hq)
  obtain ⟨s, hs, hsb⟩ := exists_mul_mem_span_of_mk'_mem q b a y hy
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hm_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact hsb

/-- **Serre's criterion, (R₁) + (S₂) ⇒ normal**, in the weaker form where (R₁) only asks that
the height-one localisations be integrally closed. -/
theorem isIntegrallyClosed_of_assPrimesHeightOne [IsNoetherianRing A] (hS : AssPrimesHeightOne A)
    (hR : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  refine mem_range_of_forall_height_eq_one hS x fun p _ hp ↦ ?_
  haveI := hR p hp
  haveI : IsFractionRing (Localization.AtPrime p) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ _
  exact IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top)

/-- **Serre's criterion, (R₁) + (S₂) ⇒ normal.** -/
theorem isIntegrallyClosed_of_regularInCodimOne [IsNoetherianRing A]
    (hR : RegularInCodimOne A) (hS : AssPrimesHeightOne A) : IsIntegrallyClosed A :=
  isIntegrallyClosed_of_assPrimesHeightOne hS fun p _ hp ↦ by
    haveI := hR p hp
    infer_instance

/-- **Normal ⇒ (R₁)**: for a Noetherian integrally closed domain, the localisation at a
height-one prime is a discrete valuation ring. -/
theorem regularInCodimOne_of_isIntegrallyClosed [IsNoetherianRing A] [IsIntegrallyClosed A] :
    RegularInCodimOne A := by
  intro p _ hp
  haveI : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]; rfl
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime p) := Ring.krullDimLE_iff.2 hdim.le
  have hnf : ¬ IsField (Localization.AtPrime p) := by
    intro hf
    have := (ringKrullDim_eq_zero_of_isField hf)
    rw [hdim] at this
    exact absurd this (by decide)
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have hm0 : maximalIdeal (Localization.AtPrime p) ≠ ⊥ :=
    (isField_iff_maximalIdeal_eq).not.1 hnf
  have key : IsIntegrallyClosed (Localization.AtPrime p) ∧
      ∃! P : Ideal (Localization.AtPrime p), P ≠ ⊥ ∧ P.IsPrime :=
    ⟨inferInstance, ⟨maximalIdeal _, ⟨hm0, inferInstance⟩, fun P ⟨hP, hP'⟩ ↦
      ((hP'.isMaximal_of_ne_bot hP).eq_of_le (maximalIdeal.isMaximal _).ne_top
        (le_maximalIdeal hP'.ne_top))⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime p) hnf).out 0 3).2 key

/-- **Normal ⇒ (S₂)**: for a Noetherian integrally closed domain, every associated prime of
`A ⧸ (a)`, `a ≠ 0`, has height one (Stacks, Lemma 10.157.6 (1)). We use the classical argument:
if `q = ((a) : y)` then either `(y/a) q ⊆ q`, making `y/a` integral, or `(y/a) q = A_q`, making
`q A_q` principal. -/
theorem assPrimesHeightOne_of_isIntegrallyClosed [IsNoetherianRing A] [IsIntegrallyClosed A] :
    AssPrimesHeightOne A := by
  intro a ha q hq
  haveI := hq.isPrime
  obtain ⟨-, m, hqm⟩ := isAssociatedPrime_iff.1 hq
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
  -- membership in `q`
  have hmem : ∀ r : A, r ∈ q ↔ r * y ∈ Ideal.span {a} := by
    intro r
    rw [hqm, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have haq : a ∈ q := (hmem a).2 (Ideal.mem_span_singleton'.2 ⟨y, mul_comm _ _⟩)
  have hq0 : q ≠ ⊥ := fun h ↦ ha (by simpa [h] using haq)
  have hy : y ∉ Ideal.span {a} := fun h ↦ (Ideal.IsPrime.ne_top ‹_›)
    ((Ideal.eq_top_iff_one _).2 ((hmem 1).2 (by simpa using h)))
  -- for `t ∈ q` write `t * y = w t * a`
  have hw : ∀ t ∈ q, ∃ w : A, w * a = t * y := fun t ht ↦
    Ideal.mem_span_singleton'.1 ((hmem t).1 ht)
  by_cases hcase : ∀ t ∈ q, ∀ w : A, w * a = t * y → w ∈ q
  · -- `y / a` is integral over `A`
    exfalso
    let K := FractionRing A
    let x : K := IsLocalization.mk' K y ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) q
    have hN : N ≠ ⊥ := by
      intro h
      have : algebraMap A K a ∈ N := Submodule.mem_map_of_mem (f := Algebra.linearMap A K) haq
      rw [h, Submodule.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective A K)] at this
      exact ha this
    have hint : IsIntegral A x := by
      refine isIntegral_of_smul_mem_submodule N hN ((IsNoetherian.noetherian q).map _) x ?_
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨w, hw'⟩ := hw t ht
      refine ⟨w, hcase t ht w hw', ?_⟩
      change algebraMap A K w = x * algebraMap A K t
      have ha' : algebraMap A K a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha
      refine mul_right_cancel₀ ha' ?_
      have hx : x * algebraMap A K a = algebraMap A K y := IsLocalization.mk'_spec K y _
      rw [← map_mul, hw', map_mul, mul_right_comm, hx, ← map_mul, ← map_mul, mul_comm]
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff K).1 ‹_› hint
    apply hy
    refine Ideal.mem_span_singleton'.2 ⟨z, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hz, IsLocalization.mk'_spec]
  · push Not at hcase
    obtain ⟨t, ht, u, hu, huq⟩ := hcase
    let B := Localization.AtPrime q
    haveI : IsNoetherianRing B := IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
    have hinj : Function.Injective (algebraMap A B) :=
      IsLocalization.injective B q.primeCompl_le_nonZeroDivisors
    have hut : u * a = t * y := hu
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_mul, mul_eq_zero] at hut
      exact huq (hut.resolve_right ha ▸ q.zero_mem)
    have hmax : maximalIdeal B = Ideal.span {algebraMap A B t} := by
      apply le_antisymm
      · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q B, Ideal.map_le_iff_le_comap]
        intro r hr
        obtain ⟨w, hw'⟩ := hw r hr
        have hur : u * r = w * t := by
          apply mul_right_cancel₀ ha
          calc u * r * a = (u * a) * r := by ring
            _ = t * (r * y) := by rw [hut]; ring
            _ = w * t * a := by rw [← hw']; ring
        rw [Ideal.mem_comap, Ideal.mem_span_singleton']
        refine ⟨IsLocalization.mk' B w (⟨u, huq⟩ : q.primeCompl), ?_⟩
        have hU : IsUnit (algebraMap A B u) := IsLocalization.map_units B (⟨u, huq⟩ : q.primeCompl)
        refine hU.mul_left_inj.1 ?_
        have hs := IsLocalization.mk'_spec B w (⟨u, huq⟩ : q.primeCompl)
        simp only at hs
        rw [mul_right_comm, hs, ← map_mul, ← map_mul, ← hur, mul_comm]
      · rw [Ideal.span_le, Set.singleton_subset_iff,
          ← IsLocalization.AtPrime.map_eq_maximalIdeal q B]
        exact Ideal.mem_map_of_mem _ ht
    have hnf : ¬ IsField B := by
      rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot,
        map_eq_zero_iff _ hinj]
      exact ht0
    have hdvr : IsDiscreteValuationRing B :=
      by
      have hp : (maximalIdeal B).IsPrincipal := ⟨⟨_, hmax⟩⟩
      exact ((IsDiscreteValuationRing.TFAE B hnf).out 0 4).2 hp
    have h1 := IsDiscreteValuationRing.ringKrullDim_eq_one (R := B)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q B] at h1
    exact_mod_cast h1

/-- **Serre's criterion for Noetherian domains** (Stacks, Lemma 10.157.4 = Tag 031S, for
domains, with (S₂) in its associated-primes form): `A` is integrally closed iff it satisfies
(R₁) and (S₂). -/
theorem isIntegrallyClosed_iff_regularInCodimOne_and_assPrimesHeightOne [IsNoetherianRing A] :
    IsIntegrallyClosed A ↔ RegularInCodimOne A ∧ AssPrimesHeightOne A :=
  ⟨fun _ ↦ ⟨regularInCodimOne_of_isIntegrallyClosed, assPrimesHeightOne_of_isIntegrallyClosed⟩,
    fun h ↦ isIntegrallyClosed_of_regularInCodimOne h.1 h.2⟩

/-- A Noetherian integrally closed domain is the intersection of its localisations at height-one
primes (Stacks, Lemma 10.157.6 (2)). -/
theorem mem_range_of_forall_height_eq_one_of_isIntegrallyClosed [IsNoetherianRing A]
    [IsIntegrallyClosed A] (x : FractionRing A)
    (hx : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      x ∈ Set.range (algebraMap (Localization.AtPrime p) (FractionRing A))) :
    x ∈ Set.range (algebraMap A (FractionRing A)) :=
  mem_range_of_forall_height_eq_one assPrimesHeightOne_of_isIntegrallyClosed x hx

end CurvesJacobian
