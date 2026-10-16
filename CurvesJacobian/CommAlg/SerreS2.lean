/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CommAlg.SerreCriterion
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Serre's condition (S₂) via regular sequences

For a Noetherian local ring `B` the depth (Stacks, Definition 10.72.1 = Tag 00LI) is the
supremum of the lengths of `B`-regular sequences in the maximal ideal (regular sequences as in
Stacks, Definition 10.68.1 = Tag 00LF, which is Mathlib's `RingTheory.Sequence.IsRegular`).
Serre's condition (S₂) (Stacks, Definition 10.157.1 = Tag 031P) asks
`depth A_𝔭 ≥ min(2, dim A_𝔭)` for every prime `𝔭`. For a domain, the cases `dim A_𝔭 ≤ 1` are
automatic (a nonzero element of `𝔭 A_𝔭` is regular), so (S₂) says: for every prime `𝔭` of height
`≥ 2` the maximal ideal of `A_𝔭` contains a regular sequence of length two. This is
`CurvesJacobian.SerreS2`.

Main results, for a Noetherian domain `A`:

* `CurvesJacobian.serreS2_iff_assPrimesHeightOne`: (S₂) holds iff every associated prime of
  `A ⧸ (a)`, `a ≠ 0`, has height one (the form used in `SerreCriterion.lean`);
* `CurvesJacobian.isIntegrallyClosed_iff_regularInCodimOne_and_serreS2`:
  **Serre's criterion** (Stacks, Lemma 10.157.4 = Tag 031S, for Noetherian domains):
  `A` is normal iff it satisfies (R₁) and (S₂).

The proofs are elementary (no `Ext`): the key step is
`CurvesJacobian.mem_span_of_isWeaklyRegular_pair`.
-/

open IsLocalRing RingTheory.Sequence Pointwise

namespace CurvesJacobian

section Pair

variable {B : Type*} [CommRing B]

lemma mem_smul_top_iff_mem_span (x c : B) :
    c ∈ x • (⊤ : Submodule B B) ↔ c ∈ Ideal.span {x} := by
  rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
  simp [smul_eq_mul, mul_comm]

/-- A pair `[x, y]` is weakly regular on `B` iff `x` is a non-zero-divisor and `y` is a
non-zero-divisor modulo `x`. -/
lemma isWeaklyRegular_pair_iff (x y : B) :
    IsWeaklyRegular B [x, y] ↔
      IsSMulRegular B x ∧ ∀ c : B, y * c ∈ Ideal.span {x} → c ∈ Ideal.span {x} := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  constructor
  · intro h c hc
    have := h (Submodule.Quotient.mk c) (by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        mem_smul_top_iff_mem_span]
      exact hc)
    rwa [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_mem_span] at this
  · intro h m hm
    induction m using Submodule.Quotient.induction_on with
    | H c =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        mem_smul_top_iff_mem_span, smul_eq_mul] at hm
      rw [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_mem_span]
      exact h c hm

/-- If `[x, z]` is weakly regular on a domain `B`, `a ≠ 0` and `x Y, z Y ∈ (a)`, then `Y ∈ (a)`.
(In other words, if `depth B ≥ 2` then the maximal ideal is not associated to `B ⧸ (a)`.) -/
lemma mem_span_of_isWeaklyRegular_pair [IsDomain B] {x z a Y : B} (ha : a ≠ 0)
    (h : IsWeaklyRegular B [x, z]) (hx : x * Y ∈ Ideal.span {a})
    (hz : z * Y ∈ Ideal.span {a}) : Y ∈ Ideal.span {a} := by
  rw [isWeaklyRegular_pair_iff] at h
  obtain ⟨hreg, hzreg⟩ := h
  obtain ⟨b1, hb1⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨b2, hb2⟩ := Ideal.mem_span_singleton'.1 hz
  have hzb : z * b1 = x * b2 := by
    apply mul_right_cancel₀ ha
    calc z * b1 * a = z * (x * Y) := by rw [mul_assoc, hb1]
      _ = x * (z * Y) := by ring
      _ = x * b2 * a := by rw [← hb2]; ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1
    (hzreg b1 (Ideal.mem_span_singleton'.2 ⟨b2, by rw [hzb, mul_comm]⟩))
  refine Ideal.mem_span_singleton'.2 ⟨c, hreg ?_⟩
  simp only [smul_eq_mul]
  rw [← hb1, ← hc]
  ring

end Pair

/-- The maximal ideal of the local ring `B` contains a `B`-regular sequence of length two,
i.e. `depth B ≥ 2` (Stacks, Definition 10.72.1). -/
def DepthGeTwo (B : Type*) [CommRing B] [IsLocalRing B] : Prop :=
  ∃ x ∈ maximalIdeal B, ∃ y ∈ maximalIdeal B, IsRegular B [x, y]

/-- **Serre's condition (S₂)** for a domain `A`: `depth A_𝔭 ≥ 2` for every prime `𝔭` of height
`≥ 2` (for primes of height `≤ 1` of a domain, `depth A_𝔭 ≥ min(2, dim A_𝔭)` is automatic). -/
def SerreS2 (A : Type*) [CommRing A] : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], 2 ≤ p.height → DepthGeTwo (Localization.AtPrime p)

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

omit [IsDomain A] [IsNoetherianRing A] in
/-- Membership in an associated prime `q = ((a) : y)` of `A ⧸ (a)`. -/
lemma mem_iff_mul_mem_of_eq_colon {a y : A} {q : Ideal A}
    (hqm : q = (⊥ : Submodule A (A ⧸ Ideal.span {a})).colon {Ideal.Quotient.mk _ y}) (r : A) :
    r ∈ q ↔ r * y ∈ Ideal.span {a} := by
  rw [hqm, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

/-- (S₂) ⇒ the associated primes of `A ⧸ (a)`, `a ≠ 0`, have height one. -/
theorem assPrimesHeightOne_of_serreS2 (h : SerreS2 A) : AssPrimesHeightOne A := by
  intro a ha q hq
  haveI := hq.isPrime
  obtain ⟨-, m, hqm⟩ := isAssociatedPrime_iff.1 hq
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
  have hmem := mem_iff_mul_mem_of_eq_colon hqm
  have haq : a ∈ q := (hmem a).2 (Ideal.mem_span_singleton'.2 ⟨y, mul_comm _ _⟩)
  have hq0 : q ≠ ⊥ := fun h ↦ ha (by simpa [h] using haq)
  by_contra hne
  have h2 : 2 ≤ q.height := by
    have h0 : q.height ≠ 0 := fun h ↦ hq0 (Ideal.height_eq_zero_iff_eq_bot.1 h)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ideal.height_ne_top_of_isPrime (I := q))
    rw [← hn] at h0 hne ⊢
    norm_cast at h0 hne ⊢
    omega
  obtain ⟨x, hx, z, hz, hreg⟩ := h q h2
  let B := Localization.AtPrime q
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B q.primeCompl_le_nonZeroDivisors
  have key : ∀ w ∈ maximalIdeal B, w * algebraMap A B y ∈ Ideal.span {algebraMap A B a} := by
    intro w hw
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl w
    have hr : r ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff B q r,
        ← IsLocalization.mk'_spec B r s]
      exact Ideal.mul_mem_right _ _ hw
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 ((hmem r).1 hr)
    refine Ideal.mem_span_singleton'.2 ⟨IsLocalization.mk' B u s, ?_⟩
    rw [mul_comm, mul_comm (IsLocalization.mk' B r s), IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm a, hu, mul_comm]
  have ha' : algebraMap A B a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1
    (mem_span_of_isWeaklyRegular_pair ha' hreg.toIsWeaklyRegular (key x hx) (key z hz))
  obtain ⟨⟨c0, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl c
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul,
    ← map_mul] at hc
  have hsy : s * y ∈ Ideal.span {a} :=
    Ideal.mem_span_singleton'.2 ⟨c0, by rw [mul_comm c0, hinj hc, mul_comm]⟩
  exact s.2 ((hmem s).2 hsy)

/-- The associated primes of `A ⧸ (a)`, `a ≠ 0`, have height one ⇒ (S₂). -/
theorem serreS2_of_assPrimesHeightOne (h : AssPrimesHeightOne A) : SerreS2 A := by
  intro p _ hp
  have hp0 : p ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hp
    exact absurd hp (by decide)
  obtain ⟨a, hap, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hfin := associatedPrimes.finite A (A ⧸ Ideal.span {a})
  have hnsub : ¬ ((p : Set A) ⊆ ⋃ q ∈ associatedPrimes A (A ⧸ Ideal.span {a}), (q : Set A)) := by
    intro hsub
    obtain ⟨q, hq, hle⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
      (fun q hq _ _ ↦ hq.isPrime)).1 hsub
    have hle' := Ideal.height_mono hle
    rw [id, h a ha q hq] at hle'
    exact absurd (hp.trans hle') (by decide)
  obtain ⟨y, hyp, hyn⟩ := Set.not_subset.1 hnsub
  have hyreg : ∀ c : A, y * c ∈ Ideal.span {a} → c ∈ Ideal.span {a} := by
    intro c hc
    by_contra hcn
    have hmc : (Ideal.Quotient.mk (Ideal.span {a}) c) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hmc
    apply hyn
    refine Set.mem_biUnion hq (hle ?_)
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hc
  let B := Localization.AtPrime p
  haveI : IsNoetherianRing B := IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B p.primeCompl_le_nonZeroDivisors
  have ha' : algebraMap A B a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hmax : ∀ r ∈ p, algebraMap A B r ∈ maximalIdeal B := fun r hr ↦
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B p r).2 hr
  refine ⟨_, hmax a hap, _, hmax y hyp, ?_⟩
  refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal B ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hmax a hap, hmax y hyp]
  rw [isWeaklyRegular_pair_iff]
  refine ⟨fun u v huv ↦ mul_left_cancel₀ ha' huv, fun c hc ↦ ?_⟩
  obtain ⟨⟨c0, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
  obtain ⟨⟨d, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl e
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq] at he
  have he' := hinj he
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1
    (hyreg ((t : A) * c0) (Ideal.mem_span_singleton'.2 ⟨s * d, by
      linear_combination he'⟩))
  refine Ideal.mem_span_singleton'.2 ⟨IsLocalization.mk' B f (t * s), ?_⟩
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
  congr 1
  push_cast
  linear_combination (s : A) * hf

/-- For a Noetherian domain, (S₂) is equivalent to: every associated prime of `A ⧸ (a)`,
`a ≠ 0`, has height one. -/
theorem serreS2_iff_assPrimesHeightOne : SerreS2 A ↔ AssPrimesHeightOne A :=
  ⟨assPrimesHeightOne_of_serreS2, serreS2_of_assPrimesHeightOne⟩

/-- **Serre's criterion for normality** (Stacks, Lemma 10.157.4 = Tag 031S, for Noetherian
domains): `A` is integrally closed iff it satisfies (R₁) and (S₂). -/
theorem isIntegrallyClosed_iff_regularInCodimOne_and_serreS2 :
    IsIntegrallyClosed A ↔ RegularInCodimOne A ∧ SerreS2 A := by
  rw [serreS2_iff_assPrimesHeightOne]
  exact isIntegrallyClosed_iff_regularInCodimOne_and_assPrimesHeightOne

/-- **Serre's condition (R₁)** (Stacks, Definition 10.157.1 = Tag 031P): `A_𝔭` is a regular
local ring for every prime `𝔭` of height `≤ 1`. -/
def SerreR1 (A : Type*) [CommRing A] : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], p.height ≤ 1 → IsRegularLocalRing (Localization.AtPrime p)

/-- For a Noetherian domain, (R₁) in the sense of regular local rings is equivalent to
`A_𝔭` being a discrete valuation ring for every height-one prime `𝔭`. -/
theorem serreR1_iff_regularInCodimOne : SerreR1 A ↔ RegularInCodimOne A := by
  constructor
  · intro h p _ hp
    have hreg := h p hp.le
    have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]; rfl
    have hnf : ¬ IsField (Localization.AtPrime p) := by
      intro hf
      have := ringKrullDim_eq_zero_of_isField hf
      rw [hdim] at this
      exact absurd this (by decide)
    have hcot : Module.finrank (ResidueField (Localization.AtPrime p))
        (CotangentSpace (Localization.AtPrime p)) = 1 := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace _).1 hreg
      rw [hdim] at this
      exact_mod_cast this
    exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime p) hnf).out 0 5).2 hcot
  · intro h p _ hp
    rcases (show p.height = 0 ∨ p.height = 1 by
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ideal.height_ne_top_of_isPrime (I := p))
      rw [← hn] at hp ⊢
      norm_cast at hp ⊢
      omega) with h0 | h1
    · have hp0 : p = ⊥ := Ideal.height_eq_zero_iff_eq_bot.1 h0
      haveI : IsNoetherianRing (Localization.AtPrime p) :=
        IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
      apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
      have hm : maximalIdeal (Localization.AtPrime p) = ⊥ := by
        rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
        exact (Ideal.map_eq_bot_iff_le_ker _).2 (fun x hx ↦ by
          rw [hp0, Ideal.mem_bot] at hx; rw [hx]; exact zero_mem _)
      rw [hm, Submodule.spanFinrank_bot]
      exact ringKrullDim_nonneg_of_nontrivial
    · haveI := h p h1
      infer_instance

/-- **Serre's criterion for normality**, in the form of Stacks, Lemma 10.157.4 (Tag 031S), for
Noetherian domains: `A` is normal iff it has properties (R₁) and (S₂). -/
theorem isIntegrallyClosed_iff_serreR1_and_serreS2 :
    IsIntegrallyClosed A ↔ SerreR1 A ∧ SerreS2 A := by
  rw [serreR1_iff_regularInCodimOne]
  exact isIntegrallyClosed_iff_regularInCodimOne_and_serreS2

end CurvesJacobian
