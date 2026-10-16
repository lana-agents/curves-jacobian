/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CommAlg.RegularLocal

/-!
# Depth and Serre's conditions (S_k)

* `CurvesJacobian.depth I M : ℕ∞` — the `I`-depth of `M` (Stacks, Definition 10.72.1 =
  Tag 00LI): `⊤` if `I M = M`, otherwise the supremum of the lengths of `M`-regular sequences
  (Stacks Tag 00LF = Mathlib's `RingTheory.Sequence.IsRegular`) with entries in `I`.
* `CurvesJacobian.SerreS k A` — Serre's condition (S_k) (Stacks, Definition 10.157.1 =
  Tag 031P): `depth A_𝔭 ≥ min(k, dim A_𝔭)` for every prime `𝔭`.

Main results:

* `CurvesJacobian.depthGeTwo_iff`: for a Noetherian local ring, `DepthGeTwo B ↔ 2 ≤ depth 𝔪 B`;
* `CurvesJacobian.serreS_two_iff_serreS2`: for a Noetherian domain, (S₂) in the sense of
  `SerreS 2` is the condition `SerreS2` of `SerreS2.lean`;
* `CurvesJacobian.isIntegrallyClosed_iff_serreR1_and_serreS_two`: Serre's criterion
  (Stacks, Lemma 10.157.4 = Tag 031S) for Noetherian domains with the definitions of loc. cit.
-/

open IsLocalRing Pointwise RingTheory.Sequence

namespace CurvesJacobian

variable {R : Type*} [CommRing R]

/-- The `I`-depth of `M` (Stacks, Definition 10.72.1). -/
noncomputable def depth (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  open Classical in
  if I • (⊤ : Submodule R M) = ⊤ then ⊤ else
    ⨆ (rs : List R) (_ : ∀ r ∈ rs, r ∈ I) (_ : IsRegular M rs), (rs.length : ℕ∞)

lemma two_le_coe_iff {e : ℕ∞} : (2 : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) ↔ 2 ≤ e :=
  WithBot.coe_le_coe

/-- **Serre's condition (S_k)** for a ring (Stacks, Definition 10.157.1). -/
def SerreS (k : ℕ) (A : Type*) [CommRing A] : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p)) ≤
    (depth (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) : WithBot ℕ∞)

section Local

variable [IsLocalRing R]

lemma depth_maximalIdeal_eq_iSup :
    depth (maximalIdeal R) R =
      ⨆ (rs : List R) (_ : ∀ r ∈ rs, r ∈ maximalIdeal R) (_ : IsRegular R rs),
        (rs.length : ℕ∞) := by
  rw [depth, if_neg]
  rw [smul_eq_mul, Ideal.mul_top]
  exact (maximalIdeal.isMaximal R).ne_top

lemma le_depth_of_isRegular {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hreg : IsRegular R rs) : (rs.length : ℕ∞) ≤ depth (maximalIdeal R) R := by
  rw [depth_maximalIdeal_eq_iSup]
  exact le_iSup_of_le rs (le_iSup_of_le hrs (le_iSup_of_le hreg le_rfl))

variable [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- For a local ring, `depth ≥ 2` iff the maximal ideal contains a regular sequence
of length two. -/
theorem depthGeTwo_iff : DepthGeTwo R ↔ 2 ≤ depth (maximalIdeal R) R := by
  constructor
  · rintro ⟨x, hx, y, hy, hreg⟩
    have := le_depth_of_isRegular (rs := [x, y]) (fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hx, hy]) hreg
    simpa using this
  · intro h
    by_contra hne
    have hle : depth (maximalIdeal R) R ≤ 1 := by
      rw [depth_maximalIdeal_eq_iSup]
      refine iSup₂_le fun rs hrs ↦ iSup_le fun hreg ↦ ?_
      match rs, hrs, hreg with
      | [], _, _ => simp
      | [_], _, _ => simp
      | x :: y :: rest, hrs, hreg =>
        exfalso
        apply hne
        have hw : IsWeaklyRegular R [x, y] :=
          ((isWeaklyRegular_append_iff R [x, y] rest).1 hreg.toIsWeaklyRegular).1
        refine ⟨x, hrs x (by simp), y, hrs y (by simp), ?_⟩
        refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R ?_ hw
        intro r hr
        exact hrs r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
    exact absurd (h.trans hle) (by decide)

omit [IsNoetherianRing R] in
/-- In a local domain which is not a field, the depth is at least one. -/
lemma one_le_depth_of_isDomain [IsDomain R] (h : maximalIdeal R ≠ ⊥) :
    1 ≤ depth (maximalIdeal R) R := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hreg : IsRegular R [x] := by
    refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R (by simpa using hx) ?_
    rw [isWeaklyRegular_singleton_iff]
    exact fun u v huv ↦ mul_left_cancel₀ hx0 huv
  simpa using le_depth_of_isRegular (by simpa using hx) hreg

end Local

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- For a Noetherian domain, `SerreS 2` (Stacks' (S₂)) is equivalent to `SerreS2`. -/
theorem serreS_two_iff_serreS2 : SerreS 2 A ↔ SerreS2 A := by
  constructor
  · intro h p _ hp
    haveI : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    have h' := h p
    have hdim : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, Nat.cast_ofNat]
      exact two_le_coe_iff.2 hp
    rw [min_eq_left hdim, Nat.cast_ofNat] at h'
    rw [depthGeTwo_iff]
    exact two_le_coe_iff.1 h'
  · intro h p _
    haveI : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ideal.height_ne_top_of_isPrime (I := p))
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h2
    · rw [← hn]
      refine (min_le_right _ _).trans ?_
      exact WithBot.coe_le_coe.2 (by simp)
    · refine (min_le_right _ _).trans ?_
      rw [← hn]
      have hm : maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
        intro hbot
        have hf : IsField (Localization.AtPrime p) := (isField_iff_maximalIdeal_eq).2 hbot
        have := ringKrullDim_eq_zero_of_isField hf
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, ← hn] at this
        exact absurd this (by decide)
      exact_mod_cast one_le_depth_of_isDomain hm
    · refine (min_le_left _ _).trans ?_
      have hp : 2 ≤ p.height := by rw [← hn]; exact_mod_cast h2
      have := (depthGeTwo_iff).1 (h p hp)
      rw [Nat.cast_ofNat]
      exact two_le_coe_iff.2 this

/-- **Serre's criterion for normality** (Stacks, Lemma 10.157.4 = Tag 031S) for Noetherian
domains, with (R₁) and (S₂) exactly as in Stacks, Definition 10.157.1. -/
theorem isIntegrallyClosed_iff_serreR1_and_serreS_two :
    IsIntegrallyClosed A ↔ SerreR1 A ∧ SerreS 2 A := by
  rw [serreS_two_iff_serreS2]
  exact isIntegrallyClosed_iff_serreR1_and_serreS2

end CurvesJacobian
