/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Characters

/-!
# Numerically cuspidal isomorphisms transport cusp lines (G2 applied)

Let `Φ : Δ ≃ₜ* Δ'` be a topological isomorphism and `S`, `S'` sets of cusp groups (conjugation
stable, self-normalising, each the closure of a cyclic group). `Φ` is **numerically cuspidal** if
`r(H) = r'(Φ H)` for every open subgroup `H` ([CombGC] Def 1.4 (ii)).

An element `b ∈ H` **spans the line of the cusp `y`** of `H` (`CurvesJacobian.CuspChar.SameLine`)
if the continuous characters `H → ℤ/p` killing `b` are exactly those unramified at `y`, and some
continuous character does not kill `b`.

Main result (`CurvesJacobian.CuspChar.transport_sameLine`): for numerically cuspidal `Φ`, if `b`
spans the line of a cusp of `H`, then `Φ b` spans the line of a cusp of `Φ H`. The proof combines
the cusp count of cyclic covers (`cuspCount_ker_add`) with hyperplane counting
(`card_mem_span_eq`).
-/

namespace CurvesJacobian.CuspChar

open Module

variable {Δ : Type*} [Group Δ] [TopologicalSpace Δ] [IsTopologicalGroup Δ]
  {Δ' : Type*} [Group Δ'] [TopologicalSpace Δ'] [IsTopologicalGroup Δ']
  {p : ℕ}

/-- `b` spans the line of the cusp `y` of `H` (for continuous `ℤ/p`-characters). -/
def SameLine (p : ℕ) (H : OpenSubgroup Δ) (S : Set (Subgroup Δ)) (b : Δ)
    (y : CuspQuot S (H : Subgroup Δ)) : Prop :=
  (∃ ξ : charSpace p H, ξv (H : Subgroup Δ) ξ.1 b ≠ 0) ∧
    ∀ ξ : charSpace p H, ξv (H : Subgroup Δ) ξ.1 b = 0 ↔ ¬ CuspRam (H : Subgroup Δ) ξ.1 S y

/-- A nonzero additive character to `ℤ/p` is onto. -/
lemma surjective_of_ne_zero' [Fact p.Prime] {A : Type*} [AddGroup A] {ξ : A →+ ZMod p}
    (hξ : ξ ≠ 0) : Function.Surjective ξ := by
  haveI : Fact (Nat.card (ZMod p)).Prime := ⟨by rw [Nat.card_zmod]; exact Fact.out⟩
  rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card ξ.range with h | h
  · exfalso
    apply hξ
    ext a
    have : ξ a ∈ ξ.range := ⟨a, rfl⟩
    rw [h] at this
    simpa using this
  · intro c
    have : c ∈ ξ.range := h ▸ AddSubgroup.mem_top c
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩

omit [TopologicalSpace Δ] [IsTopologicalGroup Δ] in
lemma not_isRam_zero (H : Subgroup Δ) (I : Subgroup Δ) :
    ¬ IsRam H (0 : Additive H →+ ZMod p) I := by
  rintro ⟨x, -, hxH, hx⟩
  exact hx (by rw [ξv_of_mem hxH]; rfl)

/-- Ramified cusps of `H` and of `Φ H` correspond in number, for characters corresponding under
`Φ`, if `Φ` is numerically cuspidal. -/
lemma ramCusps_pullChar [Fact p.Prime] (Φ : Δ ≃ₜ* Δ') {S : Set (Subgroup Δ)}
    {S' : Set (Subgroup Δ')} (hS : ConjStable S) (hN : ∀ I ∈ S, ∀ g : Δ, conjSub g I = I → g ∈ I)
    (hS' : ConjStable S') (hN' : ∀ I ∈ S', ∀ g : Δ', conjSub g I = I → g ∈ I)
    (hfin : ∀ H : OpenSubgroup Δ, Finite (CuspQuot S (H : Subgroup Δ)))
    (hfin' : ∀ H : OpenSubgroup Δ', Finite (CuspQuot S' (H : Subgroup Δ')))
    (hnum : ∀ H : OpenSubgroup Δ, cuspCount S (H : Subgroup Δ) =
      cuspCount S' (mapOpenSub Φ H : Subgroup Δ'))
    (H : OpenSubgroup Δ) (ξ : charSpace p (mapOpenSub Φ H)) :
    ramCusps (H : Subgroup Δ) (pullChar Φ H ξ.1) S =
      ramCusps (mapOpenSub Φ H : Subgroup Δ') ξ.1 S' := by
  by_cases h0 : ξ.1 = 0
  · have h0' : pullChar Φ H (0 : Additive (mapOpenSub Φ H : Subgroup Δ') →+ ZMod p) = 0 :=
      AddMonoidHom.zero_comp _
    unfold ramCusps
    rw [h0, h0']
    have e1 : IsEmpty {y : CuspQuot S (H : Subgroup Δ) //
        CuspRam (H : Subgroup Δ) (0 : Additive (H : Subgroup Δ) →+ ZMod p) S y} := by
      refine ⟨fun ⟨y, hy⟩ ↦ ?_⟩
      induction y using Quotient.inductionOn with
      | h I => exact not_isRam_zero _ _ hy
    have e2 : IsEmpty {y : CuspQuot S' (mapOpenSub Φ H : Subgroup Δ') //
        CuspRam (mapOpenSub Φ H : Subgroup Δ')
          (0 : Additive (mapOpenSub Φ H : Subgroup Δ') →+ ZMod p) S' y} := by
      refine ⟨fun ⟨y, hy⟩ ↦ ?_⟩
      induction y using Quotient.inductionOn with
      | h I => exact not_isRam_zero _ _ hy
    simp [Nat.card_of_isEmpty]
  have hsurj' := surjective_of_ne_zero' h0
  have hsurj : Function.Surjective (pullChar Φ H ξ.1) := by
    intro c
    obtain ⟨z, hz⟩ := hsurj' c
    obtain ⟨y, hy⟩ := z
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨Additive.ofMul ⟨x, hx⟩, hz⟩
  have : Finite (CuspQuot S (H : Subgroup Δ)) := hfin H
  have : Finite (CuspQuot S' (mapOpenSub Φ H : Subgroup Δ')) := hfin' _
  -- the kernel as an open subgroup
  let K : OpenSubgroup Δ := ⟨kerSub (H : Subgroup Δ) (pullChar Φ H ξ.1), pullChar_mem Φ H ξ.2⟩
  have hK : (mapOpenSub Φ K : Subgroup Δ') = kerSub (mapOpenSub Φ H : Subgroup Δ') ξ.1 :=
    map_kerSub_pullChar Φ H ξ.1
  refine ramCusps_eq_of_cuspCount_eq (H : Subgroup Δ) (pullChar Φ H ξ.1) hS hN hsurj hS' hN'
    hsurj' (hnum H) ?_
  have := hnum K
  rw [hK] at this
  exact this

/-- For linear forms `g`, `f` on a vector space: `g` is a nonzero multiple of `f` iff `f ≠ 0`
and `f`, `g` have the same kernel. -/
lemma ne_zero_and_mem_span_iff [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (f g : Dual (ZMod p) V) :
    (g ≠ 0 ∧ g ∈ Submodule.span (ZMod p) {f}) ↔ (f ≠ 0 ∧ ∀ v, f v = 0 ↔ g v = 0) := by
  constructor
  · rintro ⟨hg, hspan⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hspan
    have hc : c ≠ 0 := by rintro rfl; exact hg (zero_smul _ _)
    refine ⟨fun hf ↦ hg (by rw [hf, smul_zero]), fun v ↦ ?_⟩
    simp [hc]
  · rintro ⟨hf, hker⟩
    refine ⟨fun hg ↦ hf (LinearMap.ext fun v ↦ (hker v).2 (by simp [hg])), ?_⟩
    by_contra hns
    apply restrict_ne_zero hns
    ext ⟨v, hv⟩
    simpa using (hker v).1 (LinearMap.mem_ker.1 hv)

/-- The cusp forms: evaluation at a generator of `I_y ∩ ⟨a_y⟩` for the representative `I_y` of
the cusp `y`, characterised by `cuspForm_ne_zero_iff`. -/
lemma exists_cuspForm (H : OpenSubgroup Δ) {S : Set (Subgroup Δ)}
    (hcyc : ∀ I ∈ S, ∃ a : Δ, I = (Subgroup.zpowers a).topologicalClosure)
    (y : CuspQuot S (H : Subgroup Δ)) :
    ∃ c, ∃ hc : c ∈ (H : Subgroup Δ), ∀ ξ : charSpace p H,
      evAt c hc ξ ≠ 0 ↔ CuspRam (H : Subgroup Δ) ξ.1 S y := by
  induction y using Quotient.inductionOn with
  | h I =>
  obtain ⟨a, ha⟩ := hcyc I I.2
  obtain ⟨c, -, hcH, hc⟩ := exists_gen (p := p) (H := H) a
  refine ⟨c, hcH, fun ξ ↦ ?_⟩
  change _ ↔ IsRam (H : Subgroup Δ) ξ.1 I
  rw [evAt_apply, Ne, hc ξ, IsRam, ← ha]
  push Not
  rfl

/-- **Numerically cuspidal isomorphisms transport cusp lines.** -/
theorem transport_sameLine [Fact p.Prime] (Φ : Δ ≃ₜ* Δ') {S : Set (Subgroup Δ)}
    {S' : Set (Subgroup Δ')} (hS : ConjStable S) (hN : ∀ I ∈ S, ∀ g : Δ, conjSub g I = I → g ∈ I)
    (hS' : ConjStable S') (hN' : ∀ I ∈ S', ∀ g : Δ', conjSub g I = I → g ∈ I)
    (hcyc : ∀ I ∈ S, ∃ a : Δ, I = (Subgroup.zpowers a).topologicalClosure)
    (hcyc' : ∀ I ∈ S', ∃ a : Δ', I = (Subgroup.zpowers a).topologicalClosure)
    (hfin : ∀ H : OpenSubgroup Δ, Finite (CuspQuot S (H : Subgroup Δ)))
    (hfin' : ∀ H : OpenSubgroup Δ', Finite (CuspQuot S' (H : Subgroup Δ')))
    (hV : ∀ H : OpenSubgroup Δ, Finite (charSpace p H))
    (hnum : ∀ H : OpenSubgroup Δ, cuspCount S (H : Subgroup Δ) =
      cuspCount S' (mapOpenSub Φ H : Subgroup Δ'))
    (H : OpenSubgroup Δ) {b : Δ} (hb : b ∈ (H : Subgroup Δ))
    (hy : ∃ y, SameLine p H S b y) :
    ∃ y', SameLine p (mapOpenSub Φ H) S' (Φ b) y' := by
  classical
  set H' := mapOpenSub Φ H
  have hb' : Φ b ∈ (H' : Subgroup Δ') := mem_mapOpenSub.2 hb
  let T : charSpace p H' ≃ₗ[ZMod p] charSpace p H := pullEquiv Φ H
  have : Finite (charSpace p H) := hV H
  have : Finite (charSpace p H') := Finite.of_equiv _ T.toEquiv.symm
  have : Finite (CuspQuot S (H : Subgroup Δ)) := hfin H
  have : Finite (CuspQuot S' (H' : Subgroup Δ')) := hfin' H'
  let := Fintype.ofFinite (charSpace p H)
  let := Fintype.ofFinite (charSpace p H')
  let := Fintype.ofFinite (CuspQuot S (H : Subgroup Δ))
  let := Fintype.ofFinite (CuspQuot S' (H' : Subgroup Δ'))
  choose c hcH hc using exists_cuspForm (p := p) H hcyc
  choose c' hcH' hc' using exists_cuspForm (p := p) H' hcyc'
  let f : CuspQuot S (H : Subgroup Δ) → Dual (ZMod p) (charSpace p H) := fun y ↦ evAt (c y) (hcH y)
  let f' : CuspQuot S' (H' : Subgroup Δ') → Dual (ZMod p) (charSpace p H') :=
    fun y ↦ evAt (c' y) (hcH' y)
  -- ramification counts agree
  have hcount : ∀ ξ', ramCount f (T ξ') = ramCount f' ξ' := by
    intro ξ'
    have e := ramCusps_pullChar Φ hS hN hS' hN' hfin hfin' hnum H ξ'
    unfold ramCusps at e
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_subtype] at e
    unfold ramCount
    convert e using 3
    · exact hc _ (T ξ')
    · exact hc' _ ξ'
  set fB : Dual (ZMod p) (charSpace p H) := evAt b hb
  have hfB : fB.comp T.toLinearMap = evAt (Φ b) hb' := by
    ext ξ'
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, fB, evAt_apply]
    exact ξv_pullChar Φ H ξ'.1 b
  have hiff : ∀ y, SameLine p H S b y ↔ (f y ≠ 0 ∧ f y ∈ Submodule.span (ZMod p) {fB}) := by
    intro y
    rw [ne_zero_and_mem_span_iff]
    unfold SameLine
    apply and_congr
    · constructor
      · rintro ⟨ξ, hξ⟩ h0
        exact hξ (by rw [← evAt_apply hb]; simp [fB, h0])
      · intro h0
        by_contra hall
        push Not at hall
        exact h0 (LinearMap.ext fun ξ ↦ by rw [evAt_apply hb]; exact hall ξ)
    · apply forall_congr'
      intro ξ
      rw [← evAt_apply hb, ← hc y ξ, not_not]
  have hiff' : ∀ y', SameLine p H' S' (Φ b) y' ↔
      (f' y' ≠ 0 ∧ f' y' ∈ Submodule.span (ZMod p) {evAt (Φ b) hb'}) := by
    intro y
    rw [ne_zero_and_mem_span_iff]
    unfold SameLine
    apply and_congr
    · constructor
      · rintro ⟨ξ, hξ⟩ h0
        exact hξ (by rw [← evAt_apply hb']; simp [h0])
      · intro h0
        by_contra hall
        push Not at hall
        exact h0 (LinearMap.ext fun ξ ↦ by rw [evAt_apply hb']; exact hall ξ)
    · apply forall_congr'
      intro ξ
      rw [← evAt_apply hb', ← hc' y ξ, not_not]
  have hcard := card_mem_span_eq T f f' hcount fB
  rw [hfB] at hcard
  obtain ⟨y, hy⟩ := hy
  have hpos : 0 < (Finset.univ.filter fun y ↦
      f y ≠ 0 ∧ f y ∈ Submodule.span (ZMod p) {fB}).card :=
    Finset.card_pos.2 ⟨y, by simpa using (hiff y).1 hy⟩
  rw [hcard] at hpos
  obtain ⟨y', hy'⟩ := Finset.card_pos.1 hpos
  exact ⟨y', (hiff' y').2 (by simpa using hy')⟩

end CurvesJacobian.CuspChar
