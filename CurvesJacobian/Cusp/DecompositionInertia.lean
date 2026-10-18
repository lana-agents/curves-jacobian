/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Valuation.Integral
import CurvesJacobian.Cusp.Inertia
import CurvesJacobian.Cusp.PlaceTransitivity

/-!
# Decomposition group = inertia group for places over an algebraically closed field (MR8.3)

Let `k` be algebraically closed, `Ω / k` a field extension of transcendence degree `≤ 1` (e.g. an
algebraic extension of `k(t)`) and `W ⊊ Ω` a proper valuation subring containing `k`. Then

* `CurvesJacobian.Cusp.exists_valuation_sub_lt_one`: **the residue field of `W` is `k`**: every
  `a ∈ W` is congruent to a constant `c ∈ k` modulo the maximal ideal of `W`;
* `CurvesJacobian.Cusp.mem_inertia_of_comap_eq`: **`D_W = I_W`** — every automorphism `σ` of `Ω`
  over a subfield containing `k` which fixes the place `W` (`σ⁻¹(W) = W`) lies in the inertia
  group `GaloisPi1.inertia W` (it acts trivially on the residue field `k`).

In the setting of `CurvesJacobian/Cusp/Inertia.lean` (`Ω` Galois over `K₀ k t = k(t)`), the places
`W ⊇ k` not centred on an open `U` are proper (`ne_top_of_not_isCentredOn`), so the decomposition
group of a cusp place equals its inertia group (`mem_inertia_of_comap_eq_of_not_isCentredOn`).
This is the "same place at every level" step of the algebraic route to the commensurator
condition on cuspidal inertia ([AbsTopI] Lemma 4.1 (i), `Topics in Absolute Anabelian Geometry
I.txt` l.2741–2745: cuspidal decomposition groups are commensurably terminal; for a curve over an
algebraically closed field the decomposition group of a cusp is its inertia group).

## Proof of the residue field statement

If `ā ∉ k` for some `a ∈ W`, then all `a - c` (`c ∈ k`) are units of `W`, hence (`k`
algebraically closed, every polynomial splits) `f(a)` is a unit of `W` for every `f ≠ 0` in `k[X]`.
In particular `a` is transcendental over `k`, so (transcendence degree `≤ 1`) `Ω` is algebraic
over `k[a]`. For `x ∈ Ω` some `y ≠ 0` in `k[a]` makes `y x` integral over `k[a] ⊆ W`; since `W` is
integrally closed and `y` is a unit of `W`, `x ∈ W`. So `W = Ω`, a contradiction.
-/

open Polynomial Cardinal

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section ResidueField

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (W : ValuationSubring Ω)
  (hk : ∀ c : k, algebraMap k Ω c ∈ W)

include hk in
/-- Nonzero constants are units of `W`. -/
lemma valuation_algebraMap_eq_one {c : k} (hc : c ≠ 0) :
    W.valuation (algebraMap k Ω c) = 1 := by
  apply le_antisymm ((W.valuation_le_one_iff _).2 (hk c))
  have h1 := (W.valuation_le_one_iff _).2 (hk c⁻¹)
  have h2 : W.valuation (algebraMap k Ω c) * W.valuation (algebraMap k Ω c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  calc (1 : _) = _ := h2.symm
    _ ≤ W.valuation (algebraMap k Ω c) * 1 := mul_le_mul_right h1 _
    _ = _ := mul_one _

variable [IsAlgClosed k]

include hk in
/-- If all `a - c` (`c ∈ k`) are units of `W`, then so is `f(a)` for every nonzero `f ∈ k[X]`. -/
lemma valuation_aeval_eq_one {a : Ω} (ha : ∀ c : k, W.valuation (a - algebraMap k Ω c) = 1)
    {f : k[X]} (hf : f ≠ 0) : W.valuation (aeval a f) = 1 := by
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := f))]
  simp only [map_mul, aeval_C, map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub,
    aeval_X, ha, valuation_algebraMap_eq_one W hk (leadingCoeff_ne_zero.2 hf), one_mul,
    Multiset.map_const', Multiset.prod_replicate, one_pow]

include hk in
/-- **The residue field of a proper valuation subring `W ⊇ k` of a field of transcendence degree
`≤ 1` over the algebraically closed field `k` is `k`.** -/
theorem exists_valuation_sub_lt_one (htr : Algebra.trdeg k Ω ≤ 1) (hW : W ≠ ⊤) {a : Ω}
    (ha : a ∈ W) : ∃ c : k, W.valuation (a - algebraMap k Ω c) < 1 := by
  by_contra! h
  have h1 : ∀ c : k, W.valuation (a - algebraMap k Ω c) = 1 := fun c ↦
    le_antisymm ((W.valuation_le_one_iff _).2 (W.sub_mem ha (hk c))) (h c)
  have htra : Transcendental k a := by
    rintro ⟨p, hp, hpa⟩
    have := valuation_aeval_eq_one W hk h1 hp
    rw [hpa, map_zero] at this
    exact zero_ne_one this
  have hind : AlgebraicIndependent k (fun _ : PUnit.{u + 1} ↦ a) :=
    algebraicIndependent_unique_type_iff.2 htra
  have hbasis := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg := hbasis.isAlgebraic
  -- the nonzero elements of `k[a]` are units of `W`
  have hadj : ∀ y : Algebra.adjoin k (Set.range fun _ : PUnit.{u + 1} ↦ a),
      y ≠ 0 → W.valuation (y : Ω) = 1 := by
    rintro ⟨z, hz⟩ hy0
    rw [Set.range_const, Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    refine valuation_aeval_eq_one W hk h1 ?_
    rintro rfl
    exact hy0 (Subtype.ext (by simp))
  have hadjW : ∀ y : Algebra.adjoin k (Set.range fun _ : PUnit.{u + 1} ↦ a),
      (y : Ω) ∈ W.valuation.integer := fun y ↦ by
    rw [Valuation.mem_integer_iff]
    by_cases hy0 : y = 0
    · rw [hy0, ZeroMemClass.coe_zero, map_zero]
      exact zero_le_one
    · exact (hadj y hy0).le
  apply hW
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy0, hy⟩ := (halg.isAlgebraic x).exists_integral_multiple
  let φ := RingHom.codRestrict (algebraMap (Algebra.adjoin k (Set.range fun _ : PUnit.{u + 1} ↦ a))
    Ω) W.valuation.integer hadjW
  have hint : IsIntegral W.valuation.integer (RingHom.id Ω (y • x)) :=
    hy.map_of_comp_eq φ (RingHom.id Ω) (RingHom.ext fun _ ↦ rfl)
  have hmem := (Valuation.integer.integers W.valuation).mem_of_integral hint
  rw [Valuation.mem_integer_iff, RingHom.id_apply, Algebra.smul_def, map_mul] at hmem
  rw [← W.valuation_le_one_iff]
  have hy1 : W.valuation (algebraMap _ Ω y) = 1 := hadj y hy0
  rwa [hy1, one_mul] at hmem

include hk in
/-- **`D_W = I_W`**: an automorphism `σ` of `Ω` over a subfield `P ⊇ k` with `σ⁻¹(W) = W` acts
trivially on the residue field of `W` (which is `k`), i.e. lies in the inertia group of `W`. -/
theorem mem_inertia_of_comap_eq {P : Type u} [Field P] [Algebra k P] [Algebra P Ω]
    [IsScalarTower k P Ω] (htr : Algebra.trdeg k Ω ≤ 1) (hW : W ≠ ⊤) {σ : Ω ≃ₐ[P] Ω}
    (hσ : W.comap (σ : Ω →+* Ω) = W) : σ ∈ GaloisPi1.inertia (P := P) W := by
  intro a ha
  obtain ⟨c, hc⟩ := exists_valuation_sub_lt_one W hk htr hW ha
  have hσc : σ (algebraMap k Ω c) = algebraMap k Ω c := by
    rw [IsScalarTower.algebraMap_apply k P Ω, AlgEquiv.commutes]
  have h2 : W.valuation (σ (a - algebraMap k Ω c)) < 1 := by
    have := (valuation_comap_lt_one_iff W (σ : Ω →+* Ω) (a - algebraMap k Ω c)).1
      (by rw [hσ]; exact hc)
    simpa using this
  have : σ a - a = σ (a - algebraMap k Ω c) - (a - algebraMap k Ω c) := by
    rw [map_sub, hσc]
    ring
  rw [this]
  exact Valuation.map_sub_lt _ h2 hc

end ResidueField

section Curve

open AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- An extension `Ω` algebraic over `k(t)` has transcendence degree `≤ 1` over `k`. -/
lemma trdeg_le_one_of_isAlgebraic {t : Ω} [Algebra.IsAlgebraic (IntermediateField.adjoin k {t}) Ω] :
    Algebra.trdeg k Ω ≤ 1 := by
  have := IntermediateField.isAlgebraic_adjoin_iff_top.1 ‹_›
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk k ({t} : Set Ω)

end Curve

section Cusp

open AlgebraicGeometry AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : Pi1.Orbifold.GaloisData k t)
  (X : Scheme.{u}) [IsIntegral X] (eL : X.functionField ≃+* D.L)

/-- A place not centred on an open `U` is a proper valuation subring. -/
lemma ne_top_of_not_isCentredOn (U : X.Opens) [Nonempty U] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hW : ¬ IsCentredOn D X eL U W) : W ≠ ⊤ := by
  rintro rfl
  exact hW ⟨hkW, fun _ ↦ trivial⟩

variable [IsAlgClosed k] [IsGalois (K₀ k t) Ω]

/-- **`D_W = I_W` for the cusp places** of `Ω ⊇ K(X)`: an automorphism of `Ω` over `k(t)` fixing a
place `W ⊇ k` not centred on `U` lies in the inertia group of `W`. -/
theorem mem_inertia_of_comap_eq_of_not_isCentredOn (U : X.Opens) [Nonempty U]
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : ¬ IsCentredOn D X eL U W) {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : W.comap (σ : Ω →+* Ω) = W) :
    σ ∈ GaloisPi1.inertia W :=
  mem_inertia_of_comap_eq W hkW (trdeg_le_one_of_isAlgebraic (t := t))
    (ne_top_of_not_isCentredOn D X eL U hkW hW) hσ

end Cusp

end CurvesJacobian.Cusp
