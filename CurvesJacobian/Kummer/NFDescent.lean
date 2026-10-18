/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.NF
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Units of an NF-curve descend to `k̄_NF` up to constants

Let `N : NFModel D` be a descent of `X_{k̄}` to `k̄_NF` ([AbsTopIII] Def. 1.7, `Kummer/NF.lean`):
`F_NF ⊆ F k̄` with `F_NF · k̄ = F k̄`, `F_NF` and `k̄` linearly disjoint over `k̄_NF`, and the cusps
of `U` NF-points. The proof of [AbsTopIII] Prop. 1.8 (T3 l.2099–2106) uses that a rational
function on `X_{k̄}` whose divisor is supported on NF-points (here: a unit of `U`, whose divisor
is supported on the cusps) is an NF-rational function up to a constant of `k̄`. This file proves
it: `CurvesJacobian.Kummer.NFModel.unitsDescend`.

Proof. Fix a nonconstant `y ∈ F_NF` (`NFModel.exists_transcendental`) and write
`K₀ = k̄_NF(y) ⊆ K = k̄(y)`.

* `Ω` is algebraic over `k̄(y)` (`isAlgebraic_adjoin_kbar`), and `K₀`-linearly independent
  families in `F_NF` stay `K`-linearly independent (`NFModel.linearIndependent_adjoin`, from the
  linear disjointness); hence `F_NF` is finite over `K₀` with a basis `b` integral over
  `k̄_NF[y]` (`NFModel.exists_basis`), which is also a `K`-basis of `F k̄`.
* **Trace dual basis.** The trace matrix of `b` over `K` has entries in `K₀`, so the dual basis
  lies in `F_NF`; an element of `F k̄` integral over `k̄[y]` is a `k̄[y]`-combination of the dual
  basis, hence lies in `k̄ · F_NF = Algebra.adjoin k̄ F_NF` (`NFModel.mem_adjoin_of_isIntegral`).
* A unit `w` lies in every valuation subring containing `k̄ ∪ F_NF` (such a place is not a cusp,
  by `NFModel.cusp_nf`); by the valuative criterion of integrality, after multiplying by a
  nonzero `q ∈ k̄_NF[y]` it is integral over `k̄[y]` (`NFModel.exists_isIntegral_mul`), so
  `w ∈ k̄ · F_NF`: `w = ∑ c_b a_b` with `a_b ∈ F_NF` and `c_b ∈ k̄` linearly independent over
  `k̄_NF`.
* **Gauss lemma** (`NFModel.valuation_le_valuation_sum`): at an NF-point,
  `ord (∑ c_b a_b) = min_b ord a_b` (NF-functions are congruent to algebraic numbers there,
  `NFModel.exists_isAlgebraic_valuation_sub_lt_one`). Hence each `a_b / w` has no poles (at
  non-NF places `w` is a unit), so it is a constant `l ∈ k̄ˣ`, and `l · w = a_b ∈ F_NF`.

We also derive `NFModel.trdeg_le_one` (`X_NF` is a curve over `k̄_NF`) from the other data of
the model.
-/

open KummerTheory Curve AffOrbicurve IsLocalRing Polynomial

namespace CurvesJacobian.Kummer

universe u

section Exchange

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω) [IsGalois (K₀ k t) Ω]

include t in
/-- **Exchange**: if `y ∈ Ω` is transcendental over `k̄`, then `Ω` (algebraic over `k(t)`) is
algebraic over `k̄(y)`. -/
theorem isAlgebraic_adjoin_kbar {y : Ω} (hy : Transcendental (kbar k Ω) y) :
    Algebra.IsAlgebraic (IntermediateField.adjoin (kbar k Ω) {y}) Ω := by
  set L := kbar k Ω
  -- `t` is transcendental over `k̄`, otherwise `Ω` (hence `y`) would be algebraic over `k̄`
  have ht : Transcendental L t := by
    intro ht
    haveI : Algebra.IsAlgebraic L (K₀ L t) :=
      IntermediateField.isAlgebraic_adjoin_simple ht.isIntegral
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.trans L (K₀ L t) Ω
    exact hy (Algebra.IsAlgebraic.isAlgebraic y)
  -- `{t}` is a transcendence basis of `Ω / k̄`
  have hbt : IsTranscendenceBasis L (fun _ : PUnit.{u + 1} => t) := by
    refine (algebraicIndependent_unique_type_iff.2 ht).isTranscendenceBasis_iff_isAlgebraic.2 ?_
    rw [Set.range_const]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top).1 inferInstance
  -- hence so is `{y}`, since `trdeg = 1`
  have hby : IsTranscendenceBasis L (fun _ : PUnit.{u + 1} => y) :=
    (algebraicIndependent_unique_type_iff.2 hy).isTranscendenceBasis_of_trdeg_le_of_finite
      hbt.cardinalMk_eq_trdeg.symm.le
  have := hby.isAlgebraic_field
  rwa [Set.range_const] at this


end Exchange

section AdjoinTranscendental

open scoped IntermediateField.algebraAdjoinAdjoin

variable {F₀ L : Type*} [Field F₀] [Field L] [Algebra F₀ L] (F : IntermediateField F₀ L)

/-- The powers of an element transcendental over `F` are `F`-linearly independent. -/
lemma linearIndependent_pow_of_transcendental {y : L} (hy : Transcendental F y) :
    LinearIndependent F (fun n : ℕ => y ^ n) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hp : aeval y (∑ j ∈ s, monomial j (g j)) = 0 := by
    simpa [map_sum, aeval_monomial, Algebra.smul_def, mul_comm] using hg
  have h0 := congrArg (fun p : F[X] => p.coeff i) (transcendental_iff.1 hy _ hp)
  simpa [finsetSum_coeff, coeff_monomial, hi] using h0

/-- If `v` is linearly independent over `F(y)`, `y` transcendental over `F`, then the family
`y ^ n * v i` is linearly independent over `F`. -/
lemma linearIndependent_pow_mul_of_adjoin {y : L} (hy : Transcendental F y) {ι : Type*}
    {v : ι → L} (hli : LinearIndependent (IntermediateField.adjoin F {y}) v) :
    LinearIndependent F (fun p : ℕ × ι => y ^ p.1 * v p.2) := by
  have hA : LinearIndependent (Algebra.adjoin F {y}) v :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin F {y})
      (IntermediateField.adjoin F {y})).2 hli
  have hb : LinearIndependent F (fun n : ℕ =>
      (⟨y ^ n, pow_mem (Algebra.self_mem_adjoin_singleton F y) n⟩ : Algebra.adjoin F {y})) :=
    LinearIndependent.of_comp (Algebra.adjoin F {y}).val.toLinearMap
      (linearIndependent_pow_of_transcendental F hy)
  have h3 := linearIndependent_smul (R := F) hb hA
  convert h3 using 2 with p
  rw [Subalgebra.smul_def, smul_eq_mul]

/-- If the family `y ^ n * v i` is linearly independent over `F`, then the finite family `v` is
linearly independent over `F(y)`. -/
lemma linearIndependent_adjoin_of_pow_mul {y : L} {ι : Type*} [Finite ι] {v : ι → L}
    (he : LinearIndependent F (fun p : ℕ × ι => y ^ p.1 * v p.2)) :
    LinearIndependent (IntermediateField.adjoin F {y}) v := by
  have := Fintype.ofFinite ι
  rw [← LinearIndependent.iff_fractionRing (Algebra.adjoin F {y})
    (IntermediateField.adjoin F {y}), Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∀ i, (g i : L) ∈ (aeval y : F[X] →ₐ[F] L).range := fun i => by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g i).2
  choose p hp using hg'
  replace hp : ∀ i, aeval y (p i) = g i := hp
  obtain ⟨M, hM⟩ : ∃ M, ∀ i, (p i).natDegree < M :=
    ⟨∑ i, ((p i).natDegree + 1), fun i =>
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Finset.single_le_sum (f := fun i => (p i).natDegree + 1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i))⟩
  have key : ∑ q : Fin M × ι, (p q.2).coeff q.1 • (y ^ (q.1 : ℕ) * v q.2) = 0 := by
    rw [Fintype.sum_prod_type_right]
    have : ∀ i, ∑ n : Fin M, (p i).coeff n • (y ^ (n : ℕ) * v i) = g i • v i := by
      intro i
      rw [Subalgebra.smul_def, smul_eq_mul, ← hp i, aeval_eq_sum_range' (hM i), Finset.sum_mul,
        ← Fin.sum_univ_eq_sum_range]
      simp [Algebra.smul_def, mul_assoc]
    simp_rw [this]
    exact hg
  have he' := he.comp (fun q : Fin M × ι => ((q.1 : ℕ), q.2))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (Fin.ext h.1) h.2)
  have hc := Fintype.linearIndependent_iff.1 he' _ key
  have hpi : p i = 0 := by
    refine Polynomial.ext fun n => ?_
    rw [coeff_zero]
    by_cases hn : n < M
    · exact hc (⟨n, hn⟩, i)
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hM i) (not_lt.1 hn))
  exact Subtype.ext (by rw [← hp i, hpi, map_zero]; rfl)

end AdjoinTranscendental

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]

namespace NFModel

variable (N : NFModel D)

/-- **Linear disjointness**: `k̄_NF`-linearly independent families in `F_NF` stay
`k̄`-linearly independent. -/
theorem linearIndependent_kbar {ι : Type*} {v : ι → Ω} (hv : ∀ i, v i ∈ N.FNF)
    (hli : LinearIndependent (algebraicClosure ℚ Ω) v) : LinearIndependent (kbar k Ω) v := by
  set A := N.FNF.toIntermediateField (K := algebraicClosure ℚ Ω) fun x =>
    N.algebraic_mem _ (mem_algebraicClosure_iff.1 x.2)
  let a : ι → A := fun i => ⟨v i, hv i⟩
  have ha : LinearIndependent (algebraicClosure ℚ Ω) a :=
    LinearIndependent.of_comp A.val.toLinearMap hli
  have H : LinearIndependent (kbarNF k Ω) v := N.linearDisjoint.linearIndependent_left ha
  rw [linearIndependent_iff'] at H ⊢
  intro s g hg i hi
  have := H s (fun j => ⟨(g j : Ω), (g j).2⟩) (by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl) i hi
  exact Subtype.ext (congrArg Subtype.val this)


/-- There is a nonconstant NF-rational function `y ∈ F_NF` (transcendental over `k̄`). -/
theorem exists_transcendental : ∃ y ∈ N.FNF, Transcendental (kbar k Ω) y := by
  by_contra h
  push Not at h
  have hsub : ((N.FNF : Set Ω) ∪ kbar k Ω) ⊆ (kbar k Ω).toSubfield := by
    rintro x (hx | hx)
    · exact mem_algebraicClosure_iff.2
        ((not_not.1 (h x hx)).restrictScalars k)
    · exact hx
  have htF : t ∈ F (baseChange D) :=
    (F (baseChange D)).algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self _ t⟩
  have htk : t ∈ kbar k Ω := (Subfield.closure_le.2 hsub) (N.mem_closure t htF)
  exact transcendental_kbar D (isAlgebraic_algebraMap (⟨t, htk⟩ : kbar k Ω))

/-- `k̄_NF(y)`-linearly independent families in `F_NF` stay `k̄(y)`-linearly independent. -/
theorem linearIndependent_adjoin {y : Ω} (hy : y ∈ N.FNF) (hyt : Transcendental (kbar k Ω) y)
    {ι : Type*} [Finite ι] {v : ι → Ω} (hv : ∀ i, v i ∈ N.FNF)
    (hli : LinearIndependent (IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}) v) :
    LinearIndependent (IntermediateField.adjoin (kbar k Ω) {y}) v := by
  have := Fintype.ofFinite ι
  have hQ : Transcendental (algebraicClosure ℚ Ω) y := fun h => hyt <| by
    have hy' : y ∈ kbar k Ω :=
      mem_kbar_of_isAlgebraic (@IsAlgebraic.restrictScalars ℚ (algebraicClosure ℚ Ω) Ω
        _ _ _ _ _ _ _ _ (algebraicClosure.isAlgebraic ℚ Ω) y h)
    exact isAlgebraic_algebraMap (R := kbar k Ω) (⟨y, hy'⟩ : kbar k Ω)
  refine linearIndependent_adjoin_of_pow_mul _ (N.linearIndependent_kbar
    (fun q => mul_mem (pow_mem hy _) (hv _)) ?_)
  exact linearIndependent_pow_mul_of_adjoin _ hQ hli

/-- `F_NF` lies in a finite-dimensional extension of `k̄(y)` inside `Ω`. -/
theorem exists_finiteDimensional_le {y : Ω} (hyt : Transcendental (kbar k Ω) y) :
    ∃ E : IntermediateField (IntermediateField.adjoin (kbar k Ω) {y}) Ω,
      FiniteDimensional (IntermediateField.adjoin (kbar k Ω) {y}) E ∧
        ∀ x ∈ N.FNF, x ∈ E := by
  classical
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin (kbar k Ω) {y}) Ω :=
    isAlgebraic_adjoin_kbar t hyt
  haveI : FiniteDimensional (K₀ (kbar k Ω) t) (F (baseChange D)) := by
    have e : (IntermediateField.fixedField (baseChange D).H).fixingSubgroup = (baseChange D).H :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨_, (baseChange D).isClosed_H⟩
    exact (InfiniteGalois.isOpen_iff_finite _).1 (by rw [e]; exact (baseChange D).isOpen_H)
  haveI : Module.Free (K₀ (kbar k Ω) t) (F (baseChange D)) := Module.Free.of_divisionRing _ _
  let B := Module.finBasis (K₀ (kbar k Ω) t) (F (baseChange D))
  refine ⟨IntermediateField.adjoin _ (insert t (Set.range fun i => (B i : Ω))),
    IntermediateField.finiteDimensional_adjoin
      fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, fun x hx => ?_⟩
  set S : Set Ω := insert t (Set.range fun i => (B i : Ω)) with hS
  set E := IntermediateField.adjoin (IntermediateField.adjoin (kbar k Ω) {y}) S
  have htE : t ∈ E := IntermediateField.subset_adjoin _ S (Set.mem_insert t _)
  have hK₀E : K₀ (kbar k Ω) t ≤ E.restrictScalars (kbar k Ω) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact (IntermediateField.mem_restrictScalars _).2 htE
  have h2 := congrArg (IntermediateField.val _) (B.sum_repr ⟨x, N.mem_F x hx⟩)
  rw [map_sum] at h2
  change ∑ i, ((B.repr ⟨x, _⟩ i : Ω) * (B i : Ω)) = x at h2
  rw [← h2]
  exact sum_mem fun i _ => mul_mem (hK₀E (B.repr _ i).2)
    (IntermediateField.subset_adjoin _ S (Set.mem_insert_of_mem _ ⟨i, rfl⟩))

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- **`F_NF` is finite over `k̄_NF(y)`**, with a basis integral over `k̄_NF[y]`. -/
theorem exists_basis {y : Ω} (hy : y ∈ N.FNF) (hyt : Transcendental (kbar k Ω) y) :
    ∃ (n : ℕ) (b : Fin n → Ω), (∀ i, b i ∈ N.FNF) ∧
      LinearIndependent (IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}) b ∧
      (∀ z ∈ N.FNF,
        z ∈ Submodule.span (IntermediateField.adjoin (algebraicClosure ℚ Ω) {y})
          (Set.range b)) ∧
      ∀ i, IsIntegral (Algebra.adjoin (algebraicClosure ℚ Ω) {y}) (b i) := by
  classical
  set K0 := IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}
  set A0 := Algebra.adjoin (algebraicClosure ℚ Ω) {y}
  obtain ⟨E, hEfin, hE⟩ := N.exists_finiteDimensional_le hyt
  let L0 : IntermediateField (algebraicClosure ℚ Ω) Ω := N.FNF.toIntermediateField fun x =>
    N.algebraic_mem _ (mem_algebraicClosure_iff.1 x.2)
  have hK0L0 : K0 ≤ L0 := IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hy)
  let F0 : IntermediateField K0 Ω := IntermediateField.extendScalars hK0L0
  have hF0 : ∀ x : F0, (x : Ω) ∈ N.FNF := fun x => x.2
  have hbound : ∀ s : Finset F0, LinearIndependent K0 (fun i : s => (i : F0)) →
      s.card ≤ Module.finrank (IntermediateField.adjoin (kbar k Ω) {y}) E := by
    intro s hs
    have h1 : LinearIndependent K0 (fun i : s => ((i : F0) : Ω)) :=
      hs.map' (F0.val.toLinearMap) (LinearMap.ker_eq_bot_of_injective F0.val.injective)
    have h2 := N.linearIndependent_adjoin (ι := s) (v := fun i : s => ((i : F0) : Ω)) hy hyt
      (fun i => hF0 i) h1
    let v : s → E := fun i => ⟨((i : F0) : Ω), hE _ (hF0 i)⟩
    have h3 : LinearIndependent (IntermediateField.adjoin (kbar k Ω) {y}) v :=
      LinearIndependent.of_comp (v := v) E.val.toLinearMap h2
    have := h3.fintype_card_le_finrank
    rwa [Fintype.card_coe] at this
  haveI : Module.Free K0 F0 := Module.Free.of_divisionRing _ _
  haveI : FiniteDimensional K0 F0 := Module.rank_lt_aleph0_iff.1
    (lt_of_le_of_lt (rank_le hbound) (Cardinal.natCast_lt_aleph0))
  let b0 := Module.finBasis K0 F0
  have hint : ∀ i, ∃ a : A0, a ≠ 0 ∧ IsIntegral A0 (a • (b0 i : Ω)) := by
    intro i
    have h1 : IsAlgebraic K0 ((b0 i : F0) : Ω) :=
      ((IsIntegral.of_finite K0 (b0 i)).map F0.val).isAlgebraic
    exact ((IsFractionRing.isAlgebraic_iff A0 K0 Ω).2 h1).exists_integral_multiple
  choose a ha0 ha using hint
  have hw : ∀ i, algebraMap A0 K0 (a i) ≠ 0 := fun i h =>
    ha0 i (FaithfulSMul.algebraMap_injective A0 K0 (h.trans (map_zero _).symm))
  let w : Fin (Module.finrank K0 F0) → K0ˣ := fun i => Units.mk0 _ (hw i)
  have hb : ∀ i, a i • (b0 i : Ω) = w i • (b0 i : Ω) := fun i => by
    rw [Units.smul_def, Units.val_mk0, algebraMap_smul]
  have hli : LinearIndependent K0 (fun i => ((b0 i : F0) : Ω)) :=
    b0.linearIndependent.map' F0.val.toLinearMap
      (LinearMap.ker_eq_bot_of_injective F0.val.injective)
  refine ⟨Module.finrank K0 F0, fun i => a i • (b0 i : Ω), fun i => ?_, ?_,
    fun z hz => ?_, ha⟩
  · change a i • (b0 i : Ω) ∈ N.FNF
    rw [Subalgebra.smul_def, smul_eq_mul]
    refine N.FNF.mul_mem ?_ (hF0 _)
    have : A0 ≤ L0.toSubalgebra := Algebra.adjoin_le (Set.singleton_subset_iff.2 hy)
    exact this (a i).2
  · rw [show (fun i => a i • (b0 i : Ω)) = w • fun i => (b0 i : Ω) from funext hb]
    exact hli.units_smul w
  · have hsp : ∀ i, ((b0 i : F0) : Ω) ∈
        Submodule.span K0 (Set.range fun i => a i • (b0 i : Ω)) := fun i => by
      have : ((b0 i : F0) : Ω) = (w i)⁻¹ • (a i • (b0 i : Ω)) := by
        rw [hb, inv_smul_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h2 := congrArg (F0.val.toLinearMap) (b0.sum_repr ⟨z, hz⟩)
    rw [map_sum] at h2
    change ∑ i, F0.val.toLinearMap (b0.repr ⟨z, hz⟩ i • b0 i) = z at h2
    simp_rw [map_smul] at h2
    rw [← h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsp i)

/-- `k̄_NF ⊆ k̄`. -/
theorem mem_kbar_of_mem_algebraicClosure {z : Ω} (hz : z ∈ algebraicClosure ℚ Ω) :
    z ∈ kbar k Ω :=
  mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 hz).tower_top k)

/-- `k̄_NF(y) ⊆ k̄(y)`. -/
theorem mem_adjoin_kbar_of_mem_adjoin {y z : Ω}
    (hz : z ∈ IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}) :
    z ∈ IntermediateField.adjoin (kbar k Ω) {y} := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hz ⊢
  refine Subfield.closure_mono (Set.union_subset_union_left _ ?_) hz
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨c, mem_kbar_of_mem_algebraicClosure (k := k) c.2⟩, rfl⟩

/-- `k̄_NF[y] ⊆ k̄[y]`. -/
theorem mem_algebraAdjoin_kbar_of_mem {y z : Ω}
    (hz : z ∈ Algebra.adjoin (algebraicClosure ℚ Ω) {y}) :
    z ∈ Algebra.adjoin (kbar k Ω) {y} := by
  rw [← Subalgebra.mem_toSubring, Algebra.adjoin_eq_ring_closure] at hz ⊢
  refine Subring.closure_mono (Set.union_subset_union_left _ ?_) hz
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨c, mem_kbar_of_mem_algebraicClosure (k := k) c.2⟩, rfl⟩

/-- Integrality over `k̄_NF[y]` implies integrality over `k̄[y]`. -/
theorem isIntegral_algebraAdjoin_kbar {y z : Ω}
    (hz : IsIntegral (Algebra.adjoin (algebraicClosure ℚ Ω) {y}) z) :
    IsIntegral (Algebra.adjoin (kbar k Ω) {y}) z := by
  let φ : Algebra.adjoin (algebraicClosure ℚ Ω) {y} →+* Algebra.adjoin (kbar k Ω) {y} :=
    { toFun := fun a => ⟨a, mem_algebraAdjoin_kbar_of_mem (k := k) a.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  exact IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (RingHom.ext fun _ => rfl) hz

omit [CharZero Ω] in
/-- `k̄[y]` is integrally closed for transcendental `y`. -/
theorem isIntegrallyClosed_algebraAdjoin {F : Type*} [Field F] [Algebra F Ω] {y : Ω}
    (hy : Transcendental F y) : IsIntegrallyClosed (Algebra.adjoin F {y}) :=
  IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental F y hy).toRingEquiv

/-- Coordinates of the trace dual basis lie in any subfield containing the structure constants. -/
theorem repr_dualBasis_mem {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (bL : Module.Basis ι K L) (S : Subfield K)
    (hS : ∀ i j l m, bL.repr (bL i * bL j * bL l) m ∈ S) (i j : ι) :
    bL.repr ((Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) bL i) j ∈ S := by
  have := Fintype.ofFinite ι
  set d := (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) bL with hd
  set G : Matrix ι ι K := fun i j => Algebra.trace K L (bL i * bL j) with hGdef
  set μ : Matrix ι ι K := fun i j => bL.repr (d i) j with hμdef
  have hG : ∀ i j, G i j ∈ S := by
    intro i j
    simp only [G, Algebra.trace_eq_matrix_trace bL, Matrix.trace, Matrix.diag,
      Algebra.leftMulMatrix_eq_repr_mul]
    exact sum_mem fun l _ => hS i j l l
  have hμG : μ * G = 1 := by
    ext i l
    have h1 := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate K L) bL i l
    rw [← hd, Algebra.traceForm_apply] at h1
    conv_lhs at h1 => rw [← bL.sum_repr (d i)]
    rw [Finset.sum_mul, map_sum] at h1
    simp only [smul_mul_assoc, map_smul, smul_eq_mul] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [eq_comm (a := l)] using h1
  let G' : Matrix ι ι S := fun i j => ⟨G i j, hG i j⟩
  have hGG' : G'.map S.subtype = G := rfl
  have hdet : G.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hμG
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet' : IsUnit G'.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => hdet ?_
    rw [← hGG', ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hν : G'⁻¹.map S.subtype * G = 1 := by
    rw [← hGG', ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet', Matrix.map_one _ (map_zero _)
      (map_one _)]
  have : μ = G'⁻¹.map S.subtype := by
    rw [← Matrix.inv_eq_left_inv hμG, Matrix.inv_eq_left_inv hν]
  have hμ : μ i j = S.subtype (G'⁻¹ i j) := by rw [this]; rfl
  change μ i j ∈ S
  rw [hμ]
  exact (G'⁻¹ i j).2

/-- `k̄_NF(y) ⊆ F_NF`. -/
theorem mem_FNF_of_mem_adjoin {y z : Ω} (hy : y ∈ N.FNF)
    (hz : z ∈ IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}) : z ∈ N.FNF := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hz
  refine (Subfield.closure_le.2 (Set.union_subset ?_ ?_)) hz
  · rintro _ ⟨c, rfl⟩
    exact N.algebraic_mem _ (mem_algebraicClosure_iff.1 c.2)
  · exact Set.singleton_subset_iff.2 hy

/-- An intermediate field `L` of `Ω / k̄(y)` containing `x`, with a `k̄(y)`-basis of
`k̄_NF[y]`-integral NF-functions, in which NF-functions have coordinates in `k̄_NF(y)`. -/
theorem exists_basis_adjoin_kbar {y : Ω} (hy : y ∈ N.FNF) (hyt : Transcendental (kbar k Ω) y)
    {x : Ω} (hx : x ∈ F (baseChange D)) :
    ∃ (L : IntermediateField (IntermediateField.adjoin (kbar k Ω) {y}) Ω) (n : ℕ)
      (bL : Module.Basis (Fin n) (IntermediateField.adjoin (kbar k Ω) {y}) L),
      x ∈ L ∧ (∀ i, (bL i : Ω) ∈ N.FNF) ∧
      (∀ i, IsIntegral (Algebra.adjoin (algebraicClosure ℚ Ω) {y}) (bL i : Ω)) ∧
      ∀ u : L, (u : Ω) ∈ N.FNF → ∀ m,
        ((bL.repr u m : IntermediateField.adjoin (kbar k Ω) {y}) : Ω) ∈
          IntermediateField.adjoin (algebraicClosure ℚ Ω) {y} := by
  classical
  obtain ⟨n, b, hbF, hbli, hbspan, hbint⟩ := N.exists_basis hy hyt
  -- every element of `F_NF` is a `k̄_NF(y)`-combination of `b`
  have hcomb : ∀ z ∈ N.FNF, ∃ c : Fin n → Ω,
      (∀ i, c i ∈ IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}) ∧
        z = ∑ i, c i * b i := by
    intro z hz
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hbspan z hz)
    exact ⟨fun i => c i, fun i => (c i).2, by rw [← hc]; simp [Algebra.smul_def]⟩
  haveI := isAlgebraic_adjoin_kbar t hyt
  set K := IntermediateField.adjoin (kbar k Ω) {y} with hKdef
  set P : Submodule K Ω := Submodule.span K (Set.range b) with hPdef
  have hFP : ∀ z ∈ N.FNF, z ∈ P := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := hcomb z hz
    refine sum_mem fun i _ => ?_
    have : c i * b i = (⟨c i, mem_adjoin_kbar_of_mem_adjoin (hc i)⟩ : K) • b i := by
      simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hPmul : ∀ u v, u ∈ P → v ∈ P → u * v ∈ P := by
    intro u v hu hv
    have := Submodule.mul_mem_mul hu hv
    rw [hPdef, Submodule.span_mul_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact hFP _ (mul_mem (hbF i) (hbF j))
  set L := IntermediateField.adjoin K (Set.range b) with hLdef
  have hLP : ∀ z ∈ L, z ∈ P := by
    intro z hz
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _)] at hz
    exact (Algebra.adjoin_le (S := P.toSubalgebra (hFP 1 (one_mem _)) hPmul)
      Submodule.subset_span) hz
  have hPL : ∀ z ∈ P, z ∈ L := fun z hz =>
    (Submodule.span_le (p := Subalgebra.toSubmodule L.toSubalgebra)).2
      (by rintro _ ⟨i, rfl⟩; exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩) hz
  -- the basis of `L` over `K`
  let bv : Fin n → L := fun i => ⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  have hli : LinearIndependent K bv :=
    LinearIndependent.of_comp (L.val : L →ₐ[K] Ω).toLinearMap
      (N.linearIndependent_adjoin hy hyt hbF hbli)
  have hsp : ⊤ ≤ Submodule.span K (Set.range bv) := by
    rintro z -
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hLP z z.2)
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, Subtype.ext ?_⟩
    rw [← hc, IntermediateField.coe_sum]
    rfl
  let bL := Module.Basis.mk hli hsp
  have hbL : ∀ i, (bL i : Ω) = b i := fun i => by simp [bL, bv]
  refine ⟨L, n, bL, ?_, fun i => hbL i ▸ hbF i, fun i => hbL i ▸ hbint i, ?_⟩
  · refine (Subfield.closure_le (t := L.toSubfield)).2 (Set.union_subset ?_ ?_)
      (N.mem_closure x hx)
    · exact fun z hz => hPL z (hFP z hz)
    · intro c hc
      exact L.algebraMap_mem (⟨c, IntermediateField.algebraMap_mem K ⟨c, hc⟩⟩ : K)
  · intro u hu m
    obtain ⟨c, hc, hcu⟩ := hcomb u hu
    let c' : Fin n → K := fun i => ⟨c i, mem_adjoin_kbar_of_mem_adjoin (hc i)⟩
    have : u = ∑ i, c' i • bL i := by
      apply Subtype.ext
      rw [hcu, IntermediateField.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.coe_smul, hbL, Algebra.smul_def]
      rfl
    rw [this, bL.repr_sum_self]
    exact hc m

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The trace dual basis argument: an element of `L` integral over `k̄[y]` lies in
`k̄[F_NF]`, given a basis as in `exists_basis_adjoin_kbar`. -/
theorem mem_adjoin_of_basis {y : Ω} (hy : y ∈ N.FNF) (hyt : Transcendental (kbar k Ω) y)
    (L : IntermediateField (IntermediateField.adjoin (kbar k Ω) {y}) Ω) {n : ℕ}
    (bL : Module.Basis (Fin n) (IntermediateField.adjoin (kbar k Ω) {y}) L)
    (hbF : ∀ i, (bL i : Ω) ∈ N.FNF)
    (hbint : ∀ i, IsIntegral (Algebra.adjoin (algebraicClosure ℚ Ω) {y}) (bL i : Ω))
    (hcoord : ∀ u : L, (u : Ω) ∈ N.FNF → ∀ m,
      ((bL.repr u m : IntermediateField.adjoin (kbar k Ω) {y}) : Ω) ∈
        IntermediateField.adjoin (algebraicClosure ℚ Ω) {y})
    {x : Ω} (hxL : x ∈ L) (hint : IsIntegral (Algebra.adjoin (kbar k Ω) {y}) x) :
    x ∈ Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω) := by
  classical
  haveI : FiniteDimensional (IntermediateField.adjoin (kbar k Ω) {y}) L :=
    Module.Finite.of_basis bL
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin (kbar k Ω) {y}) L :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (IntermediateField.adjoin (kbar k Ω) {y}) L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsIntegrallyClosed (Algebra.adjoin (kbar k Ω) {y}) :=
    isIntegrallyClosed_algebraAdjoin hyt
  haveI : IsScalarTower (Algebra.adjoin (kbar k Ω) {y})
      (IntermediateField.adjoin (kbar k Ω) {y}) L :=
    IntermediateField.isScalarTower (R := Algebra.adjoin (kbar k Ω) {y}) L
  let f : L →ₐ[Algebra.adjoin (kbar k Ω) {y}] Ω := (L.val).restrictScalars _
  have hf : Function.Injective f := fun _ _ h => Subtype.ext h
  have hbint' : ∀ i, IsIntegral (Algebra.adjoin (kbar k Ω) {y}) (bL i) := fun i =>
    (isIntegral_algHom_iff f hf).1 (isIntegral_algebraAdjoin_kbar (hbint i))
  have hxint : IsIntegral (Algebra.adjoin (kbar k Ω) {y}) (⟨x, hxL⟩ : L) :=
    (isIntegral_algHom_iff f hf).1 hint
  have hmem := integralClosure_le_span_dualBasis bL hbint'
    (show (⟨x, hxL⟩ : L) ∈ Subalgebra.toSubmodule (integralClosure _ L) from hxint)
  let S : Subfield (IntermediateField.adjoin (kbar k Ω) {y}) :=
    (IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}).toSubfield.comap
      (algebraMap (IntermediateField.adjoin (kbar k Ω) {y}) Ω)
  have hS : ∀ i j l m, bL.repr (bL i * bL j * bL l) m ∈ S := by
    intro i j l m
    refine hcoord _ ?_ m
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul]
    exact mul_mem (mul_mem (hbF i) (hbF j)) (hbF l)
  have hrepr := repr_dualBasis_mem bL S hS
  generalize (Algebra.traceForm _ L).dualBasis (traceForm_nondegenerate _ L) bL = d at hmem hrepr
  have hd : ∀ i, ((d i : L) : Ω) ∈ N.FNF := by
    intro i
    rw [← bL.sum_repr (d i), IntermediateField.coe_sum]
    refine sum_mem fun j _ => ?_
    rw [IntermediateField.coe_smul, Algebra.smul_def]
    exact mul_mem (N.mem_FNF_of_mem_adjoin hy (hrepr i j)) (hbF j)
  have key : ∀ z ∈ Submodule.span (Algebra.adjoin (kbar k Ω) {y}) (Set.range d),
      (z : Ω) ∈ Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Algebra.subset_adjoin (hd i)
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul a u _ hu =>
      rw [IntermediateField.coe_smul, Algebra.smul_def]
      exact mul_mem (Algebra.adjoin_mono (Set.singleton_subset_iff.2 hy) a.2) hu
  exact key _ hmem

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- `X_NF` is a curve over `k̄_NF`: `F_NF` has transcendence degree `≤ 1` over `ℚ`. -/
theorem trdeg_le_one : Algebra.trdeg ℚ N.FNF ≤ 1 := by
  classical
  obtain ⟨y, hy, hyt⟩ := N.exists_transcendental
  obtain ⟨n, b, -, -, hspan, -⟩ := N.exists_basis hy hyt
  set K0 := IntermediateField.adjoin (algebraicClosure ℚ Ω) {y}
  set M := IntermediateField.adjoin ℚ ({y} : Set Ω)
  set L := IntermediateField.adjoin M (algebraicClosure ℚ Ω : Set Ω)
  -- every element of `F_NF` is integral over `K0 = k̄_NF(y)`, as `F_NF` is finite over `K0`
  have h1 : ∀ z ∈ N.FNF, IsIntegral K0 z := by
    let L0 : IntermediateField (algebraicClosure ℚ Ω) Ω := N.FNF.toIntermediateField fun x =>
      N.algebraic_mem _ (mem_algebraicClosure_iff.1 x.2)
    have hK0L0 : K0 ≤ L0 := IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hy)
    let F0 : IntermediateField K0 Ω := IntermediateField.extendScalars hK0L0
    haveI : IsNoetherian K0 (Submodule.span K0 (Set.range b)) :=
      isNoetherian_span_of_finite K0 (Set.finite_range b)
    haveI : IsNoetherian K0 (Subalgebra.toSubmodule F0.toSubalgebra) :=
      isNoetherian_of_le (s := Subalgebra.toSubmodule F0.toSubalgebra) fun x hx => hspan x hx
    intro z hz
    exact isIntegral_of_submodule_noetherian F0.toSubalgebra this z hz
  -- `L = ℚ(y)(k̄_NF)` is algebraic over `M = ℚ(y)` and contains `K0`
  haveI : Algebra.IsAlgebraic M L := IntermediateField.isAlgebraic_adjoin fun x hx =>
    (@IsAlgebraic.isIntegral ℚ Ω _ _ _ _ (mem_algebraicClosure_iff.1 hx)).tower_top
  have hK0L : K0.toSubfield ≤ L.toSubfield := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      exact IntermediateField.subset_adjoin M _ x.2
    · rw [Set.singleton_subset_iff]
      exact L.algebraMap_mem ⟨y, IntermediateField.mem_adjoin_simple_self ℚ y⟩
  -- hence every element of `F_NF` is algebraic over `ℚ[y]`
  have h2 : ∀ z ∈ N.FNF, IsAlgebraic (Algebra.adjoin ℚ ({y} : Set Ω)) z := by
    intro z hz
    obtain ⟨p, hpm, hp⟩ := h1 z hz
    let f : K0 →+* L := (algebraMap K0 Ω).codRestrict L fun x => hK0L x.2
    have hL : IsIntegral L z := ⟨p.map f, hpm.map f, by rw [eval₂_map]; exact hp⟩
    exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin ℚ ({y} : Set Ω)) M Ω).2
      (isIntegral_trans (R := M) z hL).isAlgebraic
  -- transport to the field `F_NF`
  let φ : N.FNF →ₐ[ℚ] Ω := N.FNF.subtype.toRatAlgHom
  have hφ : Function.Injective φ := Subtype.val_injective
  set S := Algebra.adjoin ℚ ({⟨y, hy⟩} : Set N.FNF)
  have hS : S.map φ = Algebra.adjoin ℚ ({y} : Set Ω) := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    rfl
  haveI : Algebra.IsAlgebraic S N.FNF := ⟨fun z => by
    have h3 : IsAlgebraic (S.map φ) (φ z) := hS ▸ h2 z z.2
    exact h3.of_ringHom_of_comp_eq (S.equivMapOfInjective φ hφ) φ (EquivLike.surjective _) hφ
      rfl⟩
  haveI := IntermediateField.isAlgebraic_adjoin_iff_top.2 this
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({⟨y, hy⟩} : Set N.FNF)

/-- **Elements of `F k̄` integral over `k̄[y]` lie in `k̄ · F_NF`** (trace dual basis of an
NF-basis). -/
theorem mem_adjoin_of_isIntegral {y : Ω} (hy : y ∈ N.FNF) (hyt : Transcendental (kbar k Ω) y)
    {x : Ω} (hx : x ∈ F (baseChange D))
    (hint : IsIntegral (Algebra.adjoin (kbar k Ω) {y}) x) :
    x ∈ Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω) := by
  obtain ⟨L, n, bL, hxL, hbF, hbint, hcoord⟩ := N.exists_basis_adjoin_kbar hy hyt hx
  exact N.mem_adjoin_of_basis hy hyt L bL hbF hbint hcoord hxL hint

/-- An element of a field integral over a ring mapping into a valuation subring `W` lies in `W`
(valuation subrings are integrally closed). -/
theorem mem_valuationSubring_of_isIntegral {K R : Type*} [Field K] [CommRing R] [Algebra R K]
    {W : ValuationSubring K} (hR : ∀ r : R, algebraMap R K r ∈ W) {x : K}
    (hx : IsIntegral R x) : x ∈ W := by
  obtain ⟨p, hpm, hp⟩ := hx
  let f : R →+* W := (algebraMap R K).codRestrict W.toSubring hR
  have hint : IsIntegral W x := ⟨p.map f, hpm.map f, by rw [eval₂_map]; exact hp⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hz]
  exact z.2

/-- **Clearing denominators.** If every element of the subring `S` becomes an element of the
subalgebra `A` after multiplication by a nonzero element of `T ≤ A`, then for `w` integral over
`S` some nonzero `q ∈ T` makes `q * w` integral over `A`. -/
theorem exists_isIntegral_mul_of_isIntegral {K R : Type*} [Field K] [CommRing R] [Algebra R K]
    (A : Subalgebra R K) (T S : Subring K) (hTA : T ≤ A.toSubring)
    (hS : ∀ z ∈ S, ∃ q ∈ T, q ≠ 0 ∧ q * z ∈ A) {w : K} (hw : IsIntegral S w) :
    ∃ q ∈ T, q ≠ 0 ∧ IsIntegral A (q * w) := by
  obtain ⟨p, hpm, hp⟩ := hw
  have key : ∀ m : ℕ, ∃ q ∈ T, q ≠ 0 ∧
      ∀ i < m, q * algebraMap S K (p.coeff i) ∈ A := by
    intro m
    induction m with
    | zero => exact ⟨1, T.one_mem, one_ne_zero, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨q, hqT, hq0, hq⟩ := ih
      obtain ⟨q', hq'T, hq'0, hq'⟩ := hS _ (p.coeff m).2
      refine ⟨q' * q, T.mul_mem hq'T hqT, mul_ne_zero hq'0 hq0, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [mul_assoc]; exact A.mul_mem (hTA hq'T) (hq i hi)
      · rw [mul_comm q', mul_assoc]; exact A.mul_mem (hTA hqT) hq'
  obtain ⟨q, hqT, hq0, hq⟩ := key p.natDegree
  refine ⟨q, hqT, hq0, ?_⟩
  set P := (p.map (algebraMap S K)).scaleRoots q with hP
  have hPm : P.Monic := (monic_scaleRoots_iff q).2 (hpm.map _)
  have hPl : P ∈ lifts (algebraMap A K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [hP, coeff_scaleRoots, hpm.natDegree_map, coeff_map]
    suffices h : algebraMap S K (p.coeff i) * q ^ (p.natDegree - i) ∈ A from ⟨⟨_, h⟩, rfl⟩
    rcases lt_trichotomy i p.natDegree with h | rfl | h
    · obtain ⟨j, hj⟩ : ∃ j, p.natDegree - i = j + 1 := ⟨p.natDegree - i - 1, by omega⟩
      have : algebraMap S K (p.coeff i) * q ^ (j + 1) =
          q ^ j * (q * algebraMap S K (p.coeff i)) := by ring
      rw [hj, this]
      exact A.mul_mem (A.pow_mem (hTA hqT) j) (hq i h)
    · simp [hpm.coeff_natDegree, A.one_mem]
    · rw [coeff_eq_zero_of_natDegree_lt h]; simp [A.zero_mem]
  obtain ⟨P', hP'map, -, hP'm⟩ := lifts_and_natDegree_eq_and_monic hPl hPm
  refine ⟨P', hP'm, ?_⟩
  rw [← eval_map, hP'map, hP, scaleRoots_eval_mul, eval_map, hp, mul_zero]

/-- `k̄_NF[y] ⊆ k̄[y]`. -/
theorem adjoin_algebraicClosure_le_adjoin_kbar (y : Ω) :
    (Algebra.adjoin (algebraicClosure ℚ Ω) {y}).toSubring ≤
      (Algebra.adjoin (kbar k Ω) {y}).toSubring := by
  rw [Algebra.adjoin_eq_ring_closure, Algebra.adjoin_eq_ring_closure]
  refine Subring.closure_mono (Set.union_subset_union ?_ le_rfl)
  rintro _ ⟨r, rfl⟩
  exact ⟨⟨r, mem_kbar_of_isAlgebraic (k := k) (mem_algebraicClosure_iff.1 r.2)⟩, rfl⟩

/-- Elements of the ring generated by `k̄` and `k̄_NF(y)` acquire a nonzero denominator in
`k̄_NF[y]` relative to `k̄[y]`. -/
theorem exists_mul_mem_adjoin_of_mem_closure {y z : Ω}
    (hz : z ∈ Subring.closure ((kbar k Ω : Set Ω) ∪
      (IntermediateField.adjoin (algebraicClosure ℚ Ω) {y} : Set Ω))) :
    ∃ q ∈ (Algebra.adjoin (algebraicClosure ℚ Ω) {y}).toSubring, q ≠ 0 ∧
      q * z ∈ Algebra.adjoin (kbar k Ω) {y} := by
  have hle := adjoin_algebraicClosure_le_adjoin_kbar (k := k) y
  have one_mem := (Algebra.adjoin (algebraicClosure ℚ Ω) {y}).toSubring.one_mem
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · refine ⟨1, one_mem, one_ne_zero, ?_⟩
      rw [one_mul]
      exact Subalgebra.algebraMap_mem _ (⟨x, hx⟩ : kbar k Ω)
    · obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hx
      by_cases hs0 : s = 0
      · refine ⟨1, one_mem, one_ne_zero, ?_⟩
        simp [hs0]
      · refine ⟨s, hs, hs0, ?_⟩
        rw [mul_div_cancel₀ _ hs0]
        exact hle hr
  | zero => exact ⟨1, one_mem, one_ne_zero, by simp⟩
  | one => exact ⟨1, one_mem, one_ne_zero, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨q₁, hq₁, hq₁0, ha⟩ := ha
    obtain ⟨q₂, hq₂, hq₂0, hb⟩ := hb
    refine ⟨q₁ * q₂, Subring.mul_mem _ hq₁ hq₂, mul_ne_zero hq₁0 hq₂0, ?_⟩
    have : q₁ * q₂ * (a + b) = q₂ * (q₁ * a) + q₁ * (q₂ * b) := by ring
    rw [this]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hle hq₂) ha)
      (Subalgebra.mul_mem _ (hle hq₁) hb)
  | neg a _ ha =>
    obtain ⟨q, hq, hq0, ha⟩ := ha
    exact ⟨q, hq, hq0, by rw [mul_neg]; exact Subalgebra.neg_mem _ ha⟩
  | mul a b _ _ ha hb =>
    obtain ⟨q₁, hq₁, hq₁0, ha⟩ := ha
    obtain ⟨q₂, hq₂, hq₂0, hb⟩ := hb
    refine ⟨q₁ * q₂, Subring.mul_mem _ hq₁ hq₂, mul_ne_zero hq₁0 hq₂0, ?_⟩
    have : q₁ * q₂ * (a * b) = (q₁ * a) * (q₂ * b) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ ha hb

/-- `k̄_NF[y] ⊆ F_NF` for `y ∈ F_NF`. -/
theorem adjoin_algebraicClosure_le_FNF {y : Ω} (hy : y ∈ N.FNF) :
    (Algebra.adjoin (algebraicClosure ℚ Ω) {y}).toSubring ≤ N.FNF.toSubring := by
  rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
  refine Set.union_subset ?_ (Set.singleton_subset_iff.2 hy)
  rintro _ ⟨r, rfl⟩
  exact N.algebraic_mem _ (mem_algebraicClosure_iff.1 r.2)

/-- A unit of `U` times a suitable nonzero NF-function is integral over `k̄[y]` (valuative
criterion of integrality and clearing denominators). -/
theorem exists_isIntegral_mul {y : Ω} (hy : y ∈ N.FNF) (hyt : Transcendental (kbar k Ω) y)
    (w : units D) : ∃ q ∈ N.FNF, q ≠ 0 ∧
      IsIntegral (Algebra.adjoin (kbar k Ω) {y})
        (q * algebraMap (F D) Ω ((w : (F D)ˣ) : F D)) := by
  obtain ⟨n, b, -, -, hspan, hbint⟩ := N.exists_basis hy hyt
  set s : Set Ω := (kbar k Ω : Set Ω) ∪
    (IntermediateField.adjoin (algebraicClosure ℚ Ω) {y} : Set Ω) with hs
  have hw : IsIntegral (Subring.closure s) (algebraMap (F D) Ω ((w : (F D)ˣ) : F D)) := by
    have : algebraMap (F D) Ω ((w : (F D)ˣ) : F D) ∈
        (integralClosure (Subring.closure s) Ω).toSubring := by
      rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
      rintro ⟨V, hV⟩
      change _ ∈ V
      have hA0V : ∀ r : Algebra.adjoin (algebraicClosure ℚ Ω) {y}, (r : Ω) ∈ V := fun r =>
        hV (Or.inr (IntermediateField.algebra_adjoin_le_adjoin _ _ r.2))
      have hspV : ∀ z ∈ Submodule.span (IntermediateField.adjoin (algebraicClosure ℚ Ω) {y})
          (Set.range b), z ∈ V := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact mem_valuationSubring_of_isIntegral hA0V (hbint i)
        | zero => exact V.zero_mem
        | add x x' _ _ hx hx' => exact add_mem hx hx'
        | smul c x _ hx => exact mul_mem (hV (Or.inr c.2)) hx
      have hFV : ∀ z ∈ N.FNF, z ∈ V := fun z hz => hspV z (hspan z hz)
      have hk : ∀ c : k, algebraMap k Ω c ∈ V := fun c =>
        hV (Or.inl (IntermediateField.algebraMap_mem _ c))
      have ht : t ∈ V := by
        by_contra ht
        obtain ⟨g, hg, hgV⟩ := N.cusp_nf V hk ht
        exact hgV (hFV g hg)
      exact (units_mem ⟨hk, ht⟩ w.2).1
    exact this
  obtain ⟨q, hqT, hq0, hint⟩ := exists_isIntegral_mul_of_isIntegral
    (Algebra.adjoin (kbar k Ω) {y}) (Algebra.adjoin (algebraicClosure ℚ Ω) {y}).toSubring
    (Subring.closure s) (adjoin_algebraicClosure_le_adjoin_kbar y)
    (fun z hz => exists_mul_mem_adjoin_of_mem_closure hz) hw
  exact ⟨q, N.adjoin_algebraicClosure_le_FNF hy hqT, hq0, hint⟩

/-- For a valuation subring `A`, `v_A(x) < 1` iff `x = 0` or `x⁻¹ ∉ A`. -/
lemma _root_.ValuationSubring.valuation_lt_one_iff_eq_zero_or_inv_notMem {K : Type*} [Field K]
    (A : ValuationSubring K) (x : K) : A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hpos : 0 < A.valuation x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
    rw [← A.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ hpos]
    simp [hx]

/-- At an NF-point `W`, every `z ∈ F_NF ∩ W` is a root mod `𝔪_W` of a nonzero rational
polynomial. -/
lemma exists_poly_valuation_aeval_lt_one {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) {z : Ω} (hz : z ∈ N.FNF)
    (hzW : z ∈ W) : ∃ p : ℚ[X], p ≠ 0 ∧ W.valuation (aeval z p) < 1 := by
  set V : ValuationSubring N.FNF := W.comap N.FNF.subtype
  have hVmem : ∀ x : N.FNF, x ∈ V ↔ (x : Ω) ∈ W := fun x => Iff.rfl
  have hV : V ≠ ⊤ := by
    obtain ⟨g₀, hg₀, hg₀W⟩ := hW
    intro hV
    exact hg₀W ((hVmem ⟨g₀, hg₀⟩).1 (hV ▸ ValuationSubring.mem_top _))
  have hQ : ∀ c : ℚ, algebraMap ℚ Ω c ∈ W := fun c => by
    rw [eq_ratCast (algebraMap ℚ Ω) c, ← map_ratCast (algebraMap k Ω) c]
    exact hk _
  have hkV : ∀ c : ℚ, algebraMap ℚ N.FNF c ∈ V := fun c => by
    rw [hVmem]
    have : ((algebraMap ℚ N.FNF c : N.FNF) : Ω) = algebraMap ℚ Ω c := by
      rw [eq_ratCast (algebraMap ℚ N.FNF) c, eq_ratCast (algebraMap ℚ Ω) c]
      push_cast
      rfl
    rw [this]
    exact hQ c
  letI := Decomposition.residueAlgebra V hkV
  have hkresV := Decomposition.residue_algebraMap_residueAlgebra V hkV
  obtain ⟨p, hp0, hp⟩ := isAlgebraic_residue_of_trdeg_le_one V hkV hkresV N.trdeg_le_one hV
    (residue V ⟨⟨z, hz⟩, hzW⟩)
  rw [← residue_eval₂_codRestrict V hkV hkresV ⟨⟨z, hz⟩, hzW⟩ p] at hp
  set ψV := (algebraMap ℚ N.FNF).codRestrict V.toSubring hkV
  set e : V := eval₂ ψV ⟨⟨z, hz⟩, hzW⟩ p
  have he : ((e : N.FNF) : Ω) = aeval z p := by
    have := Polynomial.hom_eval₂ p ψV (N.FNF.subtype.comp V.toSubring.subtype)
      ⟨⟨z, hz⟩, hzW⟩
    rw [show (N.FNF.subtype.comp V.toSubring.subtype).comp ψV = algebraMap ℚ Ω from
      RingHom.ext_rat _ _] at this
    rw [aeval_def]
    exact this
  refine ⟨p, hp0, ?_⟩
  have hlt : V.valuation (e : N.FNF) < 1 :=
    (V.valuation_lt_one_iff e).1 ((residue_eq_zero_iff e).1 hp)
  rw [ValuationSubring.valuation_lt_one_iff_eq_zero_or_inv_notMem] at hlt ⊢
  rw [← he]
  rcases hlt with h | h
  · left
    rw [h]
    rfl
  · right
    intro h'
    apply h
    rw [hVmem]
    simpa using h'

/-- At an NF-point, an NF-function regular there is congruent to an algebraic number. -/
theorem exists_isAlgebraic_valuation_sub_lt_one [IsAlgClosed Ω] {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) {z : Ω} (hz : z ∈ N.FNF)
    (hzW : z ∈ W) : ∃ α : Ω, IsAlgebraic ℚ α ∧ W.valuation (z - α) < 1 := by
  obtain ⟨p, hp0, hlt⟩ := N.exists_poly_valuation_aeval_lt_one hk hW hz hzW
  set q : Polynomial Ω := p.map (algebraMap ℚ Ω)
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ Ω).injective).2 hp0
  have hprod : q = C q.leadingCoeff * (q.roots.map (X - C ·)).prod :=
    (IsAlgClosed.splits q).eq_prod_roots
  have heval : aeval z p = q.leadingCoeff * (q.roots.map fun r => z - r).prod := by
    have := congrArg (eval z) hprod
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map] at this
    have hq : aeval z p = eval z q := by rw [aeval_def, eval₂_eq_eval_map]
    rw [hq]
    simpa using this
  have hlc : W.valuation q.leadingCoeff = 1 := by
    have hQ : ∀ c : ℚ, algebraMap ℚ Ω c ∈ W := fun c => by
      rw [eq_ratCast (algebraMap ℚ Ω) c, ← map_ratCast (algebraMap k Ω) c]
      exact hk _
    have hlc' : q.leadingCoeff = algebraMap ℚ Ω p.leadingCoeff :=
      leadingCoeff_map_of_injective (algebraMap ℚ Ω).injective p
    have hne : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq0
    refine le_antisymm ((W.valuation_le_one_iff _).2 (hlc' ▸ hQ _)) ?_
    have hinv : W.valuation q.leadingCoeff⁻¹ ≤ 1 := by
      rw [W.valuation_le_one_iff, hlc', ← map_inv₀]
      exact hQ _
    rw [map_inv₀] at hinv
    exact inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)) |>.1 hinv
  by_contra hne
  push Not at hne
  rw [heval, map_mul, hlc, one_mul, map_multiset_prod, Multiset.map_map] at hlt
  refine absurd hlt (not_lt.2 (Multiset.one_le_prod_of_one_le fun v hv => ?_))
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hv
  refine hne r ⟨p, hp0, ?_⟩
  have := (mem_roots hq0).1 hr
  rwa [IsRoot, eval_map, ← aeval_def] at this

omit [CharZero k] [CharZero Ω] in
/-- Elements of `k̄` lie in every valuation subring `W ⊇ k`. -/
lemma mem_of_mem_kbar {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W) {x : Ω}
    (hx : x ∈ kbar k Ω) : x ∈ W :=
  Curve.mem_of_isIntegral hk (mem_algebraicClosure_iff.1 hx).isIntegral

/-- **Gauss lemma at NF-points**: for `c_j ∈ k̄` linearly independent over `k̄_NF` and
`a_j ∈ F_NF`, `ord_W (∑ c_j a_j) = min_j ord_W a_j` (multiplicatively: each `v(a_i) ≤ v(∑)`). -/
theorem valuation_le_valuation_sum [IsAlgClosed Ω] {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) {ι : Type*} [Fintype ι]
    (c : ι → Ω) (hc : ∀ i, c i ∈ kbar k Ω)
    (hli : LinearIndependent (algebraicClosure ℚ Ω) c)
    (a : ι → Ω) (ha : ∀ i, a i ∈ N.FNF) (i : ι) :
    W.valuation (a i) ≤ W.valuation (∑ j, c j * a j) := by
  set v := W.valuation
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => v (a j)
  set u := a j₀
  by_cases hu : u = 0
  · have : a i = 0 := by
      have := hj₀ i
      rwa [show v u = 0 by simp [hu], le_zero_iff, Valuation.zero_iff] at this
    simp [this]
  have hupos : 0 < v u := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hu)
  set b : ι → Ω := fun j => a j / u
  have hbF : ∀ j, b j ∈ N.FNF := fun j => N.FNF.div_mem (ha j) (ha j₀)
  have hbW : ∀ j, b j ∈ W := fun j => by
    rw [← W.valuation_le_one_iff, map_div₀, div_le_one₀ hupos]
    exact hj₀ j
  choose α hα hαlt using fun j => N.exists_isAlgebraic_valuation_sub_lt_one hk hW (hbF j) (hbW j)
  have hα₀ : α j₀ ≠ 0 := by
    intro h
    have := hαlt j₀
    rw [h, sub_zero, show b j₀ = 1 from div_self hu, map_one] at this
    exact lt_irrefl _ this
  set β := ∑ j, c j * α j
  have hβ0 : β ≠ 0 := by
    intro h
    have := (Fintype.linearIndependent_iff.1 hli)
      (fun j => ⟨α j, mem_algebraicClosure_iff.2 (hα j)⟩) (by
        rw [← h]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
        rfl) j₀
    exact hα₀ (congrArg Subtype.val this)
  have hβk : β ∈ kbar k Ω := (kbar k Ω).sum_mem fun j _ =>
    (kbar k Ω).mul_mem (hc j) (mem_kbar_of_isAlgebraic (k := k) (hα j))
  have hβ1 : v β = 1 := by
    have hβpos : 0 < v β := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hβ0)
    refine le_antisymm ((W.valuation_le_one_iff _).2 (mem_of_mem_kbar hk hβk)) ?_
    have hinv : v β⁻¹ ≤ 1 :=
      (W.valuation_le_one_iff _).2 (mem_of_mem_kbar hk ((kbar k Ω).inv_mem hβk))
    rw [map_inv₀] at hinv
    exact (inv_le_one₀ hβpos).1 hinv
  have hdiff : v ((∑ j, c j * a j) / u - β) < 1 := by
    have : (∑ j, c j * a j) / u - β = ∑ j, c j * (b j - α j) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [b]
      ring
    rw [this]
    refine v.map_sum_lt one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((W.valuation_le_one_iff _).2
      (mem_of_mem_kbar hk (hc j)))) (hαlt j)
  have hS : v ((∑ j, c j * a j) / u) = 1 := by
    rw [show (∑ j, c j * a j) / u = β + ((∑ j, c j * a j) / u - β) by ring,
      Valuation.map_add_eq_of_lt_left _ (by rw [hβ1]; exact hdiff), hβ1]
  rw [map_div₀, div_eq_one_iff_eq hupos.ne'] at hS
  rw [hS]
  exact hj₀ i

omit [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω] in
/-- An element of `Ω` lying in every valuation subring containing `k` is algebraic over `k`. -/
lemma mem_kbar_of_forall_mem {e : Ω}
    (h : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → e ∈ W) :
    e ∈ kbar k Ω := by
  have he : e ∈ (⨅ V : {V : ValuationSubring Ω // (kbar k Ω : Set Ω) ⊆ V.toSubring},
      V.1.toSubring) := by
    refine Subring.mem_iInf.2 fun V => h V.1 fun c => V.2 ?_
    exact (kbar k Ω).algebraMap_mem c
  rw [iInf_valuationSubring_superset] at he
  have hint : IsIntegral (Subring.closure (kbar k Ω : Set Ω)) e := he
  have hle : Subring.closure (kbar k Ω : Set Ω) ≤ (kbar k Ω).toSubfield.toSubring :=
    Subring.closure_le.2 fun _ hz => hz
  let φ : Subring.closure (kbar k Ω : Set Ω) →+* kbar k Ω :=
    { toFun := fun x => ⟨x, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hcomp : (algebraMap (kbar k Ω) Ω).comp φ =
      (RingHom.id Ω).comp (algebraMap (Subring.closure (kbar k Ω : Set Ω)) Ω) := by
    ext x; rfl
  have hint' : IsIntegral (kbar k Ω) (RingHom.id Ω e) :=
    hint.map_of_comp_eq φ (RingHom.id Ω) hcomp
  exact mem_algebraicClosure_iff.2 (hint'.isAlgebraic.restrictScalars k)

/-- **Units of `U` descend to `k̄_NF` up to constants** (the descent of principal divisors
supported on NF-points, [AbsTopIII] Prop. 1.8, proof T3 l.2099–2106): for every unit `w` of `U`
there is `l ∈ k̄ˣ` with `l · w ∈ F_NF`. -/
theorem unitsDescend [IsAlgClosed Ω] (w : units D) : ∃ l : Ω, l ≠ 0 ∧ l ∈ kbar k Ω ∧
    l * algebraMap (F D) Ω ((w : (F D)ˣ) : F D) ∈ N.FNF := by
  classical
  set w' := algebraMap (F D) Ω ((w : (F D)ˣ) : F D) with hw'
  have hw0 : w' ≠ 0 := by
    rw [hw', map_ne_zero_iff _ (algebraMap (F D) Ω).injective]
    exact Units.ne_zero _
  have hwinv : algebraMap (F D) Ω (((w⁻¹ : units D) : (F D)ˣ) : F D) = w'⁻¹ := by
    rw [hw', ← map_inv₀]
    congr 1
    rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  -- non-NF places `W ⊇ k` contain `w'⁻¹`
  have hnonNF : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      ¬ N.IsNFPoint W → w'⁻¹ ∈ W := by
    intro W hk hW
    have ht : t ∈ W := by
      by_contra ht
      obtain ⟨g, hg, hgW⟩ := N.cusp_nf W hk ht
      exact hW ⟨g, hg, hgW⟩
    rw [← hwinv]
    exact (units_mem (D := D) ⟨hk, ht⟩ (w⁻¹).2).1
  -- `w' ∈ k̄ · F_NF`
  obtain ⟨y, hy, hyt⟩ := N.exists_transcendental
  obtain ⟨q, hq, hq0, hint⟩ := N.exists_isIntegral_mul hy hyt w
  have hqwF : q * w' ∈ F (baseChange D) :=
    mul_mem (N.mem_F q hq) (le_F_baseChange D ((w : (F D)ˣ) : F D).2)
  have hqw := N.mem_adjoin_of_isIntegral hy hyt hqwF hint
  have hwA : w' ∈ Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω) := by
    have : w' = q⁻¹ * (q * w') := by rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
    rw [this]
    exact mul_mem (Algebra.subset_adjoin (N.FNF.inv_mem hq)) hqw
  -- `w' = ∑ c_b * a_b` with `a_b ∈ F_NF`, `c_b ∈ k̄` linearly independent over `F_NF`
  have hspan : w' ∈ Submodule.span (kbar k Ω) (N.FNF : Set Ω) := by
    have h2 : w' ∈ Subalgebra.toSubmodule (Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω)) := hwA
    rw [Algebra.adjoin_eq_span] at h2
    have h3 : Submonoid.closure (N.FNF : Set Ω) = N.FNF.toSubmonoid :=
      Submonoid.closure_eq N.FNF.toSubmonoid
    rw [h3] at h2
    exact h2
  obtain ⟨T, hTF, hT⟩ := Submodule.mem_span_finite_of_mem_span hspan
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hT
  set C : Finset Ω := T.image fun a => (f a : Ω)
  have hwC : w' ∈ Submodule.span N.FNF (C : Set Ω) := by
    rw [← hf]
    refine Submodule.sum_mem _ fun a ha => ?_
    have e : f a • a = (⟨a, hTF ha⟩ : N.FNF) • (f a : Ω) := by
      rw [Algebra.smul_def, Subfield.smul_def, mul_comm]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ ha))
  obtain ⟨B, hBC, hBsp, hBli⟩ := exists_linearIndependent N.FNF (C : Set Ω)
  have hwB : w' ∈ Submodule.span N.FNF B := hBsp ▸ hwC
  haveI : Fintype B := (C.finite_toSet.subset hBC).fintype
  obtain ⟨g, hg⟩ := Submodule.mem_span_iff_of_fintype.1 hwB
  set c : B → Ω := Subtype.val
  set a : B → Ω := fun b => (g b : Ω)
  have hc : ∀ b, c b ∈ kbar k Ω := by
    intro b
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (hBC b.2)
    change (b : Ω) ∈ kbar k Ω
    rw [← hx]
    exact (f x).2
  have ha : ∀ b, a b ∈ N.FNF := fun b => (g b).2
  have hli : LinearIndependent (algebraicClosure ℚ Ω) c := by
    rw [linearIndependent_iff'] at hBli ⊢
    intro s μ hμ i hi
    have := hBli s (fun j => ⟨μ j, N.algebraic_mem _ (mem_algebraicClosure_iff.1 (μ j).2)⟩)
      (by
        rw [← hμ]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Subfield.smul_def, Algebra.smul_def]
        rfl) i hi
    have h1 : ((μ i : algebraicClosure ℚ Ω) : Ω) = 0 := congrArg Subtype.val this
    exact Subtype.ext h1
  have hsum : w' = ∑ b, c b * a b := by
    rw [← hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  obtain ⟨b0, hb0⟩ : ∃ b0, a b0 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hw0
    rw [hsum]
    exact Finset.sum_eq_zero fun b _ => by rw [hall b, mul_zero]
  -- `a b0 / w'` has no poles
  have he : a b0 * w'⁻¹ ∈ kbar k Ω := by
    refine mem_kbar_of_forall_mem fun W hk => ?_
    by_cases hW : N.IsNFPoint W
    · have hle := N.valuation_le_valuation_sum hk hW c hc hli a ha b0
      rw [← hsum] at hle
      rw [← W.valuation_le_one_iff, map_mul, map_inv₀]
      have hv0 : W.valuation w' ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
      calc W.valuation (a b0) * (W.valuation w')⁻¹
          ≤ W.valuation w' * (W.valuation w')⁻¹ := mul_le_mul_left hle _
        _ = 1 := mul_inv_cancel₀ hv0
    · have hab : a b0 ∈ W := by
        by_contra hn
        exact hW ⟨a b0, ha b0, hn⟩
      exact W.mul_mem _ _ hab (hnonNF W hk hW)
  refine ⟨a b0 * w'⁻¹, mul_ne_zero hb0 (inv_ne_zero hw0), he, ?_⟩
  rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one]
  exact ha b0

end NFModel

end CurvesJacobian.Kummer
