/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverConstantField
import CurvesJacobian.Cusp.CuspDegreeEq

/-!
# Cusps of a cover dominate the cusps of the base

Let `X̄` be a curve over a field `k` of characteristic zero, `N` a curve over a finite extension
`k'` of `k` and `q : N ⟶ X̄` a surjective morphism compatible with the structure morphisms. For a
nonempty open `U ⊆ X̄` we show (`CurvesJacobian.Cusp.cuspDegree_le_cuspDegree_of_surjective`)

  `Σ_{c ∉ U} [κ(c) : k] ≤ Σ_{c' ∉ q⁻¹ U} [κ(c') : k']`.

Proof: with `Ω` an algebraic closure of `k'`, both sides are the numbers of points of
`X̄_Ω ∖ U_Ω` and `N_Ω ∖ (q⁻¹U)_Ω` (`CurvesJacobian.Cusp.card_compl_eq_cuspDegree_of_isCurveOver`).
The induced `Ω`-morphism `Φ : N_Ω ⟶ X̄_Ω` is universally closed (`N_Ω` is proper over `Ω`), so
its range is closed; if it is not everything it is finite, hence (Jacobson) the image of the
generic point of `N_Ω` is a closed point and `Φ` is constant, which forces `X̄` to be a single
point lying in `U`. Hence `Φ` maps `N_Ω ∖ (q⁻¹U)_Ω` onto `X̄_Ω ∖ U_Ω`.

For the normalisation `N` of `X̄` in a finite étale cover `Y ⟶ U` (with `Y` integral), the
morphism `q = fromNormalization` is surjective (`CurvesJacobian.Cusp.surjective_fromNormalization`)
and `N` is a curve over its constant field, giving
`CurvesJacobian.Cusp.cuspDegree_le_cuspDegree_normalization`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section General

variable {k : Type u} [Field k] [CharZero k] {Xb : Scheme.{u}} [Xb.Over (Spec (.of k))]
  [IsCurveOver k Xb] {k' : Type u} [Field k'] [Algebra k k'] {N : Scheme.{u}}
  [N.Over (Spec (.of k'))] [IsCurveOver k' N]

/-- The morphism `N_Ω ⟶ X̄_Ω` induced by `q : N ⟶ X̄` over `Spec k' ⟶ Spec k`. -/
def baseChangeMap (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra k' Ω] [IsScalarTower k k' Ω]
    (q : N ⟶ Xb)
    (hq : (N ↘ Spec (.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      q ≫ (Xb ↘ Spec (.of k))) :
    baseChange k' Ω N ⟶ baseChange k Ω Xb :=
  pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _) (by
    have h : specAlgebraMap k' Ω ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
        specAlgebraMap k Ω := by
      rw [specAlgebraMap, specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
    rw [Category.assoc, ← hq, ← Category.assoc, pullback.condition, Category.assoc, h])

omit [CharZero k] in
/-- **The base-changed morphism maps the complement of `(q⁻¹U)_Ω` onto that of `U_Ω`.** -/
theorem card_compl_le_card_compl (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra k' Ω] [IsScalarTower k k' Ω] (q : N ⟶ Xb)
    (hq : (N ↘ Spec (.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      q ≫ (Xb ↘ Spec (.of k)))
    (hsurj : Function.Surjective q) (U : Xb.Opens) (hU : (U : Set Xb).Nonempty) :
    Nat.card ((baseChangeOpen k Ω U : Set (baseChange k Ω Xb))ᶜ : Set _) ≤
      Nat.card ((baseChangeOpen k' Ω (q ⁻¹ᵁ U) : Set (baseChange k' Ω N))ᶜ : Set _) := by
  have hV : ((q ⁻¹ᵁ U : N.Opens) : Set N).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨c, rfl⟩ := hsurj x
    exact ⟨c, hx⟩
  let Φ : baseChange k' Ω N ⟶ baseChange k Ω Xb := baseChangeMap Ω q hq
  have hΦfst : ∀ z, pullback.fst (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω) (Φ z) =
      q (pullback.fst (N ↘ Spec (.of k')) (specAlgebraMap k' Ω) z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    simp only [Φ, baseChangeMap, pullback.lift_fst]
  -- `Φ` is universally closed.
  haveI : IsProper (pullback.snd (N ↘ Spec (.of k')) (specAlgebraMap k' Ω)) :=
    (inferInstance : IsCurveOver Ω (baseChange k' Ω N)).toIsProper
  haveI : IsProper (pullback.snd (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω)) :=
    (inferInstance : IsCurveOver Ω (baseChange k Ω Xb)).toIsProper
  haveI : UniversallyClosed (Φ ≫ pullback.snd (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω)) := by
    simp only [Φ, baseChangeMap, pullback.lift_snd]
    infer_instance
  haveI : UniversallyClosed Φ :=
    UniversallyClosed.of_comp_of_isSeparated Φ (pullback.snd _ _)
  haveI : LocallyOfFiniteType (pullback.snd (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω)) :=
    inferInstance
  haveI : JacobsonSpace (baseChange k Ω Xb) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω))
  haveI := IsCurveOver.isIntegral Ω (baseChange k' Ω N)
  haveI := surjective_specAlgebraMap k' Ω
  -- Every point outside `U_Ω` is in the range of `Φ`.
  have hrange : ∀ y : baseChange k Ω Xb, y ∉ baseChangeOpen k Ω U → y ∈ Set.range Φ := by
    intro y hy
    by_contra hyR
    have hcl : IsClosed (Set.range Φ) := Φ.isClosedMap.isClosed_range
    have hfin : (Set.range Φ).Finite := by
      have := Anabelian.finite_compl_of_isCurveOver (k := Ω) (baseChange k Ω Xb)
        ⟨(Set.range Φ)ᶜ, hcl.isOpen_compl⟩ ⟨y, hyR⟩
      simpa using this
    let η := genericPoint (baseChange k' Ω N)
    have hη : IsClosed {Φ η} := isClosed_singleton_of_mem_finite hcl hfin ⟨η, rfl⟩
    have hconst : ∀ z, Φ z = Φ η := fun z ↦ by
      have h1 : η ⤳ z := (genericPoint_spec (baseChange k' Ω N)).specializes (Set.mem_univ z)
      have h2 : Φ η ⤳ Φ z := h1.map Φ.continuous
      rw [specializes_iff_mem_closure, hη.closure_eq] at h2
      exact h2
    have hall : ∀ x : Xb, x = pullback.fst (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω) (Φ η) := by
      intro x
      obtain ⟨c, rfl⟩ := hsurj x
      obtain ⟨z, rfl⟩ := (pullback.fst (N ↘ Spec (.of k')) (specAlgebraMap k' Ω)).surjective c
      rw [← hΦfst, hconst]
    apply hy
    change pullback.fst (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω) y ∈ U
    obtain ⟨x, hx⟩ := hU
    rw [hall (pullback.fst (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω) y), ← hall x]
    exact hx
  haveI := (compl_finite_baseChangeOpen k' Ω hV).to_subtype
  let G : ((baseChangeOpen k' Ω (q ⁻¹ᵁ U) : Set (baseChange k' Ω N))ᶜ : Set _) →
      ((baseChangeOpen k Ω U : Set (baseChange k Ω Xb))ᶜ : Set _) := fun z ↦
    ⟨Φ z.1, by
      intro h
      apply z.2
      change pullback.fst (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω) (Φ z.1) ∈ U at h
      rw [hΦfst] at h
      exact h⟩
  have hG : Function.Surjective G := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hrange y hy
    refine ⟨⟨z, fun hz ↦ hy ?_⟩, rfl⟩
    change pullback.fst (Xb ↘ Spec (.of k)) (specAlgebraMap k Ω) (Φ z) ∈ U
    rw [hΦfst]
    exact hz
  exact Nat.card_le_card_of_surjective G hG

/-- **`Σ_{c ∉ U} [κ(c) : k] ≤ Σ_{c' ∉ q⁻¹ U} [κ(c') : k']`** for a surjective morphism
`q : N ⟶ X̄` from a curve over `k'` to a curve over `k`, compatible with `k → k'`. -/
theorem cuspDegree_le_cuspDegree_of_surjective (q : N ⟶ Xb)
    (hq : (N ↘ Spec (.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      q ≫ (Xb ↘ Spec (.of k)))
    (hsurj : Function.Surjective q) (U : Xb.Opens) (hU : (U : Set Xb).Nonempty) :
    Anabelian.cuspDegree k Xb U ≤ Anabelian.cuspDegree k' N (q ⁻¹ᵁ U) := by
  haveI : CharZero k' := charZero_of_injective_algebraMap (algebraMap k k').injective
  have hV : ((q ⁻¹ᵁ U : N.Opens) : Set N).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨c, rfl⟩ := hsurj x
    exact ⟨c, hx⟩
  rw [← card_compl_eq_cuspDegree_of_isCurveOver k (AlgebraicClosure k') U hU,
    ← card_compl_eq_cuspDegree_of_isCurveOver k' (AlgebraicClosure k') (q ⁻¹ᵁ U) hV]
  exact card_compl_le_card_compl (AlgebraicClosure k') q hq hsurj U hU

end General

/-! ### The normalisation of a curve in a finite étale cover -/

section Normalization

variable {k : Type u} [Field k] [CharZero k] {Xb : Scheme.{u}} [Xb.Over (Spec (.of k))]
  [IsCurveOver k Xb] {U : Xb.Opens} (hU : (U : Set Xb).Nonempty) {Y : Scheme.{u}}
  (p : Y ⟶ U) [IsFinite p] [Etale p]

include hU in
/-- **`fromNormalization : N ⟶ X̄` is surjective**: it is finite (so its range is closed) and its
range contains the nonempty open range of the étale morphism `Y ⟶ U ⊆ X̄`. -/
theorem surjective_fromNormalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    Function.Surjective (p ≫ U.ι).fromNormalization := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  haveI := IsCurveOver.isIntegral k Xb
  haveI := isFinite_fromNormalization_of_isCurveOver (k := k) hU p
  have hcl : IsClosed (Set.range (p ≫ U.ι).fromNormalization) :=
    (p ≫ U.ι).fromNormalization.isClosedMap.isClosed_range
  haveI : UniversallyOpen p := UniversallyOpen.of_flat p
  have hop : IsOpen (Set.range (p ≫ U.ι)) := (p ≫ U.ι).isOpenMap.isOpen_range
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hd : Dense (Set.range (p ≫ U.ι)) := hop.dense ⟨_, y, rfl⟩
  have hsub : Set.range (p ≫ U.ι) ⊆ Set.range (p ≫ U.ι).fromNormalization := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(p ≫ U.ι).toNormalization y, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]⟩
  have h := hcl.closure_subset_iff.mpr hsub
  rw [hd.closure_eq] at h
  exact fun x ↦ h (Set.mem_univ x)

include hU in
/-- **Step B**: for the normalisation `N` of `X̄` in a finite étale cover `Y ⟶ U` with `Y`
integral, a curve over its constant field `k'` via some `s' : N ⟶ Spec k'` lifting
`q ≫ (X̄ ↘ Spec k)`, we have `Σ_{c ∉ U} [κ(c) : k] ≤ Σ_{c' ∉ q⁻¹ U} [κ(c') : k']`. -/
theorem cuspDegree_le_cuspDegree_normalization [IsIntegral Y] :
    haveI := isLocallyNoetherian_of_isCurveOver k Xb
    letI := normalizationOver k p
    ∃ s' : (p ≫ U.ι).normalization ⟶ Spec (.of (constField k (p ≫ U.ι).normalization)),
      s' ≫ Spec.map (CommRingCat.ofHom
          (algebraMap k (constField k (p ≫ U.ι).normalization))) =
        (p ≫ U.ι).fromNormalization ≫ (Xb ↘ Spec (.of k)) ∧
      letI : (p ≫ U.ι).normalization.Over
          (Spec (.of (constField k (p ≫ U.ι).normalization))) := ⟨s'⟩
      IsCurveOver (constField k (p ≫ U.ι).normalization) (p ≫ U.ι).normalization ∧
        Anabelian.cuspDegree k Xb U ≤
          Anabelian.cuspDegree (constField k (p ≫ U.ι).normalization) (p ≫ U.ι).normalization
            ((p ≫ U.ι).fromNormalization ⁻¹ᵁ U) := by
  haveI := isLocallyNoetherian_of_isCurveOver k Xb
  letI := normalizationOver k p
  obtain ⟨s', hs', hcurve⟩ := isCurveOver_normalization_constField (k := k) hU p
  refine ⟨s', hs', ?_⟩
  letI : (p ≫ U.ι).normalization.Over
      (Spec (.of (constField k (p ≫ U.ι).normalization))) := ⟨s'⟩
  exact ⟨hcurve, cuspDegree_le_cuspDegree_of_surjective (p ≫ U.ι).fromNormalization hs'
    (surjective_fromNormalization (k := k) hU p) U hU⟩

end Normalization

end CurvesJacobian.Cusp
