/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Kähler differentials of a local ring with principal maximal ideal

Let `k` be a field of characteristic zero and `O` a local `k`-algebra with maximal ideal
`𝔪 = (π)`, residue field algebraic over `k`, and `Ω_{O/k}` a finite `O`-module (e.g. the local
ring of a closed point on a smooth curve). Then `Ω_{O/k} = O · dπ`
(`CurvesJacobian.Cusp.kaehler_eq_smul_D`).

Proof: for `u ∈ O` let `p` be the minimal polynomial over `k` of the residue `ū`; it is separable,
so `p(u) ∈ 𝔪` and `p'(u)` is a unit. From `d(p(u)) = p'(u) du` and `p(u) = rπ`,
`du = p'(u)⁻¹ (r dπ + π dr) ∈ O dπ + 𝔪 Ω_{O/k}`; conclude by Nakayama.

Consequently, for an `O`-algebra `F` (e.g. the fraction field), every differential of `F` coming
from `Ω_{O/k}` is of the form `g dπ` with `g ∈ O`
(`CurvesJacobian.Cusp.exists_eq_smul_D_of_mem_range`).
-/

open IsLocalRing KaehlerDifferential Polynomial

namespace CurvesJacobian.Cusp

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsLocalRing O]
  [Algebra k O]

/-- `du ∈ O dπ + 𝔪 Ω_{O/k}` for every `u ∈ O` admitting `p ∈ k[X]` with `p(u) ∈ 𝔪` and `p'(u)` a
unit. -/
lemma D_mem_span_sup_smul {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (u : O) (p : k[X])
    (hp : aeval u p ∈ maximalIdeal O) (hp' : IsUnit (aeval u (derivative p))) :
    D k O u ∈ Submodule.span O {D k O π} ⊔ maximalIdeal O • (⊤ : Submodule O Ω[O⁄k]) := by
  rw [hπ, Ideal.mem_span_singleton'] at hp
  obtain ⟨r, hr⟩ := hp
  have hD := (D k O).map_aeval p u
  rw [← hr, Derivation.leibniz] at hD
  obtain ⟨v, hv⟩ := hp'
  have : D k O u = (↑v⁻¹ : O) • (r • D k O π + π • D k O r) := by
    rw [hD, ← hv, smul_smul, Units.inv_mul, one_smul]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine Submodule.mem_sup_right (Submodule.smul_mem_smul ?_ Submodule.mem_top)
    rw [hπ]
    exact Ideal.mem_span_singleton_self π

/-- In characteristic zero, if the residue field is algebraic over `k`, every `u ∈ O` admits
`p ∈ k[X]` with `p(u) ∈ 𝔪` and `p'(u)` a unit (`p` = minimal polynomial of `ū`). -/
lemma exists_aeval_mem_maximalIdeal [CharZero k] (halg : Algebra.IsAlgebraic k (ResidueField O))
    (u : O) : ∃ p : k[X], aeval u p ∈ maximalIdeal O ∧ IsUnit (aeval u (derivative p)) := by
  set ū := residue O u
  have hint : IsIntegral k ū := (halg.isAlgebraic ū).isIntegral
  set p := minpoly k ū
  have hsep : p.Separable := (minpoly.irreducible hint).separable
  have hres : ∀ q : k[X], residue O (aeval u q) = aeval ū q := fun q ↦ by
    change (IsScalarTower.toAlgHom k O (ResidueField O)) (aeval u q) = _
    rw [← aeval_algHom_apply]
    rfl
  refine ⟨p, ?_, ?_⟩
  · rw [← residue_eq_zero_iff, hres, minpoly.aeval]
  · by_contra h
    have : residue O (aeval u (derivative p)) = 0 := (residue_eq_zero_iff _).2 h
    rw [hres] at this
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval k ū) this

/-- **`Ω_{O/k} = O · dπ`** for a local `k`-algebra `O` with `𝔪 = (π)` and `Ω_{O/k}` finite over
`O`, provided every `u ∈ O` admits `p ∈ k[X]` with `p(u) ∈ 𝔪` and `p'(u)` a unit (e.g. residue
field algebraic over `k` of characteristic `0`, `exists_aeval_mem_maximalIdeal`). -/
theorem kaehler_eq_smul_D [Module.Finite O Ω[O⁄k]]
    (hsep : ∀ u : O, ∃ p : k[X], aeval u p ∈ maximalIdeal O ∧ IsUnit (aeval u (derivative p)))
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (ω : Ω[O⁄k]) : ∃ g : O, ω = g • D k O π := by
  have hle : (⊤ : Submodule O Ω[O⁄k]) ≤ Submodule.span O {D k O π} := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O) Module.Finite.fg_top
      (maximalIdeal_le_jacobson _) ?_
    rw [← span_range_derivation, Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    rw [span_range_derivation]
    obtain ⟨p, hp, hp'⟩ := hsep u
    exact D_mem_span_sup_smul hπ u p hp hp'
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp (hle Submodule.mem_top (x := ω))
  exact ⟨g, hg.symm⟩

/-- **Differentials of `F` coming from `Ω_{O/k}` are `g dπ` with `g ∈ O`.** -/
theorem exists_eq_smul_D_of_mem_range [Module.Finite O Ω[O⁄k]]
    (hsep : ∀ u : O, ∃ p : k[X], aeval u p ∈ maximalIdeal O ∧ IsUnit (aeval u (derivative p)))
    {π : O} (hπ : maximalIdeal O = Ideal.span {π})
    {F : Type*} [CommRing F] [Algebra k F] [Algebra O F] [IsScalarTower k O F]
    {ω : Ω[F⁄k]} (hω : ω ∈ LinearMap.range ((map k k O F).restrictScalars k)) :
    ∃ g : O, ω = algebraMap O F g • D k F (algebraMap O F π) := by
  obtain ⟨η, rfl⟩ := hω
  obtain ⟨g, rfl⟩ := kaehler_eq_smul_D hsep hπ η
  refine ⟨g, ?_⟩
  rw [LinearMap.restrictScalars_apply, LinearMap.map_smul, map_D, algebraMap_smul]

/-- The image of `du` in `Ω_{F/k}` is `g dπ` with `g ∈ O`. -/
theorem exists_D_eq_smul_D [Module.Finite O Ω[O⁄k]]
    (hsep : ∀ u : O, ∃ p : k[X], aeval u p ∈ maximalIdeal O ∧ IsUnit (aeval u (derivative p)))
    {π : O} (hπ : maximalIdeal O = Ideal.span {π})
    {F : Type*} [CommRing F] [Algebra k F] [Algebra O F] [IsScalarTower k O F] (u : O) :
    ∃ g : O, D k F (algebraMap O F u) = algebraMap O F g • D k F (algebraMap O F π) :=
  exists_eq_smul_D_of_mem_range hsep hπ ⟨D k O u, by
    rw [LinearMap.restrictScalars_apply, map_D]⟩

end CurvesJacobian.Cusp
