/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Descent of smoothness of relative dimension `n` along field extensions

For fields `K₀ ⊆ K` and a `K₀`-algebra `A` which is a domain, if `Spec (K ⊗[K₀] A) → Spec K` is
smooth of relative dimension `n`, then so is `Spec A → Spec K₀`
(`CurvesJacobian.smoothOfRelativeDimension_of_baseChange`).

Proof. Smoothness descends along the faithfully flat `K₀ → K`
(`Algebra.Smooth.of_smooth_tensorProduct_of_faithfully_flat`), so `A` is covered by standard
smooth localizations `A_x` (`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`), of some
relative dimension `m`. The base change `K ⊗ A_x` is standard smooth of relative dimension `m`
and a localization of `K ⊗ A`, hence also locally standard smooth of relative dimension `n`;
on a nonzero localization the two relative dimensions are both the rank of the free module of
Kähler differentials, so `m = n`.
-/

open TensorProduct AlgebraicGeometry

universe u

namespace CurvesJacobian

/-- **The relative dimension of a nontrivial standard smooth algebra is unique** (it is the rank
of the free module of Kähler differentials). -/
lemma isStandardSmoothOfRelativeDimension_unique {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Nontrivial S] {m n : ℕ} (hm : Algebra.IsStandardSmoothOfRelativeDimension m R S)
    (hn : Algebra.IsStandardSmoothOfRelativeDimension n R S) : m = n := by
  have h1 :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := S) m
  have h2 :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := S) n
  exact_mod_cast h1.symm.trans h2

/-- In a nontrivial ring, some member of a family generating the unit ideal has a nontrivial
localization. -/
lemma exists_nontrivial_localizationAway {S : Type u} [CommRing S] [Nontrivial S] {s : Set S}
    (hs : Ideal.span s = ⊤) : ∃ u ∈ s, Nontrivial (Localization.Away u) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal S
  have : ¬ s ⊆ M := fun h ↦ hM.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 h))
  obtain ⟨u, hus, huM⟩ := Set.not_subset.1 this
  refine ⟨u, hus, ?_⟩
  have hle : Submonoid.powers u ≤ M.primeCompl := by
    rw [Submonoid.powers_le]
    exact huM
  let φ : Localization.Away u →+* Localization.AtPrime M :=
    IsLocalization.map (M := Submonoid.powers u) (T := M.primeCompl) _ (RingHom.id S) hle
  exact φ.domain_nontrivial

variable {K₀ K A : Type u} [Field K₀] [Field K] [Algebra K₀ K] [CommRing A] [Algebra K₀ A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `K ⊗[K₀] A_x` is the localization of `K ⊗[K₀] A` at `1 ⊗ x`. -/
lemma isLocalizationAway_tensor (x : A) :
    letI : Algebra (K ⊗[K₀] A) (K ⊗[K₀] Localization.Away x) :=
      (Algebra.TensorProduct.map (AlgHom.id K K)
        (IsScalarTower.toAlgHom K₀ A (Localization.Away x))).toRingHom.toAlgebra
    IsLocalization.Away ((1 : K) ⊗ₜ[K₀] x) (K ⊗[K₀] Localization.Away x) := by
  letI : Algebra (K ⊗[K₀] A) (K ⊗[K₀] Localization.Away x) :=
    (Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom K₀ A (Localization.Away x))).toRingHom.toAlgebra
  haveI : IsScalarTower K (K ⊗[K₀] A) (K ⊗[K₀] Localization.Away x) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change _ = Algebra.TensorProduct.map _ _ (algebraMap K (K ⊗[K₀] A) c)
      exact ((Algebra.TensorProduct.map (AlgHom.id K K)
        (IsScalarTower.toAlgHom K₀ A (Localization.Away x))).commutes c).symm
  have H := IsLocalization.tensorProduct_tensorProduct_right K₀ K (Submonoid.powers x)
    (Localization.Away x) (by
      ext a
      change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ a) = (1 : K) ⊗ₜ _
      simp)
  rw [Submonoid.map_powers] at H
  exact H

/-- **Descent of smoothness of relative dimension `n`** along a field extension `K₀ ⊆ K`, for a
domain `A`: if `Spec (K ⊗[K₀] A) → Spec K` is smooth of relative dimension `n`, so is
`Spec A → Spec K₀`. -/
theorem smoothOfRelativeDimension_of_baseChange [IsDomain A] {n : ℕ}
    (h : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[K₀] A))))) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap K₀ A))) := by
  have hK : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap K (K ⊗[K₀] A)) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).1 h
  haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[K₀] A)))) :=
    SmoothOfRelativeDimension.smooth n _
  haveI : Algebra.Smooth K (K ⊗[K₀] A) := by
    rw [← RingHom.smooth_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap K (K ⊗[K₀] A)))).1 inferInstance
  haveI : Algebra.Smooth K₀ A := Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K
  obtain ⟨s, hspan, hs⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth K₀ A
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine ⟨s \ {0}, by rw [Ideal.span_sdiff_singleton_zero, hspan], fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := hx.2
  haveI := hs x hx.1
  rw [CommRingCat.hom_ofHom, ← IsScalarTower.algebraMap_eq]
  change RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap K₀ (Localization.Away x))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  -- the relative dimension `m` of a standard smooth presentation of `A_x`
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (hs x hx.1).out
  have hm := P.isStandardSmoothOfRelativeDimension rfl
  suffices hmn : P.dimension = n from hmn ▸ hm
  haveI : IsDomain (Localization.Away x) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  -- the base change `C = K ⊗ A_x`
  let C := K ⊗[K₀] Localization.Away x
  haveI : Nontrivial C :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K
      (Localization.Away x) (algebraMap K₀ K).injective (algebraMap K₀ _).injective
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension K C := inferInstance
  letI : Algebra (K ⊗[K₀] A) C :=
    (Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom K₀ A (Localization.Away x))).toRingHom.toAlgebra
  haveI := isLocalizationAway_tensor (K₀ := K₀) (K := K) (A := A) x
  have hC : (algebraMap (K ⊗[K₀] A) C).comp (algebraMap K (K ⊗[K₀] A)) = algebraMap K C :=
    RingHom.ext fun c ↦ (Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom K₀ A (Localization.Away x))).commutes c
  have hCn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap K C) :=
    hC ▸ (RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
        n).right) _ ((1 : K) ⊗ₜ[K₀] x) _ hK
  obtain ⟨T, hTspan, hT⟩ := hCn
  obtain ⟨u, huT, hu⟩ := exists_nontrivial_localizationAway hTspan
  have h1 := hT u huT
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      ((algebraMap C (Localization.Away u)).comp (algebraMap K C)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      P.dimension).right _ u _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 inferInstance)
  letI := ((algebraMap C (Localization.Away u)).comp (algebraMap K C)).toAlgebra
  exact isStandardSmoothOfRelativeDimension_unique h2 h1

end CurvesJacobian
