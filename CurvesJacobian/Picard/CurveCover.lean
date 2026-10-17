/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Curve.Existence
import Belyi.P1.BaseChangeIso
import CurvesJacobian.Scheme.ConstantField
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Curves: two-affine covers and global functions after base change

Let `X` be a curve over a perfect field `k` (`Belyi.IsCurveOver`).

* `IsCurveOver.exists_finite_to_P1`, `IsCurveOver.exists_two_affine_cover`: `X` has a finite
  morphism to `ℙ¹_k` (belyi's `homOfFunctionField` for a transcendental `t ∈ K(X)`), hence is
  covered by two affine opens (the preimages of the two standard charts) whose intersection is
  affine (`X` is separated).
* `IsCurveOver.isIso_appTop`: `Γ(X, 𝒪_X) = k`, i.e. `k → Γ(X, ⊤)` is an isomorphism
  (`Γ(X, 𝒪_X)` is integral over `k` since `X` is proper, and `k` is algebraically closed in
  `K(X)` by geometric integrality, `CurvesJacobian.mem_range_algebraMap_of_isAlgebraic`).
* `IsCurveOver.isIso_app_pullback_snd` (Stacks, Tag 0B9U, for `f_T : X_T → T`): for every
  `k`-scheme `T` and every quasi-compact quasi-separated open `W ⊆ T` (e.g. affine), the map
  `𝒪_T(W) → 𝒪_{X_T}(f_T⁻¹ W)` is an isomorphism, i.e. `𝒪_T ≅ f_{T*} 𝒪_{X_T}` on such opens.
  This is flat base change of global sections (Mathlib's
  `isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`, as every scheme is flat
  over a field) combined with `Γ(X, 𝒪_X) = k`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi

universe u

noncomputable section

namespace CurvesJacobian

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsCurveOver k X]

include k in
/-- In a curve, the intersection of two affine opens is affine (curves are separated). -/
theorem IsCurveOver.isAffineOpen_inf {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.mp (inferInstance :
    IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))) ⊤ (isAffineOpen_top _) U
    (by simp) V (by simp) hU hV

section Cover

variable [PerfectField k]

/-- A curve over a perfect field admits a finite morphism to `ℙ¹`. -/
theorem IsCurveOver.exists_finite_to_P1 : ∃ π : X ⟶ P1 k, IsFinite π := by
  have := IsCurveOver.isIntegral k X
  obtain ⟨t, ht⟩ := exists_transcendental_functionField k X
  exact ⟨_, isFinite_homOfFunctionField_of_isCurveOver k X ht⟩

include k in
/-- A curve over a perfect field is covered by two affine opens (whose intersection is affine
by `IsCurveOver.isAffineOpen_inf`). -/
theorem IsCurveOver.exists_two_affine_cover :
    ∃ U V : X.affineOpens, U.1 ⊔ V.1 = ⊤ := by
  obtain ⟨π, hπ⟩ := IsCurveOver.exists_finite_to_P1 k X
  have hcov : ∀ x : P1 k, x ∈ ((P1.coordCover k).openCover.f (0 : Fin 2)).opensRange ∨
      x ∈ ((P1.coordCover k).openCover.f (1 : Fin 2)).opensRange := by
    intro x
    obtain ⟨i, y, rfl⟩ := (P1.coordCover k).openCover.exists_eq x
    have hi : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hi i with rfl | rfl
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  refine ⟨⟨π ⁻¹ᵁ ((P1.coordCover k).openCover.f (0 : Fin 2)).opensRange,
      (isAffineOpen_opensRange _).preimage π⟩,
    ⟨π ⁻¹ᵁ ((P1.coordCover k).openCover.f (1 : Fin 2)).opensRange,
      (isAffineOpen_opensRange _).preimage π⟩, ?_⟩
  ext x
  simp only [Opens.coe_sup, Set.mem_union, SetLike.mem_coe, Opens.coe_top, Set.mem_univ,
    iff_true]
  exact hcov (π x)

end Cover

section GlobalSections

/-- The structure map `k → Γ(X, 𝒪_X)`, as a ring homomorphism. -/
abbrev structureToGlobal : CommRingCat.of k ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop

omit [IsCurveOver k X] in
lemma algebraMap_functionField_eq [IsIntegral X] (c : k) :
    algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial (structureToGlobal k X c) := rfl

lemma structureToGlobal_isIntegral : (structureToGlobal k X).hom.IsIntegral := by
  rw [CommRingCat.hom_comp]
  exact RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
    (isIntegral_appTop_of_universallyClosed _)

variable [PerfectField k]

/-- `Γ(X, 𝒪_X) = k` for a curve `X` over a perfect field `k`. -/
theorem IsCurveOver.bijective_structureToGlobal :
    Function.Bijective (structureToGlobal k X) := by
  have := IsCurveOver.isIntegral k X
  refine ⟨(structureToGlobal k X).hom.injective, fun s ↦ ?_⟩
  have hint : IsIntegral k (X.presheaf.germ ⊤ (genericPoint X) trivial s) := by
    obtain ⟨p, hp, hps⟩ := structureToGlobal_isIntegral k X s
    refine ⟨p, hp, ?_⟩
    have := congrArg (X.presheaf.germ ⊤ (genericPoint X) trivial).hom hps
    rw [map_zero, Polynomial.hom_eval₂] at this
    exact this
  obtain ⟨c, hc⟩ := curve_mem_range_algebraMap_of_isAlgebraic k X hint.isAlgebraic
  refine ⟨c, germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial ?_⟩
  rw [← hc, algebraMap_functionField_eq]

/-- `Γ(X, 𝒪_X) = k`: the structure map on global sections is an isomorphism. -/
theorem IsCurveOver.isIso_appTop : IsIso (X ↘ Spec (CommRingCat.of k)).appTop := by
  have : IsIso (structureToGlobal k X) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (IsCurveOver.bijective_structureToGlobal k X)
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _

/-- **Stacks, Tag 0B9U** (conclusion `𝒪_T ≅ f_{T*}𝒪_{X_T}`): for a curve `X` over a perfect
field `k`, any `k`-scheme `T` and any quasi-compact quasi-separated open `W ⊆ T`, the pullback
`f_T : X_T = X ×_k T → T` induces an isomorphism `𝒪_T(W) ≅ 𝒪_{X_T}(f_T⁻¹ W)`. -/
theorem IsCurveOver.isIso_app_pullback_snd {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of k))
    (W : T.Opens) (hW : IsCompact (W : Set T)) (hW' : IsQuasiSeparated (W : Set T)) :
    IsIso ((pullback.snd (X ↘ Spec (CommRingCat.of k)) g).app W) := by
  have H := IsPullback.of_hasPullback (X ↘ Spec (CommRingCat.of k)) g
  have hUY : pullback.snd (X ↘ Spec (CommRingCat.of k)) g ⁻¹ᵁ W =
      pullback.fst (X ↘ Spec (CommRingCat.of k)) g ⁻¹ᵁ ⊤ ⊓
        pullback.snd (X ↘ Spec (CommRingCat.of k)) g ⁻¹ᵁ W := by
    simp
  have : CompactSpace X :=
    (quasiCompact_iff_compactSpace (X ↘ Spec (CommRingCat.of k))).mp inferInstance
  have : QuasiSeparatedSpace X :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mp
      (inferInstance : QuasiSeparated (X ↘ Spec (CommRingCat.of k)))
  have hpush := (isIso_pushoutSection_iff H (show W ≤ g ⁻¹ᵁ ⊤ by simp)
    (show (⊤ : X.Opens) ≤ (X ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ by simp) hUY).mp
    (isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat H _ _ hUY
      (isAffineOpen_top _) hW hW' isCompact_univ isQuasiSeparated_univ
      (by
        have : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
          (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
            (Field.toIsField k)
        exact RingHom.Flat.of_isField this _))
  have : IsIso ((X ↘ Spec (CommRingCat.of k)).appLE ⊤ ⊤ (by simp)) := by
    have e : (X ↘ Spec (CommRingCat.of k)).appLE ⊤ ⊤ (by simp) =
        (X ↘ Spec (CommRingCat.of k)).appTop :=
      (Scheme.Hom.app_eq_appLE (f := X ↘ Spec (CommRingCat.of k))).symm
    rw [e]
    exact IsCurveOver.isIso_appTop k X
  have : IsIso (pushout.inr ((X ↘ Spec (CommRingCat.of k)).appLE ⊤ ⊤ (by simp))
      (g.appLE ⊤ W (by simp))) := inferInstance
  rw [Scheme.Hom.app_eq_appLE, ← hpush.inr_isoPushout_inv]
  infer_instance

end GlobalSections

end CurvesJacobian

end
