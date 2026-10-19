/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.TwistDGC
import CurvesJacobian.Cusp.PullbackCover

/-!
# `Π_{U_{M'}} ⊆ Π_U` for a finite extension `M'/M` (MR8, comparison of Cor 3.7 (a) and (b))

For an affine hyperbolic curve `C = (X̄, U)` over a number field `M ⊆ Ω` and a finite extension
`M ⊆ M' ⊆ Ω`, the base change `C_{M'} = (X̄_{M'}, U_{M'})` (`Belyi.Anabelian.HypCurve.bc`) comes
with the finite étale map `Spec Γ(U_{M'}) ⟶ Spec Γ(U)` (`CurvesJacobian.Cusp.bcSpec`), a base
change of `Spec M' ⟶ Spec M` (`CurvesJacobian.Cusp.isPullback_bcSpec`). Hence:

* **`CurvesJacobian.Cusp.range_bcPiHom`**: the image of `Π_{U_{M'}} ↪ Π_U`
  (`CurvesJacobian.Cusp.coverPiHom`) is the preimage of `ι(G_{M'}) ⊆ G_M`
  (`CurvesJacobian.Cusp.coverι`) under `Π_U ↠ G_M`; so `Π_{U_{M'}}` is open of index
  `[G_M : G_{M'}]` in `Π_U` (`CurvesJacobian.Cusp.relIndex_range_bcPiHom`).

This compares the `Π_U` of [AbsTopII] Cor 3.7 (b) (over the field of definition `M` of `V`) with
the base-changed one of Cor 3.7 (a) (over the field `M'` of the Belyi data).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section BaseChangePi

variable {M : Type u} [Field M] [NumberField M] (M' : Type u) [Field M'] [NumberField M']
  [Algebra M M'] [FiniteDimensional M M'] (C : HypCurve M)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

/-- `Spec Γ(U_{M'}) ⟶ Spec Γ(U)`. -/
abbrev bcSpec : Spec Γ((C.bc M').Xbar, (C.bc M').U) ⟶ Spec Γ(C.Xbar, C.U) :=
  Spec.map ((bcπ M M' C.Xbar).appLE C.U (C.bc M').U le_rfl)

omit [NumberField M'] in
include hc in
/-- **The square `Spec Γ(U_{M'}) ⟶ Spec Γ(U)` over `Spec M' ⟶ Spec M` is cartesian.** -/
lemma isPullback_bcSpec :
    IsPullback (bcSpec M' C) (sKU (C.bc M')) (sKU C) (specAlgebraMap M M') :=
  letI : (C.bc M').Xbar.Over (Spec (.of M')) := (C.bc M').over
  isPullback_specΓ (M := M) (M' := M') (bcπ M M' C.Xbar) (isPullback_bcπ M M' C.Xbar) rfl
    (isAffineOpen_U C hc)

omit [NumberField M'] in
include hc in
lemma isFiniteEtale_bcSpec : IsFiniteEtale (bcSpec M' C) := by
  haveI : IsFiniteEtale (specAlgebraMap M M') := isFiniteEtale_specAlgebraMap (M := M) (M' := M')
  exact MorphismProperty.of_isPullback (P := @IsFiniteEtale) (isPullback_bcSpec M' C hc).flip
    inferInstance

omit [NumberField M'] in
include hc in
lemma bcSpec_sKU :
    bcSpec M' C ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap M' Γ((C.bc M').Xbar, (C.bc M').U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap M M')) :=
  (isPullback_bcSpec M' C hc).w

variable (Ω : Type u) [Field Ω] [Algebra M Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic M Ω]
  [CharZero Ω] [Algebra M' Ω] [IsScalarTower M M' Ω] [Algebra.IsAlgebraic M' Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [NumberField M] [NumberField M'] [FiniteDimensional M M'] [IsAlgClosed Ω] [CharZero Ω] in
/-- Ranges of `π₁ᵉᵗ(p)` at equal base points agree. -/
lemma range_fundamentalGroupMap_congr_pt {V X : Scheme.{u}} (p : V ⟶ X)
    {v v' : Spec (.of Ω) ⟶ V} {η : Spec (.of Ω) ⟶ X} (e : v = v') (h : v ≫ p = η)
    (h' : v' ≫ p = η) :
    (fundamentalGroupMap p h).toMonoidHom.range = (fundamentalGroupMap p h').toMonoidHom.range := by
  subst e
  rfl

/-- **`Π_{U_{M'}} ↪ Π_U` has image `pr⁻¹(ι(G_{M'}))`.** -/
theorem range_bcPiHom :
    haveI := isFiniteEtale_bcSpec M' C hc
    Set.range (coverPiHom Ω C hc (C.bc M') (HypCurve.bc_cusp M' C hc) (bcSpec M' C)) =
      projGk Ω C hc ⁻¹' Set.range (coverι Ω C hc (C.bc M') (HypCurve.bc_cusp M' C hc)
        (bcSpec M' C) (bcSpec_sKU M' C hc)) := by
  set hc' := HypCurve.bc_cusp M' C hc
  haveI := isFiniteEtale_bcSpec M' C hc
  haveI : IsFiniteEtale (specAlgebraMap M M') := isFiniteEtale_specAlgebraMap (M := M) (M' := M')
  haveI := isIntegral_specSections C hc
  haveI := isIntegral_specSections (C.bc M') hc'
  set F := bcSpec M' C
  set x' := basePoint Ω (C.bc M') hc' ≫ baseChangeSpec M' Ω Γ((C.bc M').Xbar, (C.bc M').U)
  set sM := Spec.map (CommRingCat.ofHom (algebraMap M Ω))
  have hy : (x' ≫ F) ≫ sKU C = sM := coverPiHom_base_spec Ω C (C.bc M') hc' F
    (bcSpec_sKU M' C hc)
  have hv : (x' ≫ sKU (C.bc M')) ≫ specAlgebraMap M M' = sM := by
    rw [basePoint_spec₂]
    exact specMap_algebraMap_tower M M' Ω
  have hsurj : Function.Surjective (fundamentalGroupMap (sKU C) hy) :=
    fundamentalGroupMap_structure_surjective Ω C hc hy
  have key := range_fundamentalGroupMap_of_isPullback (isPullback_bcSpec M' C hc).flip hy hsurj
    (rfl : x' ≫ F = _) hv
  have hgal : (fundamentalGroupMap (specAlgebraMap M M') hv).toMonoidHom.range =
      (galoisMap M M' Ω).toMonoidHom.range :=
    range_fundamentalGroupMap_congr_pt Ω (specAlgebraMap M M') (basePoint_spec₂ Ω (C.bc M') hc')
      hv (specMap_algebraMap_tower M M' Ω)
  rw [hgal] at key
  set β := coverFib Ω C hc (C.bc M') hc' F
  set g := coverG Ω C hc (C.bc M') hc' F (bcSpec_sKU M' C hc)
  have hB : ∀ τ, projGk Ω C hc (autContinuousMulEquivOfIso β τ) =
      autContinuousMulEquivOfIso g (fundamentalGroupMap (sKU C) hy τ) := fun τ ↦ by
    change fundamentalGroupMap (sKU C) (basePoint_spec₂ Ω C hc) _ = _
    exact fundamentalGroupMap_autContinuousMulEquivOfIso (sKU C) hy (basePoint_spec₂ Ω C hc) β τ
  ext σ
  obtain ⟨τ, rfl⟩ := (autContinuousMulEquivOfIso β).surjective σ
  change _ ↔ projGk Ω C hc _ ∈ Set.range (coverι Ω C hc (C.bc M') hc' F (bcSpec_sKU M' C hc))
  rw [hB]
  constructor
  · rintro ⟨γ, hγ⟩
    have hγ' : fundamentalGroupMap F rfl γ = τ := (autContinuousMulEquivOfIso β).injective hγ
    subst hγ'
    have hmem : fundamentalGroupMap F rfl γ ∈
        (fundamentalGroupMap F (rfl : x' ≫ F = _)).toMonoidHom.range := ⟨γ, rfl⟩
    rw [key] at hmem
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, congrArg (autContinuousMulEquivOfIso g) hs⟩
  · rintro ⟨s, hs⟩
    have hmem : τ ∈ (fundamentalGroupMap F (rfl : x' ≫ F = _)).toMonoidHom.range := by
      rw [key]
      exact ⟨s, (autContinuousMulEquivOfIso g).injective hs⟩
    obtain ⟨γ, rfl⟩ := hmem
    exact ⟨γ, rfl⟩

/-- **`[Π_U : Π_{U_{M'}}] = [G_M : G_{M'}]`**, the number of geometric points of `Spec M'` over
`Spec Ω ⟶ Spec M`. -/
theorem index_range_bcPiHom :
    haveI := isFiniteEtale_bcSpec M' C hc
    haveI : IsFiniteEtale (specAlgebraMap M M') := isFiniteEtale_specAlgebraMap (M := M) (M' := M')
    (coverPiHom Ω C hc (C.bc M') (HypCurve.bc_cusp M' C hc)
      (bcSpec M' C)).toMonoidHom.range.index =
      Nat.card ((fiber (Spec.map (CommRingCat.ofHom (algebraMap M Ω)))).obj
        (coverObj (specAlgebraMap M M'))) := by
  haveI := isFiniteEtale_bcSpec M' C hc
  haveI : IsFiniteEtale (specAlgebraMap M M') := isFiniteEtale_specAlgebraMap (M := M) (M' := M')
  set hc' := HypCurve.bc_cusp M' C hc
  have e : (coverPiHom Ω C hc (C.bc M') hc' (bcSpec M' C)).toMonoidHom.range =
      (coverι Ω C hc (C.bc M') hc' (bcSpec M' C)
        (bcSpec_sKU M' C hc)).toMonoidHom.range.comap (projGk Ω C hc).toMonoidHom := by
    ext σ
    exact Set.ext_iff.1 (range_bcPiHom M' C hc Ω) σ
  have e2 : (coverι Ω C hc (C.bc M') hc' (bcSpec M' C) (bcSpec_sKU M' C hc)).toMonoidHom.range =
      (galoisMap M M' Ω).toMonoidHom.range.map
        (autContinuousMulEquivOfIso (coverG Ω C hc (C.bc M') hc' (bcSpec M' C)
          (bcSpec_sKU M' C hc))).toMulEquiv.toMonoidHom := by
    rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
    rfl
  rw [e]
  refine (Subgroup.index_comap_of_surjective _ (projGk_surjective Ω C hc)).trans ?_
  rw [e2, Subgroup.index_map_of_bijective (autContinuousMulEquivOfIso _).bijective]
  exact index_range_fundamentalGroupMap (specAlgebraMap M M') (specMap_algebraMap_tower M M' Ω)

end BaseChangePi

end CurvesJacobian.Cusp
