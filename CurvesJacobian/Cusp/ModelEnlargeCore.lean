/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelCover

/-!
# Shrinking a geometric model to a normal subgroup inside a given open subgroup (MR8 (Q-a))

For a geometric model `D` of a chain object `A` and an open subgroup `P' ⊆ A`, the normal core
`T` (in `A`) of `ι(Π_Y) ∩ P'` is open and normal in `A`, and contained in `ι(Π_Y)`; its preimage
`O ⊆ Π_Y` is open and normal, so `GeomModel.ofSub` gives a model `D₂` with image `T`
(`CurvesJacobian.Cusp.GeomModel.exists_model_normal_le`). In particular `ι₂(Π_{Y₂}) ⊆ P'` and
`ι₂(Π_{Y₂})` is normalised by all of `A`, which is the input of the enlargement step of option
(Q).
-/

open Belyi Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp.GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A)

/-- **A model with image a normal subgroup of `A` inside a given open subgroup.** -/
theorem exists_model_normal_le (P' : Subgroup A.grp) (hP' : IsOpen (P' : Set A.grp)) :
    ∃ (D₂ : GeomModel Ω CX hcX A) (T : Subgroup A.grp), T.Normal ∧ IsOpen (T : Set A.grp) ∧
      Set.range D₂.ι = T ∧ T ≤ P' ∧ T ≤ (D.ι : D.Pi →* A.grp).range := by
  set H : Subgroup A.grp := (D.ι : D.Pi →* A.grp).range ⊓ P'
  have hHo : IsOpen (H : Set A.grp) := IsOpen.inter D.isOpen_rangeι hP'
  set T := H.normalCore
  have hTo : IsOpen (T : Set A.grp) := isOpen_normalCore hHo
  have hTH : T ≤ H := Subgroup.normalCore_le H
  let O : Subgroup D.Pi := T.comap (D.ι : D.Pi →* A.grp)
  have hOo : IsOpen (O : Set D.Pi) := hTo.preimage D.ι.continuous
  haveI : O.Normal := Subgroup.Normal.comap inferInstance _
  have himg : D.ι '' (O : Set D.Pi) = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, hy⟩ := (hTH hx).1
      exact ⟨y, by change D.ι y ∈ T; rw [show D.ι y = x from hy]; exact hx, hy⟩
  have hN : A.Delta ≤ Subgroup.normalizer (D.ι '' (O : Set D.Pi)) := by
    rw [himg]
    exact le_normalizer_of_normal T rfl _
  refine ⟨D.ofSub O hOo hN, T, inferInstance, hTo, (D.range_ofSub O hOo hN).trans himg,
    fun x hx ↦ (hTH hx).2, fun x hx ↦ (hTH hx).1⟩

end CurvesJacobian.Cusp.GeomModel
