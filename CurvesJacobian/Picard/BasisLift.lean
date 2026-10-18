/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TwoChartTwist
import CurvesJacobian.Picard.QcohBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Lifting bases of invertible sheaves along thickenings

This file is generic.

* `BasisLift.isBasisOn_of_locally`: being a basis of a sheaf of modules on `O` is local on `O`.
* `BasisLift.isBasisOn_of_pullback`: let `i : Y₀ ⟶ Y` be surjective and `L` invertible on `Y`.
  A section `b ∈ Γ(L, O)` whose pullback `i^* b` is a basis of `i^* L` on `i⁻¹ O` is a basis
  of `L` on `O` (locally `b = r e` for a basis `e`, and `i^♯ r` is a unit, so `r` is a unit at
  every point of `O`: Nakayama for the stalks of an invertible sheaf).
* `BasisLift.exists_pullbackRes_eq`: if `i` is a closed immersion and `O` is affine, every
  section of `i^* L` over `i⁻¹ O` lifts to a section of `L` over `O` (sections of the pullback
  are the base change, `Scheme.Modules.isBaseChange_pullbackRes`).
* `BasisLift.exists_isBasisOn_top`: a trivial invertible sheaf has a global basis.

Together: an invertible sheaf on `Y` whose pullback to a thickening `Y₀` is trivial has a basis
on every affine open (`BasisLift.exists_isBasisOn_of_mk_eq_zero`).
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.BasisLift

open Scheme Scheme.Modules ModulesGlue

variable {Y : Scheme.{u}}

/-- **Being a basis is local.** -/
theorem isBasisOn_of_locally {L : Y.Modules} {O : Y.Opens} {b : Γ(L, O)}
    (H : ∀ y ∈ O, ∃ (O' : Y.Opens) (h : O' ≤ O), y ∈ O' ∧ L.IsBasisOn O' (rs L h b)) :
    L.IsBasisOn O b := by
  choose O' hO' hy hb using H
  intro W hW
  change Function.Bijective (fun r : Γ(Y, W) ↦ r • rs L hW b)
  -- local data on `W ⊓ O' y`
  have hloc : ∀ (y : W), L.IsBasisOn (W ⊓ O' y.1 (hW y.2)) (rs L (inf_le_left.trans hW) b) := by
    intro y
    have := isBasisOn_rs (hb y.1 (hW y.2)) (inf_le_right : W ⊓ O' y.1 (hW y.2) ≤ _)
    rwa [rs_rs] at this
  let YS : TopCat.Sheaf CommRingCat.{u} Y := Y.sheaf
  let LS : TopCat.Sheaf Ab.{u} Y := ⟨L.presheaf, L.isSheaf⟩
  constructor
  · intro r r' e
    change r • rs L hW b = r' • rs L hW b at e
    refine sheaf_eq_of_locally_eq YS r r' fun y hyW ↦ ?_
    refine ⟨W ⊓ O' y (hW hyW), inf_le_left, ⟨hyW, hy y (hW hyW)⟩, ?_⟩
    have e' := congrArg (rs L (inf_le_left : W ⊓ O' y (hW hyW) ≤ W)) e
    rw [rs_smul, rs_smul, rs_rs] at e'
    exact smul_left_injective_of_isBasisOn (hloc ⟨y, hyW⟩) e'
  · intro m
    have hc : ∀ y : W, ∃ c : Γ(Y, W ⊓ O' y.1 (hW y.2)),
        c • rs L (inf_le_left.trans hW) b = rs L inf_le_left m :=
      fun y ↦ exists_smul_eq_of_isBasisOn (hloc y) _
    choose c hc using hc
    obtain ⟨r, hr⟩ := sheaf_exists_glue YS (fun y : W ↦ W ⊓ O' y.1 (hW y.2))
      (fun _ ↦ inf_le_left) (fun y ↦ ⟨y.2, hy y.1 (hW y.2)⟩) c (by
        intro y z
        have hle : (W ⊓ O' y.1 (hW y.2)) ⊓ (W ⊓ O' z.1 (hW z.2)) ≤ W ⊓ O' y.1 (hW y.2) :=
          inf_le_left
        have hb' : L.IsBasisOn _ (rs L (hle.trans (inf_le_left.trans hW)) b) := by
          have := isBasisOn_rs (hloc y) hle
          rwa [rs_rs] at this
        refine smul_left_injective_of_isBasisOn hb' ?_
        have e1 := congrArg (rs L hle) (hc y)
        have e2 := congrArg (rs L (inf_le_right : (W ⊓ O' y.1 (hW y.2)) ⊓
          (W ⊓ O' z.1 (hW z.2)) ≤ W ⊓ O' z.1 (hW z.2))) (hc z)
        rw [rs_smul, rs_rs, rs_rs] at e1 e2
        change rr _ (c y) • _ = rr _ (c z) • _
        rw [e1, e2])
    have key : ∀ r' : Γ(Y, W), (∀ y : W, rr (inf_le_left : W ⊓ O' y.1 (hW y.2) ≤ W) r' = c y) →
        r' • rs L hW b = m := by
      intro r' hr'
      refine sheaf_eq_of_locally_eq LS _ _ fun y hyW ↦ ?_
      refine ⟨W ⊓ O' y (hW hyW), inf_le_left, ⟨hyW, hy y (hW hyW)⟩, ?_⟩
      change rs L inf_le_left (r' • rs L hW b) = rs L inf_le_left m
      rw [rs_smul, rs_rs, ← hc ⟨y, hyW⟩, hr' ⟨y, hyW⟩]
    exact ⟨r, key r hr⟩

/-- Two bases differ by a unit. -/
lemma isUnit_of_isBasisOn_smul' {L : Y.Modules} {O : Y.Opens} {e : Γ(L, O)} {c : Γ(Y, O)}
    (he : L.IsBasisOn O e) (hce : L.IsBasisOn O (c • e)) : IsUnit c :=
  TwoChart.isUnit_of_isBasisOn_smul he hce

/-- A function whose pullback along a surjective morphism is a unit is a unit. -/
lemma isUnit_of_isUnit_app {Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (hi : Function.Surjective i.base)
    {O : Y.Opens} (r : Γ(Y, O)) (hr : IsUnit (i.app O r)) : IsUnit r := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ O r fun z hz ↦ ?_
  obtain ⟨z₀, rfl⟩ := hi z
  have h1 : z₀ ∈ Y₀.basicOpen (i.app O r) := by
    rw [Y₀.basicOpen_of_isUnit hr]
    exact hz
  rw [← Scheme.preimage_basicOpen] at h1
  exact (Y.mem_basicOpen r _ hz).mp h1

variable {Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)

/-- **Bases are detected after a surjective pullback.** -/
theorem isBasisOn_of_pullback (hi : Function.Surjective i.base) {L : Y.Modules} [L.IsInvertible]
    {O : Y.Opens} {b : Γ(L, O)}
    (hb : ((pullback i).obj L).IsBasisOn (i ⁻¹ᵁ O) (pullbackSection i b)) :
    L.IsBasisOn O b := by
  refine isBasisOn_of_locally fun y hyO ↦ ?_
  obtain ⟨O₁, e, hy₁, he⟩ := IsInvertible.exists_basis (L := L) y
  refine ⟨O ⊓ O₁, inf_le_left, ⟨hyO, hy₁⟩, ?_⟩
  have he' := isBasisOn_rs he (inf_le_right : O ⊓ O₁ ≤ O₁)
  obtain ⟨r, hr⟩ := exists_smul_eq_of_isBasisOn he' (rs L inf_le_left b)
  rw [← hr]
  refine isBasisOn_smul_of_isUnit he' (isUnit_of_isUnit_app i hi r ?_)
  have h1 := isBasisOn_pullbackSection i (O ⊓ O₁) he'
  have h2 := isBasisOn_rs hb (i.preimage_mono (inf_le_left : O ⊓ O₁ ≤ O))
  have e2 : rs ((pullback i).obj L) (i.preimage_mono (inf_le_left : O ⊓ O₁ ≤ O))
      (pullbackSection i b) = (i.app (O ⊓ O₁) r) •
        pullbackSection i (rs L (inf_le_right : O ⊓ O₁ ≤ O₁) e) := by
    refine (pullbackSection_res i (inf_le_left : O ⊓ O₁ ≤ O) b).symm.trans ?_
    change pullbackSection i (rs L inf_le_left b) = _
    rw [← hr]
    exact pullbackSection_smul i r _
  rw [e2] at h2
  exact isUnit_of_isBasisOn_smul' h1 h2

/-- **Sections of a pullback along a closed immersion lift over affines.** -/
theorem exists_pullbackRes_eq [IsClosedImmersion i] {L : Y.Modules} [L.IsInvertible]
    {O : Y.Opens} (hO : IsAffineOpen O) (m : Γ((pullback i).obj L, i ⁻¹ᵁ O)) :
    ∃ b : Γ(L, O), pullbackSection i b = m := by
  have hO' : IsAffineOpen (i ⁻¹ᵁ O) := hO.preimage i
  have hs : Function.Surjective (i.app O) := i.app_surjective O hO
  letI := (i.appLE O (i ⁻¹ᵁ O) le_rfl).hom.toAlgebra
  letI : Module Γ(Y, O) Γ((pullback i).obj L, i ⁻¹ᵁ O) :=
    Module.compHom _ (algebraMap Γ(Y, O) Γ(Y₀, i ⁻¹ᵁ O))
  haveI : IsScalarTower Γ(Y, O) Γ(Y₀, i ⁻¹ᵁ O) Γ((pullback i).obj L, i ⁻¹ᵁ O) :=
    IsScalarTower.of_compHom _ _ _
  have H := isBaseChange_pullbackRes i L (le_refl (i ⁻¹ᵁ O)) hO hO'
  have key : ∀ n, n ∈ Set.range (pullbackRes i L (le_refl (i ⁻¹ᵁ O))) := by
    intro n
    refine H.inductionOn n _ ⟨0, map_zero _⟩ (fun b ↦ ⟨b, rfl⟩) ?_ ?_
    · rintro s _ ⟨b, rfl⟩
      obtain ⟨r, rfl⟩ := hs s
      refine ⟨r • b, ?_⟩
      rw [pullbackRes_smul]
      congr 1
      exact (Scheme.Hom.app_eq_appLE (f := i) (U := O) ▸ rfl)
    · rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
      exact ⟨b + b', map_add _ _ _⟩
  obtain ⟨b, hb⟩ := key m
  refine ⟨b, ?_⟩
  rw [← hb, pullbackRes_apply]
  exact (rs_self _ _ _).symm

/-- A trivial invertible sheaf has a global basis. -/
lemma exists_isBasisOn_top {M : Y.Modules} [M.IsInvertible] (h : Pic.mk M = 0) :
    ∃ s : Γ(M, ⊤), M.IsBasisOn ⊤ s := by
  rw [Pic.mk_eq_zero_iff] at h
  obtain ⟨e⟩ := h
  let s : Γ((𝟙_ Y.Modules), ⊤) := (Scheme.Modules.toSheafify (𝟙_ Y.PresheafOfModules)).app (op ⊤)
    (1 : Y.ringCatSheaf.obj.obj (op ⊤))
  have hs : (𝟙_ Y.Modules).IsBasisOn ⊤ s := Scheme.Modules.isBasisOn_sheafify
    (𝟙_ Y.PresheafOfModules) (Scheme.PresheafOfModules.isBasisOn_unit ⊤)
  exact ⟨_, hs.of_iso e.symm⟩

/-- **Bases on affines of an invertible sheaf which is trivial on a thickening.** Let
`i : Y₀ ⟶ Y` be a surjective closed immersion and `L` invertible on `Y` with `i^* L` trivial.
Then `L` has a basis on every affine open `O`, lifting the restriction of a given global basis
of `i^* L`. -/
theorem exists_isBasisOn_lift [IsClosedImmersion i] (hi : Function.Surjective i.base)
    {L : Y.Modules} [L.IsInvertible] {g : Γ((pullback i).obj L, ⊤)}
    (hg : ((pullback i).obj L).IsBasisOn ⊤ g) {O : Y.Opens} (hO : IsAffineOpen O) :
    ∃ b : Γ(L, O), L.IsBasisOn O b ∧
      pullbackSection i b = rs ((pullback i).obj L) le_top g := by
  obtain ⟨b, hb⟩ := exists_pullbackRes_eq i hO (rs _ le_top g)
  refine ⟨b, isBasisOn_of_pullback i hi ?_, hb⟩
  rw [hb]
  exact isBasisOn_rs hg le_top

end CurvesJacobian.BasisLift
