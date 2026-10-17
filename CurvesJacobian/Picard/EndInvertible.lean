/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ModulesGlue

/-!
# Endomorphisms of invertible sheaves are scalars

This file is generic. For an invertible sheaf `L` on a scheme `Y`, every endomorphism
`θ : L ⟶ L` is multiplication by a global function `c ∈ Γ(Y, 𝒪_Y)`
(`exists_eq_smul_of_isInvertible`); i.e. `End(L) = Γ(Y, 𝒪_Y)` (Stacks, Tag 01CR for the
locally free case, here proved directly from local bases).

This is the input for the rigidity of the Picard functor `Pic_{X/S,σ}`: an automorphism of an
invertible sheaf on `X_T` is a unit of `Γ(X_T, 𝒪)`, which is pulled back from `T` when
`𝒪_T ≅ f_{T,*}𝒪_{X_T}`, hence is determined by its restriction along a section `σ_T`
(compare the proof of Stacks, Lemma 44.4.3, Tag 0B9N).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme

variable {Y : Scheme.{u}}

lemma app_rs {L L' : Y.Modules} (θ : L ⟶ L') {U W : Y.Opens} (h : W ≤ U) (m : Γ(L, U)) :
    θ.app W (rs L h m) = rs L' h (θ.app U m) :=
  Scheme.PresheafOfModules.app_res ((Scheme.Modules.toPresheafOfModules Y).map θ) h m

lemma rr_mul {U W : Y.Opens} (h : W ≤ U) (a b : Γ(Y, U)) : rr h (a * b) = rr h a * rr h b :=
  map_mul _ _ _

lemma bijective_smul_of_isBasisOn {L : Y.Modules} {U : Y.Opens} {e : Γ(L, U)}
    (he : L.IsBasisOn U e) : Function.Bijective (fun r : Γ(Y, U) ↦ r • e) := by
  have : (fun r : Γ(Y, U) ↦ r • e) = (fun r ↦ r • Scheme.PresheafOfModules.res
      ((Scheme.Modules.toPresheafOfModules Y).obj L) (le_refl U) e) := by
    funext r
    exact congrArg (r • ·) (rs_self L _ e).symm
  rw [this]
  exact he (le_refl U)

/-- Coordinates with respect to a basis. -/
lemma exists_smul_eq_of_isBasisOn {L : Y.Modules} {U : Y.Opens} {e : Γ(L, U)}
    (he : L.IsBasisOn U e) (m : Γ(L, U)) : ∃ c : Γ(Y, U), c • e = m :=
  (bijective_smul_of_isBasisOn he).2 m

lemma smul_left_injective_of_isBasisOn {L : Y.Modules} {U : Y.Opens} {e : Γ(L, U)}
    (he : L.IsBasisOn U e) {c c' : Γ(Y, U)} (h : c • e = c' • e) : c = c' :=
  (bijective_smul_of_isBasisOn he).1 h

lemma isBasisOn_rs {L : Y.Modules} {U W : Y.Opens} {e : Γ(L, U)} (he : L.IsBasisOn U e)
    (h : W ≤ U) : L.IsBasisOn W (rs L h e) :=
  Scheme.PresheafOfModules.IsBasisOn.restrict he h

/-- The local scalar of an endomorphism on a basis open. -/
lemma exists_local_scalar {L : Y.Modules} (θ : L ⟶ L) {U : Y.Opens} {e : Γ(L, U)}
    (he : L.IsBasisOn U e) : ∃ c : Γ(Y, U), ∀ (W : Y.Opens) (h : W ≤ U) (m : Γ(L, W)),
      θ.app W m = rr h c • m := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_isBasisOn he (θ.app U e)
  refine ⟨c, fun W h m ↦ ?_⟩
  obtain ⟨k, rfl⟩ := exists_smul_eq_of_isBasisOn (isBasisOn_rs he h) m
  rw [Scheme.Modules.Hom.app_smul, app_rs, ← hc, rs_smul, smul_smul, smul_smul, mul_comm]

/-- **Endomorphisms of an invertible sheaf are scalars**: every `θ : L ⟶ L` is multiplication by
a global function. -/
theorem exists_eq_smul_of_isInvertible (L : Y.Modules) [L.IsInvertible] (θ : L ⟶ L) :
    ∃ c : Γ(Y, ⊤), ∀ (U : Y.Opens) (m : Γ(L, U)), θ.app U m = rr (le_top : U ≤ ⊤) c • m := by
  choose U e hyU he using fun y : Y ↦ Scheme.Modules.IsInvertible.exists_basis (L := L) y
  choose c hc using fun y : Y ↦ exists_local_scalar θ (he y)
  -- the local scalars agree on overlaps
  have hcomp : ∀ y z : Y, rr (inf_le_left : U y ⊓ U z ≤ U y) (c y) =
      rr (inf_le_right : U y ⊓ U z ≤ U z) (c z) := by
    intro y z
    have hb := isBasisOn_rs (he y) (inf_le_left : U y ⊓ U z ≤ U y)
    have h₁ := hc y (U y ⊓ U z) inf_le_left (rs L (inf_le_left : U y ⊓ U z ≤ U y) (e y))
    have h₂ := hc z (U y ⊓ U z) inf_le_right (rs L (inf_le_left : U y ⊓ U z ≤ U y) (e y))
    exact smul_left_injective_of_isBasisOn hb (h₁.symm.trans h₂)
  obtain ⟨g, hg⟩ := CurvesJacobian.sheaf_exists_glue Y.sheaf (V := ⊤) (fun y ↦ U y.1)
    (fun _ ↦ le_top) (fun y ↦ hyU y.1) (fun y ↦ c y.1) (fun y z ↦ hcomp y.1 z.1)
  refine ⟨g, fun W m ↦ ?_⟩
  refine CurvesJacobian.sheaf_eq_of_locally_eq ⟨L.presheaf, L.isSheaf⟩ _ _ fun y hy ↦
    ⟨W ⊓ U y, inf_le_left, ⟨hy, hyU y⟩, ?_⟩
  change rs L inf_le_left (θ.app W m) = rs L inf_le_left (rr (le_top : W ≤ ⊤) g • m)
  rw [← app_rs, hc y _ inf_le_right, rs_smul, rr_rr]
  congr 1
  rw [← rr_rr (le_top : U y ≤ ⊤) inf_le_right]
  exact (congrArg (rr inf_le_right) (hg ⟨y, trivial⟩)).symm

end CurvesJacobian.ModulesGlue
