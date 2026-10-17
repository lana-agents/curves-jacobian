/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.EndInvertible
import CurvesJacobian.Picard.PicMap

/-!
# Rigidity of invertible sheaves along a section

This file is generic. Let `s : T ⟶ Y` be a morphism of schemes such that a global function `c`
on `Y` with `s^♯ c = 1` is `1` (`IsRigidAlong s`); this holds if `s` is a section of
`r : Y ⟶ T` with `r^♯ : Γ(T, 𝒪) ⟶ Γ(Y, 𝒪)` surjective (`isRigidAlong_of_surjective`), e.g.
for `Y = X_T`, `r = f_T`, `s = σ_T` when `𝒪_T ≅ f_{T,*}𝒪_{X_T}` (Stacks, Lemma 44.6.1,
Tag 0B9U, gives this for curves with a rational point).

Then an endomorphism `θ` of an invertible sheaf `L` on `Y` whose pullback `s^*θ` is the
identity is the identity (`eq_id_of_pullback_map_eq_id`): `θ` is multiplication by a global
function `c` (`exists_eq_smul_of_isInvertible`) and `s^♯ c = 1`. This is the rigidity used in
the proof of Stacks, Lemma 44.4.3 (Tag 0B9N): isomorphisms of invertible sheaves on `X_T`
compatible with given trivialisations along `σ_T` are unique, hence satisfy the cocycle
condition, so that rigidified invertible sheaves glue (the Zariski sheaf property of
`Pic_{X/S,σ}`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme Scheme.Modules

variable {Y T : Scheme.{u}}

lemma app_rr (s : T ⟶ Y) {U W : Y.Opens} (h : W ≤ U) (c : Γ(Y, U)) :
    s.app W (rr h c) = rr ((Opens.map s.base).map (homOfLE h)).le (s.app U c) := by
  change (Y.presheaf.map (homOfLE h).op ≫ s.app W) c = _
  rw [s.naturality]
  rfl

/-- Global functions on `Y` are detected by their pullback along `s`. -/
def IsRigidAlong (s : T ⟶ Y) : Prop :=
  ∀ c : Γ(Y, ⊤), s.app ⊤ c = 1 → c = 1

lemma isRigidAlong_of_surjective (r : Y ⟶ T) (s : T ⟶ Y) (hsr : s ≫ r = 𝟙 T)
    (hΓ : Function.Surjective (r.app ⊤)) : IsRigidAlong s := by
  intro c hc
  obtain ⟨v, rfl⟩ := hΓ c
  have hv : v = 1 := by
    have : (s ≫ r).app ⊤ v = s.app ⊤ (r.app ⊤ v) := by
      rw [Scheme.Hom.comp_app]
      rfl
    rw [hsr, Scheme.Hom.id_app] at this
    exact this.trans hc
  rw [hv, map_one]
  rfl

/-- **Rigidity**: an endomorphism of an invertible sheaf whose pullback along `s` is the
identity is the identity, if `Y` is rigid along `s`. -/
theorem eq_id_of_pullback_map_eq_id (s : T ⟶ Y) (hs : IsRigidAlong s) (L : Y.Modules)
    [L.IsInvertible] (θ : L ⟶ L) (hθ : (Modules.pullback s).map θ = 𝟙 _) : θ = 𝟙 L := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isInvertible L θ
  have hc1 : c = 1 := by
    refine hs c (CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf (V := s ⁻¹ᵁ ⊤) _ _
      fun t _ ↦ ?_)
    obtain ⟨U, e, hsU, he⟩ := IsInvertible.exists_basis (L := L) (s.base t)
    refine ⟨s ⁻¹ᵁ U, (Opens.map s.base).monotone le_top, hsU, ?_⟩
    have hpb := isBasisOn_pullbackSection s U he
    have h1 : ((Modules.pullback s).map θ).app (s ⁻¹ᵁ U) (pullbackSection s e) =
        pullbackSection s e := by
      rw [hθ]
      rfl
    rw [pullbackSection_naturality, hc] at h1
    have h2 := pullbackSection_smul s (rr (le_top : U ≤ ⊤) c) e
    change pullbackSection s (rr (le_top : U ≤ ⊤) c • e) = _ at h2
    rw [h2] at h1
    have h3 : s.app U (rr (le_top : U ≤ ⊤) c) = 1 := by
      refine smul_left_injective_of_isBasisOn hpb ?_
      rw [one_smul]
      exact h1
    rw [app_rr] at h3
    change rr _ (s.app ⊤ c) = rr _ (1 : Γ(T, s ⁻¹ᵁ ⊤))
    rw [h3, rr, map_one]
  subst hc1
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext m
  rw [hc, rr, map_one, one_smul]
  rfl

end CurvesJacobian.ModulesGlue
