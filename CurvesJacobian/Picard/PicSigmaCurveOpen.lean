/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicSigmaCurve

/-!
# `Γ(U, 𝒪_T) = Γ(X_U, 𝒪_{X_T})` for every open `U` of a `k`-scheme `T`

Let `X` be a curve over a perfect field `k` and `T` any `k`-scheme with projection
`p : X_T ⟶ T`. We show that `p^♯ : Γ(T, U) ⟶ Γ(X_T, p⁻¹ U)` is bijective for every open
`U ⊆ T` (`IsCurveOver.bijective_app_pullback_snd`), i.e. `𝒪_T ≅ p_* 𝒪_{X_T}`. This extends
`IsCurveOver.bijective_app_top_pullback_snd` (the case `U = ⊤`) by the same gluing argument over
affine opens contained in `U`. This is the hypothesis `𝒪_T ≅ f_{T,*}𝒪_{X_T}` of Stacks,
Lemma 44.4.3 (Tag 0B9N), verified for curves as in the proof of Lemma 44.6.1 (Tag 0B9U).
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Belyi

universe u

noncomputable section

namespace CurvesJacobian

open ModulesGlue

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsCurveOver k X] [PerfectField k]

local notation "Sk" => Spec (CommRingCat.of k)

/-- `Γ(U, 𝒪_T) ≅ Γ(X_U, 𝒪_{X_T})` for every `k`-scheme `T` and open `U ⊆ T`: injectivity. -/
theorem IsCurveOver.injective_app_pullback_snd {T : Scheme.{u}} (g : T ⟶ Sk) (U : T.Opens) :
    Function.Injective ((pullback.snd (X ↘ Sk) g).app U) := by
  set p := pullback.snd (X ↘ Sk) g
  intro v w hvw
  refine CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf (V := U) v w fun t ht ↦ ?_
  obtain ⟨A, hA, htA, hAU⟩ := exists_isAffineOpen_mem_and_subset (x := t) ht
  haveI := IsCurveOver.isIso_app_pullback_snd k X g A hA.isCompact hA.isQuasiSeparated
  refine ⟨A, hAU, htA, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (p.app A)).1
  change p.app A (rr hAU v) = p.app A (rr hAU w)
  rw [app_rr, app_rr, hvw]

/-- `Γ(U, 𝒪_T) ≅ Γ(X_U, 𝒪_{X_T})` for every `k`-scheme `T` and open `U ⊆ T`: surjectivity. -/
theorem IsCurveOver.surjective_app_pullback_snd {T : Scheme.{u}} (g : T ⟶ Sk) (U : T.Opens) :
    Function.Surjective ((pullback.snd (X ↘ Sk) g).app U) := by
  set p := pullback.snd (X ↘ Sk) g
  intro c
  choose W hW htW hWU using fun t : U ↦
    exists_isAffineOpen_mem_and_subset (x := t.1) t.2
  have hiso : ∀ t, IsIso (p.app (W t)) := fun t ↦
    IsCurveOver.isIso_app_pullback_snd k X g (W t) (hW t).isCompact (hW t).isQuasiSeparated
  have hbij : ∀ t, Function.Bijective (p.app (W t)) := fun t ↦
    haveI := hiso t; ConcreteCategory.bijective_of_isIso _
  choose v hv using fun t ↦ (hbij t).2 (rr ((Opens.map p.base).monotone (hWU t)) c)
  -- compatibility on overlaps, checked on affine opens
  have hcomp : ∀ t t', rr (inf_le_left : W t ⊓ W t' ≤ W t) (v t) =
      rr (inf_le_right : W t ⊓ W t' ≤ W t') (v t') := by
    intro t t'
    refine CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf _ _ fun x hx ↦ ?_
    obtain ⟨A, hA, hxA, hAle⟩ := exists_isAffineOpen_mem_and_subset hx
    haveI := IsCurveOver.isIso_app_pullback_snd k X g A hA.isCompact hA.isQuasiSeparated
    refine ⟨A, hAle, hxA, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (p.app A)).1
    change p.app A (rr hAle (rr _ (v t))) = p.app A (rr hAle (rr _ (v t')))
    rw [rr_rr, rr_rr, app_rr, app_rr, hv, hv, rr_rr, rr_rr]
  obtain ⟨w, hw⟩ := CurvesJacobian.sheaf_exists_glue T.sheaf (V := U) W hWU htW v hcomp
  refine ⟨w, CurvesJacobian.sheaf_eq_of_locally_eq (pullback (X ↘ Sk) g).sheaf
    (V := p ⁻¹ᵁ U) _ _ fun y hy ↦ ⟨p ⁻¹ᵁ W ⟨p.base y, hy⟩,
      (Opens.map p.base).monotone (hWU _), htW ⟨p.base y, hy⟩, ?_⟩⟩
  change rr _ (p.app U w) = rr _ c
  rw [← app_rr (h := hWU ⟨p.base y, hy⟩), ← hv ⟨p.base y, hy⟩]
  exact congrArg (p.app _) (hw ⟨p.base y, hy⟩)

/-- `Γ(U, 𝒪_T) ≅ Γ(X_U, 𝒪_{X_T})` for every `k`-scheme `T` and open `U ⊆ T`. -/
theorem IsCurveOver.bijective_app_pullback_snd {T : Scheme.{u}} (g : T ⟶ Sk) (U : T.Opens) :
    Function.Bijective ((pullback.snd (X ↘ Sk) g).app U) :=
  ⟨IsCurveOver.injective_app_pullback_snd k X g U,
    IsCurveOver.surjective_app_pullback_snd k X g U⟩

/-- `p^♯ : 𝒪_T ⟶ p_* 𝒪_{X_T}` is an isomorphism on every open `U ⊆ T`. -/
theorem IsCurveOver.isIso_app_pullback_snd' {T : Scheme.{u}} (g : T ⟶ Sk) (U : T.Opens) :
    IsIso ((pullback.snd (X ↘ Sk) g).app U) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (IsCurveOver.bijective_app_pullback_snd k X g U)

end CurvesJacobian
