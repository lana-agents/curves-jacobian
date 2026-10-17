/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicRigid
import CurvesJacobian.Picard.PicSigma
import CurvesJacobian.Picard.CurveCover

/-!
# Rigidity for curves: `Γ(T, 𝒪_T) = Γ(X_T, 𝒪_{X_T})`

Let `X` be a curve over a perfect field `k` and `T` any `k`-scheme. We show that
`f_T^♯ : Γ(T, 𝒪_T) ⟶ Γ(X_T, 𝒪_{X_T})` is bijective (`IsCurveOver.bijective_app_top_pullback_snd`),
extending `IsCurveOver.isIso_app_pullback_snd` (quasi-compact quasi-separated opens) to all of
`T` by gluing over an affine cover. This is the hypothesis `𝒪_T ≅ f_{T,*}𝒪_{X_T}` of Stacks,
Lemma 44.4.3 (Tag 0B9N), verified for curves as in the proof of Lemma 44.6.1 (Tag 0B9U).

Consequently, for a rational point `σ`, `X_T` is rigid along `σ_T` (`isRigidAlong_secT`): an
automorphism of an invertible sheaf on `X_T` which is the identity along `σ_T` is the identity
(`CurvesJacobian.ModulesGlue.eq_id_of_pullback_map_eq_id`). This is the rigidity input for the
Zariski sheaf property of `Pic_{X/k,σ}`.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Belyi

universe u

noncomputable section

namespace CurvesJacobian

open ModulesGlue

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsCurveOver k X] [PerfectField k]

local notation "Sk" => Spec (CommRingCat.of k)

/-- `Γ(T, 𝒪_T) ≅ Γ(X_T, 𝒪_{X_T})` for every `k`-scheme `T`: injectivity. -/
theorem IsCurveOver.injective_app_top_pullback_snd {T : Scheme.{u}} (g : T ⟶ Sk) :
    Function.Injective ((pullback.snd (X ↘ Sk) g).app ⊤) := by
  set p := pullback.snd (X ↘ Sk) g
  intro v w hvw
  refine CurvesJacobian.sheaf_eq_of_locally_eq T.sheaf (V := ⊤) v w fun t _ ↦ ?_
  obtain ⟨A, hA, htA, -⟩ := exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
  haveI := IsCurveOver.isIso_app_pullback_snd k X g A hA.isCompact hA.isQuasiSeparated
  refine ⟨A, le_top, htA, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (p.app A)).1
  change p.app A (rr le_top v) = p.app A (rr le_top w)
  rw [app_rr, app_rr]
  change rr _ (p.app ⊤ v) = rr _ (p.app ⊤ w)
  rw [hvw]

/-- `Γ(T, 𝒪_T) ≅ Γ(X_T, 𝒪_{X_T})` for every `k`-scheme `T`: surjectivity. -/
theorem IsCurveOver.surjective_app_top_pullback_snd {T : Scheme.{u}} (g : T ⟶ Sk) :
    Function.Surjective ((pullback.snd (X ↘ Sk) g).app ⊤) := by
  set p := pullback.snd (X ↘ Sk) g
  intro c
  choose W hW htW _ using fun t : T ↦
    exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
  have hiso : ∀ t, IsIso (p.app (W t)) := fun t ↦
    IsCurveOver.isIso_app_pullback_snd k X g (W t) (hW t).isCompact (hW t).isQuasiSeparated
  have hbij : ∀ t, Function.Bijective (p.app (W t)) := fun t ↦
    haveI := hiso t; ConcreteCategory.bijective_of_isIso _
  choose v hv using fun t ↦ (hbij t).2
    (rr ((Opens.map p.base).monotone (le_top : W t ≤ ⊤)) c)
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
  obtain ⟨w, hw⟩ := CurvesJacobian.sheaf_exists_glue T.sheaf (V := ⊤) (fun t ↦ W t.1)
    (fun _ ↦ le_top) (fun t ↦ htW t.1) (fun t ↦ v t.1) (fun t t' ↦ hcomp t.1 t'.1)
  refine ⟨w, CurvesJacobian.sheaf_eq_of_locally_eq (pullback (X ↘ Sk) g).sheaf (V := ⊤) _ _
    fun y _ ↦ ⟨p ⁻¹ᵁ W (p.base y), le_top, htW (p.base y), ?_⟩⟩
  change rr _ (p.app ⊤ w) = rr _ c
  rw [← app_rr (h := (le_top : W (p.base y) ≤ ⊤)), ← hv (p.base y)]
  exact congrArg (p.app _) (hw ⟨p.base y, trivial⟩)

theorem IsCurveOver.bijective_app_top_pullback_snd {T : Scheme.{u}} (g : T ⟶ Sk) :
    Function.Bijective ((pullback.snd (X ↘ Sk) g).app ⊤) :=
  ⟨IsCurveOver.injective_app_top_pullback_snd k X g,
    IsCurveOver.surjective_app_top_pullback_snd k X g⟩

/-- For a curve `X` with a rational point `σ`, `X_T` is rigid along `σ_T` for every
`k`-scheme `T`. -/
theorem isRigidAlong_secT (σ : Sk ⟶ X) (hσ : σ ≫ (X ↘ Sk) = 𝟙 Sk) {T : Scheme.{u}}
    (g : T ⟶ Sk) : IsRigidAlong (secT (X ↘ Sk) σ hσ g) :=
  isRigidAlong_of_surjective (pullback.snd (X ↘ Sk) g) _ (secT_snd _ σ hσ g)
    (IsCurveOver.surjective_app_top_pullback_snd k X g)

end CurvesJacobian
