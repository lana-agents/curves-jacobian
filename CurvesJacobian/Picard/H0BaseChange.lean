/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CurvePerfect
import CurvesJacobian.Picard.PicDegree

/-!
# Vanishing of `H⁰` is preserved by flat base change

* `CurvesJacobian.TwoTerm.subsingleton_H0_baseChange`: if the two-set Čech `H⁰` of `(f, g)`
  vanishes, so does that of `(B ⊗ f, B ⊗ g)` for `B` flat (the differential stays injective).
* `CurvesJacobian.Cech.subsingleton_cechModH0_lineBundleBaseChange`: the same for the Čech `H⁰`
  of an invertible sheaf and its base change along a flat `Γ(S) → Γ(T)`.
* **`CurvesJacobian.subsingleton_chartH0_bcMap`**: for a curve `C` over `k`, `T` affine over `k`
  with `Γ(T)` a field and `h : T'' ⟶ T` (`T''` affine), if `L` on `C ×_k T` has no nonzero
  chart sections then neither has its pullback to `C ×_k T''`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

namespace TwoTerm

variable {A : Type u} [CommRing A] {P Q R : Type u} [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q] [AddCommGroup R] [Module A R] (f : P →ₗ[A] R) (g : Q →ₗ[A] R)

/-- **Flat base change preserves vanishing of `H⁰`.** -/
lemma subsingleton_H0_baseChange (B : Type u) [CommRing B] [Algebra A B] [Module.Flat A B]
    (h : Subsingleton (TwoCech.H0 f g)) :
    Subsingleton (TwoCech.H0 (f.baseChange B) (g.baseChange B)) := by
  have hd : Function.Injective (TwoCech.d f g) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  have hd' : Function.Injective ((TwoCech.d f g).baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hd
  have : Subsingleton (LinearMap.ker ((TwoCech.d f g).baseChange B)) := by
    rw [LinearMap.ker_eq_bot.mpr hd']
    infer_instance
  exact (H0BaseChangeEquiv f g B).toEquiv.symm.subsingleton

end TwoTerm

namespace Cech

variable {S Y T : Scheme.{u}} [Y.Over S] [T.Over S] [IsAffine S] [IsAffine T]

local notation "pY" => pullback.fst (Y ↘ S) (T ↘ S)

/-- Vanishing of the Čech `H⁰` of an invertible sheaf is preserved by flat base change. -/
lemma subsingleton_cechModH0_lineBundleBaseChange [Module.Flat Γ(S, ⊤) Γ(T, ⊤)]
    (L : Y.Modules) [L.IsInvertible] (U V : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) (h : Subsingleton (cechModH0 S L U V)) :
    Subsingleton (cechModH0 T (lineBundleBaseChange (T := T) L) (pY ⁻¹ᵁ U) (pY ⁻¹ᵁ V)) :=
  (lineBundleH0BaseChange L U V hU hV hUV).toEquiv.subsingleton_congr.mpr
    (TwoTerm.subsingleton_H0_baseChange _ _ Γ(T, ⊤) h)

variable {Y' : Scheme.{u}} [Y'.Over S] (e : Y' ⟶ Y) [IsIso e]
  (he : e ≫ (Y ↘ S) = Y' ↘ S) (L : Y.Modules) [L.IsInvertible]

omit [T.Over S] [IsAffine T] [IsAffine S] in
include he in
/-- Vanishing of the Čech `H⁰` is invariant under isomorphisms of schemes. -/
lemma subsingleton_cechModH0_pullback_iso {U V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) {U' V' : Y'.Opens} (eU : U' = e ⁻¹ᵁ U)
    (eV : V' = e ⁻¹ᵁ V) (h : Subsingleton (cechModH0 S L U V)) :
    Subsingleton (cechModH0 S ((Scheme.Modules.pullback e).obj L) U' V') := by
  have eUV : U' ⊓ V' = e ⁻¹ᵁ (U ⊓ V) := by subst eU eV; rfl
  have hf := pullbackIsoSections_res e he L hU hUV inf_le_left eU eUV inf_le_left
  have hg := pullbackIsoSections_res e he L hV hUV inf_le_right eV eUV inf_le_right
  exact (TwoCech.equivH0 _ _ _ hf hg).toEquiv.symm.subsingleton

end Cech

open Cech Belyi

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)
  [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)

omit [PerfectField k] [IsCurveOver k C] in
/-- **Vanishing of chart sections is preserved by base change from a field.** -/
theorem subsingleton_chartH0_bcMap {T T'' : Scheme.{u}} [T.Over Sk] [IsAffine T] [IsAffine T'']
    (hF : IsField Γ(T, ⊤)) (h : T'' ⟶ T) (L : (pullback (C ↘ Sk) (T ↘ Sk)).Modules)
    [L.IsInvertible] (hL : Subsingleton (chartH0 π (T ↘ Sk) L)) :
    Subsingleton (chartH0 π (h ≫ (T ↘ Sk))
      ((Scheme.Modules.pullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)).obj L)) := by
  letI : T''.Over T := ⟨h⟩
  letI := hF.toField
  haveI : Module.Flat Γ(T, ⊤) Γ(T'', ⊤) := inferInstance
  -- the comparison isomorphism `C ×_k T'' ≅ (C ×_k T) ×_T T''`
  have HP : IsPullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)
      (pullback.snd (C ↘ Sk) (h ≫ (T ↘ Sk)))
      (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) :=
    HilbPoint.isPullback_baseChangeMap (C ↘ Sk)
      (Over.homMk h rfl : Over.mk (h ≫ (T ↘ Sk)) ⟶ Over.mk (T ↘ Sk))
  let e := HP.isoPullback.hom
  have he₁ : e ≫ pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) =
      bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl :=
    HP.isoPullback_hom_fst
  have he₂ : e ≫ pullback.snd (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) =
      pullback.snd (C ↘ Sk) (h ≫ (T ↘ Sk)) :=
    HP.isoPullback_hom_snd
  have hpX : bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl ≫ pullback.fst (C ↘ Sk) (T ↘ Sk) =
      pullback.fst (C ↘ Sk) (h ≫ (T ↘ Sk)) := bcMap_fst _ _ _ _ _
  let iso : (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback
      (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T))).obj L) ≅
      (Scheme.Modules.pullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)).obj L :=
    (Scheme.Modules.pullbackComp e _).app L ≪≫ eqToIso (by rw [he₁])
  have hcharts : ∀ i : Fin 2,
      (pullback.fst (C ↘ Sk) (h ≫ (T ↘ Sk)) ≫ π) ⁻¹ᵁ ProjectiveLine.U k i =
      e ⁻¹ᵁ (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) ⁻¹ᵁ
        (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k i)) := fun i ↦ by
    rw [← hpX, ← he₁]
    rfl
  have hZU := fun i : Fin 2 ↦ isAffineOpen_preimage_fst (S := T) (T := T'')
    (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k i) (isAffineOpen_chart π i) _ rfl
  have hZUV := isAffineOpen_preimage_fst (S := T) (T := T'')
    (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1) (isAffineOpen_chart_inf π) _ rfl
  have h1 := subsingleton_cechModH0_lineBundleBaseChange (T := T'') L _ _
    (isAffineOpen_chart π 0) (isAffineOpen_chart π 1) (isAffineOpen_chart_inf π) hL
  have h2 := subsingleton_cechModH0_pullback_iso (S := T'') e he₂ ((Scheme.Modules.pullback
    (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T))).obj L) (hZU 0) (hZU 1) hZUV
    (hcharts 0) (hcharts 1) h1
  have hf := sectionsIso_res (S := T'') iso
    (inf_le_left : chartOf π (h ≫ (T ↘ Sk)) 0 ⊓ chartOf π (h ≫ (T ↘ Sk)) 1 ≤ _)
  have hg := sectionsIso_res (S := T'') iso
    (inf_le_right : chartOf π (h ≫ (T ↘ Sk)) 0 ⊓ chartOf π (h ≫ (T ↘ Sk)) 1 ≤ _)
  exact (TwoCech.equivH0 _ _ _ hf hg).toEquiv.subsingleton_congr.mp h2

omit [PerfectField k] [IsCurveOver k C] in
/-- `subsingleton_chartH0_bcMap` for an arbitrary structure morphism `g' = h ≫ g`. -/
theorem subsingleton_chartH0_bcMap' {T T'' : Scheme.{u}} [T.Over Sk] [IsAffine T] [IsAffine T'']
    (hF : IsField Γ(T, ⊤)) (h : T'' ⟶ T) (g' : T'' ⟶ Sk) (w : h ≫ (T ↘ Sk) = g')
    (L : (pullback (C ↘ Sk) (T ↘ Sk)).Modules) [L.IsInvertible]
    (hL : Subsingleton (chartH0 π (T ↘ Sk) L)) :
    Subsingleton (chartH0 π g'
      ((Scheme.Modules.pullback (bcMap (C ↘ Sk) h (T ↘ Sk) g' w)).obj L)) := by
  subst w
  exact subsingleton_chartH0_bcMap π hF h L hL

end CurvesJacobian
