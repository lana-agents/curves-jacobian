/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.SmoothLift
import CurvesJacobian.Picard.PicLift
import CurvesJacobian.Picard.PicLft

/-!
# The Picard scheme of a curve is smooth

Let `k` be a separably closed perfect field and `C` a curve over `k` with a rational point `σ`.
The Picard scheme `Pic_{C/k,σ}` (`CurvesJacobian.picScheme`) and its open subschemes `Pic^d`
(`CurvesJacobian.picDegScheme`) are **smooth over `k`** (`smooth_picScheme`,
`smooth_picDegScheme`); this is part of Stacks, Lemma 44.6.7 (Tag 0BA0).

Proof (not the one of Stacks, which uses Tag 05B5 and smoothness of `Hilb^d`): `Pic` is locally
of finite presentation (`CurvesJacobian.locallyOfFinitePresentation_picScheme`), and it has the
infinitesimal lifting property (`liftProp_picScheme`), so it is smooth
(`SmoothLift.smooth_of_liftProp`). For the lifting property, by representability we must lift
rigidified invertible sheaves along a first-order thickening `T₀ ⊆ T` of affine `k`-schemes;
invertible sheaves lift (`PicLift.surjective_map_fst`: `C_T` is covered by the two affine
charts pulled back from `ℙ¹`, so the obstruction in `H²` vanishes), and the rigidification is
restored by subtracting the pullback of `σ_T^* L` (`surjective_picSigmaMap`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

section Generic

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- If `Pic(X_T) → Pic(X_{T'})` is surjective, so is `Pic_{X/S,σ}(T) → Pic_{X/S,σ}(T')`. -/
lemma surjective_picSigmaMap {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S)
    (w : a ≫ g = g') (h : Function.Surjective (Scheme.Pic.map (bcMap f a g g' w))) :
    Function.Surjective (picSigmaMap f σ hσ a g g' w) := by
  intro ξ₀
  obtain ⟨L, hL⟩ := h ξ₀.1
  refine ⟨(picSplit f σ hσ g L).2, Subtype.ext ?_⟩
  rw [coe_picSigmaMap, coe_picSplit_apply_snd, map_sub, hL]
  have e1 := congrArg (fun φ ↦ Scheme.Pic.map φ (Scheme.Pic.map (secT f σ hσ g) L))
    (bcMap_snd f a g g' w)
  simp only [Scheme.Pic.map_comp, AddMonoidHom.comp_apply] at e1
  have e2 := congrArg (fun φ ↦ Scheme.Pic.map φ L) (secT_bcMap f σ hσ a g g' w)
  simp only [Scheme.Pic.map_comp, AddMonoidHom.comp_apply] at e2
  rw [e1, ← e2, hL, (mem_picSigmaGrp f σ hσ _).1 ξ₀.2, map_zero, sub_zero]

end Generic

open Belyi

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)

omit [PerfectField k] [IsSepClosed k] [IsCurveOver k C] in
/-- **Invertible sheaves on `C_{T₀}` lift to `C_T`** for a first-order thickening `T₀ ⊆ T` of
affine `k`-schemes. -/
theorem surjective_pic_map_bcMap_curve (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]
    {T T₀ : Scheme.{u}} [IsAffine T] [IsAffine T₀] (j : T₀ ⟶ T)
    (hs : Function.Surjective j.appTop) (hq : MatLift.SqZero j.appTop.hom) (g : T ⟶ Sk) :
    Function.Surjective (Scheme.Pic.map (bcMap (C ↘ Sk) j g (j ≫ g) rfl)) := by
  letI : T.Over Sk := ⟨g⟩
  letI : T₀.Over T := ⟨j⟩
  letI : (pullback (C ↘ Sk) (T ↘ Sk)).Over T := ⟨pullback.snd _ _⟩
  have hU := isAffineOpen_chart (T₀ := T) π 0
  have hV := isAffineOpen_chart (T₀ := T) π 1
  have hUV : curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊔
      curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1 = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ProjectiveLine.U_sup, Scheme.Hom.preimage_top]
  have key := PicLift.surjective_map_fst (S := T) (T := T₀)
    (Y := pullback (C ↘ Sk) (T ↘ Sk)) hs hq _ _ hU hV hUV
    (chartτ (curveChartMap (T₀ := T) π)) (basicOpen_chartτ _).symm
    (chartσ (curveChartMap (T₀ := T) π)) (basicOpen_chartσ _).symm
  let e := pullbackLeftPullbackSndIso (C ↘ Sk) g j
  have he : e.hom ≫ bcMap (C ↘ Sk) j g (j ≫ g) rfl =
      pullback.fst (pullback.snd (C ↘ Sk) g) j := by
    apply pullback.hom_ext
    · simp [e, pullbackLeftPullbackSndIso_hom_fst]
    · simp [e, pullback.condition]
  have hinj : Function.Injective (Scheme.Pic.map e.hom) := by
    refine Function.LeftInverse.injective (g := Scheme.Pic.map e.inv) fun x ↦ ?_
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, e.inv_hom_id, Scheme.Pic.map_id,
      AddMonoidHom.id_apply]
  intro x
  obtain ⟨y, hy⟩ := key (Scheme.Pic.map e.hom x)
  refine ⟨y, hinj ?_⟩
  change Scheme.Pic.map (pullback.fst (pullback.snd (C ↘ Sk) g) j) y = _ at hy
  rw [← he, Scheme.Pic.map_comp, AddMonoidHom.comp_apply] at hy
  exact hy

lemma picScheme_homEquiv_comp {Y Y' : Over Sk} (a : Y' ⟶ Y) (b : Y ⟶ picScheme C σ hσ) :
    ((picSchemeRepresentableBy C σ hσ).homEquiv (a ≫ b) :
      ((picSigma (C ↘ Sk) σ hσ) ⋙ forget AddCommGrpCat).obj (op Y')) =
      ((picSigma (C ↘ Sk) σ hσ).map a.op).hom ((picSchemeRepresentableBy C σ hσ).homEquiv b) :=
  (picSchemeRepresentableBy C σ hσ).homEquiv_comp a b

/-- **The infinitesimal lifting property of the Picard scheme.** -/
theorem liftProp_picScheme : SmoothLift.LiftProp (picScheme C σ hσ).hom := by
  intro T T₀ _ _ j hs hq g x₀ hx₀
  obtain ⟨π₀, hπ⟩ : ∃ π : C ⟶ ProjectiveLine.scheme k, IsFinite π :=
    IsCurveOver.exists_finite_to_P1 k C
  obtain ⟨ξ, hξ⟩ := surjective_picSigmaMap (C ↘ Sk) σ hσ j g (j ≫ g) rfl
    (surjective_pic_map_bcMap_curve C π₀ j hs hq g)
    ((picSchemeRepresentableBy C σ hσ).homEquiv (X := Over.mk (j ≫ g)) (Over.homMk x₀ hx₀))
  obtain ⟨b, rfl⟩ := ((picSchemeRepresentableBy C σ hσ).homEquiv (X := Over.mk g)).surjective ξ
  have hab : (Over.homMk j rfl : Over.mk (j ≫ g) ⟶ Over.mk g) ≫ b = Over.homMk x₀ hx₀ := by
    apply (picSchemeRepresentableBy C σ hσ).homEquiv.injective
    rw [picScheme_homEquiv_comp]
    exact hξ
  exact ⟨b.left, Over.w b, congrArg (fun c ↦ c.left) hab⟩

/-- **The Picard scheme of a curve is smooth over `k`** (part of Stacks, Lemma 44.6.7,
Tag 0BA0). -/
instance smooth_picScheme : Smooth (picScheme C σ hσ).hom :=
  SmoothLift.smooth_of_liftProp _ (liftProp_picScheme C σ hσ)

/-- **`Pic^d_{C/k,σ}` is smooth over `k`.** -/
instance smooth_picDegScheme (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π] (d : ℤ) :
    Smooth (picDegScheme C σ hσ π d).hom :=
  IsZariskiLocalAtSource.comp (smooth_picScheme C σ hσ) (picDegOpens C σ hσ π d).ι

end CurvesJacobian
