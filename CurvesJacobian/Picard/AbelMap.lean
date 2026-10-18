/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RelEffCartierPullback
import CurvesJacobian.Picard.HilbCurve
import CurvesJacobian.Picard.PicSigma

/-!
# The Abel map `Hilb^d_{C/k} ⟶ Pic_{C/k,σ}`

Let `f : X ⟶ S` have a section `σ`. For `g : T ⟶ S` and a relative effective Cartier divisor
`D` on `X_T/T`, the class `𝒪(D) ⊗ f_T^* σ_T^* 𝒪(D)^{-1}` lies in `Pic_{X/S,σ}(T)` (Stacks,
Section 44.6, Tag 0B9R): this is `abelClass`, the `Pic_{X/S,σ}`-component of the class of `D`
under the splitting `picSplit`. It is compatible with base change (`picSigmaMap_abelClass`).

For a curve `C` over a perfect field `k` with a rational point `σ`, this gives the Abel map
`γ_d : Hilb^d_{C/k} ⟶ Pic_{C/k,σ}`, `D ↦ 𝒪(D) ⊗ f_T^* σ_T^* 𝒪(D)^{-1}`, used in Stacks,
Lemma 44.6.4 (Tag 0B9X): as a natural transformation of functors on `Over (Spec k)`
(`abelOver`), of functors on all schemes (`abelSch`), and on the representing scheme
(`abelMap : yoneda.obj (hilbCurve k C d) ⟶ picSigmaSch`).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

section Generic

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

variable {T T' : Scheme.{u}}

/-- The splitting `picSplit` is compatible with pullback along `a : T' ⟶ T` over `S`. -/
lemma picSigmaMap_picSplit_snd (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g')
    (x : (pullback f g).Pic) :
    picSigmaMap f σ hσ a g g' w (picSplit f σ hσ g x).2 =
      (picSplit f σ hσ g' (Scheme.Pic.map (bcMap f a g g' w) x)).2 := by
  apply Subtype.ext
  rw [coe_picSigmaMap, coe_picSplit_apply_snd, coe_picSplit_apply_snd, map_sub]
  congr 1
  have h1 : (Scheme.Pic.map (bcMap f a g g' w)).comp (Scheme.Pic.map (pullback.snd f g)) =
      (Scheme.Pic.map (pullback.snd f g')).comp (Scheme.Pic.map a) := by
    rw [← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, bcMap_snd]
  have h2 : (Scheme.Pic.map a).comp (Scheme.Pic.map (secT f σ hσ g)) =
      (Scheme.Pic.map (secT f σ hσ g')).comp (Scheme.Pic.map (bcMap f a g g' w)) := by
    rw [← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, secT_bcMap]
  have := DFunLike.congr_fun h1 (Scheme.Pic.map (secT f σ hσ g) x)
  simp only [AddMonoidHom.comp_apply] at this ⊢
  rw [this, ← AddMonoidHom.comp_apply (Scheme.Pic.map a), h2, AddMonoidHom.comp_apply]

/-- The Abel class of a relative effective Cartier divisor `D` on `X_T/T`: the element
`𝒪(D) ⊗ f_T^* σ_T^* 𝒪(D)^{-1}` of `Pic_{X/S,σ}(T)` (Stacks, Section 44.6, Tag 0B9R). -/
def abelClass {g : T ⟶ S} (D : RelEffCartier (pullback.snd f g)) : picSigmaGrp f σ hσ g :=
  (picSplit f σ hσ g D.picClass).2

lemma coe_abelClass {g : T ⟶ S} (D : RelEffCartier (pullback.snd f g)) :
    (abelClass f σ hσ D : (pullback f g).Pic) =
      D.picClass - Scheme.Pic.map (pullback.snd f g)
        (Scheme.Pic.map (secT f σ hσ g) D.picClass) :=
  rfl

/-- Naturality of the Abel class: the pullback of the Abel class of `D` along `a : T' ⟶ T` is
the Abel class of the pulled-back divisor. -/
theorem picSigmaMap_abelClass (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g')
    (D : RelEffCartier (pullback.snd f g)) (D' : RelEffCartier (pullback.snd f g'))
    (h : D'.ideal = D.ideal.comap (bcMap f a g g' w)) :
    picSigmaMap f σ hσ a g g' w (abelClass f σ hσ D) = abelClass f σ hσ D' := by
  rw [abelClass, picSigmaMap_picSplit_snd, RelEffCartier.map_picClass_of_ideal_eq D D' _ h]
  rfl

end Generic

section Curve

open Belyi

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  [PerfectField k] [IsCurveOver k C]

local notation "Sk" => Spec (CommRingCat.of k)

variable (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k))) (d : ℕ)

/-- The Abel map `γ_d : Hilb^d_{C/k} ⟶ Pic_{C/k,σ}` as a natural transformation of functors on
`Over (Spec k)`, `D ↦ 𝒪(D) ⊗ f_T^* σ_T^* 𝒪(D)^{-1}` (Stacks, Section 44.6, Tag 0B9R, and
Lemma 44.6.4, Tag 0B9X). -/
def abelOver : hilbFunctor (C ↘ Sk) d ⟶ picSigma (C ↘ Sk) σ hσ ⋙ forget AddCommGrpCat where
  app T := ↾fun P ↦ abelClass (C ↘ Sk) σ hσ (hilbEquivRelEffCartier d C T.unop P).1
  naturality {T T'} b := by
    ext P
    exact (picSigmaMap_abelClass (C ↘ Sk) σ hσ b.unop.left _ _ (Over.w b.unop) _ _ rfl).symm

lemma abelOver_app (T : Over Sk) (P : HilbPoint (C ↘ Sk) d T) :
    (abelOver C σ hσ d).app (op T) P =
      abelClass (C ↘ Sk) σ hσ (hilbEquivRelEffCartier d C T P).1 :=
  rfl

/-- The Abel map `γ_d : Hilb^d_{C/k} ⟶ Pic_{C/k,σ}` as a natural transformation of functors on
all schemes (Stacks, Section 44.6, Tag 0B9R, and Lemma 44.6.4, Tag 0B9X). -/
def abelSch : hilbSch (C ↘ Sk) d ⟶ picSigmaSch (C ↘ Sk) σ hσ where
  app T := ↾fun x ↦ (⟨x.1, abelClass (C ↘ Sk) σ hσ (hilbEquivRelEffCartier d C _ x.2).1⟩ :
    (picSigmaSch (C ↘ Sk) σ hσ).obj T)
  naturality {T T'} b := by
    ext ⟨g, P⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact (picSigmaMap_abelClass (C ↘ Sk) σ hσ b.unop _ _ rfl _ _ rfl).symm

lemma abelSch_app {T : Scheme.{u}} (g : T ⟶ Sk) (P : HilbPoint (C ↘ Sk) d (Over.mk g)) :
    (abelSch C σ hσ d).app (op T) ⟨g, P⟩ =
      (⟨g, abelClass (C ↘ Sk) σ hσ (hilbEquivRelEffCartier d C _ P).1⟩ :
        (picSigmaSch (C ↘ Sk) σ hσ).obj (op T)) :=
  rfl

/-- The Abel morphism `γ_d : Hilb^d_{C/k} ⟶ Pic_{C/k,σ}` on the representing scheme
`Hilb^d_{C/k}`: a `T`-point `(g, D)` (`hilbCurveEquiv`) is sent to
`𝒪(D) ⊗ f_T^* σ_T^* 𝒪(D)^{-1}` (Stacks, Section 44.6, Tag 0B9R, and Lemma 44.6.4,
Tag 0B9X). -/
def abelMap : yoneda.obj (hilbCurve k C d) ⟶ picSigmaSch (C ↘ Sk) σ hσ :=
  (hilbSch (C ↘ Sk) d).reprW.hom ≫ abelSch C σ hσ d

lemma abelMap_app {T : Scheme.{u}} (a : T ⟶ hilbCurve k C d) :
    (abelMap C σ hσ d).app (op T) a =
      (⟨(hilbCurveEquiv k C d T a).1,
        abelClass (C ↘ Sk) σ hσ (hilbCurveEquiv k C d T a).2.1⟩ :
          (picSigmaSch (C ↘ Sk) σ hσ).obj (op T)) :=
  rfl

end Curve

end CurvesJacobian
