/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicSigmaSheaf
import CurvesJacobian.Picard.PicSigmaCurveOpen
import CurvesJacobian.Picard.OverSigmaSheafSmall

/-!
# `Pic_{X/k,σ}` of a curve is a Zariski sheaf

For a curve `X` over a perfect field `k` with a rational point `σ`, the rigidified Picard functor
`Pic_{X/k,σ}` (Stacks, Section 44.6, Tag 0B9R) is a sheaf for the Zariski topology on the
category of all schemes (`isSheaf_picSigmaSch_curve`): the hypothesis of
`CurvesJacobian.isSheafOver_picSigma` is `𝒪_T ≅ f_{T,*}𝒪_{X_T}` (Stacks, Lemma 44.6.1,
Tag 0B9U; `IsCurveOver.surjective_app_pullback_snd`). This is the sheaf property needed to apply
`CurvesJacobian.isRepresentable_of_translate` (Stacks, Lemma 44.5.1, Tag 0B9Q) to `Pic_{X/k,σ}`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi

universe u

namespace CurvesJacobian

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsCurveOver k X] [PerfectField k]

local notation "Sk" => Spec (CommRingCat.of k)

/-- `Pic_{X/k,σ}` satisfies the sheaf condition for open covers, for a curve `X`. -/
theorem isSheafOver_picSigma_curve (σ : Sk ⟶ X) (hσ : σ ≫ (X ↘ Sk) = 𝟙 Sk) :
    IsSheafOver.{u} (picSigma (X ↘ Sk) σ hσ ⋙ forget AddCommGrpCat) :=
  isSheafOver_picSigma _ σ hσ fun _ g U ↦ IsCurveOver.surjective_app_pullback_snd k X g U

/-- **`Pic_{X/k,σ}` of a curve is a Zariski sheaf** on the category of schemes. -/
theorem isSheaf_picSigmaSch_curve (σ : Sk ⟶ X) (hσ : σ ≫ (X ↘ Sk) = 𝟙 Sk) :
    Presieve.IsSheaf Scheme.zariskiTopology (picSigmaSch (X ↘ Sk) σ hσ) :=
  isSheaf_overSigma_of_small (isSheafOver_picSigma_curve k X σ hσ)

end CurvesJacobian
