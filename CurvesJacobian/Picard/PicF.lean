/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TwoCechInvertible
import CurvesJacobian.Picard.CurveCohomology

/-!
# The `F`-condition for line bundles on curves

Let `C` be a scheme over a field `k` with a finite morphism `π : C → ℙ¹_k`, `T₀` an affine
`k`-scheme and `L` an invertible sheaf on `X_{T₀} = C ×_k T₀`. Let `U`, `V` be the preimages in
`X_{T₀}` of the two standard charts of `ℙ¹`. The predicate `CurvesJacobian.IsFPointCurve π L`
says that the Čech `H¹` of `L` for `(U, V)` vanishes and its Čech `H⁰` is an invertible
`Γ(T₀)`-module: this is the condition defining the subfunctor `F ⊆ Pic_{X/k,σ}` of Stacks,
Lemma 44.6.2 (Tag 0B9V), on affine test schemes.

`CurvesJacobian.IsFPointCurve.baseChange`: the condition is stable under base change along any
affine `T₀`-scheme `T`, with `L_T` on `X_{T₀} ×_{T₀} T` and the covering `(U_T, V_T)`; moreover
`H⁰(L_T) ≃ Γ(T) ⊗ H⁰(L)` (`CurvesJacobian.cechH0BaseChangeCurve`). This uses only flatness of
the Čech terms over `Γ(T₀)` (no Noetherian hypotheses; cf. Stacks, Lemma 36.30.4, Tag 0B91).
Openness of `F` is not treated here.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

open Cech

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  {T₀ : Scheme.{u}} [T₀.Over (Spec (CommRingCat.of k))] [IsAffine T₀]
  (π : C ⟶ ProjectiveLine.scheme k)

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T₀ ↘ Sk)

/-- **The `F`-condition** (Stacks, Lemma 44.6.2, Tag 0B9V) for `L` on `X_{T₀}`, with respect to
the covering by the preimages of the standard charts of `ℙ¹` under `π`: the Čech `H¹` vanishes
and the Čech `H⁰` is an invertible `Γ(T₀)`-module. -/
def IsFPointCurve (L : (XT).Modules) : Prop :=
  IsFPoint T₀ L (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0)
    (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1)

/-- The overlap of the two charts of `X_{T₀}` has sections flat over `Γ(T₀)`. -/
lemma flat_chart_inf [IsFinite π] :
    Module.Flat Γ(T₀, ⊤) Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) :=
  flat_sections_baseChange _ ((ProjectiveLine.isAffineOpen_U_inf k).preimage π) _ rfl

variable {π} (T : Scheme.{u}) [T.Over T₀] [IsAffine T]

/-- **Stability of the `F`-condition under base change** (Stacks, Lemma 44.6.2, Tag 0B9V):
if `L` on `X_{T₀}` satisfies the `F`-condition, so does `L_T` for every affine `T₀`-scheme `T`,
for the pulled-back covering. -/
theorem IsFPointCurve.baseChange [IsFinite π] {L : (XT).Modules} [L.IsInvertible]
    (h : IsFPointCurve π L) :
    IsFPoint T (lineBundleBaseChange (S := T₀) (T := T) L)
      (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
        (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0))
      (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
        (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1)) :=
  haveI := flat_chart_inf (T₀ := T₀) π
  IsFPoint.baseChange L (isAffineOpen_chart π 0) (isAffineOpen_chart π 1)
    (isAffineOpen_chart_inf π) h

/-- Under the `F`-condition, `H⁰` of `L_T` is the base change of `H⁰` of `L`. -/
def cechH0BaseChangeCurve [IsFinite π] {L : (XT).Modules} [L.IsInvertible]
    (h : IsFPointCurve π L) :
    cechModH0 T (lineBundleBaseChange (S := T₀) (T := T) L)
      (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
        (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0))
      (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
        (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1)) ≃ₗ[Γ(T, ⊤)]
      Γ(T, ⊤) ⊗[Γ(T₀, ⊤)] cechModH0 T₀ L (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0)
        (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) :=
  haveI := flat_chart_inf (T₀ := T₀) π
  lineBundleH0BaseChange' L (isAffineOpen_chart π 0) (isAffineOpen_chart π 1)
    (isAffineOpen_chart_inf π) h.1

end CurvesJacobian
