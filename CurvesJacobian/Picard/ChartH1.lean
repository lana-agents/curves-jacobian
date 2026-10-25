/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicFH0

/-!
# Chart Čech `H¹` of modules on `C ×_k T`

`CurvesJacobian.chartH1 π g M`: the two-set Čech `H¹` of `M` on `C ×_k T'` for the covering by
the preimages of the two standard charts of `ℙ¹` under `π` (the `H¹` analogue of `chartH0`), and
its invariance under isomorphisms (`chartH1Congr`).
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Cech

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k)

/-- The Čech `H¹` of `M` on `C ×_k T'` for the chart covering. -/
abbrev chartH1 {T' : Scheme.{u}} (g' : T' ⟶ Spec (CommRingCat.of k))
    (M : (pullback (C ↘ Spec (CommRingCat.of k)) g').Modules) :=
  cechModH1 T' M (chartOf π g' 0) (chartOf π g' 1)

/-- Isomorphic modules have isomorphic chart `H¹`. -/
def chartH1Congr {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of k))
    {M M' : (pullback (C ↘ Spec (CommRingCat.of k)) g).Modules} (e : M ≅ M') :
    chartH1 π g M ≃ₗ[Γ(T, ⊤)] chartH1 π g M' :=
  TwoCech.equivH1 _ _ _ (sectionsIso_res (S := T) e inf_le_left)
    (sectionsIso_res (S := T) e inf_le_right)

end CurvesJacobian
