/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.GrpSeparated
import CurvesJacobian.Picard.PicDegScheme

/-!
# The Picard scheme is separated

`Pic_{C/k,σ}` is a group scheme over the field `k`, hence separated
(`CurvesJacobian.isSeparated_of_grpObj_field`); so are its open subschemes `Pic^d`
(`CurvesJacobian.isSeparated_picScheme`, `CurvesJacobian.isSeparated_picDegScheme`). This is
the separatedness part of the properness of `Pic^d` (Stacks, Lemma 44.6.7, Tag 0BA0).
-/

open CategoryTheory AlgebraicGeometry Belyi

universe u

namespace CurvesJacobian

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- **The Picard scheme of a curve is separated.** -/
instance isSeparated_picScheme : IsSeparated (picScheme C σ hσ).hom :=
  isSeparated_of_grpObj_field _

/-- **`Pic^d_{C/k,σ}` is separated.** -/
instance isSeparated_picDegScheme (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π] (d : ℤ) :
    IsSeparated (picDegScheme C σ hσ π d).hom :=
  inferInstanceAs (IsSeparated ((picDegOpens C σ hσ π d).ι ≫ (picScheme C σ hσ).hom))

end CurvesJacobian
