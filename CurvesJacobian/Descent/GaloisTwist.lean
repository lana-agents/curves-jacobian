/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Descent.GaloisSplit
import CurvesJacobian.Picard.JacobianGalois

/-!
# The semilinear Galois action on a representing object

Let `L / k` be a finite Galois extension, `P` a presheaf on `(Sch/k)` and `X` an `L`-scheme
representing the restriction of `P` to `(Sch/L)`. The Yoneda twists `φ_g = twistLeft (Spec g)`
(`CurvesJacobian.twistLeft`, `Picard/JacobianGalois`) form a semilinear action of `Gal(L/k)` on
`X` (`CurvesJacobian.GaloisDescent.twistGalAction`), to which the Galois descent of
`Descent/GaloisScheme` applies.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  (P : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type u) {X : Over (Spec (CommRingCat.of L))}
  (R : ((Over.map (sL k L)).op ⋙ P).RepresentableBy X)

/-- **The Galois action on a representing object**: `g ↦ φ_{Spec g}`. -/
def twistGalAction : GalAction (k := k) X.left X.hom where
  act g := twistLeft (sL k L) P R (specGal_comp_sL g)
  act_comp _ := twistHom_left_comp _ _ _ _
  act_one := (twistHom_congr _ _ _ specGal_one _ (Category.id_comp _)).trans
    (twistLeft_id _ _ _)
  act_mul g h := (twistLeft_comp_twistLeft _ _ _ _ _).trans
    (twistHom_congr _ _ _ (specGal_mul g h) _ _)

lemma twistGalAction_act (g : Gal(L/k)) :
    (twistGalAction P R).act g = twistLeft (sL k L) P R (specGal_comp_sL g) := rfl

end CurvesJacobian.GaloisDescent
