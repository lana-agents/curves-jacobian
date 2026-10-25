/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ThetaFamily

/-!
# Galois invariance of the theta family (JAC J2)

For `g ∈ Gal(L/k)` acting on `J_L` (`galHom`), the class `[P] + (g − 1) [σ × J_L]` of the theta
family is invariant under `1 × g` (**`thetaClass_galois`**): the Poincaré bundle is
(`poincareGalIso`) and so is the divisor `σ × J_L`, `σ` being `k`-rational. Hence
`(1 × g)^* Θ ≅ Θ` (**`nonempty_thetaFamily_galIso`**, `thetaFamilyGalIso`).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Belyi

section Curve

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "LD" => jacFieldD C σ hσ Ω

/-- The divisor of the section `ptSec x` only depends on `x`. -/
lemma picClass_ofSection_ptSec_congr {T : Scheme.{u}}
    (g' : T ⟶ Sk) {x x' : T ⟶ C} (hx : x ≫ (C ↘ Sk) = g') (hx' : x' ≫ (C ↘ Sk) = g')
    (h : x = x') :
    (RelEffCartier.ofSection C g' (ptSec C g' x hx) (ptSec_snd _ _ _ _)).picClass =
      (RelEffCartier.ofSection C g' (ptSec C g' x' hx') (ptSec_snd _ _ _ _)).picClass := by
  subst h
  rfl

/-- **The class of `σ × J_L` is invariant under `1 × g`**, `g ∈ Gal(L/k)`. -/
theorem sigmaDivJ_picClass_galois (g : Gal(LD/k)) :
    Scheme.Pic.map (bcMap (C ↘ Sk) (galHom C σ hσ Ω g).left (jacDk C σ hσ Ω).hom
        (jacDk C σ hσ Ω).hom (Over.w (galHom C σ hσ Ω g))) (sigmaDivJ C σ hσ Ω).picClass =
      (sigmaDivJ C σ hσ Ω).picClass := by
  have hx : ((jacDk C σ hσ Ω).hom ≫ σ) ≫ (C ↘ Sk) = (jacDk C σ hσ Ω).hom := by
    rw [Category.assoc, hσ, Category.comp_id]
  have hD : Scheme.Pic.map (bcMap (C ↘ Sk) (galHom C σ hσ Ω g).left (jacDk C σ hσ Ω).hom
      (jacDk C σ hσ Ω).hom (Over.w (galHom C σ hσ Ω g))) (sigmaDivJ C σ hσ Ω).picClass = _ :=
    map_picClass_ptSec C (jacDk C σ hσ Ω).hom ((jacDk C σ hσ Ω).hom ≫ σ) hx
      (galHom C σ hσ Ω g).left _ (Over.w (galHom C σ hσ Ω g))
  rw [hD]
  refine (picClass_ofSection_ptSec_congr C _ _ hx ?_).trans rfl
  rw [← Category.assoc, Over.w (galHom C σ hσ Ω g)]

/-- **The theta class is Galois-invariant**: `(1 × g)^* ([P] + (g − 1)[σ × J_L])` is the same
class, for `g ∈ Gal(L/k)`. -/
theorem thetaClass_galois (g : Gal(LD/k)) :
    Scheme.Pic.map (bcMap (C ↘ Sk) (galHom C σ hσ Ω g).left (jacDk C σ hσ Ω).hom
        (jacDk C σ hσ Ω).hom (Over.w (galHom C σ hσ Ω g))) (thetaClass C σ hσ Ω) =
      thetaClass C σ hσ Ω := by
  rw [thetaClass, map_add, map_zsmul, sigmaDivJ_picClass_galois, Scheme.Pic.map_mk]
  congr 1
  exact Scheme.Pic.mk_eq_of_iso (poincareGalIso C σ hσ Ω g)

/-- **The theta family is Galois-invariant**: `(1 × g)^* Θ ≅ Θ` for `g ∈ Gal(L/k)`. -/
theorem nonempty_thetaFamily_galIso (g : Gal(LD/k)) :
    Nonempty ((Scheme.Modules.pullback (bcMap (C ↘ Sk) (galHom C σ hσ Ω g).left
      (jacDk C σ hσ Ω).hom (jacDk C σ hσ Ω).hom (Over.w (galHom C σ hσ Ω g)))).obj
        (thetaFamily C σ hσ Ω) ≅ thetaFamily C σ hσ Ω) := by
  rw [← Scheme.Pic.mk_eq_mk_iff, ← Scheme.Pic.map_mk, mk_thetaFamily, thetaClass_galois]

/-- A (non-canonical) isomorphism `(1 × g)^* Θ ≅ Θ`, `g ∈ Gal(L/k)`. -/
def thetaFamilyGalIso (g : Gal(LD/k)) :
    (Scheme.Modules.pullback (bcMap (C ↘ Sk) (galHom C σ hσ Ω g).left
      (jacDk C σ hσ Ω).hom (jacDk C σ hσ Ω).hom (Over.w (galHom C σ hσ Ω g)))).obj
        (thetaFamily C σ hσ Ω) ≅ thetaFamily C σ hσ Ω :=
  (nonempty_thetaFamily_galIso C σ hσ Ω g).some

end Curve

end CurvesJacobian
