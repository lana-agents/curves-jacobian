/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Cor37c

/-!
# A basic open `D(r) ⊆ U` of an affine hyperbolic curve

For a hyperbolic curve `C = (X̄ ⊇ U)` over a number field `M` with a cusp (so `U` is affine and
`Γ(X̄, U)` is a domain) and a nonzero section `r ∈ Γ(X̄, U)`:

* `CurvesJacobian.Cusp.basicSubCurve`: the hyperbolic curve `(X̄, D(r))`, with a cusp
  (`basicSubCurve_cusp`) and `U = D(r)` (`basicSubCurve_U`);
* `CurvesJacobian.Cusp.basicSubCurveIso`: `Spec Γ(X̄, D(r)) ≅ Spec Γ(X̄, U)_r`, compatible with
  the maps to `Spec Γ(X̄, U)` (`basicSubCurveIso_hom_comp`, `basicSubCurveIso_hom_comp_resAlg`)
  and with the structure maps to `Spec M` (`basicSubCurveIso_hom_comp_structure`);
* `CurvesJacobian.Cusp.fillCurve_basicSubCurve`: filling `D(r) ⊆ U` gives back `C`, so that
  `basicFillMap` (`fillMap` of `D(r) ⊆ U`) is a map `Π_{D(r)} → π₁(Spec Γ(X̄, U))`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {M : Type u} [Field M] [NumberField M] (C : HypCurve M)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) (r : Γ(C.Xbar, C.U)) (hr : r ≠ 0)

omit [NumberField M] in
include hr in
/-- The basic open `D(r)` of a nonzero section `r ∈ Γ(X̄, U)` is nonempty. -/
lemma basicSubCurve_nonempty : (C.Xbar.basicOpen r : Set C.Xbar).Nonempty := by
  haveI := IsCurveOver.isIntegral M C.Xbar
  by_contra h
  exact hr ((basicOpen_eq_bot_iff r).1 ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).1 h))

/-- **The hyperbolic curve `(X̄, D(r))`** for a nonzero section `r ∈ Γ(X̄, U)`. -/
def basicSubCurve : HypCurve M :=
  subCurve C (C.Xbar.basicOpen r) (C.Xbar.basicOpen_le r) (basicSubCurve_nonempty C r hr)

lemma basicSubCurve_U : (basicSubCurve C r hr).U = C.Xbar.basicOpen r := rfl

lemma basicSubCurve_Xbar : (basicSubCurve C r hr).Xbar = C.Xbar := rfl

include hc in
/-- `(X̄, D(r))` has a cusp. -/
lemma basicSubCurve_cusp :
    ((basicSubCurve C r hr).U : Set (basicSubCurve C r hr).Xbar)ᶜ.Nonempty :=
  compl_nonempty_of_le (C.Xbar.basicOpen_le r) hc

/-- **`Γ(X̄, D(r)) ≃ Γ(X̄, U)_r`** as `Γ(X̄, U)`-algebras (`U` is affine). -/
def basicSectionsAlgEquiv :
    Localization.Away r ≃ₐ[Γ(C.Xbar, C.U)] Γ(C.Xbar, C.Xbar.basicOpen r) :=
  haveI := (isAffineOpen_U C hc).isLocalization_basicOpen r
  IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) _

/-- **`Spec Γ(X̄, D(r)) ≅ Spec Γ(X̄, U)_r`**. -/
def basicSubCurveIso :
    Spec Γ(C.Xbar, C.Xbar.basicOpen r) ≅ Spec (CommRingCat.of (Localization.Away r)) :=
  Scheme.Spec.mapIso (basicSectionsAlgEquiv C hc r).toRingEquiv.toCommRingCatIso.op

lemma basicSubCurveIso_hom :
    (basicSubCurveIso C hc r).hom =
      Spec.map (CommRingCat.ofHom (basicSectionsAlgEquiv C hc r).toRingEquiv.toRingHom) := rfl

omit [NumberField M] in
/-- `resAlg` of `D(r) ⊆ U` is the restriction map of the structure presheaf. -/
lemma resAlg_basicOpen_apply (a : Γ(C.Xbar, C.U)) :
    resAlg M (C.Xbar.basicOpen_le r) a =
      C.Xbar.presheaf.map (homOfLE (C.Xbar.basicOpen_le r)).op a := by
  simp [resAlg, Scheme.Hom.appLE]
  rfl

/-- The isomorphism is compatible with the maps to `Spec Γ(X̄, U)` (restriction map). -/
lemma basicSubCurveIso_hom_comp :
    (basicSubCurveIso C hc r).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(C.Xbar, C.U) (Localization.Away r))) =
      Spec.map (C.Xbar.presheaf.map (homOfLE (C.Xbar.basicOpen_le r)).op) := by
  rw [basicSubCurveIso_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  exact (basicSectionsAlgEquiv C hc r).commutes a

/-- The isomorphism is compatible with the maps to `Spec Γ(X̄, U)` (`resAlg`, as in `fillMap`). -/
lemma basicSubCurveIso_hom_comp_resAlg :
    (basicSubCurveIso C hc r).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(C.Xbar, C.U) (Localization.Away r))) =
      Spec.map (CommRingCat.ofHom (resAlg M (C.Xbar.basicOpen_le r)).toRingHom) := by
  rw [basicSubCurveIso_hom_comp]
  congr 1

/-- The isomorphism is compatible with the structure maps to `Spec M`. -/
lemma basicSubCurveIso_hom_comp_structure :
    (basicSubCurveIso C hc r).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap M (Localization.Away r))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.Xbar.basicOpen r))) := by
  rw [basicSubCurveIso_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext c
  change basicSectionsAlgEquiv C hc r (algebraMap Γ(C.Xbar, C.U) _ (algebraMap M _ c)) = _
  rw [AlgEquiv.commutes]
  exact (resAlg M (C.Xbar.basicOpen_le r)).commutes c

/-- **Filling `D(r) ⊆ U` gives back `C`.** -/
theorem fillCurve_basicSubCurve :
    fillCurve (basicSubCurve C r hr) (C.Xbar.basicOpen_le r) C.hyperbolic = C := rfl

/-- **`Π_{D(r)} → π₁(Spec Γ(X̄, U))`**: `fillMap` of `D(r) ⊆ U`. -/
def basicFillMap (Ω : Type u) [Field Ω] [Algebra M Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic M Ω]
    [CharZero Ω] :
    π₁ᵉᵗ(basePoint Ω (basicSubCurve C r hr) (basicSubCurve_cusp C hc r hr) ≫
        baseChangeSpec M Ω Γ(C.Xbar, C.Xbar.basicOpen r)) →ₜ*
      π₁ᵉᵗ(fillPoint Ω (basicSubCurve C r hr) (basicSubCurve_cusp C hc r hr)
          (C.Xbar.basicOpen_le r) ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) :=
  fillMap Ω (basicSubCurve C r hr) (basicSubCurve_cusp C hc r hr) (C.Xbar.basicOpen_le r)

end CurvesJacobian.Cusp
