/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithDecomp
import CurvesJacobian.Cusp.BelyiDataExists

/-!
# [AbsTopII] Corollary 3.7 (c) for a nonempty open `U_X ⊆ X`

[AbsTopII] Corollary 3.7 (c) (`Topics in Absolute Anabelian Geometry II.txt` l.4767–4769): "The
decomposition groups of the closed points of `X` lying in the complement of `U_X` may be obtained
as the images via `Π_{U_X} ↠ Π` of the cuspidal decomposition groups of `Π_{U_X}`."

For an affine hyperbolic curve `CX = (X̄, X)` over a number field `K` (with a cusp) and a
nonempty open `U_X ⊆ X`:

* `CurvesJacobian.Cusp.subCurve CX U_X`: the hyperbolic curve `(X̄, U_X)`;
* **`CurvesJacobian.Cusp.cor37c`**: up to one change of base point, for every place `W` of
  `K(X̄_Ω)^alg` over a cusp of `U_X`, the image under `Π_{U_X} ↠ Π_X` (`fillMap`) of the cuspidal
  decomposition group `Comm_{Π_{U_X}}(I_W)` is the decomposition group `arithDecomp CX W` of `W`
  in `Π_X` (`arithmeticExt Ω CX`); for `W` over a closed point `x ∈ X ∖ U_X` this is a
  decomposition group of `x`. (The curve `(X̄, X)` obtained by filling `U_X` is `CX` itself.)
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (CX : HypCurve K)
  (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The hyperbolic curve `(X̄, U_X)` for a nonempty open `U_X ⊆ X`. -/
def subCurve (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty) :
    HypCurve K where
  Xbar := CX.Xbar
  U := UX
  nonempty := hne
  cusps_finite := finite_compl_of_isCurveOver (k := K) CX.Xbar UX hne
  hyperbolic := by
    haveI := IsCurveOver.isIntegral K CX.Xbar
    exact hyp_of_le hUX (finite_compl_of_isCurveOver (k := K) CX.Xbar UX hne) CX.hyperbolic

/-- **[AbsTopII] Corollary 3.7 (c)**: for a nonempty open `U_X ⊆ X` and any change of base point
`α₀` from the base point of `X` to the image of the base point of `U_X`, there is `t ∈ Π_X` such
that for every place `W` over a cusp of `U_X`, the image under `Π_{U_X} ↠ Π_X` of the cuspidal
decomposition group `Comm_{Π_{U_X}}(I_W)` is `t · α₀(D_W(X)) · t⁻¹`, where `D_W(X)` is the
decomposition group of `W` in `Π_X` — a decomposition group of the closed point `x ∈ X ∖ U_X`
under `W` when `W` is centred on `X`. -/
theorem cor37c (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
    (α₀ : fiber (basePoint Ω CX hcX) ≅
      fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX)) :
    ∃ t, ∀ W : ValuationSubring (FFClosure (geomCurve Ω CX)),
      IsCuspPlace Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) W →
      (Subgroup.Commensurable.commensurator (arithInertia Ω (subCurve CX UX hUX hne)
          (compl_nonempty_of_le hUX hcX) W)).map
          (fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX).toMonoidHom =
        ((arithDecomp Ω CX hcX W).map (autContinuousMulEquivOfIso
          (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
            α₀)).toMulEquiv.toMonoidHom).map (MulAut.conj t).toMonoidHom :=
  exists_map_fillMap_commensurator Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX
    hcX CX.hyperbolic α₀

end CurvesJacobian.Cusp
