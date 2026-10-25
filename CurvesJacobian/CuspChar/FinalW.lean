/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.ArithTop
import CurvesJacobian.CuspChar.WeightCover

/-!
# [AbsTopI] Lemma 4.5 (v) over number fields, unconditionally

The cusp weight identity of an affine hyperbolic curve over a number field
(`CurvesJacobian.CuspChar.cuspWeightIdentity`): for every open `H ⊆ Δ_U` there is an open
`P ⊆ Π_U` normalising `H` with `det(x | Hom(H, ℤ/3^k))² = χ_{3^k}(x)^{[Δ:H](2g-2+r) + r_H}`.
It is the case `H = ⊤` (`CurvesJacobian.CuspChar.weight_top`: Kummer theory of `U_Ω`, Weil
pairing, residues at the cusps) for all curves, transported to open subgroups along the cover
curves (`CurvesJacobian.CuspChar.cuspWeightIdentity_of_top`).

Hence the hypotheses `hW`, `hW'` of `CurvesJacobian.CuspChar.mem_arithCusps_iff_map_mem` and
`CurvesJacobian.CuspChar.arithmeticExtIso` hold, and **every pair of compatible topological
isomorphisms `Π_U ≃ₜ* Π_{U'}`, `G_K ≃ₜ* G_{K'}` preserves the cuspidal inertia groups**
(`CurvesJacobian.CuspChar.mem_arithCusps_iff_map_mem'`,
`CurvesJacobian.CuspChar.arithmeticExtIso'`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  CurvesJacobian.Cusp

universe u

noncomputable section

namespace CurvesJacobian.CuspChar

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {K' : Type u} [Field K'] [NumberField K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω']
  [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω']

attribute [local instance] isAlgClosure_of_isAlgebraic

variable (Ω) in
/-- **The cusp weight identity** of an affine hyperbolic curve over a number field. -/
theorem cuspWeightIdentity (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    CuspWeightIdentity (deltaU Ω C hc) (deltaCusps Ω C hc) 3 (eulerU Ω C) (cyc3 Ω C hc) :=
  cuspWeightIdentity_of_top (fun _ _ _ _ _ C' hc' ↦ weight_top Ω C' hc') C hc

/-- **[AbsTopI] Lemma 4.5 (v)** for affine hyperbolic curves over number fields:
isomorphisms `Π_U ≃ₜ* Π_{U'}` over `G_K ≃ₜ* G_{K'}` preserve the cuspidal inertia groups. -/
theorem mem_arithCusps_iff_map_mem' {C : HypCurve K} {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
    {C' : HypCurve K'} {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (ψ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))))
    (hpr : ∀ x, projGk Ω' C' hc' (Φ x) = ψ (projGk Ω C hc x))
    (I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    I ∈ arithCusps Ω C hc ↔ I.map Φ.toMulEquiv.toMonoidHom ∈ arithCusps Ω' C' hc' :=
  mem_arithCusps_iff_map_mem Φ ψ hpr (cuspWeightIdentity Ω C hc)
    (cuspWeightIdentity Ω' C' hc') I

/-- **[AbsTopI] Lemma 4.5 (v), packaged**: compatible isomorphisms `Π_U ≃ₜ* Π_{U'}`,
`G_K ≃ₜ* G_{K'}` form an isomorphism of cuspidal extensions. -/
def arithmeticExtIso' {C : HypCurve K} {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
    {C' : HypCurve K'} {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}
    (Φ : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω' C' hc').Pi)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω' C' hc').G)
    (hpr : ∀ x, (arithmeticExt Ω' C' hc').pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x)) :
    (arithmeticExt Ω C hc).Iso (arithmeticExt Ω' C' hc') :=
  arithmeticExtIso Φ ψ hpr (cuspWeightIdentity Ω C hc) (cuspWeightIdentity Ω' C' hc')

end CurvesJacobian.CuspChar
