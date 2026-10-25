/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithmeticExt
import CurvesJacobian.LocAn.PadicSlim

/-!
# The arithmetic `CuspidalExt` over `p`-adic fields

For a finite extension `K/ℚ_p` and an algebraic closure `Ω` of `K`, `G_K` is slim
(`CurvesJacobian.LocAn.isSlim_Gk_padic`, [AbsTopI] Theorem 1.7 (ii)), i.e.
`CurvesJacobian.Cusp.IsSlimGk K Ω` holds (`CurvesJacobian.Cusp.isSlimGk_padic`). Hence the
arithmetic `CuspidalExt` `CurvesJacobian.Cusp.arithmeticExt Ω C hc` of an affine hyperbolic curve
`C` over `K` is available (`CurvesJacobian.Cusp.arithmeticExt_padic`).

`p` cannot be inferred from `K`, so `isSlimGk_padic` is a theorem, to be used via `haveI`.
-/

open CategoryTheory AlgebraicGeometry Belyi Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

omit [FiniteDimensional ℚ_[p] K] in
include p in
/-- A `p`-adic field has characteristic zero. -/
lemma charZero_padic : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective

include p in
/-- **`G_K` is slim for a finite extension `K/ℚ_p`**, as the class `IsSlimGk`. -/
theorem isSlimGk_padic (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra.IsAlgebraic K Ω] : IsSlimGk K Ω :=
  ⟨LocAn.isSlim_Gk_padic p Ω⟩

/-- **The arithmetic `CuspidalExt` of an affine hyperbolic curve over a `p`-adic field** `K`
(`Ω` an algebraic closure of `K`): `arithmeticExt Ω C hc` with the slimness of `G_K` from
`isSlimGk_padic`. -/
abbrev arithmeticExt_padic (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    CuspidalExt.{u + 1} :=
  haveI := charZero_padic p (K := K)
  haveI := isSlimGk_padic p (K := K) Ω
  arithmeticExt Ω C hc

end CurvesJacobian.Cusp
