/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.FinalW
import CurvesJacobian.CuspChar.CyclotomicPadic
import CurvesJacobian.Cusp.ArithmeticPadic

/-!
# [AbsTopI] Lemma 4.5 (v) over `p`-adic fields

For a finite extension `K/ℚ_p` the two arithmetic inputs of
`CurvesJacobian.CuspChar.mem_arithCusps_iff_map_mem'` hold: `G_K` is slim
(`CurvesJacobian.Cusp.isSlimGk_padic`) and the mod-`3^k` cyclotomic characters have no finite
exponent on open subgroups of `G_K` (`CurvesJacobian.CuspChar.cycNoExponent_padic`, from
`CurvesJacobian.CuspChar.exists_cycChar_pow_ne_one_padic`). Hence ([AbsTopI] Lemma 4.5 (v),
`Topics in Absolute Anabelian Geometry I.txt` l.3335) **for affine hyperbolic curves `U`, `U'`
over finite extensions `K/ℚ_p`, `K'/ℚ_{p'}`, every pair of compatible topological isomorphisms
`Π_U ≃ₜ* Π_{U'}`, `G_K ≃ₜ* G_{K'}` maps the cuspidal inertia groups of `Π_U` exactly onto those
of `Π_{U'}`** (`CurvesJacobian.CuspChar.mem_arithCusps_iff_map_mem_padic`), i.e. is an
isomorphism of cuspidal extensions (`CurvesJacobian.CuspChar.arithmeticExtIso_padic`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  CurvesJacobian.Cusp

universe u

noncomputable section

namespace CurvesJacobian.CuspChar

/-- **B3 for `p`-adic fields**: the mod-`3^k` cyclotomic characters have no finite exponent on
open subgroups of `Gal(Ω/K)`, `K/ℚ_p` finite (also for `p = 3`). -/
theorem cycNoExponent_padic (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] (Ω : Type*) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    [CharZero Ω] [Algebra.IsAlgebraic K Ω] : CycNoExponent K Ω 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  ⟨fun L _ _ hN ↦ exists_cycChar_pow_ne_one_padic p (by norm_num) L hN⟩

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  (p' : ℕ) [Fact p'.Prime] {K' : Type u} [Field K'] [Algebra ℚ_[p'] K']
  [FiniteDimensional ℚ_[p'] K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω'] [IsAlgClosed Ω']
  [Algebra.IsAlgebraic K' Ω'] [CharZero Ω']

include p p' in
/-- **[AbsTopI] Lemma 4.5 (v)** for affine hyperbolic curves over `p`-adic fields:
isomorphisms `Π_U ≃ₜ* Π_{U'}` over `G_K ≃ₜ* G_{K'}` preserve the cuspidal inertia groups (the
`CharZero` instances, needed to state it, are `CurvesJacobian.Cusp.charZero_padic`). -/
theorem mem_arithCusps_iff_map_mem_padic [CharZero K] [CharZero K']
    {C : HypCurve K} {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
    {C' : HypCurve K'} {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (ψ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))))
    (hpr : ∀ x, projGk Ω' C' hc' (Φ x) = ψ (projGk Ω C hc x))
    (I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    I ∈ arithCusps Ω C hc ↔ I.map Φ.toMulEquiv.toMonoidHom ∈ arithCusps Ω' C' hc' := by
  haveI := isSlimGk_padic p (K := K) Ω
  haveI := isSlimGk_padic p' (K := K') Ω'
  haveI := cycNoExponent_padic p (K := K) Ω
  exact mem_arithCusps_iff_map_mem' Φ ψ hpr I

/-- **[AbsTopI] Lemma 4.5 (v) over `p`-adic fields, packaged**: compatible isomorphisms
`Π_U ≃ₜ* Π_{U'}`, `G_K ≃ₜ* G_{K'}` form an isomorphism of cuspidal extensions. -/
def arithmeticExtIso_padic {C : HypCurve K} {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
    {C' : HypCurve K'} {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}
    (Φ : (arithmeticExt_padic p Ω C hc).Pi ≃ₜ* (arithmeticExt_padic p' Ω' C' hc').Pi)
    (ψ : (arithmeticExt_padic p Ω C hc).G ≃ₜ* (arithmeticExt_padic p' Ω' C' hc').G)
    (hpr : ∀ x, (arithmeticExt_padic p' Ω' C' hc').pr (Φ x) =
      ψ ((arithmeticExt_padic p Ω C hc).pr x)) :
    (arithmeticExt_padic p Ω C hc).Iso (arithmeticExt_padic p' Ω' C' hc') :=
  haveI := charZero_padic p (K := K)
  haveI := charZero_padic p' (K := K')
  haveI := isSlimGk_padic p (K := K) Ω
  haveI := isSlimGk_padic p' (K := K') Ω'
  haveI := cycNoExponent_padic p (K := K) Ω
  arithmeticExtIso' Φ ψ hpr

end CurvesJacobian.CuspChar
