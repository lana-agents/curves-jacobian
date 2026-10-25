/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Assembly
import CurvesJacobian.CuspChar.Cyclotomic
import CurvesJacobian.Cusp.ArithmeticExt

/-!
# The cyclotomic character of `Π_U` for an affine hyperbolic curve

For the arithmetic extension `Π_U ↠ G_K` of `CurvesJacobian.Cusp.arithmeticExt`
(`G_K = π₁ᵉᵗ(Spec K) ≅ Gal(Ω/K)`, `K` of characteristic zero with slim `G_K`),
`CurvesJacobian.CuspChar.arithCycChar Ω C hc l k` is the mod-`l^k` cyclotomic character composed
with `Π_U ↠ G_K`. Main result (`CurvesJacobian.CuspChar.arithCycChar_noExponent`): if the
cyclotomic character of `G_K` has no finite exponent on open subgroups
(`CurvesJacobian.CuspChar.CycNoExponent`: number fields and `p`-adic fields at `l = 3`), then
neither has that of `Π_U` — the hypothesis `hinf` of
`CurvesJacobian.CuspChar.isNumCusp_of_cuspWeightIdentity` (step B3 of [AbsTopI] Lemma 4.5 (v)).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite CurvesJacobian.Cusp

universe u

noncomputable section

namespace CurvesJacobian.CuspChar

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [CharZero K] [CharZero Ω] in
/-- `G_K = π₁ᵉᵗ(Spec K) ≃ₜ* Gal(Ω/K)`. -/
def gkEquivGal : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ* (Ω ≃ₐ[K] Ω) :=
  ContinuousMulEquiv.symm
    { mulEquivAutFiber K Ω with
      continuous_toFun := (isHomeomorph_mulEquivAutFiber K Ω).continuous
      continuous_invFun := (isHomeomorph_mulEquivAutFiber K Ω).homeomorph.symm.continuous }

/-- The composite `Π_U ↠ G_K ≅ Gal(Ω/K)`. -/
def piToGal [IsSlimGk K Ω] : (arithmeticExt Ω C hc).Pi →ₜ* (Ω ≃ₐ[K] Ω) :=
  ContinuousMonoidHom.comp
    { toMonoidHom := (gkEquivGal Ω).toMulEquiv.toMonoidHom
      continuous_toFun := (gkEquivGal Ω).continuous } (projGk Ω C hc)

/-- The **mod-`l^k` cyclotomic character of `Π_U`**. -/
def arithCycChar [IsSlimGk K Ω] (l k : ℕ) [NeZero l] :
    (arithmeticExt Ω C hc).Pi →* (ZMod (l ^ k))ˣ :=
  (cycChar K Ω l k).comp (piToGal Ω C hc).toMonoidHom

/-- **The cyclotomic character of `Π_U` has no finite exponent on open subgroups** (given the
same for `G_K`, `CurvesJacobian.CuspChar.CycNoExponent`). -/
theorem arithCycChar_noExponent [IsSlimGk K Ω] {l : ℕ} [NeZero l] [CycNoExponent K Ω l]
    (A B : Subgroup (arithmeticExt Ω C hc).Pi) (hA : IsOpen (A : Set (arithmeticExt Ω C hc).Pi))
    (hB : IsOpen (B : Set (arithmeticExt Ω C hc).Pi)) (N : ℕ)
    (hN : ∀ σ ∈ A ⊓ B, ∀ k, arithCycChar Ω C hc l k σ ^ N = 1) : N = 0 := by
  by_contra hN0
  set f := piToGal Ω C hc
  have hfs : Function.Surjective f := fun σ ↦ by
    obtain ⟨x, hx⟩ := projGk_surjective Ω C hc ((gkEquivGal Ω).symm σ)
    refine ⟨x, ?_⟩
    change gkEquivGal Ω (projGk Ω C hc x) = σ
    rw [hx]
    exact (gkEquivGal Ω).apply_symm_apply σ
  set H := A ⊓ B
  have hHo : IsOpen (H : Set (arithmeticExt Ω C hc).Pi) := hA.inter hB
  -- the image of `H` is an open subgroup of `Gal(Ω/K)`
  set U := H.map f.toMonoidHom
  have hUcl : IsClosed (U : Set (Ω ≃ₐ[K] Ω)) := by
    have hHc : IsCompact (H : Set (arithmeticExt Ω C hc).Pi) :=
      (Subgroup.isClosed_of_isOpen H hHo).isCompact
    rw [Subgroup.coe_map]
    exact (hHc.image f.continuous).isClosed
  have hUfi : U.FiniteIndex := by
    have : Finite ((arithmeticExt Ω C hc).Pi ⧸ H) := Subgroup.quotient_finite_of_isOpen _ hHo
    have hH0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact ⟨fun h ↦ hH0 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd H hfs))⟩
  have hUo : IsOpen (U : Set (Ω ≃ₐ[K] Ω)) := Subgroup.isOpen_of_isClosed_of_finiteIndex U hUcl
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω (U : Set (Ω ≃ₐ[K] Ω))).1
    (hUo.mem_nhds U.one_mem)
  obtain ⟨k, σ, hσ, hne⟩ := CycNoExponent.exists_ne (l := l) E (Nat.pos_of_ne_zero hN0)
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hEU hσ)
  exact hne (hN x hx k)

end CurvesJacobian.CuspChar
