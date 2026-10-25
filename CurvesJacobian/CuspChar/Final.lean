/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Arith
import CurvesJacobian.CuspChar.Centraliser
import CurvesJacobian.CuspChar.Delta

/-!
# [AbsTopI] Lemma 4.5 (v) for affine hyperbolic curves over number fields

Let `U`, `U'` be affine hyperbolic curves over number fields `K`, `K'` (with at least one cusp),
`Π_U ↠ G_K`, `Π_{U'} ↠ G_{K'}` their arithmetic fundamental groups
(`CurvesJacobian.Cusp.arithmeticExt`). **Every pair of topological isomorphisms
`Φ : Π_U ≃ₜ* Π_{U'}`, `ψ : G_K ≃ₜ* G_{K'}` compatible with the projections maps the cuspidal
inertia groups of `Π_U` exactly onto those of `Π_{U'}`**
(`CurvesJacobian.CuspChar.mem_arithCusps_iff_map_mem`), hence is a
`Belyi.Anabelian.CuspidalExt.Iso` (`CurvesJacobian.CuspChar.arithmeticExtIso`).
([AbsTopI] Lemma 4.5 (v): `Topics in Absolute Anabelian Geometry I.txt` l.3335.)

The proof is the group-theoretic route of `MR3-plan.md`: numerical cuspidality from the weight
identity (`CurvesJacobian.CuspChar.mem_deltaCusps_iff_of_cuspWeightIdentity`), with the
centraliser property of cuspidal inertia (`CurvesJacobian.CuspChar.mem_inertia_of_commute`) and
the cyclotomic character at `l = 3` (`CurvesJacobian.CuspChar.arithCycChar_noExponent`).

**Debt** (explicit theorem arguments `hW`, `hW'`): the cusp weight identity
`CurvesJacobian.CuspChar.CuspWeightIdentity` of `U` and `U'` at `l = 3` (Kummer theory of the
covers of `U_{K̄}`, Weil pairing, Riemann–Hurwitz; step B1/B2 of `MR3-plan.md`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  CurvesJacobian.Cusp

universe u

noncomputable section

namespace CurvesJacobian.CuspChar

variable {K : Type u} [Field K] [CharZero K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  {hc : (C.U : Set C.Xbar)ᶜ.Nonempty}
  {K' : Type u} [Field K'] [CharZero K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω']
  [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] {C' : HypCurve K'}
  {hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty}

variable (Ω C hc) in
/-- The mod-`3^k` cyclotomic characters of `Π_U`, typed on `π₁ᵉᵗ(U)`. -/
abbrev cyc3 [IsSlimGk K Ω] (k : ℕ) :
    π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) →* (ZMod (3 ^ k))ˣ :=
  arithCycChar Ω C hc 3 k

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] in
lemma map_deltaU_eq (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (ψ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))))
    (hpr : ∀ x, projGk Ω' C' hc' (Φ x) = ψ (projGk Ω C hc x)) :
    (deltaU Ω C hc).map Φ.toMulEquiv.toMonoidHom = deltaU Ω' C' hc' := by
  ext y
  obtain ⟨x, rfl⟩ := Φ.surjective y
  rw [Subgroup.mem_map_equiv]
  change projGk Ω C hc (Φ.symm (Φ x)) = 1 ↔ projGk Ω' C' hc' (Φ x) = 1
  rw [Φ.symm_apply_apply]
  rw [hpr x]
  constructor
  · intro h1
    rw [h1, map_one]
  · intro h1
    apply ψ.injective
    rw [h1, map_one]

/-- **[AbsTopI] Lemma 4.5 (v)** for affine hyperbolic curves over number fields: isomorphisms
`Π_U ≃ₜ* Π_{U'}` over `G_K ≃ₜ* G_{K'}` preserve the cuspidal inertia groups (debt: the cusp
weight identities `hW`, `hW'`). -/
theorem mem_arithCusps_iff_map_mem [IsSlimGk K Ω] [IsSlimGk K' Ω'] [CycNoExponent K Ω 3]
    (Φ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω' C' hc' ≫ baseChangeSpec K' Ω' Γ(C'.Xbar, C'.U)))
    (ψ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≃ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω'))))
    (hpr : ∀ x, projGk Ω' C' hc' (Φ x) = ψ (projGk Ω C hc x))
    (hW : CuspWeightIdentity (deltaU Ω C hc) (deltaCusps Ω C hc) 3 (eulerU Ω C)
      (cyc3 Ω C hc))
    (hW' : CuspWeightIdentity (deltaU Ω' C' hc') (deltaCusps Ω' C' hc') 3 (eulerU Ω' C')
      (cyc3 Ω' C' hc'))
    (I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    I ∈ arithCusps Ω C hc ↔ I.map Φ.toMulEquiv.toMonoidHom ∈ arithCusps Ω' C' hc' := by
  have hD := map_deltaU_eq Φ ψ hpr
  have hcent : ∀ (g r : ℕ), 0 < r → Pi1.SurfaceGroup.IsHyperbolic g r → ∀ (j : Fin r)
      (x z : Pi1.ProfiniteSurfaceGroup g r), x ∈ Pi1.SurfaceGroup.inertia (g := g) j → x ≠ 1 →
        z * x = x * z → z ∈ Pi1.SurfaceGroup.inertia (g := g) j :=
    fun _ _ hr h j _ _ hx hx1 hz ↦ mem_inertia_of_commute hr h j hx hx1 hz
  have key := mem_deltaCusps_iff_of_cuspWeightIdentity hcent Φ hD hW hW'
    (fun A B hA hB N hN ↦ arithCycChar_noExponent Ω C hc (l := 3) A B hA hB N hN)
  by_cases hI : I ≤ deltaU Ω C hc
  · have hI' : I.map Φ.toMulEquiv.toMonoidHom ≤ deltaU Ω' C' hc' := by
      rw [← hD]
      exact Subgroup.map_mono hI
    rw [mem_arithCusps_iff_mem_deltaCusps Ω C hc hI,
      mem_arithCusps_iff_mem_deltaCusps Ω' C' hc' hI', key]
    have he : (I.subgroupOf (deltaU Ω C hc)).map (resD Φ hD).toMulEquiv.toMonoidHom =
        (I.map Φ.toMulEquiv.toMonoidHom).subgroupOf (deltaU Ω' C' hc') := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        refine ⟨⟨x, hI hx⟩, Subgroup.mem_subgroupOf.2 hx, ?_⟩
        exact Subtype.ext hxy
    rw [he]
  · constructor
    · intro h
      exact absurd (arithCusps_le Ω C hc h) hI
    · intro h
      exfalso
      apply hI
      intro x hx
      have h1 : Φ x ∈ deltaU Ω' C' hc' :=
        arithCusps_le Ω' C' hc' h (Subgroup.mem_map_of_mem _ hx)
      rw [← hD] at h1
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
      rwa [← Φ.injective hyx]

/-- **[AbsTopI] Lemma 4.5 (v), packaged**: compatible isomorphisms `Π_U ≃ₜ* Π_{U'}`,
`G_K ≃ₜ* G_{K'}` form an isomorphism of cuspidal extensions (debt: `hW`, `hW'`). -/
def arithmeticExtIso [IsSlimGk K Ω] [IsSlimGk K' Ω'] [CycNoExponent K Ω 3]
    (Φ : (arithmeticExt Ω C hc).Pi ≃ₜ* (arithmeticExt Ω' C' hc').Pi)
    (ψ : (arithmeticExt Ω C hc).G ≃ₜ* (arithmeticExt Ω' C' hc').G)
    (hpr : ∀ x, (arithmeticExt Ω' C' hc').pr (Φ x) = ψ ((arithmeticExt Ω C hc).pr x))
    (hW : CuspWeightIdentity (deltaU Ω C hc) (deltaCusps Ω C hc) 3 (eulerU Ω C)
      (cyc3 Ω C hc))
    (hW' : CuspWeightIdentity (deltaU Ω' C' hc') (deltaCusps Ω' C' hc') 3 (eulerU Ω' C')
      (cyc3 Ω' C' hc')) :
    (arithmeticExt Ω C hc).Iso (arithmeticExt Ω' C' hc') where
  pi := Φ
  g := ψ
  pr_comm := hpr
  cusps_map := mem_arithCusps_iff_map_mem Φ ψ hpr hW hW'

end CurvesJacobian.CuspChar
