/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspTransport

/-!
# Preimages of cuspidal inertia groups along finite étale maps (MR8.5, cusp compatibility of models)

For affine hyperbolic curves `C` over `K` and `C'` over `K' ⊇ K` (with cusps) and a finite étale
`F : Spec Γ(U') ⟶ Spec Γ(U)` over `Spec K' ⟶ Spec K`, the preimage under
`coverPiHom F : Π_{U'} ↪ Π_U` of a cuspidal inertia group of `Π_U` is a cuspidal inertia group of
`Π_{U'}` (`CurvesJacobian.Cusp.comap_coverPiHom_mem_arithCusps`): it contains, with finite index,
a cuspidal inertia group `J'` (`CurvesJacobian.Cusp.exists_arithCusps_coverHom_le`), lies in
`Δ_{U'}`, and `J'` is commensurably terminal in `Δ_{U'}` ([AbsTopI] Lemma 4.1 (i)).

This is the input for transporting the cusp compatibility of geometric models along the cover
step `CurvesJacobian.Cusp.GeomModel.ofSub`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open scoped Pointwise

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {K' : Type u} [Field K'] [NumberField K'] [Algebra K K'] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra.IsAlgebraic K' Ω]
  (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
  (F : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale F]
  (hF : F ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K')))

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [NumberField K'] [Algebra K K'] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra.IsAlgebraic K' Ω] in
/-- Elements of a subgroup commensurate it. -/
lemma mem_commensurator_of_mem {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H) :
    g ∈ Subgroup.Commensurable.commensurator H := by
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct g • H = H := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro hx
      simpa [mul_assoc] using H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    · intro hx
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg
  rw [this]

include hF in
/-- `coverPiHom⁻¹(Δ_U) = Δ_{U'}`. -/
lemma comap_coverPiHom_ker_projGk_le :
    (projGk Ω C hc).toMonoidHom.ker.comap (coverPiHom Ω C hc C' hc' F).toMonoidHom ≤
      (projGk Ω C' hc').toMonoidHom.ker := by
  intro x hx
  have h1 : (arithmeticExt Ω C hc).pr (coverPiHom Ω C hc C' hc' F x) = 1 := hx
  rw [pr_coverPiHom Ω C hc C' hc' F hF] at h1
  exact (coverι_injective Ω C hc C' hc' F hF).eq_iff.1 (h1.trans (map_one _).symm)

include hF in
/-- **The preimage of a cuspidal inertia group of `Π_U` in `Π_{U'}` is a cuspidal inertia
group.** -/
theorem comap_coverPiHom_mem_arithCusps {I} (hI : I ∈ arithCusps Ω C hc) :
    I.comap (coverPiHom Ω C hc C' hc' F).toMonoidHom ∈ arithCusps Ω C' hc' := by
  set f := (coverPiHom Ω C hc C' hc' F).toMonoidHom
  have hinj : Function.Injective f := coverPiHom_injective Ω C hc C' hc' F
  obtain ⟨J, hJ, hJI, hfin⟩ := exists_arithCusps_coverHom_le Ω C hc C' hc' F hI
  have hle : J ≤ I.comap f := Subgroup.map_le_iff_le_comap.1 hJI
  have hfin' : J.relIndex (I.comap f) ≠ 0 := by
    have h1 : J.map f ≤ f.range ⊓ I := le_inf (Subgroup.map_le_range f J) hJI
    have h2 := Subgroup.relIndex_mul_relIndex (J.map f) (f.range ⊓ I) I h1 inf_le_right
    have h3 : (J.map f).relIndex (f.range ⊓ I) ≠ 0 := left_ne_zero_of_mul (h2.symm ▸ hfin)
    have e1 := Subgroup.relIndex_map_map_of_injective J (I.comap f) hinj
    have e2 : (I.comap f).map f = f.range ⊓ I := Subgroup.map_comap_eq f I
    exact e1 ▸ e2.symm ▸ h3
  have hcomm : Subgroup.Commensurable J (I.comap f) :=
    ⟨hfin', (Subgroup.relIndex_eq_one.2 hle).symm ▸ one_ne_zero⟩
  suffices h : I.comap f = J by rw [h]; exact hJ
  refine le_antisymm ?_ hle
  rw [← commensurator_inf_of_mem_arithCusps Ω C' hc' hJ, Subgroup.Commensurable.eq hcomm]
  exact le_inf (fun g hg ↦ mem_commensurator_of_mem hg)
    ((Subgroup.comap_mono (arithCusps_le Ω C hc hI)).trans
      (comap_coverPiHom_ker_projGk_le Ω C hc C' hc' F hF))

end CurvesJacobian.Cusp
