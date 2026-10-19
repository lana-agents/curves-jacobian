/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GeomModel
import CurvesJacobian.Cusp.CoverCusps
import CurvesJacobian.Cusp.FillElemOp

/-!
# Isomorphisms of schemes preserve the cuspidal inertia groups (MR8.5, option (A4))

For affine hyperbolic curves `C₁`, `C₂` over a number field `M ⊆ Ω` (with a cusp), every
isomorphism of schemes `F : Spec Γ(U₁) ≅ Spec Γ(U₂)` — **not necessarily over `Spec M`** — maps
the cuspidal inertia groups of `Π_{U₁}` onto those of `Π_{U₂}` (for any isomorphism
`φ : Π_{U₁} ≃ Π_{U₂}` induced by `F` up to a change of base point, `IsConjInduced F φ`). The
cuspidal inertia groups are intrinsic to the ring `Γ(U)`: they are the inertia groups of the
places of an algebraic closure of `Frac Γ(U)` which contain the algebraic numbers but not `Γ(U)`
(`CurvesJacobian.Cusp.mem_arithCusps_iff`), and the comparison of
`CurvesJacobian.Cusp.exists_arithCusps_map_coverPiHom` uses only the scheme map `F` (it is applied
here with `K = K' = M`).

* `CurvesJacobian.Cusp.eq_of_le_of_mem_arithCusps`: a cuspidal inertia group of finite index in
  another one equals it (commensurable terminality, [AbsTopI] Lemma 4.1 (i)).
* **`CurvesJacobian.Cusp.map_mem_arithCusps_of_isConjInduced`**: `F` maps cuspidal inertia groups
  to cuspidal inertia groups.
* **`CurvesJacobian.Cusp.map_twistPiEquiv_mem_arithCusps_iff`**: base change along `Spec α`
  matches the cusps (`Π_{U^α} ≃ Π_U`, `CurvesJacobian.Cusp.twistPiEquiv`).
* **`CurvesJacobian.Cusp.GeomModel.map_conjPi_mem_arithCusps_iff`**: the semilinear action of
  `N_A(ι(Π_Y))` on a geometric model preserves the cuspidal inertia groups of `Π_Y`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open scoped Pointwise

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Curves

variable {M : Type u} [Field M] [NumberField M] (Ω : Type u) [Field Ω] [Algebra M Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic M Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **A cuspidal inertia group of finite index in a cuspidal inertia group equals it.** -/
theorem eq_of_le_of_mem_arithCusps (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    {J J'} (hJ : J ∈ arithCusps Ω C hc) (hJ' : J' ∈ arithCusps Ω C hc) (hle : J ≤ J')
    (hfin : J.relIndex J' ≠ 0) : J = J' := by
  refine le_antisymm hle ?_
  have hcomm : Subgroup.Commensurable J J' :=
    ⟨hfin, by rw [Subgroup.relIndex_eq_one.2 hle]; exact one_ne_zero⟩
  rw [← commensurator_inf_of_mem_arithCusps Ω C hc hJ, Subgroup.Commensurable.eq hcomm]
  refine le_inf (fun g hg ↦ ?_) (arithCusps_le Ω C hc hJ')
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct g • J' = J' := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro hx
      simpa [mul_assoc] using J'.mul_mem (J'.mul_mem hg hx) (J'.inv_mem hg)
    · intro hx
      exact J'.mul_mem (J'.mul_mem (J'.inv_mem hg) hx) hg
  rw [this]

variable {C₁ C₂ : HypCurve M} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

omit [Algebra.IsAlgebraic M Ω] [CharZero Ω] in
/-- `IsConjInduced` maps of an isomorphism and its inverse compose to an inner automorphism. -/
lemma exists_conj_of_isConjInduced_inv (F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U))
    {φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) →
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U))}
    {ψ : π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)) →
      π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U))}
    (hφ : IsConjInduced F.hom φ) (hψ : IsConjInduced F.inv ψ) :
    ∃ t, ∀ σ, ψ (φ σ) = t * σ * t⁻¹ := by
  have h := IsConjInduced.congr_hom F.hom_inv_id (hφ.comp hψ)
  obtain ⟨γ, hγ⟩ := (isConjInduced_iff _ (Category.comp_id _) _).1 h
  refine ⟨γ, fun σ ↦ (hγ σ).trans ?_⟩
  change γ.conjAut (fundamentalGroupMap (𝟙 _) (Category.comp_id _) σ) = _
  rw [fundamentalGroupMap_id, Aut_conjAut_eq]
  rfl

/-- `π₁ᵉᵗ(F)` with the change of base point of `coverPiHom`, for an isomorphism `F`. -/
abbrev isoPiHom (F : Spec Γ(C₁.Xbar, C₁.U) ⟶ Spec Γ(C₂.Xbar, C₂.U)) :
    π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) →ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)) :=
  coverPiHom Ω C₂ hc₂ C₁ hc₁ F

lemma isConjInduced_isoPiHom (F : Spec Γ(C₁.Xbar, C₁.U) ⟶ Spec Γ(C₂.Xbar, C₂.U)) :
    IsConjInduced F (isoPiHom Ω (hc₁ := hc₁) (hc₂ := hc₂) F) :=
  ⟨coverFib Ω C₂ hc₂ C₁ hc₁ F, fun _ ↦ rfl⟩

/-- **An isomorphism of schemes `Spec Γ(U₁) ≅ Spec Γ(U₂)` maps cuspidal inertia groups to
cuspidal inertia groups** (through `π₁ᵉᵗ(F)` and the change of base point `coverFib`). -/
theorem map_isoPiHom_mem_arithCusps (F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U))
    {J} (hJ : J ∈ arithCusps Ω C₁ hc₁) :
    J.map (isoPiHom Ω (hc₁ := hc₁) (hc₂ := hc₂) F.hom).toMonoidHom ∈ arithCusps Ω C₂ hc₂ := by
  haveI : IsFiniteEtale F.hom := {}
  haveI : IsFiniteEtale F.inv := {}
  set c := isoPiHom Ω (hc₁ := hc₁) (hc₂ := hc₂) F.hom
  set d := isoPiHom Ω (hc₁ := hc₂) (hc₂ := hc₁) F.inv
  obtain ⟨I, hI, hJI, hfin⟩ := exists_arithCusps_map_coverPiHom Ω C₂ hc₂ C₁ hc₁ F.hom hJ
  obtain ⟨J', hJ', hIJ', hfin'⟩ := exists_arithCusps_map_coverPiHom Ω C₁ hc₁ C₂ hc₂ F.inv hI
  obtain ⟨s, hs⟩ := exists_conj_of_isConjInduced_inv Ω F (isConjInduced_isoPiHom Ω F.hom)
    (isConjInduced_isoPiHom Ω F.inv)
  have hdinj : Function.Injective d := coverPiHom_injective Ω C₁ hc₁ C₂ hc₂ F.inv
  have hJ₀ : (J.map c.toMonoidHom).map d.toMonoidHom = J.map (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.map_map]
    exact congrArg (fun f ↦ Subgroup.map f J) (MonoidHom.ext fun σ ↦ hs σ)
  have hle : (J.map c.toMonoidHom).map d.toMonoidHom ≤ I.map d.toMonoidHom :=
    Subgroup.map_mono hJI
  have hfin₀ : ((J.map c.toMonoidHom).map d.toMonoidHom).relIndex (I.map d.toMonoidHom) ≠ 0 := by
    rwa [Subgroup.relIndex_map_map_of_injective _ _ hdinj]
  have heq : (J.map c.toMonoidHom).map d.toMonoidHom = J' := by
    rw [hJ₀] at hle hfin₀ ⊢
    exact eq_of_le_of_mem_arithCusps Ω C₁ hc₁ (map_conj_mem_arithCusps Ω C₁ hc₁ hJ s) hJ'
      (hle.trans hIJ') (Subgroup.relIndex_ne_zero_trans hfin₀ hfin')
  have hId : I.map d.toMonoidHom = (J.map c.toMonoidHom).map d.toMonoidHom :=
    le_antisymm (heq ▸ hIJ') hle
  rw [Subgroup.map_injective hdinj hId] at hI
  exact hI

/-- **`IsConjInduced` maps of isomorphisms of schemes preserve the cuspidal inertia groups.** -/
theorem map_mem_arithCusps_of_isConjInduced
    (F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U))
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) →*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)))
    (hφ : IsConjInduced F.hom φ) {J} (hJ : J ∈ arithCusps Ω C₁ hc₁) :
    J.map φ ∈ arithCusps Ω C₂ hc₂ := by
  obtain ⟨t, ht⟩ := (isConjInduced_iff_exists_conj F.hom (coverFib Ω C₂ hc₂ C₁ hc₁ F.hom) φ).1 hφ
  have e : J.map φ = (J.map (isoPiHom Ω (hc₁ := hc₁) (hc₂ := hc₂) F.hom).toMonoidHom).map
      (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_map]
    exact congrArg (fun f ↦ Subgroup.map f J) (MonoidHom.ext fun σ ↦ ht σ)
  rw [e]
  exact map_conj_mem_arithCusps Ω C₂ hc₂ (map_isoPiHom_mem_arithCusps Ω F hJ) t

/-- **The cuspidal inertia groups correspond** under an `IsConjInduced` isomorphism. -/
theorem map_mem_arithCusps_iff_of_isConjInduced
    (F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U))
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≃*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)))
    (hφ : IsConjInduced F.hom φ) {J} :
    J.map φ.toMonoidHom ∈ arithCusps Ω C₂ hc₂ ↔ J ∈ arithCusps Ω C₁ hc₁ := by
  refine ⟨fun h ↦ ?_, map_mem_arithCusps_of_isConjInduced Ω F φ.toMonoidHom hφ⟩
  have := map_mem_arithCusps_of_isConjInduced Ω F.symm φ.symm.toMonoidHom
    (IsConjInduced.symm_of_iso F φ hφ) h
  have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
    ext σ
    simp
  rwa [Subgroup.map_map, e, Subgroup.map_id] at this

end Curves

section Twist

variable {M : Type u} [Field M] [NumberField M] (Ω : Type u) [Field Ω] [Algebra M Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic M Ω] [CharZero Ω] (α : M ≃+* M)

/-- **Base change along `Spec α` matches the cusps**: `Π_{U^α} ≃ Π_U` maps the cuspidal inertia
groups of the Galois twist `C^α` onto those of `C`. -/
theorem map_twistPiEquiv_mem_arithCusps_iff (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    {J} : J.map (twistPiEquiv Ω α C hc).toMulEquiv.toMonoidHom ∈ arithCusps Ω C hc ↔
      J ∈ arithCusps Ω (C.twist α) (twist_cusp α C hc) :=
  map_mem_arithCusps_iff_of_isConjInduced Ω (twistSpecIso α C hc)
    (twistPiEquiv Ω α C hc).toMulEquiv (isConjInduced_twistPiEquiv Ω α C hc)

end Twist

namespace GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A)

/-- **The semilinear action preserves the cusps**: for `g ∈ N_A(ι(Π_Y))`, conjugation by `g`
maps the cuspidal inertia groups of `Π_Y` onto cuspidal inertia groups (it is induced by the
semilinear automorphism `F_g` of `Spec Γ(U_Y)`, `GeomModel.exists_semilinearAut`). -/
theorem map_conjPi_mem_arithCusps_iff (hDGC : RelIsomDGC D.M) (g : D.Nrm) {J} :
    J.map (D.conjPi g).toMulEquiv.toMonoidHom ∈ arithCusps Ω D.Y D.hY ↔
      J ∈ arithCusps Ω D.Y D.hY := by
  obtain ⟨-, -, F, -, HF⟩ := D.exists_semilinearAut hDGC g
  exact map_mem_arithCusps_iff_of_isConjInduced Ω F (D.conjPi g).toMulEquiv HF

end GeomModel

end CurvesJacobian.Cusp
