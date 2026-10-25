/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.BcInner
import CurvesJacobian.LocAn.SectionBridgeAut
import CurvesJacobian.LocAn.GenusBaseChange

/-!
# Uniqueness for proper hyperbolic curves over finite extensions of `ℚ_p` (MR7, S8)

* `CurvesJacobian.LocAn.conjData_of_isIso`, `CurvesJacobian.LocAn.conjData_of_iso_fiber`: the
  data "`γ` realises `φ_*` as the identity up to conjugation, and `γ` lies over the base" moves
  along an isomorphism of schemes, and to any other geometric point (with a different field):
  conjugate by a path `δ : fiber ξ₀ ≅ fiber η` (fibre functors of a connected scheme are
  isomorphic) and track the images in the base.
* **`CurvesJacobian.LocAn.rationalPointsFixedMLF`**: `RationalPointsFixedMLF p`, from
  `SectionBridge.comp_eq_of_conj_padic` ([LocAn] Thm C) applied to `X̄ ≅ U` and the geometric
  generic point of the curve model.
* **`CurvesJacobian.LocAn.innerRigidProper_padic`**: inner rigidity of proper hyperbolic curves
  over finite extensions of `ℚ_p`, and **`CurvesJacobian.LocAn.uniqueProperMLF`**: the uniqueness
  half of the rel-isom-DGC for proper curves over every finite extension of `ℚ_p`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian HypCurve CurvesJacobian.Cusp AffOrbicurve

noncomputable section

namespace CurvesJacobian.LocAn

/-! ### Transport of the conjugation data -/

section Transport

variable {U X S : Scheme.{u}} {Ω L : Type u} [Field Ω] [IsSepClosed Ω] [Field L] [IsSepClosed L]

/-- **Along an isomorphism**: if `j : U ≅ X` intertwines `h` and `φ`, the conjugation data of
`h` at `ξ₀` give conjugation data of `φ` at `ξ₀ ≫ j`. -/
theorem conjData_of_isIso (j : U ⟶ X) [IsIso j] {h : U ⟶ U} {φ : X ⟶ X} (hj : h ≫ j = j ≫ φ)
    {sU : U ⟶ S} {sX : X ⟶ S} (hs : j ≫ sX = sU) {ξ₀ : Spec (.of Ω) ⟶ U}
    {ζ : Spec (.of Ω) ⟶ S} (γ : fiber (ξ₀ ≫ h) ≅ fiber ξ₀)
    (hγ : ∀ σ : π₁ᵉᵗ(ξ₀), σ = γ.conjAut (fundamentalGroupMap h rfl σ))
    (h₁ : (ξ₀ ≫ h) ≫ sU = ζ) (h₂ : ξ₀ ≫ sU = ζ) (hγb : fiberIsoMap sU h₁ h₂ γ = Iso.refl _)
    (k₁ : ((ξ₀ ≫ j) ≫ φ) ≫ sX = ζ) (k₂ : (ξ₀ ≫ j) ≫ sX = ζ) :
    ∃ γ' : fiber ((ξ₀ ≫ j) ≫ φ) ≅ fiber (ξ₀ ≫ j),
      (∀ σ : π₁ᵉᵗ(ξ₀ ≫ j), σ = γ'.conjAut (fundamentalGroupMap φ rfl σ)) ∧
      fiberIsoMap sX k₁ k₂ γ' = Iso.refl _ := by
  have e1 : (ξ₀ ≫ h) ≫ j = (ξ₀ ≫ j) ≫ φ := by rw [Category.assoc, hj, Category.assoc]
  refine ⟨fiberIsoMap j e1 rfl γ, fun σ ↦ ?_, ?_⟩
  · obtain ⟨τ, rfl⟩ := (fundamentalGroupMap_bijective_of_isIso j (rfl : ξ₀ ≫ j = ξ₀ ≫ j)).2 σ
    have a1 : ξ₀ ≫ j ≫ φ = (ξ₀ ≫ j) ≫ φ := (Category.assoc _ _ _).symm
    have a2 : ξ₀ ≫ h ≫ j = (ξ₀ ≫ j) ≫ φ := by rw [← Category.assoc, e1]
    have hφτ : (fundamentalGroupMap φ rfl (fundamentalGroupMap j rfl τ) : _ ≅ _) =
        fiberIsoMap j e1 e1 (fiberIsoMap h rfl rfl τ) := by
      rw [fundamentalGroupMap_eq_fiberIsoMap, fundamentalGroupMap_eq_fiberIsoMap,
        fiberIsoMap_fiberIsoMap j φ rfl rfl rfl rfl a1 a1, fiberIsoMap_congr hj.symm _ _ a2 a2,
        ← fiberIsoMap_fiberIsoMap h j rfl rfl e1 e1 a2 a2]
    have hτ : (τ : fiber ξ₀ ≅ fiber ξ₀) = γ.symm ≪≫ fiberIsoMap h rfl rfl τ ≪≫ γ := by
      have := hγ τ
      rw [Iso.conjAut_apply, fundamentalGroupMap_eq_fiberIsoMap] at this
      exact this
    change (fundamentalGroupMap j rfl τ : _ ≅ _) =
      (fiberIsoMap j e1 rfl γ).conjAut (fundamentalGroupMap φ rfl (fundamentalGroupMap j rfl τ))
    rw [Iso.conjAut_apply, hφτ, fundamentalGroupMap_eq_fiberIsoMap, ← fiberIsoMap_symm,
      ← fiberIsoMap_trans, ← fiberIsoMap_trans, ← hτ]
  · have b1 : (ξ₀ ≫ h) ≫ j ≫ sX = ζ := by rw [hs]; exact h₁
    have b2 : ξ₀ ≫ j ≫ sX = ζ := by rw [hs]; exact h₂
    rw [fiberIsoMap_fiberIsoMap j sX e1 rfl k₁ k₂ b1 b2, fiberIsoMap_congr hs b1 b2 h₁ h₂, hγb]

/-- **Change of the geometric point** (possibly to a different field): conjugation data of `φ`
at `ξ₀` give conjugation data of `φ` at every geometric point `η` of a connected scheme. -/
theorem conjData_of_iso_fiber [ConnectedSpace X] {φ : X ⟶ X} {sX : X ⟶ S} (hφ : φ ≫ sX = sX)
    {ξ₀ : Spec (.of Ω) ⟶ X} (η : Spec (.of L) ⟶ X) {ζ : Spec (.of Ω) ⟶ S}
    (γ : fiber (ξ₀ ≫ φ) ≅ fiber ξ₀)
    (hγ : ∀ σ : π₁ᵉᵗ(ξ₀), σ = γ.conjAut (fundamentalGroupMap φ rfl σ))
    (h₁ : (ξ₀ ≫ φ) ≫ sX = ζ) (h₂ : ξ₀ ≫ sX = ζ) (hγb : fiberIsoMap sX h₁ h₂ γ = Iso.refl _)
    (k₁ : (η ≫ φ) ≫ sX = η ≫ sX) :
    ∃ γ' : fiber (η ≫ φ) ≅ fiber η,
      (∀ σ : π₁ᵉᵗ(η), σ = γ'.conjAut (fundamentalGroupMap φ rfl σ)) ∧
      fiberIsoMap sX k₁ rfl γ' = Iso.refl _ := by
  obtain ⟨δ⟩ : Nonempty (fiber ξ₀ ≅ fiber η) := nonempty_iso_of_fiberFunctor _ _
  set D : fiber (ξ₀ ≫ φ) ≅ fiber (η ≫ φ) := fiberIsoMap φ rfl rfl δ with hD
  refine ⟨D.symm ≪≫ γ ≪≫ δ, fun σ' ↦ ?_, ?_⟩
  · have hφσ : ((fundamentalGroupMap φ rfl (δ ≪≫ σ' ≪≫ δ.symm : π₁ᵉᵗ(ξ₀))) : _ ≅ _) =
        D ≪≫ fiberIsoMap φ rfl rfl σ' ≪≫ D.symm := by
      rw [fundamentalGroupMap_eq_fiberIsoMap, fiberIsoMap_trans φ rfl rfl rfl,
        fiberIsoMap_trans φ rfl rfl rfl, fiberIsoMap_symm φ rfl rfl]
    have e : γ.symm ≪≫ (D ≪≫ fiberIsoMap φ rfl rfl σ' ≪≫ D.symm) ≪≫ γ =
        δ ≪≫ σ' ≪≫ δ.symm := by
      have := hγ (δ ≪≫ σ' ≪≫ δ.symm : π₁ᵉᵗ(ξ₀))
      rw [Iso.conjAut_apply, hφσ] at this
      exact this.symm
    change (σ' : fiber η ≅ fiber η) = (D.symm ≪≫ γ ≪≫ δ).conjAut (fundamentalGroupMap φ rfl σ')
    rw [Iso.conjAut_apply, fundamentalGroupMap_eq_fiberIsoMap]
    calc (σ' : fiber η ≅ fiber η) = δ.symm ≪≫ (δ ≪≫ σ' ≪≫ δ.symm) ≪≫ δ := by simp
      _ = δ.symm ≪≫ (γ.symm ≪≫ (D ≪≫ fiberIsoMap φ rfl rfl σ' ≪≫ D.symm) ≪≫ γ) ≪≫ δ := by
          rw [e]
      _ = _ := by simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  · have c1 : ξ₀ ≫ φ ≫ sX = ζ := by rw [hφ]; exact h₂
    have c2 : η ≫ φ ≫ sX = η ≫ sX := by rw [hφ]
    rw [fiberIsoMap_trans sX k₁ h₁ rfl, fiberIsoMap_trans sX h₁ h₂ rfl, hγb, Iso.refl_trans,
      fiberIsoMap_symm sX h₁ k₁, hD, fiberIsoMap_fiberIsoMap φ sX rfl rfl h₁ k₁ c1 c2,
      fiberIsoMap_congr hφ c1 c2 h₂ rfl, Iso.symm_self_id]

end Transport

/-! ### Rational points, inner rigidity and uniqueness over finite extensions of `ℚ_p` -/

lemma isIso_ι_of_eq_top {X : Scheme.{u}} {V : X.Opens} (hV : V = ⊤) : IsIso V.ι := by
  subst hV
  exact inferInstanceAs (IsIso X.topIso.hom)

variable (p : ℕ) [Fact p.Prime]

open WeilCurves.FunctionField in
/-- **Step L1/L2: inner automorphisms of proper hyperbolic curves over finite extensions of
`ℚ_p` fix the rational points** ([LocAn] Thm C via `SectionBridge.comp_eq_of_conj_padic`). -/
theorem rationalPointsFixedMLF : RationalPointsFixedMLF.{u} p := by
  intro K' _ _ _ Ω _ _ _ C hC pt h H x hx
  haveI := charZero_of_padic p K'
  haveI := IsCurveOver.isIntegral K' C.Xbar
  have hU : C.U = ⊤ :=
    SetLike.coe_injective ((Set.compl_empty_iff.mp hC).trans TopologicalSpace.Opens.coe_top.symm)
  haveI : IsIso C.U.ι := isIso_ι_of_eq_top hU
  obtain ⟨τ, hτ⟩ := exists_transcendental (k := K') (K := C.Xbar.functionField)
  haveI : IsGalois (K₀ K' (coordT τ)) (FFClosure C.Xbar) :=
    isGalois_K₀_algebraicClosure (k := K') τ hτ
  let φ : C.Xbar ⟶ C.Xbar := inv C.U.ι ≫ h.1.hom ≫ C.U.ι
  have hj : h.1.hom ≫ C.U.ι = C.U.ι ≫ φ := by simp [φ]
  have hφ : φ ≫ (C.Xbar ↘ Spec (.of K')) = C.Xbar ↘ Spec (.of K') := by
    change (inv C.U.ι ≫ h.1.hom ≫ C.U.ι) ≫ (C.Xbar ↘ Spec (.of K')) = _
    rw [Category.assoc, Category.assoc,
      show C.U.ι ≫ (C.Xbar ↘ Spec (.of K')) = C.toSpec from rfl, h.2, HypCurve.toSpec,
      IsIso.inv_hom_id_assoc]
  obtain ⟨γ, hp, hγ⟩ := H
  rw [isPathOverBase_iff] at hp
  have k₂ : (pt.x ≫ C.U.ι) ≫ (C.Xbar ↘ Spec (.of K')) =
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω)) := by
    rw [Category.assoc]
    exact pt.over
  have k₁ : ((pt.x ≫ C.U.ι) ≫ φ) ≫ (C.Xbar ↘ Spec (.of K')) =
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω)) := by
    rw [Category.assoc, hφ, k₂]
  obtain ⟨γ₁, hγ₁, hγ₁b⟩ := conjData_of_isIso C.U.ι hj
    (rfl : C.U.ι ≫ (C.Xbar ↘ Spec (.of K')) = C.toSpec) γ (fun σ ↦ hγ σ)
    (comp_over_of_kHom pt h.2) pt.over hp k₁ k₂
  obtain ⟨γ₂, hγ₂, hγ₂b⟩ := conjData_of_iso_fiber hφ
    (geometricGenericPoint (curveGaloisData K' hτ) C.Xbar (curveEquivL K' hτ)) γ₁ hγ₁ k₁ k₂
    hγ₁b (SectionBridge.comp_toSpec hφ _)
  have hx' : (x ≫ C.U.ι) ≫ (C.Xbar ↘ Spec (.of K')) = 𝟙 _ := by
    rw [Category.assoc]
    exact hx
  have e := SectionBridge.comp_eq_of_conj_padic K' hτ p
    (Kummer.genus_baseChange_ne_zero_of_hypCurve K' C hC hτ) hφ γ₂ hγ₂ hγ₂b hx'
  have e' : (x ≫ h.1.hom) ≫ C.U.ι = x ≫ C.U.ι := by
    rw [Category.assoc, hj, ← Category.assoc, e]
  exact (cancel_mono C.U.ι).1 e'

/-- **Inner rigidity of proper hyperbolic curves over finite extensions of `ℚ_p`.** -/
theorem innerRigidProper_padic {K : Type u} [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra.IsAlgebraic K Ω] [IsGalois K Ω] (C : HypCurve K) (hC : (C.U : Set C.Xbar)ᶜ = ∅) :
    InnerRigidProper Ω C :=
  innerRigidProper_padic_of_rationalPointsFixed (rationalPointsFixedMLF p) C hC

/-- **Uniqueness for proper hyperbolic curves over every finite extension of `ℚ_p`**:
`RelIsomDGC.UniqueProper L` for every finite extension `L` of `ℚ_p`. -/
theorem uniqueProperMLF : UniqueProperMLF.{u} p :=
  uniqueProperMLF_of_innerRigidProper p fun L _ _ _ Ω _ _ _ C hC ↦ by
    haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω)
    haveI := charZero_of_padic p L
    haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
    exact innerRigidProper_padic p C hC

end CurvesJacobian.LocAn
