/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.UniqueProperMLF

/-!
# Uniqueness for proper hyperbolic curves over number fields (MR7, S8)

The number-field analogue of `LocAn/UniqueProperMLF.lean` (same route: R0 + R5 + R6 with
[LocAn] Thm C for rational points):

* **`CurvesJacobian.LocAn.rationalPointsFixedNF`**: over a number field, a `K`-automorphism of a
  proper hyperbolic curve inducing the identity of `π₁ᵉᵗ(U, pt)` up to `Δ`-conjugation fixes every
  rational point (`SectionBridge.comp_eq_of_conj_numberField`);
* `comp_eq_of_inducedBy_of_finite_numberField`,
  `fromSpecResidueField_comp_eq_of_inducedBy_numberField`: the same for points over finite
  extensions and closed points (base change, R5);
* **`CurvesJacobian.LocAn.innerRigidProper_numberField`** (`Z(G_K) = 1` from `isSlim_Gk`) and
  **`CurvesJacobian.LocAn.uniqueProperNF`**: `RelIsomDGC.UniqueProper K` for every number field `K`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian HypCurve CurvesJacobian.Cusp AffOrbicurve

noncomputable section

namespace CurvesJacobian.LocAn

open WeilCurves.FunctionField in
/-- **Inner automorphisms of proper hyperbolic curves over number fields fix the rational
points** ([LocAn] Thm C via `SectionBridge.comp_eq_of_conj_numberField`). -/
theorem rationalPointsFixedNF (K' : Type u) [Field K'] [NumberField K'] (Ω : Type u) [Field Ω]
    [Algebra K' Ω] [IsSepClosed Ω] (C : HypCurve K') (hC : (C.U : Set C.Xbar)ᶜ = ∅)
    (pt : GeomPt Ω C) (h : KIso C C) (H : InducedBy pt pt h (ContinuousMulEquiv.refl _))
    (x : Spec (.of K') ⟶ C.U.toScheme) (hx : x ≫ C.toSpec = 𝟙 _) : x ≫ h.1.hom = x := by
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
  have e := SectionBridge.comp_eq_of_conj_numberField K' hτ
    (Kummer.genus_baseChange_ne_zero_of_hypCurve K' C hC hτ) hφ γ₂ hγ₂ hγ₂b hx'
  have e' : (x ≫ h.1.hom) ≫ C.U.ι = x ≫ C.U.ι := by
    rw [Category.assoc, hj, ← Category.assoc, e]
  exact (cancel_mono C.U.ι).1 e'

section Assembly

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsSepClosed Ω]

/-- **Points over finite extensions** (number fields): a `K`-automorphism of a proper hyperbolic
curve inducing the identity up to `Δ`-conjugation fixes every `K'`-valued point, `K'/K` finite. -/
theorem comp_eq_of_inducedBy_of_finite_numberField (C : HypCurve K) (hC : (C.U : Set C.Xbar)ᶜ = ∅)
    (pt : GeomPt Ω C) (h : KIso C C) (H : InducedBy pt pt h (ContinuousMulEquiv.refl _))
    (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (x : Spec (.of K') ⟶ C.U.toScheme) (hx : x ≫ C.toSpec = specAlgebraMap K K') :
    x ≫ h.1.hom = x := by
  let ι : K' →ₐ[K] Ω := IsSepClosed.lift
  letI : Algebra K' Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K K' Ω := IsScalarTower.of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  haveI : NumberField K' := NumberField.of_module_finite K K'
  have H' := inducedBy_bcExt K' (bcPt_bcExtPr K' pt) H
  exact comp_eq_of_bcRatPt K' h x hx (rationalPointsFixedNF K' Ω (C.bcExt K')
    (bcExt_proper K' C hC) _ _ H' (bcRatPt K' x hx) (bcRatPt_toSpec K' x hx))

/-- **Closed points** (number fields): such an automorphism fixes every closed point
`Spec κ(x) ⟶ U`. -/
theorem fromSpecResidueField_comp_eq_of_inducedBy_numberField (C : HypCurve K)
    (hC : (C.U : Set C.Xbar)ᶜ = ∅) (pt : GeomPt Ω C) (h : KIso C C)
    (H : InducedBy pt pt h (ContinuousMulEquiv.refl _)) (x : C.U.toScheme) (hx : IsClosed {x}) :
    C.U.toScheme.fromSpecResidueField x ≫ h.1.hom = C.U.toScheme.fromSpecResidueField x := by
  letI : C.U.toScheme.Over (Spec (.of K)) := ⟨C.toSpec⟩
  haveI : LocallyOfFiniteType (C.U.toScheme ↘ Spec (.of K)) :=
    (inferInstance : LocallyOfFiniteType (C.U.ι ≫ (C.Xbar ↘ Spec (.of K))))
  letI := Anabelian.residueFieldAlgebra K C.U.toScheme x
  haveI : Module.Finite K (C.U.toScheme.residueField x) := finite_residueField K hx
  exact comp_eq_of_inducedBy_of_finite_numberField C hC pt h H (C.U.toScheme.residueField x)
    (C.U.toScheme.fromSpecResidueField x)
    (CurvesJacobian.Cusp.fromSpecResidueField_comp_structure K x)

/-- **Inner rigidity of proper hyperbolic curves over number fields.** -/
theorem innerRigidProper_numberField [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    (C : HypCurve K) (hC : (C.U : Set C.Xbar)ᶜ = ∅) : InnerRigidProper Ω C := by
  intro pt h H
  have HI := inducedBy_refl_of_isConjInduced_id pt h H (isSlim_Gk (K := K) Ω).center_eq_bot
  haveI := IsCurveOver.isIntegral K C.Xbar
  letI : C.U.toScheme.Over (Spec (.of K)) := ⟨C.toSpec⟩
  haveI : h.1.hom.IsOver (Spec (.of K)) := ⟨h.2⟩
  haveI : IsReduced C.U.toScheme := isReduced_of_isOpenImmersion C.U.ι
  haveI : LocallyOfFiniteType (C.U.toScheme ↘ Spec (.of K)) :=
    (inferInstance : LocallyOfFiniteType (C.U.ι ≫ (C.Xbar ↘ Spec (.of K))))
  haveI : IsSeparated (C.U.toScheme ↘ Spec (.of K)) :=
    (inferInstance : IsSeparated (C.U.ι ≫ (C.Xbar ↘ Spec (.of K))))
  haveI : JacobsonSpace C.U.toScheme :=
    LocallyOfFiniteType.jacobsonSpace (C.U.toScheme ↘ Spec (.of K))
  refine KIso.ext (Iso.ext ?_)
  exact eq_id_of_fromSpecResidueField_closedPoints (S := Spec (.of K)) fun x hx ↦
    fromSpecResidueField_comp_eq_of_inducedBy_numberField C hC pt h HI x hx

end Assembly

/-- **Uniqueness for proper curves over every number field** (a statement). -/
def UniqueProperNF : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], RelIsomDGC.UniqueProper K

/-- **Uniqueness for proper hyperbolic curves over every number field**:
`RelIsomDGC.UniqueProper K` for every number field `K`. -/
theorem uniqueProperNF : UniqueProperNF.{u} := fun K _ _ ↦
  uniqueProper_of_innerRigidProper K fun Ω _ _ _ C hC ↦ by
    haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
    haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
    exact innerRigidProper_numberField C hC

end CurvesJacobian.LocAn
