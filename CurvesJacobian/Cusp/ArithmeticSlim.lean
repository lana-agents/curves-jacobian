/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BaseChange
import CurvesJacobian.Galois.SurfaceGroupAnyPoint
import CurvesJacobian.Galois.FiberFunctorIso
import CurvesJacobian.Galois.ChartOfOpen
import Belyi.Anabelian.LocAn

/-!
# `Π_U ↠ G_K` for an affine hyperbolic curve over a number field: `G_K` and `Δ_U` are slim

Let `K` be a number field, `Ω` an algebraic closure, and `C` a hyperbolic curve over `K`
(`Belyi.Anabelian.HypCurve`: `U ⊆ X̄`) with at least one cusp (`U ≠ X̄`, so `U` is affine,
`CurvesJacobian.Cusp.isAffineOpen_U`). With `R = Γ(X̄, U)`, an `Ω`-rational base point `x` of
`U_Ω = Spec (Ω ⊗[K] R)` (`CurvesJacobian.Cusp.basePoint`), `Π_U = π₁ᵉᵗ(U, x)` and
`G_K = π₁ᵉᵗ(Spec K) ≅ Gal(Ω/K)`:

* `CurvesJacobian.Cusp.projGk_surjective`: `Π_U ↠ G_K` is surjective (`U` is geometrically
  irreducible);
* `CurvesJacobian.Cusp.isSlim_Gk`: `G_K` is slim (number fields, local-class-field-theory);
* `CurvesJacobian.Cusp.kerProjGkEquiv`: `Δ_U = ker(Π_U ↠ G_K) ≃ₜ* Π̂_{g,r}` where `(g, r)` is
  the type of `U_Ω ⊆ X̄_Ω` (homotopy exact sequence, change of base point, and the comparison
  `π₁ᵉᵗ((X ∖ D)_{ℚ̄}) ≃ₜ* Π̂_{g,r}` of `CurvesJacobian.Galois.BelyiSurfaceGroup`);
* `CurvesJacobian.Cusp.isSlim_Delta`, `CurvesJacobian.Cusp.Delta_ne_bot`: if `U_Ω ⊆ X̄_Ω` is
  hyperbolic, `Δ_U` is slim and nontrivial (`Π̂_{g,r}` is free profinite of rank `2g + r - 1 ≥ 2`).

The hyperbolicity hypothesis `hhyp` is stated for the geometric type `(g(X̄_Ω), #(X̄_Ω ∖ U_Ω))`;
it follows from `HypCurve.hyperbolic` (the type over `K`) by
`CurvesJacobian.Cusp.isHyperbolic_baseChange` (`CurvesJacobian.Cusp.Hyperbolic`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite ProfiniteGrp.ProfiniteCompletion
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Slimness and nontriviality of `Π̂_{g,r}` in universe `u` -/

section Surface

variable {g r : ℕ}

/-- `Π̂_{g,r+1}` (in universe `u`) is the free profinite group on `2g + r` generators. -/
def surfaceCompletionEquivFreeHat (g r : ℕ) :
    completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g (r + 1)))) ≃ₜ*
      FreeHat (ULift.{u} (Pi1.SurfaceGen g r)) :=
  completionCongr (freeGroupEquivSurfaceGroup g r (Equiv.refl _)).symm

/-- **`Π̂_{g,r}` is slim** for `(g, r)` hyperbolic with `r ≥ 1` (universe `u` version of
`Pi1.SurfaceGroup.isSlim`). -/
theorem isSlim_surfaceCompletion (hr : 0 < r) (h : Pi1.SurfaceGroup.IsHyperbolic g r) :
    IsSlim (completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g r)))) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  refine IsSlim.of_continuousMulEquiv (surfaceCompletionEquivFreeHat g r).symm ?_
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hr2 : 1 < r := by unfold Pi1.SurfaceGroup.IsHyperbolic at h; omega
    exact isSlim_completion_freeGroup (a := ULift.up (Pi1.SurfaceGen.c ⟨0, by omega⟩))
      (b := ULift.up (Pi1.SurfaceGen.c ⟨1, hr2⟩)) (by simp)
  · exact isSlim_completion_freeGroup (a := ULift.up (Pi1.SurfaceGen.a ⟨0, hg⟩))
      (b := ULift.up (Pi1.SurfaceGen.b ⟨0, hg⟩)) (by simp)

/-- The profinite completion of a free group on a nonempty set is nontrivial. -/
theorem exists_ne_one_freeHat {α : Type u} (a : α) : ∃ z : FreeHat α, z ≠ 1 := by
  let f : FreeGroup α →* ULift.{u} (Multiplicative (ZMod 2)) :=
    FreeGroup.lift fun _ ↦ ULift.up (Multiplicative.ofAdd 1)
  refine ⟨etaFn (GrpCat.of (FreeGroup α)) (FreeGroup.of a), fun h ↦ ?_⟩
  have := liftFinite_eta f (FreeGroup.of a)
  rw [h, map_one] at this
  have h1 : (ULift.up (Multiplicative.ofAdd (1 : ZMod 2)) : ULift (Multiplicative (ZMod 2))) ≠ 1 :=
    fun h' ↦ by
      have := congrArg (fun z ↦ Multiplicative.toAdd z.down) h'
      simp at this
  exact h1 (by simpa [f] using this.symm)

/-- **`Π̂_{g,r}` is nontrivial** for `r ≥ 1` and `2g + r ≥ 2`. -/
theorem exists_ne_one_surfaceCompletion (hr : 0 < r) (h : Pi1.SurfaceGroup.IsHyperbolic g r) :
    ∃ z : completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g r))), z ≠ 1 := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hgen : Nonempty (Pi1.SurfaceGen g r) := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · have hr1 : 0 < r := by unfold Pi1.SurfaceGroup.IsHyperbolic at h; omega
      exact ⟨Pi1.SurfaceGen.c ⟨0, hr1⟩⟩
    · exact ⟨Pi1.SurfaceGen.a ⟨0, hg⟩⟩
  obtain ⟨z, hz⟩ := exists_ne_one_freeHat (ULift.up hgen.some : ULift.{u} (Pi1.SurfaceGen g r))
  refine ⟨(surfaceCompletionEquivFreeHat g r).symm z, fun h' ↦ hz ?_⟩
  have := congrArg (surfaceCompletionEquivFreeHat g r) h'
  simpa using this

end Surface

/-- Equal subgroups are isomorphic topological groups. -/
def continuousSubgroupCongr {G : Type*} [Group G] [TopologicalSpace G] {H H' : Subgroup G}
    (h : H = H') : H ≃ₜ* H' := by
  subst h
  exact ContinuousMulEquiv.refl _

/-! ### The arithmetic fundamental group of an affine hyperbolic curve -/

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

include hc in
/-- **The open `U` of a hyperbolic curve with a cusp is affine** (a chart `π⁻¹ D₊(X₁)` of a
rational function with poles exactly at the cusps, `CurvesJacobian.exists_chartOne_eq`). -/
lemma isAffineOpen_U : IsAffineOpen C.U := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  have hne : C.U ≠ ⊤ := fun h ↦ by
    obtain ⟨x, hx⟩ := hc
    exact hx (h ▸ trivial)
  obtain ⟨τ, hτ, hU⟩ := exists_chartOne_eq K C.U C.cusps_finite hne
  rw [hU]
  exact isAffineOpen_chartOne hτ

include hc in
lemma isIntegral_specTensor : IsIntegral (Spec (.of (Ω ⊗[K] Γ(C.Xbar, C.U)))) :=
  isIntegral_spec_tensor K Ω (isAffineOpen_U C hc) C.nonempty

include hc in
lemma isIntegral_specSections : IsIntegral (Spec Γ(C.Xbar, C.U)) := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  exact isIntegral_spec_sections (isAffineOpen_U C hc)

variable [IsAlgClosed Ω]

include hc in
lemma exists_basePoint :
    ∃ x : Spec (.of Ω) ⟶ Spec (.of (Ω ⊗[K] Γ(C.Xbar, C.U))),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] Γ(C.Xbar, C.U)))) =
        Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) ∧
      (x ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  haveI := isIntegral_specTensor Ω C hc
  haveI : IsDomain (Ω ⊗[K] Γ(C.Xbar, C.U)) := by
    have := (affine_isIntegral_iff (.of (Ω ⊗[K] Γ(C.Xbar, C.U)))).1 inferInstance
    exact this
  exact exists_rationalPoint K Ω (isAffineOpen_U C hc)

/-- An `Ω`-rational base point of `U_Ω = Spec (Ω ⊗[K] Γ(X̄, U))`. -/
def basePoint : Spec (.of Ω) ⟶ Spec (.of (Ω ⊗[K] Γ(C.Xbar, C.U))) :=
  (exists_basePoint Ω C hc).choose

lemma basePoint_spec₁ :
    basePoint Ω C hc ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] Γ(C.Xbar, C.U)))) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) :=
  (exists_basePoint Ω C hc).choose_spec.1

lemma basePoint_spec₂ :
    (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
  (exists_basePoint Ω C hc).choose_spec.2

/-- **The projection `Π_U → G_K`**, with `Π_U = π₁ᵉᵗ(U, x)` (`U = Spec Γ(X̄, U)`) and
`G_K = π₁ᵉᵗ(Spec K, Spec Ω)`. -/
def projGk : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) →ₜ*
    π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
    (basePoint_spec₂ Ω C hc)

include hc in
/-- **`Π_U ↠ G_K` is surjective**: `U` is geometrically irreducible over `K`. -/
theorem projGk_surjective : Function.Surjective (projGk Ω C hc) := by
  haveI := isIntegral_specSections C hc
  have hU := isAffineOpen_U C hc
  haveI hsurj : Surjective ((hU.isoSpec.inv ≫ C.U.ι) ≫ (C.Xbar ↘ Spec (.of K))) :=
    ⟨fun y ↦ ⟨(Classical.arbitrary (Spec Γ(C.Xbar, C.U))), Subsingleton.elim _ _⟩⟩
  haveI : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)))) := by
    rw [← isoSpec_inv_ι_structure K hU, ← Category.assoc]
    infer_instance
  exact fundamentalGroupMap_surjective_of_geometricallyConnected _ _

variable [Algebra.IsAlgebraic K Ω]

omit [NumberField K] in
/-- `Ω` is an algebraic closure of `K` (hence Galois over `K`, `char K = 0`). -/
lemma isAlgClosure_of_isAlgebraic : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **`G_K = π₁ᵉᵗ(Spec K) ≅ Gal(Ω/K)` is slim** for a number field `K`. -/
theorem isSlim_Gk : IsSlim π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := by
  let e : (Ω ≃ₐ[K] Ω) ≃ₜ* π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    { mulEquivAutFiber K Ω with
      continuous_toFun := (isHomeomorph_mulEquivAutFiber K Ω).continuous
      continuous_invFun := (isHomeomorph_mulEquivAutFiber K Ω).homeomorph.symm.continuous }
  exact (isSlim_galoisGroup_numberField K Ω).of_continuousMulEquiv e

/-- `ker(Π_U → G_K)` is the kernel of `toGaloisGroup`. -/
lemma ker_projGk : (projGk Ω C hc).toMonoidHom.ker =
    (toGaloisGroup (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
      (basePoint_spec₂ Ω C hc)).ker := by
  ext γ
  simp only [MonoidHom.mem_ker, toGaloisGroup, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  rfl

/-- **`Δ_U ≃ₜ* π₁ᵉᵗ(U_Ω)`**: the kernel of `Π_U ↠ G_K` is the geometric fundamental group
`π₁ᵉᵗ(U_Ω, x)`, `U_Ω ⊆ X̄_Ω` the base change of `U`. -/
def kerProjGkEquivGeom : (projGk Ω C hc).toMonoidHom.ker ≃ₜ*
    π₁ᵉᵗ(basePoint Ω C hc ≫ (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).hom) :=
  haveI := isIntegral_specSections C hc
  haveI := isIntegral_specTensor Ω C hc
  (continuousSubgroupCongr (ker_projGk Ω C hc)).trans <|
    (geomFundamentalGroupEquivKer (basePoint Ω C hc) (basePoint_spec₁ Ω C hc)
      (basePoint_spec₂ Ω C hc)).symm.trans <|
    fundamentalGroupEquivOfIso _ _

include hc in
/-- **`Δ_U ≃ₜ* Π̂_{g,r}`** for `(g, r)` the type of `U_Ω ⊆ X̄_Ω`. -/
theorem nonempty_kerProjGk_equiv :
    Nonempty ((projGk Ω C hc).toMonoidHom.ker ≃ₜ*
      completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup
        (curveGenus Ω (baseChange K Ω C.Xbar)).toNat
        (Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _)))))) := by
  haveI := IsCurveOver.isIntegral Ω (baseChange K Ω C.Xbar)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  have hne := nonempty_baseChangeOpen K Ω C.nonempty
  haveI : Nonempty (baseChangeOpen K Ω C.U) := hne.to_subtype
  obtain ⟨Φ⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup
    (k := Ω) (X := baseChange K Ω C.Xbar) (baseChangeOpen K Ω C.U)
    (compl_finite_baseChangeOpen K Ω C.nonempty) (compl_nonempty_baseChangeOpen K Ω hc)
    (basePoint Ω C hc ≫ (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).hom)
  exact ⟨(kerProjGkEquivGeom Ω C hc).trans Φ⟩

include hc in
/-- **`Δ_U` is slim** if `U_Ω ⊆ X̄_Ω` is hyperbolic. -/
theorem isSlim_Delta (hhyp : Pi1.SurfaceGroup.IsHyperbolic
    (curveGenus Ω (baseChange K Ω C.Xbar)).toNat
    (Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _))) :
    IsSlim (projGk Ω C hc).toMonoidHom.ker := by
  obtain ⟨e⟩ := nonempty_kerProjGk_equiv Ω C hc
  have hr : 0 < Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _) :=
    haveI := (compl_finite_baseChangeOpen K Ω C.nonempty).to_subtype
    Nat.card_pos_iff.2 ⟨(compl_nonempty_baseChangeOpen K Ω hc).to_subtype, inferInstance⟩
  exact (isSlim_surfaceCompletion hr hhyp).of_continuousMulEquiv e.symm

include hc in
/-- **`Δ_U` is nontrivial** if `U_Ω ⊆ X̄_Ω` is hyperbolic. -/
theorem Delta_ne_bot (hhyp : Pi1.SurfaceGroup.IsHyperbolic
    (curveGenus Ω (baseChange K Ω C.Xbar)).toNat
    (Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _))) :
    (projGk Ω C hc).toMonoidHom.ker ≠ ⊥ := by
  obtain ⟨e⟩ := nonempty_kerProjGk_equiv Ω C hc
  have hr : 0 < Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _) :=
    haveI := (compl_finite_baseChangeOpen K Ω C.nonempty).to_subtype
    Nat.card_pos_iff.2 ⟨(compl_nonempty_baseChangeOpen K Ω hc).to_subtype, inferInstance⟩
  obtain ⟨z, hz⟩ := exists_ne_one_surfaceCompletion hr hhyp
  intro hbot
  apply hz
  have h1 : e.symm z = 1 := by
    exact Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hbot _ (e.symm z).2)
  have h2 := congrArg e h1
  rwa [ContinuousMulEquiv.apply_symm_apply, map_one] at h2

end CurvesJacobian.Cusp
