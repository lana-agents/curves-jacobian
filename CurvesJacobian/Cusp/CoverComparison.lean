/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithmeticCover
import CurvesJacobian.Galois.BelyiSurfaceGroup

/-!
# The chain object of a cover is the arithmetic `π₁` of a hyperbolic curve over `K'`

[AbsTopI] Definition 4.2 (`Topics in Absolute Anabelian Geometry I.txt`): an `X̃/X`-chain
`X₀ ⇝ X₁ ⇝ …` consists of stacks `X_j` over finite extensions `k_j ⊇ k` (condition (1X),
l.2863–2866), whose groups `Π_j` surject onto open subgroups `G_j ⊆ G` (condition (1Π),
l.2980–2982) with slim nontrivial kernels `Δ_j` ((2Π), l.2983–2986); by [AbsTopI]
Remark 4.2.1 (l.3083–3092) a chain of schemes gives a `Π`-chain. To *iterate* operations of
type `⋏` we identify the chain object of a cover with the arithmetic fundamental group of a
hyperbolic curve over a finite extension `K'` of `K`.

Setting: `C : HypCurve K` with a cusp, `f : V ⟶ U = Spec Γ(X̄, U)` connected finite étale with a
geometric point `η` over the base point of `Π_U`, `C' : HypCurve K'` with a cusp
(`K'/K` a finite extension inside `Ω`), and `e : U' = Spec Γ(X̄', U') ≅ V` over `Spec K`.

* `CurvesJacobian.Cusp.galoisMap`: `ι : G_{K'} → G_K` induced by `Spec K' ⟶ Spec K`, injective
  (`galoisMap_injective`: `Spec K' ⟶ Spec K` is finite étale).
* `CurvesJacobian.Cusp.coverPiEquiv`: **`Π_{U'} ≃ₜ*` the group of `coverChainObj`**: transport
  along `e`, a change of base point (an isomorphism of fibre functors of `V`), and
  `coverChainObjEquiv`.
* `CurvesJacobian.Cusp.toG_coverPiEquiv`: compatibility with the projections to `G_K`, up to
  the conjugation by `coverConj ∈ G_K` coming from the change of base point:
  `toG (coverPiEquiv γ) = g · ι (pr' γ) · g⁻¹`.
* `CurvesJacobian.Cusp.map_Delta_coverPiEquiv`: `coverPiEquiv` maps `Δ_{U'}` onto `Δ` of the
  chain object (`Π_{U'} ∩ Δ_U = Δ_{U'}`).
* `CurvesJacobian.Cusp.map_pr_coverSubgroup`: the image of `coverSubgroup` in `G_K` is the
  conjugate `g · ι(G_{K'}) · g⁻¹`; `map_pr_coverSubgroup_of_comp`: it is exactly `ι(G_{K'})` if
  `η` induces the given embedding `K' ⊆ Ω`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Galois

variable (K K' Ω : Type u) [Field K] [Field K'] [Field Ω] [Algebra K K'] [Algebra K' Ω]
  [Algebra K Ω] [IsScalarTower K K' Ω]

lemma specMap_algebraMap_tower :
    Spec.map (CommRingCat.ofHom (algebraMap K' Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap K K'))
      = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable [IsSepClosed Ω]

/-- `ι : G_{K'} = π₁ᵉᵗ(Spec K') → G_K = π₁ᵉᵗ(Spec K)`, induced by `Spec K' ⟶ Spec K`. -/
def galoisMap : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K' Ω))) →ₜ*
    π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K K')))
    (specMap_algebraMap_tower K K' Ω)

omit [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] [IsSepClosed Ω] in
/-- `Spec K' ⟶ Spec K` is finite étale for an extension of number fields. -/
lemma isFiniteEtale_specMap_numberField [NumberField K] [NumberField K'] :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap K K'))) := by
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : Algebra.IsSeparable K K' := inferInstance
  haveI : Algebra.FormallyEtale K K' := Algebra.FormallyEtale.of_isSeparable K K'
  haveI : Algebra.FinitePresentation K K' :=
    (Algebra.FinitePresentation.of_finiteType (R := K) (A := K')).mp inferInstance
  haveI : Algebra.Etale K K' := ⟨inferInstance, inferInstance⟩
  rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
  exact ⟨⟩

/-- **`ι : G_{K'} → G_K` is injective** (`Gal(Ω/K') ⊆ Gal(Ω/K)`). -/
theorem galoisMap_injective [NumberField K] [NumberField K'] :
    Function.Injective (galoisMap K K' Ω) := by
  haveI := isFiniteEtale_specMap_numberField K K'
  exact fundamentalGroupMap_injective_of_isFiniteEtale' _ _ (specMap_algebraMap_tower K K' Ω)

end Galois

/-- For an isomorphism `α : F ≅ F`, `autContinuousMulEquivOfIso α` is conjugation by `α`. -/
lemma autContinuousMulEquivOfIso_self {C : Type*} [Category C] {F : C ⥤ FintypeCat.{u}}
    (α : Aut F) (σ : Aut F) : autContinuousMulEquivOfIso α σ = α * σ * α⁻¹ := by
  change α.conjAut σ = _
  rw [Iso.conjAut_apply]
  rfl

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

section Surj

variable (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
include hc in
/-- `π₁ᵉᵗ(U) → π₁ᵉᵗ(Spec K)` is surjective at **any** geometric point of `U = Spec Γ(X̄, U)`. -/
theorem fundamentalGroupMap_structure_surjective {y : Spec (.of Ω) ⟶ Spec Γ(C.Xbar, C.U)}
    (hy : y ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    Function.Surjective (fundamentalGroupMap _ hy) := by
  haveI := isIntegral_specSections C hc
  have hU := isAffineOpen_U C hc
  haveI hsurj : Surjective ((hU.isoSpec.inv ≫ C.U.ι) ≫ (C.Xbar ↘ Spec (.of K))) :=
    ⟨fun y ↦ ⟨(Classical.arbitrary (Spec Γ(C.Xbar, C.U))), Subsingleton.elim _ _⟩⟩
  haveI : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)))) := by
    rw [← isoSpec_inv_ι_structure K hU, ← Category.assoc]
    infer_instance
  exact fundamentalGroupMap_surjective_of_geometricallyConnected _ _

end Surj

variable (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  {V : Scheme.{u}} (f : V ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale f] [ConnectedSpace V]
  (η : Spec (.of Ω) ⟶ V) (h : η ≫ f = basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
  {K' : Type u} [Field K'] [NumberField K'] [Algebra K K'] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra.IsAlgebraic K' Ω] (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
  (e : Spec Γ(C'.Xbar, C'.U) ≅ V)
  (he : e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K')))

omit [NumberField K] [Algebra.IsAlgebraic K Ω] [CharZero Ω] [IsFiniteEtale f] [ConnectedSpace V]
  [Algebra.IsAlgebraic K' Ω] in
include he in
lemma coverBase_spec :
    ((basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) ≫ e.hom) ≫
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
  (Category.assoc _ e.hom _).trans ((congrArg (_ ≫ ·) he).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap K K')))
      (basePoint_spec₂ Ω C' hc')).trans (specMap_algebraMap_tower K K' Ω))))

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] [IsFiniteEtale f] [ConnectedSpace V] in
include h in
lemma coverPt_spec :
    η ≫ f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans (basePoint_spec₂ Ω C hc))

/-- An isomorphism of fibre functors of `V` from the image of the base point of `Π_{U'}` to `η`
(any two fibre functors of a Galois category are isomorphic). -/
def coverFiberIso :
    fiber ((basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) ≫ e.hom) ≅ fiber η :=
  (nonempty_iso_of_fiberFunctor _ _).some

/-- **`Π_{U'} ≃ₜ*` the group of the chain object of the cover `V ≅ U'`**: `π₁ᵉᵗ(U', x') ≃ₜ*
`π₁ᵉᵗ(V, x' ≫ e) ≃ₜ* π₁ᵉᵗ(V, η) ≃ₜ* coverSubgroup`. -/
def coverPiEquiv : (arithmeticExt Ω C' hc').Pi ≃ₜ* (coverChainObj Ω C hc f η h).grp :=
  ((fundamentalGroupEquivOfIso e (basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))).trans
    (autContinuousMulEquivOfIso (coverFiberIso Ω η C' hc' e))).trans
    (coverChainObjEquiv Ω C hc f η h)

include he in
/-- The element `g ∈ G_K` by which the change of base point conjugates (`toG_coverPiEquiv`). -/
def coverConj : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  fiberIsoMap (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
    (coverBase_spec Ω C f C' hc' e he) (coverPt_spec Ω C hc f η h) (coverFiberIso Ω η C' hc' e)

lemma toG_coverChainObjEquiv (y : π₁ᵉᵗ(η)) :
    (coverChainObj Ω C hc f η h).toG (coverChainObjEquiv Ω C hc f η h y) =
      fundamentalGroupMap (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
        (coverPt_spec Ω C hc f η h) y := by
  rw [fundamentalGroupMap_comp f _ h (basePoint_spec₂ Ω C hc)]
  rfl

/-- **Compatibility of `coverPiEquiv` with the projections to `G_K`**: for `γ ∈ Π_{U'}`,
`toG (coverPiEquiv γ) = g · ι (pr' γ) · g⁻¹` with `g = coverConj` (the inner automorphism comes
from the change of base point). -/
theorem toG_coverPiEquiv (γ : (arithmeticExt Ω C' hc').Pi) :
    (coverChainObj Ω C hc f η h).toG (coverPiEquiv Ω C hc f η h C' hc' e γ) =
      coverConj Ω C hc f η h C' hc' e he *
        galoisMap K K' Ω ((arithmeticExt Ω C' hc').pr γ) *
          (coverConj Ω C hc f η h C' hc' e he)⁻¹ := by
  let F := f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)))
  let x' := basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)
  have h1 : (x' ≫ e.hom) ≫ F = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
    coverBase_spec Ω C f C' hc' e he
  have h2 : η ≫ F = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := coverPt_spec Ω C hc f η h
  have hA := toG_coverChainObjEquiv Ω C hc f η h
    (autContinuousMulEquivOfIso (coverFiberIso Ω η C' hc' e)
      (fundamentalGroupEquivOfIso e x' γ))
  have hB := fundamentalGroupMap_autContinuousMulEquivOfIso F h1 h2
    (coverFiberIso Ω η C' hc' e) (fundamentalGroupEquivOfIso e x' γ)
  have hC : fundamentalGroupMap F h1 (fundamentalGroupEquivOfIso e x' γ) =
      galoisMap K K' Ω ((arithmeticExt Ω C' hc').pr γ) := by
    have h3 : x' ≫ e.hom ≫ F = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
      (Category.assoc _ _ _).symm.trans h1
    have h4 : x' ≫ Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K K')) =
          Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := he ▸ h3
    have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp e.hom F rfl h1 h3) γ
    have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp _ _ (basePoint_spec₂ Ω C' hc')
      (specMap_algebraMap_tower K K' Ω) h4) γ
    rw [fundamentalGroupMap_congr he h3 h4] at c1
    exact c1.symm.trans c2
  change (coverChainObj Ω C hc f η h).toG (coverChainObjEquiv Ω C hc f η h
    (autContinuousMulEquivOfIso (coverFiberIso Ω η C' hc' e)
      (fundamentalGroupEquivOfIso e x' γ))) = _
  rw [hA, hB, hC, autContinuousMulEquivOfIso_self]
  rfl

include he in
/-- `coverPiEquiv γ ∈ Δ` of the chain object iff `γ ∈ Δ_{U'}`. -/
theorem coverPiEquiv_mem_Delta_iff (γ : (arithmeticExt Ω C' hc').Pi) :
    coverPiEquiv Ω C hc f η h C' hc' e γ ∈ (coverChainObj Ω C hc f η h).Delta ↔
      γ ∈ (arithmeticExt Ω C' hc').Delta := by
  change (coverChainObj Ω C hc f η h).toG (coverPiEquiv Ω C hc f η h C' hc' e γ) = 1 ↔
    (arithmeticExt Ω C' hc').pr γ = 1
  rw [toG_coverPiEquiv Ω C hc f η h C' hc' e he]
  exact conj_eq_one_iff.trans (map_eq_one_iff _ (galoisMap_injective K K' Ω))

include he in
/-- **`Π_{U'} ∩ Δ_U = Δ_{U'}`**: `coverPiEquiv` maps `Δ_{U'}` onto `Δ` of the chain object. -/
theorem map_Delta_coverPiEquiv :
    (arithmeticExt Ω C' hc').Delta.map
        (coverPiEquiv Ω C hc f η h C' hc' e).toMulEquiv.toMonoidHom =
      (coverChainObj Ω C hc f η h).Delta := by
  ext z
  rw [Subgroup.mem_map_equiv, ← coverPiEquiv_mem_Delta_iff Ω C hc f η h C' hc' e he]
  exact iff_of_eq (congrArg (· ∈ (coverChainObj Ω C hc f η h).Delta)
    ((coverPiEquiv Ω C hc f η h C' hc' e).apply_symm_apply z))

/-- **The image of `π₁ᵉᵗ(V) ⊆ Π_U` in `G_K` is `g · ι(G_{K'}) · g⁻¹`** (`g = coverConj`). -/
theorem map_pr_coverSubgroup :
    (coverSubgroup f η h :
        Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))).map
        (projGk Ω C hc).toMonoidHom =
      (galoisMap K K' Ω).toMonoidHom.range.map
        (MulAut.conj (coverConj Ω C hc f η h C' hc' e he)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let y : (coverChainObj Ω C hc f η h).grp := ⟨x, hx⟩
    let γ := (coverPiEquiv Ω C hc f η h C' hc' e).symm y
    have h1 := toG_coverPiEquiv Ω C hc f η h C' hc' e he γ
    have h2 := congrArg (coverChainObj Ω C hc f η h).toG
      ((coverPiEquiv Ω C hc f η h C' hc' e).apply_symm_apply y)
    exact ⟨_, ⟨_, rfl⟩, (h2.symm.trans h1).symm⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨γ, rfl⟩ := (arithmeticExt Ω C' hc').pr_surjective w
    have := toG_coverPiEquiv Ω C hc f η h C' hc' e he γ
    exact ⟨_, (coverPiEquiv Ω C hc f η h C' hc' e γ).2, this⟩

omit [Algebra.IsAlgebraic K' Ω] in
include hc he hc' in
/-- **The image of `π₁ᵉᵗ(V) ⊆ Π_U` in `G_K` is `ι(G_{K'})`** when `η` induces the given
embedding `K' ⊆ Ω`. -/
theorem map_pr_coverSubgroup_of_comp
    (hη : η ≫ e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω))) :
    (coverSubgroup f η h :
        Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))).map
        (projGk Ω C hc).toMonoidHom =
      (galoisMap K K' Ω).toMonoidHom.range := by
  let F := f ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)))
  let pK' := Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U)))
  let t := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have hF : F = e.inv ≫ pK' ≫ t := by
    rw [← he, Iso.inv_hom_id_assoc]
  have h2 : η ≫ F = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := coverPt_spec Ω C hc f η h
  have hη' : (η ≫ e.inv) ≫ pK' = Spec.map (CommRingCat.ofHom (algebraMap K' Ω)) :=
    (Category.assoc _ _ _).trans hη
  have h5 : η ≫ e.inv ≫ pK' ≫ t = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := hF ▸ h2
  -- `pr ∘ π₁(f) = ι ∘ π₁(pK') ∘ π₁(e⁻¹)`
  have key : ∀ y : π₁ᵉᵗ(η), projGk Ω C hc (fundamentalGroupMap f h y) =
      galoisMap K K' Ω (fundamentalGroupMap pK' hη' (fundamentalGroupMap e.inv rfl y)) := by
    intro y
    have c0 := toG_coverChainObjEquiv Ω C hc f η h y
    have c1 := DFunLike.congr_fun (fundamentalGroupMap_congr hF h2 h5) y
    have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp e.inv (pK' ≫ t) rfl
      ((Category.assoc _ _ _).trans h5) h5) y
    have c3 := DFunLike.congr_fun (fundamentalGroupMap_comp pK' t hη'
      (specMap_algebraMap_tower K K' Ω) ((Category.assoc _ _ _).trans h5))
      (fundamentalGroupMap e.inv rfl y)
    exact c0.trans (c1.trans (c2.trans c3))
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← range_fundamentalGroupMap_eq_coverSubgroup] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (key y).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨u, rfl⟩ := fundamentalGroupMap_structure_surjective Ω C' hc' hη' w
    obtain ⟨y, rfl⟩ := (fundamentalGroupMap_bijective_of_isIso e.inv
      (rfl : η ≫ e.inv = η ≫ e.inv)).2 u
    refine ⟨fundamentalGroupMap f h y, ?_, key y⟩
    rw [← range_fundamentalGroupMap_eq_coverSubgroup]
    exact ⟨y, rfl⟩

end CurvesJacobian.Cusp
