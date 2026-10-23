/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelAutRing
import CurvesJacobian.Cusp.ChainPush

/-!
# Faithfulness of the action of `N_A(ι(Π_Y)) / ι(Π_Y)` on a geometric model

For a geometric model `D` of a chain object `A` (`CurvesJacobian.Cusp.GeomModel`) and the
rel-isom-DGC over its field of definition, the ring automorphisms
`GeomModel.autRing : N_A(ι(Π_Y)) →* Aut_K(Γ(U_Y))` have kernel exactly `ι(Π_Y)`:

* **`CurvesJacobian.Cusp.ChainObj.eq_one_of_forall_commute`**: chain objects are slim, i.e. an
  element centralising an open subgroup is trivial (`G` and `Δ_A` are slim).
* `CurvesJacobian.Cusp.GeomModel.mem_range_of_autRing_eq_one`: if `autRing g = 1`, then `F_g` is
  the identity, so conjugation by `g` on `ι(Π_Y)` is inner, and `g ∈ ι(Π_Y)` by slimness.
* **`CurvesJacobian.Cusp.GeomModel.ker_autRing`**: `ker autRing = ι(Π_Y)`, and
  `GeomModel.ker_autRing_comp_subtype` for a subgroup `P' ≤ N`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- **Chain objects are slim**: an element of `A` centralising an open subgroup is trivial. -/
theorem ChainObj.eq_one_of_forall_commute {E : CuspidalExt.{u}} (A : ChainObj E)
    {U : Subgroup A.grp} (hU : IsOpen (U : Set A.grp)) {z : A.grp}
    (hz : ∀ u ∈ U, z * u = u * z) : z = 1 := by
  have hV : IsOpen ((U.map (A.toG : A.grp →* E.G) : Subgroup E.G) : Set E.G) :=
    isOpen_map_of_isOpen_range A.toG A.isOpen_range_toG hU
  have hG : A.toG z = 1 := E.slim_G ⟨_, hV⟩ _ fun _ hv ↦ by
    obtain ⟨u, hu, rfl⟩ := hv
    change A.toG z * A.toG u = A.toG u * A.toG z
    rw [← map_mul, ← map_mul, hz u hu]
  have hzΔ : z ∈ A.Delta := MonoidHom.mem_ker.2 hG
  have hW : IsOpen ((U.comap A.Delta.subtype : Subgroup A.Delta) : Set A.Delta) :=
    hU.preimage continuous_subtype_val
  have h1 : (⟨z, hzΔ⟩ : A.Delta) = 1 := A.slim_delta ⟨_, hW⟩ _ fun w hw ↦
    Subtype.ext (hz w.1 hw)
  exact congrArg Subtype.val h1

namespace GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A) (hDGC : RelIsomDGC.Exists D.M)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- If `autRing g = 1`, then `F_{g⁻¹}` is the identity. -/
lemma semilinearAction_inv_hom_eq_id {g : D.Nrm} (hg : D.autRing hDGC g = 1) :
    (D.semilinearAction hDGC g⁻¹).hom = 𝟙 _ := by
  rw [← specMap_autRing, hg]
  exact Spec.map_id _

/-- **The kernel of `autRing` lies in `ι(Π_Y)`.** -/
theorem mem_range_of_autRing_eq_one {g : D.Nrm} (hg : D.autRing hDGC g = 1) :
    (g : A.grp) ∈ Set.range D.ι := by
  have H : IsConjInduced (𝟙 _) (D.conjPi g⁻¹) :=
    (D.isConjInduced_semilinearAutOf hDGC g⁻¹).congr_hom
      (D.semilinearAction_inv_hom_eq_id hDGC hg)
  obtain ⟨γ', hγ⟩ := (isConjInduced_iff _ (Category.comp_id _) _).1 H
  let γ : D.Pi := γ'
  have hc : ∀ σ, D.conjPi g⁻¹ σ = γ * σ * γ⁻¹ := fun σ ↦ by
    rw [hγ σ]
    change γ'.conjAut (fundamentalGroupMap (𝟙 _) (Category.comp_id _) σ) = _
    rw [fundamentalGroupMap_id]
    exact Aut_conjAut_eq γ' σ
  have hz : (g : A.grp) * D.ι γ = 1 := by
    refine ChainObj.eq_one_of_forall_commute A (U := (D.ι : D.Pi →* A.grp).range)
      (by rw [MonoidHom.coe_range]; exact D.isOpen_range) ?_
    rintro _ ⟨σ, rfl⟩
    have h := D.ι_conjPi g⁻¹ σ
    rw [hc σ, map_mul, map_mul, map_inv, Subgroup.coe_inv, inv_inv] at h
    change (g : A.grp) * D.ι γ * D.ι σ = D.ι σ * ((g : A.grp) * D.ι γ)
    calc (g : A.grp) * D.ι γ * D.ι σ
        = (g : A.grp) * (D.ι γ * D.ι σ * (D.ι γ)⁻¹) * D.ι γ := by group
      _ = (g : A.grp) * ((g : A.grp)⁻¹ * D.ι σ * g) * D.ι γ := by rw [h]
      _ = D.ι σ * ((g : A.grp) * D.ι γ) := by group
  exact ⟨γ⁻¹, by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left hz).symm⟩

/-- **`ker autRing = ι(Π_Y)`**: the action of `N_A(ι(Π_Y)) / ι(Π_Y)` on `Γ(U_Y)` is faithful. -/
theorem ker_autRing : (D.autRing hDGC).ker = D.ιNHom.range := by
  refine le_antisymm (fun g hg ↦ ?_) (D.range_ιNHom_le_ker_autRing hDGC)
  obtain ⟨σ, hσ⟩ := D.mem_range_of_autRing_eq_one hDGC (MonoidHom.mem_ker.1 hg)
  exact ⟨σ, Subtype.ext hσ⟩

/-- `ker (autRing|_{P'}) = ι(Π_Y) ∩ P'`. -/
theorem ker_autRing_comp_subtype (P' : Subgroup D.Nrm) :
    ((D.autRing hDGC).comp P'.subtype).ker = D.ιNHom.range.subgroupOf P' := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← ker_autRing, MonoidHom.mem_ker]
  rfl

end GeomModel

end CurvesJacobian.Cusp
