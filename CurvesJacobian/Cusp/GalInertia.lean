/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FieldChange
import CurvesJacobian.Cusp.Inertia
import CurvesJacobian.Cusp.LineCuspInertia
import CurvesJacobian.Cusp.ChainPush

/-!
# Cuspidal inertia groups as Galois inertia groups through the generic point

* `CurvesJacobian.Cusp.cuspInertia_eq_galInertia`: the cuspidal inertia group
  `cuspInertia D X eL hH U W` (defined through the Galois data `D`) is the intrinsic
  `galInertia` of `W` through the generic point `genericL : Spec L ⟶ U`;
* `AlgebraicGeometry.FiniteEtale.galInertia_eq_map`: for `Ω / F` algebraic, `galInertia` is the
  image of the inertia subgroup `GaloisPi1.inertiaSubgroup W`;
* `AlgebraicGeometry.FiniteEtale.map_galInertia_le`,
  `AlgebraicGeometry.FiniteEtale.relIndex_map_galInertia_ne_zero`: **naturality** — for
  `f : Y ⟶ X` and generic points `j_Y : Spec F_Y ⟶ Y`, `j_X : Spec F_X ⟶ X` with
  `j_Y ≫ f = Spec(F_X → F_Y) ≫ j_X`, `f_*` maps the inertia group of `W` at `Y` into the
  inertia group of `W` at `X`, with finite index if `F_Y / F_X` is finite.
-/

open CategoryTheory Limits PreGaloisCategory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
  (F : Type u) [Field F] [Algebra F Ω] [IsGalois F Ω] (j : Spec (.of F) ⟶ X)
  (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η)

lemma galInertia_eq_map (W : ValuationSubring Ω) :
    galInertia η F j h W = (GaloisPi1.inertiaSubgroup (P := F) W).map (galoisAction F j h) := by
  rw [galInertia]
  conv_rhs => rw [← Subgroup.closure_eq (GaloisPi1.inertiaSubgroup (P := F) W)]
  rw [MonoidHom.map_closure]
  rfl

section Naturality

variable {Y X : Scheme.{u}} (f : Y ⟶ X) {FY FX Ω : Type u} [Field FY] [Field FX] [Field Ω]
  [IsSepClosed Ω] [Algebra FX FY] [Algebra FY Ω] [Algebra FX Ω] [IsScalarTower FX FY Ω]
  [IsGalois FY Ω] [IsGalois FX Ω] (jY : Spec (.of FY) ⟶ Y) (jX : Spec (.of FX) ⟶ X)
  (hj : jY ≫ f = Spec.map (CommRingCat.ofHom (algebraMap FX FY)) ≫ jX)

omit [IsSepClosed Ω] [IsGalois FY Ω] [IsGalois FX Ω] in
include hj in
lemma specAlgebraMap_comp_generic :
    Spec.map (CommRingCat.ofHom (algebraMap FX Ω)) ≫ jX =
      (Spec.map (CommRingCat.ofHom (algebraMap FY Ω)) ≫ jY) ≫ f := by
  rw [Category.assoc, hj, ← Category.assoc, specMap_algebraMap_comp FY FX]

/-- The elements of `Gal(Ω / F_X)` fixing `F_Y`. -/
def fixingFY : Subgroup (Ω ≃ₐ[FX] Ω) :=
  (IsScalarTower.toAlgHom FX FY Ω).fieldRange.fixingSubgroup

include hj in
/-- **Naturality of the Galois action**: `f_*` of the action of `g ∈ Gal(Ω / F_Y)` at `Y` is the
action of `g` (as an element of `Gal(Ω / F_X)`) at `X`. -/
lemma fundamentalGroupMap_galoisAction_generic (g : Ω ≃ₐ[FY] Ω) :
    fundamentalGroupMap f rfl (galoisAction FY jY rfl g) =
      galoisAction FX jX (specAlgebraMap_comp_generic f jY jX hj) (g.restrictScalars FX) := by
  rw [fundamentalGroupMap_galoisAction FY jY f rfl rfl (by rw [Category.assoc])]
  exact galoisAction_eq_of_apply_eq FY (jY ≫ f) jX _ _ g _ fun _ ↦ rfl

include hj in
/-- **Inertia groups map into inertia groups.** -/
theorem map_galInertia_le (W : ValuationSubring Ω) :
    (galInertia _ FY jY rfl W).map (fundamentalGroupMap f rfl).toMonoidHom ≤
      galInertia _ FX jX (specAlgebraMap_comp_generic f jY jX hj) W := by
  rw [galInertia_eq_map, galInertia_eq_map, Subgroup.map_map]
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g.restrictScalars FX, hg, ?_⟩
  exact (fundamentalGroupMap_galoisAction_generic f jY jX hj g).symm

include hj in
/-- **With finite index** if `F_Y / F_X` is finite. -/
theorem relIndex_map_galInertia_ne_zero [FiniteDimensional FX FY] (W : ValuationSubring Ω) :
    ((galInertia _ FY jY rfl W).map (fundamentalGroupMap f rfl).toMonoidHom).relIndex
      (galInertia _ FX jX (specAlgebraMap_comp_generic f jY jX hj) W) ≠ 0 := by
  set S := GaloisPi1.inertiaSubgroup (P := FX) W
  have hR : (fixingFY (FX := FX) (FY := FY) (Ω := Ω)).index ≠ 0 := by
    rw [fixingFY, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    have e := (IsScalarTower.toAlgHom FX FY Ω).equivFieldRange.toLinearEquiv
    rw [← e.finrank_eq]
    exact Module.finrank_pos.ne'
  have h1 : (S ⊓ fixingFY (FX := FX) (FY := FY) (Ω := Ω)).relIndex S ≠ 0 := by
    rw [Subgroup.inf_relIndex_left]
    intro h0
    exact hR (by rw [← Subgroup.relIndex_top_right]; exact
      Subgroup.relIndex_eq_zero_of_le_right le_top h0)
  have h2 := Belyi.Anabelian.Subgroup.relIndex_map_ne_zero (galoisAction FX jX
    (specAlgebraMap_comp_generic f jY jX hj)) h1
  rw [galInertia_eq_map _ FX]
  refine fun h0 ↦ h2 (Subgroup.relIndex_eq_zero_of_le_left ?_ h0)
  rintro _ ⟨g, ⟨hgS, hgR⟩, rfl⟩
  have hcomm : ∀ c : FY, g (algebraMap FY Ω c) = algebraMap FY Ω c := fun c ↦
    hgR ⟨_, c, rfl⟩
  let g' : Ω ≃ₐ[FY] Ω := { g with commutes' := hcomm }
  rw [galInertia_eq_map, Subgroup.map_map]
  refine ⟨g', hgS, ?_⟩
  exact (fundamentalGroupMap_galoisAction_generic f jY jX hj g').trans rfl

end Naturality

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L) [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)

omit [X.Over (Spec (CommRingCat.of k))] in
/-- **The cuspidal inertia group is the Galois inertia group through the generic point.** -/
theorem cuspInertia_eq_galInertia (U : X.Opens) [Nonempty U] (W : ValuationSubring Ω) :
    cuspInertia D X eL hH U W =
      galInertia (specPoint D.L Ω ≫ genericL D X eL U) D.L (genericL D X eL U) rfl W := by
  rw [cuspInertia, galInertia]
  congr 1
  ext γ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨D.toGalL (Subgroup.inclusion hH σ), hσ, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨σ', rfl⟩ := D.toGalL_surjective g
    exact ⟨⟨σ', D.le σ'.2⟩, hg, rfl⟩

end CurvesJacobian.Cusp
