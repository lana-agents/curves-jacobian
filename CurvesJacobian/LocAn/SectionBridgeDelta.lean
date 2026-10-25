/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SectionBridge

/-!
# `Δ_X = ker(π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k))` in the Galois model

An element of `π₁ᵉᵗ(X, η̄)` acting trivially on the fibres of finite étale `k`-schemes (i.e. in the
kernel of `π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k)`) goes to `Δ_X = ker(Π_X → G_k)` under `etalePi1EquivPiX'`
(`CurvesJacobian.LocAn.SectionBridge.mem_DeltaX_of_fundamentalGroupMap_eq_one`): test the action
on the point `Spec Ω ⟶ Spec k(a)` for `a ∈ k̄`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi IsLocalRing Pi1.Orbifold
open AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace CurvesJacobian.LocAn.SectionBridge

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- If `σ ∈ H` acts trivially, through `Spec L ⟶ Spec k`, on the fibres of finite étale
`k`-schemes, then `σ` fixes `k̄`. -/
theorem hToGk_eq_one_of_galoisAction (j : Spec (.of D.L) ⟶ Spec (.of k))
    (hj : j = Spec.map (CommRingCat.ofHom (algebraMap k D.L))) {η : Spec (.of Ω) ⟶ Spec (.of k)}
    (hη : Spec.map (CommRingCat.ofHom (algebraMap D.L Ω)) ≫ j = η) (hH : D.H ≤ D.HL) (σ : D.H)
    (h : galoisAction D.L j hη (D.toGalL (Subgroup.inclusion hH σ)) = 1) : hToGk D σ = 1 := by
  subst hj
  subst hη
  ext a
  change algebraMap (kbar k Ω) Ω (hToGk D σ a) = (a : Ω)
  rw [algebraMap_hToGk_apply]
  let K : IntermediateField k (kbar k Ω) := IntermediateField.adjoin k {a}
  haveI : FiniteDimensional k K := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral a)
  haveI := isFiniteEtale_Spec_intermediateField K
  let E : FiniteEtale (Spec (.of k)) := mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let ι : K →+* Ω := (algebraMap (kbar k Ω) Ω).comp (algebraMap K (kbar k Ω))
  have hw : Spec.map (CommRingCat.ofHom ι) ≫ E.hom =
      Spec.map (CommRingCat.ofHom (algebraMap D.L Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k D.L)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let w : (fiber _).obj E := (fiberObjEquivHom _ E).symm (Over.homMk _ hw)
  have h1 := galoisAction_hom_app_left D.L _ rfl (D.toGalL (Subgroup.inclusion hH σ)) E w
  rw [h] at h1
  change (fiberObjEquivHom _ E w).left = _ at h1
  simp only [w, Equiv.apply_symm_apply, Over.homMk_left] at h1
  have h3 := Spec.map_injective (h1.trans (Spec.map_comp _ _).symm)
  have h2 := congrArg (fun f ↦ f.hom ⟨a, IntermediateField.mem_adjoin_simple_self k a⟩) h3
  exact h2.symm

section Curve

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
include hk in
/-- The generic point `Spec L ⟶ X` lies over `Spec L ⟶ Spec k`. -/
lemma genericLX_toSpec :
    genericLX D X eL ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k D.L)) := by
  rw [genericLX, Category.assoc, ← specMap_algebraMap_functionField, ← Spec.map_comp]
  congr 1
  ext c
  exact hk c

variable [IsCurveOver k X]

/-- **`Δ_X = ker(π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k))` in the Galois model**: an element of `π₁ᵉᵗ(X, η̄)`
mapping to `1` in `π₁ᵉᵗ(Spec k)` goes to `Δ_X` under `π₁ᵉᵗ(X, η̄) ≃ Π_X`. -/
theorem mem_DeltaX_of_fundamentalGroupMap_eq_one (hHL : D.HL = D.H) {τ : X.functionField}
    (hτ : ((eL τ : D.L) : Ω) = t) (γ : π₁ᵉᵗ(geometricGenericPoint D X eL))
    (hγ : fundamentalGroupMap (X ↘ Spec (.of k)) rfl γ = 1) :
    etalePi1EquivPiX' D X eL hk hτ hHL.ge γ ∈ DeltaX D := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (etalePi1EquivPiX' D X eL hk hτ hHL.ge γ)
  have hγσ : γ = galoisAction D.L (genericLX D X eL) (genericLX_point D eL)
      (D.toGalL (Subgroup.inclusion hHL.ge σ)) := by
    apply (etalePi1EquivPiX' D X eL hk hτ hHL.ge).injective
    rw [etalePi1EquivPiX'_galoisAction D eL hk hHL hτ]
    exact hσ.symm
  rw [DeltaX, MonoidHom.mem_ker, ← hσ]
  change piXToGk D (σ : PiX D) = 1
  rw [piXToGk_mk]
  refine hToGk_eq_one_of_galoisAction D (genericLX D X eL ≫ (X ↘ Spec (.of k)))
    (genericLX_toSpec D eL hk) ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (X ↘ Spec (.of k))) (genericLX_point D eL))) hHL.ge σ ?_
  rw [← fundamentalGroupMap_galoisAction_eq (genericLX D X eL) (X ↘ Spec (.of k)) _ rfl
    (genericLX_point D eL) rfl, ← hγσ, hγ]

end Curve

end CurvesJacobian.LocAn.SectionBridge
