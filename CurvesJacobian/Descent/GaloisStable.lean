/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Descent.GaloisScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Galois-stable affine opens

Let `L / k` be a finite Galois extension and `X` a separated `L`-scheme with a semilinear
`Gal(L/k)`-action `a`. For an affine open `U ⊆ X`, the intersection `⋂_g g⁻¹ U` of its
`Gal(L/k)`-translates is a `G`-stable affine open (`GalAction.isAffineOpen_stableInf`,
`GalAction.isStable_stableInf`) containing every point whose orbit lies in `U`
(`GalAction.mem_stableInf_iff`). This reduces the hypothesis `hcov` of
`isRepresentable_descFunctor` / `descScheme` to: every Galois orbit of a point lies in an affine
open.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]

namespace GalAction

variable {X : Scheme.{u}} {q : X ⟶ Spec (CommRingCat.of L)} (a : GalAction (k := k) X q)

instance (g : Gal(L/k)) : IsIso (a.act g) :=
  ⟨⟨a.act g⁻¹, a.act_act_inv g, a.act_inv_act g⟩⟩

/-- The intersection `⋂_g g⁻¹ U` of the Galois translates of `U`. -/
def stableInf (U : X.Opens) : X.Opens := Finset.univ.inf fun g : Gal(L/k) ↦ a.act g ⁻¹ᵁ U

lemma mem_stableInf_iff (U : X.Opens) (x : X) :
    x ∈ a.stableInf U ↔ ∀ g : Gal(L/k), a.act g x ∈ U := by
  rw [stableInf, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
  simp

lemma isStable_stableInf (U : X.Opens) : a.IsStable (a.stableInf U) := by
  intro h
  ext x
  change a.act h x ∈ a.stableInf U ↔ x ∈ a.stableInf U
  rw [mem_stableInf_iff, mem_stableInf_iff]
  constructor
  · intro H g
    have := H (h⁻¹ * g)
    rwa [← Scheme.Hom.comp_apply, a.act_mul, mul_inv_cancel_left] at this
  · intro H g
    rw [← Scheme.Hom.comp_apply, a.act_mul]
    exact H _

lemma isAffineOpen_stableInf [IsSeparated q] {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (a.stableInf U) := by
  haveI : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = q ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  rw [stableInf, Finset.inf_eq_iInf]
  simp only [Finset.mem_univ, iInf_pos]
  exact IsAffineOpen.iInf fun g ↦ hU.preimage_of_isIso (a.act g)

lemma le_stableInf_of_isStable {U V : X.Opens} (hV : a.IsStable V) (h : V ≤ U) :
    V ≤ a.stableInf U := by
  intro x hx
  rw [mem_stableInf_iff]
  exact fun g ↦ h (a.mem_of_isStable hV g hx)

end GalAction

end CurvesJacobian.GaloisDescent
