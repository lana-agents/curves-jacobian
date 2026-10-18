/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbAdd
import CurvesJacobian.Picard.TwistCech

/-!
# The class of a relative effective Cartier divisor is additive

Let `f : X ⟶ S` be a morphism of schemes and `D`, `E` relative effective Cartier divisors on
`X/S`. The canonical section `s_D ⊗ s_E` of `𝒪(D) ⊗ 𝒪(E)` has zero scheme `D + E`, so
`[𝒪(D + E)] = [𝒪(D)] + [𝒪(E)]` in `Pic(X)`.

* `Scheme.Modules.zeroIdeal_tmulSection`: the zero scheme of `s ⊗ t` is `Z(s) + Z(t)`, i.e.
  its ideal sheaf is the product of the ideal sheaves.
* `RelEffCartier.picClass_add`: `(D + E).picClass = D.picClass + E.picClass`.
* `RelEffCartier.picClass_zero`: the empty divisor has class `0`.
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

open Scheme CurvesJacobian CurvesJacobian.ModulesGlue

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The zero scheme of a pure tensor `s ⊗ t` of sections of invertible sheaves is the sum of the
zero schemes: its ideal is the product of the ideals. -/
theorem zeroIdeal_tmulSection (L M : X.Modules) [L.IsInvertible] [M.IsInvertible]
    (s : Γ(L, ⊤)) (t : Γ(M, ⊤)) :
    zeroIdeal (L ⊗ M) (tmulSection s t) = zeroIdeal L s * zeroIdeal M t := by
  have H : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧
      (zeroIdeal (L ⊗ M) (tmulSection s t)).ideal W = (zeroIdeal L s * zeroIdeal M t).ideal W := by
    intro x
    obtain ⟨U₁, e₁, hx₁, he₁⟩ := IsInvertible.exists_basis (L := L) x
    obtain ⟨U₂, e₂, hx₂, he₂⟩ := IsInvertible.exists_basis (L := M) x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ U₁ ⊓ U₂ from ⟨hx₁, hx₂⟩)
        (U₁ ⊓ U₂).2
    have h₁ : W ≤ U₁ := le_trans hWU inf_le_left
    have h₂ : W ≤ U₂ := le_trans hWU inf_le_right
    have he₁' := isBasisOn_rs he₁ h₁
    have he₂' := isBasisOn_rs he₂ h₂
    obtain ⟨a, ha⟩ := exists_smul_eq_of_isBasisOn he₁' (L.presheaf.map (homOfLE le_top).op s)
    obtain ⟨b, hb⟩ := exists_smul_eq_of_isBasisOn he₂' (M.presheaf.map (homOfLE le_top).op t)
    refine ⟨⟨W, hW⟩, hxW, ?_⟩
    have hL := zeroIdeal_ideal_of_isBasisOn L s (U := ⟨W, hW⟩) he₁' ha.symm
    have hM := zeroIdeal_ideal_of_isBasisOn M t (U := ⟨W, hW⟩) he₂' hb.symm
    have hLM : (L ⊗ M).presheaf.map (homOfLE le_top).op (tmulSection s t) =
        (a * b) • tmulSection (rs L h₁ e₁) (rs M h₂ e₂) := by
      rw [tmulSection_res, ← ha, ← hb, mul_smul]
      refine (tmulSection_smul_left a _ _).trans ?_
      exact congrArg (a • ·) (tmulSection_smul_right b _ _)
    rw [zeroIdeal_ideal_of_isBasisOn (L ⊗ M) (tmulSection s t) (U := ⟨W, hW⟩)
      (isBasisOn_tmulSection he₁' he₂') hLM, IdealSheafData.ideal_mul, Pi.mul_apply, hL, hM,
      Ideal.span_singleton_mul_span_singleton]
  choose W hxW hW using H
  exact IdealSheafData.ext_of_iSup_eq_top W
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) hW

end Scheme.Modules

namespace RelEffCartier

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The canonical section `s_D ⊗ s_E` of `𝒪(D) ⊗ 𝒪(E)` is a nonzerodivisor on every affine
open. -/
lemma injective_smul_tmulSection_canonicalSection (D E : RelEffCartier f) (U : X.affineOpens) :
    Function.Injective fun r : Γ(X, U.1) ↦ r •
      (D.lineBundle ⊗ E.lineBundle).presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (Modules.tmulSection D.canonicalSection E.canonicalSection) := by
  haveI := Modules.projective_sections D.lineBundle U.2
  have key : (fun r : Γ(X, U.1) ↦ r •
      (D.lineBundle ⊗ E.lineBundle).presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (Modules.tmulSection D.canonicalSection E.canonicalSection)) =
      Modules.tensorSections D.lineBundle E.lineBundle U.1 ∘
        tmulRight (R := Γ(X, U.1))
          (E.lineBundle.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op E.canonicalSection) ∘
        fun r : Γ(X, U.1) ↦
          r • D.lineBundle.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op D.canonicalSection := by
    funext r
    simp only [Function.comp_apply, tmulRight_apply, Modules.tensorSections_tmul]
    rw [Modules.tmulSection_res]
    exact (Modules.tmulSection_smul_left r _ _).symm
  rw [key]
  exact (Modules.bijective_tensorSections U.2).1.comp
    ((injective_tmulRight (E.injective_smul_canonicalSection U.1)).comp
      (D.injective_smul_canonicalSection U.1))

/-- **The class of a relative effective Cartier divisor is additive**:
`[𝒪(D + E)] = [𝒪(D)] + [𝒪(E)]`. -/
theorem picClass_add (D E : RelEffCartier f) :
    (D.add E).picClass = D.picClass + E.picClass := by
  have h : (D.add E).ideal = Modules.zeroIdeal (D.lineBundle ⊗ E.lineBundle)
      (Modules.tmulSection D.canonicalSection E.canonicalSection) := by
    rw [Modules.zeroIdeal_tmulSection, D.zeroIdeal_canonicalSection,
      E.zeroIdeal_canonicalSection]
    rfl
  rw [picClass_eq_of_ideal_eq_zeroIdeal (D.add E) _ _
    (injective_smul_tmulSection_canonicalSection D E) h, Pic.mk_tensor]
  rfl

/-- The empty divisor has trivial class. -/
theorem picClass_zero (f : X ⟶ S) : (CurvesJacobian.RelEffCartier.zero f).picClass = 0 := by
  have h := picClass_add (CurvesJacobian.RelEffCartier.zero f) (CurvesJacobian.RelEffCartier.zero f)
  rw [CurvesJacobian.RelEffCartier.zero_add_zero] at h
  exact add_eq_left.mp h.symm

end RelEffCartier

end AlgebraicGeometry

end
