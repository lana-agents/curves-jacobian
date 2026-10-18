/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicSpecEquiv
import CurvesJacobian.Picard.PicMap

/-!
# Classes in the Picard group are locally trivial

Every `x ∈ Pic(T)` dies on a neighbourhood of each point: there is an open `V ∋ t` such that
`h^* x = 0` for every morphism `h : T'' ⟶ T` landing in `V`
(`AlgebraicGeometry.Scheme.Pic.exists_opens_map_eq_zero`).
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Pic

open Modules

variable {T : Scheme.{u}}

/-- An invertible sheaf with a basis on all of `X` is trivial in `Pic X`. -/
lemma mk_eq_zero_of_isBasisOn {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] {A : X.Opens}
    (hA : A = ⊤) {s : Γ(L, A)} (hs : L.IsBasisOn A s) : mk L = 0 := by
  subst hA
  haveI := isIso_homOfSection hs
  rw [mk_eq_zero_iff]
  exact ⟨(asIso (homOfSection s)).symm ≪≫ structureSheafIsoUnit X⟩

/-- **Local triviality of Picard classes.** -/
theorem exists_opens_map_eq_zero (x : T.Pic) (t : T) : ∃ V : T.Opens, t ∈ V ∧
    ∀ {T'' : Scheme.{u}} (h : T'' ⟶ T), Set.range h ⊆ V → map h x = 0 := by
  obtain ⟨L, hL, rfl⟩ := mk_surjective x
  obtain ⟨U, s, htU, hs⟩ := IsInvertible.exists_basis (L := L) t
  refine ⟨U, htU, fun h hh ↦ ?_⟩
  have htop : h ⁻¹ᵁ U = ⊤ := eq_top_iff.mpr fun y _ ↦ hh ⟨y, rfl⟩
  rw [map_mk]
  exact mk_eq_zero_of_isBasisOn _ htop (isBasisOn_pullbackSection h U hs)

end AlgebraicGeometry.Scheme.Pic
