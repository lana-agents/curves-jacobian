/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BaseChange

/-!
# The fibre of a base change over a rational point is one point (MR8.3, task 2 (iv))

For `f : X ⟶ S`, `g : Y ⟶ S` with `Y` a one-point scheme whose residue field is a field (e.g.
`Y = Spec Ω`) and `x : X` with `κ(f x) → κ(x)` an isomorphism (a rational point), at most one
point of `X ×_S Y` lies over `x` (`AlgebraicGeometry.Scheme.Pullback.subsingleton_fst_fiber`):
by Mathlib's `Scheme.Pullback.carrierEquiv` the points over `x` are the primes of
`κ(x) ⊗_{κ(s)} κ(y) ≅ κ(y)`.

Consequence (`CurvesJacobian.Cusp.subsingleton_baseChangeOpen_diff`): if `U' ∖ U ⊆ {x}` with `x`
a `k`-rational point, then `U'_Ω ∖ U_Ω` has at most one point — the hypothesis `hsub` of
`CurvesJacobian.Cusp.ker_fillMap_eq_map`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

set_option backward.isDefEq.respectTransparency false in
lemma subsingleton_spec_tensor (T : Triplet f g) [IsIso (f.residueFieldMap T.x)] :
    Subsingleton (Spec T.tensor) := by
  haveI : IsIso (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
    pushout_inr_iso_of_left_iso _ _
  let e : Y.residueField T.y ≅ T.tensor := asIso (pushout.inr _ _)
  let h : Spec T.tensor ≅ Spec (Y.residueField T.y) := Scheme.Spec.mapIso e.op
  refine ⟨fun a b ↦ ?_⟩
  have hs : Subsingleton (Spec (Y.residueField T.y)) := inferInstance
  have := hs.elim (h.hom a) (h.hom b)
  simpa using congrArg h.inv this

/-- **At most one point over a rational point.** -/
theorem subsingleton_fst_fiber [Subsingleton Y] (x : X) [IsIso (f.residueFieldMap x)] :
    {t : ↑(pullback f g) | pullback.fst f g t = x}.Subsingleton := by
  intro t₁ h₁ t₂ h₂
  apply carrierEquiv.injective
  have hx₁ : (Triplet.ofPoint t₁).x = x := h₁
  have hx₂ : (Triplet.ofPoint t₂).x = x := h₂
  have hT : Triplet.ofPoint t₁ = Triplet.ofPoint t₂ :=
    Triplet.ext (hx₁.trans hx₂.symm) (Subsingleton.elim _ _)
  refine carrierEquiv_eq_iff.2 ⟨hT, ?_⟩
  haveI : IsIso (f.residueFieldMap (Triplet.ofPoint t₂).x) := by rw [hx₂]; infer_instance
  exact (subsingleton_spec_tensor (Triplet.ofPoint t₂)).elim _ _

end AlgebraicGeometry.Scheme.Pullback

namespace CurvesJacobian.Cusp

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Filling in a rational point adds one geometric point.** If `U' ∖ U ⊆ {x}` with
`κ(x) = k`, then `U'_Ω ∖ U_Ω` has at most one point. -/
theorem subsingleton_baseChangeOpen_diff {U U' : X.Opens} {x : X}
    (hx : (U' : Set X) \ U ⊆ {x}) [IsIso ((X ↘ Spec (.of k)).residueFieldMap x)] :
    ((baseChangeOpen k Ω U' : Set (baseChange k Ω X)) \ baseChangeOpen k Ω U).Subsingleton := by
  refine (Scheme.Pullback.subsingleton_fst_fiber (g := Belyi.specAlgebraMap k Ω) x).anti ?_
  rintro t ⟨ht', ht⟩
  exact hx ⟨ht', ht⟩

end CurvesJacobian.Cusp
