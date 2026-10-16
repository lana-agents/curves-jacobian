/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Scheme.ValuationPoints
import Belyi.FunctionField
import Belyi.Curve.SmoothStalk
import WeilCurves.FunctionField.Place

/-!
# Points of a curve and places of its function field

Let `k` be a field and `X` an integral `k`-scheme, with the `k`-algebra structure on the function
field `K(X)` of `Belyi.instAlgebraFunctionField`.

* `CurvesJacobian.extendsOver_iff`: a valuation subring `O ⊆ K(X)` extends over `X ⟶ Spec k`
  (`ExtendsOver`) iff `k ⊆ O`.
* `CurvesJacobian.pointEquivValuationSubringOver`: if `X` is separated and universally closed over
  `k` and its stalks are valuation rings, then `X ≃ {O : ValuationSubring K(X) // k ⊆ O}`.
* `CurvesJacobian.stalkValuationSubring_eq_top_iff`: the generic point is the one with `O = K(X)`.
* `CurvesJacobian.curvePlaceEquiv`: for a curve `X` over a perfect field `k` (belyi's
  `IsCurveOver`), the non-generic points of `X` are in bijection with the places of `K(X)/k`
  in the sense of weil-curves (`WeilCurves.FunctionField.Place k K(X)`: valuation subrings
  `O ≠ K(X)` containing `k`), `x ↦ 𝒪_{X,x}`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi

namespace CurvesJacobian

universe u

section Over

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsIntegral X]

/-- A valuation subring of `K(X)` extends over `X ⟶ Spec k` iff it contains `k`. -/
theorem extendsOver_iff (O : ValuationSubring X.functionField) :
    ExtendsOver (X ↘ Spec (CommRingCat.of k)) O ↔
      ∀ c : k, algebraMap k X.functionField c ∈ O := by
  constructor
  · rintro ⟨g, hg⟩ c
    have h : Spec.preimage g ≫ CommRingCat.ofHom (algebraMap O X.functionField) =
        CommRingCat.ofHom (algebraMap k X.functionField) := by
      rw [← Spec.map_inj, Spec.map_comp, Spec.map_preimage, hg,
        specMap_algebraMap_functionField]
    have h2 : algebraMap k X.functionField c =
        (((Spec.preimage g).hom c : O) : X.functionField) :=
      (congrArg (fun φ ↦ φ.hom c) h).symm
    rw [h2]
    exact ((Spec.preimage g).hom c).2
  · intro h
    let ψ : CommRingCat.of k ⟶ CommRingCat.of O :=
      CommRingCat.ofHom ((algebraMap k X.functionField).codRestrict O.toSubring h)
    refine ⟨Spec.map ψ, ?_⟩
    rw [← Spec.map_comp, ← specMap_algebraMap_functionField]
    rfl

variable {X}

/-- Points of an integral scheme, separated and universally closed over a field `k`, with
valuation-ring stalks are the valuation subrings of `K(X)` containing `k`. -/
noncomputable def pointEquivValuationSubringOver [X.IsSeparated]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    X ≃ {O : ValuationSubring X.functionField // ∀ c : k, algebraMap k X.functionField c ∈ O} :=
  (pointEquivValuationSubring hX (X ↘ Spec (CommRingCat.of k))).trans
    (Equiv.subtypeEquivRight fun O ↦ extendsOver_iff k X O)

lemma pointEquivValuationSubringOver_apply [X.IsSeparated]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (x : X) :
    (pointEquivValuationSubringOver k hX x).1 = stalkValuationSubring hX x :=
  rfl

end Over

section Generic

variable {X : Scheme.{u}} [IsIntegral X] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))

lemma stalkValuationSubring_genericPoint :
    stalkValuationSubring hX (genericPoint X) = ⊤ := by
  refine eq_top_iff.2 fun f _ ↦ ⟨f, ?_⟩
  change (X.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint X))).hom f = f
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

lemma stalkValuationSubring_eq_top_iff [X.IsSeparated] (x : X) :
    stalkValuationSubring hX x = ⊤ ↔ x = genericPoint X := by
  constructor
  · intro h
    exact stalkValuationSubring_injective hX (h.trans (stalkValuationSubring_genericPoint hX).symm)
  · rintro rfl
    exact stalkValuationSubring_genericPoint hX

end Generic

/-- A scheme separated over a field is a separated scheme. -/
lemma isSeparated_of_over (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))] :
    X.IsSeparated := by
  constructor
  rw [show terminal.from X = (X ↘ Spec (CommRingCat.of k)) ≫ terminal.from _ from
    terminal.hom_ext _ _]
  infer_instance

section Curve

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **Points of a curve ↔ places.** For a curve `X` over a perfect field `k`, the points of `X`
other than the generic point correspond to the places of `K(X)/k` (weil-curves), via
`x ↦ 𝒪_{X,x} ⊆ K(X)`. -/
noncomputable def curvePlaceEquiv :
    {x : X // x ≠ genericPoint X} ≃ WeilCurves.FunctionField.Place k X.functionField :=
  haveI := isSeparated_of_over k X
  let hX : ∀ x : X, ValuationRing (X.presheaf.stalk x) :=
    valuationRing_stalk_of_isCurveOver k X
  let e := pointEquivValuationSubringOver k hX
  { toFun := fun x ↦ ⟨(e x.1).1, fun h ↦ x.2 ((stalkValuationSubring_eq_top_iff hX x.1).1 h),
      (e x.1).2⟩
    invFun := fun P ↦ ⟨e.symm ⟨P.1, P.2.2⟩, fun h ↦ P.2.1 (by
      have := congrArg Subtype.val (e.apply_symm_apply ⟨P.1, P.2.2⟩)
      rw [← this, h]
      exact stalkValuationSubring_genericPoint hX)⟩
    left_inv := fun x ↦ Subtype.ext (by simp)
    right_inv := fun P ↦ Subtype.ext (by simp) }

lemma curvePlaceEquiv_apply (x : {x : X // x ≠ genericPoint X}) :
    (curvePlaceEquiv k X x).1 =
      stalkValuationSubring (valuationRing_stalk_of_isCurveOver k X) x.1 :=
  rfl

end Curve

end CurvesJacobian
