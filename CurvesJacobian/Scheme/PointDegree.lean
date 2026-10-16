/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Scheme.CurvePic

/-!
# The degree of a closed point is the degree of its residue field

For a curve `X` over a perfect field `k` and a closed point `x`, the degree of the corresponding
place of `K(X)/k` equals `[κ(x) : k]`, where `κ(x)` is the residue field of the scheme `X` at `x`
with its `k`-algebra structure from `X ↘ Spec k` (`CurvesJacobian.pointDegree_eq_finrank`).

The proof identifies the stalk `𝒪_{X,x}` with the valuation ring of the place
(`CurvesJacobian.stalkRingEquiv`) compatibly with `k`, and passes to residue fields.
-/

open CategoryTheory AlgebraicGeometry Belyi WeilCurves.FunctionField

namespace CurvesJacobian

universe u

section

variable {X : Scheme.{u}} [IsIntegral X] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))

/-- The stalk at `x` is isomorphic to its image in the function field. -/
noncomputable def stalkRingEquiv (x : X) :
    X.presheaf.stalk x ≃+* stalkValuationSubring hX x :=
  RingEquiv.ofBijective (stalkToValuationSubring hX x rfl).hom
    ⟨fun _ _ h ↦ algebraMap_stalk_injective x (congrArg Subtype.val h),
      fun ⟨_, a, rfl⟩ ↦ ⟨a, rfl⟩⟩

lemma coe_stalkRingEquiv (x : X) (a : X.presheaf.stalk x) :
    (stalkRingEquiv hX x a : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField a :=
  rfl

end

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

/-- The `k`-algebra structure on the stalk at `x`, via `X ↘ Spec k`. -/
noncomputable abbrev stalkAlgebra (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- The `k`-algebra structure on the residue field at `x`, via `X ↘ Spec k`. -/
noncomputable abbrev residueFieldAlgebra (x : X) : Algebra k (X.residueField x) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

lemma algebraMap_stalk_functionField_germ [IsIntegral X] (x : X) (c : k) :
    algebraMap (X.presheaf.stalk x) X.functionField
      ((X.presheaf.germ ⊤ x trivial).hom
        ((X ↘ Spec (CommRingCat.of k)).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
      algebraMap k X.functionField c := by
  change (X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes
      (genericPoint_specializes x)).hom _ = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  rfl

variable [PerfectField k] [IsCurveOver k X] [IsIntegral X]

/-- **The degree of a closed point is `[κ(x) : k]`.** -/
theorem pointDegree_eq_finrank (x : ClosedPoint X) :
    pointDegree k X x =
      letI := residueFieldAlgebra k X x.1
      Module.finrank k (X.residueField x.1) := by
  letI := residueFieldAlgebra k X x.1
  set hX := valuationRing_stalk_of_isCurveOver k X
  set P := curvePlaceEquiv k X x
  have hP : P.1 = stalkValuationSubring hX x.1 := curvePlaceEquiv_apply k X x
  -- the residue fields are isomorphic as rings
  let e : X.residueField x.1 ≃+* P.ResidueField :=
    (IsLocalRing.ResidueField.mapEquiv ((stalkRingEquiv hX x.1).trans
      (RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hP.symm))))
  -- and `k`-linearly so
  let eA : X.residueField x.1 ≃ₐ[k] P.ResidueField :=
    { e with
      commutes' := fun c ↦ by
        change IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ _) =
          P.residue (P.baseHom c)
        rw [IsLocalRing.ResidueField.map_residue]
        congr 1
        apply Subtype.ext
        change (stalkRingEquiv hX x.1 _ : X.functionField) = algebraMap k X.functionField c
        rw [coe_stalkRingEquiv]
        exact algebraMap_stalk_functionField_germ k X x.1 c }
  rw [pointDegree, Place.deg, eA.toLinearEquiv.finrank_eq]

end CurvesJacobian
