/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Scheme.CurveFunctionField
import Belyi.Dimension
import WeilCurves.FunctionField.Picard

/-!
# Divisors and the Picard group of a curve

Let `X` be a curve over a perfect field `k` (`IsCurveOver k X`). Its closed points are the points
other than the generic point (`CurvesJacobian.isClosed_closedPoint`), and they correspond to the
places of `K(X)/k` (`curvePlaceEquiv`). Transporting weil-curves' divisor theory along this
bijection:

* `CurvesJacobian.CurveDivisor X`: Weil divisors, finitely supported `ℤ`-valued functions on the
  closed points; `CurvesJacobian.divisorEquiv : CurveDivisor X ≃+ Divisor k K(X)`;
* `CurvesJacobian.pointDegree x = [κ(P_x) : k]` and `CurvesJacobian.CurveDivisor.deg`;
* `CurvesJacobian.curveDiv f`: the divisor of a rational function, with
  `curveDiv_apply` (`ord` at the place of `x`), `curveDiv_mul`, `deg_curveDiv` (`= 0`), and
  `mem_stalk_iff` (`f ∈ 𝒪_{X,x} ↔ ord_x f ≥ 0`);
* `CurvesJacobian.CurvePic X := CurveDivisor X ⧸ (principal divisors)`, with
  `CurvesJacobian.curvePicEquiv : CurvePic X ≃+ Pic k K(X)`, the degree `CurvePic.deg` and
  `CurvesJacobian.CurvePic0 X := ker deg`.

`CurvePic X` is the divisor class group of `X`; identifying it with the group of isomorphism
classes of invertible sheaves (and with `H¹(X_et, 𝔾ₘ)`) is not formalised (see `CJ-plan.md` §8).
-/

open CategoryTheory AlgebraicGeometry Belyi WeilCurves.FunctionField

namespace CurvesJacobian

universe u

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- The closed points of a curve: the points other than the generic point. -/
abbrev ClosedPoint : Type u := {x : X // x ≠ genericPoint X}

omit [PerfectField k] in
include k in
/-- Points other than the generic point of a curve are closed. -/
lemma isClosed_closedPoint [PerfectField k] (x : ClosedPoint X) : IsClosed ({x.1} : Set X) :=
  isClosed_singleton_of_ne_genericPoint (krullDimLE_one_stalk_of_isCurveOver k X) x.2

include k in
/-- A curve has a closed point (a place of `K(X)/k` exists). -/
lemma nonempty_closedPoint : Nonempty (ClosedPoint X) :=
  ⟨(curvePlaceEquiv k X).symm (Classical.arbitrary _)⟩

include k in
/-- **The closed points of a curve are exactly the non-generic points.** -/
lemma isClosed_singleton_iff (x : X) : IsClosed ({x} : Set X) ↔ x ≠ genericPoint X := by
  refine ⟨fun hx hη ↦ ?_, fun hx ↦ isClosed_closedPoint k X ⟨x, hx⟩⟩
  obtain ⟨y, hy⟩ := nonempty_closedPoint k X
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  rw [← hη, hx.closure_eq] at hcl
  have : y ∈ ({x} : Set X) := hcl ▸ Set.mem_univ y
  exact hy (this.trans hη)

/-- Weil divisors on a curve. -/
abbrev CurveDivisor : Type u := ClosedPoint X →₀ ℤ

/-- Divisors on `X` are divisors of the function field. -/
noncomputable def divisorEquiv : CurveDivisor X ≃+ Divisor k X.functionField :=
  Finsupp.domCongr (curvePlaceEquiv k X)

@[simp]
lemma divisorEquiv_apply (D : CurveDivisor X) (x : ClosedPoint X) :
    divisorEquiv k X D (curvePlaceEquiv k X x) = D x := by
  simp [divisorEquiv, Finsupp.domCongr_apply]

/-- The degree `[κ(x) : k]` of a closed point (that of the corresponding place). -/
noncomputable def pointDegree (x : ClosedPoint X) : ℕ := (curvePlaceEquiv k X x).deg

/-- The degree of a divisor on `X`. -/
noncomputable def CurveDivisor.deg (D : CurveDivisor X) : ℤ := (divisorEquiv k X D).deg

lemma CurveDivisor.deg_single (x : ClosedPoint X) (n : ℤ) :
    CurveDivisor.deg k X (Finsupp.single x n) = n * pointDegree k X x := by
  simp [CurveDivisor.deg, divisorEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single,
    Divisor.deg_single, pointDegree]

/-- The divisor of a rational function on `X`. -/
noncomputable def curveDiv (f : X.functionField) : CurveDivisor X :=
  (divisorEquiv k X).symm (Divisor.div k f)

@[simp]
lemma curveDiv_apply (f : X.functionField) (x : ClosedPoint X) :
    curveDiv k X f x = (curvePlaceEquiv k X x).ord f := by
  rw [← divisorEquiv_apply k X, curveDiv, AddEquiv.apply_symm_apply, Divisor.div_apply]

lemma curveDiv_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    curveDiv k X (f * g) = curveDiv k X f + curveDiv k X g := by
  rw [curveDiv, Divisor.div_mul hf hg, map_add]
  rfl

/-- **Principal divisors have degree zero** on a curve. -/
lemma deg_curveDiv (f : X.functionField) : CurveDivisor.deg k X (curveDiv k X f) = 0 := by
  rw [CurveDivisor.deg, curveDiv, AddEquiv.apply_symm_apply]
  exact Divisor.deg_div f

/-- A nonzero rational function lies in the local ring at a closed point iff its order there is
nonnegative. -/
lemma mem_stalk_iff {f : X.functionField} (hf : f ≠ 0) (x : ClosedPoint X) :
    f ∈ stalkValuationSubring (valuationRing_stalk_of_isCurveOver k X) x.1 ↔
      0 ≤ curveDiv k X f x := by
  rw [curveDiv_apply, ← curvePlaceEquiv_apply k X x, Place.mem_iff_ord_nonneg]
  simp [hf]

/-- The principal divisors on `X`. -/
noncomputable def curvePrincipal : AddSubgroup (CurveDivisor X) :=
  (principal k X.functionField).comap (divisorEquiv k X).toAddMonoidHom

lemma curveDiv_mem_curvePrincipal {f : X.functionField} (hf : f ≠ 0) :
    curveDiv k X f ∈ curvePrincipal k X := by
  change divisorEquiv k X (curveDiv k X f) ∈ principal k X.functionField
  rw [curveDiv, AddEquiv.apply_symm_apply]
  exact div_mem_principal hf

lemma map_curvePrincipal :
    (curvePrincipal k X).map (divisorEquiv k X).toAddMonoidHom = principal k X.functionField := by
  rw [curvePrincipal, AddSubgroup.map_comap_eq_self_of_surjective]
  exact (divisorEquiv k X).surjective

/-- **The Picard (divisor class) group of a curve.** -/
abbrev CurvePic : Type u := CurveDivisor X ⧸ curvePrincipal k X

/-- The Picard group of `X` is that of its function field. -/
noncomputable def curvePicEquiv : CurvePic k X ≃+ Pic k X.functionField :=
  QuotientAddGroup.congr _ _ (divisorEquiv k X) (map_curvePrincipal k X)

/-- The degree on the Picard group of `X`. -/
noncomputable def CurvePic.deg : CurvePic k X →+ ℤ :=
  (Pic.deg k X.functionField).comp (curvePicEquiv k X).toAddMonoidHom

@[simp]
lemma CurvePic.deg_mk (D : CurveDivisor X) :
    CurvePic.deg k X (QuotientAddGroup.mk D) = CurveDivisor.deg k X D :=
  rfl

/-- `Pic⁰` of a curve: the divisor classes of degree zero. -/
noncomputable def CurvePic0 : AddSubgroup (CurvePic k X) := (CurvePic.deg k X).ker

end CurvesJacobian
