/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianBridgeSurj
import CurvesJacobian.Kummer.WeilGenericPoint
import CurvesJacobian.Cusp.CoverGaloisData

/-!
# `Pic⁰` of a curve over an algebraically closed field is divisible

Let `k` be algebraically closed of characteristic `0`.

* `CurvesJacobian.deg_picEquivOfAlgEquiv`, `CurvesJacobian.exists_nsmul_eq_of_algEquiv`:
  `k`-isomorphisms of function fields preserve degrees of divisor classes, hence divisibility
  of `Pic⁰`.
* `CurvesJacobian.selfBaseChangeAlgEquiv`: `K(X) ≃ₐ[k] K(X_k)` for the trivial base change
  `X_k = X ×_k k` (the projection `X_k ⟶ X` is an isomorphism over `Spec k`).
* **`CurvesJacobian.exists_nsmul_eq_picZero_functionField`**: for a curve `X/k`,
  `Pic⁰(K(X))` is divisible (JAC-4a, `exists_nsmul_eq_picZero_of_charZero` for `κ = k`, with a
  `k`-rational point from `GenericPoint.exists_section`).
* **`CurvesJacobian.exists_nsmul_eq_of_deg_eq_zero`**: in the Galois model
  (`eL : K(X) ≃ L`, `H ≤ H_L`), `Pic⁰(F D)` is divisible.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField Pi1.Orbifold
open AffOrbicurve KummerTheory Curve

universe u

noncomputable section

namespace CurvesJacobian

section Transport

variable {κ K K' : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Field K'] [Algebra κ K]
  [Algebra κ K'] [IsFunctionField κ K] [IsFunctionField κ K'] (e : K ≃ₐ[κ] K')

/-- `k`-isomorphisms of function fields over an algebraically closed field preserve degrees of
divisor classes. -/
lemma deg_picEquivOfAlgEquiv (x : Pic κ K) :
    Pic.deg κ K' (picEquivOfAlgEquiv e x) = Pic.deg κ K x := by
  induction x using QuotientAddGroup.induction_on with
  | H E => exact Kummer.deg_divisorEquivOfAlgEquiv e E

include e in
/-- Divisibility of `Pic⁰` is invariant under `k`-isomorphisms of function fields. -/
lemma exists_nsmul_eq_of_algEquiv {n : ℕ}
    (h : ∀ y : (Pic.deg κ K).ker, ∃ x : (Pic.deg κ K).ker, n • x = y)
    (y : (Pic.deg κ K').ker) : ∃ x : (Pic.deg κ K').ker, n • x = y := by
  set φ := picEquivOfAlgEquiv e
  have hy : φ.symm y.1 ∈ (Pic.deg κ K).ker := by
    rw [AddMonoidHom.mem_ker, ← deg_picEquivOfAlgEquiv e, AddEquiv.apply_symm_apply]
    exact y.2
  obtain ⟨x, hx⟩ := h ⟨_, hy⟩
  refine ⟨⟨φ x.1, ?_⟩, Subtype.ext ?_⟩
  · rw [AddMonoidHom.mem_ker, deg_picEquivOfAlgEquiv e]
    exact x.2
  · change n • φ x.1 = y.1
    rw [← map_nsmul, ← AddSubgroup.coe_nsmul, hx]
    exact φ.apply_symm_apply _

end Transport

section SelfBaseChange

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "Xk" => pullback (X ↘ Sk) (specAlgebraMap k k)

omit [X.Over (Spec (.of k))] in
/-- `Spec k ⟶ Spec k` induced by `k → k` is the identity. -/
lemma specAlgebraMap_self : specAlgebraMap k k = 𝟙 Sk := by
  rw [specAlgebraMap, show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from rfl, Spec.map_id]

instance isIso_fst_self : IsIso (pullback.fst (X ↘ Sk) (specAlgebraMap k k)) := by
  have : IsIso (specAlgebraMap k k) := by rw [specAlgebraMap_self]; infer_instance
  infer_instance

/-- The projection `X_k ⟶ X` is a morphism over `Spec k`. -/
lemma over_fst_self : (Xk ↘ Sk) = pullback.fst (X ↘ Sk) (specAlgebraMap k k) ≫ (X ↘ Sk) := by
  change pullback.snd _ _ = _
  rw [pullback.condition]
  exact (Category.comp_id _).symm.trans
    (congrArg (pullback.snd (X ↘ Sk) (specAlgebraMap k k) ≫ ·) (specAlgebraMap_self (k := k)).symm)

omit [X.Over (Spec (.of k))] in
lemma isIso_stalkSpecializes_of_eq {Y : Scheme.{u}} {x y : Y} (e : x = y) (h : x ⤳ y) :
    IsIso (Y.presheaf.stalkSpecializes h) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

omit [X.Over (Spec (.of k))] in
/-- The map of function fields induced by an isomorphism of integral schemes is bijective. -/
lemma bijective_functionFieldMap_of_isIso {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (q : Y ⟶ Z) [IsIso q] (hq : q (genericPoint Y) = genericPoint Z) :
    Function.Bijective (Cusp.functionFieldMap q hq) := by
  haveI := isIso_stalkSpecializes_of_eq hq (show q (genericPoint Y) ⤳ genericPoint Z by rw [hq])
  haveI : IsIso (Cusp.functionFieldMap q hq) := by
    unfold Cusp.functionFieldMap
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (Cusp.functionFieldMap q hq)

variable [IsCurveOver k X] [IsIntegral X]

/-- **`K(X) ≃ₐ[k] K(X_k)`** for the trivial base change `X_k = X ×_k k`. -/
def selfBaseChangeAlgEquiv : X.functionField ≃ₐ[k] (Xk).functionField :=
  AlgEquiv.ofBijective
    (Cusp.functionFieldAlgHom (pullback.fst (X ↘ Sk) (specAlgebraMap k k)) (over_fst_self X)
      (Kummer.fst_genericPoint k k))
    (bijective_functionFieldMap_of_isIso _ _)

end SelfBaseChange

section Divisible

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {n : ℕ}

/-- **`Pic⁰(K(X))` is divisible** for a curve `X` over an algebraically closed field `k` of
characteristic `0` (JAC-4a: `J(k)` is divisible, transported along `Pic⁰(K(X_k)) ≃ J(k)` and
`K(X) ≃ₐ[k] K(X_k)`; a rational point exists as `k = k̄`). -/
theorem exists_nsmul_eq_picZero_functionField (hn : n ≠ 0)
    (y : (Pic.deg k X.functionField).ker) :
    ∃ x : (Pic.deg k X.functionField).ker, n • x = y := by
  obtain ⟨σ, hσ⟩ := GenericPoint.exists_section k X
  exact exists_nsmul_eq_of_algEquiv (selfBaseChangeAlgEquiv X).symm
    (exists_nsmul_eq_picZero_of_charZero X k σ hσ hn) y

end Divisible

section Galois

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
  [Field Ω] [Algebra k Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L}

attribute [local instance] isFunctionField_F

/-- **`K(X) ≃ₐ[k] F D`** in the Galois model with `H ≤ H_L` (so `F D = L`). -/
def functionFieldEquivF (hH : D.H ≤ D.HL)
    (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c) :
    X.functionField ≃ₐ[k] F D :=
  { eL.trans (IntermediateField.equivOfEq
      (show D.L = F D by rw [GaloisData.L, F, le_antisymm hH D.le])).toRingEquiv with
    commutes' := fun c ↦ Subtype.ext (by
      change ((eL (algebraMap k X.functionField c) : D.L) : Ω) = _
      rw [hk]
      rfl) }

/-- **`Pic⁰` of the Galois model is divisible** ([AbsTopIII] §1, step b4 of MR5): for
`F D = L ≅ K(X)` with `X` a curve over `k = k̄` of characteristic `0`, every degree-zero divisor
class of `F D` is `n` times a degree-zero class, `n ≥ 1`. -/
theorem exists_nsmul_eq_of_deg_eq_zero (hH : D.H ≤ D.HL)
    (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
    (hn : n ≠ 0) (y : (Pic.deg k (F D)).ker) : ∃ x : (Pic.deg k (F D)).ker, n • x = y :=
  exists_nsmul_eq_of_algEquiv (functionFieldEquivF hH hk)
    (exists_nsmul_eq_picZero_functionField X hn) y

end Galois

end CurvesJacobian
