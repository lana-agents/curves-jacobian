/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianTorsionCount
import CurvesJacobian.Cusp.GenusLocAnEq

/-!
# The genus of the Galois model `F k̄` of a curve

* `CurvesJacobian.deg_placeMap`, `CurvesJacobian.deg_divisorEquivOfAlgEquiv`,
  `CurvesJacobian.ell_divisorEquivOfAlgEquiv`: degrees of places and divisors and the dimensions
  `ℓ(A)` are invariant under `k`-isomorphisms of function fields;
* `CurvesJacobian.genus_congr`: hence so is the genus `riemannConst + 1`;
* `CurvesJacobian.Kummer.genus_baseChange_eq_curveGenus`: for the Galois model
  `D = curveGaloisData k hτ` of a curve `X` (characteristic `0`), `g(F k̄) = g(X)`
  (`F k̄ ≃ K(X_{k̄})`, `CurvesJacobian.Kummer.ffEquiv`, and `g(X_{k̄}) = g(X)`);
* `CurvesJacobian.Kummer.genus_baseChange_ne_zero_of_curveGenus`,
  `genus_baseChange_ne_zero_of_locAn`, `genus_baseChange_ne_zero_of_hypCurve`: the hypothesis
  `g(F k̄) ≠ 0` from `g(X) ≠ 0`, from `dim H⁰(X, Ω¹) ≠ 0`, and for a proper hyperbolic curve
  (no cusps, so `2 < 2g`).
-/

open CategoryTheory AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian

section Transport

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  (e : K ≃ₐ[k] K')

/-- `O_P ≃ O_{e P}`. -/
def placeMapRingEquiv (P : Place k K) : P.1 ≃+* (placeMap e P).1 where
  toFun x := ⟨e (x : K), (mem_placeMap_apply e P x).2 x.2⟩
  invFun y := ⟨e.symm (y : K'), (mem_placeMap e P y).1 y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : K))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K'))
  map_mul' x y := Subtype.ext (map_mul e (x : K) y)
  map_add' x y := Subtype.ext (map_add e (x : K) y)

/-- `κ(P) ≃ₐ[k] κ(e P)`. -/
def residueFieldAlgEquiv (P : Place k K) :
    P.ResidueField ≃ₐ[k] (placeMap e P).ResidueField :=
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv (placeMapRingEquiv e P)) fun c ↦ by
    change IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ (P.baseHom c)) =
      IsLocalRing.residue _ ((placeMap e P).baseHom c)
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    exact Subtype.ext (e.commutes c)

theorem deg_placeMap (P : Place k K) : (placeMap e P).deg = P.deg :=
  (residueFieldAlgEquiv e P).toLinearEquiv.finrank_eq.symm

variable [PerfectField k] [IsFunctionField k K] [IsFunctionField k K']

omit [PerfectField k] [IsFunctionField k K] [IsFunctionField k K'] in
theorem deg_divisorEquivOfAlgEquiv (A : Divisor k K) :
    (divisorEquivOfAlgEquiv e A).deg = A.deg := by
  induction A using Finsupp.induction_linear with
  | zero => rw [map_zero, Divisor.deg_zero, Divisor.deg_zero]
  | add A B hA hB => rw [map_add, Divisor.deg_add, Divisor.deg_add, hA, hB]
  | single P n =>
    change Divisor.deg (Finsupp.equivMapDomain (placeEquivOfAlgEquiv e) (Finsupp.single P n)) = _
    rw [Finsupp.equivMapDomain_single, Divisor.deg_single, Divisor.deg_single]
    change (n : ℤ) * ((placeMap e P).deg : ℤ) = _
    rw [deg_placeMap]

theorem mem_L_divisorEquivOfAlgEquiv (A : Divisor k K) (f : K) :
    e f ∈ Divisor.L (divisorEquivOfAlgEquiv e A) ↔ f ∈ Divisor.L A := by
  rw [Divisor.mem_L, Divisor.mem_L, map_eq_zero_iff e e.injective]
  refine or_congr Iff.rfl ?_
  rw [← (placeEquivOfAlgEquiv e).forall_congr_right]
  refine forall_congr' fun P ↦ ?_
  change -(Finsupp.equivMapDomain (placeEquivOfAlgEquiv e) A) (placeMap e P) ≤
    (placeMap e P).ord (e f) ↔ _
  rw [Finsupp.equivMapDomain_apply, ord_placeMap]
  change -A ((placeEquivOfAlgEquiv e).symm (placeEquivOfAlgEquiv e P)) ≤ _ ↔ _
  rw [Equiv.symm_apply_apply]

theorem L_divisorEquivOfAlgEquiv (A : Divisor k K) :
    Divisor.L (divisorEquivOfAlgEquiv e A) = (Divisor.L A).map e.toLinearEquiv.toLinearMap := by
  ext y
  rw [Submodule.mem_map_equiv, ← mem_L_divisorEquivOfAlgEquiv e A]
  change _ ↔ e (e.symm y) ∈ _
  rw [e.apply_symm_apply]

theorem ell_divisorEquivOfAlgEquiv (A : Divisor k K) :
    (divisorEquivOfAlgEquiv e A).ell = A.ell := by
  rw [Divisor.ell, Divisor.ell, L_divisorEquivOfAlgEquiv, LinearEquiv.finrank_map_eq]

include e in
theorem riemannConst_congr : Divisor.riemannConst k K = Divisor.riemannConst k K' := by
  unfold Divisor.riemannConst
  have h : (fun A : Divisor k K' ↦ A.deg - (A.ell : ℤ)) ∘ divisorEquivOfAlgEquiv e =
      fun A : Divisor k K ↦ A.deg - (A.ell : ℤ) := by
    funext A
    simp only [Function.comp_apply, deg_divisorEquivOfAlgEquiv, ell_divisorEquivOfAlgEquiv]
  rw [← h, Set.range_comp, (divisorEquivOfAlgEquiv e).surjective.range_eq, Set.image_univ]

include e in
/-- **The genus is invariant under `k`-isomorphisms of function fields.** -/
theorem genus_congr : genus k K = genus k K' := by
  rw [genus, genus, riemannConst_congr e]

end Transport

namespace Kummer

open CurvesJacobian.Cusp

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- **`g(F k̄) = g(X)`** for the Galois model `D = curveGaloisData k hτ` of a curve `X` over a
field of characteristic `0`. -/
theorem genus_baseChange_eq_curveGenus :
    genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) =
      curveGenus k X := by
  rw [genus_congr (ffEquiv k hτ), ← curveGenus_baseChangeKbar k X]
  rfl

theorem genus_baseChange_ne_zero_of_curveGenus (hg : curveGenus k X ≠ 0) :
    genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0 := by
  rwa [genus_baseChange_eq_curveGenus]

/-- `g(F k̄) ≠ 0` from `dim_k H⁰(X, Ω¹) ≠ 0`. -/
theorem genus_baseChange_ne_zero_of_locAn (hg : Anabelian.curveGenus k X ≠ 0) :
    genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0 := by
  rw [genus_baseChange_eq_curveGenus, ← locAn_curveGenus_eq k X]
  exact_mod_cast hg

end Kummer

/-- A proper hyperbolic curve (no cusps) has `dim_k H⁰(X̄, Ω¹) ≥ 2`. -/
theorem two_le_locAn_curveGenus_of_hypCurve {k : Type u} [Field k]
    (C : Anabelian.HypCurve k) [IsIntegral C.Xbar] (hU : (C.U : Set C.Xbar)ᶜ = ∅) :
    2 ≤ Anabelian.curveGenus k C.Xbar := by
  have h := C.hyperbolic
  rw [Anabelian.cuspDegree, hU, finsum_mem_empty] at h
  omega

namespace Kummer

open CurvesJacobian.Cusp

attribute [local instance] isFunctionField_F

/-- A proper hyperbolic curve (no cusps) has `g(X̄) ≥ 2`. -/
theorem two_le_curveGenus_of_hypCurve (k : Type u) [Field k] [CharZero k]
    (C : Anabelian.HypCurve k) [IsIntegral C.Xbar] (hU : (C.U : Set C.Xbar)ᶜ = ∅) :
    2 ≤ curveGenus k C.Xbar := by
  rw [← locAn_curveGenus_eq k C.Xbar]
  exact_mod_cast two_le_locAn_curveGenus_of_hypCurve C hU

/-- `g(F k̄) ≠ 0` for the Galois model of a proper hyperbolic curve `C` (no cusps). -/
theorem genus_baseChange_ne_zero_of_hypCurve (k : Type u) [Field k] [CharZero k]
    (C : Anabelian.HypCurve k) [IsIntegral C.Xbar] (hU : (C.U : Set C.Xbar)ᶜ = ∅)
    {τ : C.Xbar.functionField} (hτ : Transcendental k τ)
    [IsGalois (K₀ k (coordT τ)) (FFClosure C.Xbar)] :
    genus (kbar k (FFClosure C.Xbar)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0 :=
  genus_baseChange_ne_zero_of_curveGenus k hτ (by
    have := two_le_curveGenus_of_hypCurve k C hU
    omega)

end Kummer

end CurvesJacobian
