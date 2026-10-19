/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.WeilGenericPoint
import CurvesJacobian.Kummer.JacobianTorsionCount
import CurvesJacobian.Kummer.JacobianTorsion
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The Weil pairing: Galois equivariance, nondegeneracy and perfectness on `J(k̄)[n]`

* `CurvesJacobian.Kummer.constRes τ`: the automorphism of the constants `κ` induced by
  `τ ∈ constAut κ K`; `placeMap_eq_placeTr`, `picMap_eq_picTr`.
* **`CurvesJacobian.Kummer.weilPairing_picMap`** (Galois equivariance):
  `e_n(τ a, τ b) = τ(e_n(a, b))`.
* `CurvesJacobian.Kummer.weilPairing_nondegenerate_of_algEquiv`: nondegeneracy transports along
  `κ`-isomorphisms of function fields; `weilPairing_self_curve` (alternating) for curves.
* `CurvesJacobian.Kummer.weilDual`, **`weilDual_bijective`** (perfectness): for a nondegenerate
  pairing on a finite `Pic(K)[n]` (`κ` algebraically closed of characteristic `0`),
  `b ↦ e_n(·, b)` is a bijection `Pic(K)[n] ≃ Hom(Pic(K)[n], κˣ)` (`= Hom(Pic(K)[n], μ_n)`), by
  counting (`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`).
* For the Galois model `D = curveGaloisData k hτ` of a curve `X/k` (`F k̄ = K(X_{k̄})`):
  `weilPairing_picAct` (`e_n(h a, h b) = h(e_n(a, b))` for `h ∈ H`, acting on `k̄` through
  `G_k`), **`weilPairing_nondegenerate_baseChange`**, `weilPairing_self_baseChange`,
  **`weilDual_bijective_baseChange`**.
-/

open WeilCurves.FunctionField AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open CurvesJacobian.Cusp

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.Kummer

section ConstAut

variable {κ K : Type*} [Field κ] [Field K] [Algebra κ K]

/-- The automorphism of the constants induced by `τ ∈ constAut κ K`:
`τ (c • 1) = (constRes τ c) • 1`. -/
def constRes (τ : constAut κ K) : κ ≃+* κ where
  toFun c := ((τ.2 c).1).choose
  invFun c := ((τ.2 c).2).choose
  left_inv c := by
    apply (algebraMap κ K).injective
    rw [((τ.2 _).2).choose_spec, ((τ.2 c).1).choose_spec, RingEquiv.symm_apply_apply]
  right_inv c := by
    apply (algebraMap κ K).injective
    rw [((τ.2 _).1).choose_spec, ((τ.2 c).2).choose_spec, RingEquiv.apply_symm_apply]
  map_mul' a b := by
    apply (algebraMap κ K).injective
    rw [((τ.2 _).1).choose_spec, map_mul, map_mul, map_mul, ((τ.2 a).1).choose_spec,
      ((τ.2 b).1).choose_spec]
  map_add' a b := by
    apply (algebraMap κ K).injective
    rw [((τ.2 _).1).choose_spec, map_add, map_add, map_add, ((τ.2 a).1).choose_spec,
      ((τ.2 b).1).choose_spec]

lemma constRes_spec (τ : constAut κ K) (c : κ) :
    (τ : K ≃+* K) (algebraMap κ K c) = algebraMap κ K (constRes τ c) :=
  ((τ.2 c).1).choose_spec.symm

lemma placeMap_eq_placeTr (τ : constAut κ K) (Q : Place κ K) :
    placeMap τ Q = placeTr (τ : K ≃+* K) (constRes τ) (constRes_spec τ) Q :=
  Place.ext rfl

lemma placeEquiv_eq (τ : constAut κ K) :
    placeEquiv τ = placeTrEquiv (τ : K ≃+* K) (constRes τ) (constRes_spec τ) :=
  Equiv.ext fun Q ↦ placeMap_eq_placeTr τ Q

variable [PerfectField κ] [IsFunctionField κ K]

lemma divMap_eq_divTr (τ : constAut κ K) (D : Divisor κ K) :
    divMap τ D = divTr (τ : K ≃+* K) (constRes τ) (constRes_spec τ) D := by
  change Finsupp.domCongr (placeEquiv τ) D = Finsupp.domCongr (placeTrEquiv _ _ _) D
  rw [placeEquiv_eq]

lemma picMap_eq_picTr (τ : constAut κ K) (x : Pic κ K) :
    picMap τ x = picTr (τ : K ≃+* K) (constRes τ) (constRes_spec τ) x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [picMap_mk, picTr_mk, divMap_eq_divTr]

end ConstAut

section Equivariance

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

lemma picMap_mem_picTorsion' {n : ℕ} (τ : constAut κ K) {x : Pic κ K}
    (hx : x ∈ picTorsion κ K n) : picMap τ x ∈ picTorsion κ K n := by
  change n • picMap τ x = 0
  rw [← map_nsmul, show n • x = 0 from hx, map_zero]

/-- **Galois equivariance of the Weil pairing**: `e_n(τ a, τ b) = τ(e_n(a, b))` for
`τ ∈ constAut κ K` (acting on the constants by `constRes τ`). -/
theorem weilPairing_picMap {n : ℕ} [NeZero n] (τ : constAut κ K) (a b : picTorsion κ K n) :
    weilPairing n ⟨picMap τ a, picMap_mem_picTorsion' τ a.2⟩
      ⟨picMap τ b, picMap_mem_picTorsion' τ b.2⟩ = constRes τ (weilPairing n a b) := by
  rw [← weilPairing_tr (τ : K ≃+* K) (constRes τ) (constRes_spec τ)]
  congr 1

end Equivariance

section Transport

variable {κ K K' : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]
  [Field K'] [Algebra κ K'] [IsFunctionField κ K'] (e : K ≃ₐ[κ] K')

include e in
/-- Nondegeneracy transports along `κ`-isomorphisms of function fields. -/
theorem weilPairing_nondegenerate_of_algEquiv {n : ℕ} [NeZero n]
    (h : ∀ a : picTorsion κ K' n, (∀ b, weilPairing n a b = 1) → a = 0)
    (a : picTorsion κ K n) (ha : ∀ b, weilPairing n a b = 1) : a = 0 := by
  set φ : K ≃+* K' := e.toRingEquiv
  have hφ : ∀ c : κ, φ (algebraMap κ K c) = algebraMap κ K' (RingEquiv.refl κ c) :=
    fun c ↦ e.commutes c
  have hsurj : Function.Surjective (picTorsionTr φ (RingEquiv.refl κ) hφ n) := by
    intro b'
    refine ⟨⟨(picTr φ (RingEquiv.refl κ) hφ).symm b', ?_⟩, Subtype.ext ?_⟩
    · change n • (picTr φ (RingEquiv.refl κ) hφ).symm b' = 0
      rw [← map_nsmul, show n • (b' : Pic κ K') = 0 from b'.2, map_zero]
    · exact (picTr φ (RingEquiv.refl κ) hφ).apply_symm_apply _
  have h0 := h (picTorsionTr φ (RingEquiv.refl κ) hφ n a) fun b' ↦ by
    obtain ⟨b, rfl⟩ := hsurj b'
    rw [weilPairing_tr, ha b, map_one]
  apply Subtype.ext
  have := congrArg Subtype.val h0
  simp only [coe_picTorsionTr, ZeroMemClass.coe_zero] at this
  exact (AddEquiv.map_eq_zero_iff _).mp this

end Transport

section Perfect

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [CharZero κ] [Field K] [Algebra κ K]
  [IsFunctionField κ K] {n : ℕ} [NeZero n]

/-- `e_n(·, b)` as a character `Pic(K)[n] → κˣ`. -/
def weilChar (b : picTorsion κ K n) : Multiplicative (picTorsion κ K n) →* κˣ where
  toFun a := Units.mk0 (weilPairing n (Multiplicative.toAdd a) b) (weilPairing_ne_zero _ _)
  map_one' := Units.ext (weilPairing_zero_left b)
  map_mul' _ _ := Units.ext (weilPairing_add_left _ _ b)

/-- **The Weil duality map** `b ↦ e_n(·, b)`, `Pic(K)[n] → Hom(Pic(K)[n], κˣ)`. -/
def weilDual : picTorsion κ K n → (Multiplicative (picTorsion κ K n) →* κˣ) := weilChar

lemma weilDual_injective (h : ∀ a : picTorsion κ K n, (∀ b, weilPairing n a b = 1) → a = 0) :
    Function.Injective (weilDual (κ := κ) (K := K) (n := n)) := by
  intro b b' hbb'
  have key : ∀ a : picTorsion κ K n, weilPairing n (b - b') a = 1 := fun a ↦ by
    have h1 := congrArg (fun χ ↦ ((χ (Multiplicative.ofAdd a) : κˣ) : κ)) hbb'
    simp only [weilDual, weilChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
      Units.val_mk0] at h1
    rw [weilPairing_swap, sub_eq_add_neg, weilPairing_add_right]
    have hneg : weilPairing n a (-b') = (weilPairing n a b')⁻¹ := by
      have h2 := weilPairing_add_right a b' (-b')
      rw [add_neg_cancel, weilPairing_zero_right] at h2
      exact eq_inv_of_mul_eq_one_right h2.symm
    rw [hneg, h1, mul_inv_cancel₀ (weilPairing_ne_zero _ _), inv_one]
  exact sub_eq_zero.mp (h _ key)

/-- **Perfectness of the Weil pairing**: a nondegenerate `e_n` on a finite `Pic(K)[n]` identifies
`Pic(K)[n]` with its dual `Hom(Pic(K)[n], κˣ)`. -/
theorem weilDual_bijective [Finite (picTorsion κ K n)]
    (h : ∀ a : picTorsion κ K n, (∀ b, weilPairing n a b = 1) → a = 0) :
    Function.Bijective (weilDual (κ := κ) (K := K) (n := n)) := by
  haveI : NeZero (Monoid.exponent (Multiplicative (picTorsion κ K n)) : κ) :=
    ⟨Nat.cast_ne_zero.mpr (Monoid.exponent_ne_zero_of_finite)⟩
  haveI : Finite (Multiplicative (picTorsion κ K n) →* κˣ) := Finite.of_equiv _
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      (Multiplicative (picTorsion κ K n)) κ).some.toEquiv.symm
  refine (weilDual_injective h).bijective_of_nat_card_le ?_
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  rfl

end Perfect

section GaloisModel

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

lemma coe_constRes_autF (h : D.H) (c : kbar k Ω) :
    ((constRes (autF D h) c : kbar k Ω) : Ω) = (h : Ω ≃ₐ[K₀ k t] Ω) c := by
  have h1 := congrArg (fun x : F (baseChange D) ↦ (x : Ω)) (constRes_spec (autF D h) c)
  simp only [coe_autF_apply] at h1
  exact h1.symm

/-- **Galois equivariance of the Weil pairing on `J(k̄)[n]`**: `e_n(h a, h b) = h(e_n(a, b))`
for `h ∈ H` (acting on `J(k̄) = Pic(F k̄)` by `picAct` and on `μ_n ⊆ k̄ ⊆ Ω` through `G_k`). -/
theorem weilPairing_picAct {n : ℕ} [NeZero n] (h : D.H)
    (a b : picTorsion (kbar k Ω) (F (baseChange D)) n) :
    ((weilPairing n ⟨picAct D h a, picAct_mem_picTorsion D h a.2⟩
      ⟨picAct D h b, picAct_mem_picTorsion D h b.2⟩ : kbar k Ω) : Ω) =
      (h : Ω ≃ₐ[K₀ k t] Ω) (weilPairing n a b : kbar k Ω) := by
  rw [← coe_constRes_autF]
  exact congrArg (fun c : kbar k Ω ↦ (c : Ω)) (weilPairing_picMap (autF D h) a b)

end GaloisModel

section Curve

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- **Nondegeneracy of the Weil pairing on `J(k̄)[n] = Pic(F k̄)[n]`** for the Galois model of a
curve over a field of characteristic `0`. -/
theorem weilPairing_nondegenerate_baseChange {n : ℕ} [NeZero n]
    (a : picTorsion (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) n)
    (ha : ∀ b, weilPairing n a b = 1) : a = 0 :=
  weilPairing_nondegenerate_of_algEquiv (ffEquiv k hτ)
    (fun a' ha' ↦ GenericPoint.weilPairing_nondegenerate (kbar k (FFClosure X))
      (baseChangeKbar k X) a' ha') a ha

instance finite_picTorsion_baseChange {n : ℕ} [NeZero n] :
    Finite (picTorsion (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) n) :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_picTorsion_baseChange' k hτ n]; exact pow_ne_zero _ (NeZero.ne n))

/-- **The Weil pairing on `J(k̄)[n]` is alternating**: `e_n(a, a) = 1`. -/
theorem weilPairing_self_baseChange {n : ℕ} [NeZero n]
    (a : picTorsion (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) n) :
    weilPairing n a a = 1 := by
  refine weilPairing_self a ?_
  obtain ⟨y, hy, h2⟩ := exists_nsmul_eq_of_mem_picTorsion_baseChange k hτ
    (Nat.pos_of_ne_zero (NeZero.ne n)) two_pos a.2
  exact ⟨⟨y, hy⟩, h2⟩

/-- **Perfectness of the Weil pairing on `J(k̄)[n]`**: `b ↦ e_n(·, b)` is a bijection
`J(k̄)[n] ≃ Hom(J(k̄)[n], k̄ˣ)`. -/
theorem weilDual_bijective_baseChange {n : ℕ} [NeZero n] :
    Function.Bijective (weilDual (κ := kbar k (FFClosure X))
      (K := F (Kummer.baseChange (curveGaloisData k hτ))) (n := n)) :=
  weilDual_bijective (weilPairing_nondegenerate_baseChange k hτ)

end Curve

end CurvesJacobian.Kummer
