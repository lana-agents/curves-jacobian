/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspInertiaQuotient
import CurvesJacobian.Cusp.CuspTerminalFew
import CurvesJacobian.Cusp.SingleCusp
import CurvesJacobian.Galois.FunctionFieldF
import CurvesJacobian.LocAn.Stabilizer

/-!
# Inner rigidity in the Galois model of a curve (MR7, steps G2–G3)

Let `k` be algebraically closed of characteristic `0`, `X` a curve over `k` with Galois model
`(D, eL)` (`Ω ⊇ L ≅ K(X)`, `H ≤ H_L`), and `U ⊆ X` a hyperbolic open (`2 < 2g + r`,
`r = |X ∖ U| ≥ 1`). Let `σ` be a ring automorphism of `Ω` fixing `k`, preserving `L`, mapping the
sections `eL(Γ(U))` onto themselves, and such that **conjugation by `σ` does not change the action
on `π₁ᵉᵗ(U)`**: `chartHom (σ⁻¹ n σ) = chartHom n` for `n ∈ H`. Then `σ` is the identity on `L`
(`CurvesJacobian.LocAn.eq_of_chartHom_conj`).

This is the core of the uniqueness half of the relative Grothendieck conjecture for affine
hyperbolic curves (MR7 plan, "S2 route"): an automorphism of a curve acting on `π₁` by an inner
automorphism lifts to such a `σ` (`LocAn/InnerRigidAffine.lean`).

## Proof

* (G2) For every place `W` over a cusp, `σ⁻¹(W)` has the same cuspidal inertia group as `W`, so
  by terminality (`exists_mem_ker_comap_eq`) `σ⁻¹(W) = n(W)` for some `n` acting trivially on
  `π₁ᵉᵗ(U)` (`exists_ker_comap_eq_of_chartHom_conj`). Hence `σ|_L` fixes every cusp.
* (F2/F3) In genus `0`, `σ|_L` fixes the `r ≥ 3` cusps and is the identity
  (`eq_one_of_genus_eq_zero`); in genus `≥ 1` it has finite order `m`
  (`exists_pow_eq_one_of_fixes`). Then `σ^m ∈ H` centralises `π₁ᵉᵗ(U)`, which is centre-free, so
  `σ^m` acts trivially.
* (G3) Choose an open normal `V ⊴ π₁ᵉᵗ(U)` and `ι` in the inertia group of `W` whose image mod `V`
  has order divisible by `m` (`exists_open_normal_cuspInertia_pow`); let `E = Ω^{H_V}` (a function
  field over `k`). On `E`, `σ` and `ι` commute, fix the place below `W`, `σ^m = 1` and
  `m ∣ ord(ι)`, so `σ|_E` is a power of `ι|_E` (`exists_eq_pow_of_commute`) and fixes `L`.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold PreGaloisCategory WeilCurves.FunctionField CurvesJacobian.Cusp
open KummerTheory.Curve (F)

universe u

noncomputable section

namespace CurvesJacobian.LocAn

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

/-! ### Conjugating `H` by a ring automorphism preserving `L` -/

section Conj

variable {D}

omit [IsSepClosed Ω] [IsAlgClosed k] [CharZero k] in
lemma apply_eq_of_mem_H (hH : D.H ≤ D.HL) {n : Ω ≃ₐ[K₀ k t] Ω} (hn : n ∈ D.H) {x : Ω}
    (hx : x ∈ D.L) : n x = x := by
  have : n ∈ D.L.fixingSubgroup := D.fixingSubgroup_L ▸ hH hn
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x hx

/-- **`σ⁻¹ n σ`** for `n ∈ H`, again an element of `H` (it fixes `L`). -/
def conjH (hH : D.H ≤ D.HL) (σ : Ω ≃+* Ω) (hσL : ∀ x, x ∈ D.L ↔ σ x ∈ D.L) (n : D.H) : D.H :=
  ⟨{ (σ.trans (n : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv).trans σ.symm with
      commutes' := fun c ↦ by
        change σ.symm ((n : Ω ≃ₐ[K₀ k t] Ω) (σ (algebraMap (K₀ k t) Ω c))) = _
        have hc : algebraMap (K₀ k t) Ω c ∈ D.L := D.L.algebraMap_mem c
        rw [apply_eq_of_mem_H hH n.2 ((hσL _).1 hc), RingEquiv.symm_apply_apply] },
    D.le (by
      rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      change σ.symm ((n : Ω ≃ₐ[K₀ k t] Ω) (σ x)) = x
      rw [apply_eq_of_mem_H hH n.2 ((hσL x).1 hx), RingEquiv.symm_apply_apply])⟩

omit [IsSepClosed Ω] [IsAlgClosed k] [CharZero k] in
lemma conjH_apply (hH : D.H ≤ D.HL) (σ : Ω ≃+* Ω) (hσL : ∀ x, x ∈ D.L ↔ σ x ∈ D.L) (n : D.H)
    (x : Ω) :
    (conjH hH σ hσL n : Ω ≃ₐ[K₀ k t] Ω) x = σ.symm ((n : Ω ≃ₐ[K₀ k t] Ω) (σ x)) := rfl

omit [_root_.IsGalois (↥(K₀ k t)) Ω] [IsSepClosed Ω] [IsAlgClosed k] [CharZero k] in
lemma symm_hσL {σ : Ω ≃+* Ω} (hσL : ∀ x, x ∈ D.L ↔ σ x ∈ D.L) :
    ∀ x, x ∈ D.L ↔ σ.symm x ∈ D.L := fun x ↦ by
  rw [hσL (σ.symm x), RingEquiv.apply_symm_apply]

omit [IsSepClosed Ω] [IsAlgClosed k] [CharZero k] in
lemma conjH_conjH_symm (hH : D.H ≤ D.HL) (σ : Ω ≃+* Ω) (hσL : ∀ x, x ∈ D.L ↔ σ x ∈ D.L)
    (n : D.H) : conjH hH σ hσL (conjH hH σ.symm (symm_hσL hσL) n) = n := by
  ext x
  simp [conjH_apply]

end Conj

/-! ### Inertia groups under a ring automorphism -/

section Inertia

variable {P : Type u} [Field P] [Algebra P Ω]

omit [IsSepClosed Ω] in
lemma mem_inertia_comap_iff_of_apply (σ : Ω ≃+* Ω) (W : ValuationSubring Ω) (n m : Ω ≃ₐ[P] Ω)
    (h : ∀ x, m x = σ (n (σ.symm x))) :
    n ∈ GaloisPi1.inertia (W.comap (σ : Ω →+* Ω)) ↔ m ∈ GaloisPi1.inertia W := by
  simp only [GaloisPi1.inertia, Set.mem_setOf_eq]
  have key : ∀ x : Ω, (W.comap (σ : Ω →+* Ω)).valuation x < 1 ↔ W.valuation (σ x) < 1 := by
    intro x
    rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap]
    simp
  constructor
  · intro hn a ha
    have := hn (σ.symm a) (by simpa [ValuationSubring.mem_comap] using ha)
    rw [key, map_sub, RingEquiv.apply_symm_apply] at this
    rwa [h]
  · intro hm a ha
    rw [key, map_sub]
    have := hm (σ a) ha
    rwa [h, RingEquiv.symm_apply_apply] at this

omit [IsSepClosed Ω] in
/-- Inertia elements map `W` into itself. -/
lemma mem_of_mem_inertia {W : ValuationSubring Ω} {n : Ω ≃ₐ[P] Ω}
    (hn : n ∈ GaloisPi1.inertia W) {a : Ω} (ha : a ∈ W) : n a ∈ W := by
  have h1 : n a - a ∈ W := by
    rw [← ValuationSubring.valuation_le_one_iff]
    exact (hn a ha).le
  simpa using add_mem h1 ha

omit [IsSepClosed Ω] in
/-- Inertia elements fix `W`. -/
lemma apply_mem_iff_of_mem_inertia [Algebra.IsAlgebraic P Ω] {W : ValuationSubring Ω}
    {n : Ω ≃ₐ[P] Ω} (hn : n ∈ GaloisPi1.inertia W) (a : Ω) : n a ∈ W ↔ a ∈ W := by
  refine ⟨fun h ↦ ?_, mem_of_mem_inertia hn⟩
  have hinv : n⁻¹ ∈ GaloisPi1.inertia W :=
    (GaloisPi1.inertiaSubgroup (P := P) W).inv_mem (x := n) hn
  have := mem_of_mem_inertia hinv h
  rwa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply] at this

end Inertia

/-! ### (G2) Places over cusps are fixed modulo the kernel -/

section Cusps

variable (U : X.Opens) [Nonempty U] (σ : Ω ≃+* Ω) (hσL : ∀ x, x ∈ D.L ↔ σ x ∈ D.L)
  (hσk : ∀ c : k, σ (algebraMap k Ω c) = algebraMap k Ω c)
  (hσU : ∀ b : Γ(X, U), ∃ a : Γ(X, U),
    σ ((eL (X.germToFunctionField U a) : D.L) : Ω) = ((eL (X.germToFunctionField U b) : D.L) : Ω))
  (hconj : ∀ n : D.H, D.chartHom hH (genericL D X eL U) (conjH hH σ hσL n) =
    D.chartHom hH (genericL D X eL U) n)

omit [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsAlgClosed k] [CharZero k] in
include hconj in
lemma chartHom_conjH_symm (n : D.H) :
    D.chartHom hH (genericL D X eL U) (conjH hH σ.symm (symm_hσL hσL) n) =
      D.chartHom hH (genericL D X eL U) n := by
  have := hconj (conjH hH σ.symm (symm_hσL hσL) n)
  rw [conjH_conjH_symm] at this
  exact this.symm

omit [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsAlgClosed k] [CharZero k] in
include hconj in
/-- The cuspidal inertia group of `σ⁻¹(W)` is that of `W`. -/
lemma cuspInertia_comap_eq (W : ValuationSubring Ω) :
    cuspInertia D X eL hH U (W.comap (σ : Ω →+* Ω)) = cuspInertia D X eL hH U W := by
  rw [cuspInertia, cuspInertia]
  congr 1
  ext γ
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨conjH hH σ.symm (symm_hσL hσL) n, ?_, chartHom_conjH_symm D X eL hH U σ hσL hconj n⟩
    exact (mem_inertia_comap_iff_of_apply σ W _ _ fun x ↦ rfl).1 hn
  · rintro ⟨n, hn, rfl⟩
    refine ⟨conjH hH σ hσL n, ?_, hconj n⟩
    refine (mem_inertia_comap_iff_of_apply σ W _ (n : Ω ≃ₐ[K₀ k t] Ω) fun x ↦ ?_).2 hn
    simp [conjH_apply]

include hk hτ hσk hσU hconj in
/-- **(G2) A place over a cusp is fixed by `σ` modulo the kernel of `H → π₁ᵉᵗ(U)`.** -/
theorem exists_ker_comap_eq_of_chartHom_conj (hUfin : (U : Set X)ᶜ.Finite)
    (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X))
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) :
    ∃ n : D.H, D.chartHom hH (genericL D X eL U) n = 1 ∧
      ∀ x, σ ((n : Ω ≃ₐ[K₀ k t] Ω) x) ∈ W ↔ x ∈ W := by
  set W' := W.comap (σ : Ω →+* Ω)
  have hkW' : ∀ c : k, algebraMap k Ω c ∈ W' := fun c ↦ by
    rw [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, hσk]
    exact hkW c
  have hW'U : ¬ IsCentredOn D X eL U W' := by
    rintro ⟨-, h⟩
    refine hWU ⟨hkW, fun b ↦ ?_⟩
    obtain ⟨a, ha⟩ := hσU b
    have := h a
    rwa [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, ha] at this
  have hcomm : (cuspInertia D X eL hH U W').relIndex (cuspInertia D X eL hH U W) ≠ 0 := by
    rw [cuspInertia_comap_eq D X eL hH U σ hσL hconj W, Subgroup.relIndex_self]
    exact one_ne_zero
  have hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X) ∨
      ∃ O₀ : Subgroup D.H, O₀.Normal ∧ IsOpen (O₀ : Set D.H) ∧
        (D.chartHom hH (genericL D X eL U)).ker ≤ O₀ ∧ CuspSep D O₀ W' := by
    by_cases h3 : 2 < Nat.card ((U : Set X)ᶜ : Set X)
    · exact Or.inl h3
    · exact Or.inr (exists_cuspSep D X eL hH hk hτ (by omega) hUfin hkW' hW'U)
  obtain ⟨n, hn, hnW⟩ := exists_mem_ker_comap_eq D X eL hH hk hτ hUfin hU3 hkW' hkW hW'U hWU
    hcomm
  have key : ∀ y, (n : Ω ≃ₐ[K₀ k t] Ω) y ∈ W ↔ σ y ∈ W := fun y ↦ by
    simpa [W', ValuationSubring.mem_comap] using SetLike.ext_iff.1 hnW y
  refine ⟨n⁻¹, by rw [map_inv, hn, inv_one], fun x ↦ ?_⟩
  have := key (((n⁻¹ : D.H) : Ω ≃ₐ[K₀ k t] Ω) x)
  rw [← this]
  simp

end Cusps

/-! ### Restricting ring automorphisms to intermediate fields -/

section Restrict

variable (E : IntermediateField (K₀ k t) Ω) (ρ : Ω ≃+* Ω)
  (hρE : ∀ x, x ∈ E ↔ ρ x ∈ E) (hρk : ∀ c : k, ρ (algebraMap k Ω c) = algebraMap k Ω c)

/-- The restriction of a ring automorphism `ρ` of `Ω` fixing `k` and preserving `E` to a
`k`-automorphism of `E`. -/
def restrictAlg : (↥E) ≃ₐ[k] ↥E where
  toFun x := ⟨ρ (x : Ω), (hρE x).1 x.2⟩
  invFun x := ⟨ρ.symm (x : Ω), by rw [hρE, RingEquiv.apply_symm_apply]; exact x.2⟩
  left_inv x := Subtype.ext (ρ.symm_apply_apply (x : Ω))
  right_inv x := Subtype.ext (ρ.apply_symm_apply (x : Ω))
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' c := Subtype.ext (hρk c)

omit [_root_.IsGalois (↥(K₀ k t)) Ω] [IsSepClosed Ω] [IsAlgClosed k] [CharZero k] in
@[simp] lemma coe_restrictAlg (x : E) : (restrictAlg E ρ hρE hρk x : Ω) = ρ (x : Ω) := rfl

omit [_root_.IsGalois (↥(K₀ k t)) Ω] [IsSepClosed Ω] [IsAlgClosed k] [CharZero k] in
lemma restrictAlg_pow (j : ℕ) (x : E) :
    ((restrictAlg E ρ hρE hρk ^ j) x : Ω) = (ρ ^ j) (x : Ω) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, pow_succ, RingAut.mul_apply]
    rfl

end Restrict

/-! ### `σ` on `K(X)` and the places below the cusps -/

section Main

variable (U : X.Opens) [Nonempty U] (σ : Ω ≃+* Ω) (hσL : ∀ x, x ∈ D.L ↔ σ x ∈ D.L)
  (hσk : ∀ c : k, σ (algebraMap k Ω c) = algebraMap k Ω c)
  (hσU : ∀ b : Γ(X, U), ∃ a : Γ(X, U),
    σ ((eL (X.germToFunctionField U a) : D.L) : Ω) = ((eL (X.germToFunctionField U b) : D.L) : Ω))
  (hconj : ∀ n : D.H, D.chartHom hH (genericL D X eL U) (conjH hH σ hσL n) =
    D.chartHom hH (genericL D X eL U) n)

/-- `σ` restricted to `L`. -/
def σL : D.L ≃+* D.L where
  toFun x := ⟨σ (x : Ω), (hσL x).1 x.2⟩
  invFun x := ⟨σ.symm (x : Ω), (symm_hσL hσL x).1 x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : Ω))
  right_inv x := Subtype.ext (σ.apply_symm_apply (x : Ω))
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

include hk hσk in
/-- `σ` as a `k`-automorphism of `K(X)` (through `eL : K(X) ≅ L`). -/
def σX : X.functionField ≃ₐ[k] X.functionField :=
  AlgEquiv.ofRingEquiv (f := (eL.trans (σL D σ hσL)).trans eL.symm) fun c ↦ by
    apply eL.injective
    apply Subtype.ext
    change ((eL (eL.symm (σL D σ hσL (eL (algebraMap k X.functionField c)))) : D.L) : Ω) = _
    rw [RingEquiv.apply_symm_apply]
    change σ ((eL (algebraMap k X.functionField c) : D.L) : Ω) = _
    rw [hk, hσk]

omit [IsCurveOver k X] [_root_.IsGalois (↥(K₀ k t)) Ω] [IsSepClosed Ω] [IsAlgClosed k]
  [CharZero k] in
lemma coe_eL_σX (z : X.functionField) :
    ((eL (σX D X eL hk σ hσL hσk z) : D.L) : Ω) = σ (eL z) := by
  change ((eL (eL.symm (σL D σ hσL (eL z))) : D.L) : Ω) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The place of `K(X)` below a place `W` of `Ω` over a cusp. -/
def placeOf {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) : Place k X.functionField :=
  ⟨comapK D X eL hk W, fun h ↦ hWU ⟨hkW, fun a ↦ by
      have : X.germToFunctionField U a ∈ comapK D X eL hk W := h ▸ ValuationSubring.mem_top _
      exact this⟩,
    fun c ↦ by
      change ((eL (algebraMap k X.functionField c) : D.L) : Ω) ∈ W
      rw [hk]
      exact hkW c⟩

omit [_root_.IsGalois (↥(K₀ k t)) Ω] [IsSepClosed Ω] [IsAlgClosed k] [CharZero k]
  [IsCurveOver k X] in
lemma mem_placeOf {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) (z : X.functionField) :
    z ∈ (placeOf D X eL hk U hkW hWU).1 ↔ ((eL z : D.L) : Ω) ∈ W := Iff.rfl

include hτ hσU hconj in
/-- **`σ` fixes the places of `K(X)` over the cusps.** -/
lemma fixes_placeOf (hUfin : (U : Set X)ᶜ.Finite)
    (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X))
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) :
    Fixes (σX D X eL hk σ hσL hσk) (placeOf D X eL hk U hkW hWU) := by
  obtain ⟨n, -, hn⟩ := exists_ker_comap_eq_of_chartHom_conj D X eL hH hk hτ U σ hσL hσk hσU
    hconj hUfin hhyp hkW hWU
  refine fixes_iff.2 fun z ↦ ?_
  rw [mem_placeOf, mem_placeOf, coe_eL_σX]
  have := hn (eL z)
  rwa [apply_eq_of_mem_H hH n.2 (eL z).2] at this

end Main

/-! ### Assembly -/

section Assembly

variable (U : X.Opens) [Nonempty U] (σ : Ω ≃+* Ω) (hσL : ∀ x, x ∈ D.L ↔ σ x ∈ D.L)
  (hσk : ∀ c : k, σ (algebraMap k Ω c) = algebraMap k Ω c)
  (hσU : ∀ b : Γ(X, U), ∃ a : Γ(X, U),
    σ ((eL (X.germToFunctionField U a) : D.L) : Ω) = ((eL (X.germToFunctionField U b) : D.L) : Ω))
  (hconj : ∀ n : D.H, D.chartHom hH (genericL D X eL U) (conjH hH σ hσL n) =
    D.chartHom hH (genericL D X eL U) n)

include hH hk hτ in
/-- `π₁ᵉᵗ(U)` is centre-free (`U` hyperbolic with a cusp). -/
lemma eq_one_of_forall_commute (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X))
    {c : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)} (hc : ∀ γ, c * γ = γ * c) : c = 1 := by
  obtain ⟨Θ, -⟩ :=
    exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed D eL hH hk hτ U hUfin hUne
  have hr : 0 < Nat.card ((U : Set X)ᶜ : Set X) := by
    haveI := hUfin.to_subtype
    exact Nat.card_pos_iff.2 ⟨hUne.to_subtype, inferInstance⟩
  have hcen : Θ c ∈ Subgroup.center _ := Subgroup.mem_center_iff.2 fun δ ↦ by
    obtain ⟨γ, rfl⟩ := Θ.surjective δ
    rw [← map_mul, ← map_mul, hc]
  rw [Pi1.SurfaceGroup.center_eq_bot hr hhyp, Subgroup.mem_bot] at hcen
  exact Θ.injective (hcen.trans (map_one Θ).symm)

omit [_root_.IsGalois (↥(K₀ k t)) Ω] [IsSepClosed Ω] [IsAlgClosed k] [CharZero k] in
include hσL in
lemma pow_hσL (j : ℕ) : ∀ x, x ∈ D.L ↔ (σ ^ j) x ∈ D.L := by
  induction j with
  | zero => exact fun x ↦ Iff.rfl
  | succ j ih =>
    intro x
    rw [pow_succ, RingAut.mul_apply, hσL, ih]

omit [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsAlgClosed k] [CharZero k] in
include hconj in
lemma chartHom_conjH_pow (j : ℕ) (n : D.H) :
    D.chartHom hH (genericL D X eL U) (conjH hH (σ ^ j) (pow_hσL D σ hσL j) n) =
      D.chartHom hH (genericL D X eL U) n := by
  induction j generalizing n with
  | zero =>
    exact congrArg _ (Subtype.ext (AlgEquiv.ext fun x ↦ by simp [conjH_apply]; rfl))
  | succ j ih =>
    have e : conjH hH (σ ^ (j + 1)) (pow_hσL D σ hσL (j + 1)) n =
        conjH hH σ hσL (conjH hH (σ ^ j) (pow_hσL D σ hσL j) n) := by
      ext x
      simp only [conjH_apply]
      apply (σ ^ (j + 1)).injective
      rw [RingEquiv.apply_symm_apply, pow_succ, RingAut.mul_apply, RingAut.mul_apply,
        RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [e, hconj, ih]

include hk hτ hσk hσU hconj in
/-- **Inner rigidity in the Galois model**: `σ` is the identity on `L`. -/
theorem eq_of_chartHom_conj (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X)) :
    ∀ x ∈ D.L, σ x = x := by
  classical
  set χ := D.chartHom hH (genericL D X eL U) with hχ
  -- it suffices to show `σX = 1`
  suffices key : σX D X eL hk σ hσL hσk = 1 by
    intro x hx
    obtain ⟨z, hz⟩ := eL.surjective ⟨x, hx⟩
    have := coe_eL_σX D X eL hk σ hσL hσk z
    rw [key, AlgEquiv.one_apply, hz] at this
    exact this.symm
  have hfix := fun {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) ↦
    fixes_placeOf D X eL hH hk hτ U σ hσL hσk hσU hconj hUfin hhyp hkW hWU
  have hX := valuationRing_stalk_of_isCurveOver k X
  haveI := isSeparated_of_over k X
  -- a place over a cusp
  have hcusp : ∀ x : X, x ∉ U → ∃ W : ValuationSubring Ω, comapK D X eL hk W = stalkVS k x ∧
      (∀ c : k, algebraMap k Ω c ∈ W) ∧ ¬ IsCentredOn D X eL U W := fun x hxU ↦ by
    obtain ⟨W, hW, hWtop, hWU⟩ :=
      exists_isCentredOn_not_isCentredOn D X eL hk (V := ⊤) hUfin (Set.mem_univ x) hxU
    exact ⟨W, hW, hWtop.1, hWU⟩
  by_cases hg0 : (curveGenus k X).toNat = 0
  · -- genus `0`: three fixed places
    have hg : genus k X.functionField = 0 := by
      have h0 : 0 ≤ curveGenus k X := genus_nonneg_of_isAlgClosed
      have := Int.toNat_eq_zero.1 hg0
      exact le_antisymm this h0
    have h3 : 2 < ((U : Set X)ᶜ).ncard := by
      rw [← Nat.card_coe_set_eq]
      omega
    obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := (Set.two_lt_ncard_iff hUfin).1 h3
    obtain ⟨W₁, hW₁, hk₁, hU₁⟩ := hcusp x₁ h₁
    obtain ⟨W₂, hW₂, hk₂, hU₂⟩ := hcusp x₂ h₂
    obtain ⟨W₃, hW₃, hk₃, hU₃⟩ := hcusp x₃ h₃
    have hinj : ∀ {x y : X} {Wx Wy : ValuationSubring Ω},
        comapK D X eL hk Wx = stalkVS k x → comapK D X eL hk Wy = stalkVS k y →
        comapK D X eL hk Wx = comapK D X eL hk Wy → x = y := fun hx hy hxy ↦
      (pointEquivValuationSubringOver k hX).injective (Subtype.ext (hx.symm.trans
        (hxy.trans hy)))
    refine eq_one_of_genus_eq_zero hg (P := placeOf D X eL hk U hk₁ hU₁)
      (Q₁ := placeOf D X eL hk U hk₂ hU₂) (Q₂ := placeOf D X eL hk U hk₃ hU₃)
      (fun h ↦ h₁₂ (hinj hW₁ hW₂ (congrArg Subtype.val h).symm))
      (fun h ↦ h₁₃ (hinj hW₁ hW₃ (congrArg Subtype.val h).symm))
      (fun h ↦ h₂₃ (hinj hW₂ hW₃ (congrArg Subtype.val h)))
      (hfix hk₁ hU₁) (hfix hk₂ hU₂) (hfix hk₃ hU₃)
  -- genus `≥ 1`
  have hg : 1 ≤ genus k X.functionField := by
    change 1 ≤ curveGenus k X
    omega
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨W, -, hkW, hWU⟩ := hcusp x₀ hx₀
  obtain ⟨m, hm, hσm⟩ := exists_pow_eq_one_of_fixes hg (hfix hkW hWU)
  -- `σ ^ m` is the identity on `L`
  have hσmL : ∀ x ∈ D.L, (σ ^ m) x = x := by
    intro x hx
    obtain ⟨z, hz⟩ := eL.surjective ⟨x, hx⟩
    have key : ∀ j, ((eL ((σX D X eL hk σ hσL hσk ^ j) z) : D.L) : Ω) = (σ ^ j) (eL z) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [pow_succ', AlgEquiv.mul_apply, coe_eL_σX, ih, pow_succ', RingAut.mul_apply]
    have := key m
    rw [hσm, AlgEquiv.one_apply, hz] at this
    exact this.symm
  -- `σ ^ m ∈ H` acts trivially on `π₁ᵉᵗ(U)`
  let sm : D.H := ⟨{ σ ^ m with
      commutes' := fun c ↦ hσmL _ (D.L.algebraMap_mem c) },
    D.le (by
      rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
      exact hσmL)⟩
  have hsm : χ sm = 1 := by
    refine eq_one_of_forall_commute D X eL hH hk hτ U hUfin ⟨x₀, hx₀⟩ hhyp fun γ ↦ ?_
    obtain ⟨n, rfl⟩ := (genericL_spec D X eL hk hH hτ U hUfin).2 γ
    have e : sm⁻¹ * n * sm = conjH hH (σ ^ m) (pow_hσL D σ hσL m) n := by
      ext x
      rfl
    have := chartHom_conjH_pow D X eL hH U σ hσL hconj m n
    rw [← e, map_mul, map_mul, map_inv, mul_assoc] at this
    exact (inv_mul_eq_iff_eq_mul.1 this).symm
  -- a finite quotient in which the inertia of `W` has order divisible by `m`
  obtain ⟨V, hVn, hVo, y, hy, hyV⟩ := exists_open_normal_cuspInertia_pow D eL hH hk hτ U hUfin
    ⟨x₀, hx₀⟩ (Or.inr (by omega)) hkW hWU hm
  rw [cuspInertia_eq_galInertia, galInertia_eq_map] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨ι₀, rfl⟩ := D.toGalL_surjective g
  let ι : D.H := ⟨ι₀, D.le ι₀.2⟩
  have hιχ : χ ι = galoisAction D.L (genericL D X eL U) rfl (D.toGalL ι₀) := rfl
  have hιW : (ι : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W := hg
  -- the field `E = Ω ^ {χ⁻¹ V}`
  let HV : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := (V.comap χ).map D.H.subtype
  have mem_HV : ∀ n : D.H, (n : Ω ≃ₐ[K₀ k t] Ω) ∈ HV ↔ χ n ∈ V := fun n ↦ by
    constructor
    · rintro ⟨n', hn', hnn'⟩
      rwa [← Subtype.ext hnn']
    · exact fun h ↦ ⟨n, h, rfl⟩
  have HV_le : HV ≤ D.H := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hHVo : IsOpen (HV : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
    have : (HV : Set (Ω ≃ₐ[K₀ k t] Ω)) = Subtype.val '' (χ ⁻¹' (V : Set _)) := by
      ext x
      simp [HV]
    rw [this]
    exact D.isOpen_H.isOpenMap_subtype_val _ (hVo.preimage (D.continuous_chartHom hH _))
  let DE : GaloisData k t :=
    { H := HV
      HL := HV
      le := le_rfl
      isOpen_HL := hHVo
      conj_mem := fun h hh n hn ↦ HV.mul_mem (HV.mul_mem hh hn) (HV.inv_mem hh)
      transcendental := D.transcendental }
  haveI : IsFunctionField k (F DE) := isFunctionField_F DE
  have mem_E : ∀ x, x ∈ F DE ↔ ∀ h ∈ HV, h x = x := fun x ↦
    IntermediateField.mem_fixedField_iff _ _
  have hHVc : IsClosed (HV : Set (Ω ≃ₐ[K₀ k t] Ω)) := Subgroup.isClosed_of_isOpen _ hHVo
  have fix_E : ∀ n : D.H, (∀ x ∈ F DE, (n : Ω ≃ₐ[K₀ k t] Ω) x = x) ↔ χ n ∈ V := fun n ↦ by
    rw [← mem_HV]
    have := InfiniteGalois.fixingSubgroup_fixedField (k := K₀ k t) (K := Ω) ⟨HV, hHVc⟩
    rw [← IntermediateField.mem_fixingSubgroup_iff]
    change _ ∈ (IntermediateField.fixedField HV).fixingSubgroup ↔ _
    rw [this]
  have ker_E : ∀ n : D.H, χ n = 1 → ∀ x ∈ F DE, (n : Ω ≃ₐ[K₀ k t] Ω) x = x := fun n hn ↦
    (fix_E n).2 (hn ▸ V.one_mem)
  have hL_E : ∀ x ∈ D.L, x ∈ F DE := fun x hx ↦ (mem_E x).2 fun h hh ↦
    apply_eq_of_mem_H hH (HV_le hh) hx
  -- `σ` and the elements of `H` preserve `E`
  have hσE : ∀ x, x ∈ F DE ↔ σ x ∈ F DE := by
    intro x
    constructor
    · intro hx
      refine (mem_E _).2 fun h hh ↦ ?_
      replace hx := (mem_E _).1 hx
      obtain ⟨n, hnV, rfl⟩ := hh
      have := hx _ ((mem_HV (conjH hH σ hσL n)).2 (by rw [hconj]; exact hnV))
      rw [conjH_apply] at this
      exact σ.symm.injective (by simpa using this)
    · intro hx
      refine (mem_E _).2 fun h hh ↦ ?_
      replace hx := (mem_E _).1 hx
      obtain ⟨n, hnV, rfl⟩ := hh
      have := hx _ ((mem_HV (conjH hH σ.symm (symm_hσL hσL) n)).2
        (by rw [chartHom_conjH_symm D X eL hH U σ hσL hconj]; exact hnV))
      rw [conjH_apply, RingEquiv.symm_symm, RingEquiv.symm_apply_apply] at this
      exact σ.injective this
  have hHE : ∀ ρ : D.H, ∀ x, x ∈ F DE ↔ (ρ : Ω ≃ₐ[K₀ k t] Ω) x ∈ F DE := by
    intro ρ x
    constructor
    · intro hx
      refine (mem_E _).2 fun h hh ↦ ?_
      replace hx := (mem_E _).1 hx
      obtain ⟨n, hnV, rfl⟩ := hh
      have hc : χ (ρ⁻¹ * n * ρ) ∈ V := by
        have := hVn.conj_mem _ hnV (χ ρ)⁻¹
        simpa [map_mul, map_inv] using this
      have := hx _ ((mem_HV _).2 hc)
      change ((ρ⁻¹ : D.H) : Ω ≃ₐ[K₀ k t] Ω) ((n : Ω ≃ₐ[K₀ k t] Ω)
        ((ρ : Ω ≃ₐ[K₀ k t] Ω) x)) = x at this
      have h' := congrArg (ρ : Ω ≃ₐ[K₀ k t] Ω) this
      simp only [Subgroup.coe_inv, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h'
      exact h'
    · intro hx
      refine (mem_E _).2 fun h hh ↦ ?_
      replace hx := (mem_E _).1 hx
      obtain ⟨n, hnV, rfl⟩ := hh
      have hc : χ (ρ * n * ρ⁻¹) ∈ V := by
        have := hVn.conj_mem _ hnV (χ ρ)
        simpa [map_mul, map_inv] using this
      have := hx _ ((mem_HV _).2 hc)
      change (ρ : Ω ≃ₐ[K₀ k t] Ω) ((n : Ω ≃ₐ[K₀ k t] Ω) (((ρ⁻¹ : D.H) : Ω ≃ₐ[K₀ k t] Ω)
        ((ρ : Ω ≃ₐ[K₀ k t] Ω) x))) = (ρ : Ω ≃ₐ[K₀ k t] Ω) x at this
      rw [show ((ρ⁻¹ : D.H) : Ω ≃ₐ[K₀ k t] Ω) ((ρ : Ω ≃ₐ[K₀ k t] Ω) x) = x by
        simp] at this
      exact (ρ : Ω ≃ₐ[K₀ k t] Ω).injective this
  have hHk : ∀ ρ : D.H, ∀ c : k, (ρ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (algebraMap k Ω c) =
      algebraMap k Ω c := fun ρ c ↦ by
    rw [IsScalarTower.algebraMap_apply k (K₀ k t) Ω]
    exact (ρ : Ω ≃ₐ[K₀ k t] Ω).commutes _
  let σE := restrictAlg (F DE) σ hσE hσk
  set ιE := restrictAlg (F DE) (ι : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv (hHE ι) (hHk ι) with hιE
  -- the place of `E` below `W`
  obtain ⟨a₀, ha₀⟩ : ∃ a : Γ(X, U), ((eL (X.germToFunctionField U a) : D.L) : Ω) ∉ W := by
    by_contra h
    push Not at h
    exact hWU ⟨hkW, h⟩
  let PE : Place k (F DE) :=
    ⟨W.comap (algebraMap (F DE) Ω), fun h ↦ ha₀ (by
        have : (⟨_, hL_E _ (eL (X.germToFunctionField U a₀)).2⟩ : F DE) ∈
          W.comap (algebraMap (F DE) Ω) := h ▸ ValuationSubring.mem_top _
        exact this),
      fun c ↦ by
        change algebraMap k Ω c ∈ W
        exact hkW c⟩
  have mem_PE : ∀ x : F DE, x ∈ PE.1 ↔ (x : Ω) ∈ W := fun x ↦ Iff.rfl
  obtain ⟨n₀, hn₀, hn₀W⟩ := exists_ker_comap_eq_of_chartHom_conj D X eL hH hk hτ U σ hσL hσk
    hσU hconj hUfin hhyp hkW hWU
  have hσfix : Fixes σE PE := fixes_iff.2 fun x ↦ by
    rw [mem_PE, mem_PE, coe_restrictAlg]
    have := hn₀W x
    rwa [ker_E n₀ hn₀ x x.2] at this
  have hιfix : Fixes ιE PE := fixes_iff.2 fun x ↦ by
    rw [mem_PE, mem_PE, coe_restrictAlg]
    exact apply_mem_iff_of_mem_inertia hιW x
  have hcomm : Commute ιE σE := by
    ext x
    change (ι : Ω ≃ₐ[K₀ k t] Ω) (σ x) = σ ((ι : Ω ≃ₐ[K₀ k t] Ω) x)
    have h1 : χ (ι⁻¹ * conjH hH σ hσL ι) = 1 := by
      rw [map_mul, hconj, map_inv, inv_mul_cancel]
    have := ker_E _ h1 x x.2
    change ((ι⁻¹ : D.H) : Ω ≃ₐ[K₀ k t] Ω) (σ.symm ((ι : Ω ≃ₐ[K₀ k t] Ω) (σ x))) = x at this
    have h2 : σ.symm ((ι : Ω ≃ₐ[K₀ k t] Ω) (σ x)) = (ι : Ω ≃ₐ[K₀ k t] Ω) x := by
      have h3 := congrArg (ι : Ω ≃ₐ[K₀ k t] Ω) this
      simp only [Subgroup.coe_inv, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h3
      exact h3
    rw [← h2, RingEquiv.apply_symm_apply]
  have hσEm : σE ^ m = 1 := by
    ext x
    rw [restrictAlg_pow, AlgEquiv.one_apply]
    exact ker_E sm hsm x x.2
  -- the order of `ι` on `E`
  have hpowι : ∀ (j : ℕ) (x : Ω), ((ι : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv ^ j) x =
      ((ι ^ j : D.H) : Ω ≃ₐ[K₀ k t] Ω) x := by
    intro j
    induction j with
    | zero => exact fun _ ↦ rfl
    | succ j ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, ih, pow_succ, Subgroup.coe_mul, AlgEquiv.mul_apply]
      rfl
  have hιpow : ∀ j : ℕ, ιE ^ j = 1 ↔ χ ι ^ j ∈ V := by
    intro j
    rw [← map_pow, ← fix_E]
    constructor
    · intro h x hx
      have := congrArg (fun f : F DE ≃ₐ[k] F DE ↦ (f ⟨x, hx⟩ : Ω)) h
      simp only [hιE, restrictAlg_pow, AlgEquiv.one_apply] at this
      rwa [hpowι] at this
    · intro h
      ext x
      rw [hιE, restrictAlg_pow, AlgEquiv.one_apply, hpowι]
      exact h x x.2
  haveI : CompactSpace π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) := inferInstance
  haveI := Subgroup.quotient_finite_of_isOpen V hVo
  have hfin : IsOfFinOrder ιE := by
    have hq := isOfFinOrder_of_finite (QuotientGroup.mk (χ ι) : _ ⧸ V)
    refine ⟨orderOf (QuotientGroup.mk (χ ι) : _ ⧸ V), hq.orderOf_pos, ?_⟩
    rw [isPeriodicPt_mul_iff_pow_eq_one, hιpow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow,
      pow_orderOf_eq_one]
  have he : 0 < orderOf ιE := hfin.orderOf_pos
  have hme : m ∣ orderOf ιE := hyV _ ((hιpow _).1 (pow_orderOf_eq_one ιE))
  obtain ⟨a, ha⟩ := exists_eq_pow_of_commute hιfix hσfix hcomm he rfl hm hσEm hme
  -- conclusion: `σ` fixes `L`
  ext z
  apply eL.injective
  apply Subtype.ext
  rw [coe_eL_σX, AlgEquiv.one_apply]
  have hz : ((eL z : D.L) : Ω) ∈ F DE := hL_E _ (eL z).2
  have := congrArg (fun f : F DE ≃ₐ[k] F DE ↦ (f ⟨_, hz⟩ : Ω)) ha
  simp only [σE, coe_restrictAlg] at this
  rw [this]
  have hfixι : ιE ⟨_, hz⟩ = ⟨_, hz⟩ := Subtype.ext (apply_eq_of_mem_H hH ι.2 (eL z).2)
  clear this ha
  induction a with
  | zero => rfl
  | succ a ih => rw [pow_succ, AlgEquiv.mul_apply, hfixι, ih]

end Assembly

end CurvesJacobian.LocAn
