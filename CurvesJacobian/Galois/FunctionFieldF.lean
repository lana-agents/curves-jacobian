/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.TameChar
import WeilCurves.FunctionField.Place
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# The function field of the Galois model is a function field of one variable

In the Galois-theoretic setting of `pi1` / continuous-kummer-theory (`D : GaloisData k t`,
`Ω ⊇ K₀ = k(t)`, `F = F D = Ω^H` finite over `k(t)`):

* `CurvesJacobian.isFunctionField_F`: `F` is a function field of one variable over `k` in the
  sense of weil-curves (finite over `k⟮t⟯`, `t` transcendental);
* `CurvesJacobian.exists_valuationSubring_liesOver`: every place `P` of `F/k` is the restriction
  of a valuation subring `W` of `Ω` (`x ∈ P ↔ x ∈ W` for `x ∈ F`), by Chevalley's extension
  theorem (Mathlib's `LocalSubring.exists_le_valuationSubring`).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

namespace CurvesJacobian

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t)

/-- `t` as an element of `F`. -/
def tF : F D := algebraMap (K₀ k t) (F D) ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩

lemma coe_tF : ((tF D : F D) : Ω) = t := rfl

instance isScalarTower_k_F_Ω : IsScalarTower k (F D) Ω :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma transcendental_tF : Transcendental k (tF D) := by
  have h : Transcendental k ((tF D : F D) : Ω) := by rw [coe_tF]; exact D.transcendental
  exact (transcendental_algebraMap_iff (algebraMap (F D) Ω).injective).1 h

variable [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]

omit [CharZero k] [IsSepClosed Ω] in
/-- **`F` is a function field of one variable over `k`.** -/
theorem isFunctionField_F : IsFunctionField k (F D) := by
  refine ⟨⟨tF D, transcendental_tF D, ?_⟩⟩
  -- `k(t) → k⟮tF⟯ ⊆ F`
  set E : IntermediateField k (F D) := IntermediateField.adjoin k {tF D}
  have hmem : ∀ x : K₀ k t, algebraMap (K₀ k t) (F D) x ∈ E := by
    intro x
    have hx : (x : Ω) ∈ (K₀ k t) := x.2
    have hle : (K₀ k t) ≤ (E.map (IntermediateField.val (F D) |>.restrictScalars k)) := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact ⟨tF D, IntermediateField.mem_adjoin_simple_self k _, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle hx
    have : y = algebraMap (K₀ k t) (F D) x := Subtype.ext hyx
    exact this ▸ hy
  letI : Algebra (K₀ k t) E :=
    ((algebraMap (K₀ k t) (F D)).codRestrict E.toSubalgebra hmem).toAlgebra
  haveI : IsScalarTower (K₀ k t) E (F D) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional (K₀ k t) (F D) := inferInstance
  exact Module.Finite.of_restrictScalars_finite (K₀ k t) E (F D)

attribute [local instance] isFunctionField_F

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] in
/-- Every place of `F/k` extends to a valuation subring of `Ω`. -/
theorem exists_valuationSubring_liesOver (P : Place k (F D)) :
    ∃ W : ValuationSubring Ω, ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1 := by
  let f : P.1 →+* Ω := (algebraMap (F D) Ω).comp P.1.subtype
  obtain ⟨W, hW⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  obtain ⟨hle, hloc⟩ := hW
  refine ⟨W, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ hle ⟨⟨x, hx⟩, rfl⟩⟩⟩
  by_contra hxP
  have hx0 : x ≠ 0 := by rintro rfl; exact hxP P.1.zero_mem
  have hinv : x⁻¹ ∈ P.1 := (P.1.mem_or_inv_mem x).resolve_left hxP
  -- `x⁻¹` is a unit of `W`, hence of the image of `P`
  let a : (LocalSubring.range f).toSubring := ⟨f ⟨x⁻¹, hinv⟩, ⟨⟨x⁻¹, hinv⟩, rfl⟩⟩
  have hunit : IsUnit (Subring.inclusion hle a) := by
    refine IsUnit.of_mul_eq_one ⟨(x : Ω), hx⟩ (Subtype.ext ?_)
    change ((x⁻¹ : F D) : Ω) * (x : Ω) = 1
    rw [← IntermediateField.coe_mul, inv_mul_cancel₀ hx0, IntermediateField.coe_one]
  obtain ⟨b, hb⟩ := (isUnit_of_map_unit _ a hunit).exists_right_inv
  obtain ⟨⟨c, hc⟩, hcb⟩ := b.2
  apply hxP
  have hval : ((x⁻¹ : F D) : Ω) * (c : Ω) = 1 := by
    have := congrArg Subtype.val hb
    simp only [Subring.coe_mul, Subring.coe_one] at this
    rw [← this]
    congr 1
  have hcx : c = x := by
    apply (algebraMap (F D) Ω).injective
    change (c : Ω) = (x : Ω)
    have hx' : ((x⁻¹ : F D) : Ω) * (x : Ω) = 1 := by
      rw [← IntermediateField.coe_mul, inv_mul_cancel₀ hx0, IntermediateField.coe_one]
    have hne : ((x⁻¹ : F D) : Ω) ≠ 0 := by
      intro h; rw [h, zero_mul] at hx'; exact zero_ne_one hx'
    exact mul_left_cancel₀ hne (hval.trans hx'.symm)
  rw [← hcx]
  exact hc

end CurvesJacobian
