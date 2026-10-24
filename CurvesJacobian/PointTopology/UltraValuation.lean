/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# The valuation ring of finite elements of an ultrapower

Let `L` be a normed field and `𝒰` an ultrafilter on a type `I`. The ultrapower
`Filter.Germ (𝒰 : Filter I) L` is a field. We define the subring `finiteGerms 𝒰 L` of germs of
functions that are bounded along `𝒰`, show that it is a valuation ring with fraction field the
ultrapower, and, for proper `L`, construct the standard part map `stdPart 𝒰 L`, a ring
homomorphism `finiteGerms 𝒰 L →+* L` sending the germ of a bounded function to its limit
along `𝒰`.

## Main definitions

* `CurvesJacobian.PointTopology.finiteGerms`: the subring of bounded germs.
* `CurvesJacobian.PointTopology.stdPart`: the standard part map.

## Main results

* `CurvesJacobian.PointTopology.mem_finiteGerms_iff`
* instances `ValuationRing (finiteGerms 𝒰 L)` and
  `IsFractionRing (finiteGerms 𝒰 L) (Filter.Germ (𝒰 : Filter I) L)`
* `CurvesJacobian.PointTopology.tendsto_stdPart`,
  `CurvesJacobian.PointTopology.exists_mem_finiteGerms_of_tendsto`,
  `CurvesJacobian.PointTopology.stdPart_const`
-/

namespace CurvesJacobian.PointTopology

open Filter Topology

universe u

variable {I : Type u} (𝒰 : Ultrafilter I) (L : Type u) [NormedField L]

/-- The subring of the ultrapower `Filter.Germ 𝒰 L` consisting of the germs of functions that
are bounded along `𝒰`. -/
def finiteGerms : Subring (Germ (𝒰 : Filter I) L) where
  carrier := {ξ | ∃ C : ℝ, ξ.LiftPred fun x : L => ‖x‖ ≤ C}
  zero_mem' := ⟨0, Germ.liftPred_coe.2 (Eventually.of_forall fun _ => by simp)⟩
  one_mem' := ⟨1, Germ.liftPred_coe.2 (Eventually.of_forall fun _ => by simp)⟩
  add_mem' {a b} ha hb := by
    induction a using Germ.inductionOn
    induction b using Germ.inductionOn
    obtain ⟨C, hC⟩ := ha
    obtain ⟨D, hD⟩ := hb
    refine ⟨C + D, ?_⟩
    rw [← Germ.coe_add, Germ.liftPred_coe] at *
    filter_upwards [hC, hD] with i hi hj
    exact (norm_add_le _ _).trans (add_le_add hi hj)
  mul_mem' {a b} ha hb := by
    induction a using Germ.inductionOn
    induction b using Germ.inductionOn
    obtain ⟨C, hC⟩ := ha
    obtain ⟨D, hD⟩ := hb
    refine ⟨C * D, ?_⟩
    rw [← Germ.coe_mul, Germ.liftPred_coe] at *
    filter_upwards [hC, hD] with i hi hj
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul hi hj (norm_nonneg _) ((norm_nonneg _).trans hi)
  neg_mem' {a} ha := by
    induction a using Germ.inductionOn
    obtain ⟨C, hC⟩ := ha
    refine ⟨C, ?_⟩
    rw [← Germ.coe_neg, Germ.liftPred_coe] at *
    simpa using hC

/-- The germ of `f` is finite iff `f` is bounded along `𝒰`. -/
theorem mem_finiteGerms_iff (f : I → L) :
    (f : Germ (𝒰 : Filter I) L) ∈ finiteGerms 𝒰 L ↔ ∃ C : ℝ, ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ C :=
  exists_congr fun _ => Germ.liftPred_coe

/-- Every germ or its inverse is bounded. -/
theorem mem_or_inv_mem_finiteGerms (ξ : Germ (𝒰 : Filter I) L) :
    ξ ∈ finiteGerms 𝒰 L ∨ ξ⁻¹ ∈ finiteGerms 𝒰 L := by
  induction ξ using Germ.inductionOn with | h f => ?_
  by_cases h : ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ 1
  · exact Or.inl ((mem_finiteGerms_iff 𝒰 L f).2 ⟨1, h⟩)
  · right
    rw [← Ultrafilter.eventually_not] at h
    rw [← Germ.coe_inv, mem_finiteGerms_iff]
    refine ⟨1, h.mono fun i hi => ?_⟩
    rw [Pi.inv_apply, norm_inv]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hi))

instance : IsDomain (finiteGerms 𝒰 L) := inferInstance

instance : ValuationRing (finiteGerms 𝒰 L) where
  cond' a b := by
    by_cases h : (b : Germ (𝒰 : Filter I) L) = 0
    · refine ⟨0, Or.inl ?_⟩
      ext
      simp [h]
    by_cases h : (a : Germ (𝒰 : Filter I) L) = 0
    · refine ⟨0, Or.inr ?_⟩
      ext
      simp [h]
    rcases mem_or_inv_mem_finiteGerms 𝒰 L (a / b) with hh | hh
    · refine ⟨⟨a / b, hh⟩, Or.inr ?_⟩
      ext
      simp [field]
    · rw [show ((a : Germ (𝒰 : Filter I) L) / b)⁻¹ = b / a by simp] at hh
      refine ⟨⟨b / a, hh⟩, Or.inl ?_⟩
      ext
      simp [field]

instance : IsFractionRing (finiteGerms 𝒰 L) (Germ (𝒰 : Filter I) L) where
  map_units := fun ⟨y, hy⟩ =>
    (Units.mk0 (y : Germ (𝒰 : Filter I) L)
      fun c => nonZeroDivisors.ne_zero hy <| Subtype.ext c).isUnit
  surj z := by
    by_cases h : z = 0
    · exact ⟨(0, 1), by simp [h]⟩
    rcases mem_or_inv_mem_finiteGerms 𝒰 L z with hh | hh
    · exact ⟨(⟨z, hh⟩, 1), by simp; rfl⟩
    · refine ⟨⟨1, ⟨⟨_, hh⟩, ?_⟩⟩, mul_inv_cancel₀ h⟩
      exact mem_nonZeroDivisors_iff_ne_zero.2
        fun c => h (inv_eq_zero.mp (congr_arg Subtype.val c))
  exists_of_eq {a b} h := ⟨1, by simpa using Subtype.ext h⟩

/-- Constant germs are finite. -/
theorem const_mem_finiteGerms (c : L) :
    ((c : Germ (𝒰 : Filter I) L)) ∈ finiteGerms 𝒰 L :=
  (mem_finiteGerms_iff 𝒰 L fun _ => c).2 ⟨‖c‖, Eventually.of_forall fun _ => le_rfl⟩

/-- The limit along `𝒰` of a representative of a germ (junk value if no limit exists). -/
noncomputable def germLim (ξ : Germ (𝒰 : Filter I) L) : L :=
  ξ.liftOn (fun f => limUnder (𝒰 : Filter I) f) fun f g h => by
    change lim (map f (𝒰 : Filter I)) = lim (map g (𝒰 : Filter I))
    rw [map_congr h]

theorem germLim_eq_of_tendsto {f : I → L} {a : L} (h : Tendsto f (𝒰 : Filter I) (𝓝 a)) :
    germLim 𝒰 L f = a :=
  h.limUnder_eq

section StdPart

variable [ProperSpace L]

theorem exists_tendsto_of_bounded (f : I → L) (hf : ∃ C : ℝ, ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ C) :
    ∃ a, Tendsto f (𝒰 : Filter I) (𝓝 a) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : L) C).ultrafilter_le_nhds (𝒰.map f) (by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact hC.mono fun i hi => by simpa using hi)
  exact ⟨a, by rwa [Ultrafilter.coe_map] at ha⟩

theorem tendsto_germLim (f : I → L) (hf : ∃ C : ℝ, ∀ᶠ i in (𝒰 : Filter I), ‖f i‖ ≤ C) :
    Tendsto f (𝒰 : Filter I) (𝓝 (germLim 𝒰 L f)) :=
  tendsto_nhds_limUnder (exists_tendsto_of_bounded 𝒰 L f hf)

/-- The standard part map: the ring homomorphism `finiteGerms 𝒰 L →+* L` sending the germ of a
bounded function to its limit along `𝒰`. -/
noncomputable def stdPart : finiteGerms 𝒰 L →+* L where
  toFun ξ := germLim 𝒰 L ξ
  map_one' := germLim_eq_of_tendsto 𝒰 L (f := fun _ => (1 : L)) tendsto_const_nhds
  map_zero' := germLim_eq_of_tendsto 𝒰 L (f := fun _ => (0 : L)) tendsto_const_nhds
  map_mul' := by
    rintro ⟨ξ, hξ⟩ ⟨η, hη⟩
    induction ξ using Germ.inductionOn with | h f => ?_
    induction η using Germ.inductionOn with | h g => ?_
    rw [mem_finiteGerms_iff] at hξ hη
    exact germLim_eq_of_tendsto 𝒰 L (f := f * g)
      ((tendsto_germLim 𝒰 L f hξ).mul (tendsto_germLim 𝒰 L g hη))
  map_add' := by
    rintro ⟨ξ, hξ⟩ ⟨η, hη⟩
    induction ξ using Germ.inductionOn with | h f => ?_
    induction η using Germ.inductionOn with | h g => ?_
    rw [mem_finiteGerms_iff] at hξ hη
    exact germLim_eq_of_tendsto 𝒰 L (f := f + g)
      ((tendsto_germLim 𝒰 L f hξ).add (tendsto_germLim 𝒰 L g hη))

theorem stdPart_mk (f : I → L) (hf : (f : Germ (𝒰 : Filter I) L) ∈ finiteGerms 𝒰 L) :
    stdPart 𝒰 L ⟨f, hf⟩ = germLim 𝒰 L f :=
  rfl

/-- The germ of a bounded function tends to its standard part along `𝒰`. -/
theorem tendsto_stdPart (f : I → L) (hf : (f : Germ (𝒰 : Filter I) L) ∈ finiteGerms 𝒰 L) :
    Tendsto f (𝒰 : Filter I) (𝓝 (stdPart 𝒰 L ⟨f, hf⟩)) :=
  tendsto_germLim 𝒰 L f ((mem_finiteGerms_iff 𝒰 L f).1 hf)

/-- A function converging along `𝒰` has bounded germ, with standard part its limit. -/
theorem exists_mem_finiteGerms_of_tendsto (f : I → L) (a : L)
    (h : Tendsto f (𝒰 : Filter I) (𝓝 a)) :
    ∃ hf : (f : Germ (𝒰 : Filter I) L) ∈ finiteGerms 𝒰 L, stdPart 𝒰 L ⟨f, hf⟩ = a := by
  refine ⟨(mem_finiteGerms_iff 𝒰 L f).2 ⟨‖a‖ + 1, ?_⟩, germLim_eq_of_tendsto 𝒰 L h⟩
  have := (continuous_norm.tendsto a).comp h
  exact this.eventually (eventually_le_nhds (lt_add_one ‖a‖))

/-- The standard part of a constant germ is the constant. -/
@[simp]
theorem stdPart_const (c : L) :
    stdPart 𝒰 L ⟨(c : Germ (𝒰 : Filter I) L), const_mem_finiteGerms 𝒰 L c⟩ = c :=
  germLim_eq_of_tendsto 𝒰 L (f := fun _ => c) tendsto_const_nhds

/-- The kernel of the standard part map consists of the germs tending to `0`. -/
theorem stdPart_eq_zero_iff (f : I → L) (hf : (f : Germ (𝒰 : Filter I) L) ∈ finiteGerms 𝒰 L) :
    stdPart 𝒰 L ⟨f, hf⟩ = 0 ↔ Tendsto f (𝒰 : Filter I) (𝓝 0) :=
  ⟨fun h => h ▸ tendsto_stdPart 𝒰 L f hf, fun h => germLim_eq_of_tendsto 𝒰 L h⟩

end StdPart

end CurvesJacobian.PointTopology
