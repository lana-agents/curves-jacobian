/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.ZerosPoles

/-!
# A nonconstant function takes every constant value

[AbsTopIII] Prop. 1.8, proof (T3 l.2099–2106): "since `k_NF` is algebraically closed, any
nonconstant rational function on `X_NF` determines a morphism `X_NF → ℙ¹_{k_NF}` such that the
induced map `X_NF(k_NF) → ℙ¹_{k_NF}(k_NF)` is surjective". In terms of places of a function field
`K / κ` (weil-curves):

* `CurvesJacobian.Kummer.exists_ord_sub_pos`: for `f ∈ K` transcendental over `κ` and `c ∈ κ`
  there is a place `P` with `ord_P(f - c) > 0`, i.e. `f(P) = c` (the value `∞` is
  `Place.exists_ord_neg`). For `κ` algebraically closed every place is a `κ`-rational point, so
  this is the surjectivity of `f : X(κ) → ℙ¹(κ)` on `κ`-points.
-/

open WeilCurves.FunctionField

namespace CurvesJacobian.Kummer

variable {κ K : Type*} [Field κ] [Field K] [Algebra κ K] [PerfectField κ] [IsFunctionField κ K]

omit [PerfectField κ] [IsFunctionField κ K] in
/-- `f - c` is transcendental if `f` is. -/
lemma transcendental_sub_algebraMap {f : K} (hf : Transcendental κ f) (c : κ) :
    Transcendental κ (f - algebraMap κ K c) := by
  intro h
  apply hf
  have := h.add (isAlgebraic_algebraMap (R := κ) c)
  rwa [sub_add_cancel] at this

/-- **A nonconstant function takes every value `c ∈ κ`**: some place `P` has `ord_P(f - c) > 0`. -/
theorem exists_ord_sub_pos {f : K} (hf : Transcendental κ f) (c : κ) :
    ∃ P : Place κ K, 0 < P.ord (f - algebraMap κ K c) :=
  Place.exists_ord_pos (transcendental_sub_algebraMap hf c)

/-- The value: `f ∈ O_P` and `f - c ∈ 𝔪_P`, i.e. `f(P) = c`. -/
theorem exists_mem_and_sub_mem {f : K} (hf : Transcendental κ f) (c : κ) :
    ∃ P : Place κ K, f ∈ P.1 ∧ (f - algebraMap κ K c) ∈ P.1 ∧
      (f - algebraMap κ K c)⁻¹ ∉ P.1 := by
  obtain ⟨P, hP⟩ := exists_ord_sub_pos hf c
  have hmem : f - algebraMap κ K c ∈ P.1 := P.mem_of_ord_nonneg hP.le
  refine ⟨P, ?_, hmem, fun h => ?_⟩
  · have := add_mem hmem (P.algebraMap_mem c)
    rwa [sub_add_cancel] at this
  · have := P.ord_nonneg_of_mem h
    rw [P.ord_inv] at this
    omega

end CurvesJacobian.Kummer
