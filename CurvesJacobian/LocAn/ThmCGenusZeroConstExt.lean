/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThmCConstExt
import CurvesJacobian.LocAn.ThmCGenusZero

/-!
# [LocAn] Theorem C in genus `0` with cusps rational over a finite extension (MR7 S3(a), step 4)

Let `K ⊆ Ω` be an algebraic (e.g. finite) extension of `k` over which the curve has genus `0` and
`U_K` has two distinct cusps of degree `1`. Restricting to the Galois model of `U_K`
(`Kummer.constExt K D`, `LocAn/ThmCConstExt.lean`), `Δ_U`-conjugate sections over `k` of rational
points `x, y` become `Δ_{U_K}`-conjugate sections over `K` of `x_K, y_K`
(`exists_conj_ratSectionGk_constExt`); the genus-`0` theorem over `K`
(`placeOfF_eq_of_ratSectionGk_conj_genus_zero`) gives `x_K = y_K`, hence `x = y`
(`placeOfF_eq_of_placeOfF_constExt_eq`).

## Main results

* `CurvesJacobian.LocAn.piToGk_constExt_eq_one`: `Δ_U ∩ Π_{U_K} ⊆ Δ_{U_K}`;
* `CurvesJacobian.LocAn.exists_conj_ratSectionGk_constExt`: conjugacy transfer to `K`;
* **`CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj_genus_zero_constExt`**: Thm C
  (profinite) in genus `0`, `K` Kummer-faithful for `𝔾_m`.
-/

/-! ### [LocAn] Theorem C in genus `0`, cusps rational over a finite extension -/

namespace CurvesJacobian.LocAn

open KummerTheory Curve AffOrbicurve IsLocalRing CurvesJacobian.Kummer WeilCurves.FunctionField

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [Algebra.IsAlgebraic k K]

attribute [local instance] isFunctionField_F

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- `K̄ ⊆ k̄` for `K/k` algebraic. -/
lemma mem_kbar_of_mem_kbarK (y : kbar K Ω) : (y : Ω) ∈ kbar k Ω := by
  exact mem_algebraicClosure_iff.2
    (isIntegral_trans (R := k) (A := K) (y : Ω)
      (mem_algebraicClosure_iff.1 y.2).isIntegral).isAlgebraic

/-- `Δ_{U_K} = Δ_U ∩ Π_{U_K}`: an element of `Π_{U_K}` trivial in `G_k` is trivial in `G_K`. -/
lemma piToGk_constExt_eq_one {δ' : Pi (constExt K D)} (h : piToGk D (piRes K D δ') = 1) :
    piToGk (constExt K D) δ' = 1 := by
  induction δ' using QuotientGroup.induction_on with
  | H σ =>
    refine AlgEquiv.ext fun y => Subtype.ext ?_
    change algebraMap (kbar K Ω) Ω (hToGk (constExt K D) σ y) = (y : Ω)
    rw [algebraMap_hToGk_apply]
    have h1 := congrArg (fun φ : Gk k Ω => ((φ ⟨y, mem_kbar_of_mem_kbarK y⟩ : kbar k Ω) : Ω)) h
    change algebraMap (kbar k Ω) Ω (hToGk D (hRes K D σ) _) = (y : Ω) at h1
    rw [algebraMap_hToGk_apply] at h1
    exact h1

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **Conjugate sections over `k` stay conjugate over `K`**: `Δ_U`-conjugate sections of
`Π_U → G_k` at rational points restrict to `Δ_{U_K}`-conjugate sections of `Π_{U_K} → G_K`. -/
theorem exists_conj_ratSectionGk_constExt (hHL : D.HL = D.H) {x y : RatPoint D} (hx : t ∈ x.A)
    (hy : t ∈ y.A) {δ : Pi D} (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹) :
    ∃ δ' ∈ (piToGk (constExt K D)).ker, ∀ g',
      ratSectionGk (y.constExt K) (constExt_HL_eq D hHL) hy g' =
        δ' * ratSectionGk (x.constExt K) (constExt_HL_eq D hHL) hx g' * δ'⁻¹ := by
  obtain ⟨δ', rfl⟩ : δ ∈ (piRes K D).range := (mem_range_piRes_iff (K := K) D δ).2 fun c => by
    rw [MonoidHom.mem_ker.1 hδ]
    rfl
  refine ⟨δ', piToGk_constExt_eq_one (MonoidHom.mem_ker.1 hδ), fun g' => ?_⟩
  obtain ⟨g, hgg⟩ := exists_resGk g'
  apply piRes_injective D
  rw [map_mul, map_mul, map_inv, piRes_ratSectionGk y hHL hy g' g hgg,
    piRes_ratSectionGk x hHL hx g' g hgg]
  exact h g

/-- `placeOfF` over `K` determines `placeOfF` over `k` (`F ⊆ F K`). -/
lemma placeOfF_eq_of_placeOfF_constExt_eq {x y : RatPoint D}
    (he : placeOfF (x.constExt K) = placeOfF (y.constExt K)) : placeOfF x = placeOfF y := by
  apply Subtype.ext
  ext u
  have := congrArg (fun p : Place K (F (constExt K D)) =>
    (⟨u, le_F_constExt D u.2⟩ : F (constExt K D)) ∈ p.1) he
  exact Iff.of_eq this

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) in genus `0`, cusps rational over a finite extension** (MR7
S3(a), step 4): if over an algebraic extension `K ⊆ Ω` of `k` the curve has genus `0`, `U_K` has
two distinct cusps `P, Q` of degree `1`, and `K` is Kummer-faithful for `𝔾_m`, then rational
points `x, y` of `U` with `Δ_U`-conjugate sections of `Π_U → G_k` are the same point. -/
theorem placeOfF_eq_of_ratSectionGk_conj_genus_zero_constExt (hkf : IsKummerFaithfulGm K)
    (hHL : D.HL = D.H) {x y : RatPoint D} (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D}
    (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹)
    (hg : genus K (F (constExt K D)) = 0) {P Q : Place K (F (constExt K D))} (hPQ : P ≠ Q)
    (hP : P.deg = 1) (hQ : Q.deg = 1) (hPc : tF (constExt K D) ∉ P.1)
    (hQc : tF (constExt K D) ∉ Q.1) :
    placeOfF x = placeOfF y := by
  obtain ⟨δ', hδ', h'⟩ := exists_conj_ratSectionGk_constExt (K := K) hHL hx hy hδ h
  exact placeOfF_eq_of_placeOfF_constExt_eq
    (placeOfF_eq_of_ratSectionGk_conj_genus_zero hkf (constExt_HL_eq D hHL) hx hy hδ' h' hg hPQ
      hP hQ hPc hQc)

end CurvesJacobian.LocAn
