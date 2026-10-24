/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticTorsionCount
import CurvesJacobian.Cusp.MulNSubgroup
import EllipticCurves.Torsion.StructureGeneral

/-!
# `K`-rational `N`-torsion has `N²` points

`CurvesJacobian.Cusp.TorsionRationalN E N` (`EllipticChainEN.lean`) says that `E[N]` is
`K`-rational in coordinates (`ΨSq_N` splits over `K` and over each root there is a `K`-point of
`E`); `CurvesJacobian.Cusp.TorsionCardN E N` (`MulNSubgroup.lean`) is the group-theoretic form
`#E(K)[N] = N²` used by `cor34_mulN`. `EllipticTorsionCount.lean` proves `TorsionCardN → …`;
here is the converse, so the two notions agree in characteristic `0` (this is the rationality
condition "`E[N]` is `K`-rational" of [IUTchI, Definition 3.1 (b)] in either form):

* **`CurvesJacobian.Cusp.torsionCardN_of_torsionRationalN`**: `char K = 0`, `N ≥ 1`,
  `TorsionRationalN E N` ⇒ `TorsionCardN E N`.
* **`CurvesJacobian.Cusp.torsionCardN_iff_torsionRationalN`**: the equivalence.

Proof: over an algebraic closure `L`, `#E(L)[N] = N²` (`card_torsion_eq_sq`, elliptic-curves
package) and the coordinate-wise map `E(K)[N] → E(L)[N]` is injective. It is surjective: for
`(e', y') ∈ E(L)[N]`, `ΨSq_N(e') = ψ_N(e', y')² = 0`, so `e' = e ∈ K` because `ΨSq_N` splits over
`K`; by hypothesis some `y ∈ K` has `(e, y) ∈ E`, and `y' ∈ {y, -y - a₁e - a₃}` lies in `K`.
-/

open Polynomial WeierstrassCurve

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- **`K`-rational `N`-torsion in coordinates gives `#E(K)[N] = N²`** (`char K = 0`). -/
theorem torsionCardN_of_torsionRationalN {N : ℕ} (hN : 1 ≤ N) (hEN : TorsionRationalN E N) :
    TorsionCardN E N := by
  classical
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let EL := E.map ι
  let g : E.toAffine.torsion N → EL.toAffine.torsion N :=
    fun P ↦ ⟨ptMapTC E ι P, ptMapTC_mem_torsion E ι P.2⟩
  have hg : Function.Injective g := fun P Q hPQ ↦
    Subtype.ext (ptMapTC_injective E ι (congrArg Subtype.val hPQ))
  have hne : E.ΨSq N ≠ 0 := E.ΨSq_ne_zero (by
    rw [Int.cast_natCast]
    exact Nat.cast_ne_zero.2 (by omega))
  have hsurj : Function.Surjective g := by
    rintro ⟨_ | ⟨e', y', hns'⟩, hmem⟩
    · exact ⟨0, rfl⟩
    have hψ : (EL.ψ N).evalEval e' y' = 0 := by
      rw [Affine.mem_torsion_iff, nsmul_some_eq_zero_iffTC] at hmem
      exact hmem
    have hroot : ((E.ΨSq N).map ι).IsRoot e' := by
      have h2 := Affine.ψ_sq_evalEval hns'.1 (N : ℤ)
      rw [hψ, zero_pow two_ne_zero] at h2
      change ((E.ΨSq N).map ι).eval e' = 0
      rw [← map_ΨSq]
      exact h2.symm
    obtain ⟨e, rfl⟩ := hEN.1.mem_range_of_isRoot hne hroot
    have he : (E.ΨSq N).eval e = 0 := by
      have h := hroot.eq_zero
      rw [eval_map, eval₂_at_apply] at h
      exact ι.injective (h.trans (map_zero ι).symm)
    obtain ⟨y, hy⟩ := hEN.2 e he
    have hyL : EL.toAffine.Equation (ι e) (ι y) := (E.toAffine.map_equation ι.injective e y).2 hy
    -- `y'` is `y` or `-y - a₁ e - a₃`, both in `K`
    obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ : K, E.toAffine.Equation e y₀ ∧ ι y₀ = y' := by
      rcases Affine.Y_eq_of_X_eq hns'.1 hyL rfl with h | h
      · exact ⟨y, hy, h.symm⟩
      · refine ⟨E.toAffine.negY e y, (E.toAffine.equation_neg e y).2 hy, ?_⟩
        rw [h]
        exact (E.toAffine.map_negY ι e y).symm
    have hns₀ : E.toAffine.Nonsingular e y₀ :=
      (Affine.equation_iff_nonsingular (W := E.toAffine)).1 hy₀
    have hmem₀ : (Affine.Point.some e y₀ hns₀ : E.toAffine.Point) ∈ E.toAffine.torsion N := by
      rw [Affine.mem_torsion_iff, nsmul_some_eq_zero_iffTC]
      apply ι.injective
      rw [map_zero, ← map_ψ_evalEvalTC]
      exact hψ
    exact ⟨⟨_, hmem₀⟩, rfl⟩
  have hcardL : Nat.card (EL.toAffine.torsion N) = N ^ 2 :=
    Affine.card_torsion_eq_sq two_ne_zero (Nat.cast_ne_zero.2 (by omega))
  unfold TorsionCardN
  rw [← hcardL]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hg, hsurj⟩)

/-- **The two forms of "`E[N]` is `K`-rational" agree** (`char K = 0`, `N ≥ 1`). -/
theorem torsionCardN_iff_torsionRationalN {N : ℕ} (hN : 1 ≤ N) :
    TorsionCardN E N ↔ TorsionRationalN E N := by
  classical
  refine ⟨fun h ↦ torsionRationalN_of_card_torsion E hN ?_,
    torsionCardN_of_torsionRationalN E hN⟩
  unfold TorsionCardN at h
  convert h

end CurvesJacobian.Cusp
