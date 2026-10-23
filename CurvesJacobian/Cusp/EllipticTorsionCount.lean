/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticChainEN
import EllipticCurves.Torsion.TwoTorsionOrder
import EllipticCurves.Torsion.XSupport

/-!
# `K`-rationality of `E[N]` from the torsion count `#E(K)[N] = N²`

`CurvesJacobian.Cusp.TorsionRationalN E N` (`EllipticChainEN.lean`) expresses "`E[N]` is
`K`-rational" in coordinates: `ΨSq_N` splits over `K`, and over each of its roots there is a
`K`-point of `E`. Here we derive it from the group-theoretic form `#E(K)[N] = N²`
(`E(K)[N]` = `E.toAffine.torsion N` of the elliptic-curves package):

* **`CurvesJacobian.Cusp.torsionRationalN_of_card_torsion`**: if `char K = 0`, `N ≥ 1` and
  `Nat.card E(K)[N] = N²`, then `TorsionRationalN E N`.

Proof: over an algebraic closure `L` of `K`, `#E(L)[N] ≤ N²` (`card_torsion_le_sq_of_charZero`),
and the coordinate-wise map `E(K)[N] → E(L)[N]` is injective (`n • (x, y) = 0 ⇔ ψ_N(x, y) = 0`,
`nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic`, and `ψ_N` commutes with base change),
hence bijective. A root `e` of `ΨSq_N` in `L` is the `x`-coordinate of a point `(e, y)` of `E(L)`
(solve the quadratic in `y`), which is `N`-torsion because `ψ_N(e, y)² = ΨSq_N(e) = 0`
(`ψ_sq_evalEval`); so it comes from `E(K)[N]` and `e ∈ K`.
-/

open Polynomial WeierstrassCurve

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section TorsionCount

variable {F L : Type*} [Field F] [Field L] (W : WeierstrassCurve F) (f : F →+* L)

/-- The coordinate-wise map `W(F) → W(L)` of points (no group structure needed). -/
def ptMapTC : W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).2 h)

lemma ptMapTC_injective : Function.Injective (ptMapTC W f) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hP
  · rfl
  · exact absurd hP (by simp [ptMapTC])
  · exact absurd hP (by simp [ptMapTC])
  · simp only [ptMapTC, Affine.Point.some.injEq] at hP
    obtain ⟨hx, hy⟩ := hP
    obtain rfl := f.injective hx
    obtain rfl := f.injective hy
    rfl

lemma map_ψ_evalEvalTC (n : ℤ) (x y : F) :
    ((W.map f).ψ n).evalEval (f x) (f y) = f ((W.ψ n).evalEval x y) := by
  rw [map_ψ, map_mapRingHom_evalEval]

variable [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L] [W.IsElliptic]

lemma nsmul_some_eq_zero_iffTC {x y : F} (h : W.toAffine.Nonsingular x y) (N : ℕ) :
    (N • (Affine.Point.some x y h : W.toAffine.Point) = 0) ↔ (W.ψ N).evalEval x y = 0 :=
  Affine.nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic two_ne_zero h N

lemma ptMapTC_mem_torsion {N : ℕ} {P : W.toAffine.Point} (hP : P ∈ W.toAffine.torsion N) :
    ptMapTC W f P ∈ (W.map f).toAffine.torsion N := by
  rw [Affine.mem_torsion_iff] at hP ⊢
  rcases P with _ | ⟨x, y, h⟩
  · exact smul_zero _
  · rw [nsmul_some_eq_zero_iffTC] at hP
    change N • (Affine.Point.some (f x) (f y) _ : (W.map f).toAffine.Point) = 0
    rw [nsmul_some_eq_zero_iffTC, map_ψ_evalEvalTC, hP, map_zero]

end TorsionCount

variable {K : Type u} [Field K] [CharZero K] [DecidableEq K] (E : WeierstrassCurve K)
  [E.IsElliptic]

/-- Over an algebraically closed field of characteristic `0`, every root `e` of `ΨSq_N` is the
`x`-coordinate of a nonsingular point `(e, y)` with `ψ_N(e, y) = 0`. -/
lemma exists_point_of_ΨSq_rootTC {L : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    (W : WeierstrassCurve L) [W.IsElliptic] {N : ℕ} {e : L} (he : (W.ΨSq N).eval e = 0) :
    ∃ (y : L) (_ : W.toAffine.Nonsingular e y), (W.ψ N).evalEval e y = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    ((W.a₁ * e + W.a₃) ^ 2 + 4 * (e ^ 3 + W.a₂ * e ^ 2 + W.a₄ * e + W.a₆)) two_pos
  have hy : W.toAffine.Equation e ((-(W.a₁ * e + W.a₃) + s) / 2) := by
    rw [Affine.equation_iff']
    linear_combination (1 / 4 : L) * hs
  have hns := (Affine.equation_iff_nonsingular (W := W.toAffine)).1 hy
  refine ⟨_, hns, ?_⟩
  have h2 := Affine.ψ_sq_evalEval hy (N : ℤ)
  rw [he] at h2
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h2

/-- **`E[N]` is `K`-rational in the coordinate form if `#E(K)[N] = N²`** (`char K = 0`). -/
theorem torsionRationalN_of_card_torsion {N : ℕ} (hN : 1 ≤ N)
    (hcard : Nat.card (E.toAffine.torsion N) = N ^ 2) : TorsionRationalN E N := by
  classical
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let EL := E.map ι
  -- the map `E(K)[N] → E(L)[N]` is a bijection
  let g : E.toAffine.torsion N → EL.toAffine.torsion N :=
    fun P ↦ ⟨ptMapTC E ι P, ptMapTC_mem_torsion E ι P.2⟩
  have hg : Function.Injective g := fun P Q hPQ ↦
    Subtype.ext (ptMapTC_injective E ι (congrArg Subtype.val hPQ))
  haveI : Finite (EL.toAffine.torsion N) := Affine.finite_torsion_of_charZero hN
  have hle : Nat.card (EL.toAffine.torsion N) ≤ Nat.card (E.toAffine.torsion N) := by
    rw [hcard]
    exact Affine.card_torsion_le_sq_of_charZero hN
  have hbij : Function.Bijective g := hg.bijective_of_nat_card_le hle
  -- every root of `ΨSq_N` over `L` is the `x`-coordinate of the image of a `K`-point
  have hroot : ∀ e' : AlgebraicClosure K, ((E.ΨSq N).map ι).eval e' = 0 →
      ∃ (x y : K) (_ : E.toAffine.Nonsingular x y), ι x = e' := by
    intro e' he'
    rw [← map_ΨSq] at he'
    obtain ⟨y', hns', hψ⟩ := exists_point_of_ΨSq_rootTC EL he'
    have hmem : (Affine.Point.some e' y' hns' : EL.toAffine.Point) ∈ EL.toAffine.torsion N := by
      rw [Affine.mem_torsion_iff, nsmul_some_eq_zero_iffTC]
      exact hψ
    obtain ⟨⟨P, hP⟩, hgP⟩ := hbij.2 ⟨_, hmem⟩
    have hgP' : ptMapTC E ι P = Affine.Point.some e' y' hns' := congrArg Subtype.val hgP
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd hgP' (by simp [ptMapTC])
    · simp only [ptMapTC, Affine.Point.some.injEq] at hgP'
      exact ⟨x, y, h, hgP'.1⟩
  have hne : E.ΨSq N ≠ 0 := E.ΨSq_ne_zero (by
    rw [Int.cast_natCast]
    exact Nat.cast_ne_zero.2 (by omega))
  refine ⟨Splits.of_splits_map_of_injective ι.injective (IsAlgClosed.splits _) fun a ha ↦ ?_,
    fun e he ↦ ?_⟩
  · have ha' := (mem_roots'.1 ha).2
    obtain ⟨x, -, -, hx⟩ := hroot a ha'
    exact ⟨x, hx⟩
  · have he' : ((E.ΨSq N).map ι).eval (ι e) = 0 := by
      rw [eval_map, eval₂_at_apply, he, map_zero]
    obtain ⟨x, y, h, hx⟩ := hroot (ι e) he'
    obtain rfl := ι.injective hx
    exact ⟨y, h.1⟩

end CurvesJacobian.Cusp
