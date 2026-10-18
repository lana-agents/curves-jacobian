/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Riemann
import WeilCurves.Hurwitz.Belyi

/-!
# Uniformisers of a rational function field that are polynomials

Let `K = k(s)` be a rational function field over a perfect field `k` (a function field with
`k⟮s⟯ = ⊤`, `s` transcendental) and `P` a place of `K` with `s ∈ 𝒪_P`. Then `p(s)` is a
uniformiser at `P` for `p` the minimal polynomial over `k` of the residue of `s`
(`CurvesJacobian.Cusp.ord_aeval_minpoly_residue_eq_one`).

Proof: `y = p(s)` has a zero at `P` (`ord_aeval_minpoly_residue_pos`), and
`ord_P(y) deg P ≤ Σ_{P' zero of y} ord_{P'}(y) deg P' = [K : k(y)] ≤ deg p ≤ [κ(P) : k] = deg P`,
since `s` is a root of `p(X) - y ∈ k(y)[X]` and `p` is the minimal polynomial of an element of
`κ(P)`.
-/

open WeilCurves.FunctionField Polynomial Module
open scoped IntermediateField

namespace CurvesJacobian.Cusp

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

omit [PerfectField k] [IsFunctionField k K] in
/-- `[K : k(y)] ≤ deg p` for `y = p(s)`, `K = k(s)`. -/
lemma finrank_adjoin_aeval_le {s : K} (h1 : k⟮s⟯ = ⊤) (p : k[X]) (hp : p.Monic)
    (hdeg : p.natDegree ≠ 0) :
    finrank k⟮aeval s p⟯ K ≤ p.natDegree := by
  set F' := k⟮aeval s p⟯
  set y : F' := IntermediateField.AdjoinSimple.gen k (aeval s p)
  set q : F'[X] := p.map (algebraMap k F') - C y
  have hqm : q.Monic := (hp.map _).sub_of_left (degree_C_le.trans_lt (by
    rw [degree_map, degree_eq_natDegree hp.ne_zero]; exact_mod_cast Nat.pos_of_ne_zero hdeg))
  have hqs : aeval s q = 0 := by
    simp only [q, map_sub, aeval_map_algebraMap, aeval_C]
    rw [sub_eq_zero]
    rfl
  have hint : IsIntegral F' s := ⟨q, hqm, hqs⟩
  have hdq : q.natDegree = p.natDegree := by
    simp only [q]
    rw [natDegree_sub_C, natDegree_map]
  have htop : F'⟮s⟯ = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ k⟮s⟯ := h1 ▸ IntermediateField.mem_top
    have hle : k⟮s⟯ ≤ (F'⟮s⟯).restrictScalars k := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self F' s
    exact hle hz
  have h2 : finrank F' K = finrank F' F'⟮s⟯ := by
    rw [htop, IntermediateField.finrank_top']
  rw [h2, IntermediateField.adjoin.finrank hint, ← hdq]
  exact natDegree_le_of_dvd (minpoly.dvd F' s hqs) hqm.ne_zero

/-- **`p(s)` is a uniformiser at `P`** for `K = k(s)`, `s ∈ 𝒪_P` and `p` the minimal polynomial of
the residue of `s`. -/
theorem ord_aeval_minpoly_residue_eq_one {s : K} (hs : Transcendental k s) (h1 : k⟮s⟯ = ⊤)
    (P : Place k K) (hsP : s ∈ P.1) :
    P.ord (aeval s (minpoly k (P.residue ⟨s, hsP⟩))) = 1 := by
  classical
  set r := P.residue ⟨s, hsP⟩
  have hint : IsIntegral k r := Algebra.IsIntegral.isIntegral r
  set p := minpoly k r
  have hpos := Divisor.ord_aeval_minpoly_residue_pos hs P hsP
  have hdeg0 : p.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  set y := aeval s p
  have hyt : Transcendental k y :=
    hs.aeval p hdeg0 (by rw [(minpoly.monic hint).leadingCoeff]; exact one_mem _)
  have hsum := Place.sum_ord_mul_deg_zeros y hyt
  set T := (Place.finite_setOf_ord_pos (k := k) y).toFinset
  have hPT : P ∈ T := by simpa [T] using hpos
  have hle : P.ord y * (P.deg : ℤ) ≤ finrank k⟮y⟯ K := by
    rw [← hsum]
    refine Finset.single_le_sum (f := fun P : Place k K ↦ P.ord y * (P.deg : ℤ))
      (fun Q hQ ↦ ?_) hPT
    have : 0 < Q.ord y := by simpa [T] using hQ
    positivity
  have hfin : finrank k⟮y⟯ K ≤ p.natDegree :=
    finrank_adjoin_aeval_le h1 p (minpoly.monic hint) hdeg0
  have hdP : p.natDegree ≤ P.deg := minpoly.natDegree_le r
  have hd : (0 : ℤ) < P.deg := by exact_mod_cast P.deg_pos
  have : P.ord y * (P.deg : ℤ) ≤ P.deg := by
    have h3 : ((finrank k⟮y⟯ K : ℕ) : ℤ) ≤ P.deg := by exact_mod_cast hfin.trans hdP
    linarith
  nlinarith

end CurvesJacobian.Cusp
