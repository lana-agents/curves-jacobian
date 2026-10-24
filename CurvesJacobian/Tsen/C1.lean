/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Tsen.Homogeneous
import WeilCurves.FunctionField.Riemann
import Mathlib.RingTheory.Norm.Basic

/-!
# Tsen's theorem: function fields of curves over algebraically closed fields are `C₁`

Let `k` be algebraically closed and `K / k` a function field in one variable. Tsen's theorem
(SGA 4½, Arcata III, Théorème (2.3); the property `C₁` is Définition (2.1)) says that every
homogeneous polynomial of degree `d > 0` in `N > d` variables over `K` has a nontrivial zero.
As in the proof of Arcata III (2.2), applied to the norm form of a finite extension `L' / K`
(a homogeneous polynomial of degree `[L' : K]` in `[L' : K]` variables whose only zero is `0`),
this gives that the norm `L' → K` is surjective.

## Proof

We follow Tsen's method of undetermined coefficients, with Riemann–Roch spaces in place of
spaces of polynomials of bounded degree. Fix a divisor `D` of positive degree and a divisor
`E ≥ 0` with all coefficients of `φ` in `L(E)`. For `s` large, write the unknowns as
`xᵢ = ∑ⱼ tᵢⱼ bⱼ` with `(bⱼ)` a `k`-basis of `L(sD)`. Then `φ(x)` lies in `W = L(E + d s D)` and,
in a `k`-basis of `W`, its coordinates are polynomials over `k` in the `tᵢⱼ` without constant
term. The Riemann inequality and `ℓ(A) ≤ deg A + ℓ(0)` give `dim W < N · dim L(sD)` for `s`
large because `d < N`, so these polynomials have a nontrivial common zero over `k`
(`CurvesJacobian.Tsen.exists_ne_zero_common_zero_of_card_lt`).

The polynomial bookkeeping is done with `MvPolynomial (Fin N × Fin m) K`: the polynomial
`Ψ = φ(∑ⱼ bⱼ X_{ij})` has all its coefficients in `W` (`CoeffsIn`).

## Main results

* `CurvesJacobian.Tsen.exists_ne_zero_eval_eq_zero` : Tsen's theorem (`K` is `C₁`).
* `CurvesJacobian.Tsen.exists_norm_eq` : norms from finite extensions of `K` are surjective.

## References

* [SGA 4½, *Arcata*, III, Définition (2.1), Proposition (2.2), Théorème (2.3)]
  (local text `jac-dd/sga45/n32.txt`, l. 1027, 1033, 1050)
-/

namespace CurvesJacobian.Tsen

open IntermediateField MvPolynomial WeilCurves.FunctionField WeilCurves.FunctionField.Divisor

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section CoeffsIn

variable [PerfectField k] [IsFunctionField k K] {τ : Type*}

/-- `L(A) · L(B) ⊆ L(A + B)`. -/
theorem mul_mem_L_add {A B : Divisor k K} {f g : K} (hf : f ∈ L A) (hg : g ∈ L B) :
    f * g ∈ L (A + B) := by
  by_cases hfg : f * g = 0
  · rw [hfg]; exact zero_mem _
  have hf0 : f ≠ 0 := left_ne_zero_of_mul hfg
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hfg
  rw [mem_L, or_iff_right hf0] at hf
  rw [mem_L, or_iff_right hg0] at hg
  refine Or.inr fun P => ?_
  rw [P.ord_mul hf0 hg0]
  have h1 := hf P
  have h2 := hg P
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega

theorem one_mem_L_zero : (1 : K) ∈ L (0 : Divisor k K) := mem_L_zero.mpr isAlgebraic_one

/-- All coefficients of the polynomial `Ψ` over `K` lie in the Riemann–Roch space `L(A)`. -/
def CoeffsIn (A : Divisor k K) (Ψ : MvPolynomial τ K) : Prop :=
  ∀ ν, coeff ν Ψ ∈ L A

theorem coeffsIn_C {A : Divisor k K} {c : K} (hc : c ∈ L A) :
    CoeffsIn A (C c : MvPolynomial τ K) := by
  classical
  intro ν
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact zero_mem _

theorem coeffsIn_one : CoeffsIn (0 : Divisor k K) (1 : MvPolynomial τ K) := by
  have h := coeffsIn_C (τ := τ) (one_mem_L_zero (k := k) (K := K))
  rwa [map_one] at h

theorem coeffsIn_X (s : τ) : CoeffsIn (0 : Divisor k K) (X s : MvPolynomial τ K) := by
  classical
  intro ν
  rw [coeff_X]
  split_ifs
  · exact one_mem_L_zero
  · exact zero_mem _

theorem coeffsIn_sum {ι : Type*} (s : Finset ι) {A : Divisor k K} {Ψ : ι → MvPolynomial τ K}
    (h : ∀ i ∈ s, CoeffsIn A (Ψ i)) : CoeffsIn A (∑ i ∈ s, Ψ i) := fun ν => by
  rw [coeff_sum]
  exact Submodule.sum_mem _ fun i hi => h i hi ν

theorem CoeffsIn.mul {A B : Divisor k K} {Ψ Θ : MvPolynomial τ K} (h₁ : CoeffsIn A Ψ)
    (h₂ : CoeffsIn B Θ) : CoeffsIn (A + B) (Ψ * Θ) := by
  classical
  intro ν
  rw [coeff_mul]
  exact Submodule.sum_mem _ fun x _ => mul_mem_L_add (h₁ x.1) (h₂ x.2)

theorem CoeffsIn.pow {A : Divisor k K} {Ψ : MvPolynomial τ K} (h : CoeffsIn A Ψ) (n : ℕ) :
    CoeffsIn (n • A) (Ψ ^ n) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact coeffsIn_one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul h

theorem coeffsIn_prod {ι : Type*} (s : Finset ι) {A : ι → Divisor k K}
    {Ψ : ι → MvPolynomial τ K} (h : ∀ i ∈ s, CoeffsIn (A i) (Ψ i)) :
    CoeffsIn (∑ i ∈ s, A i) (∏ i ∈ s, Ψ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact coeffsIn_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Substituting polynomials with coefficients in `L(G)` into a form of degree `d` with
coefficients in `L(E)` gives a polynomial with coefficients in `L(E + d G)`. -/
theorem coeffsIn_bind₁ {σ : Type*} {E G : Divisor k K} {d : ℕ} (φ : MvPolynomial σ K)
    (hφ : φ.IsHomogeneous d) (hE : ∀ μ, coeff μ φ ∈ L E) (y : σ → MvPolynomial τ K)
    (hy : ∀ i, CoeffsIn G (y i)) : CoeffsIn (E + d • G) (bind₁ y φ) := by
  rw [as_sum φ, map_sum]
  refine coeffsIn_sum _ fun μ hμ => ?_
  rw [bind₁_monomial]
  have hsum : ∑ i ∈ μ.support, μ i • G = d • G := by
    rw [← Finset.sum_smul, ← hφ.degree_eq_sum_deg_support hμ]
  rw [← hsum]
  exact (coeffsIn_C (hE μ)).mul (coeffsIn_prod _ fun i _ => (hy i).pow (μ i))

end CoeffsIn

section Tsen

variable (k) [IsAlgClosed k] [IsFunctionField k K]

include k

/-- **Tsen's theorem** (SGA 4½, Arcata III, (2.3)): the function field `K` of a curve over an
algebraically closed field `k` is `C₁`: a form of degree `d > 0` in `N > d` variables over `K`
has a nontrivial zero. -/
theorem exists_ne_zero_eval_eq_zero {N d : ℕ} (φ : MvPolynomial (Fin N) K)
    (hφ : φ.IsHomogeneous d) (hd : 0 < d) (hN : d < N) :
    ∃ x : Fin N → K, x ≠ 0 ∧ MvPolynomial.eval x φ = 0 := by
  classical
  -- a divisor of positive degree
  obtain ⟨t, ht⟩ := exists_transcendental k K
  set D : Divisor k K := polarDivisor k t with hD
  have hδ : 1 ≤ D.deg := by
    rw [hD, deg_polarDivisor ht]
    haveI := finiteDimensional_adjoin ht
    have := Module.finrank_pos (R := k⟮t⟯) (M := K)
    omega
  -- a divisor `E ≥ 0` with all coefficients of `φ` in `L(E)`
  set E : Divisor k K := ∑ μ ∈ φ.support, polarDivisor k (coeff μ φ) with hEdef
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun μ _ => polarDivisor_nonneg _
  have hE : ∀ μ, coeff μ φ ∈ L E := by
    intro μ
    by_cases hμ : μ ∈ φ.support
    · refine L_mono (Finset.single_le_sum (f := fun μ => polarDivisor k (coeff μ φ))
        (fun μ _ => polarDivisor_nonneg _) hμ) ?_
      refine Or.inr fun P => ?_
      have := neg_polarDivisor_le_div (k := k) (coeff μ φ) P
      simpa only [Finsupp.coe_neg, Pi.neg_apply, div_apply] using this
    · rw [notMem_support_iff.mp hμ]; exact zero_mem _
  -- the dimension count
  set c := riemannConst k K with hc
  set z : ℤ := (ell (0 : Divisor k K) : ℤ) with hz
  set s : ℕ := (N * c + E.deg + z).toNat + 1 with hs
  set G : Divisor k K := s • D with hG
  set W : Divisor k K := E + d • G with hW
  set m := Module.finrank k (L G) with hmdef
  set r := Module.finrank k (L W) with hrdef
  have hm : G.deg - c ≤ (m : ℤ) := riemann_inequality G
  have hr : (r : ℤ) ≤ max 0 (W.deg + z) := ell_le_max W
  have hGdeg : G.deg = s * D.deg := deg_nsmul s D
  have hWdeg : W.deg = E.deg + d * (s * D.deg) := by rw [hW, deg_add, deg_nsmul, hGdeg]
  have hEdeg : 0 ≤ E.deg := deg_nonneg hE0
  have hz0 : 0 ≤ z := Int.natCast_nonneg _
  have hcount : r < N * m := by
    have hs' : N * c + E.deg + z < (s : ℤ) := by
      have := Int.self_le_toNat (N * c + E.deg + z)
      rw [hs]; push_cast; linarith
    have h1 : (N : ℤ) * (G.deg - c) ≤ N * m := mul_le_mul_of_nonneg_left hm (by positivity)
    have hsδ : 0 ≤ (s : ℤ) * D.deg := mul_nonneg (by positivity) (by omega)
    have h2 : 0 ≤ ((N : ℤ) - d - 1) * (s * D.deg) := mul_nonneg (by omega) hsδ
    have h3 : 0 ≤ (s : ℤ) * (D.deg - 1) := mul_nonneg (by positivity) (by omega)
    have h4 : 0 ≤ (d : ℤ) * (s * D.deg) := mul_nonneg (by positivity) hsδ
    have hmax : max 0 (W.deg + z) = W.deg + z := max_eq_right (by rw [hWdeg]; linarith)
    rw [hmax, hWdeg] at hr
    rw [hGdeg] at h1
    have : (r : ℤ) < N * m := by nlinarith
    exact_mod_cast this
  -- bases
  let b := Module.finBasis k (L G)
  let bW := Module.finBasis k (L W)
  -- the generic substitution
  let y : Fin N → MvPolynomial (Fin N × Fin m) K := fun i =>
    ∑ j : Fin m, C ((b j : L G) : K) * X (i, j)
  have hy : ∀ i, CoeffsIn G (y i) := fun i => coeffsIn_sum _ fun j _ => by
    have := (coeffsIn_C (τ := Fin N × Fin m) (b j).2).mul (coeffsIn_X (k := k) (i, j))
    rwa [add_zero] at this
  set Ψ : MvPolynomial (Fin N × Fin m) K := bind₁ y φ with hΨdef
  have hΨ : CoeffsIn W Ψ := coeffsIn_bind₁ φ hφ hE y hy
  let xt : (Fin N × Fin m → k) → Fin N → K := fun t i =>
    ((∑ j : Fin m, t (i, j) • b j : L G) : K)
  have heval : ∀ t : Fin N × Fin m → k,
      eval (fun p => algebraMap k K (t p)) Ψ = eval (xt t) φ := by
    intro t
    have h : eval (fun p => algebraMap k K (t p)) (bind₁ y φ) =
        eval (fun i => eval (fun p => algebraMap k K (t p)) (y i)) φ :=
      eval₂Hom_bind₁ (RingHom.id K) _ y φ
    rw [hΨdef, h]
    refine congrArg (fun g => eval g φ) (funext fun i => ?_)
    simp only [y, xt, map_sum, map_mul, eval_C, eval_X, Submodule.coe_sum, Submodule.coe_smul,
      Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- the element `φ(x(t))` of `L(W)` and its coordinates
  let wν : (Fin N × Fin m →₀ ℕ) → L W := fun ν => ⟨coeff ν Ψ, hΨ ν⟩
  let w : (Fin N × Fin m → k) → L W := fun t =>
    ∑ ν ∈ Ψ.support, (ν.prod fun n e => t n ^ e) • wν ν
  have hw : ∀ t, ((w t : L W) : K) = eval (xt t) φ := by
    intro t
    rw [← heval]
    conv_rhs => rw [as_sum Ψ]
    simp only [w, wν, map_sum, eval_monomial, Submodule.coe_sum, Submodule.coe_smul,
      Algebra.smul_def]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [mul_comm, map_finsuppProd]
    simp only [map_pow]
  let f : Fin r → MvPolynomial (Fin N × Fin m) k := fun l =>
    ∑ ν ∈ Ψ.support, monomial ν (bW.coord l (wν ν))
  have hf : ∀ l t, eval t (f l) = bW.coord l (w t) := by
    intro l t
    simp only [f, w, map_sum, eval_monomial, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun ν _ => mul_comm _ _
  have hw0 : w 0 = 0 := by
    have h0 : xt 0 = 0 := by
      funext i
      simp [xt]
    apply Subtype.ext
    rw [hw, h0, eval_zero]
    exact constantCoeff_eq_zero_of_isHomogeneous hd hφ
  have hf0 : ∀ l, constantCoeff (f l) = 0 := by
    intro l
    rw [← eval_zero, hf, hw0, map_zero]
  obtain ⟨t, ht0, htz⟩ := exists_ne_zero_common_zero_of_card_lt (k := k) f hf0
    (by simpa [Fintype.card_prod, Fintype.card_fin] using hcount)
  refine ⟨xt t, ?_, ?_⟩
  · intro hx
    obtain ⟨⟨i, j⟩, hij⟩ := Function.ne_iff.mp ht0
    have hxi : (∑ j : Fin m, t (i, j) • b j : L G) = 0 := by
      apply Subtype.ext
      exact congrFun hx i
    exact hij (Fintype.linearIndependent_iff.mp b.linearIndependent _ hxi j)
  · rw [← hw]
    have : w t = 0 := bW.forall_coord_eq_zero_iff.mp fun l => by rw [← hf]; exact htz l
    rw [this, ZeroMemClass.coe_zero]

end Tsen

/-- **Norms are surjective** (Tsen's theorem applied to the norm form, as in SGA 4½,
Arcata III, (2.2)): for a finite extension `L'` of the function field `K` of a curve over an
algebraically closed field `k`, the norm `L' → K` is surjective. -/
theorem exists_norm_eq (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed k]
    [IsFunctionField k K] (L' : Type*) [Field L'] [Algebra K L'] [FiniteDimensional K L']
    (f : K) : ∃ y : L', Algebra.norm K y = f := by
  classical
  set n := Module.finrank K L' with hn
  have hn0 : 0 < n := Module.finrank_pos
  let e : Module.Basis (Fin n) K L' := Module.finBasis K L'
  let M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n + 1)) K) :=
    Matrix.of fun a b => ∑ i : Fin n, C (Algebra.leftMulMatrix e (e i) a b) * X i.succ
  have hM : ∀ a b, (M a b).IsHomogeneous 1 := fun a b => by
    simp only [M, Matrix.of_apply]
    exact IsHomogeneous.sum _ _ _ fun i _ => by
      have := (isHomogeneous_C (Fin (n + 1)) (Algebra.leftMulMatrix e (e i) a b)).mul
        (isHomogeneous_X K i.succ)
      rwa [zero_add] at this
  have hdet : M.det.IsHomogeneous n := by
    rw [Matrix.det_apply']
    refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have h1 : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin (n + 1)) K).IsHomogeneous 0 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin (n + 1)) K)]
      exact isHomogeneous_C _ _
    have h2 : (∏ i, M (σ i) i).IsHomogeneous n := by
      have := IsHomogeneous.prod (Finset.univ : Finset (Fin n)) (fun i => M (σ i) i)
        (fun _ => 1) (fun i _ => hM _ _)
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    have := h1.mul h2
    rwa [zero_add] at this
  set Φ : MvPolynomial (Fin (n + 1)) K := M.det - C f * X 0 ^ n with hΦdef
  have hΦ : Φ.IsHomogeneous n := by
    refine hdet.sub ?_
    have := (isHomogeneous_C (Fin (n + 1)) f).mul ((isHomogeneous_X K 0).pow n)
    rwa [zero_add, one_mul] at this
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_eval_eq_zero k Φ hΦ hn0 (Nat.lt_succ_self n)
  have hnorm : ∀ w : Fin (n + 1) → K,
      eval w M.det = Algebra.norm K (∑ i : Fin n, w i.succ • e i) := by
    intro w
    rw [Algebra.norm_eq_matrix_det e, RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sum, map_mul,
      eval_C, eval_X, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hv' : Algebra.norm K (∑ i : Fin n, v i.succ • e i) = f * v 0 ^ n := by
    rw [← hnorm]
    simpa [hΦdef, sub_eq_zero] using hv
  have hv00 : v 0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn0.ne', mul_zero, Algebra.norm_eq_zero_iff] at hv'
    have hi := Fintype.linearIndependent_iff.mp e.linearIndependent _ hv'
    apply hv0
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact h0
    · exact hi i
  refine ⟨(v 0)⁻¹ • ∑ i : Fin n, v i.succ • e i, ?_⟩
  rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, ← hn, hv', inv_pow, mul_left_comm,
    inv_mul_cancel₀ (pow_ne_zero n hv00), mul_one]

end CurvesJacobian.Tsen
