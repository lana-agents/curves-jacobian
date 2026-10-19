/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.FunctionField.DivisorEval
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Weil reciprocity

Let `K / κ` be a function field of one variable over an algebraically closed field `κ`. For
nonzero `f, g ∈ K` whose divisors have disjoint supports, `f(div g) = g(div f)`
(`CurvesJacobian.weil_reciprocity`; Sutherland, *Elliptic curves* (MIT 18.783, 2019),
Lecture 24, Theorem 24.20, whose proof refers to Silverman, *The Arithmetic of Elliptic Curves*,
2nd ed., Exercise 2.11). Values `f(D)` are `CurvesJacobian.evalDiv` (Sutherland, Def. 24.18).

## Proof (the norm route of Silverman's exercise)

If `g` is constant both sides are `1`. Otherwise let `N = N_{K/κ(g)}`. For a transcendental `t`
let `A_t` be the chart ring (the integral closure of `κ[t]` in `K`, weil-curves).

* **Order of the norm** (`WeilReciprocity.ord_norm`): at a zero `P₀` of `t`,
  `ord_{P₀} N(f) = ord_{P₀}(t) · ∑_{t(P) = 0} ord_P f`. Via Mathlib's ideal norm `Ideal.relNorm`:
  every prime `Q | (t)` of `A_t` has `relNorm Q = (t)` (`WeilReciprocity.relNorm_eq_of_mem`,
  comparing `relNorm (t A_t) = (t)^n` with the fundamental identity `∑ e_Q = n`; all residue
  degrees are `1` since `κ` is algebraically closed. Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`
  does not apply since `κ(t)` is not perfect in positive characteristic).
* **Value of the norm** (`WeilReciprocity.val_norm`): if `f` is a unit at the zeros of `t`, then
  `N(f)(P₀) = ∏_{t(P) = 0} f(P)^{ord_P t}`. Via `N(x) mod (t) = det(x | A_t ⧸ (t))`
  (`WeilReciprocity.mk_norm_eq`), the Chinese remainder theorem
  `A_t ⧸ (t) ≅ ∏_Q A_t ⧸ Q^{e_Q}` (Mathlib's `Ideal.Factors.piQuotientLinearEquiv`), and the fact
  that multiplication by `x` on `A_t ⧸ Q^e` is `x(Q)` plus a nilpotent map
  (`WeilReciprocity.det_lmul_of_isNilpotent_sub`).
* **The projective line**: write `N(f) = r(g) / s(g)` with coprime `r, s ∈ κ[X]`. Then
  `f(div g) = N(f)(0) / N(f)(∞) = (r(0) / s(0)) / (lc r / lc s)` and
  `g(div f) = ∏_{a ≠ 0} a^{mult_a r - mult_a s} = ∏ roots(r) / ∏ roots(s)`; these agree since
  `r(0) = (-1)^{deg r} lc(r) ∏ roots(r)` and `deg r = deg s`.

## Main results

* `CurvesJacobian.weil_reciprocity`.
* `CurvesJacobian.WeilReciprocity.ord_norm`, `CurvesJacobian.WeilReciprocity.val_norm`: order and
  value of `N_{K/κ(t)}(f)` at the zeros of `t`.
* `CurvesJacobian.WeilReciprocity.mk_norm_eq`: the norm commutes with reduction modulo an ideal;
  `CurvesJacobian.WeilReciprocity.det_pi'`: determinant of a product of endomorphisms of a
  dependent finite product of free modules.
-/

open WeilCurves.FunctionField IsDedekindDomain Polynomial UniqueFactorizationMonoid
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

set_option linter.unusedSectionVars false

namespace CurvesJacobian

namespace WeilReciprocity

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

/-! ### Norms modulo an ideal -/

section NormQuotient

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S]

/-- The coordinates of an element of `I S` in an `R`-basis of `S` lie in `I`. -/
theorem repr_mem_of_mem_map {ι : Type*} (b : Module.Basis ι R S) (I : Ideal R) {y : S}
    (hy : y ∈ I.map (algebraMap R S)) (i : ι) : b.repr y i ∈ I := by
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map] at hy
  refine Submodule.smul_induction_on hy (fun r hr n _ ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ hr
  · rw [map_add, Finsupp.add_apply]
    exact I.add_mem hy hz

/-- **The norm commutes with reduction modulo an ideal**: `N(x) mod I = N(x mod I S)`. -/
theorem mk_norm_eq (I : Ideal R) (x : S) :
    Ideal.Quotient.mk I (Algebra.norm R x) =
      Algebra.norm (R ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap R S)) x) := by
  classical
  let b := Module.Free.chooseBasis R S
  set v : Module.Free.ChooseBasisIndex R S → S ⧸ I.map (algebraMap R S) :=
    fun i ↦ Ideal.Quotient.mk _ (b i) with hv
  have hsum : ∀ y : S, Ideal.Quotient.mk (I.map (algebraMap R S)) y =
      ∑ i, Ideal.Quotient.mk I (b.repr y i) • v i := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hv, Ideal.Quotient.mk_smul_mk_quotient_map_quotient, Algebra.smul_def, map_mul]
  have hli : LinearIndependent (R ⧸ I) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (g i)
    have h0 : Ideal.Quotient.mk (I.map (algebraMap R S)) (∑ j, c j • b j) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← hc j, hv, Ideal.Quotient.mk_smul_mk_quotient_map_quotient, Algebra.smul_def,
        map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0
    have := repr_mem_of_mem_map b I h0 i
    rw [b.repr_sum_self] at this
    rw [← hc i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have hsp : ⊤ ≤ Submodule.span (R ⧸ I) (Set.range v) := by
    rintro z -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hsum y]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = v i := fun i ↦ Module.Basis.mk_apply hli hsp i
  have hrepr : ∀ (y : S) (i), b'.repr (Ideal.Quotient.mk _ y) i =
      Ideal.Quotient.mk I (b.repr y i) := by
    intro y i
    rw [hsum y]
    simp_rw [← hb']
    rw [b'.repr_sum_self]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, hb', hv, ← map_mul, hrepr]

/-- `det (c + N) = c^{dim}` for a nilpotent endomorphism `N`. -/
theorem det_algebraMap_add_of_isNilpotent {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (c : F) {N : Module.End F M} (hN : IsNilpotent N) :
    LinearMap.det (algebraMap F (Module.End F M) c + N) = c ^ Module.finrank F M := by
  rw [← sub_neg_eq_add, ← LinearMap.eval_charpoly, hN.neg.charpoly_eq_X_pow_finrank, eval_pow,
    eval_X]

/-- If `a - c` is nilpotent then `N_{A/F}(a) = c^{[A : F]}`. -/
theorem det_lmul_of_isNilpotent_sub {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A] (a : A) (c : F) (h : IsNilpotent (a - algebraMap F A c)) :
    LinearMap.det (Algebra.lmul F A a) = c ^ Module.finrank F A := by
  have : Algebra.lmul F A a = algebraMap F (Module.End F A) c +
      Algebra.lmul F A (a - algebraMap F A c) := by
    rw [map_sub, AlgHom.commutes, add_sub_cancel]
  rw [this, det_algebraMap_add_of_isNilpotent c (h.map (Algebra.lmul F A))]

theorem det_lmul_of_isNilpotent_sub' {F A B : Type*} [Field F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A] [CommRing B] (π : B →+* A) (x y : B) (c : F)
    (hc : algebraMap F A c = π y) (h : IsNilpotent (π (x - y))) :
    LinearMap.det (Algebra.lmul F A (π x)) = c ^ Module.finrank F A := by
  rw [map_sub, ← hc] at h
  exact det_lmul_of_isNilpotent_sub _ c h

/-- The determinant of a block diagonal matrix with blocks of varying sizes. -/
theorem det_blockDiagonal'' {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (A : ∀ i, Matrix (m i) (m i) R) : (Matrix.blockDiagonal' A).det = ∏ i, (A i).det := by
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' A).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have hinj : Function.Injective
      (fun a : m k ↦ (⟨⟨k, a⟩, rfl⟩ : {x : (Σ i, m i) // x.1 = k})) := by
    intro a b h
    simpa using congrArg (fun x : {x : (Σ i, m i) // x.1 = k} ↦ x.1) h
  have hsurj : Function.Surjective
      (fun a : m k ↦ (⟨⟨k, a⟩, rfl⟩ : {x : (Σ i, m i) // x.1 = k})) := by
    rintro ⟨⟨i, a⟩, h⟩
    subst h
    exact ⟨a, rfl⟩
  rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ ⟨hinj, hsurj⟩)]
  congr 1
  ext a b
  simp [Matrix.toSquareBlock_def, Matrix.blockDiagonal'_apply_eq]

/-- The determinant of a product of endomorphisms of a (dependent) finite product of free
modules. -/
theorem det_pi' {R ι : Type*} [CommRing R] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)] (f : ∀ i, Module.End R (M i)) :
    (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det := by
  classical
  let b := fun i ↦ Module.Free.chooseBasis R (M i)
  let B := Pi.basis b
  have h : LinearMap.toMatrix B B (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))) =
      Matrix.blockDiagonal' (fun i ↦ LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rw [LinearMap.toMatrix_apply', Matrix.blockDiagonal'_apply]
    by_cases hij : i₁ = j₁
    · subst hij
      simp [B, Pi.basis_apply, Pi.basis_repr, LinearMap.toMatrix_apply']
    · simp [B, Pi.basis_apply, Pi.basis_repr, hij]
  rw [← LinearMap.det_toMatrix B, h, det_blockDiagonal'']
  exact Finset.prod_congr rfl fun i _ ↦ LinearMap.det_toMatrix (b i) (f i)

theorem det_pi_field {F ι : Type*} [Field F] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)] [∀ i, FiniteDimensional F (M i)]
    (f : ∀ i, Module.End F (M i)) :
    (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det :=
  det_pi' f

section CRT

variable [IsDedekindDomain S] (p : Ideal R) [p.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/-- On `S ⧸ Q^e` (`Q | p` of residue degree `1`), multiplication by `x ≡ r mod Q` is `r` plus a
nilpotent map, so its determinant is `r^e`. -/
theorem det_lmul_quotient_pow (Q : (factors (p.map (algebraMap R S))).toFinset)
    (hf : Ideal.inertiaDeg' p (Q : Ideal S) = 1) (x : S) (r : R)
    (hr : x - algebraMap R S r ∈ (Q : Ideal S)) :
    LinearMap.det (Algebra.lmul (R ⧸ p) (S ⧸ (Q : Ideal S) ^ Ideal.ramificationIdx' p (Q : Ideal S))
      (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk p r ^ Ideal.ramificationIdx' p (Q : Ideal S) := by
  have hnil : IsNilpotent (Ideal.Quotient.mk
      ((Q : Ideal S) ^ Ideal.ramificationIdx' p (Q : Ideal S)) (x - algebraMap R S r)) :=
    ⟨_, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hr _⟩
  have hf' := Ideal.Factors.finrank_pow_ramificationIdx p Q
  rw [hf, mul_one] at hf'
  rw [det_lmul_of_isNilpotent_sub' (Ideal.Quotient.mk _) x (algebraMap R S r)
    (Ideal.Quotient.mk p r) (Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx _ _ _) hnil,
    hf']

/-- **Chinese remainder theorem**: `N(x mod p)` is the product of the determinants of
multiplication by `x` on the `S ⧸ Q^{e_Q}`. -/
theorem norm_quotient_eq_prod (hp : p.map (algebraMap R S) ≠ ⊥) (x : S) :
    Algebra.norm (R ⧸ p) (Ideal.Quotient.mk (p.map (algebraMap R S)) x) =
      ∏ Q : (factors (p.map (algebraMap R S))).toFinset,
        LinearMap.det (Algebra.lmul (R ⧸ p)
          (S ⧸ (Q : Ideal S) ^ Ideal.ramificationIdx' p (Q : Ideal S))
          (Ideal.Quotient.mk _ x)) := by
  set e := Ideal.Factors.piQuotientLinearEquiv S p hp
  rw [Algebra.norm_apply, ← LinearMap.det_conj _ e, ← det_pi_field]
  congr 1
  refine LinearMap.ext fun z ↦ funext fun Q ↦ ?_
  change Ideal.Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x * e.symm z) Q =
    Ideal.Quotient.mk _ x * z Q
  rw [map_mul, Ideal.Factors.piQuotientEquiv_mk]
  change _ * e (e.symm z) Q = _
  rw [e.apply_symm_apply]

/-- `N(x) mod p = ∏_{Q | p} x(Q)^{e_Q}` when all residue degrees are `1`. -/
theorem mk_norm_eq_prod (hp : p.map (algebraMap R S) ≠ ⊥) (x : S) (c : Ideal S → R)
    (hf : ∀ Q ∈ (factors (p.map (algebraMap R S))).toFinset, Ideal.inertiaDeg' p Q = 1)
    (hc : ∀ Q ∈ (factors (p.map (algebraMap R S))).toFinset, x - algebraMap R S (c Q) ∈ Q) :
    Ideal.Quotient.mk p (Algebra.norm R x) =
      ∏ Q ∈ (factors (p.map (algebraMap R S))).toFinset,
        Ideal.Quotient.mk p (c Q) ^ Ideal.ramificationIdx' p Q := by
  refine ((mk_norm_eq p x).trans (norm_quotient_eq_prod p hp x)).trans ?_
  conv_rhs => rw [← Finset.prod_coe_sort]
  exact Finset.prod_congr rfl fun Q _ ↦ det_lmul_quotient_pow p Q (hf Q Q.2) x (c Q) (hc Q Q.2)

end CRT

end NormQuotient

/-! ### The chart of a transcendental element -/

section Chart

variable (κ) (t : K) [Fact (Transcendental κ t)]

instance : IsPrincipalIdealRing (Algebra.adjoin κ {t}) := isPrincipalIdealRing_adjoin Fact.out

/-- `t` as an element of `κ[t]`. -/
noncomputable def tR : Algebra.adjoin κ {t} := ⟨t, Algebra.self_mem_adjoin_singleton κ t⟩

theorem algEquiv_X : Polynomial.algEquivOfTranscendental κ t Fact.out X = tR κ t := by
  rw [Polynomial.algEquivOfTranscendental_apply, aeval_X]; rfl

theorem irreducible_tR : Irreducible (tR κ t) := by
  rw [← algEquiv_X]
  exact (MulEquiv.irreducible_iff
    (Polynomial.algEquivOfTranscendental κ t Fact.out).toMulEquiv).mpr Polynomial.irreducible_X

instance isMaximal_span_tR : (Ideal.span {tR κ t}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_tR κ t)

theorem span_tR_ne_bot : Ideal.span {tR κ t} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact (irreducible_tR κ t).ne_zero

/-- `κ[t] ⧸ (t) = κ`. -/
theorem finrank_quotient_span_tR :
    Module.finrank κ (Algebra.adjoin κ {t} ⧸ Ideal.span {tR κ t}) = 1 := by
  letI := Ideal.Quotient.field (Ideal.span {tR κ t})
  let e := Polynomial.algEquivOfTranscendental κ t Fact.out
  have he : e X = tR κ t := algEquiv_X κ t
  have hsurj : Function.Surjective
      (algebraMap κ (Algebra.adjoin κ {t} ⧸ Ideal.span {tR κ t})) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨q, rfl⟩ := e.surjective r
    obtain ⟨q', hq'⟩ := Polynomial.X_dvd_sub_C (p := q)
    refine ⟨q.coeff 0, ?_⟩
    rw [IsScalarTower.algebraMap_apply κ (Algebra.adjoin κ {t}), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq, ← AlgEquiv.commutes e, ← map_sub, Polynomial.algebraMap_eq,
      ← neg_sub, map_neg, neg_mem_iff, hq', map_mul, he]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hbij : Function.Bijective
      (Algebra.ofId κ (Algebra.adjoin κ {t} ⧸ Ideal.span {tR κ t})) :=
    ⟨(algebraMap κ _).injective, hsurj⟩
  rw [← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- `t` as an element of the chart ring `A_t`. -/
noncomputable def tS : chartRing κ t :=
  algebraMap (Algebra.adjoin κ {t}) (chartRing κ t) (tR κ t)

theorem coe_tS : ((tS κ t : chartRing κ t) : K) = t := rfl

theorem tS_ne_zero : tS κ t ≠ 0 := by
  intro h
  exact ne_zero_of_transcendental (Fact.out : Transcendental κ t) (congrArg Subtype.val h)

theorem map_span_tR :
    (Ideal.span {tR κ t}).map (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)) =
      Ideal.span {tS κ t} := by
  rw [Ideal.map_span, Set.image_singleton]; rfl

theorem map_span_tR_ne_bot :
    (Ideal.span {tR κ t}).map (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)) ≠ ⊥ := by
  rw [map_span_tR, Ne, Ideal.span_singleton_eq_bot]; exact tS_ne_zero κ t

theorem mem_primesOver_iff (v : HeightOneSpectrum (chartRing κ t)) :
    v.asIdeal ∈ (Ideal.span {tR κ t}).primesOver (chartRing κ t) ↔ tS κ t ∈ v.asIdeal := by
  constructor
  · rintro ⟨-, hlo⟩
    have h1 : tR κ t ∈ v.asIdeal.under (Algebra.adjoin κ {t}) := by
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    exact h1
  · intro h
    refine ⟨v.isPrime, ⟨(isMaximal_span_tR κ t).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h

theorem mem_asIdeal_iff (v : HeightOneSpectrum (chartRing κ t)) :
    tS κ t ∈ v.asIdeal ↔ 0 < (Place.ofChart t v).ord t := by
  have h := Place.mem_toChart_iff t (Place.ofChart t v) (Place.self_mem_ofChart t v)
    (r := tS κ t)
  rw [Place.toChart_ofChart] at h
  rw [Place.ord_pos_iff, h]
  exact ⟨fun h' ↦ ⟨ne_zero_of_transcendental (Fact.out : Transcendental κ t), h'⟩,
    fun h' ↦ h'.2⟩

theorem inertiaDeg'_eq_finrank (P : Ideal (chartRing κ t)) [P.IsPrime]
    [P.LiesOver (Ideal.span {tR κ t})] :
    Ideal.inertiaDeg' (Ideal.span {tR κ t}) P = Module.finrank κ (chartRing κ t ⧸ P) := by
  letI := Ideal.Quotient.field (Ideal.span {tR κ t})
  have : Module.Free κ (Algebra.adjoin κ {t} ⧸ Ideal.span {tR κ t}) :=
    Module.Free.of_divisionRing _ _
  have : Module.Free (Algebra.adjoin κ {t} ⧸ Ideal.span {tR κ t}) (chartRing κ t ⧸ P) :=
    Module.Free.of_divisionRing _ _
  rw [Ideal.inertiaDeg'_algebraMap,
    ← Module.finrank_mul_finrank κ (Algebra.adjoin κ {t} ⧸ Ideal.span {tR κ t}),
    finrank_quotient_span_tR, one_mul]

/-- The place of `K` attached to an ideal of the chart ring (junk if it is not a nonzero
prime). -/
noncomputable def placeOf (Q : Ideal (chartRing κ t)) : Place κ K := by
  classical
  exact if h : Q.IsPrime ∧ Q ≠ ⊥ then Place.ofChart t ⟨Q, h.1, h.2⟩ else Classical.arbitrary _

variable {κ t}

theorem isPrime_ne_bot_of_mem {Q : Ideal (chartRing κ t)}
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t)) :
    Q.IsPrime ∧ Q ≠ ⊥ := by
  have hmem := (IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t) _).mp hQ
  exact ⟨hmem.1, Ideal.ne_bot_of_mem_primesOver (span_tR_ne_bot κ t) hmem⟩

theorem placeOf_eq {Q : Ideal (chartRing κ t)} (h : Q.IsPrime ∧ Q ≠ ⊥) :
    placeOf κ t Q = Place.ofChart t ⟨Q, h.1, h.2⟩ := by
  rw [placeOf, dif_pos h]

theorem toChart_placeOf {Q : Ideal (chartRing κ t)} (h : Q.IsPrime ∧ Q ≠ ⊥) :
    ((placeOf κ t Q).toChart t
      (by rw [placeOf_eq h]; exact Place.self_mem_ofChart t _)).asIdeal = Q := by
  have := Place.toChart_ofChart t (⟨Q, h.1, h.2⟩ : HeightOneSpectrum (chartRing κ t))
  convert congrArg HeightOneSpectrum.asIdeal this using 3; rw [placeOf_eq h]

/-- Reindexing products over the zeros of `t` by the primes of `A_t` over `(t)`. -/
@[to_additive /-- Reindexing sums over the zeros of `t` by the primes of `A_t` over `(t)`. -/]
theorem prod_zeros_eq {M : Type*} [CommMonoid M] (φ : Place κ K → M) :
    ∏ P ∈ (Place.finite_setOf_ord_pos (k := κ) t).toFinset, φ P =
      ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
        φ (placeOf κ t Q) := by
  symm
  refine Finset.prod_bij' (fun Q _ ↦ placeOf κ t Q)
    (fun P hP ↦ (P.toChart t (P.mem_of_ord_nonneg
      ((Set.Finite.mem_toFinset _).mp hP).le)).asIdeal) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro Q hQ
    have h := isPrime_ne_bot_of_mem hQ
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, placeOf_eq h, ← mem_asIdeal_iff κ t,
      ← mem_primesOver_iff κ t]
    exact (IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t) _).mp hQ
  · intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t) _]
    have hP' := (Set.Finite.mem_toFinset _).mp hP
    refine (mem_primesOver_iff κ t (P.toChart t (P.mem_of_ord_nonneg hP'.le))).mpr ?_
    rw [Place.mem_toChart_iff]
    exact ((P.ord_pos_iff).mp hP').2
  · intro Q hQ
    exact toChart_placeOf (isPrime_ne_bot_of_mem hQ)
  · intro P hP
    have hP' := (Set.Finite.mem_toFinset _).mp hP
    set v := P.toChart t (P.mem_of_ord_nonneg hP'.le)
    have h : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥ := ⟨v.isPrime, v.ne_bot⟩
    rw [placeOf_eq h]
    exact Place.ofChart_toChart t P (P.mem_of_ord_nonneg hP'.le)

/-- A constant of `κ` as an element of `A_t`. -/
noncomputable def cS (c : κ) : chartRing κ t :=
  algebraMap (Algebra.adjoin κ {t}) (chartRing κ t) (algebraMap κ (Algebra.adjoin κ {t}) c)

theorem coe_cS (c : κ) : ((cS (t := t) c : chartRing κ t) : K) = algebraMap κ K c := rfl

theorem ord_placeOf {Q : Ideal (chartRing κ t)} (h : Q.IsPrime ∧ Q ≠ ⊥) {x : chartRing κ t}
    (hx : x ≠ 0) :
    (placeOf κ t Q).ord (x : K) = (normalizedFactors (Ideal.span {x})).count Q := by
  rw [placeOf_eq h]
  have := Place.ord_ofChart_algebraMap t (⟨Q, h.1, h.2⟩ : HeightOneSpectrum (chartRing κ t)) hx
  rw [show (x : K) = algebraMap (chartRing κ t) K x from rfl, this,
    multiplicity_eq_count_normalizedFactors (Ideal.prime_of_isPrime h.2 h.1).irreducible
      (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]), normalize_eq]

theorem ord_placeOf_t {Q : Ideal (chartRing κ t)}
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t)) :
    (placeOf κ t Q).ord t = Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q := by
  have h := isPrime_ne_bot_of_mem hQ
  have := h.1
  have h1 := ord_placeOf h (tS_ne_zero κ t)
  rw [coe_tS] at h1
  rw [h1, ← map_span_tR,
    Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (map_span_tR_ne_bot κ t)
      h.1 h.2]

theorem inertiaDeg'_eq_one {Q : Ideal (chartRing κ t)}
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t)) :
    Ideal.inertiaDeg' (Ideal.span {tR κ t}) Q = 1 := by
  have hmem := (IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t) _).mp hQ
  have : Q.IsPrime := hmem.1
  have : Q.LiesOver (Ideal.span {tR κ t}) := hmem.2
  have h := isPrime_ne_bot_of_mem hQ
  rw [inertiaDeg'_eq_finrank κ t Q,
    show Q = (⟨Q, h.1, h.2⟩ : HeightOneSpectrum (chartRing κ t)).asIdeal from rfl,
    Place.finrank_quotient_eq_deg, Place.deg_eq_one]

/-- `x ≡ x(P) mod Q` for the place `P` attached to `Q`. -/
theorem sub_val_mem {Q : Ideal (chartRing κ t)} (h : Q.IsPrime ∧ Q ≠ ⊥) (x : chartRing κ t) :
    x - cS (Place.val (placeOf κ t Q) (x : K)) ∈ Q := by
  set v : HeightOneSpectrum (chartRing κ t) := ⟨Q, h.1, h.2⟩
  have hP : placeOf κ t Q = Place.ofChart t v := placeOf_eq h
  have hx : (x : K) ∈ (placeOf κ t Q).1 := by
    rw [hP]; exact (Place.ofChart t v).algebraMap_chartRing_mem t (Place.self_mem_ofChart t v) x
  have hv := (Place.val_eq_iff (placeOf κ t Q) hx (Place.val (placeOf κ t Q) (x : K))).mp rfl
  rcases hv with h0 | hpos
  · have : x - cS (Place.val (placeOf κ t Q) (x : K)) = 0 :=
      Subtype.ext (by simpa [coe_cS] using h0)
    rw [this]; exact Q.zero_mem
  · have hmem := Place.mem_toChart_iff t (Place.ofChart t v) (Place.self_mem_ofChart t v)
      (r := x - cS (Place.val (placeOf κ t Q) (x : K)))
    rw [Place.toChart_ofChart] at hmem
    refine hmem.mpr ?_
    rw [← hP]
    exact ((placeOf κ t Q).ord_pos_iff.mp hpos).2

end Chart

/-! ### The ideal norm of the primes over `(t)` -/

section RelNorm

variable {t : K} [Fact (Transcendental κ t)]

theorem multiset_prod_map_pow {M ι : Type*} [CommMonoid M] (a : M) (f : ι → ℕ)
    (s : Multiset ι) : (s.map fun i ↦ a ^ f i).prod = a ^ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih => simp [pow_add, ih]

theorem relNorm_map_span_tR :
    Ideal.relNorm (Algebra.adjoin κ {t}) ((Ideal.span {tR κ t}).map
      (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t))) =
      Ideal.span {tR κ t} ^ Module.finrank (Algebra.adjoin κ {t}) (chartRing κ t) := by
  rw [map_span_tR, Ideal.relNorm_singleton, Algebra.intNorm_eq_norm, tS,
    Algebra.norm_algebraMap, Ideal.span_singleton_pow]

theorem finrank_chartRing :
    Module.finrank (Algebra.adjoin κ {t}) (chartRing κ t) = Module.finrank κ⟮t⟯ K :=
  (Algebra.IsAlgebraic.finrank_of_isFractionRing (Algebra.adjoin κ {t}) κ⟮t⟯
      (chartRing κ t) K).symm

/-- All residue degrees are `1`, so the ideal norm of a prime `Q` of `A_t` over `(t)` is `(t)`.
(Over the imperfect field `κ(t)` Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal` does not apply;
we compare `relNorm (t A_t) = (t)^n` with the fundamental identity `∑ e_Q = n`.) -/
theorem relNorm_eq_of_mem {Q : Ideal (chartRing κ t)}
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t)) :
    Ideal.relNorm (Algebra.adjoin κ {t}) Q = Ideal.span {tR κ t} := by
  classical
  have hp0 := span_tR_ne_bot κ t
  have hmap0 := map_span_tR_ne_bot κ t
  set F := factors ((Ideal.span {tR κ t}).map
    (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t))) with hF
  have hex : ∀ Q' ∈ F, ∃ s, Ideal.relNorm (Algebra.adjoin κ {t}) Q' =
      Ideal.span {tR κ t} ^ s := by
    intro Q' hQ'
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp
      (Multiset.mem_toFinset.mpr hQ')
    have : Q'.IsPrime := hmem.1
    have : Q'.LiesOver (Ideal.span {tR κ t}) := hmem.2
    exact Ideal.exists_relNorm_eq_pow_of_isPrime Q' _
  choose! s hs using hex
  have hs1 : ∀ Q' ∈ F, 1 ≤ s Q' := by
    intro Q' hQ'
    by_contra h0
    have h00 : s Q' = 0 := by omega
    have hle := Ideal.relNorm_le_comap (Algebra.adjoin κ {t}) Q'
    rw [hs Q' hQ', h00, pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.comap_eq_top_iff] at hle
    exact (Ideal.isPrime_of_prime (prime_of_factor _ hQ')).ne_top hle
  have key : Ideal.span {tR κ t} ^ Module.finrank (Algebra.adjoin κ {t}) (chartRing κ t) =
      Ideal.span {tR κ t} ^ (F.map s).sum := by
    rw [← relNorm_map_span_tR]
    conv_lhs => rw [← associated_iff_eq.mp (factors_prod hmap0)]
    rw [map_multiset_prod, Multiset.map_congr rfl hs, multiset_prod_map_pow]
  have hinj := pow_injective_of_not_isUnit (q := Ideal.span {tR κ t})
    (by rw [Ideal.isUnit_iff]; exact (isMaximal_span_tR κ t).ne_top) hp0
  have hsum : (F.map s).sum = Multiset.card F := by
    rw [← hinj key, finrank_chartRing, ← Ideal.sum_ramification_inertia (chartRing κ t) κ⟮t⟯ K hp0,
      ← Multiset.toFinset_sum_count_eq]
    refine Finset.sum_congr rfl fun Q' hQ' ↦ ?_
    have h := isPrime_ne_bot_of_mem hQ'
    rw [inertiaDeg'_eq_one hQ', mul_one,
      Ideal.IsDedekindDomain.ramificationIdx'_eq_factors_count hmap0 h.1 h.2]
  have hQF : Q ∈ F := Multiset.mem_toFinset.mp hQ
  obtain ⟨F', hF'⟩ := Multiset.exists_cons_of_mem hQF
  have hle : (F'.map fun _ ↦ 1).sum ≤ (F'.map s).sum :=
    Multiset.sum_map_le_sum_map _ _ fun Q' hQ' ↦ hs1 Q' (hF' ▸ Multiset.mem_cons_of_mem hQ')
  rw [hF', Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons] at hsum
  simp only [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one] at hle
  have h1 : s Q = 1 := by have := hs1 Q hQF; omega
  rw [hs Q hQF, h1, pow_one]

theorem map_ne_bot {J : Ideal (Algebra.adjoin κ {t})} (hJ : J ≠ ⊥) :
    J.map (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)) ≠ ⊥ := by
  rwa [Ne, Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective (Algebra.adjoin κ {t}) (chartRing κ t))]

/-- The prime `Q₀` over `(t)` does not divide the extension of the norm of a prime not over
`(t)`. -/
theorem count_map_relNorm_prime {Q₀ Q : Ideal (chartRing κ t)}
    (hQ₀ : Q₀ ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t))
    (hQ : Prime Q) :
    (normalizedFactors ((Ideal.relNorm (Algebra.adjoin κ {t}) Q).map
      (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)))).count Q₀ =
      Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q₀ *
        if Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t)
        then 1 else 0 := by
  classical
  have h₀ := isPrime_ne_bot_of_mem hQ₀
  by_cases hQp : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t)
  · rw [if_pos hQp, mul_one, relNorm_eq_of_mem hQp,
      Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (map_span_tR_ne_bot κ t)
        h₀.1 h₀.2]
  rw [if_neg hQp, mul_zero, Multiset.count_eq_zero]
  intro hmem
  apply hQp
  have hle := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hmem)
  rw [Ideal.map_le_iff_le_comap] at hle
  have hmem₀ := (IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t) _).mp hQ₀
  have hover : Ideal.span {tR κ t} = Q₀.under (Algebra.adjoin κ {t}) := hmem₀.2.over
  have hQne : Q ≠ ⊥ := hQ.ne_zero
  have : Q₀.IsPrime := h₀.1
  have : Q.IsPrime := Ideal.isPrime_of_prime hQ
  have hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal this hQne
  have hqmax : (Q.under (Algebra.adjoin κ {t})).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime Q (Q.under (Algebra.adjoin κ {t}))
  rw [hs] at hle
  have hle' : Q.under (Algebra.adjoin κ {t}) ≤ Ideal.span {tR κ t} := by
    rw [hover]
    exact Ideal.IsPrime.le_of_pow_le hle
  have heq := hqmax.eq_of_le (isMaximal_span_tR κ t).ne_top hle'
  rw [IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t)]
  exact ⟨this, ⟨heq.symm⟩⟩

/-- The multiplicity of `Q₀ | (t)` in the extension of `relNorm I` is `e(Q₀) · ∑_{Q | (t)} v_Q(I)`.
-/
theorem count_map_relNorm {Q₀ : Ideal (chartRing κ t)}
    (hQ₀ : Q₀ ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t))
    (I : Ideal (chartRing κ t)) (hI : I ≠ ⊥) :
    (normalizedFactors ((Ideal.relNorm (Algebra.adjoin κ {t}) I).map
      (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)))).count Q₀ =
      Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q₀ *
        ∑ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
          (normalizedFactors I).count Q := by
  classical
  revert hI
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro x hx _
    rw [Ideal.isUnit_iff.mp hx, Ideal.relNorm_top, Ideal.map_top, ← Ideal.one_eq_top,
      normalizedFactors_one]
    simp
  · intro J Q hJ hQ ih _
    have hrQ : Ideal.relNorm (Algebra.adjoin κ {t}) Q ≠ ⊥ := by
      rw [Ne, Ideal.relNorm_eq_bot_iff]; exact hQ.ne_zero
    have hrJ : Ideal.relNorm (Algebra.adjoin κ {t}) J ≠ ⊥ := by
      rw [Ne, Ideal.relNorm_eq_bot_iff]; exact hJ
    rw [map_mul, Ideal.map_mul, normalizedFactors_mul (map_ne_bot hrQ) (map_ne_bot hrJ),
      Multiset.count_add, count_map_relNorm_prime hQ₀ hQ, ih hJ,
      normalizedFactors_mul hQ.ne_zero hJ, normalizedFactors_irreducible hQ.irreducible,
      normalize_eq]
    simp only [Multiset.count_add, Finset.sum_add_distrib, Multiset.count_singleton, mul_add]
    rw [Finset.sum_ite_eq']

/-- **Order of the norm** in the chart: for `x ∈ A_t` and `Q₀ | (t)`,
`ord_{Q₀} N(x) = e(Q₀) · ∑_{Q | (t)} ord_Q x`. -/
theorem ord_norm_chart {Q₀ : Ideal (chartRing κ t)}
    (hQ₀ : Q₀ ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t))
    {x : chartRing κ t} (hx : x ≠ 0) :
    (placeOf κ t Q₀).ord ((Algebra.norm (Algebra.adjoin κ {t}) x : Algebra.adjoin κ {t}) : K) =
      (placeOf κ t Q₀).ord t *
        ∑ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
          (placeOf κ t Q).ord (x : K) := by
  have h₀ := isPrime_ne_bot_of_mem hQ₀
  have hN : Algebra.norm (Algebra.adjoin κ {t}) x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have hN' : algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)
      (Algebra.norm (Algebra.adjoin κ {t}) x) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective (Algebra.adjoin κ {t}) (chartRing κ t))]
  have e1 : ((Algebra.norm (Algebra.adjoin κ {t}) x : Algebra.adjoin κ {t}) : K) =
      ((algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)
        (Algebra.norm (Algebra.adjoin κ {t}) x) : chartRing κ t) : K) := rfl
  have hspan : Ideal.span {algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)
      (Algebra.norm (Algebra.adjoin κ {t}) x)} =
      (Ideal.relNorm (Algebra.adjoin κ {t}) (Ideal.span {x})).map
        (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t)) := by
    rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm, Ideal.map_span, Set.image_singleton]
  have hx' : Ideal.span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [e1, ord_placeOf h₀ hN', ord_placeOf_t hQ₀, hspan, count_map_relNorm hQ₀ _ hx']
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun Q hQ ↦ ?_
  rw [ord_placeOf (isPrime_ne_bot_of_mem hQ) hx]

/-- The norm of `K / κ(t)` restricts to the norm of `A_t / κ[t]`. -/
theorem algebraMap_norm_chart (x : chartRing κ t) :
    algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ (x : K)) =
      ((Algebra.norm (Algebra.adjoin κ {t}) x : Algebra.adjoin κ {t}) : K) := by
  haveI := IsIntegralClosure.isLocalization (Algebra.adjoin κ {t}) κ⟮t⟯ K (chartRing κ t)
  have h := Algebra.norm_localization (Algebra.adjoin κ {t}) (Rₘ := κ⟮t⟯) (Sₘ := K)
    (nonZeroDivisors (Algebra.adjoin κ {t})) x
  rw [show (x : K) = algebraMap (chartRing κ t) K x from rfl, h,
    ← IsScalarTower.algebraMap_apply]
  rfl

end RelNorm

/-! ### The value of the norm at a zero of `t` -/

section Value

variable {t : K} [Fact (Transcendental κ t)]

/-- `N(x) ≡ ∏_{Q | (t)} x(Q)^{e_Q} mod (t)` for `x ∈ A_t`. -/
theorem mk_norm_chart (x : chartRing κ t) :
    Ideal.Quotient.mk (Ideal.span {tR κ t}) (Algebra.norm (Algebra.adjoin κ {t}) x) =
      Ideal.Quotient.mk (Ideal.span {tR κ t}) (algebraMap κ (Algebra.adjoin κ {t})
        (∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
          Place.val (placeOf κ t Q) (x : K) ^ Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q)) := by
  rw [mk_norm_eq_prod (Ideal.span {tR κ t}) (map_span_tR_ne_bot κ t) x
    (fun Q ↦ algebraMap κ (Algebra.adjoin κ {t}) (Place.val (placeOf κ t Q) (x : K)))
    (fun Q hQ ↦ inertiaDeg'_eq_one hQ) (fun Q hQ ↦ sub_val_mem (isPrime_ne_bot_of_mem hQ) x)]
  simp only [map_prod, map_pow]

theorem mem_placeOf {Q : Ideal (chartRing κ t)} (h : Q.IsPrime ∧ Q ≠ ⊥) (y : chartRing κ t) :
    (y : K) ∈ (placeOf κ t Q).1 := by
  rw [placeOf_eq h]
  exact (Place.ofChart t _).algebraMap_chartRing_mem t (Place.self_mem_ofChart t _) y

theorem ord_placeOf_t_pos {Q : Ideal (chartRing κ t)}
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t)) :
    0 < (placeOf κ t Q).ord t := by
  have h := isPrime_ne_bot_of_mem hQ
  rw [ord_placeOf_t hQ]
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
    (map_span_tR_ne_bot κ t) h.1 (by
      rw [IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t)] at hQ
      rw [Ideal.map_le_iff_le_comap, hQ.2.over]))

/-- **Value of the norm** in the chart: `N(x)(Q₀) = ∏_{Q | (t)} x(Q)^{e_Q}` for `x ∈ A_t`. -/
theorem val_norm_chart {Q₀ : Ideal (chartRing κ t)}
    (hQ₀ : Q₀ ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t))
    (x : chartRing κ t) :
    Place.val (placeOf κ t Q₀)
      ((Algebra.norm (Algebra.adjoin κ {t}) x : Algebra.adjoin κ {t}) : K) =
      ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
        Place.val (placeOf κ t Q) (x : K) ^ Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q := by
  have h₀ := isPrime_ne_bot_of_mem hQ₀
  have hmk := mk_norm_chart x
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hmk
  obtain ⟨r, hr⟩ := hmk
  set c := ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
    Place.val (placeOf κ t Q) (x : K) ^ Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q
  have hK : ((Algebra.norm (Algebra.adjoin κ {t}) x : Algebra.adjoin κ {t}) : K) =
      algebraMap κ K c + (r : K) * t := by
    have := congrArg (fun z : Algebra.adjoin κ {t} ↦ (z : K)) hr
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_algebraMap] at this
    rw [show ((tR κ t : Algebra.adjoin κ {t}) : K) = t from rfl] at this
    rw [this]; ring
  have hrmem : (r : K) ∈ (placeOf κ t Q₀).1 :=
    mem_placeOf h₀ (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t) r)
  have htmem : t ∈ (placeOf κ t Q₀).1 := mem_placeOf h₀ (tS κ t)
  have ht0 : Place.val (placeOf κ t Q₀) t = 0 :=
    (Place.val_eq_zero_iff (placeOf κ t Q₀) htmem).mpr (Or.inr (ord_placeOf_t_pos hQ₀))
  rw [hK, Place.val_add _ ((placeOf κ t Q₀).algebraMap_mem c) (mul_mem hrmem htmem),
    Place.val_mul _ hrmem htmem, ht0, mul_zero, add_zero, Place.val_algebraMap]

end Value

/-! ### Order and value of the norm `N_{K/κ(t)}` -/

section FieldNorm

variable {t : K} [Fact (Transcendental κ t)]

theorem toChart_mem {P : Place κ K} (hP : 0 < P.ord t) :
    (P.toChart t (P.mem_of_ord_nonneg hP.le)).asIdeal ∈
      IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t) := by
  rw [IsDedekindDomain.mem_primesOverFinset_iff (span_tR_ne_bot κ t)]
  refine (mem_primesOver_iff κ t _).mpr ?_
  rw [Place.mem_toChart_iff]
  exact ((P.ord_pos_iff).mp hP).2

theorem placeOf_toChart {P : Place κ K} (hP : 0 < P.ord t) :
    placeOf κ t (P.toChart t (P.mem_of_ord_nonneg hP.le)).asIdeal = P := by
  set v := P.toChart t (P.mem_of_ord_nonneg hP.le)
  rw [placeOf_eq ⟨v.isPrime, v.ne_bot⟩]
  exact Place.ofChart_toChart t P (P.mem_of_ord_nonneg hP.le)

theorem coe_ne_zero_of_mem_nonZeroDivisors {x : chartRing κ t}
    (hx : x ∈ nonZeroDivisors (chartRing κ t)) : (x : K) ≠ 0 := fun h ↦
  nonZeroDivisors.ne_zero hx (Subtype.ext h)

/-- **Order of the norm**: `ord_{P₀} N(f) = ord_{P₀}(t) · ∑_{t(P) = 0} ord_P f`. -/
theorem ord_norm_adjoin {f : K} (hf : f ≠ 0) {P₀ : Place κ K} (hP₀ : 0 < P₀.ord t) :
    P₀.ord (algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ f)) =
      P₀.ord t * ∑ P ∈ (Place.finite_setOf_ord_pos (k := κ) t).toFinset, P.ord f := by
  have key : ∀ x : chartRing κ t, x ≠ 0 →
      P₀.ord (algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ (x : K))) =
        P₀.ord t * ∑ P ∈ (Place.finite_setOf_ord_pos (k := κ) t).toFinset, P.ord (x : K) := by
    intro x hx
    have h := ord_norm_chart (toChart_mem hP₀) hx
    rw [placeOf_toChart hP₀] at h
    rw [algebraMap_norm_chart, h, sum_zeros_eq]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := chartRing κ t) f
  have hb0 : (b : K) ≠ 0 := coe_ne_zero_of_mem_nonZeroDivisors hb
  have ha0 : (a : K) ≠ 0 := left_ne_zero_of_mul (by rwa [div_eq_mul_inv] at hf)
  have ha0' : a ≠ 0 := fun h ↦ ha0 (by rw [h]; rfl)
  have hb0' : b ≠ 0 := fun h ↦ hb0 (by rw [h]; rfl)
  have hNa : Algebra.norm κ⟮t⟯ (a : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha0
  have hNb : Algebra.norm κ⟮t⟯ (b : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb0
  change P₀.ord (algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ ((a : K) / (b : K)))) =
    P₀.ord t * ∑ P ∈ (Place.finite_setOf_ord_pos (k := κ) t).toFinset, P.ord ((a : K) / (b : K))
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_mul, map_inv₀,
    Place.ord_mul _ ((_root_.map_ne_zero _).mpr hNa)
      (inv_ne_zero ((_root_.map_ne_zero _).mpr hNb)),
    Place.ord_inv, key a ha0', key b hb0']
  simp only [Place.ord_mul _ ha0 (inv_ne_zero hb0), Place.ord_inv, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  ring

/-- Prime avoidance: a function regular at the zeros of `t` has a denominator in `A_t` which
does not vanish at the zeros of `t`. -/
theorem exists_mul_mem_chart {f : K} (hf : ∀ P : Place κ K, 0 < P.ord t → f ∈ P.1) :
    ∃ y : chartRing κ t,
      (∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t), y ∉ Q) ∧
        (y : K) * f ∈ chartRing κ t := by
  let D : Ideal (chartRing κ t) :=
    { carrier := {y | (y : K) * f ∈ chartRing κ t}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, AddMemClass.coe_add, add_mul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {y} hy ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MulMemClass.coe_mul, mul_assoc] at hy ⊢
        exact mul_mem c.2 hy }
  have hnot : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
      ¬D ≤ Q := by
    intro Q hQ hle
    have h := isPrime_ne_bot_of_mem hQ
    have hfm := hf _ (ord_placeOf_t_pos hQ)
    rw [placeOf_eq h] at hfm
    obtain ⟨a, s, hs, hfa⟩ := hfm
    have hs0 : (s : K) ≠ 0 := fun h0 ↦ hs (by
      rw [show s = 0 from Subtype.ext h0]; exact Q.zero_mem)
    apply hs
    apply hle
    change (s : K) * f ∈ chartRing κ t
    have : (s : K) * f = a := by
      rw [hfa, show algebraMap (chartRing κ t) K a = (a : K) from rfl,
        show algebraMap (chartRing κ t) K s = (s : K) from rfl, mul_comm (a : K), ← mul_assoc,
        mul_inv_cancel₀ hs0, one_mul]
    rw [this]; exact a.2
  by_contra hcon
  have hsub : (D : Set (chartRing κ t)) ⊆
      ⋃ Q ∈ (IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t) :
        Set (Ideal (chartRing κ t))), ((fun Q : Ideal (chartRing κ t) ↦ Q) Q : Set _) := by
    intro y hy
    by_contra hy'
    simp only [Set.mem_iUnion, not_exists] at hy'
    exact hcon ⟨y, fun Q hQ hyQ ↦ hy' Q hQ hyQ, hy⟩
  obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime ⊤ ⊤
    (fun Q hQ _ _ ↦ (isPrime_ne_bot_of_mem hQ).1)).mp hsub
  exact hnot Q hQ hle

/-- **Value of the norm**: if `f` has neither zero nor pole at the zeros of `t`, then
`N(f)(P₀) = ∏_{t(P) = 0} f(P)^{ord_P t}` for every zero `P₀` of `t`. -/
theorem val_norm_adjoin {f : K} (hf : f ≠ 0) (hu : ∀ P : Place κ K, 0 < P.ord t → P.ord f = 0)
    {P₀ : Place κ K} (hP₀ : 0 < P₀.ord t) :
    Place.val P₀ (algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ f)) =
      ∏ P ∈ (Place.finite_setOf_ord_pos (k := κ) t).toFinset,
        Place.val P f ^ (P.ord t).toNat := by
  obtain ⟨y, hyQ, hyf⟩ := exists_mul_mem_chart (fun P hP ↦ P.mem_of_ord_nonneg (hu P hP).ge)
  set x : chartRing κ t := ⟨(y : K) * f, hyf⟩ with hx
  have hQ₀ := toChart_mem hP₀
  have hP₀' := placeOf_toChart hP₀
  set Q₀ := (P₀.toChart t (P₀.mem_of_ord_nonneg hP₀.le)).asIdeal
  have hvy : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
      Place.val (placeOf κ t Q) (y : K) ≠ 0 := by
    intro Q hQ h0
    have := sub_val_mem (isPrime_ne_bot_of_mem hQ) y
    rw [h0, show cS (t := t) (0 : κ) = 0 by simp [cS], sub_zero] at this
    exact hyQ Q hQ this
  -- the norm of `f` is a unit at `P₀`
  have hordf : P₀.ord (algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ f)) = 0 := by
    rw [ord_norm_adjoin hf hP₀,
      Finset.sum_eq_zero (fun P hP ↦ hu P
        ((Set.Finite.mem_toFinset (Place.finite_setOf_ord_pos (k := κ) t)).mp hP)), mul_zero]
  have hNy := val_norm_chart hQ₀ y
  have hNx := val_norm_chart hQ₀ x
  rw [hP₀'] at hNy hNx
  have hmul : algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ (x : K)) =
      algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ (y : K)) *
        algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ f) := by
    rw [← map_mul, ← map_mul]
  rw [← algebraMap_norm_chart] at hNy
  rw [← algebraMap_norm_chart] at hNx
  have hymem : algebraMap κ⟮t⟯ K (Algebra.norm κ⟮t⟯ (y : K)) ∈ P₀.1 := by
    rw [algebraMap_norm_chart, ← hP₀']
    exact mem_placeOf (isPrime_ne_bot_of_mem hQ₀)
      (algebraMap (Algebra.adjoin κ {t}) (chartRing κ t) _)
  have hfmem := Place.mem_of_ord_eq_zero P₀ hordf
  rw [hmul, Place.val_mul P₀ hymem hfmem, hNy] at hNx
  have hprod : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
      Place.val (placeOf κ t Q) (x : K) =
        Place.val (placeOf κ t Q) (y : K) * Place.val (placeOf κ t Q) f := by
    intro Q hQ
    have hP := ord_placeOf_t_pos hQ
    exact Place.val_mul _ (mem_placeOf (isPrime_ne_bot_of_mem hQ) y)
      (Place.mem_of_ord_eq_zero _ (hu _ hP))
  have hxprod : ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
      Place.val (placeOf κ t Q) (x : K) ^ Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q =
      (∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
        Place.val (placeOf κ t Q) (y : K) ^ Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q) *
      ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
        Place.val (placeOf κ t Q) f ^ Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q hQ ↦ by rw [hprod Q hQ, mul_pow]
  rw [hxprod] at hNx
  have hne : ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {tR κ t}) (chartRing κ t),
      Place.val (placeOf κ t Q) (y : K) ^ Ideal.ramificationIdx' (Ideal.span {tR κ t}) Q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun Q hQ ↦ pow_ne_zero _ (hvy Q hQ)
  rw [mul_left_cancel₀ hne hNx, prod_zeros_eq]
  refine Finset.prod_congr rfl fun Q hQ ↦ ?_
  rw [ord_placeOf_t hQ, Int.toNat_natCast]

end FieldNorm

/-- **Order of the norm** `N = N_{K/E}`, `E = κ(t)`: for a zero `P₀` of `t`,
`ord_{P₀} N(f) = ord_{P₀}(t) · ∑_{t(P) = 0} ord_P f` (all residue degrees are `1`). -/
theorem ord_norm {t : K} (ht : Transcendental κ t) {E : IntermediateField κ K} (hE : κ⟮t⟯ = E)
    {f : K} (hf : f ≠ 0) {P₀ : Place κ K} (hP₀ : 0 < P₀.ord t) :
    P₀.ord (algebraMap E K (Algebra.norm E f)) =
      P₀.ord t * ∑ P ∈ (Place.finite_setOf_ord_pos (k := κ) t).toFinset, P.ord f := by
  subst hE
  haveI : Fact (Transcendental κ t) := ⟨ht⟩
  exact ord_norm_adjoin hf hP₀

/-- **Value of the norm** `N = N_{K/E}`, `E = κ(t)`: if `f` has neither zero nor pole at the zeros
of `t`, then `N(f)(P₀) = ∏_{t(P) = 0} f(P)^{ord_P t}` for every zero `P₀` of `t`. -/
theorem val_norm {t : K} (ht : Transcendental κ t) {E : IntermediateField κ K} (hE : κ⟮t⟯ = E)
    {f : K} (hf : f ≠ 0) (hu : ∀ P : Place κ K, 0 < P.ord t → P.ord f = 0)
    {P₀ : Place κ K} (hP₀ : 0 < P₀.ord t) :
    Place.val P₀ (algebraMap E K (Algebra.norm E f)) =
      ∏ P ∈ (Place.finite_setOf_ord_pos (k := κ) t).toFinset,
        Place.val P f ^ (P.ord t).toNat := by
  subst hE
  haveI : Fact (Transcendental κ t) := ⟨ht⟩
  exact val_norm_adjoin hf hu hP₀

/-! ### Values and orders of polynomials in a function -/

section Poly

variable (P : Place κ K) {g : K}

theorem aeval_mem (hg : g ∈ P.1) (q : κ[X]) : aeval g q ∈ P.1 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact mul_mem (P.algebraMap_mem a) (pow_mem hg n)

theorem val_aeval (hg : g ∈ P.1) (q : κ[X]) :
    Place.val P (aeval g q) = eval (Place.val P g) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Place.val_add P (aeval_mem P hg p) (aeval_mem P hg q), hp, hq, eval_add]
  | monomial n a =>
    rw [aeval_monomial, Place.val_mul P (P.algebraMap_mem a) (pow_mem hg n), Place.val_algebraMap,
      Place.val_pow P hg, eval_monomial]

theorem ord_aeval_eq_zero (hg : g ∈ P.1) {q : κ[X]} (hq : eval (Place.val P g) q ≠ 0) :
    P.ord (aeval g q) = 0 := by
  have hv : Place.val P (aeval g q) ≠ 0 := by rwa [val_aeval P hg]
  have hmem := aeval_mem P hg q
  have hne : aeval g q ≠ 0 := fun h ↦ hv (by rw [h, Place.val_zero])
  have h0 := P.ord_nonneg_of_mem hmem
  by_contra hne'
  exact hv ((Place.val_eq_zero_iff P hmem).mpr (Or.inr (lt_of_le_of_ne h0 (Ne.symm hne'))))

theorem aeval_ne_zero (hgt : Transcendental κ g) {q : κ[X]} (hq : q ≠ 0) : aeval g q ≠ 0 :=
  fun h ↦ hgt ⟨q, hq, h⟩

/-- `ord_P q(g) = mult_{g(P)}(q) · ord_P (g - g(P))`. -/
theorem ord_aeval (hgt : Transcendental κ g) (hg : g ∈ P.1) {q : κ[X]} (hq : q ≠ 0) :
    P.ord (aeval g q) = rootMultiplicity (Place.val P g) q *
      P.ord (g - algebraMap κ K (Place.val P g)) := by
  set a := Place.val P g
  have hga : g - algebraMap κ K a ≠ 0 := aeval_ne_zero (q := X - C a) hgt (X_sub_C_ne_zero a)
    |> fun h ↦ by simpa using h
  conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq q a]
  have h1 : eval a (q /ₘ (X - C a) ^ rootMultiplicity a q) ≠ 0 :=
    eval_divByMonic_pow_rootMultiplicity_ne_zero a hq
  have h2 : aeval g (q /ₘ (X - C a) ^ rootMultiplicity a q) ≠ 0 := by
    refine aeval_ne_zero hgt fun h ↦ h1 ?_
    rw [h, eval_zero]
  rw [map_mul, map_pow, P.ord_mul (pow_ne_zero _ (by simpa using hga)) h2,
    ord_aeval_eq_zero P hg h1, add_zero, Place.ord_pow]
  simp

theorem aeval_eq_pow_mul_reverse (hg : g ≠ 0) (q : κ[X]) :
    aeval g q = g ^ q.natDegree * aeval g⁻¹ q.reverse := by
  letI := invertibleOfNonzero hg
  have h := eval₂_reverse_mul_pow (algebraMap κ K) g q
  rw [invOf_eq_inv] at h
  rw [aeval_def, aeval_def, ← h, mul_comm]

end Poly

/-! ### Regrouping `f(div g)` and `g(div f)` -/

section Regroup

theorem zpow_sum₀ {ι : Type*} {a : κ} (ha : a ≠ 0) (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, a ^ n i = a ^ ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]

/-- `f(div g) = (∏_{g(P) = 0} f(P)^{ord_P g}) / ∏_{g(P) = ∞} f(P)^{-ord_P g}`. -/
theorem evalDiv_div_eq (f g : K) :
    evalDiv f (Divisor.div κ g) =
      (∏ P ∈ (Place.finite_setOf_ord_pos (k := κ) g).toFinset,
        Place.val P f ^ (P.ord g).toNat) /
      ∏ P ∈ (Place.finite_setOf_ord_pos (k := κ) g⁻¹).toFinset,
        Place.val P f ^ (P.ord g⁻¹).toNat := by
  classical
  have hsupp : (Divisor.div κ g).support = (Place.finite_setOf_ord_pos (k := κ) g).toFinset ∪
      (Place.finite_setOf_ord_pos (k := κ) g⁻¹).toFinset := by
    ext P
    simp only [Finsupp.mem_support_iff, Divisor.div_apply, Finset.mem_union,
      Set.Finite.mem_toFinset, Set.mem_setOf_eq, Place.ord_inv]
    omega
  have hdisj : Disjoint (Place.finite_setOf_ord_pos (k := κ) g).toFinset
      (Place.finite_setOf_ord_pos (k := κ) g⁻¹).toFinset := by
    rw [Finset.disjoint_left]
    intro P h1 h2
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Place.ord_inv] at h1 h2
    omega
  rw [evalDiv, Finsupp.prod, hsupp, Finset.prod_union hdisj, div_eq_mul_inv,
    ← Finset.prod_inv_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun P hP ↦ ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
    rw [Divisor.div_apply, ← zpow_natCast, Int.toNat_of_nonneg hP.le]
  · refine Finset.prod_congr rfl fun P hP ↦ ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
    rw [Divisor.div_apply, ← zpow_natCast, Int.toNat_of_nonneg hP.le, Place.ord_inv, zpow_neg,
      inv_inv]

/-- `g(div f) = ∏_a a^{∑_{g(P) = a} ord_P f}`, for a finite set `T ∌ 0` of values containing the
values of `g` on the support of `div f`. -/
theorem evalDiv_eq_prod_fiber {f g : K} (hgt : Transcendental κ g)
    (h : ∀ P : Place κ K, P.ord f = 0 ∨ P.ord g = 0) (T : Finset κ)
    (hT : ∀ P : Place κ K, P.ord f ≠ 0 → Place.val P g ∈ T) (hT0 : (0 : κ) ∉ T) :
    evalDiv g (Divisor.div κ f) = ∏ a ∈ T, a ^ ∑ P ∈ (Place.finite_setOf_ord_pos (k := κ)
      (g - algebraMap κ K a)).toFinset, P.ord f := by
  classical
  rw [evalDiv, Finsupp.prod, ← Finset.prod_fiberwise_of_maps_to (g := fun P ↦ Place.val P g)
    (t := T) (fun P hP ↦ hT P (by simpa using hP))]
  refine Finset.prod_congr rfl fun a ha ↦ ?_
  have ha0 : a ≠ 0 := fun h0 ↦ hT0 (h0 ▸ ha)
  rw [Finset.prod_congr rfl (g := fun P ↦ a ^ (Divisor.div κ f) P) fun P hP ↦ by
    rw [(Finset.mem_filter.mp hP).2], zpow_sum₀ ha0]
  congr 1
  have hga : ∀ P : Place κ K, g ∈ P.1 → (Place.val P g = a ↔
      0 < P.ord (g - algebraMap κ K a)) := by
    intro P hg
    rw [Place.val_eq_iff P hg]
    have hne : g - algebraMap κ K a ≠ 0 := by
      intro h0
      exact transcendental_sub_algebraMap hgt a (by rw [h0]; exact isAlgebraic_zero)
    simp [hne]
  refine Finset.sum_subset (fun P hP ↦ ?_) (fun P hP hP' ↦ ?_)
  · obtain ⟨hP1, hP2⟩ := Finset.mem_filter.mp hP
    have hf0 : P.ord f ≠ 0 := by simpa using hP1
    have hg0 : P.ord g = 0 := (h P).resolve_left hf0
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      ← hga P (Place.mem_of_ord_eq_zero P hg0)]
    exact hP2
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
    by_contra hf0
    apply hP'
    have hg0 : P.ord g = 0 := (h P).resolve_left hf0
    refine Finset.mem_filter.mpr ⟨by simpa using hf0, ?_⟩
    exact (hga P (Place.mem_of_ord_eq_zero P hg0)).mpr hP

end Regroup

/-! ### Weil reciprocity -/

/-- Weil reciprocity when `g` is transcendental. -/
theorem weil_reciprocity_of_transcendental {f g : K} (hf : f ≠ 0) (hgt : Transcendental κ g)
    (h : ∀ P : Place κ K, P.ord f = 0 ∨ P.ord g = 0) :
    evalDiv f (Divisor.div κ g) = evalDiv g (Divisor.div κ f) := by
  classical
  haveI : Fact (Transcendental κ g) := ⟨hgt⟩
  have hg0 : g ≠ 0 := ne_zero_of_transcendental hgt
  set N := algebraMap κ⟮g⟯ K (Algebra.norm κ⟮g⟯ f) with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, map_eq_zero_iff _ (algebraMap κ⟮g⟯ K).injective]
    exact Algebra.norm_ne_zero_iff.mpr hf
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff κ N).mp
    (Algebra.norm κ⟮g⟯ f).2
  have hs0 : s ≠ 0 := by
    rintro rfl; apply hN0; rw [hrs, map_zero, div_zero]
  -- reduce `N = r(g) / s(g)` to lowest terms
  set d := GCDMonoid.gcd r s
  have hd0 : d ≠ 0 := fun h0 ↦ hs0 ((_root_.gcd_eq_zero_iff r s).mp h0).2
  set r' := r / d
  set s' := s / d
  have hcop : IsCoprime r' s' := isCoprime_div_gcd_div_gcd hs0
  have hr : r = d * r' :=
    (EuclideanDomain.mul_div_cancel' hd0 (GCDMonoid.gcd_dvd_left r s)).symm
  have hs : s = d * s' :=
    (EuclideanDomain.mul_div_cancel' hd0 (GCDMonoid.gcd_dvd_right r s)).symm
  have hs'0 : s' ≠ 0 := by rintro h0; rw [h0, mul_zero] at hs; exact hs0 hs
  have hNrs : N = aeval g r' / aeval g s' := by
    rw [hrs, hr, hs, map_mul, map_mul, mul_div_mul_left _ _ (aeval_ne_zero hgt hd0)]
  have hr'0 : r' ≠ 0 := by
    rintro h0; apply hN0; rw [hNrs, h0, map_zero, zero_div]
  -- order of `N` at the places over `a ∈ κ`
  have F1 : ∀ a : κ, ∀ P₀ : Place κ K, 0 < P₀.ord (g - algebraMap κ K a) →
      ((rootMultiplicity a r' : ℤ) - rootMultiplicity a s') =
        ∑ P ∈ (Place.finite_setOf_ord_pos (k := κ) (g - algebraMap κ K a)).toFinset,
          P.ord f := by
    intro a P₀ hP₀
    have hgmem : g ∈ P₀.1 := by
      have := add_mem (P₀.mem_of_ord_nonneg hP₀.le) (P₀.algebraMap_mem a)
      simpa using this
    have hval : Place.val P₀ g = a := (Place.val_eq_iff P₀ hgmem a).mpr (Or.inr hP₀)
    have h1 := ord_norm (transcendental_sub_algebraMap hgt a) (adjoin_sub_algebraMap_eq g a) hf hP₀
    rw [← hN, hNrs, P₀.ord_div (aeval_ne_zero hgt hr'0) (aeval_ne_zero hgt hs'0),
      ord_aeval P₀ hgt hgmem hr'0, ord_aeval P₀ hgt hgmem hs'0, hval] at h1
    apply mul_right_cancel₀ hP₀.ne'
    rw [sub_mul, h1, mul_comm]
  -- `N` has neither zero nor pole at `0`
  obtain ⟨P₀, hP₀⟩ := Place.exists_ord_pos hgt
  have hP₀' : 0 < P₀.ord (g - algebraMap κ K 0) := by simpa using hP₀
  have hm0 : rootMultiplicity 0 r' = rootMultiplicity 0 s' := by
    have h1 := F1 0 P₀ hP₀'
    rw [Finset.sum_eq_zero (fun P hP ↦ (h P).resolve_right (by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, sub_zero] at hP
      exact hP.ne'))] at h1
    omega
  have hnot : ¬(eval 0 r' = 0 ∧ eval 0 s' = 0) := by
    rintro ⟨h1, h2⟩
    obtain ⟨u, v, huv⟩ := hcop
    have := congrArg (eval 0) huv
    simp [h1, h2] at this
  have hr0 : eval 0 r' ≠ 0 := by
    intro h1
    have hpos : 0 < rootMultiplicity 0 r' := (rootMultiplicity_pos hr'0).mpr h1
    rw [hm0] at hpos
    exact hnot ⟨h1, (rootMultiplicity_pos hs'0).mp hpos⟩
  have hs0' : eval 0 s' ≠ 0 := by
    intro h2
    have hpos : 0 < rootMultiplicity 0 s' := (rootMultiplicity_pos hs'0).mpr h2
    rw [← hm0] at hpos
    exact hnot ⟨(rootMultiplicity_pos hr'0).mp hpos, h2⟩
  -- `N` has neither zero nor pole at `∞`
  obtain ⟨P₁, hP₁⟩ := Place.exists_ord_neg hgt
  have hP₁' : 0 < P₁.ord g⁻¹ := by rw [Place.ord_inv]; omega
  have hginv : g⁻¹ ∈ P₁.1 := P₁.mem_of_ord_nonneg hP₁'.le
  have hvinv : Place.val P₁ g⁻¹ = 0 := (Place.val_eq_zero_iff P₁ hginv).mpr (Or.inr hP₁')
  have hrev : ∀ q : κ[X], q ≠ 0 → eval (Place.val P₁ g⁻¹) q.reverse ≠ 0 := by
    intro q hq
    rw [hvinv, ← coeff_zero_eq_eval_zero, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hq
  have hrev0 : ∀ q : κ[X], q ≠ 0 → aeval g⁻¹ q.reverse ≠ 0 := by
    intro q hq h0
    have := val_aeval P₁ hginv q.reverse
    rw [h0, Place.val_zero] at this
    exact hrev q hq this.symm
  have hord : ∀ q : κ[X], q ≠ 0 → P₁.ord (aeval g q) = q.natDegree * P₁.ord g := by
    intro q hq
    rw [aeval_eq_pow_mul_reverse hg0, P₁.ord_mul (pow_ne_zero _ hg0) (hrev0 q hq), Place.ord_pow,
      ord_aeval_eq_zero P₁ hginv (hrev q hq), add_zero]
  have hdeg : r'.natDegree = s'.natDegree := by
    have h1 := ord_norm (transcendental_inv hgt) (adjoin_inv_eq g) hf hP₁'
    rw [Finset.sum_eq_zero (fun P hP ↦ (h P).resolve_right (by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Place.ord_inv] at hP
      omega)), mul_zero, ← hN, hNrs, P₁.ord_div (aeval_ne_zero hgt hr'0) (aeval_ne_zero hgt hs'0),
      hord r' hr'0, hord s' hs'0, ← sub_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · omega
    · omega
  -- the left-hand side: `f(div g) = N(0) / N(∞)`
  have hgmem : g ∈ P₀.1 := P₀.mem_of_ord_nonneg hP₀.le
  have hv0 : Place.val P₀ g = 0 := (Place.val_eq_zero_iff P₀ hgmem).mpr (Or.inr hP₀)
  have hLHS : evalDiv f (Divisor.div κ g) =
      (eval 0 r' / eval 0 s') / (r'.leadingCoeff / s'.leadingCoeff) := by
    rw [evalDiv_div_eq]
    congr 1
    · rw [← val_norm hgt rfl hf (fun P hP ↦ (h P).resolve_right hP.ne') hP₀, ← hN, hNrs,
        Place.val_div P₀ (aeval_ne_zero hgt hs'0) (ord_aeval_eq_zero P₀ hgmem (by rwa [hv0]))
          (ord_aeval_eq_zero P₀ hgmem (by rwa [hv0])), val_aeval P₀ hgmem, val_aeval P₀ hgmem,
        hv0]
    · rw [← val_norm (transcendental_inv hgt) (adjoin_inv_eq g) hf (fun P hP ↦ (h P).resolve_right
        (by rw [Place.ord_inv] at hP; omega)) hP₁', ← hN, hNrs, aeval_eq_pow_mul_reverse hg0 r',
        aeval_eq_pow_mul_reverse hg0 s', hdeg, mul_div_mul_left _ _ (pow_ne_zero _ hg0),
        Place.val_div P₁ (hrev0 s' hs'0) (ord_aeval_eq_zero P₁ hginv (hrev r' hr'0))
          (ord_aeval_eq_zero P₁ hginv (hrev s' hs'0)), val_aeval P₁ hginv, val_aeval P₁ hginv,
        hvinv, ← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, coeff_zero_reverse,
        coeff_zero_reverse]
  -- the right-hand side: `g(div f) = ∏ roots r' / ∏ roots s'`
  set T : Finset κ := r'.roots.toFinset ∪ s'.roots.toFinset ∪
    (Divisor.div κ f).support.image fun P ↦ Place.val P g
  have hT : ∀ P : Place κ K, P.ord f ≠ 0 → Place.val P g ∈ T := fun P hP ↦
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simpa using hP))
  have hT0 : (0 : κ) ∉ T := by
    simp only [T, Finset.mem_union, Multiset.mem_toFinset, mem_roots hr'0, mem_roots hs'0,
      IsRoot.def, Finset.mem_image, Finsupp.mem_support_iff, Divisor.div_apply, not_or,
      not_exists, not_and]
    refine ⟨⟨hr0, hs0'⟩, fun P hP hv ↦ ?_⟩
    exact Place.val_ne_zero P hg0 ((h P).resolve_left hP) hv
  have hTne : ∀ a ∈ T, a ≠ 0 := fun a ha h0 ↦ hT0 (h0 ▸ ha)
  have hprod : ∀ q : κ[X], q ≠ 0 → q.roots.toFinset ⊆ T →
      ∏ a ∈ T, a ^ rootMultiplicity a q = q.roots.prod := by
    intro q hq hsub
    rw [Finset.prod_multiset_count, ← Finset.prod_subset hsub]
    · exact Finset.prod_congr rfl fun a _ ↦ by rw [count_roots]
    · intro a _ ha
      rw [rootMultiplicity_eq_zero (fun hroot ↦ ha (Multiset.mem_toFinset.mpr
        ((mem_roots hq).mpr hroot))), pow_zero]
  have hRHS : evalDiv g (Divisor.div κ f) = r'.roots.prod / s'.roots.prod := by
    rw [evalDiv_eq_prod_fiber hgt h T hT hT0]
    rw [Finset.prod_congr rfl fun a _ ↦ by
      obtain ⟨Pa, hPa⟩ := Place.exists_ord_pos (transcendental_sub_algebraMap hgt a)
      rw [← F1 a Pa hPa]]
    rw [Finset.prod_congr rfl fun a ha ↦ zpow_sub₀ (hTne a ha) _ _, Finset.prod_div_distrib]
    simp only [zpow_natCast]
    rw [hprod r' hr'0 (fun a ha ↦ by simp [T, ha]), hprod s' hs'0 (fun a ha ↦ by simp [T, ha])]
  rw [hLHS, hRHS, ← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero,
    (IsAlgClosed.splits r').coeff_zero_eq_leadingCoeff_mul_prod_roots,
    (IsAlgClosed.splits s').coeff_zero_eq_leadingCoeff_mul_prod_roots, hdeg]
  have hlr : r'.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hr'0
  have hls : s'.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hs'0
  have hps : s'.roots.prod ≠ 0 := by
    intro h0
    apply hs0'
    rw [← coeff_zero_eq_eval_zero,
      (IsAlgClosed.splits s').coeff_zero_eq_leadingCoeff_mul_prod_roots, h0, mul_zero]
  field_simp

end WeilReciprocity

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

open WeilReciprocity in
/-- **Weil reciprocity** (Sutherland, *Elliptic curves*, Lecture 24, Theorem 24.20; Silverman,
*The Arithmetic of Elliptic Curves*, Exercise 2.11): for nonzero functions `f, g` on a curve over
an algebraically closed field whose divisors have disjoint supports, `f(div g) = g(div f)`. -/
theorem weil_reciprocity {f g : K} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ P : Place κ K, P.ord f = 0 ∨ P.ord g = 0) :
    evalDiv f (Divisor.div κ g) = evalDiv g (Divisor.div κ f) := by
  by_cases hgt : Transcendental κ g
  · exact weil_reciprocity_of_transcendental hf hgt h
  have hga : IsAlgebraic κ g := by
    by_contra hc
    exact hgt hc
  -- a constant `g` lies in `κ`
  obtain ⟨c, rfl⟩ : ∃ c : κ, algebraMap κ K c = g := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Place κ K))
    have hgP : g ∈ P.1 := P.mem_of_isAlgebraic hga
    refine ⟨Place.val P g, ?_⟩
    rcases (Place.val_eq_iff P hgP (Place.val P g)).mp rfl with h0 | hpos
    · exact (sub_eq_zero.mp h0).symm
    · rw [P.ord_eq_zero_of_isAlgebraic (hga.sub (isAlgebraic_algebraMap _))] at hpos
      exact absurd hpos (lt_irrefl 0)
  have hc0 : c ≠ 0 := fun h0 ↦ hg (by rw [h0, map_zero])
  rw [Divisor.div_eq_zero_of_isAlgebraic hga, evalDiv_zero, evalDiv_algebraMap hc0,
    Divisor.deg_div, zpow_zero]

end CurvesJacobian
