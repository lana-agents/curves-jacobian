/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Picard

/-!
# `n`-torsion of the divisor class group via Kummer classes

Let `K/k` be a function field of one variable over a perfect field `k` (weil-curves'
`IsFunctionField`) and `n ≥ 1`. A divisor class `[D]` is killed by `n` iff `n • D = div f` for
some `f ∈ Kˣ`; `f` is determined by `[D]` up to `n`-th powers and functions without zeros and
poles. This gives the divisor-level half of the Kummer description of `Pic⁰[n]`
(Milne, *Abelian Varieties*, III.Lemma 9.2: `Hom(π₁(V), ℤ/n) ≅ Pic(V)ₙ`, via the Kummer
extensions `k(V)(f^{1/n})` with `(f) = nD`):

* `CurvesJacobian.kummerClasses k K n`: the units `f` with `div f ∈ n • Div(K)` (written
  additively in `Additive Kˣ`);
* `CurvesJacobian.kummerToPic`: `f ↦ [D]` where `n • D = div f`, onto the `n`-torsion
  `CurvesJacobian.picTorsion k K n` (`kummerToPic_surjective`);
* `CurvesJacobian.ker_kummerToPic`: its kernel consists of `c · gⁿ` with `div c = 0`;
* `CurvesJacobian.picTorsionEquiv`:
  `kummerClasses ⧸ (constants + n-th powers) ≃+ Pic(K)[n]`;
* `CurvesJacobian.deg_eq_zero_of_mem_picTorsion`: `Pic(K)[n] ⊆ Pic⁰(K)`.

Counting `Pic⁰(K k̄)[n]` (`= n^{2g}`) is not done here; see `CJ-plan.md` §10.
-/

open WeilCurves.FunctionField

namespace CurvesJacobian

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]
  (n : ℕ)

/-- The `n`-torsion of the divisor class group. -/
noncomputable def picTorsion : AddSubgroup (Pic k K) := (nsmulAddMonoidHom (α := Pic k K) n).ker

/-- The multiples `n • D` of divisors. -/
noncomputable def nsmulDivisors : AddSubgroup (Divisor k K) :=
  (nsmulAddMonoidHom (α := Divisor k K) n).range

/-- Units whose divisor is divisible by `n` ("unramified Kummer classes"). -/
noncomputable def kummerClasses : AddSubgroup (Additive Kˣ) :=
  (nsmulDivisors k K n).comap (divHom k K)

/-- The constants (units without zeros or poles) plus the `n`-th powers. -/
noncomputable def kummerTrivial : AddSubgroup (Additive Kˣ) :=
  (divHom k K).ker ⊔ (nsmulAddMonoidHom (α := Additive Kˣ) n).range

variable {k K n}

omit [PerfectField k] [IsFunctionField k K] in
lemma nsmul_injective (hn : 0 < n) : Function.Injective (fun D : Divisor k K ↦ n • D) := by
  intro D E h
  ext P
  have := congrArg (fun F : Divisor k K ↦ F P) h
  simp only [Finsupp.smul_apply, nsmul_eq_mul] at this
  exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hn.ne' : (n : ℤ) ≠ 0) this

/-- The divisor `D` with `n • D = div f`, for a Kummer class `f`. -/
noncomputable def kummerDivisor (f : kummerClasses k K n) : Divisor k K :=
  (f.2 : divHom k K f.1 ∈ nsmulDivisors k K n).choose

lemma nsmul_kummerDivisor (f : kummerClasses k K n) :
    n • kummerDivisor f = divHom k K f.1 :=
  (f.2 : divHom k K f.1 ∈ nsmulDivisors k K n).choose_spec

lemma kummerDivisor_eq (hn : 0 < n) (f : kummerClasses k K n) {D : Divisor k K}
    (hD : n • D = divHom k K f.1) : kummerDivisor f = D :=
  nsmul_injective hn ((nsmul_kummerDivisor f).trans hD.symm)

variable (hn : 0 < n)

/-- `f ↦ [D]` with `n • D = div f`, as an additive map to `Pic(K)[n]`. -/
noncomputable def kummerToPic : kummerClasses k K n →+ picTorsion k K n where
  toFun f := ⟨QuotientAddGroup.mk (kummerDivisor f), by
    change n • (QuotientAddGroup.mk (kummerDivisor f) : Pic k K) = 0
    rw [← QuotientAddGroup.mk_nsmul, nsmul_kummerDivisor, QuotientAddGroup.eq_zero_iff]
    exact ⟨_, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    change (QuotientAddGroup.mk (kummerDivisor (0 : kummerClasses k K n)) : Pic k K) = 0
    rw [kummerDivisor_eq hn 0 (D := 0) (by rw [smul_zero]; exact (map_zero _).symm)]
    rfl
  map_add' f g := by
    apply Subtype.ext
    have h : n • (kummerDivisor f + kummerDivisor g) = divHom k K (f + g).1 := by
      rw [smul_add, nsmul_kummerDivisor, nsmul_kummerDivisor, ← map_add]
      rfl
    change (QuotientAddGroup.mk (kummerDivisor (f + g)) : Pic k K) =
      QuotientAddGroup.mk (kummerDivisor f) + QuotientAddGroup.mk (kummerDivisor g)
    rw [kummerDivisor_eq hn (f + g) h, QuotientAddGroup.mk_add]

lemma kummerToPic_apply (f : kummerClasses k K n) :
    (kummerToPic hn f : Pic k K) = QuotientAddGroup.mk (kummerDivisor f) :=
  rfl

/-- Every `n`-torsion class comes from a Kummer class. -/
theorem kummerToPic_surjective : Function.Surjective (kummerToPic (k := k) (K := K) hn) := by
  rintro ⟨c, hc⟩
  obtain ⟨D, hD⟩ := QuotientAddGroup.mk_surjective c
  have hc' := AddMonoidHom.mem_ker.1 hc
  rw [nsmulAddMonoidHom_apply, ← hD, ← QuotientAddGroup.mk_nsmul,
    QuotientAddGroup.eq_zero_iff] at hc'
  obtain ⟨u, hu⟩ := hc'
  have hmem : u ∈ kummerClasses k K n := ⟨D, hu.symm⟩
  refine ⟨⟨u, hmem⟩, Subtype.ext ?_⟩
  rw [kummerToPic_apply, kummerDivisor_eq hn ⟨u, hmem⟩ hu.symm, hD]

/-- **The kernel of `f ↦ [D]`** is (constants) · (`n`-th powers). -/
theorem ker_kummerToPic :
    (kummerToPic (k := k) (K := K) hn).ker =
      (kummerTrivial k K n).comap (kummerClasses k K n).subtype := by
  ext f
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.coe_subtype]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [kummerToPic_apply, ZeroMemClass.coe_zero, QuotientAddGroup.eq_zero_iff] at h'
    obtain ⟨g, hg⟩ := h'
    -- `f - n • g` has trivial divisor
    have hc : f.1 - n • g ∈ (divHom k K).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, map_nsmul, hg, nsmul_kummerDivisor, sub_self]
    have : f.1 = (f.1 - n • g) + n • g := by abel
    rw [kummerTrivial, this]
    exact AddSubgroup.add_mem_sup hc ⟨g, rfl⟩
  · intro h
    obtain ⟨c, hc, _, ⟨g, rfl⟩, hcg⟩ := AddSubgroup.mem_sup.1 h
    apply Subtype.ext
    rw [kummerToPic_apply, ZeroMemClass.coe_zero, QuotientAddGroup.eq_zero_iff]
    refine ⟨g, ?_⟩
    have : divHom k K f.1 = n • divHom k K g := by
      rw [← hcg, map_add, AddMonoidHom.mem_ker.1 hc, zero_add, nsmulAddMonoidHom_apply, map_nsmul]
    exact (kummerDivisor_eq hn f this.symm).symm

/-- **`Pic(K)[n]` via Kummer classes:**
`{f : div f ∈ n • Div} ⧸ (constants · n-th powers) ≃+ Pic(K)[n]`. -/
noncomputable def picTorsionEquiv :
    kummerClasses k K n ⧸ (kummerTrivial k K n).comap (kummerClasses k K n).subtype ≃+
      picTorsion k K n :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_kummerToPic hn).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (kummerToPic_surjective hn))

include hn in
/-- `n`-torsion classes have degree zero. -/
theorem deg_eq_zero_of_mem_picTorsion {c : Pic k K} (hc : c ∈ picTorsion k K n) :
    Pic.deg k K c = 0 := by
  have h : n • Pic.deg k K c = 0 := by
    rw [← map_nsmul,show n • c = 0 from hc, map_zero]
  rw [nsmul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast hn.ne')

end CurvesJacobian
