/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.PlaceAut
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Automorphisms fixing a place of a curve of positive genus have finite order

Let `K/κ` be a function field of one variable over an algebraically closed field `κ` of
characteristic `0`, of genus `g ≥ 1`, and `σ ∈ Aut_κ(K)` an automorphism fixing a place `P`.
Then **`σ` has finite order** (`CurvesJacobian.LocAn.exists_pow_eq_one_of_fixes`).

Proof. `σ` acts on the finite-dimensional space `L(N P)` (`N = g + 1`, so `ℓ(N P) ≥ 2` by
Riemann–Roch) and on its quotient by the constants; an eigenvector there is a nonconstant `f` with
`σ f = v f + b`, `v, b ∈ κ`.

* If `v` is a root of unity and `v ≠ 1`, or `v = 1` and `b = 0`, then a power of `σ` fixes the
  transcendental `x = f + b/(v - 1)` (resp. `x = f`), so it lies in the finite group
  `Aut(K/κ(x))`, and `σ` has finite order.
* If `v = 1` and `b ≠ 0`, then `x = f/b` satisfies `σ x = x + 1`; if `v` is not a root of unity,
  then `x = f + b/(v - 1)` satisfies `σ x = v x`. In both cases a place ramified over `a ∈ κ`
  (`a ≠ 0` in the second case) is moved by `σⁿ` to a place ramified over `a - n` (resp. `a vⁿ`);
  these are infinitely many ramified places, while the different has finite support
  (`finite_setOf_ramified`). So `x : X → ℙ¹` is unramified outside `0` and `∞`, and the
  Riemann–Hurwitz formula (weil-curves' `genus_belyi`) gives `2g - 2 = -c₀ - c_∞ < 0`
  (`genus_le_zero_of_unramified`), a contradiction.

This is (F2) of the MR7 plan's uniqueness route.
-/

open WeilCurves.FunctionField WeilCurves.FunctionField.Divisor Module
open scoped IntermediateField

namespace CurvesJacobian.LocAn

variable {κ K : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Algebra κ K] [IsFunctionField κ K]

section Ramification

variable [CharZero κ]

omit [IsAlgClosed κ] in
/-- **Finitely many places are ramified for `x : X → ℙ¹`**: the places `Q` with
`ord_Q (x - a) ≥ 2` for some `a ∈ κ` lie in the support of the different of `K / κ(x)`. -/
theorem finite_setOf_ramified {x : K} (hx : Transcendental κ x) :
    {Q : Place κ K | ∃ a : κ, 2 ≤ Q.ord (x - algebraMap κ K a)}.Finite := by
  classical
  set F := κ⟮x⟯
  set t : F := IntermediateField.AdjoinSimple.gen κ x
  have htx : algebraMap F K t = x := rfl
  have ht : Transcendental κ t := by
    rw [← transcendental_algebraMap_iff (algebraMap F K).injective, htx]; exact hx
  have htop : κ⟮t⟯ = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  have hK1 : ∀ a : κ, finrank κ⟮t - algebraMap κ F a⟯ F = 1 := fun a ↦ by
    rw [adjoin_sub_algebraMap_eq, IntermediateField.finrank_eq_one_iff_eq_top]; exact htop
  have hK1' : finrank κ⟮t⟯ F = 1 := by
    rw [IntermediateField.finrank_eq_one_iff_eq_top]; exact htop
  haveI : FiniteDimensional κ⟮t⟯ F := Module.finite_of_finrank_eq_succ hK1'
  haveI : IsFunctionField κ F := ⟨⟨t, ht, inferInstance⟩⟩
  haveI : FiniteDimensional F K := finiteDimensional_adjoin hx
  have hram : ∀ (Q : Place κ K) (a : κ), 0 < Q.ord (x - algebraMap κ K a) →
      ramIndex F Q = Q.ord (x - algebraMap κ K a) := by
    intro Q a hQ
    have hxa : x - algebraMap κ K a = algebraMap F K (t - algebraMap κ F a) := by
      rw [map_sub, htx, ← IsScalarTower.algebraMap_apply]
    rw [hxa, ord_algebraMap_eq_ramIndex_mul] at hQ ⊢
    have he := ramIndex_pos (K := F) Q
    have hpos : 0 < (Q.restrict (K := F)).ord (t - algebraMap κ F a) :=
      pos_of_mul_pos_right hQ he.le
    obtain ⟨h1, -⟩ := ord_eq_one_of_finrank_eq_one (transcendental_sub_algebraMap ht a)
      (hK1 a) hpos
    rw [h1, mul_one]
  refine (different κ F K).support.finite_toSet.subset fun Q ⟨a, ha⟩ ↦ ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff, different_apply_of_charZero,
    hram Q a (by omega)]
  omega

omit [IsAlgClosed κ] in
/-- A place has at most one value: if `x - a` and `x - b` both vanish at `Q`, then `a = b`. -/
theorem eq_of_ord_sub_pos {Q : Place κ K} {x : K} {a b : κ} (ha : 0 < Q.ord (x - algebraMap κ K a))
    (hb : 0 < Q.ord (x - algebraMap κ K b)) : a = b := by
  by_contra hne
  have hc : algebraMap κ K (b - a) ≠ 0 := (map_ne_zero _).2 (sub_ne_zero.2 (Ne.symm hne))
  have e : (x - algebraMap κ K a) + -(x - algebraMap κ K b) = algebraMap κ K (b - a) := by
    rw [map_sub]; ring
  have h := Q.min_le_ord_add (f := x - algebraMap κ K a) (g := -(x - algebraMap κ K b))
    (by rw [e]; exact hc)
  rw [e, Q.ord_algebraMap_base, Place.ord_neg] at h
  omega

omit [IsAlgClosed κ] in
/-- If infinitely many values `a n` (`n ∈ ℕ`, pairwise distinct) are ramification values of `x`,
we get a contradiction. -/
theorem false_of_injective_ramified {x : K} (hx : Transcendental κ x) {a : ℕ → κ}
    (ha : Function.Injective a)
    (hram : ∀ n, ∃ Q : Place κ K, 2 ≤ Q.ord (x - algebraMap κ K (a n))) :
    False := by
  choose Q hQ using hram
  have hQinj : Function.Injective Q := by
    intro m n hmn
    apply ha
    refine eq_of_ord_sub_pos (Q := Q m) (x := x) (by have := hQ m; omega) ?_
    rw [hmn]; have := hQ n; omega
  exact Set.infinite_range_of_injective hQinj
    ((finite_setOf_ramified hx).subset (Set.range_subset_iff.2 fun n ↦ ⟨a n, hQ n⟩))

/-- **Genus of a cover of `ℙ¹` unramified outside `0, ∞`**: if `ord_Q (x - a) ≤ 1` for all places
`Q` and all `a ≠ 0`, then `g ≤ 0`. -/
theorem genus_le_zero_of_unramified {x : K} (hx : Transcendental κ x)
    (hunr : ∀ (Q : Place κ K) (a : κ), a ≠ 0 → Q.ord (x - algebraMap κ K a) ≤ 1) :
    genus κ K ≤ 0 := by
  classical
  have hB := genus_belyi hx fun Q a ha0 _ ↦ hunr Q a ha0
  -- the fibre over `1` has `d` points
  have hx1 : x - 1 = x - algebraMap κ K 1 := by rw [map_one]
  have htr1 : Transcendental κ (x - 1) := by rw [hx1]; exact transcendental_sub_algebraMap hx 1
  have hsum := Place.sum_ord_mul_deg_zeros (x - 1) htr1
  set Z1 := (Place.finite_setOf_ord_pos (k := κ) (x - 1)).toFinset
  have hcard : (Z1.card : ℤ) = finrank κ⟮x⟯ K := by
    have h1 : ∀ Q ∈ Z1, Q.ord (x - 1) * (Q.deg : ℤ) = 1 := by
      intro Q hQ
      have hpos : 0 < Q.ord (x - 1) := by simpa [Z1] using hQ
      have hle := hunr Q 1 one_ne_zero
      rw [← hx1] at hle
      rw [Place.deg_eq_one]
      push_cast
      omega
    rw [Finset.sum_congr rfl h1] at hsum
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    rw [hsum, hx1, adjoin_sub_algebraMap_eq]
  have hc1 : {Q : Place κ K | 0 < Q.ord (x - 1)}.ncard = Z1.card :=
    Set.ncard_eq_toFinset_card _ _
  -- the fibres over `0` and `∞` are nonempty
  obtain ⟨Q0, hQ0⟩ := Place.exists_ord_pos hx
  obtain ⟨Qi, hQi⟩ := Place.exists_ord_neg hx
  have hc0 : 1 ≤ {Q : Place κ K | 0 < Q.ord x}.ncard :=
    (Set.ncard_pos (Place.finite_setOf_ord_pos x)).2 ⟨Q0, hQ0⟩
  have hci : 1 ≤ {Q : Place κ K | Q.ord x < 0}.ncard :=
    (Set.ncard_pos (Place.finite_setOf_ord_neg x)).2 ⟨Qi, hQi⟩
  rw [hc1, hcard] at hB
  have : (2 : ℤ) * genus κ K - 2 ≤ -2 := by
    rw [hB]
    have h0 : (1 : ℤ) ≤ ({Q : Place κ K | 0 < Q.ord x}.ncard : ℤ) := by exact_mod_cast hc0
    have hi : (1 : ℤ) ≤ ({Q : Place κ K | Q.ord x < 0}.ncard : ℤ) := by exact_mod_cast hci
    linarith
  linarith

end Ramification

/-! ### The eigenvector -/

omit [IsFunctionField κ K] in
/-- An element of `K` not in `κ` is transcendental over `κ` (`κ` algebraically closed). -/
theorem transcendental_of_notMem_range {f : K} (hf : f ∉ Set.range (algebraMap κ K)) :
    Transcendental κ f := by
  intro halg
  apply hf
  have hint : IsIntegral κ f := halg.isIntegral
  set A := Algebra.adjoin κ {f}
  haveI : Module.Finite κ A := Algebra.finite_adjoin_simple_of_isIntegral hint
  haveI : IsDomain A := Subalgebra.isDomain A
  haveI : Algebra.IsIntegral κ A := Algebra.IsIntegral.of_finite κ A
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ) (K := A)).2
    ⟨f, Algebra.subset_adjoin rfl⟩
  exact ⟨c, congrArg Subtype.val hc⟩

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma placeMap_mul (σ τ : K ≃ₐ[κ] K) (P : Place κ K) :
    placeMap (σ * τ) P = placeMap σ (placeMap τ P) :=
  Place.ext (SetLike.ext fun x ↦ by
    rw [mem_placeMap, mem_placeMap, mem_placeMap]
    rfl)

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma placeMap_one (P : Place κ K) : placeMap 1 P = P :=
  Place.ext (SetLike.ext fun x ↦ by rw [mem_placeMap]; rfl)

omit [IsAlgClosed κ] [IsFunctionField κ K] in
lemma placeMap_placeMap_inv (σ : K ≃ₐ[κ] K) (Q : Place κ K) :
    placeMap σ (placeMap σ⁻¹ Q) = Q := by
  rw [← placeMap_mul, mul_inv_cancel, placeMap_one]

/-- `ord_{σ Q}(σ x) = ord_Q x`. -/
lemma ord_placeMap_apply (σ : K ≃ₐ[κ] K) (Q : Place κ K) (x : K) :
    (placeMap σ Q).ord (σ x) = Q.ord x :=
  ord_placeTr σ.toRingEquiv (RingEquiv.refl κ) (fun c ↦ σ.commutes c) Q x

/-- `σ` preserves `L(N P)` if it fixes `P`. -/
lemma apply_mem_L_single {σ : K ≃ₐ[κ] K} {P : Place κ K} (hσ : Fixes σ P) {N : ℤ} {h : K}
    (hh : h ∈ L (Finsupp.single P N : Divisor κ K)) :
    σ h ∈ L (Finsupp.single P N : Divisor κ K) := by
  classical
  rcases mem_L.1 hh with h0 | hP
  · rw [h0, map_zero]; exact zero_mem _
  refine mem_L.2 (Or.inr fun Q ↦ ?_)
  set Q' := placeMap σ⁻¹ Q
  have hQ : placeMap σ Q' = Q := placeMap_placeMap_inv σ Q
  have hiff : Q' = P ↔ Q = P := by
    constructor
    · rintro h; rw [← hQ, h]; exact hσ
    · rintro rfl; exact hσ.inv
  have := hP Q'
  have e : Q.ord (σ h) = Q'.ord h := by rw [← ord_placeMap_apply σ Q' h, hQ]
  have hD : (Finsupp.single P N : Divisor κ K) Q = Finsupp.single P N Q' := by
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hq : Q = P
    · rw [if_pos hq.symm, if_pos (hiff.2 hq).symm]
    · rw [if_neg (Ne.symm hq), if_neg (fun h ↦ hq (hiff.1 h.symm))]
  rw [e, hD]
  exact this

/-- **A nonconstant `f ∈ L(N P)` with `σ f = v f + b`**, if `ℓ(N P) ≥ 2`. -/
theorem exists_eigen_mod_const {P : Place κ K} {N : ℤ} (hN0 : 0 ≤ N)
    (hN : 2 ≤ ell (Finsupp.single P N : Divisor κ K))
    {σ : K ≃ₐ[κ] K} (hσ : Fixes σ P) :
    ∃ f ∈ L (Finsupp.single P N : Divisor κ K), f ∉ Set.range (algebraMap κ K) ∧ ∃ v b : κ,
      v ≠ 0 ∧ σ f = algebraMap κ K v * f + algebraMap κ K b := by
  classical
  set D : Divisor κ K := Finsupp.single P N
  set V := L D
  have hσV : ∀ h ∈ V, σ h ∈ V := fun h hh ↦ apply_mem_L_single hσ hh
  -- `σ` as a linear endomorphism of `V`
  let φ : V →ₗ[κ] V :=
    { toFun := fun h ↦ ⟨σ h, hσV h h.2⟩
      map_add' := fun a b ↦ Subtype.ext (map_add σ (a : K) b)
      map_smul' := fun c a ↦ Subtype.ext (by
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, map_mul,
          AlgEquiv.commutes]) }
  -- the constants
  have hconst : ∀ c : κ, algebraMap κ K c ∈ V := by
    intro c
    refine mem_L.2 ?_
    by_cases hc : algebraMap κ K c = 0
    · exact Or.inl hc
    refine Or.inr fun Q ↦ ?_
    rw [Q.ord_algebraMap_base]
    simp only [D, Finsupp.single_apply]
    split_ifs <;> omega
  let C : Submodule κ V := Submodule.span κ {⟨1, by simpa using hconst 1⟩}
  have hφC : C ≤ C.comap φ := by
    rw [Submodule.span_le]
    rintro _ rfl
    exact Submodule.subset_span (Subtype.ext (by simp [φ]))
  let ψ := C.mapQ C φ hφC
  -- `ℓ(D) ≥ 2`
  have hell : 2 ≤ finrank κ V := hN
  have hC1 : finrank κ C ≤ 1 := finrank_span_le_card _ |>.trans (by simp)
  haveI : Nontrivial (V ⧸ C) := by
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    have := Submodule.finrank_le C
    rw [htop, finrank_top] at hC1
    omega
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ψ
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective C w
  have hfC : f ∉ C := by
    intro h
    exact hw.2 ((Submodule.Quotient.mk_eq_zero C).2 h)
  have hdiff : φ f - μ • f ∈ C := by
    have := hw.apply_eq_smul
    rw [← Submodule.Quotient.mk_smul, Submodule.mapQ_apply, ← sub_eq_zero,
      ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero] at this
    exact this
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hdiff
  have hfK : (f : K) ∉ Set.range (algebraMap κ K) := by
    rintro ⟨c, hc⟩
    apply hfC
    refine Submodule.mem_span_singleton.2 ⟨c, Subtype.ext ?_⟩
    simp [← hc, Algebra.smul_def]
  refine ⟨f, f.2, hfK, μ, b, ?_, ?_⟩
  · rintro rfl
    have h1 : σ (f : K) = algebraMap κ K b := by
      have := congrArg Subtype.val hb
      simpa [φ, Algebra.smul_def] using this.symm
    apply hfK
    refine ⟨b, ?_⟩
    apply σ.injective
    rw [h1, AlgEquiv.commutes]
  · have := congrArg Subtype.val hb
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sub,
      SetLike.val_smul, Algebra.smul_def, mul_one] at this
    rw [eq_sub_iff_add_eq] at this
    rw [← this]
    ring

/-- Riemann–Roch: `ℓ(N P) ≥ 2` for `N = g + 1`. -/
theorem two_le_ell_single (P : Place κ K) :
    2 ≤ ell (Finsupp.single P (genus κ K + 1) : Divisor κ K) := by
  have hRR := riemannRoch (Finsupp.single P (genus κ K + 1) : Divisor κ K)
  have hdeg : Divisor.deg (Finsupp.single P (genus κ K + 1) : Divisor κ K) = genus κ K + 1 := by
    simp only [Divisor.deg_single, Place.deg_eq_one, Nat.cast_one, mul_one]
  have : (0 : ℤ) ≤ (ell (canonical κ K - Finsupp.single P (genus κ K + 1)) : ℤ) :=
    Nat.cast_nonneg _
  have h2 : (2 : ℤ) ≤ ell (Finsupp.single P (genus κ K + 1) : Divisor κ K) := by
    rw [hdeg] at hRR; omega
  exact_mod_cast h2

/-! ### Finite order -/

omit [IsAlgClosed κ] in
/-- If `σⁿ` fixes a transcendental element, then `σ` has finite order. -/
theorem exists_pow_eq_one_of_pow_apply_eq {σ : K ≃ₐ[κ] K} {x : K} (hx : Transcendental κ x)
    {n : ℕ} (hn : 0 < n) (hσx : (σ ^ n) x = x) : ∃ m, 0 < m ∧ σ ^ m = 1 := by
  set H : Subgroup (K ≃ₐ[κ] K) := Subgroup.zpowers (σ ^ n)
  have hxH : x ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
    clear hτ
    have hinv : ((σ ^ n)⁻¹) x = x := by
      conv_lhs => rw [← hσx]
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσx, ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]
  have hle : κ⟮x⟯ ≤ IntermediateField.fixedField H :=
    IntermediateField.adjoin_simple_le_iff.2 hxH
  haveI : FiniteDimensional κ⟮x⟯ K := finiteDimensional_adjoin hx
  let τ : K ≃ₐ[κ⟮x⟯] K :=
    { (σ ^ n).toRingEquiv with
      commutes' := fun r ↦ by
        have := (IntermediateField.mem_fixedField_iff H _).1 (hle r.2) (σ ^ n)
          (Subgroup.mem_zpowers _)
        exact this }
  obtain ⟨N, hN, hτN⟩ := (isOfFinOrder_of_finite τ).exists_pow_eq_one
  have key : ∀ M : ℕ, ∀ y, (τ ^ M) y = ((σ ^ n) ^ M) y := by
    intro M
    induction M with
    | zero => intro y; rfl
    | succ M ih =>
      intro y
      rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]
      rfl
  refine ⟨n * N, Nat.mul_pos hn hN, ?_⟩
  ext y
  rw [pow_mul, ← key, hτN]
  rfl

variable [CharZero κ]

/-- **An automorphism fixing a place of a curve of genus `≥ 1` has finite order.** -/
theorem exists_pow_eq_one_of_fixes (hg : 1 ≤ genus κ K) {σ : K ≃ₐ[κ] K} {P : Place κ K}
    (hσ : Fixes σ P) : ∃ m, 0 < m ∧ σ ^ m = 1 := by
  obtain ⟨f, -, hf, v, b, hv, hσf⟩ := exists_eigen_mod_const (by omega) (two_le_ell_single P) hσ
  have hft : Transcendental κ f := transcendental_of_notMem_range hf
  by_cases hroot : ∃ n, 0 < n ∧ v ^ n = 1
  · obtain ⟨n, hn, hvn⟩ := hroot
    by_cases hv1 : v = 1
    · subst hv1
      by_cases hb : b = 0
      · subst hb
        refine exists_pow_eq_one_of_pow_apply_eq hft (n := 1) one_pos ?_
        simpa using hσf
      · -- translation: `x = f / b`, `σ x = x + 1`
        exfalso
        set x := algebraMap κ K b⁻¹ * f
        have hbK : algebraMap κ K b ≠ 0 := (map_ne_zero _).2 hb
        have hσx : ∀ m : ℕ, (σ ^ m) x = x + (m : K) := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, map_natCast, map_mul,
              AlgEquiv.commutes, hσf, map_one, one_mul]
            simp only [x, map_inv₀]
            field_simp
            push_cast
            ring
        have hxt : Transcendental κ x := by
          intro h
          apply hft
          have : f = algebraMap κ K b * x := by
            simp only [x, map_inv₀]; field_simp
          rw [this]
          exact (isAlgebraic_algebraMap b).mul h
        refine absurd (genus_le_zero_of_unramified hxt fun Q a _ ↦ ?_) (by omega)
        by_contra hQ
        push Not at hQ
        refine false_of_injective_ramified hxt (a := fun n : ℕ ↦ a - n) (fun m n h ↦ ?_)
          (fun n ↦ ⟨placeMap (σ ^ n) Q, ?_⟩)
        · simpa using h
        · have := ord_placeTr (σ ^ n).toRingEquiv (RingEquiv.refl κ)
            (fun c ↦ (σ ^ n).commutes c) Q (x - algebraMap κ K a)
          change (placeMap (σ ^ n) Q).ord ((σ ^ n) (x - algebraMap κ K a)) = _ at this
          rw [map_sub, hσx, AlgEquiv.commutes] at this
          have e : x + (n : K) - algebraMap κ K a = x - algebraMap κ K (a - n) := by
            rw [map_sub, map_natCast]; ring
          rw [e] at this
          omega
    · -- `v` a nontrivial root of unity: `σⁿ` fixes `x = f + b/(v - 1)`
      have hv1' : (v - 1 : κ) ≠ 0 := sub_ne_zero.2 hv1
      set x := f + algebraMap κ K (b / (v - 1))
      have hσx : σ x = algebraMap κ K v * x := by
        simp only [x, map_add, AlgEquiv.commutes, hσf, map_div₀, map_sub, map_one]
        have : algebraMap κ K v - 1 ≠ 0 := by
          rw [← map_one (algebraMap κ K), ← map_sub]; exact (map_ne_zero _).2 hv1'
        field_simp
        ring
      have hσxn : ∀ m : ℕ, (σ ^ m) x = algebraMap κ K (v ^ m) * x := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, hσx, pow_succ',
            map_mul]
          ring
      have hxt : Transcendental κ x := by
        intro h
        apply hft
        have : f = x - algebraMap κ K (b / (v - 1)) := by simp [x]
        rw [this]
        exact h.sub (isAlgebraic_algebraMap _)
      exact exists_pow_eq_one_of_pow_apply_eq hxt hn (by rw [hσxn, hvn, map_one, one_mul])
  · -- `v` not a root of unity
    exfalso
    push Not at hroot
    have hv1 : v ≠ 1 := fun h ↦ hroot 1 one_pos (by rw [h, pow_one])
    have hv1' : (v - 1 : κ) ≠ 0 := sub_ne_zero.2 hv1
    set x := f + algebraMap κ K (b / (v - 1))
    have hσx : σ x = algebraMap κ K v * x := by
      simp only [x, map_add, AlgEquiv.commutes, hσf, map_div₀, map_sub, map_one]
      have : algebraMap κ K v - 1 ≠ 0 := by
        rw [← map_one (algebraMap κ K), ← map_sub]; exact (map_ne_zero _).2 hv1'
      field_simp
      ring
    have hσxn : ∀ m : ℕ, (σ ^ m) x = algebraMap κ K (v ^ m) * x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, hσx, pow_succ',
          map_mul]
        ring
    have hxt : Transcendental κ x := by
      intro h
      apply hft
      have : f = x - algebraMap κ K (b / (v - 1)) := by simp [x]
      rw [this]
      exact h.sub (isAlgebraic_algebraMap _)
    refine absurd (genus_le_zero_of_unramified hxt fun Q a ha ↦ ?_) (by omega)
    by_contra hQ
    push Not at hQ
    have hvn : ∀ m : ℕ, v ^ m ≠ 0 := fun m ↦ pow_ne_zero m hv
    refine false_of_injective_ramified hxt (a := fun n : ℕ ↦ a / v ^ n) (fun m n h ↦ ?_)
      (fun n ↦ ⟨placeMap (σ ^ n) Q, ?_⟩)
    · simp only at h
      have h2 : v ^ n = v ^ m := by
        rw [div_eq_div_iff (hvn m) (hvn n)] at h
        exact mul_left_cancel₀ ha h
      have hinj : Function.Injective fun k : ℕ ↦ (Units.mk0 v hv) ^ k := by
        rw [injective_pow_iff_not_isOfFinOrder, isOfFinOrder_iff_pow_eq_one]
        rintro ⟨k, hk, hk1⟩
        exact hroot k hk (by simpa [Units.ext_iff] using hk1)
      exact (hinj (Units.ext (by simpa using h2))).symm
    · have := ord_placeTr (σ ^ n).toRingEquiv (RingEquiv.refl κ)
        (fun c ↦ (σ ^ n).commutes c) Q (x - algebraMap κ K a)
      change (placeMap (σ ^ n) Q).ord ((σ ^ n) (x - algebraMap κ K a)) = _ at this
      rw [map_sub, hσxn, AlgEquiv.commutes] at this
      have e : algebraMap κ K (v ^ n) * x - algebraMap κ K a =
          algebraMap κ K (v ^ n) * (x - algebraMap κ K (a / v ^ n)) := by
        rw [map_div₀, mul_sub]
        have : algebraMap κ K (v ^ n) ≠ 0 := (map_ne_zero _).2 (hvn n)
        field_simp
      have hvK : algebraMap κ K (v ^ n) ≠ 0 := (map_ne_zero _).2 (hvn n)
      rw [e] at this
      by_cases h0 : x - algebraMap κ K (a / v ^ n) = 0
      · rw [h0, mul_zero, Place.ord_zero] at this; omega
      · rw [Place.ord_mul _ hvK h0, Place.ord_algebraMap_base, zero_add] at this
        omega

end CurvesJacobian.LocAn
