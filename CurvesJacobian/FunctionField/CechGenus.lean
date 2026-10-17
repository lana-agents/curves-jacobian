/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.TwoCech
import WeilCurves.FunctionField.RiemannRoch

/-!
# The Čech `H¹` of a two-set cover of a function field has dimension `g`

Let `K/k` be a function field (weil-curves) and let `s`, `s'` be disjoint nonempty finite sets of
places. Consider the rings of functions regular outside `s`, outside `s'`, and outside `s ∪ s'`:
`R_U = regularOutside s`, `R_V = regularOutside s'`, `R_{UV} = regularOutside (s ∪ s')`. For a
curve `X` covered by two affine opens `U`, `V` with complements `s`, `s'`, these are the rings
`Γ(U, 𝒪)`, `Γ(V, 𝒪)`, `Γ(U ∩ V, 𝒪)`. The two-set Čech `H¹` `R_{UV}/(R_U + R_V)`
(`FormalSchemes.TwoCech`) is finite-dimensional of dimension `g + ℓ(0) - 1`
(`CurvesJacobian.finrank_cechH1FF`), i.e. `g` when `k` is the full constant field (`ℓ(0) = 1`).

Proof: with `E = ∑_{P ∈ s} P`, `E' = ∑_{P ∈ s'} P`, `R_{UV} = ⋃ₙ L(n(E + E'))`, and
`L(n(E + E')) ∩ (R_U + R_V) = L(nE) + L(nE')` with `L(nE) ∩ L(nE') = L(0)`, so by Riemann–Roch
the image of `L(n(E + E'))` in `H¹` has dimension `g + ℓ(0) - 1` for `n ≫ 0`; these images
increase with `n` and exhaust `H¹`.
-/

open WeilCurves.FunctionField WeilCurves.FunctionField.Divisor Module

namespace CurvesJacobian

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k]
  [IsFunctionField k K]

/-- Decidable equality of places (classical), for unions of finite sets of places. -/
noncomputable instance : DecidableEq (Place k K) := Classical.decEq _

/-- Functions regular at all places outside a finite set `s`. -/
def regularOutside (s : Finset (Place k K)) : Submodule k K where
  carrier := {f | ∀ P : Place k K, P ∉ s → f ∈ P.1}
  zero_mem' _ _ := zero_mem _
  add_mem' hf hg P hP := add_mem (hf P hP) (hg P hP)
  smul_mem' c f hf P hP := by
    rw [Algebra.smul_def]
    exact mul_mem (P.mem_of_ord_nonneg (by rw [P.ord_algebraMap_base])) (hf P hP)

variable {k}

lemma regularOutside_mono {s s' : Finset (Place k K)} (h : s ⊆ s') :
    regularOutside k s ≤ regularOutside k s' :=
  fun _ hf P hP ↦ hf P (fun hs ↦ hP (h hs))

variable (k) in
/-- The two-set Čech `H¹` `R_{UV} / (R_U + R_V)` for the "cover" with complements `s`, `s'`. -/
abbrev cechH1FF (s s' : Finset (Place k K)) : Type _ :=
  TwoCech.H1 (Submodule.inclusion (regularOutside_mono (k := k) Finset.subset_union_left :
      regularOutside k s ≤ regularOutside k (s ∪ s')))
    (Submodule.inclusion (regularOutside_mono (k := k) Finset.subset_union_right :
      regularOutside k s' ≤ regularOutside k (s ∪ s')))

lemma mem_range_d_iff (s s' : Finset (Place k K)) (x : regularOutside k (s ∪ s')) :
    x ∈ LinearMap.range (TwoCech.d
      (Submodule.inclusion (regularOutside_mono (k := k) Finset.subset_union_left :
        regularOutside k s ≤ regularOutside k (s ∪ s')))
      (Submodule.inclusion (regularOutside_mono (k := k) Finset.subset_union_right :
        regularOutside k s' ≤ regularOutside k (s ∪ s')))) ↔
      (x : K) ∈ regularOutside k s ⊔ regularOutside k s' := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    simp only [TwoCech.d_apply, Submodule.coe_sub, Submodule.coe_inclusion]
    exact sub_mem (Submodule.mem_sup_left a.2) (Submodule.mem_sup_right b.2)
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    refine ⟨(⟨a, ha⟩, -⟨b, hb⟩), ?_⟩
    ext
    simp [hab]

lemma mem_val_iff_ord (P : Place k K) (f : K) : f ∈ P.1 ↔ 0 ≤ P.ord f := by
  rw [← not_lt, P.ord_neg_iff, not_not]

section Divisors

variable (k) in
/-- The reduced divisor `∑_{P ∈ s} P`. -/
noncomputable def finsetDiv (s : Finset (Place k K)) : Divisor k K :=
  ∑ P ∈ s, Finsupp.single P 1

omit [PerfectField k] [IsFunctionField k K] in
lemma finsetDiv_apply (s : Finset (Place k K)) (P : Place k K) :
    finsetDiv k s P = if P ∈ s then 1 else 0 := by
  classical
  simp only [finsetDiv, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

omit [PerfectField k] [IsFunctionField k K] in
lemma finsetDiv_apply_of_mem {s : Finset (Place k K)} {P : Place k K} (h : P ∈ s) :
    finsetDiv k s P = 1 := by
  classical
  rw [finsetDiv_apply, if_pos h]

omit [PerfectField k] [IsFunctionField k K] in
lemma finsetDiv_apply_of_not_mem {s : Finset (Place k K)} {P : Place k K} (h : P ∉ s) :
    finsetDiv k s P = 0 := by
  classical
  rw [finsetDiv_apply, if_neg h]

omit [PerfectField k] [IsFunctionField k K] in
lemma finsetDiv_nonneg (s : Finset (Place k K)) : 0 ≤ finsetDiv k s := by
  intro P
  by_cases h : P ∈ s
  · rw [finsetDiv_apply_of_mem h]; simp
  · rw [finsetDiv_apply_of_not_mem h]; simp

omit [PerfectField k] [IsFunctionField k K] in
lemma finsetDiv_ne_zero {s : Finset (Place k K)} (hs : s.Nonempty) : finsetDiv k s ≠ 0 := by
  obtain ⟨P, hP⟩ := hs
  intro h
  have := congrArg (· P) h
  simp only [finsetDiv_apply_of_mem hP, Finsupp.coe_zero, Pi.zero_apply] at this
  exact one_ne_zero this

lemma deg_finsetDiv_pos {s : Finset (Place k K)} (hs : s.Nonempty) : 0 < (finsetDiv k s).deg :=
  deg_pos_of_nonneg_of_ne_zero (finsetDiv_nonneg s) (finsetDiv_ne_zero hs)

end Divisors

section RiemannRoch

variable {s s' : Finset (Place k K)}

lemma L_nsmul_finsetDiv_le (s : Finset (Place k K)) (n : ℕ) :
    L (n • finsetDiv k s) ≤ regularOutside k s := by
  rintro f (rfl | hf) P hP
  · exact zero_mem _
  rw [mem_val_iff_ord]
  have := hf P
  simpa [finsetDiv_apply_of_not_mem hP] using this

lemma L_nsmul_sum_mono (s s' : Finset (Place k K)) {m n : ℕ} (h : m ≤ n) :
    L (m • (finsetDiv k s + finsetDiv k s')) ≤ L (n • (finsetDiv k s + finsetDiv k s')) :=
  L_mono (nsmul_le_nsmul_left (add_nonneg (finsetDiv_nonneg s) (finsetDiv_nonneg s')) h)

lemma L_nsmul_sum_le (s s' : Finset (Place k K)) (n : ℕ) :
    L (n • (finsetDiv k s + finsetDiv k s')) ≤ regularOutside k (s ∪ s') := by
  rintro f (rfl | hf) P hP
  · exact zero_mem _
  rw [Finset.mem_union, not_or] at hP
  rw [mem_val_iff_ord]
  have := hf P
  simpa [finsetDiv_apply_of_not_mem hP.1, finsetDiv_apply_of_not_mem hP.2] using this

/-- Every function regular outside `s ∪ s'` lies in some `L(n(E + E'))`. -/
lemma exists_mem_L_nsmul_sum (f : K) (hf : f ∈ regularOutside k (s ∪ s')) :
    ∃ n : ℕ, f ∈ L (n • (finsetDiv k s + finsetDiv k s')) := by
  by_cases hf0 : f = 0
  · exact ⟨0, hf0 ▸ zero_mem _⟩
  let u := (Place.finite_setOf_ord_neg (k := k) f).toFinset
  refine ⟨∑ P ∈ u, (-P.ord f).toNat, Or.inr fun P ↦ ?_⟩
  simp only [Finsupp.smul_apply, Finsupp.coe_add, Pi.add_apply, nsmul_eq_mul]
  have hs0 := finsetDiv_nonneg (k := k) s P
  have hs0' := finsetDiv_nonneg (k := k) s' P
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hs0 hs0'
  by_cases hP : P.ord f < 0
  · have hPu : P ∈ u := by simp [u, hP]
    have hmem : P ∈ s ∪ s' := by
      by_contra h
      exact (P.ord_neg_iff.mp hP) (hf P h)
    have h1 : (1 : ℤ) ≤ finsetDiv k s P + finsetDiv k s' P := by
      rcases Finset.mem_union.mp hmem with h | h
      · rw [finsetDiv_apply_of_mem h]; omega
      · rw [finsetDiv_apply_of_mem h]; omega
    have h2 : ((-P.ord f).toNat : ℤ) ≤ ((∑ P ∈ u, (-P.ord f).toNat : ℕ) : ℤ) := by
      exact_mod_cast Finset.single_le_sum (f := fun P ↦ (-P.ord f).toNat)
        (fun _ _ ↦ Nat.zero_le _) hPu
    have h3 : -P.ord f ≤ ((∑ P ∈ u, (-P.ord f).toNat : ℕ) : ℤ) :=
      (Int.self_le_toNat _).trans h2
    have h4 : ((∑ P ∈ u, (-P.ord f).toNat : ℕ) : ℤ) ≤
        ((∑ P ∈ u, (-P.ord f).toNat : ℕ) : ℤ) * (finsetDiv k s P + finsetDiv k s' P) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) h1
    linarith
  · push Not at hP
    have : (0 : ℤ) ≤ ((∑ P ∈ u, (-P.ord f).toNat : ℕ) : ℤ) *
        (finsetDiv k s P + finsetDiv k s' P) :=
      mul_nonneg (Nat.cast_nonneg _) (by omega)
    linarith

/-- `ord (x + y) ≥ min (ord x) (ord y)`, in a form with an explicit lower bound. -/
lemma ord_add_ge (P : Place k K) {x y : K} (hxy : x + y ≠ 0) {m : ℤ} (hx : m ≤ P.ord x)
    (hy : m ≤ P.ord y) : m ≤ P.ord (x + y) :=
  (le_min hx hy).trans (P.min_le_ord_add hxy)

/-- If `a + b ∈ L(n(E + E'))` with `a` regular outside `s` and `b` regular outside `s'`
(`s`, `s'` disjoint), then `a ∈ L(nE)`. -/
lemma mem_L_of_add_mem (hdisj : Disjoint s s') (n : ℕ) {a b : K}
    (ha : a ∈ regularOutside k s) (hb : b ∈ regularOutside k s')
    (hab : a + b ∈ L (n • (finsetDiv k s + finsetDiv k s'))) :
    a ∈ L (n • finsetDiv k s) := by
  by_cases ha0 : a = 0
  · exact ha0 ▸ zero_mem _
  refine Or.inr fun P ↦ ?_
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  by_cases hPs : P ∈ s
  · have hPs' : P ∉ s' := Finset.disjoint_left.mp hdisj hPs
    rw [finsetDiv_apply_of_mem hPs]
    have hbP : 0 ≤ P.ord b := (mem_val_iff_ord P b).mp (hb P hPs')
    have hkey : -(n : ℤ) ≤ P.ord (a + b) := by
      rcases hab with h0 | h
      · rw [h0, Place.ord_zero]; simp
      · have := h P
        simp only [Finsupp.smul_apply, Finsupp.coe_add, Pi.add_apply, nsmul_eq_mul,
          finsetDiv_apply_of_mem hPs, finsetDiv_apply_of_not_mem hPs'] at this
        simpa using this
    have hsum : a = (a + b) + (-b) := by ring
    have hneg : -(n : ℤ) ≤ P.ord (-b) := by
      rw [P.ord_neg]
      have : (0 : ℤ) ≤ n := Nat.cast_nonneg n
      linarith
    have := ord_add_ge P (x := a + b) (y := -b) (by rw [← hsum]; exact ha0) hkey hneg
    rw [← hsum] at this
    simpa using this
  · rw [finsetDiv_apply_of_not_mem hPs, mul_zero, neg_zero]
    exact (mem_val_iff_ord P a).mp (ha P hPs)

/-- `L(n(E + E')) ∩ (R_U + R_V) = L(nE) + L(nE')`. -/
lemma mem_L_sup_of_mem (hdisj : Disjoint s s') (n : ℕ) {f : K}
    (hf : f ∈ L (n • (finsetDiv k s + finsetDiv k s')))
    (hUV : f ∈ regularOutside k s ⊔ regularOutside k s') :
    f ∈ L (n • finsetDiv k s) ⊔ L (n • finsetDiv k s') := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hUV
  refine Submodule.add_mem_sup (mem_L_of_add_mem hdisj n ha hb hf) ?_
  rw [add_comm a b, add_comm (finsetDiv k s)] at hf
  exact mem_L_of_add_mem hdisj.symm n hb ha hf

lemma L_inf_L (hdisj : Disjoint s s') (n : ℕ) :
    L (n • finsetDiv k s) ⊓ L (n • finsetDiv k s') = L (0 : Divisor k K) := by
  apply le_antisymm
  · rintro f ⟨hp | hp, hz | hz⟩
    · exact Or.inl hp
    · exact Or.inl hp
    · exact Or.inl hz
    refine Or.inr fun P ↦ ?_
    have h1 := hp P
    have h2 := hz P
    simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
    by_cases hPs : P ∈ s
    · have hPs' : P ∉ s' := Finset.disjoint_left.mp hdisj hPs
      simpa [finsetDiv_apply_of_not_mem hPs'] using h2
    · simpa [finsetDiv_apply_of_not_mem hPs] using h1
  · exact le_inf (L_mono (nsmul_nonneg (finsetDiv_nonneg s) n))
      (L_mono (nsmul_nonneg (finsetDiv_nonneg s') n))

variable (k s s') in
/-- The map `L(n(E + E')) → H¹`. -/
noncomputable def toCechH1FF (n : ℕ) :
    L (n • (finsetDiv k s + finsetDiv k s')) →ₗ[k] cechH1FF k s s' :=
  (Submodule.mkQ _) ∘ₗ Submodule.inclusion (L_nsmul_sum_le s s' n)

lemma ker_toCechH1FF (hdisj : Disjoint s s') (n : ℕ) : LinearMap.ker (toCechH1FF k s s' n) =
    (L (n • finsetDiv k s) ⊔ L (n • finsetDiv k s')).comap
      (L (n • (finsetDiv k s + finsetDiv k s'))).subtype := by
  ext ⟨f, hf⟩
  simp only [LinearMap.mem_ker, toCechH1FF, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype]
  rw [mem_range_d_iff]
  exact ⟨fun h ↦ mem_L_sup_of_mem hdisj n hf h,
    fun h ↦ sup_le_sup (L_nsmul_finsetDiv_le s n) (L_nsmul_finsetDiv_le s' n) h⟩

lemma finrank_range_toCechH1FF_eq (hdisj : Disjoint s s') (n : ℕ) :
    (finrank k (LinearMap.range (toCechH1FF k s s' n)) : ℤ) =
      ell (n • (finsetDiv k s + finsetDiv k s')) - ell (n • finsetDiv k s) -
        ell (n • finsetDiv k s') + ell (0 : Divisor k K) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (toCechH1FF k s s' n)
  rw [ker_toCechH1FF hdisj] at h1
  have hle : L (n • finsetDiv k s) ⊔ L (n • finsetDiv k s') ≤
      L (n • (finsetDiv k s + finsetDiv k s')) :=
    sup_le (L_mono (nsmul_le_nsmul_right (le_add_of_nonneg_right (finsetDiv_nonneg s')) n))
      (L_mono (nsmul_le_nsmul_right (le_add_of_nonneg_left (finsetDiv_nonneg s)) n))
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (L (n • finsetDiv k s))
    (L (n • finsetDiv k s'))
  rw [L_inf_L hdisj] at h2
  simp only [ell]
  omega

variable (k K) in
/-- A bound beyond which Riemann–Roch computes all the `ℓ` involved. -/
noncomputable def cechBound : ℕ := (2 * genus k K).toNat

lemma finrank_range_toCechH1FF (hdisj : Disjoint s s') (hs : s.Nonempty) (hs' : s'.Nonempty)
    {n : ℕ} (hn : cechBound k K ≤ n) :
    (finrank k (LinearMap.range (toCechH1FF k s s' n)) : ℤ) =
      genus k K + ell (0 : Divisor k K) - 1 := by
  rw [finrank_range_toCechH1FF_eq hdisj]
  have hd := deg_finsetDiv_pos (k := k) hs
  have hd' := deg_finsetDiv_pos (k := k) hs'
  have hn' : 2 * genus k K ≤ (n : ℤ) := by
    have := Int.self_le_toNat (2 * genus k K)
    unfold cechBound at hn
    omega
  have hnd : (n : ℤ) ≤ n * (finsetDiv k s).deg := le_mul_of_one_le_right (by positivity) hd
  have hnd' : (n : ℤ) ≤ n * (finsetDiv k s').deg := le_mul_of_one_le_right (by positivity) hd'
  have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have e1 := ell_eq_of_deg_gt (A := n • (finsetDiv k s + finsetDiv k s')) (by
    rw [deg_nsmul, deg_add]; nlinarith)
  have e2 := ell_eq_of_deg_gt (A := n • finsetDiv k s) (by rw [deg_nsmul]; nlinarith)
  have e3 := ell_eq_of_deg_gt (A := n • finsetDiv k s') (by rw [deg_nsmul]; nlinarith)
  rw [e1, e2, e3, deg_nsmul, deg_nsmul, deg_nsmul, deg_add]
  ring

lemma range_toCechH1FF_mono {m n : ℕ} (h : m ≤ n) :
    LinearMap.range (toCechH1FF k s s' m) ≤ LinearMap.range (toCechH1FF k s s' n) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Submodule.inclusion (L_nsmul_sum_mono s s' h) x, rfl⟩

lemma exists_mem_range_toCechH1FF (x : cechH1FF k s s') :
    ∃ n, x ∈ LinearMap.range (toCechH1FF k s s' n) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨n, hn⟩ := exists_mem_L_nsmul_sum (s := s) (s' := s') (y : K) y.2
  exact ⟨n, ⟨⟨y, hn⟩, rfl⟩⟩

lemma range_toCechH1FF_eq_top (hdisj : Disjoint s s') (hs : s.Nonempty) (hs' : s'.Nonempty) :
    LinearMap.range (toCechH1FF k s s' (cechBound k K)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn⟩ := exists_mem_range_toCechH1FF x
  have hle := range_toCechH1FF_mono (k := k) (s := s) (s' := s')
    (le_max_right n (cechBound k K))
  have heq : LinearMap.range (toCechH1FF k s s' (cechBound k K)) =
      LinearMap.range (toCechH1FF k s s' (max n (cechBound k K))) :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      have a := finrank_range_toCechH1FF hdisj hs hs' (le_refl (cechBound k K))
      have b := finrank_range_toCechH1FF hdisj hs hs' (le_max_right n (cechBound k K))
      omega)
  rw [heq]
  exact range_toCechH1FF_mono (le_max_left _ _) hn

/-- The Čech `H¹` of a two-set cover of a function field is finite-dimensional. -/
theorem finiteDimensional_cechH1FF (hdisj : Disjoint s s') (hs : s.Nonempty)
    (hs' : s'.Nonempty) : FiniteDimensional k (cechH1FF k s s') := by
  have : FiniteDimensional k (LinearMap.range (toCechH1FF k s s' (cechBound k K))) :=
    LinearMap.finiteDimensional_range _
  rw [range_toCechH1FF_eq_top hdisj hs hs'] at this
  exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl)

/-- **`h¹ = g`**: the Čech `H¹` `R_{UV}/(R_U + R_V)` of a two-set cover with disjoint nonempty
finite complements has dimension `g + ℓ(0) - 1` (so `g` when `k` is algebraically closed in
`K`). -/
theorem finrank_cechH1FF (hdisj : Disjoint s s') (hs : s.Nonempty) (hs' : s'.Nonempty) :
    (finrank k (cechH1FF k s s') : ℤ) = genus k K + ell (0 : Divisor k K) - 1 := by
  rw [← finrank_range_toCechH1FF hdisj hs hs' (le_refl (cechBound k K)),
    range_toCechH1FF_eq_top hdisj hs hs', finrank_top]

end RiemannRoch

end CurvesJacobian
