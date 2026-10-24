/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Line
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Archimedean

/-!
# Numerically cuspidal isomorphisms are cuspidal (step G of [AbsTopI] Lemma 4.5 (v))

Let `Δ`, `Δ'` be profinite groups with sets `S`, `S'` of **cusp groups**: conjugation-stable,
self-normalising (`N_Δ(I) = I`), each the closure `cl⟨a⟩` of a cyclic group with `a ∉ cl⟨a^p⟩`
for every prime `p` (e.g. `I ≅ ℤ̂`), containing the centraliser of each of their nontrivial
elements, finitely many cusps for every open subgroup, and finitely many continuous
`ℤ/p`-characters on every open subgroup.

**Theorem** (`CurvesJacobian.CuspChar.mem_iff_map_mem_of_numCusp`). If a topological isomorphism
`Φ : Δ ≃ₜ* Δ'` is *numerically cuspidal* — `r(H) = r'(Φ H)` for every open subgroup `H`, where
`r(H)` is the number of `H`-conjugacy classes of cusp groups — then `Φ` maps cusp groups exactly
onto cusp groups.

This replaces [CombGC] Thm 1.6 (i) (`Combinatorial Grothendieck Conjecture.txt` l.691–735), whose
proof uses cuspidally *purely* totally ramified cyclic covers, which do not exist (see
`MR3-plan.md`). Here: for a cusp group `I = cl⟨a⟩`, put `b = Φ a` and, for a prime `p`,
`B_p = ⋂_{p ∤ n} cl⟨b^n⟩` (the pro-`p` part of `cl⟨b⟩`).

* **Lemma T** (`exists_mem_sup_of_numCusp`): for every open normal `N ⊆ Δ'`, with `d` the order of
  `b` modulo `N` and `d'` its prime-to-`p` part, `b^{d'} ∈ J N` for a cusp group `J`. Otherwise
  the character `ξ : ⟨b^{d'}⟩N → ℤ/p` through the cyclic `p`-group `⟨b^{d'}⟩N/N` is unramified
  at every cusp but nonzero at `b^{d'}`, while `a^{d'}` spans the line of the cusp `I` — this
  contradicts `transport_sameLine`.
* By compactness `B_p ⊆ J_p ∈ S'`; `B_p ≠ 1`; the `B_q` commute with `B_2`, so all lie in `J_2`
  (centralisers, self-normalising); the `B_q` generate `cl⟨b⟩` modulo every `N`, so
  `Φ I ⊆ J_2`. Symmetrically and by the centraliser property, `Φ I = J_2`.
-/

namespace CurvesJacobian.CuspChar

open Module

section Profinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- A closed subgroup is the intersection of the `C N`, `N` open normal. -/
lemma mem_of_forall_mem_sup {C : Subgroup G} (hC : IsClosed (C : Set G)) {x : G}
    (h : ∀ N : OpenNormalSubgroup G, x ∈ C ⊔ (N : Subgroup G)) : x ∈ C := by
  by_contra hx
  have hC' := ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨C, hC⟩
  have : x ∉ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ C ≤ N} := by
    rw [← hC']
    exact hx
  rw [Subgroup.mem_sInf] at this
  push Not at this
  obtain ⟨U, ⟨hUo, hCU⟩, hxU⟩ := this
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo U.one_mem
  exact hxU ((sup_le hCU (fun y hy ↦ hN hy)) (h N))

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
lemma isClosed_sup_open (C : Subgroup G) (N : OpenNormalSubgroup G) :
    IsClosed ((C ⊔ (N : Subgroup G) : Subgroup G) : Set G) :=
  Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right N.isOpen')

end Profinite

section GroupLemmas

variable {G : Type*} [Group G] [TopologicalSpace G]

lemma mem_sup_iff {C : Subgroup G} {N : OpenNormalSubgroup G} {x : G} :
    x ∈ C ⊔ (N : Subgroup G) ↔ ∃ c ∈ C, c⁻¹ * x ∈ (N : Subgroup G) := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal]
  constructor
  · rintro ⟨c, hc, n, hn, rfl⟩
    exact ⟨c, hc, by simpa using hn⟩
  · rintro ⟨c, hc, hn⟩
    exact ⟨c, hc, c⁻¹ * x, hn, by group⟩

lemma conj_mem_sup {C : Subgroup G} {N : OpenNormalSubgroup G} {x : G} (g : G)
    (hx : x ∈ conjSub g C ⊔ (N : Subgroup G)) : g⁻¹ * x * g ∈ C ⊔ (N : Subgroup G) := by
  obtain ⟨c, hc, hn⟩ := mem_sup_iff.1 hx
  refine mem_sup_iff.2 ⟨g⁻¹ * c * g, mem_conjSub_iff.1 hc, ?_⟩
  have := (N.isNormal').conj_mem _ hn g⁻¹
  simpa [mul_assoc] using this

end GroupLemmas

section Main

variable {Δ : Type*} [Group Δ] [TopologicalSpace Δ] [IsTopologicalGroup Δ] [CompactSpace Δ]
  [TotallyDisconnectedSpace Δ] [T2Space Δ]
  {Δ' : Type*} [Group Δ'] [TopologicalSpace Δ'] [IsTopologicalGroup Δ'] [CompactSpace Δ']
  [TotallyDisconnectedSpace Δ'] [T2Space Δ']

/-- The properties of the set of cuspidal inertia groups used by the group-theoretic
characterisation: conjugation-stable; self-normalising ([AbsTopI] Lemma 4.5 (vi)); each the
closure of a cyclic group whose generator is no `p`-th power of an element of it (e.g. `≅ ℤ̂`);
the centraliser of every nontrivial element of a cusp group lies in it (cf. [AbsTopI]
Lemma 4.1 (i)); finitely many cusps for every open
subgroup; finitely many continuous `ℤ/p`-characters on every open subgroup. -/
def IsCuspSet (S : Set (Subgroup Δ)) : Prop :=
  ConjStable S ∧ (∀ I ∈ S, ∀ g : Δ, conjSub g I = I → g ∈ I) ∧
    (∀ I ∈ S, ∃ a : Δ, I = (Subgroup.zpowers a).topologicalClosure) ∧
    (∀ I ∈ S, ∀ a : Δ, I = (Subgroup.zpowers a).topologicalClosure → ∀ p : ℕ, p.Prime →
      a ∉ (Subgroup.zpowers (a ^ p)).topologicalClosure) ∧
    (∀ I ∈ S, ∀ x ∈ I, x ≠ 1 → ∀ z : Δ, z * x = x * z → z ∈ I) ∧
    (∀ H : OpenSubgroup Δ, Finite (CuspQuot S (H : Subgroup Δ))) ∧
    (∀ p : ℕ, p.Prime → ∀ H : OpenSubgroup Δ, Finite (charSpace p H))

/-- `Φ` is **numerically cuspidal**: `r(H) = r'(Φ H)` for all open `H` ([CombGC] Def 1.4 (ii)). -/
def IsNumCusp (Φ : Δ ≃ₜ* Δ') (S : Set (Subgroup Δ)) (S' : Set (Subgroup Δ')) : Prop :=
  ∀ H : OpenSubgroup Δ, cuspCount S (H : Subgroup Δ) = cuspCount S' (mapOpenSub Φ H : Subgroup Δ')

omit [CompactSpace Δ] [TotallyDisconnectedSpace Δ] [T2Space Δ] in
lemma IsCuspSet.isClosed {S : Set (Subgroup Δ)} (hS : IsCuspSet S) {I : Subgroup Δ}
    (hI : I ∈ S) : IsClosed (I : Set Δ) := by
  obtain ⟨a, rfl⟩ := hS.2.2.1 I hI
  exact Subgroup.isClosed_topologicalClosure _

omit [CompactSpace Δ] [TotallyDisconnectedSpace Δ] [T2Space Δ] in
/-- `x ∈ cl⟨a⟩ ⇒ x^n ∈ cl⟨a^n⟩`. -/
lemma pow_mem_closure_zpowers {a x : Δ} (hx : x ∈ (Subgroup.zpowers a).topologicalClosure)
    (n : ℕ) : x ^ n ∈ (Subgroup.zpowers (a ^ n)).topologicalClosure := by
  have hc : Continuous fun y : Δ ↦ y ^ n := continuous_pow n
  have himg : (fun y : Δ ↦ y ^ n) '' (Subgroup.zpowers a : Set Δ) ⊆
      (Subgroup.zpowers (a ^ n) : Set Δ) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    change (a ^ n) ^ k = (a ^ k) ^ n
    rw [← zpow_natCast a n, ← zpow_mul, ← zpow_natCast (a ^ k) n, ← zpow_mul, mul_comm]
  have := image_closure_subset_closure_image hc ⟨x, hx, rfl⟩
  exact closure_mono himg this

omit [TopologicalSpace Δ] [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ]
  [T2Space Δ] in
lemma ξv_pow {p : ℕ} {H : Subgroup Δ} {ξ : Additive H →+ ZMod p} {x : Δ} (hx : x ∈ H) (n : ℕ) :
    ξv H ξ (x ^ n) = n • ξv H ξ x := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, ξv_of_mem H.one_mem]
    exact ξ.map_zero
  | succ n ih => rw [pow_succ, ξv_mul (H.pow_mem hx n) hx, ih, succ_nsmul]

/-- The quotient by an open normal subgroup is finite. -/
instance finite_quotient_openNormal (N : OpenNormalSubgroup Δ') :
    Finite (Δ' ⧸ (N : Subgroup Δ')) :=
  Subgroup.quotient_finite_of_isOpen _ N.isOpen'

omit [CompactSpace Δ] [TotallyDisconnectedSpace Δ] [T2Space Δ] [TotallyDisconnectedSpace Δ']
  [T2Space Δ'] in
/-- **Lemma T.** -/
lemma exists_mem_sup_of_numCusp (Φ : Δ ≃ₜ* Δ') {S : Set (Subgroup Δ)}
    {S' : Set (Subgroup Δ')} (hS : IsCuspSet S) (hS' : IsCuspSet S') (hnum : IsNumCusp Φ S S')
    {I : Subgroup Δ} (hI : I ∈ S) {a : Δ} (ha : I = (Subgroup.zpowers a).topologicalClosure)
    {p : ℕ} (hp : p.Prime) (N : OpenNormalSubgroup Δ') :
    ∃ J ∈ S', Φ a ^ ordCompl[p] (orderOf (QuotientGroup.mk (Φ a) : Δ' ⧸ (N : Subgroup Δ'))) ∈
      J ⊔ (N : Subgroup Δ') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSc, hSN, hScyc, -, -, hSfin, hSV⟩ := hS
  obtain ⟨hSc', hSN', hScyc', -, -, hSfin', hSV'⟩ := hS'
  set b := Φ a
  set d := orderOf (QuotientGroup.mk b : Δ' ⧸ (N : Subgroup Δ'))
  set d' := ordCompl[p] d
  set e := b ^ d'
  have hd : d ≠ 0 := (orderOf_pos _).ne'
  have hd'pos : 0 < d' := Nat.ordCompl_pos p hd
  have hpd' : ¬ p ∣ d' := Nat.not_dvd_ordCompl hp hd
  -- `S'` is nonempty
  have hS'ne : ∃ J, J ∈ S' := by
    have h1 : cuspCount S ((⊤ : OpenSubgroup Δ) : Subgroup Δ) ≠ 0 := by
      have : Finite (CuspQuot S ((⊤ : OpenSubgroup Δ) : Subgroup Δ)) := hSfin ⊤
      have : Nonempty (CuspQuot S ((⊤ : OpenSubgroup Δ) : Subgroup Δ)) :=
        ⟨Quotient.mk _ ⟨I, hI⟩⟩
      exact Nat.card_pos.ne'
    rw [hnum ⊤] at h1
    have : Nonempty (CuspQuot S' (mapOpenSub Φ ⊤ : Subgroup Δ')) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      exact h1 (Nat.card_of_isEmpty)
    obtain ⟨q⟩ := this
    induction q using Quotient.inductionOn with
    | h J => exact ⟨J.1, J.2⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨J₀, hJ₀⟩ := hS'ne
  have he : (QuotientGroup.mk e : Δ' ⧸ (N : Subgroup Δ')) ≠ 1 := by
    intro h1
    apply hcon J₀ hJ₀
    exact Subgroup.mem_sup_right ((QuotientGroup.eq_one_iff e).1 h1)
  set ē := (QuotientGroup.mk e : Δ' ⧸ (N : Subgroup Δ'))
  -- the order of `ē` is `p^k`, `k ≥ 1`
  have hordē : orderOf ē = ordProj[p] d := by
    simp only [ē, e, QuotientGroup.mk_pow]
    rw [orderOf_pow' _ hd'pos.ne', Nat.gcd_eq_right (Nat.ordCompl_dvd d p)]
    exact Nat.div_eq_of_eq_mul_left hd'pos (Nat.ordProj_mul_ordCompl_eq_self d p).symm
  have hpord : p ∣ orderOf ē := by
    rw [hordē]
    have hk : d.factorization p ≠ 0 := by
      intro hk
      apply he
      rw [← orderOf_eq_one_iff, hordē, hk, pow_zero]
    exact dvd_pow_self p hk
  have hpow_one : ∀ m : ℤ, ē ^ m = 1 → (p : ℤ) ∣ m := fun m hm ↦
    (Int.natCast_dvd_natCast.2 hpord).trans (orderOf_dvd_iff_zpow_eq_one.2 hm)
  have hcast : ∀ m m' : ℤ, ē ^ m = ē ^ m' → (m : ZMod p) = m' := by
    intro m m' h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    apply hpow_one
    rw [zpow_sub, h, mul_inv_cancel]
  have hgen : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → ē ∈ Subgroup.zpowers (ē ^ m) := by
    intro m hm
    have hcop : IsCoprime m (orderOf ē : ℤ) := by
      rw [hordē]
      have h1 : Nat.Coprime p m.natAbs :=
        (hp.coprime_iff_not_dvd).2 fun h ↦ hm (Int.natCast_dvd.2 h)
      have h2 : IsCoprime (p : ℤ) m :=
        Int.isCoprime_iff_gcd_eq_one.2 (by simpa [Int.gcd] using h1)
      have : IsCoprime m (p : ℤ) := h2.symm
      push_cast
      exact this.pow_right
    obtain ⟨u, v, huv⟩ := hcop
    refine Subgroup.mem_zpowers_iff.2 ⟨u, ?_⟩
    rw [← zpow_mul, mul_comm]
    have : ē ^ (u * m + v * (orderOf ē : ℤ)) = ē ^ (1 : ℤ) := by rw [huv]
    rw [zpow_add, mul_comm v, zpow_mul ē (orderOf ē : ℤ) v, zpow_natCast, pow_orderOf_eq_one,
      one_zpow, mul_one, zpow_one] at this
    exact this
  -- the open subgroup `H' = ⟨e⟩ N` and its preimage `H`
  set K' : Subgroup Δ' := Subgroup.zpowers e ⊔ (N : Subgroup Δ')
  have hK'open : IsOpen (K' : Set Δ') := Subgroup.isOpen_mono le_sup_right N.isOpen'
  let H : OpenSubgroup Δ :=
    ⟨K'.comap Φ.toMulEquiv.toMonoidHom, hK'open.preimage Φ.continuous⟩
  have hH' : (mapOpenSub Φ H : Subgroup Δ') = K' :=
    Subgroup.map_comap_eq_self_of_surjective Φ.surjective _
  have hmemH' : ∀ x, x ∈ (mapOpenSub Φ H : Subgroup Δ') →
      ∃ m : ℤ, (QuotientGroup.mk x : Δ' ⧸ (N : Subgroup Δ')) = ē ^ m := by
    intro x hx
    rw [hH'] at hx
    obtain ⟨c, hc, hn⟩ := mem_sup_iff.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_zpow]
    exact (QuotientGroup.eq.2 hn).symm
  -- the character `χ : H' → ℤ/p`
  let χ : Additive (mapOpenSub Φ H : Subgroup Δ') →+ ZMod p :=
    { toFun := fun z ↦ ((hmemH' _ (Additive.toMul z).2).choose : ZMod p)
      map_zero' := by
        rw [← Int.cast_zero]
        apply hcast
        rw [← (hmemH' _
          (Additive.toMul (0 : Additive (mapOpenSub Φ H : Subgroup Δ'))).2).choose_spec]
        simp
      map_add' := fun z w ↦ by
        rw [← Int.cast_add]
        apply hcast
        rw [zpow_add, ← (hmemH' _ (Additive.toMul z).2).choose_spec,
          ← (hmemH' _ (Additive.toMul w).2).choose_spec,
          ← (hmemH' _ (Additive.toMul (z + w)).2).choose_spec]
        rfl }
  have hχ : ∀ x (hx : x ∈ (mapOpenSub Φ H : Subgroup Δ')) (m : ℤ),
      (QuotientGroup.mk x : Δ' ⧸ (N : Subgroup Δ')) = ē ^ m →
        ξv (mapOpenSub Φ H : Subgroup Δ') χ x = m := by
    intro x hx m hm
    rw [ξv_of_mem hx]
    apply hcast
    rw [← hm]
    exact ((hmemH' _ hx).choose_spec).symm
  have heH' : e ∈ (mapOpenSub Φ H : Subgroup Δ') := by
    rw [hH']
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hχe : ξv (mapOpenSub Φ H : Subgroup Δ') χ e = 1 := by
    rw [hχ e heH' 1 (zpow_one _).symm]
    simp
  have hχmem : χ ∈ charSpace p (mapOpenSub Φ H) := by
    change IsOpen (kerSub (mapOpenSub Φ H : Subgroup Δ') χ : Set Δ')
    refine Subgroup.isOpen_mono (H₁ := (N : Subgroup Δ')) ?_ N.isOpen'
    intro n hn
    have hnH : n ∈ (mapOpenSub Φ H : Subgroup Δ') := by
      rw [hH']
      exact Subgroup.mem_sup_right hn
    refine mem_kerSub_iff.2 ⟨hnH, ?_⟩
    rw [hχ n hnH 0 (by rw [zpow_zero]; exact (QuotientGroup.eq_one_iff n).2 hn)]
    simp
  -- `χ` is unramified at every cusp of `H'`
  have hunram : ∀ J ∈ S', ¬ IsRam (mapOpenSub Φ H : Subgroup Δ') χ J := by
    rintro J hJ ⟨x, hxJ, hxH, hx⟩
    obtain ⟨m, hm⟩ := hmemH' x hxH
    have hpm : ¬ (p : ℤ) ∣ m := by
      intro hdvd
      apply hx
      rw [hχ x hxH m hm]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd m p).2 hdvd
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hgen m hpm)
    apply hcon J hJ
    refine mem_sup_iff.2 ⟨x ^ j, J.zpow_mem hxJ j, ?_⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hm]
    exact hj
  -- `a^{d'}` spans the line of the cusp `I` of `H`
  have hbH : a ^ d' ∈ (H : Subgroup Δ) := by
    change Φ (a ^ d') ∈ K'
    rw [map_pow]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers e)
  have hline : SameLine p H S (a ^ d') (Quotient.mk _ ⟨I, hI⟩) := by
    refine ⟨⟨⟨pullChar Φ H χ, pullChar_mem Φ H hχmem⟩, ?_⟩,
      fun ξ ↦ ⟨fun h0 hram ↦ ?_, fun hnr ↦ ?_⟩⟩
    · rw [ξv_pullChar, map_pow, hχe]
      exact one_ne_zero
    · obtain ⟨x, hxI, hxH, hx⟩ := hram
      have hxI' : x ∈ I := hxI
      rw [ha] at hxI'
      have hker : (Subgroup.zpowers (a ^ d')).topologicalClosure ≤ kerSub (H : Subgroup Δ) ξ.1 :=
        Subgroup.topologicalClosure_minimal _
          ((Subgroup.zpowers_le).2 (mem_kerSub_iff.2 ⟨hbH, h0⟩))
          (Subgroup.isClosed_of_isOpen _ ξ.2)
      have h1 := (mem_kerSub_iff.1 (hker (pow_mem_closure_zpowers hxI' d'))).2
      rw [ξv_pow hxH, nsmul_eq_mul] at h1
      have hd'0 : (d' : ZMod p) ≠ 0 := by
        rwa [Ne, ZMod.natCast_eq_zero_iff]
      exact hx ((mul_eq_zero.1 h1).resolve_left hd'0)
    · by_contra h0
      apply hnr
      refine ⟨a ^ d', ?_, hbH, h0⟩
      change a ^ d' ∈ I
      rw [ha]
      exact Subgroup.le_topologicalClosure _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _)
  obtain ⟨y', hy'⟩ := transport_sameLine Φ hSc hSN hSc' hSN' hScyc hScyc' hSfin hSfin'
    (hSV p hp) hnum H hbH ⟨_, hline⟩
  have hram := (not_iff_not.2 (hy'.2 ⟨χ, hχmem⟩)).1 (by rw [map_pow, hχe]; exact one_ne_zero)
  rw [not_not] at hram
  induction y' using Quotient.inductionOn with
  | h J => exact hunram J.1 J.2 hram

end Main

end CurvesJacobian.CuspChar
