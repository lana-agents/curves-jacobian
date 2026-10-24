/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Main

/-!
# Numerically cuspidal isomorphisms are cuspidal: the compactness part

Continuation of `CurvesJacobian/CuspChar/Main.lean`. For `b ∈ Δ'` and a prime `p`,
`pPart b p = ⋂_{n > 0, p ∤ n} cl⟨b^n⟩` is the pro-`p` part of `cl⟨b⟩`. We show:

* `pow_ordCompl_mem_pPart_sup`: modulo every open normal `N`, the `p`-part of `b` lies in
  `pPart b p · N`;
* `exists_le_of_forall_le_sup`: a closed subgroup contained in `J_N N` with `J_N ∈ S'` for every
  `N` is contained in some `J ∈ S'` (finitely many classes and compactness);
* **`mem_iff_map_mem_of_numCusp`**: a numerically cuspidal `Φ : Δ ≃ₜ* Δ'` maps cusp groups exactly
  onto cusp groups.
-/

namespace CurvesJacobian.CuspChar

section Cuspidal

variable {Δ : Type*} [Group Δ] [TopologicalSpace Δ] [IsTopologicalGroup Δ] [CompactSpace Δ]
  [TotallyDisconnectedSpace Δ] [T2Space Δ]
  {Δ' : Type*} [Group Δ'] [TopologicalSpace Δ'] [IsTopologicalGroup Δ'] [CompactSpace Δ']
  [TotallyDisconnectedSpace Δ'] [T2Space Δ']

/-- The pro-`p` part `⋂_{n > 0, p ∤ n} cl⟨b^n⟩` of `cl⟨b⟩`. -/
def pPart (b : Δ') (p : ℕ) : Subgroup Δ' :=
  ⨅ n : {n : ℕ // 0 < n ∧ ¬ p ∣ n}, (Subgroup.zpowers (b ^ n.1)).topologicalClosure

omit [CompactSpace Δ'] [TotallyDisconnectedSpace Δ'] [T2Space Δ'] in
lemma pPart_le_closure (b : Δ') {p : ℕ} (hp : p.Prime) :
    pPart b p ≤ (Subgroup.zpowers b).topologicalClosure := by
  intro x hx
  have := (Subgroup.mem_iInf.1 hx) ⟨1, one_pos, hp.not_dvd_one⟩
  simpa using this

omit [CompactSpace Δ'] [TotallyDisconnectedSpace Δ'] [T2Space Δ'] in
lemma isClosed_pPart (b : Δ') (p : ℕ) : IsClosed (pPart b p : Set Δ') := by
  rw [pPart, Subgroup.coe_iInf]
  exact isClosed_iInter fun _ ↦ Subgroup.isClosed_topologicalClosure _

/-- `b^m, b^n ∈ K ⇒ b^{gcd(m,n)} ∈ K`. -/
lemma pow_gcd_mem {G : Type*} [Group G] {K : Subgroup G} {b : G} {m n : ℕ} (hm : b ^ m ∈ K)
    (hn : b ^ n ∈ K) : b ^ Nat.gcd m n ∈ K := by
  have hb := Nat.gcd_eq_gcd_ab m n
  have e : b ^ Nat.gcd m n = (b ^ m) ^ Nat.gcdA m n * (b ^ n) ^ Nat.gcdB m n := by
    rw [← zpow_natCast, hb, zpow_add, ← zpow_natCast b m, ← zpow_natCast b n, ← zpow_mul,
      ← zpow_mul]
  rw [e]
  exact K.mul_mem (K.zpow_mem hm _) (K.zpow_mem hn _)

/-- In a finite group, `x^{d'} ∈ ⟨x^n⟩` if `d'` is the prime-to-`p` part of the order of `x` and
`p ∤ n`. -/
lemma pow_ordCompl_mem_zpowers {Q : Type*} [Group Q] [Finite Q] (x : Q) {p : ℕ} (hp : p.Prime)
    {n : ℕ} (hn : ¬ p ∣ n) : x ^ ordCompl[p] (orderOf x) ∈ Subgroup.zpowers (x ^ n) := by
  set d := orderOf x
  have hd : d ≠ 0 := (orderOf_pos x).ne'
  set g := Nat.gcd n d
  -- `x^g ∈ ⟨x^n⟩` by Bézout
  have hg : x ^ g ∈ Subgroup.zpowers (x ^ n) :=
    pow_gcd_mem (Subgroup.mem_zpowers _) (by rw [pow_orderOf_eq_one]; exact one_mem _)
  -- `g ∣ d'`
  have hgd' : g ∣ ordCompl[p] d := by
    have hcop : Nat.Coprime g (p ^ d.factorization p) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact fun h ↦ hn (h.trans (Nat.gcd_dvd_left n d))
    have : g ∣ p ^ d.factorization p * ordCompl[p] d := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
      exact Nat.gcd_dvd_right n d
    exact hcop.dvd_of_dvd_mul_left this
  obtain ⟨k, hk⟩ := hgd'
  rw [hk, pow_mul]
  exact Subgroup.pow_mem _ hg k

omit [TotallyDisconnectedSpace Δ'] [T2Space Δ'] in
/-- **The `p`-part of `b` modulo `N` lies in `pPart b p · N`.** -/
lemma pow_ordCompl_mem_pPart_sup (b : Δ') {p : ℕ} (hp : p.Prime) (N : OpenNormalSubgroup Δ') :
    b ^ ordCompl[p] (orderOf (QuotientGroup.mk b : Δ' ⧸ (N : Subgroup Δ'))) ∈
      pPart b p ⊔ (N : Subgroup Δ') := by
  set x := b ^ ordCompl[p] (orderOf (QuotientGroup.mk b : Δ' ⧸ (N : Subgroup Δ')))
  have : Nonempty {n : ℕ // 0 < n ∧ ¬ p ∣ n} := ⟨⟨1, one_pos, hp.not_dvd_one⟩⟩
  let t : {n : ℕ // 0 < n ∧ ¬ p ∣ n} → Set Δ' := fun n ↦
    ((Subgroup.zpowers (b ^ n.1)).topologicalClosure : Set Δ') ∩ {c | c⁻¹ * x ∈ (N : Subgroup Δ')}
  have hNcl : IsClosed ((N : Subgroup Δ') : Set Δ') := Subgroup.isClosed_of_isOpen _ N.isOpen'
  have htcl : ∀ n, IsClosed (t n) := fun n ↦
    (Subgroup.isClosed_topologicalClosure _).inter
      (hNcl.preimage ((continuous_inv).mul continuous_const))
  have htn : ∀ n, (t n).Nonempty := by
    intro n
    have hmem := pow_ordCompl_mem_zpowers (QuotientGroup.mk b : Δ' ⧸ (N : Subgroup Δ')) hp n.2.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine ⟨(b ^ n.1) ^ j, Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem _
      (Subgroup.mem_zpowers _) j), ?_⟩
    change ((b ^ n.1) ^ j)⁻¹ * x ∈ (N : Subgroup Δ')
    rw [← QuotientGroup.eq]
    simp only [x, QuotientGroup.mk_zpow, QuotientGroup.mk_pow] at hj ⊢
    exact hj
  have htd : Directed (· ⊇ ·) t := by
    intro n m
    refine ⟨⟨n.1 * m.1, Nat.mul_pos n.2.1 m.2.1, fun h ↦ ?_⟩, ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd h n.2.2
      · exact absurd h m.2.2
    · refine Set.inter_subset_inter_left _ (Subgroup.topologicalClosure_mono ?_)
      change Subgroup.zpowers (b ^ (n.1 * m.1)) ≤ _
      rw [Subgroup.zpowers_le, pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · refine Set.inter_subset_inter_left _ (Subgroup.topologicalClosure_mono ?_)
      change Subgroup.zpowers (b ^ (n.1 * m.1)) ≤ _
      rw [Subgroup.zpowers_le, mul_comm, pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun n ↦ (htcl n).isCompact) htcl
  rw [Set.mem_iInter] at hc
  refine mem_sup_iff.2 ⟨c, Subgroup.mem_iInf.2 fun n ↦ (hc n).1, (hc ⟨1, one_pos,
    hp.not_dvd_one⟩).2⟩

omit [T2Space Δ'] in
/-- **Compactness over the cusp classes.** -/
lemma exists_le_of_forall_le_sup {S' : Set (Subgroup Δ')} (hS' : IsCuspSet S')
    {B : Subgroup Δ'} (h : ∀ N : OpenNormalSubgroup Δ', ∃ J ∈ S', B ≤ J ⊔ (N : Subgroup Δ')) :
    ∃ J ∈ S', B ≤ J := by
  classical
  have hcl : ∀ I ∈ S', IsClosed (I : Set Δ') := fun I hI ↦ hS'.isClosed hI
  obtain ⟨hSc', -, -, -, -, hSfin', -⟩ := hS'
  have hNe : Nonempty (OpenNormalSubgroup Δ') :=
    ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ, isNormal' := inferInstance }⟩
  let Q := CuspQuot S' ((⊤ : OpenSubgroup Δ') : Subgroup Δ')
  have : Finite Q := hSfin' ⊤
  let := Fintype.ofFinite Q
  let r : Q → Subgroup Δ' := fun q ↦ (Quotient.out q).1
  have hr : ∀ q, r q ∈ S' := fun q ↦ (Quotient.out q).2
  -- every cusp group is conjugate to a representative
  have hconj : ∀ J ∈ S', ∃ q g, J = conjSub g (r q) := by
    intro J hJ
    refine ⟨Quotient.mk _ ⟨J, hJ⟩, ?_⟩
    obtain ⟨g, -, hg⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk _ ⟨J, hJ⟩ : Q))
    exact ⟨g, hg.symm⟩
  let A : Q → OpenNormalSubgroup Δ' → Set Δ' := fun q N ↦
    {g | ∀ x ∈ B, g⁻¹ * x * g ∈ r q ⊔ (N : Subgroup Δ')}
  have hA : ∀ N, ∃ q, (A q N).Nonempty := by
    intro N
    obtain ⟨J, hJ, hBJ⟩ := h N
    obtain ⟨q, g, rfl⟩ := hconj J hJ
    exact ⟨q, g, fun x hx ↦ conj_mem_sup g (hBJ hx)⟩
  have hAmono : ∀ q {N₁ N₂ : OpenNormalSubgroup Δ'}, N₁ ≤ N₂ → A q N₁ ⊆ A q N₂ := by
    intro q N₁ N₂ hle g hg x hx
    exact (sup_le_sup_left (show (N₁ : Subgroup Δ') ≤ N₂ from hle) _) (hg x hx)
  -- some class works for every `N`
  have hq : ∃ q, ∀ N, (A q N).Nonempty := by
    by_contra hno
    push Not at hno
    choose Nq hNq using hno
    have hQne : (Finset.univ : Finset Q).Nonempty := by
      obtain ⟨q, -⟩ := hA (Classical.arbitrary _)
      exact ⟨q, Finset.mem_univ q⟩
    · obtain ⟨q, hq⟩ := hA (Finset.univ.inf' hQne Nq)
      obtain ⟨g, hg⟩ := hq
      have := hAmono q (Finset.inf'_le Nq (Finset.mem_univ q)) hg
      rw [hNq q] at this
      exact this
  obtain ⟨q, hqN⟩ := hq
  -- compactness in `Δ'`
  have hAcl : ∀ N, IsClosed (A q N) := by
    intro N
    have : A q N = ⋂ x ∈ B, (fun g : Δ' ↦ g⁻¹ * x * g) ⁻¹' ((r q ⊔ (N : Subgroup Δ') :
        Subgroup Δ') : Set Δ') := by
      ext g
      simp [A]
    rw [this]
    exact isClosed_biInter fun x _ ↦ (isClosed_sup_open (r q) N).preimage
      ((continuous_inv.mul continuous_const).mul continuous_id)
  have hdir : Directed (· ⊇ ·) (A q) := fun N₁ N₂ ↦
    ⟨N₁ ⊓ N₂, hAmono q inf_le_left, hAmono q inf_le_right⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (A q) hdir
    hqN (fun N ↦ (hAcl N).isCompact) hAcl
  rw [Set.mem_iInter] at hg
  refine ⟨conjSub g (r q), hSc' _ (hr q) g, fun x hx ↦ mem_conjSub_iff.2 ?_⟩
  exact mem_of_forall_mem_sup (hcl _ (hr q)) fun N ↦ hg N x hx

/-- In a finite group, `x ∈ ⟨x^n⟩` if `n` is prime to the order of `x`. -/
lemma mem_zpowers_pow_of_coprime {Q : Type*} [Group Q] (x : Q) {n : ℕ}
    (h : Nat.Coprime n (orderOf x)) : x ∈ Subgroup.zpowers (x ^ n) := by
  refine Subgroup.mem_zpowers_iff.2 ⟨Nat.gcdA n (orderOf x), ?_⟩
  have hb := Nat.gcd_eq_gcd_ab n (orderOf x)
  rw [h, Nat.cast_one] at hb
  rw [← zpow_natCast, ← zpow_mul]
  conv_rhs => rw [← zpow_one x, hb]
  rw [zpow_add, zpow_mul x _ (Nat.gcdB _ _), zpow_natCast x (orderOf x), pow_orderOf_eq_one,
    one_zpow, mul_one, mul_comm]

omit [T2Space Δ'] in
/-- **`pPart b p ≠ 1`** if `b ∉ cl⟨b^p⟩`. -/
lemma pPart_ne_bot {b : Δ'} {p : ℕ} (hp : p.Prime)
    (hb : b ∉ (Subgroup.zpowers (b ^ p)).topologicalClosure) : pPart b p ≠ ⊥ := by
  -- some `N` with `b ∉ cl⟨b^p⟩ N`
  obtain ⟨N, hN⟩ : ∃ N : OpenNormalSubgroup Δ',
      b ∉ (Subgroup.zpowers (b ^ p)).topologicalClosure ⊔ (N : Subgroup Δ') := by
    by_contra hall
    push Not at hall
    exact hb (mem_of_forall_mem_sup (Subgroup.isClosed_topologicalClosure _) hall)
  set bq := (QuotientGroup.mk b : Δ' ⧸ (N : Subgroup Δ'))
  set d := orderOf bq
  have hd : d ≠ 0 := (orderOf_pos _).ne'
  -- `p ∣ d`
  have hpd : p ∣ d := by
    by_contra hpd
    apply hN
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
      (mem_zpowers_pow_of_coprime bq ((hp.coprime_iff_not_dvd).2 hpd))
    refine mem_sup_iff.2 ⟨(b ^ p) ^ j, Subgroup.le_topologicalClosure _
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j), ?_⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, QuotientGroup.mk_pow]
    exact hj
  -- `e = b^{d'} ∉ N`
  set d' := ordCompl[p] d
  have hd'pos : 0 < d' := Nat.ordCompl_pos p hd
  have he : b ^ d' ∉ (N : Subgroup Δ') := by
    intro he
    have h1 : bq ^ d' = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 he
    have := orderOf_dvd_of_pow_eq_one h1
    have h2 : p ∣ d' := hpd.trans this
    exact Nat.not_dvd_ordCompl hp hd h2
  intro hbot
  have := pow_ordCompl_mem_pPart_sup b hp N
  rw [hbot, bot_sup_eq] at this
  exact he this

omit [CompactSpace Δ] [TotallyDisconnectedSpace Δ] [T2Space Δ] [CompactSpace Δ']
  [TotallyDisconnectedSpace Δ'] [T2Space Δ'] in
/-- The closure of `⟨c⟩` is carried by `Φ` to the closure of `⟨Φ c⟩`. -/
lemma map_topologicalClosure_zpowers (Φ : Δ ≃ₜ* Δ') (c : Δ) :
    (Subgroup.zpowers c).topologicalClosure.map Φ.toMulEquiv.toMonoidHom =
      (Subgroup.zpowers (Φ c)).topologicalClosure := by
  apply SetLike.coe_injective
  rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe]
  have himg : (Φ.toMulEquiv.toMonoidHom : Δ → Δ') '' (Subgroup.zpowers c : Set Δ) =
      (Subgroup.zpowers (Φ c) : Set Δ') := by
    rw [← Subgroup.coe_map, MonoidHom.map_zpowers]
    rfl
  have := Φ.toHomeomorph.image_closure (Subgroup.zpowers c : Set Δ)
  change (Φ.toHomeomorph : Δ → Δ') '' _ = _
  rw [this]
  exact congrArg closure himg

lemma mem_closure_zpowers_comm {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] {b x z : G} (hx : x ∈ (Subgroup.zpowers b).topologicalClosure)
    (hz : z ∈ (Subgroup.zpowers b).topologicalClosure) : x * z = z * x := by
  letI := Subgroup.commGroupTopologicalClosure (Subgroup.zpowers b) fun u v ↦ by
    obtain ⟨_, i, rfl⟩ := u
    obtain ⟨_, j, rfl⟩ := v
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← zpow_add, ← zpow_add, add_comm]
  have := mul_comm (⟨x, hx⟩ : (Subgroup.zpowers b).topologicalClosure) ⟨z, hz⟩
  exact congrArg Subtype.val this

omit [CompactSpace Δ] [TotallyDisconnectedSpace Δ] [T2Space Δ] in
/-- **One inclusion**: a numerically cuspidal `Φ` maps every cusp group into a cusp group. -/
theorem exists_map_le_of_numCusp (Φ : Δ ≃ₜ* Δ') {S : Set (Subgroup Δ)}
    {S' : Set (Subgroup Δ')} (hS : IsCuspSet S) (hS' : IsCuspSet S') (hnum : IsNumCusp Φ S S')
    {I : Subgroup Δ} (hI : I ∈ S) : ∃ J ∈ S', I.map Φ.toMulEquiv.toMonoidHom ≤ J := by
  obtain ⟨a, ha⟩ := hS.2.2.1 I hI
  set b := Φ a
  have hmapI : I.map Φ.toMulEquiv.toMonoidHom = (Subgroup.zpowers b).topologicalClosure := by
    rw [ha, map_topologicalClosure_zpowers]
  -- each `p`-part lies in a cusp group
  have hBp : ∀ p : ℕ, p.Prime → ∃ J ∈ S', pPart b p ≤ J := by
    intro p hp
    apply exists_le_of_forall_le_sup hS'
    intro N
    obtain ⟨J, hJ, hmem⟩ := exists_mem_sup_of_numCusp Φ hS hS' hnum hI ha hp N
    refine ⟨J, hJ, ?_⟩
    set d := orderOf (QuotientGroup.mk b : Δ' ⧸ (N : Subgroup Δ'))
    have hd : d ≠ 0 := (orderOf_pos _).ne'
    intro x hx
    have hx' := (Subgroup.mem_iInf.1 hx) ⟨ordCompl[p] d, Nat.ordCompl_pos p hd,
      Nat.not_dvd_ordCompl hp hd⟩
    exact Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hmem)
      (isClosed_sup_open J N) hx'
  -- `b ∉ cl⟨b^p⟩`
  have hbp : ∀ p : ℕ, p.Prime → b ∉ (Subgroup.zpowers (b ^ p)).topologicalClosure := by
    intro p hp hb
    apply hS.2.2.2.1 I hI a ha p hp
    have : Φ a ∈ (Subgroup.zpowers (a ^ p)).topologicalClosure.map Φ.toMulEquiv.toMonoidHom := by
      rw [map_topologicalClosure_zpowers, map_pow]
      exact hb
    obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.1 this
    have : y = a := Φ.injective hya
    exact this ▸ hy
  obtain ⟨J₂, hJ₂, hB₂⟩ := hBp 2 Nat.prime_two
  have hB₂ne : pPart b 2 ≠ ⊥ := pPart_ne_bot Nat.prime_two (hbp 2 Nat.prime_two)
  -- every `p`-part lies in `J₂`
  have hBq : ∀ q : ℕ, q.Prime → pPart b q ≤ J₂ := by
    intro q hq z hz
    have hzcl := pPart_le_closure b hq hz
    have hsub : pPart b 2 ≤ J₂ ⊓ conjSub z J₂ := by
      intro x hx
      refine ⟨hB₂ hx, mem_conjSub_iff.2 ?_⟩
      have hcomm := mem_closure_zpowers_comm (pPart_le_closure b Nat.prime_two hx) hzcl
      have : z⁻¹ * x * z = x := by
        rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact hB₂ hx
    have hne : J₂ ⊓ conjSub z J₂ ≠ ⊥ := fun h ↦ hB₂ne (le_bot_iff.1 (h ▸ hsub))
    have heq := hS'.2.2.2.2.1 J₂ hJ₂ _ (hS'.1 J₂ hJ₂ z) hne
    exact hS'.2.1 J₂ hJ₂ z heq.symm
  -- hence `b ∈ J₂`
  have hbJ : b ∈ J₂ := by
    refine mem_of_forall_mem_sup (hS'.isClosed hJ₂) fun N ↦ ?_
    set K := J₂ ⊔ (N : Subgroup Δ')
    set d := orderOf (QuotientGroup.mk b : Δ' ⧸ (N : Subgroup Δ'))
    have hd : 0 < d := orderOf_pos _
    have hdK : b ^ d ∈ K := Subgroup.mem_sup_right ((QuotientGroup.eq_one_iff _).1
      (by rw [QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _))
    have hqK : ∀ q : ℕ, q.Prime → b ^ ordCompl[q] d ∈ K := fun q hq ↦
      (sup_le_sup_right (hBq q hq) _) (pow_ordCompl_mem_pPart_sup b hq N)
    -- the least `m > 0` with `b^m ∈ K` divides `d` and all `d'_q`, hence is `1`
    have hex : ∃ m, 0 < m ∧ b ^ m ∈ K := ⟨d, hd, hdK⟩
    classical
    set m₀ := Nat.find hex
    have hm₀ := Nat.find_spec hex
    have hdvd : ∀ n, b ^ n ∈ K → m₀ ∣ n := by
      intro n hn
      by_cases hn0 : n = 0
      · rw [hn0]; exact dvd_zero _
      have hg := pow_gcd_mem hm₀.2 hn
      have hgpos : 0 < Nat.gcd m₀ n := Nat.gcd_pos_of_pos_left _ hm₀.1
      have hle := Nat.find_min' hex ⟨hgpos, hg⟩
      have hge := Nat.gcd_le_left n hm₀.1
      have : Nat.gcd m₀ n = m₀ := le_antisymm hge hle
      rw [← this]
      exact Nat.gcd_dvd_right _ _
    have hm₀1 : m₀ = 1 := by
      by_contra hne
      obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hne
      have hqd : q ∣ d := hqm.trans (hdvd d hdK)
      exact Nat.not_dvd_ordCompl hq hd.ne' (hqm.trans (hdvd _ (hqK q hq)))
    have h1 : b ^ m₀ ∈ K := hm₀.2
    rw [hm₀1, pow_one] at h1
    exact h1
  refine ⟨J₂, hJ₂, ?_⟩
  rw [hmapI]
  exact Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le).2 hbJ) (hS'.isClosed hJ₂)

omit [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] [T2Space Δ]
  [IsTopologicalGroup Δ'] [CompactSpace Δ'] [TotallyDisconnectedSpace Δ'] [T2Space Δ'] in
lemma isNumCusp_symm (Φ : Δ ≃ₜ* Δ') {S : Set (Subgroup Δ)} {S' : Set (Subgroup Δ')}
    (hnum : IsNumCusp Φ S S') : IsNumCusp Φ.symm S' S := by
  intro H'
  have h := hnum (mapOpenSub Φ.symm H')
  have : (mapOpenSub Φ (mapOpenSub Φ.symm H') : Subgroup Δ') = H' := by
    change ((H' : Subgroup Δ').map _).map _ = _
    rw [Subgroup.map_map]
    convert Subgroup.map_id (H' : Subgroup Δ')
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
    exact Φ.apply_symm_apply x
  rw [this] at h
  exact h.symm

omit [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] [T2Space Δ]
  [IsTopologicalGroup Δ'] [CompactSpace Δ'] [TotallyDisconnectedSpace Δ'] [T2Space Δ'] in
lemma map_symm_map (Φ : Δ ≃ₜ* Δ') (I : Subgroup Δ) :
    (I.map Φ.toMulEquiv.toMonoidHom).map Φ.symm.toMulEquiv.toMonoidHom = I := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id I
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
  exact Φ.symm_apply_apply x

/-- A numerically cuspidal `Φ` maps every cusp group onto a cusp group. -/
theorem map_mem_of_numCusp (Φ : Δ ≃ₜ* Δ') {S : Set (Subgroup Δ)}
    {S' : Set (Subgroup Δ')} (hS : IsCuspSet S) (hS' : IsCuspSet S') (hnum : IsNumCusp Φ S S')
    {I : Subgroup Δ} (hI : I ∈ S) : I.map Φ.toMulEquiv.toMonoidHom ∈ S' := by
  obtain ⟨J, hJ, hIJ⟩ := exists_map_le_of_numCusp Φ hS hS' hnum hI
  obtain ⟨I₂, hI₂, hJI₂⟩ := exists_map_le_of_numCusp Φ.symm hS' hS (isNumCusp_symm Φ hnum) hJ
  have hII₂ : I ≤ I₂ := by
    rw [← map_symm_map Φ I]
    exact (Subgroup.map_mono hIJ).trans hJI₂
  obtain ⟨a, ha⟩ := hS.2.2.1 I hI
  have hIne : I ≠ ⊥ := by
    intro hbot
    apply hS.2.2.2.1 I hI a ha 2 Nat.prime_two
    have : a = 1 := by
      have : a ∈ I := ha ▸ Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers a)
      rw [hbot] at this
      exact this
    rw [this]
    exact Subgroup.one_mem _
  have hEq : I = I₂ := hS.2.2.2.2.1 I hI I₂ hI₂ (by rwa [inf_eq_left.2 hII₂])
  have hJle : J ≤ I.map Φ.toMulEquiv.toMonoidHom := by
    have h1 := Subgroup.map_mono (f := Φ.toMulEquiv.toMonoidHom) (hEq ▸ hJI₂)
    have h2 := map_symm_map Φ.symm J
    simp only [ContinuousMulEquiv.symm_symm] at h2
    rwa [h2] at h1
  exact (le_antisymm hIJ hJle) ▸ hJ

/-- **[AbsTopI] Lemma 4.5 (v), group-theoretic core** (replacing [CombGC] Thm 1.6 (i)): a
numerically cuspidal topological isomorphism maps the cusp groups exactly onto the cusp groups. -/
theorem mem_iff_map_mem_of_numCusp (Φ : Δ ≃ₜ* Δ') {S : Set (Subgroup Δ)}
    {S' : Set (Subgroup Δ')} (hS : IsCuspSet S) (hS' : IsCuspSet S') (hnum : IsNumCusp Φ S S')
    (I : Subgroup Δ) : I ∈ S ↔ I.map Φ.toMulEquiv.toMonoidHom ∈ S' := by
  refine ⟨fun h ↦ map_mem_of_numCusp Φ hS hS' hnum h, fun h ↦ ?_⟩
  have := map_mem_of_numCusp Φ.symm hS' hS (isNumCusp_symm Φ hnum) h
  rwa [map_symm_map] at this

end Cuspidal

end CurvesJacobian.CuspChar
