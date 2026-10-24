/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Surface.CommensuratorOne

/-!
# The centraliser property of cuspidal inertia in profinite surface groups

Let `(g, r)` be hyperbolic with `r ≥ 1` and let `Iⱼ = ⟨cⱼ⟩‾ ⊆ Π̂_{g,r}` be a cuspidal inertia
group. We prove that **the centraliser of every nontrivial element of `Iⱼ` lies in `Iⱼ`**
(`CurvesJacobian.CuspChar.mem_inertia_of_commute`,
`CurvesJacobian.CuspChar.centralizer_le_inertia`).
This strengthens the commensurable terminality of cuspidal decomposition groups of
[AbsTopI] Lemma 4.1 (i) (`Topics in Absolute Anabelian Geometry I.txt` l.2742–2745: "If xA is a
cusp, then A is a torsion-free, commensurably terminal infinite subgroup of Δ"), proved in
`Pi1.Surface.Commensurator(One)` via the centraliser of `cⱼᵐ`, `m ≥ 1`; here `x` is an arbitrary
nontrivial element of `Iⱼ ≅ ℤ̂`, so its closed span need not be open in `Iⱼ`.

## The argument

* **Free profinite groups** (`mem_basisInertia_of_commute_of_mem`): let `x ≠ 1` lie in the
  inertia group `A_a = ⟨a⟩‾` of a basis element of `F̂(α)` and let `z` commute with `x`, with
  `z ∉ A_a`. Choose finite quotients `f₀` with `f̂₀(z) ∉ ⟨f₀ a⟩` and `f₁` with `f̂₁(x) ≠ 1`, put
  `φ = f₀ × f₁`, `s = φ(a)`, `t = φ̂(x) = sⁱ ≠ 1` of order `K = o / gcd(o, i)` (`o = ord s`), and
  map `F(α)` to the wreath product `ℤ/K ≀ Q` by `a ↦ (s, δ₁)` (other generators `↦ (φ b, 0)`).
  Then `xᴷ ↦ (1, d)` with `d(y) = #{n < iK | sⁿ y = 1} = q · 1_{⟨s⟩}(y)` where `iK = o q` and
  `q` is prime to `K > 1`; invariance of `d` under `φ̂(z)` forces `φ̂(z) ∈ ⟨s⟩`, a contradiction.
  This generalises `Pi1.Profinite.mem_basisInertia_of_commute` (the case `x = aᵐ`, coefficients
  `𝔽₂`).
* **At least two cusps** (`mem_inertia_two_of_commute`): move `cⱼ` to `c₀` by an automorphism
  (`Pi1.SurfaceGroup.exists_mulEquiv_isConj_cusp`); `c₀` is a basis element of
  `Π̂_{g,r+2} ≅ F̂(a, b, c_{≤ r})`.
* **One cusp** (`mem_inertia_one_of_commute`, `g ≥ 1`): `Π̂_{g,1} ≅ F̂(a₁, b₁, …)` with cusp
  `w⁻¹`, `w = ∏ [aᵢ, bᵢ]`. In the index-`3` subgroup `N̂ = ker χ₃` the word `w` is a basis
  element (`Pi1.SurfaceGroup.cuspEmb`). If `z` commutes with `x ∈ ⟨w⟩‾ \ {1}` and `χ₃(z) ≠ 0`,
  then in every quotient `F → Perm(ℤ/3 × ℤ/M)` given by the cocycle counting `s(1, b₁)` (in which
  `w` acts by `0, -1, +1` on the three fibres) the image `wⁱ` of `x` is trivial on the fibres;
  with `M = ord f(w)` for an arbitrary finite quotient `f` this forces `f̂(x) = 1`, so `x = 1`
  (`chiThree_eq_one_of_commute`). Hence `z ∈ N̂`, and we conclude in the free group `N̂`.
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology
open scoped Pointwise

universe u

namespace CurvesJacobian.CuspChar

open Pi1.Profinite

namespace WreathMod

variable {Q : Type u} [Group Q] {K : ℕ}

/-- The permutation `(y, c) ↦ (q y, c + f y)` of `Q × ℤ/K`. -/
def wr (q : Q) (f : Q → ZMod K) : Equiv.Perm (Q × ZMod K) where
  toFun p := (q * p.1, p.2 + f p.1)
  invFun p := (q⁻¹ * p.1, p.2 - f (q⁻¹ * p.1))
  left_inv p := by simp
  right_inv p := by simp

@[simp]
lemma wr_apply (q : Q) (f : Q → ZMod K) (p : Q × ZMod K) :
    wr q f p = (q * p.1, p.2 + f p.1) :=
  rfl

lemma wr_mul (q q' : Q) (f f' : Q → ZMod K) :
    wr q f * wr q' f' = wr (q * q') (fun x ↦ f' x + f (q' * x)) := by
  ext p
  · simp [mul_assoc]
  · simp [add_assoc]

lemma wr_injective {q q' : Q} {f f' : Q → ZMod K} (h : wr q f = wr q' f') :
    q = q' ∧ f = f' := by
  refine ⟨?_, funext fun x ↦ ?_⟩
  · simpa using congrArg Prod.fst (Equiv.ext_iff.1 h (1, 0))
  · simpa using congrArg Prod.snd (Equiv.ext_iff.1 h (x, 0))

lemma wr_one_zero : wr (1 : Q) (0 : Q → ZMod K) = 1 := by
  ext p <;> simp

lemma wr_inv (q : Q) (f : Q → ZMod K) :
    (wr q f)⁻¹ = wr q⁻¹ (fun x ↦ -f (q⁻¹ * x)) := by
  rw [inv_eq_iff_mul_eq_one, wr_mul, ← wr_one_zero]
  congr 1
  · simp
  · funext x
    simp

lemma wr_pow (q : Q) (f : Q → ZMod K) (n : ℕ) :
    wr q f ^ n = wr (q ^ n) (fun x ↦ ∑ i ∈ Finset.range n, f (q ^ i * x)) := by
  induction n with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact wr_one_zero.symm
  | succ n ih =>
    rw [pow_succ, ih, wr_mul, pow_succ]
    congr 1
    funext x
    rw [Finset.sum_range_succ', pow_zero, one_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pow_succ, mul_assoc]

/-- If `wr z e` commutes with `wr 1 d`, then `d` is invariant under left translation by `z`. -/
lemma invariant_of_commute {z : Q} {e d : Q → ZMod K}
    (h : wr z e * wr 1 d = wr 1 d * wr z e) (x : Q) : d (z * x) = d x := by
  rw [wr_mul, wr_mul] at h
  have := congrFun (wr_injective h).2 x
  simp only [one_mul] at this
  rw [add_comm] at this
  exact (add_left_cancel this).symm

open Classical in
/-- The indicator of `1 : Q`, with values in `ℤ/K`. -/
noncomputable def delta : Q → ZMod K := fun x ↦ if x = 1 then 1 else 0

open Classical in
/-- The number of `i < n` with `s ^ i * y = 1`, modulo `K`. -/
noncomputable def cnt (s y : Q) (n : ℕ) : ZMod K :=
  ((Finset.range n).filter fun i ↦ s ^ i * y = 1).card

lemma sum_delta (s y : Q) (n : ℕ) :
    ∑ i ∈ Finset.range n, (delta (s ^ i * y) : ZMod K) = cnt s y n := by
  classical
  simp only [delta, cnt]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma exists_of_cnt_ne_zero {s y : Q} {n : ℕ} (h : (cnt s y n : ZMod K) ≠ 0) :
    ∃ i < n, s ^ i * y = 1 := by
  classical
  by_contra hne
  simp only [not_exists, not_and] at hne
  apply h
  have : (Finset.range n).filter (fun i ↦ s ^ i * y = 1) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i hi ↦ hne i (Finset.mem_range.1 hi)
  rw [cnt]
  convert Nat.cast_zero (R := ZMod K)
  convert Finset.card_empty (α := ℕ)

lemma cnt_one_mul [Finite Q] (s : Q) (q : ℕ) :
    (cnt s 1 (orderOf s * q) : ZMod K) = q := by
  classical
  have ho : 0 < orderOf s := orderOf_pos s
  have : (Finset.range (orderOf s * q)).filter (fun i ↦ s ^ i * 1 = 1) =
      (Finset.range (orderOf s * q)).filter (orderOf s ∣ ·) := by
    ext i
    simp [orderOf_dvd_iff_pow_eq_one]
  rw [cnt]
  convert congrArg (Nat.cast (R := ZMod K)) (card_filter_dvd_range_mul _ q ho)

end WreathMod

open WreathMod

variable {α : Type u}

/-- The homomorphism `F(α) → Perm (Q × ℤ/K)`, `x ↦ wr (φ x) (f x)`. -/
noncomputable def wrHomMod {Q : Type u} [Group Q] {K : ℕ} (φ : FreeGroup α →* Q)
    (f : α → Q → ZMod K) : FreeGroup α →* Equiv.Perm (Q × ZMod K) :=
  FreeGroup.lift fun i ↦ wr (φ (FreeGroup.of i)) (f i)

lemma wrHomMod_eq {Q : Type u} [Group Q] {K : ℕ} (φ : FreeGroup α →* Q) (f : α → Q → ZMod K)
    (w : FreeGroup α) : ∃ d, wrHomMod φ f w = wr (φ w) d := by
  induction w using FreeGroup.induction_on with
  | C1 => exact ⟨0, by simp [wr_one_zero]⟩
  | of i => exact ⟨f i, by simp [wrHomMod]⟩
  | inv_of i _ =>
    exact ⟨fun x ↦ -f i ((φ (FreeGroup.of i))⁻¹ * x), by simp [wrHomMod, wr_inv]⟩
  | mul x y hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨_, by rw [map_mul, hd, hd', wr_mul, map_mul]⟩

lemma wrHomMod_of {Q : Type u} [Group Q] {K : ℕ} (φ : FreeGroup α →* Q) (f : α → Q → ZMod K)
    (i : α) : wrHomMod φ f (FreeGroup.of i) = wr (φ (FreeGroup.of i)) (f i) := by
  simp [wrHomMod]

lemma liftFinite_wrHomMod {Q : Type u} [Group Q] [Finite Q] {K : ℕ} [NeZero K]
    (φ : FreeGroup α →* Q) (f : α → Q → ZMod K) (y : FreeHat α) :
    ∃ e, liftFinite (wrHomMod φ f) y = wr (liftFinite φ y) e := by
  obtain ⟨x₀, -, hψ, hφ⟩ := exists_etaFn_eq₂ (wrHomMod φ f) φ isOpen_univ (Set.mem_univ y)
  obtain ⟨e, he⟩ := wrHomMod_eq φ f x₀
  exact ⟨e, by rw [← hψ, he, hφ]⟩

/-- The invariance argument for an element `k` of `F̂(α)` commuting with `z`. -/
lemma invariant_of_commute_hat {Q : Type u} [Group Q] [Finite Q] {K : ℕ} [NeZero K]
    (φ : FreeGroup α →* Q) (f : α → Q → ZMod K) {k z : FreeHat α} {d : Q → ZMod K}
    (hk : liftFinite (wrHomMod φ f) k = wr 1 d) (hz : z * k = k * z) (x : Q) :
    d (liftFinite φ z * x) = d x := by
  obtain ⟨e, he⟩ := liftFinite_wrHomMod φ f z
  have hc := congrArg (liftFinite (wrHomMod φ f)) hz
  rw [map_mul, map_mul, hk, he] at hc
  exact invariant_of_commute hc x

/-- **The centraliser of a nontrivial element of `A_a` lies in `A_a`.** -/
theorem mem_basisInertia_of_commute_of_mem {a : α} {x z : FreeHat α} (hx : x ∈ basisInertia a)
    (hx1 : x ≠ 1) (hz : z * x = x * z) : z ∈ basisInertia a := by
  classical
  by_contra hzA
  have hex : ∃ (P : Type u) (_ : Group P) (_ : Finite P) (f : FreeGroup α →* P),
      liftFinite f z ∉ Subgroup.zpowers (f (FreeGroup.of a)) := by
    by_contra h
    push Not at h
    exact hzA (mem_basisInertia_of fun P _ _ f ↦ h P _ _ f)
  obtain ⟨P₀, _, _, f₀, hf₀⟩ := hex
  have hex₁ : ∃ (P : Type u) (_ : Group P) (_ : Finite P) (f : FreeGroup α →* P),
      liftFinite f x ≠ 1 := by
    by_contra h
    push Not at h
    exact hx1 (eq_one_of_forall_liftFinite fun P _ _ f ↦ h P _ _ f)
  obtain ⟨P₁, _, _, f₁, hf₁⟩ := hex₁
  set φ := f₀.prod f₁
  set s := φ (FreeGroup.of a)
  set t := liftFinite φ x
  have ht1 : t ≠ 1 := by
    intro h
    apply hf₁
    have := liftFinite_comp φ (MonoidHom.snd _ _) x
    rw [MonoidHom.snd_comp_prod] at this
    rw [this]
    change t.2 = 1
    rw [h]
    rfl
  set K := orderOf t
  haveI : NeZero K := ⟨(orderOf_pos t).ne'⟩
  set f : α → (P₀ × P₁) → ZMod K := fun b ↦ if b = a then delta else 0
  set ψ := wrHomMod φ f
  have hψa : ψ (FreeGroup.of a) = wr s delta := by
    simp [ψ, wrHomMod_of, f, s]
  obtain ⟨i, hi⟩ : ∃ i : ℕ, liftFinite ψ x = wr s delta ^ i := by
    have h := liftFinite_mem_zpowers ψ hx
    rw [hψa, ← mem_powers_iff_mem_zpowers] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hi.symm⟩
  have hts : t = s ^ i := by
    obtain ⟨e, he⟩ := liftFinite_wrHomMod φ f x
    rw [hi, wr_pow] at he
    exact (wr_injective he).1.symm
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact ht1 (by rw [hts, pow_zero])
  -- `K = o / gcd(o, i)` and `i K = o q` with `q` prime to `K`
  set o := orderOf s
  set g := Nat.gcd o i
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hi0)
  have hK : K = o / g := by
    change orderOf t = _
    rw [hts, orderOf_pow' s hi0]
  set q := i / g
  have hoK : o = K * g := by rw [hK, Nat.div_mul_cancel (Nat.gcd_dvd_left o i)]
  have hiq : i = q * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right o i)).symm
  have hiK : i * K = o * q := by rw [hoK, hiq]; ring
  have hcop : Nat.Coprime K q := by
    rw [hK]
    exact Nat.coprime_div_gcd_div_gcd hg
  have hK1 : K ≠ 1 := fun h ↦ ht1 (orderOf_eq_one_iff.1 h)
  have hq : (q : ZMod K) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hK1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  -- `x ^ K` maps to `wr 1 d` with `d = cnt s · (i K)`
  have hsK : s ^ (i * K) = 1 := by rw [pow_mul, ← hts, pow_orderOf_eq_one]
  have hk : liftFinite ψ (x ^ K) = wr 1 (fun y ↦ cnt s y (i * K)) := by
    rw [map_pow, hi, ← pow_mul, wr_pow, hsK]
    congr 1
    funext y
    exact sum_delta s y _
  have hkz : z * x ^ K = x ^ K * z := ((Commute.pow_right hz) K : _)
  have hinv := invariant_of_commute_hat φ f hk hkz 1
  rw [mul_one, hiK, WreathMod.cnt_one_mul] at hinv
  obtain ⟨j, -, hj⟩ := exists_of_cnt_ne_zero (hinv.symm ▸ hq)
  apply hf₀
  have hzs : liftFinite φ z = (s ^ j)⁻¹ := eq_inv_of_mul_eq_one_right hj
  have hfst := liftFinite_comp φ (MonoidHom.fst _ _) z
  rw [MonoidHom.fst_comp_prod, hzs] at hfst
  rw [hfst]
  simp only [MonoidHom.coe_fst, Prod.fst_inv, Prod.pow_fst]
  exact inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)




/-! ### Transport along isomorphisms -/

/-- The centraliser property transports along `comap` by an isomorphism. -/
lemma mem_comap_of_commute {G H : Type*} [Group G] [Group H] (e : G ≃* H) {B : Subgroup H}
    (hB : ∀ {x z : H}, x ∈ B → x ≠ 1 → z * x = x * z → z ∈ B) {x z : G}
    (hx : x ∈ B.comap e.toMonoidHom) (hx1 : x ≠ 1) (hz : z * x = x * z) :
    z ∈ B.comap e.toMonoidHom := by
  refine hB hx (fun h ↦ hx1 (e.injective (h.trans (map_one e).symm))) ?_
  change e z * e x = e x * e z
  rw [← map_mul, ← map_mul, hz]

/-! ### The once-punctured case -/

section One

open Pi1 Pi1.SurfaceGroup Pi1.ReidemeisterSchreier

attribute [local instance] Pi1.SurfaceGroup.sheetAction

variable {g : ℕ}

/-- The cocycle along an integer power of an element fixing `ω`. -/
lemma coc_zpow_of_smul_eq {β Ω G : Type*} [MulAction (FreeGroup β) Ω] [Group G]
    {lab : Ω → β → G} {w : FreeGroup β} {ω : Ω} (hw : w • ω = ω) (k : ℤ) :
    coc lab (w ^ k) ω = coc lab w ω ^ k := by
  have := map_zpow (cocHom lab ω) ⟨w, hw⟩ k
  simpa using this

/-- **An element centralising a nontrivial element of `⟨w⟩‾` lies in `N̂`**: it is killed by
the character `χ₃`. -/
theorem chiThree_eq_one_of_commute {x z : FreeHat (SurfaceGen (g + 1) 0)}
    (hx : x ∈ cuspInertiaF g) (hx1 : x ≠ 1) (hz : z * x = x * z) :
    liftFinite chiThree z = 1 := by
  by_contra hχ
  apply hx1
  refine eq_one_of_forall_liftFinite fun P _ _ f ↦ ?_
  set W := cuspWord (g + 1)
  set M := orderOf (f W)
  haveI : NeZero M := ⟨(orderOf_pos _).ne'⟩
  set φ := extAction (countLab (g := g) M)
  set ψ := f.prod φ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (liftFinite_mem_zpowers_of_mem ψ hx)
  have hfx : liftFinite f x = f W ^ i := by
    have := liftFinite_comp ψ (MonoidHom.fst _ _) x
    rw [MonoidHom.fst_comp_prod] at this
    rw [this, ← hi]
    simp [ψ, W]
  have hφx : liftFinite φ x = φ W ^ i := by
    have := liftFinite_comp ψ (MonoidHom.snd _ _) x
    rw [MonoidHom.snd_comp_prod] at this
    rw [this, ← hi]
    simp [ψ, W]
  obtain ⟨x₀, -, hφx₀, hχx₀⟩ := exists_etaFn_eq₂ φ chiThree isOpen_univ (Set.mem_univ z)
  have hc := congrArg (liftFinite φ) hz
  rw [map_mul, map_mul, ← hφx₀, hφx, ← map_zpow, ← map_mul, ← map_mul] at hc
  have h3 := congrArg (fun p ↦ (p ((0 : ZMod 3), (1 : Multiplicative (ZMod M)))).2) hc
  simp only [φ, extAction_apply, mul_one] at h3
  have hWω : ∀ ω : ZMod 3, W • ω = ω := fun ω ↦ by simpa using cuspWord_pow_smul (g := g) 1 ω
  have hW0 : W ^ i • (0 : ZMod 3) = 0 := MulAction.mem_stabilizer_iff.1
    (Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.2 (hWω 0)) i)
  have hc0 : coc (countLab (g := g) M) (W ^ i) 0 = 1 := by
    rw [coc_zpow_of_smul_eq (hWω 0), coc_countLab, show (0 : ZMod 3) - 1 = 2 from rfl,
      countLab_ne _ (show (2 : ZMod 3) ≠ 1 by decide),
      countLab_ne _ (show (0 : ZMod 3) ≠ 1 by decide), inv_one, mul_one, one_zpow]
  rw [coc_mul, coc_mul, hW0, hc0, mul_one] at h3
  have h4 : coc (countLab (g := g) M) (W ^ i) (x₀ • 0) = 1 :=
    mul_right_cancel (h3.symm.trans (one_mul _).symm)
  rw [coc_zpow_of_smul_eq (hWω _), coc_countLab, smul_def, add_zero] at h4
  have hne : Multiplicative.toAdd (chiThree x₀) ≠ 0 := by
    intro h0
    apply hχ
    rw [← hχx₀, ← ofAdd_toAdd (chiThree x₀), h0, ofAdd_zero]
  have hdvd : (M : ℤ) ∣ i := by
    rw [← orderOf_ofAdd_one M]
    apply orderOf_dvd_iff_zpow_eq_one.2
    generalize Multiplicative.toAdd (chiThree x₀) = k at h4 hne
    have hk : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hk k with rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [show (1 : ZMod 3) - 1 = 0 from rfl, countLab_ne _ (show (0 : ZMod 3) ≠ 1 by decide),
        countLab_one, one_mul, inv_zpow'] at h4
      rwa [zpow_neg, inv_eq_one] at h4
    · rw [show (2 : ZMod 3) - 1 = 1 from rfl, countLab_ne _ (show (2 : ZMod 3) ≠ 1 by decide),
        countLab_one, inv_one, mul_one] at h4
      exact h4
  rw [hfx]
  exact orderOf_dvd_iff_zpow_eq_one.1 hdvd

/-- **The centraliser of a nontrivial element of `⟨w⟩‾ ⊆ F̂(a₁, b₁, …)` lies in `⟨w⟩‾`.** -/
theorem mem_cuspInertiaF_of_commute {x z : FreeHat (SurfaceGen (g + 1) 0)}
    (hx : x ∈ cuspInertiaF g) (hx1 : x ≠ 1) (hz : z * x = x * z) : z ∈ cuspInertiaF g := by
  obtain ⟨δ, rfl⟩ := mem_range_cuspEmb (chiThree_eq_one_of_commute hx hx1 hz)
  obtain ⟨x', hx', rfl⟩ := le_map_cuspEmb hx
  have hx'1 : x' ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  have hc : δ * x' = x' * δ := cuspEmb_injective (by rw [map_mul, map_mul]; exact hz)
  have := mem_basisInertia_of_commute_of_mem hx' hx'1 hc
  rw [← comap_cuspEmb] at this
  exact this

/-- **Centraliser property of the cusp of `Π̂_{g,1}`** (`g ≥ 1`). -/
theorem mem_inertia_one_of_commute {g : ℕ} (hg : 0 < g) {x z : ProfiniteSurfaceGroup g 1}
    (hx : x ∈ inertia (g := g) 0) (hx1 : x ≠ 1) (hz : z * x = x * z) :
    z ∈ inertia (g := g) 0 := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  rw [inertia_one_eq_comap] at hx ⊢
  exact mem_comap_of_commute _ (fun hx hx1 hz ↦ mem_cuspInertiaF_of_commute hx hx1 hz) hx hx1 hz

end One

/-! ### At least two cusps -/

open Pi1 Pi1.SurfaceGroup in
/-- **Centraliser property of the cusps of `Π̂_{g,r+2}`.** -/
theorem mem_inertia_two_of_commute {g r : ℕ} (k : Fin (r + 2))
    {x z : ProfiniteSurfaceGroup g (r + 2)} (hx : x ∈ inertia (g := g) k) (hx1 : x ≠ 1)
    (hz : z * x = x * z) : z ∈ inertia (g := g) k := by
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_isConj_cusp (g := g) (Equiv.swap k 0)
  obtain ⟨c, hc⟩ := isConj_iff.1 (hθ k)
  rw [Equiv.swap_apply_left] at hc
  let ψ : SurfaceGroup g (r + 2) ≃* SurfaceGroup g (r + 2) := θ.trans (MulAut.conj c)
  have hψ : ψ (cusp k) = cusp 0 := by
    simp only [ψ, MulEquiv.trans_apply, MulAut.conj_apply]
    exact hc
  let e := completionCongr ψ
  have he : e (etaFn _ (cusp k)) = etaFn (GrpCat.of (SurfaceGroup g (r + 2))) (cusp 0) := by
    simp only [e, completionCongr_apply, completionMap_eta, MulEquiv.coe_toMonoidHom, hψ]
  have hI : inertia (g := g) k =
      (inertia (g := g) (r := r + 2) 0).comap e.toMulEquiv.toMonoidHom := by
    rw [inertia, inertia, ← comap_topologicalClosure_zpowers e, he]
  have h0 : inertia (g := g) (r := r + 2) 0 =
      (Profinite.basisInertia (SurfaceGen.c (0 : Fin (r + 1)))).comap
        (profiniteFreeEquiv (g := g) (r := r + 1)).toMulEquiv.toMonoidHom :=
    inertia_castSucc_eq_comap (g := g) (r := r + 1) 0
  rw [hI] at hx ⊢
  refine mem_comap_of_commute _ (fun hx hx1 hz ↦ ?_) hx hx1 hz
  rw [h0] at hx ⊢
  exact mem_comap_of_commute _ (fun hx hx1 hz ↦ mem_basisInertia_of_commute_of_mem hx hx1 hz)
    hx hx1 hz

open Pi1 Pi1.SurfaceGroup in
/-- **The centraliser property of cuspidal inertia** ([AbsTopI] Lemma 4.1 (i)): for `(g, r)`
hyperbolic with `r ≥ 1`, an element of `Π̂_{g,r}` commuting with a nontrivial element of a
cuspidal inertia group `Iⱼ` lies in `Iⱼ`. -/
theorem mem_inertia_of_commute {g r : ℕ} (hr : 0 < r) (h : IsHyperbolic g r) (j : Fin r)
    {x z : ProfiniteSurfaceGroup g r} (hx : x ∈ inertia (g := g) j) (hx1 : x ≠ 1)
    (hz : z * x = x * z) : z ∈ inertia (g := g) j := by
  rcases r with _ | _ | r
  · omega
  · obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    exact mem_inertia_one_of_commute (by unfold IsHyperbolic at h; omega) hx hx1 hz
  · exact mem_inertia_two_of_commute j hx hx1 hz

open Pi1 Pi1.SurfaceGroup in
/-- The centraliser of a nontrivial element of a cuspidal inertia group `Iⱼ` lies in `Iⱼ`. -/
theorem centralizer_le_inertia {g r : ℕ} (hr : 0 < r) (h : IsHyperbolic g r) (j : Fin r)
    {x : ProfiniteSurfaceGroup g r} (hx : x ∈ inertia (g := g) j) (hx1 : x ≠ 1) :
    Subgroup.centralizer {x} ≤ inertia (g := g) j := fun _ hz ↦
  mem_inertia_of_commute hr h j hx hx1 (Subgroup.mem_centralizer_singleton_iff.1 hz)

end CurvesJacobian.CuspChar
