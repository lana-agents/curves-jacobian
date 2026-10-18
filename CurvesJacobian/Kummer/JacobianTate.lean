/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.PicTorsionCount

/-!
# Divisibility of the torsion of `J(k̄)` and the Tate module

Let `A` be an abelian group whose `n`-torsion `A[n]` has `n^r` elements for every `n ≥ 1` (for
`A = Pic(K(X))` of a curve `X` of genus `g` over an algebraically closed field of characteristic
`0`, `r = 2g`: `natCard_picTorsion`). Then:

* `CurvesJacobian.Tate.exists_nsmul_eq_of_mem_torsion`: multiplication by `m` maps `A[nm]` onto
  `A[n]` (count: the kernel is `A[m]`, so the image has `(nm)^r / m^r = n^r` elements); in
  particular the torsion subgroup of `A` is divisible;
* `CurvesJacobian.Tate.tateModule A ℓ`: the `ℓ`-adic Tate module `T_ℓ A = lim (A[ℓ^m], ·ℓ)`, as
  the group of sequences `(x_m)` with `ℓ^m x_m = 0` and `ℓ x_{m+1} = x_m`;
* `CurvesJacobian.Tate.tateProj_surjective`: every `x ∈ A[ℓ^m]` is the `m`-th component of a point
  of `T_ℓ A` (the transition maps are onto);
* `CurvesJacobian.Tate.tateMap`: an additive map `A → A` acts on `T_ℓ A` (the Galois action
  `picAct` of `G_k` on `J(k̄)`, `Kummer/PicAction.lean`, gives the Galois representation on
  `T_ℓ J`).

For `X` a curve over an algebraically closed field of characteristic `0`:
`CurvesJacobian.Tate.exists_nsmul_eq_of_mem_picTorsion` (`J(k̄)[nm] ↠ J(k̄)[n]`) and
`CurvesJacobian.Tate.tateProj_surjective_pic`.

Divisibility of all of `J(k̄)` (not only of its torsion) needs the abelian variety `J` (or
`Pic/n ↪ H²(Δ_X, μ_n)`); it is not used here (continuous-kummer-theory `Plans/MR5Plan.md` §10,
JAC-4a).
-/

namespace CurvesJacobian.Tate

variable {A : Type*} [AddCommGroup A]

/-- `A[n]`. -/
abbrev torsionBy (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).ker

lemma mem_torsionBy {n : ℕ} {x : A} : x ∈ torsionBy A n ↔ n • x = 0 := Iff.rfl

/-- `x ↦ m x`, `A[nm] → A[n]`. -/
def mulTorsion (n m : ℕ) : torsionBy A (n * m) →+ torsionBy A n where
  toFun x := ⟨m • (x : A), by
    change n • m • (x : A) = 0
    rw [smul_smul]
    exact x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

lemma ker_mulTorsion (n m : ℕ) :
    (mulTorsion (A := A) n m).ker = (torsionBy A m).addSubgroupOf (torsionBy A (n * m)) := by
  ext x
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

variable {r : ℕ}

/-- **`m · A[nm] = A[n]`** when `#A[d] = d^r` for all `d ≥ 1`. -/
theorem mulTorsion_surjective (hcard : ∀ d : ℕ, 0 < d → Nat.card (torsionBy A d) = d ^ r)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : Function.Surjective (mulTorsion (A := A) n m) := by
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hfin : ∀ d : ℕ, 0 < d → Finite (torsionBy A d) := fun d hd =>
    Nat.finite_of_card_ne_zero (by rw [hcard d hd]; exact pow_ne_zero _ hd.ne')
  haveI := hfin n hn
  haveI := hfin (n * m) hnm
  have hkm : Nat.card (mulTorsion (A := A) n m).ker = m ^ r := by
    have hle : torsionBy A m ≤ torsionBy A (n * m) := by
      intro x hx
      change (n * m) • x = 0
      rw [← smul_smul, show m • x = 0 from hx, smul_zero]
    rw [ker_mulTorsion, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv,
      hcard m hm]
  have hmul := AddSubgroup.card_mul_index (mulTorsion (A := A) n m).ker
  rw [AddSubgroup.index_ker, hkm, hcard (n * m) hnm, mul_pow, mul_comm] at hmul
  have hrange : Nat.card (mulTorsion (A := A) n m).range = n ^ r :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hm r) hmul
  have htop : (mulTorsion (A := A) n m).range = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [hrange, hcard n hn])
  intro x
  exact AddMonoidHom.mem_range.1 (htop ▸ AddSubgroup.mem_top x)

/-- Every `x ∈ A[n]` is `m • y` for some `y ∈ A[nm]`. -/
theorem exists_nsmul_eq_of_mem_torsion (hcard : ∀ d : ℕ, 0 < d → Nat.card (torsionBy A d) = d ^ r)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {x : A} (hx : x ∈ torsionBy A n) :
    ∃ y ∈ torsionBy A (n * m), m • y = x := by
  obtain ⟨y, hy⟩ := mulTorsion_surjective hcard hn hm ⟨x, hx⟩
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

/-- **The ℓ-adic Tate module** `T_ℓ A = lim (A[ℓ^m], ·ℓ)`: sequences `(x_m)` with `ℓ^m x_m = 0`
and `ℓ x_{m+1} = x_m`. -/
def tateModule (A : Type*) [AddCommGroup A] (ℓ : ℕ) : AddSubgroup (ℕ → A) where
  carrier := {s | ∀ m, ℓ ^ m • s m = 0 ∧ ℓ • s (m + 1) = s m}
  zero_mem' m := by simp
  add_mem' {s t} hs ht m := by
    simp only [Pi.add_apply, smul_add, (hs m).1, (ht m).1, (hs m).2, (ht m).2, add_zero, and_self]
  neg_mem' {s} hs m := by
    simp only [Pi.neg_apply, smul_neg, (hs m).1, (hs m).2, neg_zero, and_self]

/-- The projection `T_ℓ A → A[ℓ^m]`. -/
def tateProj (ℓ m : ℕ) : tateModule A ℓ →+ torsionBy A (ℓ ^ m) where
  toFun s := ⟨(s : ℕ → A) m, (s.2 m).1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The sequence `x_j = ℓ^{m-j} x` for `j ≤ m`, lifted step by step above `m`. -/
theorem tateProj_surjective (hcard : ∀ d : ℕ, 0 < d → Nat.card (torsionBy A d) = d ^ r)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) : Function.Surjective (tateProj (A := A) ℓ m) := by
  -- one lifting step
  have lift : ∀ j (y : torsionBy A (ℓ ^ j)), ∃ z : torsionBy A (ℓ ^ (j + 1)), ℓ • (z : A) = y := by
    intro j y
    obtain ⟨z, hz, hzy⟩ := exists_nsmul_eq_of_mem_torsion hcard (pow_pos hℓ j) hℓ y.2
    exact ⟨⟨z, by rwa [pow_succ]⟩, hzy⟩
  choose L hL using lift
  rintro ⟨x, hx⟩
  -- the lifts above `m`
  let up : (i : ℕ) → torsionBy A (ℓ ^ (m + i)) := fun i =>
    Nat.rec (motive := fun i => torsionBy A (ℓ ^ (m + i))) ⟨x, hx⟩ (fun i y => L (m + i) y) i
  have hup : ∀ i, ℓ • (up (i + 1) : A) = (up i : A) := fun i => hL (m + i) (up i)
  let s : ℕ → A := fun j => if h : m ≤ j then (up (j - m) : A) else ℓ ^ (m - j) • x
  have hs_le : ∀ j, m ≤ j → s j = up (j - m) := fun j h => dif_pos h
  have hs_lt : ∀ j, ¬ m ≤ j → s j = ℓ ^ (m - j) • x := fun j h => dif_neg h
  refine ⟨⟨s, fun j => ⟨?_, ?_⟩⟩, ?_⟩
  · by_cases h : m ≤ j
    · rw [hs_le j h, show ℓ ^ j = ℓ ^ (m + (j - m)) by rw [Nat.add_sub_cancel' h]]
      exact (up (j - m)).2
    · rw [hs_lt j h, smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega)]
      exact hx
  · by_cases h : m ≤ j
    · rw [hs_le j h, hs_le (j + 1) (by omega), Nat.sub_add_comm h]
      exact hup _
    · by_cases h' : m = j + 1
      · subst h'
        rw [hs_le _ le_rfl, hs_lt j h, Nat.sub_self, Nat.add_sub_cancel_left, pow_one]
        rfl
      · rw [hs_lt j h, hs_lt (j + 1) (by omega), smul_smul, ← pow_succ']
        congr 2
        omega
  · ext
    change s m = x
    rw [hs_le m le_rfl, Nat.sub_self]
    rfl

/-- An additive endomorphism acts on the Tate module (componentwise). -/
def tateMap (ℓ : ℕ) (f : A →+ A) : tateModule A ℓ →+ tateModule A ℓ where
  toFun s := ⟨fun j => f ((s : ℕ → A) j), fun j => ⟨by rw [← map_nsmul, (s.2 j).1, map_zero],
    by rw [← map_nsmul, (s.2 j).2]⟩⟩
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

lemma tateProj_tateMap (ℓ m : ℕ) (f : A →+ A) (s : tateModule A ℓ) :
    ((tateProj ℓ m (tateMap ℓ f s) : torsionBy A (ℓ ^ m)) : A) = f (tateProj ℓ m s : A) :=
  rfl

section Curve

open CategoryTheory AlgebraicGeometry Belyi WeilCurves.FunctionField

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- `#J(k̄)[d] = d^{2g}` in the form used above. -/
lemma natCard_torsionBy_pic (d : ℕ) (hd : 0 < d) :
    Nat.card (torsionBy (Pic k X.functionField) d) = d ^ (2 * (curveGenus k X).toNat) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  exact natCard_picTorsion d

/-- **`m · J(k̄)[nm] = J(k̄)[n]`** for a curve over an algebraically closed field of
characteristic `0`. -/
theorem exists_nsmul_eq_of_mem_picTorsion {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {x : Pic k X.functionField} (hx : x ∈ picTorsion k X.functionField n) :
    ∃ y ∈ picTorsion k X.functionField (n * m), m • y = x :=
  exists_nsmul_eq_of_mem_torsion natCard_torsionBy_pic hn hm hx

/-- The projections `T_ℓ J → J[ℓ^m]` are onto. -/
theorem tateProj_surjective_pic {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) :
    Function.Surjective (tateProj (A := Pic k X.functionField) ℓ m) :=
  tateProj_surjective natCard_torsionBy_pic hℓ m

end Curve

end CurvesJacobian.Tate
