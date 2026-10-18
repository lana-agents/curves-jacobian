/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ChainPushOps

/-!
# Objects and operations of concatenated paths (MR8.5)

To read off the cuspidalisation candidate of a Belyi chain built as an
`Belyi.Anabelian.OpPath` ([AbsTopII] Corollary 3.7 (a), `Topics in Absolute Anabelian Geometry
II.txt` l.4743–4753), the `n`-th object and operation of a concatenation are identified with those
of the pieces:

* `OpPath.objN_append_left`, `OpPath.objN_append_right`, `OpPath.opN_append_left_heq`,
  `OpPath.opN_append_right_heq`, `OpPath.objN_ofSeq`, `OpPath.opN_ofSeq_heq`;
* `OpPath.objN_belyiPath`, `OpPath.opN_belyiPath_heq`, `OpPath.objN_belyiPath_last`,
  `OpPath.opN_belyiPath_last_heq`: inside the second run and at the last operation of a Belyi
  path;
* `ElemOp.decuspHom_heq`, `ElemOp.quotHom_heq`, `ElemOp.decuspHom_push`: the operation
  homomorphisms are compatible with these identifications (`ChainObj.equivOfEq`);
* `PiChain.objCongr_eq_equivOfEq`.
-/

universe u

noncomputable section

namespace Belyi.Anabelian

variable {E : CuspidalExt.{u}}

namespace ChainObj

lemma equivOfEq_trans {A B C : ChainObj E} (h₁ : A = B) (h₂ : B = C) (x : A.grp) :
    equivOfEq h₂ (equivOfEq h₁ x) = equivOfEq (h₁.trans h₂) x := by
  subst h₁ h₂
  rfl

lemma equivOfEq_rfl {A : ChainObj E} (h : A = A) (x : A.grp) : equivOfEq h x = x := rfl

end ChainObj

namespace ElemOp

/-- `decuspHom` along equalities of objects and a heterogeneous equality of operations. -/
lemma decuspHom_heq {A B A' B' : ChainObj E} (o : ElemOp A B) (o' : ElemOp A' B') (hA : A = A')
    (hB : B = B') (h : HEq o o') (k : o.kind = .decusp) (k' : o'.kind = .decusp) (x : A.grp) :
    ChainObj.equivOfEq hB (o.decuspHom k x) = o'.decuspHom k' (ChainObj.equivOfEq hA x) := by
  subst hA hB
  obtain rfl := eq_of_heq h
  rfl

/-- `quotHom` along equalities of objects and a heterogeneous equality of operations. -/
lemma quotHom_heq {A B A' B' : ChainObj E} (o : ElemOp A B) (o' : ElemOp A' B') (hA : A = A')
    (hB : B = B') (h : HEq o o') (k : o.kind = .quot) (k' : o'.kind = .quot) (x : A.grp) :
    ChainObj.equivOfEq hB (o.quotHom k x) = o'.quotHom k' (ChainObj.equivOfEq hA x) := by
  subst hA hB
  obtain rfl := eq_of_heq h
  rfl

variable {E' : CuspidalExt.{u}} {A : ChainObj E} {j : A.grp →ₜ* E'.Pi} {hj : IsOpen (Set.range j)}
  {ι : E'.G →ₜ* E.G} {hι : Function.Injective ι} {hιo : IsOpen (Set.range ι)}
  {hcomp : ∀ x, ι (E'.pr (j x)) = A.toG x}

/-- Pushing an operation does not change its operation homomorphism. -/
lemma decuspHom_push (hc : A.CuspMatch j) {B₁ B₂ : ChainObj E'} :
    ∀ (o : ElemOp B₁ B₂) (k : o.kind = .decusp) (k' : (o.push (hj := hj) (hι := hι) (hιo := hιo)
      (hcomp := hcomp) hc).kind = .decusp), (o.push hc).decuspHom k' = o.decuspHom k
  | .decusp .., _, _ => rfl
  | .cover .., k, _ => absurd k (by simp [kind])
  | .quot .., k, _ => absurd k (by simp [kind])
  | .deorb .., k, _ => absurd k (by simp [kind])

end ElemOp

namespace OpPath

theorem objN_append_left : ∀ {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) (k : ℕ),
    k ≤ p.length → (p.append q).objN k = p.objN k
  | _, _, _, nil _, _, k, hk => by
    obtain rfl : k = 0 := by simpa [length] using hk
    rfl
  | _, _, _, cons _ _, _, 0, _ => rfl
  | _, _, _, cons _ p, q, k + 1, hk => objN_append_left p q k (by simp only [length] at hk; omega)

theorem objN_append_right : ∀ {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) (k : ℕ),
    (p.append q).objN (p.length + k) = q.objN k
  | _, _, _, nil _, q, k => by
    change objN (0 + k) q = objN k q
    rw [Nat.zero_add]
  | _, _, _, cons _ p, q, k => by
    rw [show (cons _ p).length + k = (p.length + k) + 1 by simp only [length]; omega]
    exact objN_append_right p q k

theorem opN_congr_heq {A C : ChainObj E} (p : OpPath A C) {a b : ℕ} (hab : a = b)
    (ha : a < p.length) (hb : b < p.length) : HEq (p.opN a ha) (p.opN b hb) := by
  subst hab
  rfl

theorem opN_append_left_heq : ∀ {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) (k : ℕ)
    (hk : k < p.length) (h' : k < (p.append q).length),
    HEq ((p.append q).opN k h') (p.opN k hk)
  | _, _, _, nil _, _, _, hk, _ => absurd hk (by simp [length])
  | _, _, _, cons _ _, _, 0, _, _ => HEq.rfl
  | _, _, _, cons _ p, q, k + 1, hk, _ =>
    opN_append_left_heq p q k (by simp only [length] at hk; omega) _

theorem opN_append_right_heq : ∀ {A B C : ChainObj E} (p : OpPath A B) (q : OpPath B C) (k : ℕ)
    (hk : k < q.length) (h' : p.length + k < (p.append q).length),
    HEq ((p.append q).opN (p.length + k) h') (q.opN k hk)
  | _, _, _, nil _, q, k, hk, h' =>
    opN_congr_heq q (Nat.zero_add k) h' hk
  | _, _, _, cons o p, q, k, hk, h' => by
    have e : (cons o p).length + k = (p.length + k) + 1 := by simp only [length]; omega
    refine (opN_congr_heq ((cons o p).append q) e h' (by rw [← e]; exact h')).trans ?_
    exact opN_append_right_heq p q k hk _

theorem objN_ofSeq : ∀ (r : ℕ) (f : (i : ℕ) → i ≤ r → ChainObj E)
    (g : ∀ i (h : i < r), ElemOp (f i h.le) (f (i + 1) h)) (k : ℕ) (hk : k ≤ r),
    (ofSeq r f g).objN k = f k hk
  | 0, f, g, k, hk => by
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    rfl
  | r + 1, f, g, k, hk => by
    rcases Nat.lt_or_ge k (r + 1) with h | h
    · rw [ofSeq, objN_append_left _ _ k (by rw [length_ofSeq]; omega),
        objN_ofSeq r _ _ k (by omega)]
    · obtain rfl : k = r + 1 := le_antisymm hk h
      have := objN_append_right (ofSeq r (fun i h ↦ f i (h.trans (Nat.le_succ r)))
        (fun i h ↦ g i (h.trans (Nat.lt_succ_self r)))) (single (g r (Nat.lt_succ_self r))) 1
      rw [length_ofSeq] at this
      exact this

theorem opN_ofSeq_heq : ∀ (r : ℕ) (f : (i : ℕ) → i ≤ r → ChainObj E)
    (g : ∀ i (h : i < r), ElemOp (f i h.le) (f (i + 1) h)) (k : ℕ) (hk : k < r)
    (h' : k < (ofSeq r f g).length), HEq ((ofSeq r f g).opN k h') (g k hk)
  | 0, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | r + 1, f, g, k, hk, h' => by
    rcases Nat.lt_or_ge k r with h | h
    · exact (opN_append_left_heq _ _ k (by rw [length_ofSeq]; exact h) h').trans
        (opN_ofSeq_heq r _ _ k h _)
    · obtain rfl : k = r := le_antisymm (Nat.lt_succ_iff.1 hk) h
      have e : (ofSeq k (fun i h ↦ f i (h.trans (Nat.le_succ k)))
          (fun i h ↦ g i (h.trans (Nat.lt_succ_self k)))).length + 0 = k := by
        rw [length_ofSeq, Nat.add_zero]
      refine (opN_congr_heq _ e.symm h' (by rw [e]; exact h')).trans ?_
      exact opN_append_right_heq _ (single (g k (Nat.lt_succ_self k))) 0 Nat.one_pos _

variable {A₁ A₂ A₃ A₄ A₅ A₆ : ChainObj E} (o₁ : ElemOp (ChainObj.base E) A₁)
  (o₂ : ElemOp A₁ A₂) (r₁ : OpPath A₂ A₃) (o₃ : ElemOp A₃ A₄) (r₂ : OpPath A₄ A₅)
  (o₄ : ElemOp A₅ A₆)

/-- The objects of the second run of a Belyi path. -/
theorem objN_belyiPath (k : ℕ) (hk : k ≤ r₂.length) :
    (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).objN (r₁.length + 3 + k) = r₂.objN k := by
  rw [show r₁.length + 3 + k = (r₁.length + (k + 1)) + 1 + 1 by omega]
  change (r₁.append (cons o₃ (r₂.append (single o₄)))).objN (r₁.length + (k + 1)) = _
  rw [objN_append_right]
  exact objN_append_left r₂ (single o₄) k hk

/-- The operations of the second run of a Belyi path. -/
theorem opN_belyiPath_heq (k : ℕ) (hk : k < r₂.length)
    (h' : r₁.length + 3 + k < (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).length) :
    HEq ((belyiPath o₁ o₂ r₁ o₃ r₂ o₄).opN (r₁.length + 3 + k) h') (r₂.opN k hk) := by
  have e : r₁.length + 3 + k = (r₁.length + (k + 1)) + 1 + 1 := by omega
  refine (opN_congr_heq _ e h' (by rw [← e]; exact h')).trans ?_
  change HEq ((r₁.append (cons o₃ (r₂.append (single o₄)))).opN (r₁.length + (k + 1)) _) _
  have hl : k + 1 < (cons o₃ (r₂.append (single o₄))).length := by
    simp only [length, length_append, length_single]
    omega
  refine (opN_append_right_heq r₁ _ (k + 1) hl _).trans ?_
  exact opN_append_left_heq r₂ (single o₄) k hk _

/-- The second to last object of a Belyi path. -/
theorem objN_belyiPath_last :
    (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).objN (r₁.length + r₂.length + 3) = A₅ := by
  rw [show r₁.length + r₂.length + 3 = r₁.length + 3 + r₂.length by omega,
    objN_belyiPath o₁ o₂ r₁ o₃ r₂ o₄ r₂.length le_rfl]
  exact objN_length r₂

/-- The last operation of a Belyi path. -/
theorem opN_belyiPath_last_heq
    (h' : r₁.length + r₂.length + 3 < (belyiPath o₁ o₂ r₁ o₃ r₂ o₄).length) :
    HEq ((belyiPath o₁ o₂ r₁ o₃ r₂ o₄).opN (r₁.length + r₂.length + 3) h') o₄ := by
  have e : r₁.length + r₂.length + 3 = (r₁.length + (r₂.length + 1)) + 1 + 1 := by omega
  refine (opN_congr_heq _ e h' (by rw [← e]; exact h')).trans ?_
  change HEq ((r₁.append (cons o₃ (r₂.append (single o₄)))).opN (r₁.length + (r₂.length + 1)) _) _
  have hl : r₂.length + 1 < (cons o₃ (r₂.append (single o₄))).length := by
    simp only [length, length_append, length_single]
    omega
  refine (opN_append_right_heq r₁ _ (r₂.length + 1) hl _).trans ?_
  change HEq ((r₂.append (single o₄)).opN (r₂.length + 0) _) _
  exact opN_append_right_heq r₂ (single o₄) 0 Nat.one_pos _

end OpPath

namespace PiChain

/-- `objCongr` is `equivOfEq`. -/
lemma objCongr_eq_equivOfEq (c : PiChain E) {a b : ℕ} (hab : a = b) (ha : a ≤ c.len)
    (hb : b ≤ c.len) (x) :
    c.objCongr hab ha hb x = ChainObj.equivOfEq (by subst hab; rfl) x := by
  subst hab
  rfl

end PiChain

end Belyi.Anabelian
