/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.ZHat

/-!
# Functoriality of the Kummer completion `(Kˣ)^∧`

For a ring homomorphism `φ : k →+* K` of fields of characteristic `0`,
`CurvesJacobian.Kummer.completionMap φ : (kˣ)^∧ → (Kˣ)^∧` is the map induced levelwise by
`kˣ/(kˣ)ⁿ → Kˣ/(Kˣ)ⁿ`. For `φ = algebraMap k K` it is the map `η ↦ η|_{G_K}` of
[AbsTopIII] Prop. 1.8(ii) under `H¹(G_k, Ẑ(1)) ≅ (kˣ)^∧`.
-/

open KummerTheory

namespace CurvesJacobian.Kummer

variable {k K : Type*} [Field k] [Field K] [CharZero k] [CharZero K]

/-- The index `n` of `(kˣ)^∧` viewed over another field of characteristic `0`. -/
def reindex (i : KummerIndex K) : KummerIndex k := ⟨i.n, Nat.cast_ne_zero.mpr i.n_ne_zero⟩

/-- `kˣ/(kˣ)ⁿ → Kˣ/(Kˣ)ⁿ` induced by `φ`. -/
noncomputable def quotMap (φ : k →+* K) (n : ℕ) :
    kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range →* Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range :=
  QuotientGroup.map _ _ (Units.map (φ : k →* K)) <| by
    rintro _ ⟨b, rfl⟩
    exact ⟨Units.map (φ : k →* K) b, by simp⟩

omit [CharZero k] [CharZero K] in
@[simp]
lemma quotMap_mk (φ : k →+* K) (n : ℕ) (a : kˣ) :
    quotMap φ n (QuotientGroup.mk a) = QuotientGroup.mk (Units.map (φ : k →* K) a) := rfl

omit [CharZero k] [CharZero K] in
lemma quotTransition_quotMap (φ : k →+* K) {m n : ℕ} (h : m ∣ n)
    (x : kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range) :
    quotTransition K h (quotMap φ n x) = quotMap φ m (quotTransition k h x) := by
  induction x using QuotientGroup.induction_on with
  | H a => rfl

/-- **Functoriality of `(kˣ)^∧`**: the map `(kˣ)^∧ → (Kˣ)^∧` induced by `φ : k →+* K`. -/
noncomputable def completionMap (φ : k →+* K) : KummerCompletion k →* KummerCompletion K where
  toFun x := ⟨fun i => quotMap φ i.n (x.1 (reindex i)), fun i j h => by
    change quotTransition K h (quotMap φ j.n (x.1 (reindex j))) = quotMap φ i.n (x.1 (reindex i))
    rw [quotTransition_quotMap]
    congr 1
    exact x.2 (reindex i) (reindex j) h⟩
  map_one' := Subtype.ext (funext fun i => by
    change quotMap φ i.n ((1 : KummerCompletion k).1 (reindex i)) = 1
    exact map_one _)
  map_mul' x y := Subtype.ext (funext fun i => map_mul (quotMap φ i.n) _ _)

omit [CharZero K] in
lemma completionMap_apply (φ : k →+* K) (x : KummerCompletion k) (i : KummerIndex K) :
    (completionMap φ x).1 i = quotMap φ i.n (x.1 (reindex i)) := rfl

omit [CharZero K] in
lemma completionMap_toKummerCompletion (φ : k →+* K) (a : kˣ) :
    completionMap φ (toKummerCompletion k a) = toKummerCompletion K (Units.map (φ : k →* K) a) :=
  rfl

end CurvesJacobian.Kummer
