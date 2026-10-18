/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.CompletionMap
import ContinuousKummerTheory.Kummer.Faithful

/-!
# Descent of Kummer completions along finite extensions

Let `K/k` be a finite extension of fields of characteristic `0`, with `k` torally
Kummer-faithful. If the image of `c ∈ (kˣ)^∧` in `(Kˣ)^∧` (under
`CurvesJacobian.Kummer.completionMap`) is the class of an element `a ∈ Kˣ`, then `c` is the class
of an element `b ∈ kˣ` with `b = a` in `K`
(`CurvesJacobian.Kummer.exists_eq_toKummerCompletion_of_completionMap_eq`).

The proof is elementary:

* `CurvesJacobian.Kummer.normMap : (Kˣ)^∧ → (kˣ)^∧` is induced levelwise by the norm, and
  `normMap (completionMap c) = c ^ [K : k]` (`CurvesJacobian.Kummer.normMap_completionMap`).
* Torsion elements of `(kˣ)^∧` are classes of roots of unity of `k`
  (`CurvesJacobian.Kummer.exists_eq_toKummerCompletion_of_pow_eq_one`).
* `a` is fixed by `Gal(L/k)` for a finite Galois extension `L ⊇ K` (the normal closure), by
  functoriality (`CurvesJacobian.Kummer.completionMap_comp`) and Kummer-faithfulness of `L`; so
  `a ∈ k` (`CurvesJacobian.Kummer.exists_units_map_eq_of_completionMap_eq`).
-/

open KummerTheory

universe u

namespace CurvesJacobian.Kummer

section Basic

variable {k : Type*} [Field k] [CharZero k]

/-- For `k` Kummer-faithful for `𝔾_m` (characteristic `0`), `kˣ → (kˣ)^∧` is injective. -/
lemma injective_toKummerCompletion (hkf : IsKummerFaithfulGm k) :
    Function.Injective (toKummerCompletion k) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  refine hkf a fun n hn => ?_
  have h := congrArg (fun x : KummerCompletion k => x.1 ⟨n, by exact_mod_cast hn.ne'⟩) ha
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff a).1 h
  exact ⟨y, hy⟩

/-- **Torsion in `(kˣ)^∧`**: if `c ^ d = 1` with `d > 0`, then `c` is the class of a `d`-th root of
unity of `k`. -/
theorem exists_eq_toKummerCompletion_of_pow_eq_one {d : ℕ} (hd : 0 < d)
    (c : KummerCompletion k) (hc : c ^ d = 1) :
    ∃ ζ : kˣ, ζ ^ d = 1 ∧ c = toKummerCompletion k ζ := by
  have hlev : ∀ i : KummerIndex k, ∃ ζ : rootsOfUnity d k,
      c.1 i = QuotientGroup.mk (ζ : kˣ) := by
    intro i
    let j : KummerIndex k :=
      ⟨i.n * d, by push_cast; exact mul_ne_zero i.ne_zero (by exact_mod_cast hd.ne')⟩
    have hij : i ≤ j := dvd_mul_right i.n d
    obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (c.1 j)
    have h1 : (c ^ d).1 j = 1 := by rw [hc]; rfl
    have h2 : (c ^ d).1 j = QuotientGroup.mk (e ^ d) := by
      change (c.1 j) ^ d = _
      rw [← he, QuotientGroup.mk_pow]
    rw [h2] at h1
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 h1
    simp only [powMonoidHom_apply] at hy
    have hζ : (e * (y ^ i.n)⁻¹) ^ d = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, show i.n * d = j.n from rfl, hy, mul_inv_cancel]
    refine ⟨⟨e * (y ^ i.n)⁻¹, (mem_rootsOfUnity _ _).2 hζ⟩, ?_⟩
    rw [← c.2 i j hij, ← he]
    refine QuotientGroup.eq.2 ⟨y⁻¹, ?_⟩
    simp [inv_pow]
  by_contra hne
  push Not at hne
  have hex : ∀ ζ : rootsOfUnity d k, ∃ i : KummerIndex k, c.1 i ≠ QuotientGroup.mk (ζ : kˣ) := by
    intro ζ
    by_contra h
    push Not at h
    exact hne ζ ((mem_rootsOfUnity _ _).1 ζ.2) (Subtype.ext (funext h))
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  choose f hf using hex
  haveI := Fintype.ofFinite (rootsOfUnity d k)
  obtain ⟨M, hM⟩ := Finset.exists_le (Finset.univ.image f)
  obtain ⟨ζ, hζ⟩ := hlev M
  apply hf ζ
  rw [← c.2 (f ζ) M (hM _ (Finset.mem_image_of_mem f (Finset.mem_univ ζ))), hζ]
  rfl

end Basic

section Functoriality

variable {k K L : Type*} [Field k] [Field K] [Field L] [CharZero k] [CharZero K] [CharZero L]

omit [CharZero L] in
/-- **Functoriality of `(kˣ)^∧`**: `completionMap (ψ ∘ φ) = completionMap ψ ∘ completionMap φ`. -/
theorem completionMap_comp (φ : k →+* K) (ψ : K →+* L) (c : KummerCompletion k) :
    completionMap (ψ.comp φ) c = completionMap ψ (completionMap φ c) := by
  apply Subtype.ext
  funext i
  obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (c.1 (reindex i))
  change quotMap (ψ.comp φ) i.n (c.1 (reindex i)) =
    quotMap ψ i.n (quotMap φ i.n (c.1 (reindex i)))
  rw [← he]
  rfl

end Functoriality

section Norm

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [CharZero k] [CharZero K]

omit [CharZero k] [CharZero K] in
variable (k) in
/-- `Kˣ/(Kˣ)ⁿ → kˣ/(kˣ)ⁿ` induced by the norm `N_{K/k}`. -/
noncomputable def normQuot (n : ℕ) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range →* kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range :=
  QuotientGroup.map _ _ (Units.map (Algebra.norm k : K →* k)) <| by
    rintro _ ⟨b, rfl⟩
    exact ⟨Units.map (Algebra.norm k : K →* k) b, by simp⟩

omit [CharZero k] [CharZero K] in
@[simp]
lemma normQuot_mk (n : ℕ) (a : Kˣ) :
    normQuot k n (QuotientGroup.mk a) =
      QuotientGroup.mk (Units.map (Algebra.norm k : K →* k) a) := rfl

omit [CharZero k] [CharZero K] in
lemma quotTransition_normQuot {m n : ℕ} (h : m ∣ n)
    (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :
    quotTransition k h (normQuot k n x) = normQuot k m (quotTransition K h x) := by
  induction x using QuotientGroup.induction_on with
  | H a => rfl

variable (k) in
/-- The **norm map** `(Kˣ)^∧ → (kˣ)^∧`, induced levelwise by `N_{K/k} : Kˣ/(Kˣ)ⁿ → kˣ/(kˣ)ⁿ`. -/
noncomputable def normMap : KummerCompletion K →* KummerCompletion k where
  toFun x := ⟨fun i => normQuot k i.n (x.1 (reindex i)), fun i j h => by
    change quotTransition k h (normQuot k j.n (x.1 (reindex j))) =
      normQuot k i.n (x.1 (reindex i))
    rw [quotTransition_normQuot]
    congr 1
    exact x.2 (reindex i) (reindex j) h⟩
  map_one' := Subtype.ext (funext fun i => by
    change normQuot k i.n ((1 : KummerCompletion K).1 (reindex i)) = 1
    exact map_one _)
  map_mul' x y := Subtype.ext (funext fun i => map_mul (normQuot k i.n) _ _)

omit [CharZero k] in
lemma normMap_toKummerCompletion (a : Kˣ) :
    normMap k (toKummerCompletion K a) =
      toKummerCompletion k (Units.map (Algebra.norm k : K →* k) a) := rfl

/-- `N_{K/k} ∘ res = (·) ^ [K : k]` on `(kˣ)^∧`. -/
theorem normMap_completionMap (c : KummerCompletion k) :
    normMap k (completionMap (algebraMap k K) c) = c ^ Module.finrank k K := by
  apply Subtype.ext
  funext i
  obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (c.1 i)
  change normQuot k i.n (quotMap (algebraMap k K) i.n (c.1 i)) = (c.1 i) ^ Module.finrank k K
  rw [← he, quotMap_mk, normQuot_mk, ← QuotientGroup.mk_pow]
  congr 1
  ext
  simp [Algebra.norm_algebraMap]

end Norm

/-- A field over a field of characteristic `0` has characteristic `0`. -/
theorem charZero_of_algebra (k K : Type*) [Field k] [Field K] [Algebra k K] [CharZero k] :
    CharZero K :=
  charZero_of_injective_algebraMap (algebraMap k K).injective

section Descent

set_option synthInstance.checkSynthOrder false in
attribute [local instance] charZero_of_algebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k] [FiniteDimensional k K]

/-- **Galois descent of `𝔾_m`-classes**: if the image of `c ∈ (kˣ)^∧` in `(Kˣ)^∧` is the class of
`a ∈ Kˣ` and `k` is torally Kummer-faithful, then `a` lies in `k`. -/
theorem exists_units_map_eq_of_completionMap_eq (htf : IsTorallyKummerFaithful k)
    (c : KummerCompletion k) (a : Kˣ)
    (h : completionMap (algebraMap k K) c = toKummerCompletion K a) :
    ∃ b : kˣ, Units.map (algebraMap k K : k →* K) b = a := by
  let L := IntermediateField.normalClosure k K (AlgebraicClosure K)
  haveI : CharZero L := charZero_of_algebra k L
  have hL : IsKummerFaithfulGm L := htf L
  let ι : K →+* L := algebraMap K L
  have hι : ι.comp (algebraMap k K) = algebraMap k L := (IsScalarTower.algebraMap_eq k K L).symm
  have hx : toKummerCompletion L (Units.map (ι : K →* L) a) =
      completionMap (algebraMap k L) c := by
    rw [← completionMap_toKummerCompletion, ← h, ← completionMap_comp, hι]
  have hfix : ∀ σ : Gal(L/k), σ (ι a) = ι a := by
    intro σ
    have hσ : (σ : L →+* L).comp (algebraMap k L) = algebraMap k L :=
      RingHom.ext fun x => σ.commutes x
    have := injective_toKummerCompletion hL
      (a₁ := Units.map ((σ : L →+* L) : L →* L) (Units.map (ι : K →* L) a))
      (a₂ := Units.map (ι : K →* L) a) (by
        rw [← completionMap_toKummerCompletion, hx, ← completionMap_comp, hσ])
    simpa using congrArg Units.val this
  obtain ⟨b0, hb0⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed (ι a)).2 hfix)
  have hb0' : algebraMap k K b0 = a := ι.injective (by rw [← hb0, ← hι]; rfl)
  have hne : b0 ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by rw [← hb0', map_zero])
  exact ⟨Units.mk0 b0 hne, Units.ext (by simpa using hb0')⟩

/-- **Descent for Kummer completions** (field level): if the restriction to a finite extension `K`
of `c ∈ (kˣ)^∧` is the class of `a ∈ Kˣ` and `k` is torally Kummer-faithful, then `c` is the
class of some `b ∈ kˣ`, and `b = a` in `K`. -/
theorem exists_eq_toKummerCompletion_of_completionMap_eq (htf : IsTorallyKummerFaithful k)
    (c : KummerCompletion k) (a : Kˣ)
    (h : completionMap (algebraMap k K) c = toKummerCompletion K a) :
    ∃ b : kˣ, c = toKummerCompletion k b ∧ Units.map (algebraMap k K : k →* K) b = a := by
  obtain ⟨b, hb⟩ := exists_units_map_eq_of_completionMap_eq htf c a h
  have hc1 : completionMap (algebraMap k K) (c * (toKummerCompletion k b)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, completionMap_toKummerCompletion, hb, mul_inv_cancel]
  have hpow : (c * (toKummerCompletion k b)⁻¹) ^ Module.finrank k K = 1 := by
    rw [← normMap_completionMap (K := K), hc1, map_one]
  obtain ⟨ζ, -, hζ⟩ := exists_eq_toKummerCompletion_of_pow_eq_one Module.finrank_pos _ hpow
  have hc : c = toKummerCompletion k (ζ * b) := by
    rw [map_mul, ← hζ, inv_mul_cancel_right]
  refine ⟨ζ * b, hc, ?_⟩
  apply injective_toKummerCompletion (htf K)
  rw [← completionMap_toKummerCompletion, ← hc, h]

end Descent

end CurvesJacobian.Kummer
