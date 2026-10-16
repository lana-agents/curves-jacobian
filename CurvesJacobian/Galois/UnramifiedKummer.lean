/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.FunctionFieldF
import ContinuousKummerTheory.Curve.Residue

/-!
# Unramified Kummer classes are the functions with divisor divisible by `n`

Setting of `pi1` / continuous-kummer-theory: `k` of characteristic `0`, `Ω` separably closed and
Galois over `K₀ = k(t)`, `D : GaloisData k t`, `F = F D = Ω^H`, `n ≥ 1`. For `v ∈ Fˣ`, the
Kummer class `κ(v) ∈ H¹(Gal(Ω/F), μₙ)` restricted to `H` (`resMu D n`) can be evaluated on every
`σ` in the inertia group of a place `W ⊇ k` of `Ω` (`ContH1.evalTriv`).

* `CurvesJacobian.IsUnramifiedKummer D n v`: `κ(v)` is trivial on the inertia groups of all places
  `W ⊇ k` of `Ω` (`F(v^{1/n})/F` is unramified at every place of `F`; cusps included);
* `CurvesJacobian.isUnramifiedKummer_iff`: this holds iff `n ∣ ord_P v` for every place `P` of
  `F/k` (weil-curves' places, via `isFunctionField_F`), i.e. iff `div v ∈ n · Div(F)`.

Proof: both directions are the two local statements of continuous-kummer-theory:
`κ(v)|_{I_W} = κ(π)|_{I_W}^{ord_P v}` for a uniformiser `π` at `P = W ∩ F`
(`Curve.evalTriv_res_kummer_eq_zpow`), and the tame character `κ(π)|_{I_W}` is onto `μₙ`
(`Curve.evalTriv_kummer_surjective`), together with the extension of places of `F` to `Ω`
(`exists_valuationSubring_liesOver`). This is the Galois form of Milne, *Abelian Varieties*,
III.Lemma 9.2 (Kummer covers `k(V)(g^{1/n})` with `(g) = nD` are étale).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

namespace CurvesJacobian

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]
  (n : ℕ) [NeZero n]

attribute [local instance] isFunctionField_F

/-- The Kummer class of `v` is trivial on the inertia groups of all places `W ⊇ k` of `Ω`. -/
def IsUnramifiedKummer (v : (F D)ˣ) : Prop :=
  ∀ (W : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ W) (σ : D.H)
    (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W),
    ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω v)) = 1

variable {D}

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] in
/-- For `W` lying over `P`, the valuation of `W` on `F` is controlled by `P`. -/
lemma valuation_lt_one_iff {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) {x : F D} (hx : x ≠ 0) :
    W.valuation ((x : F D) : Ω) < 1 ↔ x ∈ P.1 ∧ x⁻¹ ∉ P.1 := by
  have hxΩ : ((x : F D) : Ω) ≠ 0 := fun h ↦ hx (Subtype.ext h)
  rw [← hW, ← hW]
  constructor
  · intro h
    refine ⟨(W.valuation_le_one_iff _).1 h.le, fun hinv ↦ ?_⟩
    have h2 := (W.valuation_le_one_iff _).2 hinv
    rw [IntermediateField.coe_inv, map_inv₀] at h2
    have hne : W.valuation ((x : F D) : Ω) ≠ 0 := by rwa [Valuation.ne_zero_iff]
    exact absurd ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2) (not_le.2 h)
  · rintro ⟨h1, h2⟩
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 h1) fun heq ↦ h2 ?_
    apply (W.valuation_le_one_iff _).1
    rw [IntermediateField.coe_inv, map_inv₀, heq, inv_one]

variable (D)

/-- **Unramified Kummer classes ↔ divisors divisible by `n`.** -/
theorem isUnramifiedKummer_iff (v : (F D)ˣ) :
    IsUnramifiedKummer D n v ↔ ∀ P : Place k (F D), (n : ℤ) ∣ P.ord (v : F D) := by
  constructor
  · intro hun P
    obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver D P
    have hk : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k (F D) Ω]
      exact (hW _).2 (P.algebraMap_mem c)
    obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
    have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
    have hπmem : π ∈ P.1 ∧ π⁻¹ ∉ P.1 := by
      refine ⟨P.mem_of_ord_nonneg (by rw [hπ1]; norm_num), fun h ↦ ?_⟩
      have := P.ord_nonneg_of_mem h
      rw [P.ord_inv, hπ1] at this
      norm_num at this
    have hπW : W.valuation ((π : F D) : Ω) < 1 := (valuation_lt_one_iff hW hπ0).2 hπmem
    have hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω) := by
      intro f hf hlt
      set x : F D := ⟨f, hf⟩
      rcases eq_or_ne x 0 with hx0 | hx0
      · have : f = 0 := congrArg Subtype.val hx0
        rw [this, map_zero]; exact zero_le
      obtain ⟨hxP, hxP'⟩ := (valuation_lt_one_iff hW hx0).1 hlt
      have hord : 1 ≤ P.ord x := by
        have h0 := P.ord_nonneg_of_mem hxP
        rcases (show P.ord x = 0 ∨ 1 ≤ P.ord x by omega) with h | h
        · exact absurd ((P.ord_eq_zero_iff hx0).1 h).2 hxP'
        · exact h
      have hdiv : x / π ∈ P.1 := P.mem_of_ord_nonneg (by rw [P.ord_div hx0 hπ0, hπ1]; omega)
      have hdivW := (W.valuation_le_one_iff _).2 ((hW _).2 hdiv)
      rw [IntermediateField.coe_div, map_div₀] at hdivW
      have hπΩ : W.valuation ((π : F D) : Ω) ≠ 0 := by
        rw [Valuation.ne_zero_iff]; exact fun h ↦ hπ0 (Subtype.ext h)
      exact (div_le_one₀ (zero_lt_iff.2 hπΩ)).1 hdivW
    -- a primitive `n`-th root of unity
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    haveI : NeZero (n : Ω) := NeZero.charZero
    obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
    let ζ : Mu n Ω := hμ.toRootsOfUnity
    obtain ⟨σ, hσ, hσζ⟩ := evalTriv_kummer_surjective (D := D) hk (Units.mk0 π hπ0) hπW hπ n ζ
    set m := P.ord (v : F D)
    have hunit : P.ord ((v * (Units.mk0 π hπ0) ^ (-m) : (F D)ˣ) : F D) = 0 := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, P.ord_mul v.ne_zero
        (zpow_ne_zero _ hπ0), P.ord_zpow, hπ1]
      ring
    have hu0 : ((v * (Units.mk0 π hπ0) ^ (-m) : (F D)ˣ) : F D) ≠ 0 := Units.ne_zero _
    obtain ⟨hu1, hu2⟩ := (P.ord_eq_zero_iff hu0).1 hunit
    have heq := evalTriv_res_kummer_eq_zpow hk hσ n v (Units.mk0 π hπ0) m ((hW _).2 hu1)
      ((hW _).2 (by simpa using hu2))
    rw [hun W hk σ hσ, hσζ] at heq
    have h1 : (Mu.val ζ) ^ m = 1 := by rw [← map_zpow, ← heq, map_one]
    have h2 : μ ^ m = 1 := by
      have := congrArg (fun z : Ωˣ ↦ (z : Ω)) h1
      simp only [Units.val_zpow_eq_zpow_val, Units.val_one] at this
      exact this
    exact (hμ.zpow_eq_one_iff_dvd m).1 h2
  · intro hdiv W hk σ hσ
    set A : ValuationSubring (F D) := W.comap (algebraMap (F D) Ω)
    by_cases hA : A = ⊤
    · have hv : ((v : F D) : Ω) ∈ W := by
        have : (v : F D) ∈ A := hA ▸ ValuationSubring.mem_top _
        exact this
      have hv' : (((v⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W := by
        have : ((v⁻¹ : (F D)ˣ) : F D) ∈ A := hA ▸ ValuationSubring.mem_top _
        exact this
      exact evalTriv_res_kummer_of_unit hk hσ n v hv hv'
    · let P : Place k (F D) := ⟨A, hA, fun c ↦ by
        change algebraMap (F D) Ω (algebraMap k (F D) c) ∈ W
        rw [← IsScalarTower.algebraMap_apply k (F D) Ω]
        exact hk c⟩
      have hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1 := fun _ ↦ Iff.rfl
      obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
      have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
      set m := P.ord (v : F D)
      obtain ⟨m', hm'⟩ := hdiv P
      have hunit : P.ord ((v * (Units.mk0 π hπ0) ^ (-m) : (F D)ˣ) : F D) = 0 := by
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, P.ord_mul v.ne_zero
          (zpow_ne_zero _ hπ0), P.ord_zpow, hπ1]
        ring
      have hu0 : ((v * (Units.mk0 π hπ0) ^ (-m) : (F D)ˣ) : F D) ≠ 0 := Units.ne_zero _
      obtain ⟨hu1, hu2⟩ := (P.ord_eq_zero_iff hu0).1 hunit
      rw [evalTriv_res_kummer_eq_zpow hk hσ n v (Units.mk0 π hπ0) m ((hW _).2 hu1)
        ((hW _).2 (by simpa using hu2)), show m = n * m' from hm', zpow_mul]
      have hpow : ∀ ζ : Mu n Ω, ζ ^ (n : ℤ) = 1 := fun ζ ↦ by
        apply Mu.ext
        rw [map_zpow, zpow_natCast, Mu.val_pow_n, map_one]
      rw [hpow, one_zpow]

end CurvesJacobian
