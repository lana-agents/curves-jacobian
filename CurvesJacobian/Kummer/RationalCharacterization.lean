/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.PointRestriction

/-!
# [AbsTopIII] Prop. 1.8 at rational points

[AbsTopIII] Prop. 1.8 (T3 l.2061–2106) characterises, inside
`P_U ⊆ H¹(Π_U, M_X)` (`CurvesJacobian.Kummer.PU`, the inverse image of the cuspidal principal
divisors), the Kummer classes of nonconstant functions (i) and of constants (ii) by their
restrictions `η|_x = s_x^*(η)` to points. Here the points are `k`-rational points of `U`
(`CurvesJacobian.Kummer.restrictPt`); the NF-conditions of Def. 1.7 and points over finite
extensions `k_x` are treated in later files.

* `CurvesJacobian.Kummer.exists_eq_kummerMapZHat_of_restrictPt` (**Prop. 1.8(i), "if"**, at
  rational points): if `η ∈ P_U` has `η|_{x₁} = 0` and `η|_{x₂} ≠ 0` for rational points
  `x₁, x₂` of `U`, then `η = κ_U(w)` for a nonconstant unit `w` of `U` with `w(x₁) = 1`.
  Applied to a positive multiple `η† = η^N ∈ P_U` this is the statement of (i) for `η†`.
* `CurvesJacobian.Kummer.restrictPt_kummerMapZHat_eq_one_iff` (**Prop. 1.8(i), "only if"**,
  given the points): for `k` Kummer-faithful for `𝔾_m`, `κ_U(w)|_x = 0` iff `w(x) = 1`.
* `CurvesJacobian.Kummer.eq_toKummerCompletion_of_restrictPt_eq` (**Prop. 1.8(ii)**, at a rational
  point): if `κ_U(f)|_x = c|_x` for `c ∈ (kˣ)^∧`, then `c` is the Kummer class of the constant
  `f(x) ∈ kˣ`, i.e. `constMapZHat c = κ_U(f(x))`.

The hypotheses are those of `Kummer/Image.lean` (`IsKummerFaithfulJac D`, `k` algebraically
closed in `F`) and `D.HL = D.H` (`U = Spec R`).
-/

open KummerTheory Curve AffOrbicurve IsLocalRing

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- For `k` Kummer-faithful for `𝔾_m` (characteristic `0`), `kˣ → (kˣ)^∧` is injective. -/
lemma toKummerCompletion_injective (hkf : IsKummerFaithfulGm k) :
    Function.Injective (toKummerCompletion k) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  refine hkf a fun n hn => ?_
  have h := congrArg (fun x : KummerCompletion k => x.1 ⟨n, by exact_mod_cast hn.ne'⟩) ha
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff a).1 h
  exact ⟨y, hy⟩

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
/-- A unit of `U` has a value in `kˣ` at a rational point. -/
lemma exists_value (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    [Algebra k (ResidueField A)]
    (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
      ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)
    (ht : t ∈ A) (v : units D) :
    ∃ (hv : (((v : (F D)ˣ) : F D) : Ω) ∈ A)
      (_ : ((((v : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) (a : kˣ),
      residue A ⟨_, hv⟩ = algebraMap k (ResidueField A) a := by
  obtain ⟨hv, hv'⟩ := units_mem (D := D) ⟨hk, ht⟩ v.2
  obtain ⟨a, ha⟩ := exists_residue_eq_of_rational D A hrat _ hv hv'
  exact ⟨hv, hv', a, ha⟩

section Point

variable (D) (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]
  (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)
  (hHL : D.HL = D.H) (ht : t ∈ A)

/-- A constant class `c ∈ (kˣ)^∧` restricts trivially to a rational point iff `c = 1`. -/
theorem restrictPt_constMapZHat_eq_one_iff (c : KummerCompletion k) :
    restrictPt D A hk hkres hrat hHL ht (constMapZHat D c) = 1 ↔ c = 1 := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  rw [← (kummerZHatEquiv k (ResidueField A)).injective.eq_iff, map_one,
    kummerZHatEquiv_restrictPt_constMapZHat]

/-- `κ_U(v) · c` restricts trivially to a rational point `x` iff `v(x) · c = 1` in `(kˣ)^∧`. -/
theorem restrictPt_mul_eq_one_iff (v : units D) (a : kˣ) (c : KummerCompletion k)
    (hv : (((v : (F D)ˣ) : F D) : Ω) ∈ A) (hv' : ((((v : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hva : residue A ⟨_, hv⟩ = algebraMap k (ResidueField A) a) :
    restrictPt D A hk hkres hrat hHL ht (kummerMapZHat D v * constMapZHat D c) = 1 ↔
      toKummerCompletion k a * c = 1 := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  rw [← (kummerZHatEquiv k (ResidueField A)).injective.eq_iff, map_one,
    kummerZHatEquiv_restrictPt_of_eq D A hk hkres hrat hHL ht v a c hv hv' hva]

end Point



/-- **[AbsTopIII] Prop. 1.8(i), "if", at rational points.** If `η ∈ P_U` restricts trivially to a
rational point `x₁` of `U` and nontrivially to a rational point `x₂`, then `η = κ_U(w)` for a
nonconstant unit `w` of `U`. -/
theorem exists_eq_kummerMapZHat_of_restrictPt (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) (hHL : D.HL = D.H)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) (hη : η ∈ PU D)
    (A₁ : ValuationSubring Ω) (hk₁ : ∀ c : k, algebraMap k Ω c ∈ A₁)
    [Algebra k (ResidueField A₁)]
    (hkres₁ : ∀ c : k, residue A₁ ⟨algebraMap k Ω c, hk₁ c⟩ = algebraMap k (ResidueField A₁) c)
    [Algebra.IsIntegral k (ResidueField A₁)]
    (hrat₁ : ∀ (a : F D) (ha : (a : Ω) ∈ A₁),
      ∃ c : k, residue A₁ ⟨_, ha⟩ = algebraMap k (ResidueField A₁) c) (ht₁ : t ∈ A₁)
    (A₂ : ValuationSubring Ω) (hk₂ : ∀ c : k, algebraMap k Ω c ∈ A₂)
    [Algebra k (ResidueField A₂)]
    (hkres₂ : ∀ c : k, residue A₂ ⟨algebraMap k Ω c, hk₂ c⟩ = algebraMap k (ResidueField A₂) c)
    [Algebra.IsIntegral k (ResidueField A₂)]
    (hrat₂ : ∀ (a : F D) (ha : (a : Ω) ∈ A₂),
      ∃ c : k, residue A₂ ⟨_, ha⟩ = algebraMap k (ResidueField A₂) c) (ht₂ : t ∈ A₂)
    (h₁ : restrictPt D A₁ hk₁ hkres₁ hrat₁ hHL ht₁ η = 1)
    (h₂ : restrictPt D A₂ hk₂ hkres₂ hrat₂ hHL ht₂ η ≠ 1) :
    ∃ w : units D, η = kummerMapZHat D w ∧ w ∉ Set.range (constUnit D) := by
  obtain ⟨v, c, rfl⟩ := (mem_PU_iff hJ hkF η).1 hη
  obtain ⟨hv, hv', a, ha⟩ := exists_value A₁ hk₁ hrat₁ ht₁ v
  have hc : c = toKummerCompletion k a⁻¹ := by
    rw [restrictPt_mul_eq_one_iff D A₁ hk₁ hkres₁ hrat₁ hHL ht₁ v a c hv hv' ha] at h₁
    rw [map_inv, eq_inv_iff_mul_eq_one, mul_comm]
    exact h₁
  have hconst : constMapZHat D c = kummerMapZHat D (constUnit D a⁻¹) := by
    rw [hc, constMapZHat_toKummerCompletion]
  refine ⟨v * constUnit D a⁻¹, by rw [hconst, map_mul], ?_⟩
  rintro ⟨b, hb⟩
  -- a constant class restricts to the same element of `(kˣ)^∧` at both points
  have hη : kummerMapZHat D v * constMapZHat D c = constMapZHat D (toKummerCompletion k b) := by
    rw [hconst, ← map_mul, ← hb, constMapZHat_toKummerCompletion]
  rw [hη] at h₁ h₂
  exact h₂ ((restrictPt_constMapZHat_eq_one_iff D A₂ hk₂ hkres₂ hrat₂ hHL ht₂ _).2
    ((restrictPt_constMapZHat_eq_one_iff D A₁ hk₁ hkres₁ hrat₁ hHL ht₁ _).1 h₁))

/-- **[AbsTopIII] Prop. 1.8(i), "only if", at a given rational point**: for `k` Kummer-faithful
for `𝔾_m`, `κ_U(w)|_x = 0` iff `w(x) = 1`. -/
theorem restrictPt_kummerMapZHat_eq_one_iff (hkf : IsKummerFaithfulGm k) (hHL : D.HL = D.H)
    (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    [Algebra k (ResidueField A)]
    (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
    [Algebra.IsIntegral k (ResidueField A)]
    (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
      ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c) (ht : t ∈ A)
    (w : units D) (a : kˣ)
    (hw : (((w : (F D)ˣ) : F D) : Ω) ∈ A) (hw' : ((((w : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hwa : residue A ⟨_, hw⟩ = algebraMap k (ResidueField A) a) :
    restrictPt D A hk hkres hrat hHL ht (kummerMapZHat D w) = 1 ↔ a = 1 := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  rw [← (kummerZHatEquiv k (ResidueField A)).injective.eq_iff, map_one,
    restrictPt_kummerMapZHat D A hk hkres hrat hHL ht w a hw hw' hwa,
    kummerZHatEquiv_kummerZHat, ← map_one (toKummerCompletion k)]
  exact (toKummerCompletion_injective hkf).eq_iff

/-- **[AbsTopIII] Prop. 1.8(ii) at a rational point**: if `κ_U(f)|_x = c|_x` for
`c ∈ (kˣ)^∧ ≅ H¹(G_k, Ẑ(1))`, then `c` is the Kummer class of the constant `f(x) ∈ kˣ`; in
particular `constMapZHat c = κ_U(f(x))` is the Kummer class of a constant. -/
theorem eq_toKummerCompletion_of_restrictPt_eq (hHL : D.HL = D.H)
    (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    [Algebra k (ResidueField A)]
    (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
    [Algebra.IsIntegral k (ResidueField A)]
    (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
      ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c) (ht : t ∈ A)
    (f : units D) (a : kˣ)
    (hf : (((f : (F D)ˣ) : F D) : Ω) ∈ A) (hf' : ((((f : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hfa : residue A ⟨_, hf⟩ = algebraMap k (ResidueField A) a) (c : KummerCompletion k)
    (h : restrictPt D A hk hkres hrat hHL ht (kummerMapZHat D f) =
      restrictPt D A hk hkres hrat hHL ht (constMapZHat D c)) :
    c = toKummerCompletion k a ∧ constMapZHat D c = kummerMapZHat D (constUnit D a) := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  have hc : c = toKummerCompletion k a := by
    have := congrArg (kummerZHatEquiv k (ResidueField A)) h
    rw [restrictPt_kummerMapZHat D A hk hkres hrat hHL ht f a hf hf' hfa,
      kummerZHatEquiv_kummerZHat, kummerZHatEquiv_restrictPt_constMapZHat] at this
    exact this.symm
  exact ⟨hc, by rw [hc, constMapZHat_toKummerCompletion]⟩

end CurvesJacobian.Kummer
