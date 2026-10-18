/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ClosedRestriction
import CurvesJacobian.Kummer.CompletionDescent
import CurvesJacobian.Kummer.Image
import CurvesJacobian.Kummer.ClosedPoints

/-!
# [AbsTopIII] Prop. 1.8 at closed points over finite extensions `k_x`

[AbsTopIII] Prop. 1.8 (T3 l.2061–2106) characterises, inside `P_U ⊆ H¹(Π_U, M_X)`, the Kummer
classes of nonconstant functions (i) and of constants (ii) by their restrictions
`η|_x = s_x^*(η) ∈ H¹(G_{k_x}, M_X)` to points `x ∈ U(k_x)`, `[k_x : k] < ∞`. Here `η|_x` is the
`Ẑ(1)`-level restriction `restrictClosed` of `Kummer/ClosedRestriction.lean`, `k` is torally
Kummer-faithful, and the descent `(kˣ)^∧ ∩ k_xˣ = kˣ` of `Kummer/CompletionDescent.lean`
replaces the rational-point argument of `Kummer/RationalCharacterization.lean`.

* `restrictClosed_kummerMapZHat_eq_one_iff`: `κ_U(u)|_x = 0` iff `u(x) = 1`;
* `restrictClosed_kummerMapZHat_eq_one_iff_forall`: `κ_U(u)|_x = 0` iff all level-`n`
  restrictions along `D_A → Π_U` vanish (the form used in `Kummer/ClosedPoints.lean`);
* `exists_eq_kummerMapZHat_of_restrictClosed` (**Prop. 1.8(i), "if"**): if `η ∈ P_U` has
  `η|_{x₁} = 0` and `η|_{x₂} ≠ 0` at closed points over finite extensions of `k`, then
  `η = κ_U(w)` for a nonconstant unit `w` of `U`;
* `exists_restrictClosed_of_transcendental` (**Prop. 1.8(i), "only if"**, `Ẑ(1)`-level);
* `eq_toKummerCompletion_of_restrictClosed_eq` (**Prop. 1.8(ii), "if"**, closed points): if
  `κ_U(f)|_x = c|_{G_{k_x}}` for `c ∈ (kˣ)^∧`, then `c` is the Kummer class of a constant
  `b ∈ kˣ` with `b = f(x)`.
-/

open KummerTheory Curve AffOrbicurve IsLocalRing

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]

section Point

variable (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)] (hHL : D.HL = D.H) (ht : t ∈ A)

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **`η|_x` for `η = κ_U(v) · c ∈ P_U`**: `η|_x = v(x) · c|_{G_{k_x}}` in `(k_xˣ)^∧`. -/
theorem kummerZHatEquiv_restrictClosed_mul (v : units D) (c : KummerCompletion k)
    (hv : (((v : (F D)ˣ) : F D) : Ω) ∈ A) (hv' : ((((v : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    haveI := isAlgClosed_residueField A hk hkres
    haveI := isGalois_residueField A hk hkres
    haveI : CharZero (Decomposition.pointField (F D) A hk hkres) :=
      charZero_of_injective_algebraMap (algebraMap k _).injective
    haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
      IsGalois.tower_top_intermediateField _
    kummerZHatEquiv _ (ResidueField A)
        (restrictClosed D A hk hkres hHL ht (kummerMapZHat D v * constMapZHat D c)) =
      toKummerCompletion _ (unitValue D A hk hkres v hv hv') *
        completionMap (algebraMap k (Decomposition.pointField (F D) A hk hkres)) c := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  haveI : CharZero (Decomposition.pointField (F D) A hk hkres) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
    IsGalois.tower_top_intermediateField _
  have e1 := congrArg (kummerZHatEquiv _ (ResidueField A))
    (restrictClosed_kummerMapZHat D A hk hkres hHL ht v hv hv')
  rw [kummerZHatEquiv_kummerZHat] at e1
  have e2 := kummerZHatEquiv_restrictClosed_constMapZHat D A hk hkres hHL ht c
  rw [map_mul, map_mul]
  exact congrArg₂ (· * ·) e1 e2

variable [FiniteDimensional k (Decomposition.pointField (F D) A hk hkres)]

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- A constant `b ∈ kˣ` restricts trivially to a closed point iff `b = 1` (`k` torally
Kummer-faithful). -/
theorem restrictClosed_constMapZHat_eq_one_iff (htf : IsTorallyKummerFaithful k) (b : kˣ) :
    restrictClosed D A hk hkres hHL ht (constMapZHat D (toKummerCompletion k b)) = 1 ↔ b = 1 := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  haveI : CharZero (Decomposition.pointField (F D) A hk hkres) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
    IsGalois.tower_top_intermediateField _
  rw [← (kummerZHatEquiv _ (ResidueField A)).injective.eq_iff, map_one,
    kummerZHatEquiv_restrictClosed_constMapZHat, completionMap_toKummerCompletion,
    ← map_one (toKummerCompletion (Decomposition.pointField (F D) A hk hkres)),
    (injective_toKummerCompletion (htf _)).eq_iff]
  constructor
  · intro h
    apply Units.map_injective (f := (algebraMap k (Decomposition.pointField (F D) A hk hkres) :
      k →* Decomposition.pointField (F D) A hk hkres)) (algebraMap k _).injective
    rw [h, map_one]
  · rintro rfl
    exact map_one _

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(i), `η†|x = 0`, at the `Ẑ(1)`-level**: for `k` torally
Kummer-faithful and `[k_x : k] < ∞`, `κ_U(u)|_x = 0` iff `u(x) = 1`. -/
theorem restrictClosed_kummerMapZHat_eq_one_iff (htf : IsTorallyKummerFaithful k)
    (u : units D) (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A)
    (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    restrictClosed D A hk hkres hHL ht (kummerMapZHat D u) = 1 ↔ residue A ⟨_, hu⟩ = 1 := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  haveI : CharZero (Decomposition.pointField (F D) A hk hkres) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
    IsGalois.tower_top_intermediateField _
  rw [restrictClosed_kummerMapZHat D A hk hkres hHL ht u hu hu',
    ← map_one (kummerZHat (Decomposition.pointField (F D) A hk hkres) (ResidueField A)),
    ((kummerZHat_injective_iff _ (ResidueField A)).2 (htf _)).eq_iff, Units.ext_iff,
    Subtype.ext_iff]
  rfl

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
omit [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
  [FiniteDimensional k (Decomposition.pointField (F D) A hk hkres)] in
/-- `κ_U(u)|_x = 0` iff all level-`n` restrictions of `κ_U(u)` along `D_A → Π_U` vanish. -/
theorem restrictClosed_kummerMapZHat_eq_one_iff_forall [IsAlgClosed Ω]
    [Algebra.IsIntegral k (ResidueField A)] (u : units D) :
    restrictClosed D A hk hkres hHL ht (kummerMapZHat D u) = 1 ↔
      ∀ (n : ℕ) [NeZero n],
        letI := Decomposition.muAction (F D) A hk hkres n
        ContH1.map (decompToPi D A) (continuous_decompToPi D A)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) = 1 := by
  rw [restrictClosed_eq_one_iff]
  constructor
  · intro h n _
    have := h ⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
    rwa [map_proj_kummerMapZHat] at this
  · intro h i
    rw [map_proj_kummerMapZHat]
    exact h i.n

end Point

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(i), "if", at closed points over finite extensions `k_x`.** For `k`
torally Kummer-faithful: if `η ∈ P_U` restricts trivially to a closed point `x₁` of `U` and
nontrivially to a closed point `x₂` (`[k_{x_i} : k] < ∞`), then `η = κ_U(w)` for a nonconstant
unit `w` of `U`. Applied to a positive multiple `η† = η^N ∈ P_U` this is the statement of (i)
for `η†` (NF-ness of `w`: `Kummer/NFCharacterization.lean`). -/
theorem exists_eq_kummerMapZHat_of_restrictClosed (htf : IsTorallyKummerFaithful k)
    (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) (hHL : D.HL = D.H)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) (hη : η ∈ PU D)
    (A₁ : ValuationSubring Ω) (hk₁ : ∀ c : k, algebraMap k Ω c ∈ A₁)
    [Algebra k (ResidueField A₁)]
    (hkres₁ : ∀ c : k, residue A₁ ⟨algebraMap k Ω c, hk₁ c⟩ = algebraMap k (ResidueField A₁) c)
    [Algebra.IsIntegral k (ResidueField A₁)]
    [FiniteDimensional k (Decomposition.pointField (F D) A₁ hk₁ hkres₁)] (ht₁ : t ∈ A₁)
    (A₂ : ValuationSubring Ω) (hk₂ : ∀ c : k, algebraMap k Ω c ∈ A₂)
    [Algebra k (ResidueField A₂)]
    (hkres₂ : ∀ c : k, residue A₂ ⟨algebraMap k Ω c, hk₂ c⟩ = algebraMap k (ResidueField A₂) c)
    [Algebra.IsIntegral k (ResidueField A₂)]
    [FiniteDimensional k (Decomposition.pointField (F D) A₂ hk₂ hkres₂)] (ht₂ : t ∈ A₂)
    (h₁ : restrictClosed D A₁ hk₁ hkres₁ hHL ht₁ η = 1)
    (h₂ : restrictClosed D A₂ hk₂ hkres₂ hHL ht₂ η ≠ 1) :
    ∃ w : units D, η = kummerMapZHat D w ∧ w ∉ Set.range (constUnit D) := by
  obtain ⟨v, c, rfl⟩ := (mem_PU_iff hJ hkF η).1 hη
  obtain ⟨hv, hv'⟩ := units_mem (D := D) ⟨hk₁, ht₁⟩ v.2
  haveI := isAlgClosed_residueField A₁ hk₁ hkres₁
  haveI := isGalois_residueField A₁ hk₁ hkres₁
  haveI : CharZero (Decomposition.pointField (F D) A₁ hk₁ hkres₁) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : IsGalois (Decomposition.pointField (F D) A₁ hk₁ hkres₁) (ResidueField A₁) :=
    IsGalois.tower_top_intermediateField _
  have e := congrArg (kummerZHatEquiv _ (ResidueField A₁)) h₁
  rw [kummerZHatEquiv_restrictClosed_mul D A₁ hk₁ hkres₁ hHL ht₁ v c hv hv', map_one] at e
  have hc : completionMap (algebraMap k (Decomposition.pointField (F D) A₁ hk₁ hkres₁)) c =
      toKummerCompletion _ (unitValue D A₁ hk₁ hkres₁ v hv hv')⁻¹ := by
    rw [map_inv, eq_inv_iff_mul_eq_one, mul_comm]
    exact e
  obtain ⟨b, hb, -⟩ := exists_eq_toKummerCompletion_of_completionMap_eq htf c _ hc
  have hconst : constMapZHat D c = kummerMapZHat D (constUnit D b) := by
    rw [hb, constMapZHat_toKummerCompletion]
  refine ⟨v * constUnit D b, by rw [hconst, map_mul], ?_⟩
  rintro ⟨b', hb'⟩
  have hη' : kummerMapZHat D v * constMapZHat D c = constMapZHat D (toKummerCompletion k b') := by
    rw [hconst, ← map_mul, ← hb', constMapZHat_toKummerCompletion]
  rw [hη'] at h₁ h₂
  obtain rfl := (restrictClosed_constMapZHat_eq_one_iff D A₁ hk₁ hkres₁ hHL ht₁ htf b').1 h₁
  exact h₂ (by rw [map_one, map_one, map_one])

/-- **[AbsTopIII] Prop. 1.8(i), "only if", at the `Ẑ(1)`-level** (T3 l.2078–2087, proof
l.2099–2106): for `k` torally Kummer-faithful and a nonconstant unit `f` of `U`, there are
`M ≥ 1` and closed points `x₁, x₂` of `U` with `[k_{x_i} : k] < ∞`, `κ_U(f^M)|x₁ = 0` and
`κ_U(f^M)|x₂ ≠ 0` (`η|_x = s_x^*(η) ∈ H¹(G_{k_x}, Ẑ(1))`). -/
theorem exists_restrictClosed_of_transcendental (htf : IsTorallyKummerFaithful k)
    (hHL : D.HL = D.H) (f : units D) (hf : Transcendental k ((f : (F D)ˣ) : F D)) :
    ∃ M : ℕ, 0 < M ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
            (kummerMapZHat D (f ^ M)) = 1) ∧
      (∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
            (kummerMapZHat D (f ^ M)) ≠ 1) := by
  obtain ⟨M, hM, ⟨A, hk, ht, hint, hfin, h1⟩, ⟨A₂, hk₂, ht₂, hint₂, hfin₂, h2⟩⟩ :=
    exists_restrict_kummerMap_of_transcendental D htf f hf
  refine ⟨M, hM, ⟨A, hk, ht, hint, hfin, ?_⟩, ⟨A₂, hk₂, ht₂, hint₂, hfin₂, ?_⟩⟩
  · letI := Decomposition.residueAlgebra A hk
    exact (restrictClosed_kummerMapZHat_eq_one_iff_forall D A hk _ hHL ht _).2 h1
  · letI := Decomposition.residueAlgebra A₂ hk₂
    exact fun h => h2 ((restrictClosed_kummerMapZHat_eq_one_iff_forall D A₂ hk₂ _ hHL ht₂ _).1 h)

end CurvesJacobian.Kummer
