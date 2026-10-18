/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.Image
import ContinuousKummerTheory.Curve.RationalSection

/-!
# The `Ẑ(1)`-level restriction `η|_x` to a rational point

[AbsTopIII] Prop. 1.8 (T3 l.2080–2087): for a point `x` of `U` with section
`s_x : G_{k_x} → Π_U`, `η|_x := s_x^*(η) ∈ H¹(G_{k_x}, M_X)`. Here `x` is a `k`-rational point of
`U` (a place `A ⊆ Ω` with `κ(A ∩ F) = k`, continuous-kummer-theory `Curve/RationalPoint.lean`),
`s_x = ratSectionMap : Gal(κ(A)/k) → Π_U`, and `M_X = Ẑ(1)`. The coefficients are reduced modulo
`𝔪_A`, levelwise by `Decomposition.reduceMu`:

* `CurvesJacobian.Kummer.reduceZHat : Ẑ(1)_Ω → Ẑ(1)_{κ(A)}`;
* `CurvesJacobian.Kummer.restrictPt A … : H¹(Π_U, Ẑ(1)) → H¹(Gal(κ(A)/k), Ẑ(1))`, `η ↦ η|_x`;
* `restrictPt_kummerMapZHat`: **`κ_U(u)|_x = κ_k(u(x))`** at the `Ẑ`-level;
* `kummerZHatEquiv_restrictPt_constMapZHat`: for `c ∈ (kˣ)^∧`, `c|_x = c` (under
  `H¹(Gal(κ(A)/k), Ẑ(1)) ≃ (kˣ)^∧`): classes from `H¹(G_k, Ẑ(1))` restrict to themselves;
* `kummerZHatEquiv_restrictPt_of_eq`: for `η = κ_U(v) · c ∈ P_U` (`mem_PU_iff`),
  `η|_x = v(x) · c` in `(kˣ)^∧`.
-/

open KummerTheory Curve AffOrbicurve IsLocalRing

namespace CurvesJacobian.Kummer

universe u

section Reduce

variable {Ω : Type*} [Field Ω] (A : ValuationSubring Ω)

/-- Reduction of roots of unity commutes with the transition maps. -/
lemma reduceMu_transition {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m ∣ n) (ζ : Mu n Ω) :
    Decomposition.reduceMu A m hm (Mu.transition h ζ) =
      Mu.transition h (Decomposition.reduceMu A n hn ζ) := by
  apply Mu.ext
  apply Units.ext
  rw [Mu.val_transition, Units.val_pow_eq_pow_val]
  change residue A _ = residue A _ ^ (n / m)
  rw [← map_pow]
  rfl

variable {k : Type*} [Field k] (K : Type*) [Field K] [CharZero K]

/-- The index `n` of `Ẑ(1)` over `k`, viewed over a field `K` of characteristic `0`. -/
def liftIndex (i : KummerIndex k) : KummerIndex K := ⟨i.n, Nat.cast_ne_zero.mpr i.n_ne_zero⟩

/-- **Reduction of `Ẑ(1)` modulo `𝔪_A`**: `Ẑ(1)_Ω → Ẑ(1)_{κ(A)}`, levelwise `reduceMu`. -/
noncomputable def reduceZHat : ZHatOne K Ω →* ZHatOne k (ResidueField A) where
  toFun x := ⟨fun i => Decomposition.reduceMu A i.n i.n_ne_zero
      (ZHatOne.proj (liftIndex K i) x), fun i j h => by
    rw [← reduceMu_transition A i.n_ne_zero j.n_ne_zero h]
    congr 1
    exact x.2 (liftIndex K i) (liftIndex K j) h⟩
  map_one' := by
    apply Subtype.ext
    funext i
    simp only [map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    funext i
    simp only [map_mul]
    rfl

lemma proj_reduceZHat (i : KummerIndex k) (x : ZHatOne K Ω) :
    ZHatOne.proj i (reduceZHat A K x) =
      Decomposition.reduceMu A i.n i.n_ne_zero (ZHatOne.proj (liftIndex K i) x) := rfl

lemma continuous_reduceZHat : Continuous (reduceZHat (k := k) A K) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  exact continuous_of_discreteTopology.comp (ZHatOne.continuous_proj (liftIndex K i))

end Reduce

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] (A : ValuationSubring Ω)
  [CharZero k] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
  (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)
  (hHL : D.HL = D.H) (ht : t ∈ A)

omit [IsGalois (K₀ k t) Ω] [CharZero k] in
include hk hkres in
/-- The residue field of a place `A ⊇ k` with `κ(A)` algebraic over `k` is algebraically
closed (`κ(A) ≅ k̄`). -/
lemma isAlgClosed_residueField : IsAlgClosed (ResidueField A) :=
  IsAlgClosed.of_ringEquiv (kbar k Ω) _ (kbarEquiv A hk hkres).toRingEquiv

omit [IsGalois (K₀ k t) Ω] in
include hk hkres in
/-- `κ(A) / k` is Galois (`κ(A) ≅ k̄`, characteristic `0`). -/
lemma isGalois_residueField : IsGalois k (ResidueField A) :=
  (kbarEquiv A hk hkres).transfer_galois.mp (isGalois_kbar (k := k) (Ω := Ω))

/-- `s_x` is compatible with the reduction `Ẑ(1)_Ω → Ẑ(1)_{κ(A)}`. -/
lemma reduceZHat_ratSectionMap_smul (g : ResidueField A ≃ₐ[k] ResidueField A)
    (x : ZHatOne (F D) Ω) :
    reduceZHat (k := k) A (F D) (ratSectionMap D A hk hkres hrat hHL ht g • x) =
      g • reduceZHat (k := k) A (F D) x := by
  apply Subtype.ext
  funext i
  haveI : NeZero i.n := ⟨i.n_ne_zero⟩
  change Decomposition.reduceMu A i.n i.n_ne_zero
      (ZHatOne.proj (liftIndex (F D) i) (ratSectionMap D A hk hkres hrat hHL ht g • x)) = _
  rw [proj_pi_smul]
  exact reduceMu_sectionMap_smul D A hk hkres hHL ht _ i.n g _

/-- **The restriction `η|_x = s_x^*(η)`** of a class `η ∈ H¹(Π_U, Ẑ(1))` to a rational point `x`
of `U` ([AbsTopIII] Prop. 1.8, T3 l.2080–2087), with values in
`H¹(Gal(κ(A)/k), Ẑ(1)_{κ(A)})`. -/
noncomputable def restrictPt :
    ContH1 (Pi D) (ZHatOne (F D) Ω) →*
      ContH1 (ResidueField A ≃ₐ[k] ResidueField A) (ZHatOne k (ResidueField A)) :=
  ContH1.map (ratSectionMap D A hk hkres hrat hHL ht)
    (continuous_ratSectionMap D A hk hkres hrat hHL ht) (reduceZHat A (F D))
    (continuous_reduceZHat A (F D)) (reduceZHat_ratSectionMap_smul D A hk hkres hrat hHL ht)

/-- The `μ_n`-component of `η|_x` is the `μ_n`-level restriction of the `μ_n`-component of
`η`. -/
lemma h1Proj_restrictPt (i : KummerIndex k) (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    haveI : NeZero i.n := ⟨i.n_ne_zero⟩
    h1Proj k (ResidueField A) i (restrictPt D A hk hkres hrat hHL ht η) =
      ContH1.map (ratSectionMap D A hk hkres hrat hHL ht)
        (continuous_ratSectionMap D A hk hkres hrat hHL ht)
        (Decomposition.reduceMu A i.n (NeZero.ne i.n)) continuous_of_discreteTopology
        (reduceMu_sectionMap_smul D A hk hkres hHL ht _ i.n)
        (ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj (liftIndex (F D) i))
          (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x) η) := by
  induction η using ContH1.induction_on with
  | h c => rfl

/-- **`κ_U(u)|_x = κ_k(u(x))`** at the `Ẑ(1)`-level ([AbsTopIII] Prop. 1.8): the restriction to
a rational point `x` of the Kummer class of a unit `u` of `U` is the Kummer class of its value
`u(x) = a ∈ kˣ`. -/
theorem restrictPt_kummerMapZHat (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    haveI := isAlgClosed_residueField A hk hkres
    haveI := isGalois_residueField A hk hkres
    restrictPt D A hk hkres hrat hHL ht (kummerMapZHat D u) =
      kummerZHat k (ResidueField A) a := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  apply h1ToLimit_injective k (ResidueField A)
  apply Subtype.ext
  funext i
  haveI : NeZero i.n := ⟨i.n_ne_zero⟩
  rw [h1ToLimit_apply, h1ToLimit_apply]
  rw [h1Proj_restrictPt, map_proj_kummerMapZHat, h1Proj_kummerZHat]
  exact ratSectionMap_kummerMap D A hk hkres hrat hHL ht i.n u a hu hu' hua

/-- **Constant classes restrict to themselves**: for `c ∈ (kˣ)^∧`, the restriction of
`constMapZHat c ∈ H¹(Π_U, Ẑ(1))` to a rational point is `c` under
`H¹(Gal(κ(A)/k), Ẑ(1)) ≃ (kˣ)^∧` ([AbsTopIII] Prop. 1.8(ii), `η|_{G_{k_x}}`). -/
theorem kummerZHatEquiv_restrictPt_constMapZHat (c : KummerCompletion k) :
    haveI := isAlgClosed_residueField A hk hkres
    haveI := isGalois_residueField A hk hkres
    kummerZHatEquiv k (ResidueField A) (restrictPt D A hk hkres hrat hHL ht (constMapZHat D c)) =
      c := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  letI := kbarAlgebra A hk
  haveI := isScalarTower_kbarAlgebra A hk hkres
  rw [← MulEquiv.eq_symm_apply]
  apply h1ToLimit_injective k (ResidueField A)
  apply Subtype.ext
  funext i
  haveI : NeZero i.n := ⟨i.n_ne_zero⟩
  rw [h1ToLimit_apply, h1ToLimit_apply]
  rw [h1Proj_restrictPt]
  have h1 : ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj (liftIndex (F D) i))
      (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x) (constMapZHat D c) =
      ContH1.map (piToGk D) (continuous_piToGk D) (muMap i.n (kbar k Ω) Ω)
        continuous_of_discreteTopology (muMap_piToGk_smul D i.n)
        (h1Proj k (kbar k Ω) i ((kummerZHatEquiv k (kbar k Ω)).symm c)) := by
    rw [constMapZHat_apply]
    induction (kummerZHatEquiv k (kbar k Ω)).symm c using ContH1.induction_on with
    | h c' => rfl
  have h2 : h1Proj k (kbar k Ω) i ((kummerZHatEquiv k (kbar k Ω)).symm c) =
      kummerEquiv i.n k (kbar k Ω) (c.1 i) := by
    change ((h1ZHatOneEquiv k (kbar k Ω)) ((h1ZHatOneEquiv k (kbar k Ω)).symm
      (kummerLimitEquiv k (kbar k Ω) c))).1 i = _
    rw [MulEquiv.apply_symm_apply, kummerLimitEquiv_apply]
  have h3 : h1Proj k (ResidueField A) i ((kummerZHatEquiv k (ResidueField A)).symm c) =
      kummerEquiv i.n k (ResidueField A) (c.1 i) := by
    change ((h1ZHatOneEquiv k (ResidueField A)) ((h1ZHatOneEquiv k (ResidueField A)).symm
      (kummerLimitEquiv k (ResidueField A) c))).1 i = _
    rw [MulEquiv.apply_symm_apply, kummerLimitEquiv_apply]
  rw [h1, ratSectionMap_map_piToGk, h2, h3]
  induction c.1 i using QuotientGroup.induction_on with
  | H a =>
    rw [kummerEquiv_mk, kummerEquiv_mk, restriction_kummer]
    congr 1

/-- **`η|_x` for `η = κ_U(v) · c ∈ P_U`**: `η|_x = v(x) · c` in `(kˣ)^∧`. -/
theorem kummerZHatEquiv_restrictPt_of_eq (v : units D) (a : kˣ) (c : KummerCompletion k)
    (hv : (((v : (F D)ˣ) : F D) : Ω) ∈ A) (hv' : ((((v : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hva : residue A ⟨_, hv⟩ = algebraMap k (ResidueField A) a) :
    haveI := isAlgClosed_residueField A hk hkres
    haveI := isGalois_residueField A hk hkres
    kummerZHatEquiv k (ResidueField A)
        (restrictPt D A hk hkres hrat hHL ht (kummerMapZHat D v * constMapZHat D c)) =
      toKummerCompletion k a * c := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  rw [map_mul, map_mul, restrictPt_kummerMapZHat D A hk hkres hrat hHL ht v a hv hv' hva,
    kummerZHatEquiv_kummerZHat, kummerZHatEquiv_restrictPt_constMapZHat]

end CurvesJacobian.Kummer
