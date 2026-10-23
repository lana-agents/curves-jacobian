/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThmC
import CurvesJacobian.Kummer.PointRestriction

/-!
# [LocAn] Theorem C via Kummer classes of units (MR7 S3(a), first part)

For a curve of genus `0` the Jacobian argument of `LocAn/ThmC.lean` is empty. Kummer classes of
units of `U` replace it ([LocAn] l.5116–5118 for the profinite version; [AbsTopIII] Prop. 1.8 for
the restriction of Kummer classes to points). This file proves the units form of Theorem C, in
`pi1`'s Galois model (`D : GaloisData k t`), for any field `k` of characteristic `0` that is
Kummer-faithful for `𝔾_m` (number fields and finite extensions of `ℚ_p`).

> If two rational points `x, y` of `U` have `Δ_U`-conjugate sections `s_x, s_y : G_k → Π_U`, then
> `w(x) = w(y)` for every unit `w ∈ Γ(U, 𝒪_U^×)`.

The proof uses two facts.
* A cocycle `c` of `Π_U` with values in `μ_n` satisfies
  `c(δ s δ⁻¹) = (s • c(δ))⁻¹ · c(s) · c(δ)` for `δ ∈ Δ_U` (`cocycle_conj`), because `Δ_U` acts
  trivially on `μ_n ⊆ k̄`. So `c ∘ s_x` is a coboundary iff `c ∘ s_y` is (`isTrivAlong_conj`).
* Triviality of the restriction of a class to `x`, computed in `H¹(Gal(κ(A_x)/k), μ_n(κ(A_x)))`, is
  the same as `c ∘ s_x` being a coboundary with values in `μ_n(Ω)`
  (`map_ratSectionMap_mk_eq_one_iff`). Reduction `μ_n(Ω) → μ_n(κ(A_x))` is bijective
  (`reduceMu_injective`, `reduceMu_surjective`).

Then `κ_U(w) / κ_U(w(y))` restricts trivially to `y`, hence to `x`, so `w(x)/w(y)` is an `n`-th
power for every `n` ([AbsTopIII] Prop. 1.8(ii), `ratSectionMap_kummerMap`).

## Main results

* `CurvesJacobian.LocAn.cocycle_conj`, `CurvesJacobian.LocAn.isTrivAlong_conj`;
* `CurvesJacobian.LocAn.map_ratSectionMap_mk_eq_one_iff`;
* **`CurvesJacobian.LocAn.eq_of_ratSectionGk_conj_units`**: the units form of Theorem C.

For `U ⊆ ℙ¹ ∖ {0, ∞}` the coordinate is a unit, so this separates rational points. Turning that
into `placeOfF x = placeOfF y` is MR7 plan S3(a) step 3. The general genus-`0` case (no two
rational cusps) needs a finite extension making two cusps rational: S3(a) step 4 and S3(c).
-/

universe u

open KummerTheory Curve AffOrbicurve IsLocalRing CurvesJacobian.Kummer groupCohomology

namespace CurvesJacobian.LocAn

/-- **Cocycles under conjugation by an element acting trivially.** For a `1`-cocycle `c` and `δ`
acting trivially on `M`: `c(δ s δ⁻¹) = (s • c(δ))⁻¹ · c(s) · c(δ)`. -/
theorem cocycle_conj {P M : Type*} [Group P] [CommGroup M] [MulDistribMulAction P M]
    {c : P → M} (hc : IsMulCocycle₁ c) {δ : P} (hδ : ∀ m : M, δ • m = m) (s : P) :
    c (δ * s * δ⁻¹) = (s • c δ)⁻¹ * c s * c δ := by
  have hδ' : ∀ m : M, δ⁻¹ • m = m := fun m ↦ by
    have := hδ (δ⁻¹ • m)
    rw [smul_inv_smul] at this
    exact this.symm
  have h1 : c 1 = 1 := by simpa using hc 1 1
  have hinv : c δ⁻¹ = (c δ)⁻¹ := by
    have := hc δ⁻¹ δ
    rw [inv_mul_cancel, h1, hδ'] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  rw [hc, hc, hinv, mul_smul, hδ, hδ, smul_inv']
  exact (mul_assoc _ _ _).symm

theorem comm_aux {M : Type*} [CommGroup M] (a b m d : M) :
    a⁻¹ * (b / m) * d = b / a / (m / d) := by
  simp only [div_eq_mul_inv, mul_inv, inv_inv, mul_comm, mul_assoc, mul_left_comm]

section General

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- `c ∘ s` is a coboundary with values in `μ_n(Ω)` (for `s : G_k → Π_U`). -/
def IsTrivAlong {n : ℕ} [NeZero n] (c : Pi D → Mu n Ω) (s : Gk k Ω →* Pi D) : Prop :=
  ∃ m : Mu n Ω, ∀ g, c (s g) = s g • m / m

/-- Elements of `Δ_U = ker(Π_U → G_k)` act trivially on `μ_n(Ω)` (`μ_n ⊆ k̄`). -/
theorem smul_mu_of_piToGk_eq_one {n : ℕ} [NeZero n] {δ : Pi D} (hδ : piToGk D δ = 1)
    (m : Mu n Ω) : δ • m = m := by
  obtain ⟨m₀, rfl⟩ := muMap_surjective (k := k) (Ω := Ω) n m
  rw [← muMap_piToGk_smul D n δ m₀, hδ, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **Coboundaries along `Δ_U`-conjugate sections.** -/
theorem isTrivAlong_conj {n : ℕ} [NeZero n] {c : Pi D → Mu n Ω} (hc : IsMulCocycle₁ c)
    {s s' : Gk k Ω →* Pi D} {δ : Pi D} (hδ : piToGk D δ = 1)
    (hs : ∀ g, s' g = δ * s g * δ⁻¹) (h : IsTrivAlong c s) : IsTrivAlong c s' := by
  obtain ⟨m, hm⟩ := h
  have hδm := smul_mu_of_piToGk_eq_one (D := D) (n := n) hδ
  have hδm' : ∀ m : Mu n Ω, δ⁻¹ • m = m := fun m ↦ by
    have := hδm (δ⁻¹ • m)
    rw [smul_inv_smul] at this
    exact this.symm
  refine ⟨m / c δ, fun g ↦ ?_⟩
  rw [hs, cocycle_conj hc hδm, hm, mul_smul, mul_smul, hδm', hδm, smul_div']
  exact comm_aux _ _ _ _

/-- `muMap` along an injective ring homomorphism is injective. -/
theorem muMap_injective (n : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Function.Injective (muMap n K L) := by
  intro a b h
  apply Mu.ext
  apply Units.ext
  have := congrArg (fun z ↦ ((Mu.val z : Lˣ) : L)) h
  simp only [val_muMap, Units.coe_map, MonoidHom.coe_coe] at this
  exact (algebraMap K L).injective this

/-- `muMap` along a surjective ring homomorphism is surjective. -/
theorem muMap_surjective_of_surjective (n : ℕ) {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hs : Function.Surjective (algebraMap K L)) : Function.Surjective (muMap n K L) := by
  intro m
  obtain ⟨z, hz⟩ := hs ((Mu.val m : Lˣ) : L)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact (Mu.val m).ne_zero hz.symm
  have hzn : (Units.mk0 z hz0) ^ n = 1 := by
    apply Units.ext
    apply (algebraMap K L).injective
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hz, Units.val_one, map_one,
      ← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]
  refine ⟨Mu.mk _ hzn, Mu.ext (Units.ext ?_)⟩
  simp [hz]

variable (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]

omit [CharZero k] [IsAlgClosed Ω] [Algebra k (ResidueField A)]
  [Algebra.IsIntegral k (ResidueField A)] in
include hk in
/-- Reduction `μ_n(Ω) → μ_n(κ(A))` is injective at a place `A` over `k` with `κ(A)` algebraic. -/
theorem reduceMu_injective (n : ℕ) [NeZero n] :
    Function.Injective (Decomposition.reduceMu A n (NeZero.ne n)) := by
  letI := kbarAlgebra A hk
  intro a b h
  obtain ⟨a₀, rfl⟩ := muMap_surjective (k := k) (Ω := Ω) n a
  obtain ⟨b₀, rfl⟩ := muMap_surjective (k := k) (Ω := Ω) n b
  rw [reduceMu_muMap A hk n, reduceMu_muMap A hk n] at h
  rw [muMap_injective n (kbar k Ω) (ResidueField A) h]

omit [CharZero k] in
include hkres in
/-- Reduction `μ_n(Ω) → μ_n(κ(A))` is surjective at a place `A` over `k` with `κ(A)`
algebraic. -/
theorem reduceMu_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (Decomposition.reduceMu A n (NeZero.ne n)) := by
  letI := kbarAlgebra A hk
  intro m
  obtain ⟨m₀, rfl⟩ := muMap_surjective_of_surjective n
    (K := kbar k Ω) (L := ResidueField A) (kbarResidue_surjective A hk hkres) m
  exact ⟨_, reduceMu_muMap A hk n m₀⟩

/-- **Restriction to a rational point is trivial iff the cocycle is a coboundary along the
section** (with values in `μ_n(Ω)`). -/
theorem map_ratSectionMap_mk_eq_one_iff (x : RatPoint D) (hHL : D.HL = D.H) (ht : t ∈ x.A)
    (n : ℕ) [NeZero n] (c : ContH1.cocycles (Pi D) (Mu n Ω)) :
    ContH1.map (ratSectionMap D x.A x.hk x.hkres x.hrat hHL ht)
        (continuous_ratSectionMap D x.A x.hk x.hkres x.hrat hHL ht)
        (Decomposition.reduceMu x.A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_sectionMap_smul D x.A x.hk x.hkres hHL ht _ n) (ContH1.mk c) = 1 ↔
      IsTrivAlong (c : Pi D → Mu n Ω) (ratSectionGk x hHL ht) := by
  rw [ContH1.map_mk, ContH1.mk_eq_one_iff]
  have hR1 := reduceMu_injective x.A x.hk n
  have hR2 := reduceMu_surjective x.A x.hk x.hkres n
  set e := AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) with he
  constructor
  · rintro ⟨m', hm'⟩
    obtain ⟨m, rfl⟩ := hR2 m'
    refine ⟨m, fun g ↦ hR1 ?_⟩
    have h1 := hm' (e g)
    rw [ContH1.cocyclesMap_apply] at h1
    rw [map_div]
    change Decomposition.reduceMu x.A n (NeZero.ne n)
        (c (ratSectionMap D x.A x.hk x.hkres x.hrat hHL ht (e g))) =
      Decomposition.reduceMu x.A n (NeZero.ne n)
        (ratSectionMap D x.A x.hk x.hkres x.hrat hHL ht (e g) • m) / _
    refine h1.symm.trans ?_
    congr 1
    exact (reduceMu_sectionMap_smul D x.A x.hk x.hkres hHL ht
      (decompositionMap_surjective_of_rational D x.A x.hk x.hkres x.hrat) n (e g) m).symm
  · rintro ⟨m, hm⟩
    refine ⟨Decomposition.reduceMu x.A n (NeZero.ne n) m, fun τ ↦ ?_⟩
    obtain ⟨g, rfl⟩ := e.surjective τ
    rw [ContH1.cocyclesMap_apply, ← reduceMu_sectionMap_smul D x.A x.hk x.hkres hHL ht
      (decompositionMap_surjective_of_rational D x.A x.hk x.hkres x.hrat) n, ← map_div]
    exact congrArg _ (hm g).symm

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite), units form**: if two rational points `x, y` of `U` have
`Δ_U`-conjugate sections `s_x, s_y : G_k → Π_U` and `k` is Kummer-faithful for `𝔾_m`, then every
unit `w` of `U` takes the same value at `x` and `y` (`w(x) = a`, `w(y) = b` ⇒ `a = b`). -/
theorem eq_of_ratSectionGk_conj_units (hkf : IsKummerFaithfulGm k) (hHL : D.HL = D.H)
    {x y : RatPoint D} (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D} (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹)
    (w : units D) (a b : kˣ)
    (hwx : (((w : (F D)ˣ) : F D) : Ω) ∈ x.A)
    (hwx' : ((((w : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ x.A)
    (hwa : residue x.A ⟨_, hwx⟩ = algebraMap k (ResidueField x.A) a)
    (hwy : (((w : (F D)ˣ) : F D) : Ω) ∈ y.A)
    (hwy' : ((((w : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ y.A)
    (hwb : residue y.A ⟨_, hwy⟩ = algebraMap k (ResidueField y.A) b) :
    a = b := by
  haveI := isAlgClosed_residueField x.A x.hk x.hkres
  haveI := isAlgClosed_residueField y.A y.hk y.hkres
  haveI := isGalois_residueField x.A x.hk x.hkres
  have hcx : (((constUnit D b : (F D)ˣ) : F D) : Ω) ∈ x.A := x.hk b
  have hcx' : ((((constUnit D b : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ x.A := x.hk (b⁻¹ : kˣ)
  have hcy : (((constUnit D b : (F D)ˣ) : F D) : Ω) ∈ y.A := y.hk b
  have hcy' : ((((constUnit D b : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ y.A := y.hk (b⁻¹ : kˣ)
  have hδ' : piToGk D δ⁻¹ = 1 := by rw [map_inv, MonoidHom.mem_ker.1 hδ, inv_one]
  have key : ∀ (n : ℕ) [NeZero n], kummer n k (ResidueField x.A) (a / b) = 1 := by
    intro n _
    obtain ⟨c, hc⟩ := ContH1.mk_surjective
      (kummerMap D n w / kummerMap D n (constUnit D b))
    have hyθ := congrArg (ContH1.map (ratSectionMap D y.A y.hk y.hkres y.hrat hHL hy)
        (continuous_ratSectionMap D y.A y.hk y.hkres y.hrat hHL hy)
        (Decomposition.reduceMu y.A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_sectionMap_smul D y.A y.hk y.hkres hHL hy _ n)) hc
    rw [map_div, ratSectionMap_kummerMap D y.A y.hk y.hkres y.hrat hHL hy n w b hwy hwy' hwb,
      ratSectionMap_kummerMap D y.A y.hk y.hkres y.hrat hHL hy n (constUnit D b) b hcy hcy'
        (y.hkres b), div_self'] at hyθ
    rw [map_ratSectionMap_mk_eq_one_iff y hHL hy n c] at hyθ
    have hxθ := isTrivAlong_conj (ContH1.isMulCocycle₁ c) (s := ratSectionGk y hHL hy)
      (s' := ratSectionGk x hHL hx) hδ' (fun g ↦ by rw [h g]; group) hyθ
    rw [← map_ratSectionMap_mk_eq_one_iff x hHL hx n c, hc, map_div,
      ratSectionMap_kummerMap D x.A x.hk x.hkres x.hrat hHL hx n w a hwx hwx' hwa,
      ratSectionMap_kummerMap D x.A x.hk x.hkres x.hrat hHL hx n (constUnit D b) b hcx hcx'
        (x.hkres b)] at hxθ
    rw [map_div]
    exact hxθ
  refine div_eq_one.mp (hkf _ fun n hn ↦ ?_)
  haveI : NeZero n := ⟨hn.ne'⟩
  have hker : a / b ∈ (kummer n k (ResidueField x.A)).ker := key n
  rw [ker_kummer] at hker
  exact hker

end General

end CurvesJacobian.LocAn
