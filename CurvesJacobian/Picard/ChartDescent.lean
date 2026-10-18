/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ChartBaseChange
import CurvesJacobian.Picard.CurveCohomology
import CurvesJacobian.Picard.QuasiFiniteCriterion
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Adjoin.FG

/-!
# Noetherian approximation for two-chart Čech data over `A ⊗_K R`

Let `K` be a field and `R_U → R_W ← R_V` maps of `K`-algebras which are localizations at
`τ ∈ R_U`, `σ ∈ R_V` with `τ σ = 1` on `R_W`, and with `R_U`, `R_V` finite over `K[X]` via `τ`,
`σ` (the two charts of a finite map from a curve to `ℙ¹_K`). For a `K`-algebra `A` consider the
chart rings `A ⊗_K R_U`, `A ⊗_K R_V`, `A ⊗_K R_W`.

* `ChartDescent.chartModule`: the Čech data of matrix data `D` over these rings form a
  `ProjectiveLine.ChartModule A` (a quasi-coherent module on `ℙ¹_A`, given by its charts);
  hence (Serre's theorems on `ℙ¹_A`, formal-schemes) `H¹` is finite, and `H⁰` is finite when `A`
  is Noetherian; the Čech terms are flat over `A`.
* `ChartDescent.hasPerfectModel_noetherian`: over a Noetherian `A` the Čech data have a perfect
  model (Mumford's lemma).
* **`ChartDescent.hasPerfectModel`**: over an ARBITRARY `K`-algebra `A` the Čech data of matrix
  data have a perfect model. Proof by Noetherian approximation: the finitely many matrix entries
  are defined over a finitely generated `K`-subalgebra `A₀ ⊆ A` (Noetherian), the relations
  descend since `A₀ ⊗_K R → A ⊗_K R` is injective, and perfect models are stable under base
  change (cf. the reduction to the Noetherian case in the proof of Stacks, Lemma 36.30.1,
  Tag 0A1H, of which Lemma 36.30.4, Tag 0B91, is a special case).
-/

open TensorProduct LinearMap Polynomial Matrix

universe u

namespace CurvesJacobian.ChartDescent

open ChartMatrix

variable {K : Type u} [Field K] {RU RV RW : Type u} [CommRing RU] [CommRing RV] [CommRing RW]
  [Algebra K RU] [Algebra K RV] [Algebra K RW] (jU : RU →ₐ[K] RW) (jV : RV →ₐ[K] RW)

/-- The chart map `A ⊗ R_U → A ⊗ R_W`. -/
abbrev tens (A : Type u) [CommRing A] [Algebra K A] {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') : A ⊗[K] R →ₐ[A] A ⊗[K] R' :=
  Algebra.TensorProduct.map (AlgHom.id A A) j

lemma tens_tmul (A : Type u) [CommRing A] [Algebra K A] {R R' : Type u} [CommRing R]
    [CommRing R'] [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (a : A) (r : R) :
    tens A j (a ⊗ₜ r) = a ⊗ₜ j r := rfl

section Tensor

variable {B : Type u} [CommRing B] [Algebra K B] {R R' : Type u} [CommRing R] [CommRing R']
  [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (τ : R)

lemma one_tmul_pow (r : R) (k : ℕ) : ((1 : B) ⊗ₜ[K] r) ^ k = (1 : B) ⊗ₜ (r ^ k) := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow]

/-- Localization surjectivity, after tensoring. -/
lemma exists_pow_mul_eq_tens (hloc : ∀ w : R', ∃ (r : R) (k : ℕ), j τ ^ k * w = j r)
    (z : B ⊗[K] R') : ∃ (k : ℕ) (y : B ⊗[K] R), ((1 : B) ⊗ₜ[K] j τ) ^ k * z = tens B j y := by
  induction z with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul b w =>
    obtain ⟨r, k, hk⟩ := hloc w
    refine ⟨k, b ⊗ₜ r, ?_⟩
    rw [one_tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hk, tens_tmul]
  | add x y hx hy =>
    obtain ⟨k₁, y₁, h₁⟩ := hx
    obtain ⟨k₂, y₂, h₂⟩ := hy
    refine ⟨k₁ + k₂, ((1 : B) ⊗ₜ τ) ^ k₂ * y₁ + ((1 : B) ⊗ₜ τ) ^ k₁ * y₂, ?_⟩
    rw [mul_add, map_add, map_mul, map_mul, map_pow, map_pow, tens_tmul, ← h₁, ← h₂, pow_add]
    ring

/-- Localization kernel, after tensoring (uses flatness over the field `K`). -/
lemma exists_pow_mul_eq_zero_tens (hker : ∀ r : R, j r = 0 → ∃ k : ℕ, τ ^ k * r = 0)
    (y : B ⊗[K] R) (hy : tens B j y = 0) : ∃ k : ℕ, ((1 : B) ⊗ₜ[K] τ) ^ k * y = 0 := by
  have hy' : y ∈ LinearMap.ker (AlgebraTensorModule.lTensor B B j.toLinearMap) := hy
  rw [Module.Flat.ker_lTensor_eq] at hy'
  obtain ⟨y', rfl⟩ := hy'
  clear hy
  induction y' with
  | zero => exact ⟨0, by simp⟩
  | tmul b r =>
    obtain ⟨k, hk⟩ := hker r.1 r.2
    refine ⟨k, ?_⟩
    rw [AlgebraTensorModule.lTensor_tmul, one_tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    simp [hk]
  | add x y hx hy =>
    obtain ⟨k₁, h₁⟩ := hx
    obtain ⟨k₂, h₂⟩ := hy
    refine ⟨k₁ + k₂, ?_⟩
    rw [map_add, mul_add, pow_add]
    set t := ((1 : B) ⊗ₜ[K] τ)
    set X := AlgebraTensorModule.lTensor B B (LinearMap.ker j.toLinearMap).subtype x
    set Y := AlgebraTensorModule.lTensor B B (LinearMap.ker j.toLinearMap).subtype y
    calc t ^ k₁ * t ^ k₂ * X + t ^ k₁ * t ^ k₂ * Y = t ^ k₂ * (t ^ k₁ * X) + t ^ k₁ * (t ^ k₂ * Y)
          := by ring
      _ = 0 := by rw [h₁, h₂, mul_zero, mul_zero, add_zero]

end Tensor

section Vec

variable {B : Type u} [CommRing B] [Algebra K B] {R R' : Type u} [CommRing R] [CommRing R']
  [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (τ : R) {n : ℕ}

/-- Localization surjectivity for vectors, with a uniform exponent. -/
lemma exists_pow_smul_eq_comp (hloc : ∀ w : R', ∃ (r : R) (k : ℕ), j τ ^ k * w = j r)
    (z : Fin n → B ⊗[K] R') :
    ∃ (k : ℕ) (y : Fin n → B ⊗[K] R), ((1 : B) ⊗ₜ[K] j τ) ^ k • z = tens B j ∘ y := by
  choose k y hy using fun i ↦ exists_pow_mul_eq_tens j τ hloc (B := B) (z i)
  refine ⟨∑ i, k i, fun i ↦ ((1 : B) ⊗ₜ τ) ^ (∑ i, k i - k i) * y i, funext fun i ↦ ?_⟩
  have hle : k i ≤ ∑ i, k i := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  change ((1 : B) ⊗ₜ[K] j τ) ^ (∑ i, k i) * z i =
    tens B j (((1 : B) ⊗ₜ τ) ^ (∑ i, k i - k i) * y i)
  rw [map_mul, map_pow, tens_tmul, ← hy i, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

/-- Localization kernel for vectors, with a uniform exponent. -/
lemma exists_pow_smul_eq_zero_comp (hker : ∀ r : R, j r = 0 → ∃ k : ℕ, τ ^ k * r = 0)
    (y : Fin n → B ⊗[K] R) (hy : tens B j ∘ y = 0) :
    ∃ k : ℕ, ((1 : B) ⊗ₜ[K] τ) ^ k • y = 0 := by
  choose k hk using fun i ↦ exists_pow_mul_eq_zero_tens j τ hker (y i) (congrFun hy i)
  refine ⟨∑ i, k i, funext fun i ↦ ?_⟩
  have hle : k i ≤ ∑ i, k i := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  change ((1 : B) ⊗ₜ[K] τ) ^ (∑ i, k i) * y i = 0
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hk i, mul_zero]

end Vec

section SmulL

variable {A S M : Type u} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]
  [Module A M] [IsScalarTower A S M]

/-- Multiplication by `c ∈ S` on an `S`-submodule, as an `A`-linear map. -/
def smulL (p : Submodule S M) (c : S) : p →ₗ[A] p where
  toFun x := c • x
  map_add' := smul_add c
  map_smul' a x := by
    rw [RingHom.id_apply, ← algebraMap_smul S a x, smul_smul, mul_comm, ← smul_smul,
      algebraMap_smul]

lemma smulL_pow_apply (p : Submodule S M) (c : S) (k : ℕ) (x : p) :
    (smulL (A := A) p c ^ k) x = c ^ k • x := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', mul_smul]
    rfl

end SmulL

section Chart

variable {jU jV} (τ : RU) (σ : RV) (hτσ : jU τ * jV σ = 1)
  (hlocU : ∀ w : RW, ∃ (r : RU) (k : ℕ), jU τ ^ k * w = jU r)
  (hkerU : ∀ r : RU, jU r = 0 → ∃ k : ℕ, τ ^ k * r = 0)
  (hlocV : ∀ w : RW, ∃ (r : RV) (k : ℕ), jV σ ^ k * w = jV r)
  (hkerV : ∀ r : RV, jV r = 0 → ∃ k : ℕ, σ ^ k * r = 0)
  {A : Type u} [CommRing A] [Algebra K A] (D : MatData (tens A jU) (tens A jV))

lemma map_mulVec_alg {S S' : Type u} [CommRing S] [CommRing S'] [Algebra A S] [Algebra A S']
    (f : S →ₐ[A] S') {a b : ℕ} (M : Matrix (Fin a) (Fin b) S) (v : Fin b → S) :
    M.map f *ᵥ (f ∘ v) = f ∘ (M *ᵥ v) :=
  map_mulVec_comp (f : S →+* S') M v

include hτσ in
lemma tmul_unit : ((1 : A) ⊗ₜ[K] jU τ) * ((1 : A) ⊗ₜ[K] jV σ) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hτσ]
  rfl

/-- Multiplication by the chart coordinate `T = τ = σ⁻¹` on the overlap. -/
def chartT : D.PW ≃ₗ[A] D.PW :=
  LinearEquiv.ofLinear (smulL D.PW ((1 : A) ⊗ₜ[K] jU τ)) (smulL D.PW ((1 : A) ⊗ₜ[K] jV σ))
    (LinearMap.ext fun x ↦ by
      change ((1 : A) ⊗ₜ[K] jU τ) • ((1 : A) ⊗ₜ[K] jV σ) • x = x
      rw [smul_smul, tmul_unit τ σ hτσ, one_smul])
    (LinearMap.ext fun x ↦ by
      change ((1 : A) ⊗ₜ[K] jV σ) • ((1 : A) ⊗ₜ[K] jU τ) • x = x
      rw [smul_smul, mul_comm, tmul_unit τ σ hτσ, one_smul])

lemma chartT_pow_apply (k : ℕ) (z : D.PW) :
    (((chartT τ σ hτσ D) ^ k) z : Fin D.n → A ⊗[K] RW) = ((1 : A) ⊗ₜ[K] jU τ) ^ k • z.1 := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, pow_succ', mul_smul, ← ih]
    rfl

lemma chartT_symm_pow_apply (k : ℕ) (z : D.PW) :
    (((chartT τ σ hτσ D).symm ^ k) z : Fin D.n → A ⊗[K] RW) =
      ((1 : A) ⊗ₜ[K] jV σ) ^ k • z.1 := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, pow_succ', mul_smul, ← ih]
    rfl

include hlocU hkerU hlocV hkerV in
/-- **The Čech data of matrix data over `A ⊗ R` form a quasi-coherent module on `ℙ¹_A`**, given
by its two charts (`ProjectiveLine.ChartModule`). -/
def chartModule : ProjectiveLine.ChartModule A where
  M0 := ModuleCat.of A D.PU
  M1 := ModuleCat.of A D.PV
  M01 := ModuleCat.of A D.PW
  x0 := smulL D.PU ((1 : A) ⊗ₜ[K] τ)
  x1 := smulL D.PV ((1 : A) ⊗ₜ[K] σ)
  t := chartT τ σ hτσ D
  r0 := D.fU
  r1 := D.fV
  r0_x0 m := Subtype.ext <| funext fun i ↦ by
    change tens A jU (((1 : A) ⊗ₜ[K] τ) * m.1 i) = ((1 : A) ⊗ₜ[K] jU τ) * tens A jU (m.1 i)
    rw [map_mul, tens_tmul]
  r1_x1 m := Subtype.ext <| by
    change D.Φ *ᵥ (tens A jV ∘ (((1 : A) ⊗ₜ[K] σ) • m.1)) =
      ((1 : A) ⊗ₜ[K] jV σ) • (D.Φ *ᵥ (tens A jV ∘ m.1))
    have : tens A jV ∘ (((1 : A) ⊗ₜ[K] σ) • m.1) =
        ((1 : A) ⊗ₜ[K] jV σ) • (tens A jV ∘ m.1) := funext fun i ↦ by
      change tens A jV (((1 : A) ⊗ₜ[K] σ) * m.1 i) = ((1 : A) ⊗ₜ[K] jV σ) * tens A jV (m.1 i)
      rw [map_mul, tens_tmul]
    rw [this, Matrix.mulVec_smul]
  exists_r0 z := by
    obtain ⟨k, y, hk⟩ := exists_pow_smul_eq_comp jU τ hlocU z.1
    refine ⟨fixProj (R := A) D.eU D.eU_mul y, k, Subtype.ext ?_⟩
    rw [chartT_pow_apply]
    change _ = tens A jU ∘ (D.eU *ᵥ y)
    rw [← map_mulVec_alg, ← hk, Matrix.mulVec_smul, mem_fixSub.mp z.2]
  ker_r0 m hm := by
    have h0 : tens A jU ∘ m.1 = 0 := congrArg Subtype.val hm
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_comp jU τ hkerU m.1 h0
    exact ⟨k, Subtype.ext (by rw [smulL_pow_apply]; exact hk)⟩
  exists_r1 z := by
    obtain ⟨k, y, hk⟩ := exists_pow_smul_eq_comp jV σ hlocV (D.Ψ *ᵥ z.1)
    refine ⟨fixProj (R := A) D.eV D.eV_mul y, k, Subtype.ext ?_⟩
    rw [chartT_symm_pow_apply]
    change _ = D.Φ *ᵥ (tens A jV ∘ (D.eV *ᵥ y))
    rw [← map_mulVec_alg, ← hk, Matrix.mulVec_mulVec, D.Φ_eV, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, D.Φ_Ψ, mem_fixSub.mp z.2]
  ker_r1 m hm := by
    have h0 : D.Φ *ᵥ (tens A jV ∘ m.1) = 0 := congrArg Subtype.val hm
    have h1 : tens A jV ∘ m.1 = 0 := by
      calc tens A jV ∘ m.1 = tens A jV ∘ (D.eV *ᵥ m.1) := by rw [mem_fixSub.mp m.2]
        _ = (D.eV.map (tens A jV)) *ᵥ (tens A jV ∘ m.1) := (map_mulVec_alg _ _ _).symm
        _ = (D.Ψ * D.Φ) *ᵥ (tens A jV ∘ m.1) := by rw [D.Ψ_Φ]
        _ = D.Ψ *ᵥ (D.Φ *ᵥ (tens A jV ∘ m.1)) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by rw [h0, Matrix.mulVec_zero]
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_comp jV σ hkerV m.1 h1
    exact ⟨k, Subtype.ext (by rw [smulL_pow_apply]; exact hk)⟩

/-- The chart modules are flat over `A`. -/
lemma flat_fixSub {R : Type u} [CommRing R] [Algebra K R] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) (A ⊗[K] R)) (he : e * e = e) : Module.Flat A (fixSub e) :=
  Module.Flat.of_retract (fixIncl (R := A) e) (fixProj e he) (fixProj_fixIncl e he)

lemma finite_fixSub {R : Type u} [CommRing R] {n : ℕ} (e : Matrix (Fin n) (Fin n) R)
    (he : e * e = e) : Module.Finite R (fixSub e) :=
  Module.Finite.of_surjective (fixProj (R := R) e he)
    fun v ↦ ⟨v.1, Subtype.ext (show e *ᵥ v.1 = v.1 from mem_fixSub.mp v.2)⟩

include hτσ hlocU hkerU hlocV hkerV in
/-- **Over a Noetherian ring, matrix data have a perfect model** (Serre's finiteness on `ℙ¹_A`
for the chart module, plus Mumford's lemma). -/
theorem hasPerfectModel_noetherian
    (hfinU : letI := (aeval (R := K) τ).toRingHom.toAlgebra; Module.Finite K[X] RU)
    (hfinV : letI := (aeval (R := K) σ).toRingHom.toAlgebra; Module.Finite K[X] RV)
    [IsNoetherianRing A] : D.HasPerfectModel := by
  haveI := finite_fixSub D.eU D.eU_mul
  haveI := finite_fixSub D.eV D.eV_mul
  haveI := flat_fixSub D.eU D.eU_mul
  haveI := flat_fixSub D.eV D.eV_mul
  haveI := flat_fixSub (D.eU.map (tens A jU)) (by rw [← map_mul_hom, D.eU_mul])
  let M := chartModule τ σ hτσ hlocU hkerU hlocV hkerV D
  haveI h0 : Module.Finite A[X] (Module.AEval' M.x0) :=
    finite_aeval_of_finite ((1 : A) ⊗ₜ[K] τ) (smulL (A := A) D.PU ((1 : A) ⊗ₜ[K] τ))
      (fun _ ↦ rfl) (QuasiFiniteCriterion.finite_tensor_polynomial A τ hfinU)
  haveI h1 : Module.Finite A[X] (Module.AEval' M.x1) :=
    finite_aeval_of_finite ((1 : A) ⊗ₜ[K] σ) (smulL (A := A) D.PV ((1 : A) ⊗ₜ[K] σ))
      (fun _ ↦ rfl) (QuasiFiniteCriterion.finite_tensor_polynomial A σ hfinV)
  exact TwoTerm.hasPerfectModel_of_noetherian D.fU D.fV M.finite_H0 M.finite_H1

end Chart

section Descent

variable {A : Type u} [CommRing A] [Algebra K A] {R : Type u} [CommRing R] [Algebra K R]

/-- The inclusion `A₀ ⊗_K R → A ⊗_K R` for a subalgebra `A₀ ⊆ A`. -/
abbrev incl (A₀ : Subalgebra K A) (R : Type u) [CommRing R] [Algebra K R] :
    A₀ ⊗[K] R →ₐ[A₀] A ⊗[K] R :=
  Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id K R)

lemma incl_tmul (A₀ : Subalgebra K A) (a : A₀) (r : R) : incl A₀ R (a ⊗ₜ r) = (a : A) ⊗ₜ r :=
  rfl

/-- Every element of `A ⊗_K R` comes from `A₀ ⊗_K R` for `A₀` containing a finite set. -/
lemma exists_finset_mem_range (x : A ⊗[K] R) : ∃ s : Finset A, ∀ A₀ : Subalgebra K A,
    (↑s : Set A) ⊆ A₀ → ∃ y : A₀ ⊗[K] R, incl A₀ R y = x := by
  classical
  induction x with
  | zero => exact ⟨∅, fun _ _ ↦ ⟨0, map_zero _⟩⟩
  | tmul a r => exact ⟨{a}, fun A₀ h ↦ ⟨⟨a, h (by simp)⟩ ⊗ₜ r, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun A₀ h ↦ ?_⟩
    rw [Finset.coe_union, Set.union_subset_iff] at h
    obtain ⟨x', hx'⟩ := hs A₀ h.1
    obtain ⟨y', hy'⟩ := ht A₀ h.2
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

/-- Every matrix over `A ⊗_K R` comes from `A₀ ⊗_K R` for `A₀` containing a finite set. -/
lemma exists_finset_matrix {a b : ℕ} (M : Matrix (Fin a) (Fin b) (A ⊗[K] R)) :
    ∃ s : Finset A, ∀ A₀ : Subalgebra K A, (↑s : Set A) ⊆ A₀ →
      ∃ M₀ : Matrix (Fin a) (Fin b) (A₀ ⊗[K] R), M₀.map (incl A₀ R) = M := by
  classical
  choose s hs using fun p : Fin a × Fin b ↦ exists_finset_mem_range (M p.1 p.2)
  refine ⟨Finset.univ.biUnion s, fun A₀ hA₀ ↦ ?_⟩
  have : ∀ p : Fin a × Fin b, ∃ y, incl A₀ R y = M p.1 p.2 := fun p ↦
    hs p A₀ ((Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem s (Finset.mem_univ p))).trans
      hA₀)
  choose y hy using this
  exact ⟨Matrix.of fun i j ↦ y (i, j), by ext i j; exact hy (i, j)⟩

lemma incl_injective (A₀ : Subalgebra K A) : Function.Injective (incl A₀ R) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := R)
    (A₀.val.toLinearMap) Subtype.val_injective
  convert h using 1
  funext x
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a r => rfl

lemma isBaseChange_incl (A₀ : Subalgebra K A) : IsBaseChange A (incl A₀ R).toLinearMap := by
  refine IsBaseChange.of_equiv
    (Algebra.TensorProduct.cancelBaseChange K A₀ A A R).toLinearEquiv fun x ↦ ?_
  induction x with
  | zero => simp
  | add x y hx hy => rw [tmul_add, map_add, hx, hy, map_add]
  | tmul a r =>
    rw [AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.cancelBaseChange_tmul]
    change (a • (1 : A)) ⊗ₜ r = (a : A) ⊗ₜ r
    rw [Algebra.smul_def, mul_one]
    rfl

lemma incl_tens (A₀ : Subalgebra K A) {R' : Type u} [CommRing R'] [Algebra K R']
    (j : R →ₐ[K] R') (x : A₀ ⊗[K] R) : incl A₀ R' (tens A₀ j x) = tens A j (incl A₀ R x) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a r => rfl

variable (τ : RU) (σ : RV) (hτσ : jU τ * jV σ = 1)
  (hlocU : ∀ w : RW, ∃ (r : RU) (k : ℕ), jU τ ^ k * w = jU r)
  (hkerU : ∀ r : RU, jU r = 0 → ∃ k : ℕ, τ ^ k * r = 0)
  (hlocV : ∀ w : RW, ∃ (r : RV) (k : ℕ), jV σ ^ k * w = jV r)
  (hkerV : ∀ r : RV, jV r = 0 → ∃ k : ℕ, σ ^ k * r = 0)
  (hfinU : letI := (aeval (R := K) τ).toRingHom.toAlgebra; Module.Finite K[X] RU)
  (hfinV : letI := (aeval (R := K) σ).toRingHom.toAlgebra; Module.Finite K[X] RV)

include hτσ hlocU hkerU hlocV hkerV hfinU hfinV in
/-- **Noetherian approximation**: over an arbitrary `K`-algebra `A`, the two-chart Čech data of
matrix data over `A ⊗_K R` have a perfect model (Stacks, Lemma 36.30.4, Tag 0B91, for this
two-affine situation, with the reduction to the Noetherian case as in Lemma 36.30.1,
Tag 0A1H). -/
theorem hasPerfectModel (D : MatData (tens A jU) (tens A jV)) : D.HasPerfectModel := by
  classical
  obtain ⟨n, m, eU, eV, Φ, Ψ, h1, h2, h3, h4, h5, h6⟩ := D
  obtain ⟨s₁, hs₁⟩ := exists_finset_matrix eU
  obtain ⟨s₂, hs₂⟩ := exists_finset_matrix eV
  obtain ⟨s₃, hs₃⟩ := exists_finset_matrix Φ
  obtain ⟨s₄, hs₄⟩ := exists_finset_matrix Ψ
  set A₀ := Algebra.adjoin K (↑(s₁ ∪ s₂ ∪ s₃ ∪ s₄) : Set A) with hA₀
  haveI : IsNoetherianRing A₀ := isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset _)
  have hsub : (↑(s₁ ∪ s₂ ∪ s₃ ∪ s₄) : Set A) ⊆ A₀ := Algebra.subset_adjoin
  simp only [Finset.coe_union, Set.union_subset_iff] at hsub
  obtain ⟨eU₀, heU⟩ := hs₁ A₀ hsub.1.1.1
  obtain ⟨eV₀, heV⟩ := hs₂ A₀ hsub.1.1.2
  obtain ⟨Φ₀, hΦ⟩ := hs₃ A₀ hsub.1.2
  obtain ⟨Ψ₀, hΨ⟩ := hs₄ A₀ hsub.2
  have iU := incl_injective (R := RU) A₀
  have iV := incl_injective (R := RV) A₀
  have iW := incl_injective (R := RW) A₀
  have cU : ∀ x, incl A₀ RW (tens A₀ jU x) = tens A jU (incl A₀ RU x) := incl_tens A₀ jU
  have cV : ∀ x, incl A₀ RW (tens A₀ jV x) = tens A jV (incl A₀ RV x) := incl_tens A₀ jV
  have mU : (eU₀.map (tens A₀ jU)).map (incl A₀ RW) = eU.map (tens A jU) := by
    ext i j
    change incl A₀ RW (tens A₀ jU (eU₀ i j)) = tens A jU (eU i j)
    rw [cU, ← heU]
    rfl
  have mV : (eV₀.map (tens A₀ jV)).map (incl A₀ RW) = eV.map (tens A jV) := by
    ext i j
    change incl A₀ RW (tens A₀ jV (eV₀ i j)) = tens A jV (eV i j)
    rw [cV, ← heV]
    rfl
  let D₀ : MatData (tens A₀ jU) (tens A₀ jV) :=
    { n := n, m := m, eU := eU₀, eV := eV₀, Φ := Φ₀, Ψ := Ψ₀
      eU_mul := Matrix.map_injective iU (show (eU₀ * eU₀).map (incl A₀ RU) = eU₀.map _ by
        rw [map_mul_hom, heU, h1])
      eV_mul := Matrix.map_injective iV (show (eV₀ * eV₀).map (incl A₀ RV) = eV₀.map _ by
        rw [map_mul_hom, heV, h2])
      Φ_Ψ := Matrix.map_injective iW (show (Φ₀ * Ψ₀).map (incl A₀ RW) =
          (eU₀.map (tens A₀ jU)).map (incl A₀ RW) by
        rw [map_mul_hom, hΦ, hΨ, h3, mU])
      Ψ_Φ := Matrix.map_injective iW (show (Ψ₀ * Φ₀).map (incl A₀ RW) =
          (eV₀.map (tens A₀ jV)).map (incl A₀ RW) by
        rw [map_mul_hom, hΦ, hΨ, h4, mV])
      eU_Φ := Matrix.map_injective iW (show ((eU₀.map (tens A₀ jU)) * Φ₀).map (incl A₀ RW) =
        Φ₀.map _ by rw [map_mul_hom, hΦ, mU, h5])
      Φ_eV := Matrix.map_injective iW (show (Φ₀ * (eV₀.map (tens A₀ jV))).map (incl A₀ RW) =
        Φ₀.map _ by rw [map_mul_hom, hΦ, mV, h6]) }
  have H₀ := hasPerfectModel_noetherian τ σ hτσ hlocU hkerU hlocV hkerV D₀ hfinU hfinV
  have H := D₀.hasPerfectModel_mapBC (incl A₀ RU) (incl A₀ RV) (incl A₀ RW) cU cV
    (isBaseChange_incl A₀) (isBaseChange_incl A₀) (isBaseChange_incl A₀) H₀
  have e : D₀.mapBC (incl A₀ RU) (incl A₀ RV) (incl A₀ RW) cU cV =
      ⟨n, m, eU, eV, Φ, Ψ, h1, h2, h3, h4, h5, h6⟩ := by
    simp only [MatData.mapBC, D₀, heU, heV, hΦ, hΨ]
  rw [e] at H
  exact H

end Descent

end CurvesJacobian.ChartDescent
