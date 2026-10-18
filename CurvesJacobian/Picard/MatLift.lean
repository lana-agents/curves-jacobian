/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Lifting matrix data along square-zero extensions

Let `q : R → R̄` be a surjective ring homomorphism whose kernel has square zero
(`CurvesJacobian.MatLift.SqZero q`: `a b ∈ ker q ⇒ a b = 0`). This file lifts the matrix data of
finite projective modules glued along two charts (cf. `CurvesJacobian.MatSheaf.Data`):

* `MatLift.exists_idempotent_lift`: idempotent matrices lift (Mathlib's
  `exists_isIdempotentElem_eq_of_ker_isNilpotent`, applied to `Mₙ(R) → Mₙ(R̄)`);
* `MatLift.exists_gluing_lift`: given idempotents `e_U`, `e_V` over the overlap ring lifting
  `ē_U`, `ē_V`, gluing matrices `Φ̄`, `Ψ̄` with `Φ̄ Ψ̄ = ē_U`, `Ψ̄ Φ̄ = ē_V`, `ē_U Φ̄ = Φ̄ = Φ̄ ē_V`
  lift to `Φ`, `Ψ` with the same relations and `Φ ↦ Φ̄` (the obstruction to lifting the gluing
  isomorphism of the modules vanishes: it would live in an `H²`, and there are only two charts);
* `MatLift.exists_rankOne_lift`: an idempotent which is of rank one modulo `ker q`,
  `ē = p̄ λ̄ᵀ` with `λ̄ ⬝ p̄ = 1`, is of rank one, `e = p λᵀ` with `λ ⬝ p = 1` and `p ↦ p̄`.

This is the algebra behind the infinitesimal lifting property of the Picard functor of a curve
(the formal smoothness of `Pic`; the obstruction space `H²(C, 𝒪)` vanishes).
-/

open Matrix

universe u

namespace CurvesJacobian.MatLift

variable {R R' : Type*} [CommRing R] [CommRing R'] (q : R →+* R')

/-- The kernel of `q` has square zero. -/
def SqZero : Prop := ∀ a b : R, q a = 0 → q b = 0 → a * b = 0

variable {q}

lemma map_eq_zero_apply {k l : Type*} {M : Matrix k l R} (h : M.map q = 0) (i : k) (j : l) :
    q (M i j) = 0 :=
  congrFun (congrFun h i) j

lemma mul_eq_zero_of_map {k l m : ℕ} (hq : SqZero q) {M : Matrix (Fin k) (Fin l) R}
    {N : Matrix (Fin l) (Fin m) R} (hM : M.map q = 0) (hN : N.map q = 0) : M * N = 0 := by
  ext i j
  simp only [mul_apply, zero_apply]
  exact Finset.sum_eq_zero fun x _ ↦
    hq _ _ (map_eq_zero_apply hM i x) (map_eq_zero_apply hN x j)

lemma eq_zero_of_idempotent {k : ℕ} (hq : SqZero q) {Q : Matrix (Fin k) (Fin k) R}
    (hQ : Q * Q = Q) (h : Q.map q = 0) : Q = 0 := by
  rw [← hQ]
  exact mul_eq_zero_of_map hq h h

lemma map_surjective {k l : ℕ} (hs : Function.Surjective q) (M' : Matrix (Fin k) (Fin l) R') :
    ∃ M : Matrix (Fin k) (Fin l) R, M.map q = M' :=
  ⟨fun i j ↦ (hs (M' i j)).choose, by ext i j; exact (hs (M' i j)).choose_spec⟩

lemma vec_surjective {k : ℕ} (hs : Function.Surjective q) (v' : Fin k → R') :
    ∃ v : Fin k → R, q ∘ v = v' :=
  ⟨fun i ↦ (hs (v' i)).choose, funext fun i ↦ (hs (v' i)).choose_spec⟩

/-- **Idempotent matrices lift** along a surjection with square-zero kernel. -/
theorem exists_idempotent_lift {k : ℕ} (hs : Function.Surjective q) (hq : SqZero q)
    (e' : Matrix (Fin k) (Fin k) R') (he' : e' * e' = e') :
    ∃ e : Matrix (Fin k) (Fin k) R, e * e = e ∧ e.map q = e' := by
  obtain ⟨M, hM⟩ := map_surjective hs e'
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (q.mapMatrix)
    (fun x hx ↦ ⟨2, by
      have hx' : x.map q = 0 := hx
      rw [pow_two]
      exact mul_eq_zero_of_map hq hx' hx'⟩) e' ⟨M, hM⟩ he'
  exact ⟨e, he, hee⟩

lemma isUnit_of_map_eq_one (hq : SqZero q) {u : R} (hu : q u = 1) : IsUnit u := by
  have hk : q (u - 1) = 0 := by rw [map_sub, hu, map_one, sub_self]
  refine isUnit_iff_exists_inv.mpr ⟨1 - (u - 1), ?_⟩
  have := hq _ _ hk hk
  linear_combination -this

variable {RU RV RW RU' RV' RW' : Type*} [CommRing RU] [CommRing RV] [CommRing RW]
  [CommRing RU'] [CommRing RV'] [CommRing RW']

/-- **The gluing matrices lift.** Let `qW : R_W → R̄_W` be surjective with square-zero kernel,
`e_U`, `e_V` idempotents over `R_W` with images `ē_U`, `ē_V`, and `Φ̄`, `Ψ̄` gluing matrices for
`ē_U`, `ē_V`. Then there are gluing matrices `Φ`, `Ψ` for `e_U`, `e_V` with `Φ ↦ Φ̄`. -/
theorem exists_gluing_lift {n m : ℕ} {qW : RW →+* RW'} (hs : Function.Surjective qW)
    (hq : SqZero qW) (eU : Matrix (Fin n) (Fin n) RW) (eV : Matrix (Fin m) (Fin m) RW)
    (heU : eU * eU = eU) (heV : eV * eV = eV)
    (Φ' : Matrix (Fin n) (Fin m) RW') (Ψ' : Matrix (Fin m) (Fin n) RW')
    (hΦΨ : Φ' * Ψ' = eU.map qW) (hΨΦ : Ψ' * Φ' = eV.map qW)
    (heUΦ : eU.map qW * Φ' = Φ') (hΦeV : Φ' * eV.map qW = Φ') :
    ∃ (Φ : Matrix (Fin n) (Fin m) RW) (Ψ : Matrix (Fin m) (Fin n) RW),
      Φ * Ψ = eU ∧ Ψ * Φ = eV ∧ eU * Φ = Φ ∧ Φ * eV = Φ ∧ Φ.map qW = Φ' := by
  obtain ⟨Φ₁, hΦ₁⟩ := map_surjective hs Φ'
  obtain ⟨Ψ₁, hΨ₁⟩ := map_surjective hs Ψ'
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ, Φ = eU * Φ₁ * eV := ⟨_, rfl⟩
  obtain ⟨Ψ₂, hΨ₂def⟩ : ∃ Ψ₂, Ψ₂ = eV * Ψ₁ * eU := ⟨_, rfl⟩
  have hΦmap : Φ.map qW = Φ' := by
    rw [hΦdef, Matrix.map_mul, Matrix.map_mul, hΦ₁, heUΦ, hΦeV]
  have heUΦ' : eU * Φ = Φ := by rw [hΦdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, heU]
  have hΦeV' : Φ * eV = Φ := by rw [hΦdef, Matrix.mul_assoc, heV]
  have heVΨ₂ : eV * Ψ₂ = Ψ₂ := by rw [hΨ₂def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, heV]
  have hΨ₂eU : Ψ₂ * eU = Ψ₂ := by rw [hΨ₂def, Matrix.mul_assoc, heU]
  obtain ⟨N, hNdef⟩ : ∃ N, N = Φ * Ψ₂ - eU := ⟨_, rfl⟩
  have hNmap : N.map qW = 0 := by
    have : (Φ * Ψ₂).map qW = eU.map qW := by
      rw [Matrix.map_mul, hΦmap, hΨ₂def, Matrix.map_mul, Matrix.map_mul, hΨ₁, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hΦeV, hΦΨ, ← Matrix.map_mul, heU]
    rw [hNdef, Matrix.map_sub _ (map_sub _), this, sub_self]
  have heUN : eU * N = N := by
    rw [hNdef, Matrix.mul_sub, ← Matrix.mul_assoc, heUΦ', heU]
  have hNeU : N * eU = N := by
    rw [hNdef, Matrix.sub_mul, Matrix.mul_assoc, hΨ₂eU, heU]
  have hNN : N * N = 0 := mul_eq_zero_of_map hq hNmap hNmap
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = Ψ₂ * (eU - N) := ⟨_, rfl⟩
  have hΦΨ' : Φ * Ψ = eU := by
    have hΦΨ₂ : Φ * Ψ₂ = eU + N := by rw [hNdef]; abel
    rw [hΨdef, ← Matrix.mul_assoc, hΦΨ₂, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, heU,
      heUN, hNeU, hNN]
    abel
  have heVΨ : eV * Ψ = Ψ := by rw [hΨdef, ← Matrix.mul_assoc, heVΨ₂]
  obtain ⟨P, hPdef⟩ : ∃ P, P = Ψ * Φ := ⟨_, rfl⟩
  have hPP : P * P = P := by
    rw [hPdef, Matrix.mul_assoc, ← Matrix.mul_assoc Φ, hΦΨ', heUΦ']
  have hPmap : P.map qW = eV.map qW := by
    have h1 : Ψ.map qW * Φ' = eV.map qW * Ψ' * Φ' := by
      rw [hΨdef, Matrix.map_mul, Matrix.map_sub _ (map_sub _), hNmap, sub_zero, hΨ₂def,
        Matrix.map_mul,
        Matrix.map_mul, hΨ₁, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc (eU.map qW) (eU.map qW), ← Matrix.map_mul, heU, heUΦ,
        Matrix.mul_assoc]
    rw [hPdef, Matrix.map_mul, hΦmap, h1, Matrix.mul_assoc, hΨΦ, ← Matrix.map_mul, heV]
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = eV - P := ⟨_, rfl⟩
  have hPeV : P * eV = P := by rw [hPdef, Matrix.mul_assoc, hΦeV']
  have heVP : eV * P = P := by rw [hPdef, ← Matrix.mul_assoc, heVΨ]
  have hQQ : Q * Q = Q := by
    rw [hQdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, heV, heVP, hPeV, hPP]
    abel
  have hQ0 : Q = 0 := eq_zero_of_idempotent hq hQQ
    (by rw [hQdef, Matrix.map_sub _ (map_sub _), hPmap, sub_self])
  refine ⟨Φ, Ψ, hΦΨ', ?_, heUΦ', hΦeV', hΦmap⟩
  rw [← hPdef]
  rw [hQdef] at hQ0
  exact (sub_eq_zero.mp hQ0).symm

/-- **Rank-one idempotents lift**: if `e` is idempotent and `e ↦ p̄ λ̄ᵀ` with `λ̄ ⬝ p̄ = 1`, then
`e = p λᵀ` with `λ ⬝ p = 1` and `p ↦ p̄`. -/
theorem exists_rankOne_lift {n : ℕ} (hs : Function.Surjective q) (hq : SqZero q)
    (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) (p' l' : Fin n → R')
    (he' : e.map q = vecMulVec p' l') (hdot : l' ⬝ᵥ p' = 1) :
    ∃ p l : Fin n → R, e = vecMulVec p l ∧ l ⬝ᵥ p = 1 ∧ q ∘ p = p' := by
  obtain ⟨p₁, hp₁⟩ := vec_surjective hs p'
  obtain ⟨l₁, hl₁⟩ := vec_surjective hs l'
  obtain ⟨p₂, hp₂⟩ : ∃ p₂, p₂ = e *ᵥ p₁ := ⟨_, rfl⟩
  obtain ⟨l₂, hl₂⟩ : ∃ l₂, l₂ = l₁ ᵥ* e := ⟨_, rfl⟩
  have hmapv : ∀ (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R),
      q ∘ (M *ᵥ v) = M.map q *ᵥ (q ∘ v) :=
    fun M v ↦ funext fun i ↦ RingHom.map_mulVec q M v i
  have hmapv' : ∀ (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R),
      q ∘ (v ᵥ* M) = (q ∘ v) ᵥ* M.map q :=
    fun M v ↦ funext fun i ↦ RingHom.map_vecMul q M v i
  have hp₂' : q ∘ p₂ = p' := by
    rw [hp₂, hmapv, he', hp₁, vecMulVec_mulVec, hdot]
    simp
  have hl₂' : q ∘ l₂ = l' := by
    rw [hl₂, hmapv', he', hl₁, vecMul_vecMulVec, hdot, one_smul]
  obtain ⟨u, hu⟩ : ∃ u, u = l₂ ⬝ᵥ p₂ := ⟨_, rfl⟩
  have hqu : q u = 1 := by rw [hu, RingHom.map_dotProduct, hp₂', hl₂', hdot]
  obtain ⟨v, hv⟩ := (isUnit_of_map_eq_one hq hqu).exists_right_inv
  have hqv : q v = 1 := by
    have := congrArg q hv
    rw [map_mul, hqu, one_mul, map_one] at this
    exact this
  refine ⟨v • p₂, l₂, ?_, ?_, ?_⟩
  · have hep : e *ᵥ p₂ = p₂ := by rw [hp₂, mulVec_mulVec, he]
    have hle : l₂ ᵥ* e = l₂ := by rw [hl₂, vecMul_vecMul, he]
    obtain ⟨E, hE⟩ : ∃ E, E = vecMulVec (v • p₂) l₂ := ⟨_, rfl⟩
    have heE : e * E = E := by rw [hE, mul_vecMulVec, mulVec_smul, hep]
    have hEe : E * e = E := by rw [hE, vecMulVec_mul, hle]
    have hEE : E * E = E := by
      rw [hE, vecMulVec_mul_vecMulVec, dotProduct_smul, ← hu, smul_eq_mul, mul_comm, hv]
      ext i j
      simp [vecMulVec_apply]
    have hQ : (e - E) * (e - E) = e - E := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, he, heE, hEe, hEE]
      abel
    have hQmap : (e - E).map q = 0 := by
      rw [Matrix.map_sub _ (map_sub _), he', hE]
      ext i j
      simp only [map_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, sub_apply,
        zero_apply]
      have h1 := congrFun hp₂' i
      have h2 := congrFun hl₂' j
      simp only [Function.comp_apply] at h1 h2
      rw [hqv, h1, h2, one_mul, sub_self]
    rw [sub_eq_zero.mp (eq_zero_of_idempotent hq hQ hQmap), hE]
  · rw [dotProduct_smul, ← hu, smul_eq_mul, mul_comm, hv]
  · funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, hqv, one_mul]
    exact congrFun hp₂' i

end CurvesJacobian.MatLift
