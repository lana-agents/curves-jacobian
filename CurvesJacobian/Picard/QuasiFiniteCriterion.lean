/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.BaseChange
import CurvesJacobian.Picard.PushoutAlgebra

/-!
# A quasi-finiteness criterion for hypersurfaces in relative curves

Let `B` be an `A`-algebra which is finite over `A[X]`, `S = B_h` a localization of `B` and
`g ∈ S` a nonzerodivisor such that `S/g` is `A`-flat. Then `S/g` is quasi-finite over `A`
(`CurvesJacobian.QuasiFiniteCriterion.quasiFinite_quotient`).

Proof: for a prime `𝔭` of `A` with residue field `K`, `g` stays a nonzerodivisor in
`K ⊗_A S` (flatness of `S/g`), so no prime containing it is minimal; `K ⊗_A S` is a localization
of `K ⊗_A B`, which is integral over `K[X]`, so by incomparability a non-minimal prime of
`K ⊗_A S` lies over a nonzero, hence maximal, prime of `K[X]` and is maximal. Thus the fibre
`K ⊗_A S/g` has dimension `0` and is finite over `K`.

This is the algebraic core of "(2) ⇒ (3)" of Stacks, Lemma 44.3.1 (Tag 0B9D) for curves
`C ×_k T`: a relative effective Cartier divisor is locally quasi-finite over the base.
-/

open Polynomial TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.QuasiFiniteCriterion

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra A[X] B]
  [IsScalarTower A A[X] B]

section Integral

variable (K : Type u) [CommRing K] [Algebra A K]

/-- `K[X]` acting on `K ⊗_A B` through the image of `X`. -/
abbrev fibreAlgebra : Algebra K[X] (K ⊗[A] B) :=
  (aeval (R := K) ((1 : K) ⊗ₜ[A] algebraMap A[X] B X)).toRingHom.toAlgebra

attribute [local instance] fibreAlgebra

lemma fibreAlgebra_comp :
    (algebraMap K[X] (K ⊗[A] B)).comp (mapRingHom (algebraMap A K)) =
      (Algebra.TensorProduct.includeRight.toRingHom : B →+* K ⊗[A] B).comp
        (algebraMap A[X] B) := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · change aeval _ (Polynomial.map _ (C a)) = (1 : K) ⊗ₜ[A] algebraMap A[X] B (C a)
    rw [Polynomial.map_C, aeval_C, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply A A[X] B, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one a,
      Algebra.algebraMap_eq_smul_one a, smul_tmul]
  · change aeval _ (Polynomial.map _ X) = (1 : K) ⊗ₜ[A] algebraMap A[X] B X
    rw [Polynomial.map_X, aeval_X]

/-- If `B` is integral over `A[X]`, then `K ⊗_A B` is integral over `K[X]`. -/
theorem isIntegral_fibre [Algebra.IsIntegral A[X] B] : Algebra.IsIntegral K[X] (K ⊗[A] B) := by
  constructor
  intro y
  induction y with
  | zero => exact isIntegral_zero
  | add x y hx hy => exact hx.add hy
  | tmul k b =>
    have hb : IsIntegral K[X] ((1 : K) ⊗ₜ[A] b) :=
      IsIntegral.map_of_comp_eq (mapRingHom (algebraMap A K))
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* K ⊗[A] B) (fibreAlgebra_comp K)
        (Algebra.IsIntegral.isIntegral b)
    have hk : k ⊗ₜ[A] b = algebraMap K[X] (K ⊗[A] B) (C k) * ((1 : K) ⊗ₜ[A] b) := by
      change _ = aeval _ (C k) * _
      rw [aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hk]
    exact isIntegral_algebraMap.mul hb

end Integral

section Localization

variable (K : Type u) [CommRing K] [Algebra A K] {h : B} (S : Type u) [CommRing S] [Algebra B S]
  [Algebra A S] [IsScalarTower A B S] [IsLocalization.Away h S]

/-- The map `K ⊗_A B → K ⊗_A S`. -/
abbrev locMap : K ⊗[A] B →ₐ[A] K ⊗[A] S :=
  Algebra.TensorProduct.map (AlgHom.id A K) (IsScalarTower.toAlgHom A B S)

omit [Algebra A[X] B] [IsScalarTower A A[X] B] in
include h in
/-- Every element of `K ⊗_A B_h` is the image of an element of `K ⊗_A B` up to a power of `h`. -/
lemma exists_pow_mul_eq (y : K ⊗[A] S) :
    ∃ (n : ℕ) (z : K ⊗[A] B),
      ((1 : K) ⊗ₜ[A] algebraMap B S h) ^ n * y = locMap (A := A) (B := B) K S z := by
  induction y with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul k s =>
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) s
    refine ⟨n, k ⊗ₜ b, ?_⟩
    simp only at hs
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_comm, ← map_pow, hs]
  | add x y hx hy =>
    obtain ⟨n₁, z₁, h₁⟩ := hx
    obtain ⟨n₂, z₂, h₂⟩ := hy
    refine ⟨n₁ + n₂, ((1 : K) ⊗ₜ[A] h) ^ n₂ * z₁ + ((1 : K) ⊗ₜ[A] h) ^ n₁ * z₂, ?_⟩
    simp only [map_add, map_mul, map_pow, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      IsScalarTower.coe_toAlgHom']
    rw [← h₁, ← h₂, pow_add]
    ring

omit [Algebra A B] [Algebra A[X] B] [IsScalarTower A A[X] B] [IsScalarTower A B S] in
include h in
lemma isUnit_one_tmul : IsUnit ((1 : K) ⊗ₜ[A] algebraMap B S h) := by
  have hu : IsUnit (algebraMap B S h) := IsLocalization.Away.algebraMap_isUnit h
  exact hu.map (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := S))

omit [Algebra A[X] B] [IsScalarTower A A[X] B] in
include h in
/-- Ideals of `K ⊗_A B_h` with the same preimage in `K ⊗_A B` are equal. -/
lemma eq_of_comap_eq {Q₁ Q₂ : Ideal (K ⊗[A] S)}
    (e : Q₁.comap (locMap (A := A) (B := B) K S) = Q₂.comap (locMap (A := A) (B := B) K S)) :
    Q₁ = Q₂ := by
  have key : ∀ {Q₁ Q₂ : Ideal (K ⊗[A] S)},
      Q₁.comap (locMap (A := A) (B := B) K S) = Q₂.comap (locMap (A := A) (B := B) K S) →
        Q₁ ≤ Q₂ := by
    intro Q₁ Q₂ e y hy
    obtain ⟨n, z, hz⟩ := exists_pow_mul_eq (A := A) (B := B) K S (h := h) y
    have hz₁ : z ∈ Q₁.comap (locMap (A := A) (B := B) K S) := by
      rw [Ideal.mem_comap, ← hz]
      exact Q₁.mul_mem_left _ hy
    rw [e, Ideal.mem_comap, ← hz] at hz₁
    exact (Ideal.unit_mul_mem_iff_mem Q₂ ((isUnit_one_tmul K S (h := h)).pow n)).mp hz₁
  exact le_antisymm (key e) (key e.symm)

end Localization

/-- **Quasi-finiteness criterion.** Let `B` be finite over `A[X]`, `S = B_h` and `g ∈ S` a
nonzerodivisor with `S/g` flat over `A`. Then `S/g` is quasi-finite over `A`. -/
theorem quasiFinite_quotient [Module.Finite A[X] B] {h : B} (S : Type u) [CommRing S]
    [Algebra B S] [Algebra A S] [IsScalarTower A B S] [IsLocalization.Away h S]
    [Algebra.FiniteType A S] {g : S} (hg : IsSMulRegular S g)
    [Module.Flat A (S ⧸ Ideal.span {g})] : Algebra.QuasiFinite A (S ⧸ Ideal.span {g}) := by
  constructor
  intro P _
  set K := P.ResidueField
  haveI : Algebra.FiniteType A (S ⧸ Ideal.span {g}) :=
    Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  rw [Module.finite_iff_krullDimLE_zero]
  refine Ring.KrullDimLE.mk₀ fun 𝔮 h𝔮 ↦ ?_
  -- the surjection `K ⊗ S → K ⊗ S/g`
  set ψ : K ⊗[A] S →ₐ[A] K ⊗[A] (S ⧸ Ideal.span {g}) :=
    Algebra.TensorProduct.map (AlgHom.id A K) (Ideal.Quotient.mkₐ A (Ideal.span {g}))
  have hψ : Function.Surjective ψ :=
    Algebra.TensorProduct.map_surjective _ _ (fun x ↦ ⟨x, rfl⟩)
      (Ideal.Quotient.mkₐ_surjective A _)
  set Q := 𝔮.comap ψ.toRingHom
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  -- `1 ⊗ g` is a nonzerodivisor of `K ⊗ S` lying in `Q`
  have hgQ : (1 : K) ⊗ₜ[A] g ∈ Q := by
    rw [Ideal.mem_comap]
    change ψ _ ∈ 𝔮
    rw [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g), tmul_zero]
    exact 𝔮.zero_mem
  have hreg : (1 : K) ⊗ₜ[A] g ∈ nonZeroDivisors (K ⊗[A] S) := by
    have h1 := isSMulRegular_tmul_one (A := A) (B := K) hg
    let e := Algebra.TensorProduct.comm A S K
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    rw [mul_comm] at hx
    have : e.symm x = 0 := by
      apply h1
      simp only [smul_eq_mul, mul_zero]
      have : g ⊗ₜ[A] (1 : K) = e.symm ((1 : K) ⊗ₜ[A] g) := rfl
      rw [this, ← map_mul, hx, map_zero]
    simpa using congrArg e this
  have hQmin : Q ∉ minimalPrimes (K ⊗[A] S) := fun hQ ↦
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hgQ hQ hreg
  obtain ⟨Q', hQ', hQ'Q⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := Q))
  have hQ'prime : Q'.IsPrime := hQ'.1.1
  have hlt : Q' < Q := lt_of_le_of_ne hQ'Q (fun e ↦ hQmin (e ▸ hQ'))
  -- pull back to `K ⊗ B`, integral over `K[X]`
  letI := fibreAlgebra (A := A) (B := B) K
  haveI := isIntegral_fibre (A := A) (B := B) K
  set φ := locMap (A := A) (B := B) K S
  have hlt₀ : Q'.comap φ < Q.comap φ := by
    refine lt_of_le_of_ne (Ideal.comap_mono hQ'Q) (fun e ↦ hlt.ne ?_)
    exact eq_of_comap_eq (A := A) (B := B) K S (h := h) e
  haveI : (Q'.comap φ).IsPrime := Ideal.comap_isPrime _ _
  haveI : (Q.comap φ).IsPrime := Ideal.comap_isPrime _ _
  have hlt₁ := Ideal.IsIntegral.comap_lt_comap (R := K[X]) hlt₀
  have hne : (Q.comap φ).comap (algebraMap K[X] (K ⊗[A] B)) ≠ ⊥ :=
    ne_bot_of_gt (lt_of_le_of_lt bot_le hlt₁)
  haveI : ((Q.comap φ).comap (algebraMap K[X] (K ⊗[A] B))).IsPrime := Ideal.comap_isPrime _ _
  have hmax₁ : ((Q.comap φ).comap (algebraMap K[X] (K ⊗[A] B))).IsMaximal :=
    IsPrime.to_maximal_ideal hne
  have hmax₀ : (Q.comap φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hmax₁
  -- hence `Q` is maximal
  have hQmax : Q.IsMaximal := by
    obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQp.ne_top
    have : Q.comap φ = M.comap φ :=
      hmax₀.eq_of_le (Ideal.comap_ne_top _ hM.ne_top) (Ideal.comap_mono hQM)
    rw [eq_of_comap_eq (A := A) (B := B) K S (h := h) this]
    exact hM
  -- and so is `𝔮 = ψ(Q)`
  have e𝔮 : 𝔮 = Q.map ψ.toRingHom := (Ideal.map_comap_of_surjective _ hψ 𝔮).symm
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective ψ.toRingHom hψ hQmax with htop | hmax
  · exact absurd (e𝔮.trans htop) h𝔮.ne_top
  · rwa [e𝔮]

section TensorPolynomial

/-- If `R` is finite over `k₀[X]` acting through `r`, then `A ⊗_{k₀} R` is finite over `A[X]`
acting through `1 ⊗ r`. -/
theorem finite_tensor_polynomial {k₀ R : Type u} [CommRing k₀] [CommRing R] [Algebra k₀ R]
    (A : Type u) [CommRing A] [Algebra k₀ A] (r : R)
    (hR : letI := (aeval (R := k₀) r).toRingHom.toAlgebra; Module.Finite k₀[X] R) :
    letI := (aeval (R := A) ((1 : A) ⊗ₜ[k₀] r)).toRingHom.toAlgebra
    Module.Finite A[X] (A ⊗[k₀] R) := by
  letI := (aeval (R := k₀) r).toRingHom.toAlgebra
  letI := (aeval (R := A) ((1 : A) ⊗ₜ[k₀] r)).toRingHom.toAlgebra
  classical
  obtain ⟨G, hG⟩ := hR.fg_top
  refine ⟨⟨G.image (fun g ↦ (1 : A) ⊗ₜ[k₀] g), ?_⟩⟩
  set P : Submodule A[X] (A ⊗[k₀] R) :=
    Submodule.span A[X] ↑(G.image (fun g ↦ (1 : A) ⊗ₜ[k₀] g))
  have key : ∀ ρ : R, ∀ a : A, a ⊗ₜ[k₀] ρ ∈ P := by
    intro ρ
    have hρ : ρ ∈ Submodule.span k₀[X] (G : Set R) := hG ▸ Submodule.mem_top
    induction hρ using Submodule.span_induction with
    | mem x hx =>
      intro a
      have e : a ⊗ₜ[k₀] x = (C a : A[X]) • ((1 : A) ⊗ₜ[k₀] x) := by
        rw [Algebra.smul_def]
        change _ = aeval _ (C a) * _
        rw [aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      refine P.smul_mem _ (Submodule.subset_span ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    | zero => intro a; rw [tmul_zero]; exact P.zero_mem
    | add x y _ _ hx hy => intro a; rw [tmul_add]; exact P.add_mem (hx a) (hy a)
    | smul p x _ hx =>
      intro a
      have e : a ⊗ₜ[k₀] (p • x) = (p.map (algebraMap k₀ A)) • (a ⊗ₜ[k₀] x) := by
        rw [Algebra.smul_def, Algebra.smul_def]
        change a ⊗ₜ[k₀] (aeval r p * x) = aeval ((1 : A) ⊗ₜ[k₀] r) (p.map _) * (a ⊗ₜ[k₀] x)
        rw [aeval_map_algebraMap,
          show (1 : A) ⊗ₜ[k₀] r = Algebra.TensorProduct.includeRight r from rfl,
          aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [e]
      exact P.smul_mem _ (hx a)
  rw [eq_top_iff]
  rintro y -
  induction y with
  | zero => exact P.zero_mem
  | tmul a ρ => exact key ρ a
  | add x y hx hy => exact P.add_mem hx hy

end TensorPolynomial

end CurvesJacobian.QuasiFiniteCriterion
