/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.FiniteStability
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Maximal ideals in a fibre, before and after an extension of algebraically closed fields

* `CurvesJacobian.maximalSpectrumEquivAlgHom`: for `K` algebraically closed and `A` a finitely
  generated `K`-algebra, maximal ideals of `A` are the `K`-points `A →ₐ[K] K` (Hilbert's
  Nullstellensatz, via Zariski's lemma `finite_of_finite_type_of_isJacobsonRing`);
  `maximalSpectrumMemEquivAlgHom`: those containing `z - c` are the points with `φ z = c`.
* `CurvesJacobian.card_maximalSpectrum_baseChange`: let `k ⊆ Ω` be algebraically closed fields
  and `B` a finitely generated `k`-algebra with `t ∈ B` such that `k[t] → B` is finite. Then for
  `a ∈ k` the maximal ideals of `Ω ⊗[k] B` containing `1 ⊗ t - a` are as many as the maximal
  ideals of `B` containing `t - a`:
  `Hom_Ω(Ω ⊗ B, Ω) = Hom_k(B, Ω)`, and a `k`-point `B → Ω` with `t ↦ a` takes values in `k`
  (`B` is integral over `k[t]`).
-/

open scoped TensorProduct

namespace CurvesJacobian

section Nullstellensatz

variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- **Residue fields at maximal ideals are `K`** (Zariski's lemma). -/
lemma algebraMap_quotient_bijective (M : Ideal A) [M.IsMaximal] :
    Function.Bijective (algebraMap K (A ⧸ M)) := by
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The `K`-point of `A` with kernel a maximal ideal `M`. -/
noncomputable def pointOfMaximal (M : MaximalSpectrum A) : A →ₐ[K] K :=
  haveI := M.isMaximal
  ((AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ M.asIdeal))
    (algebraMap_quotient_bijective M.asIdeal)).symm : (A ⧸ M.asIdeal) →ₐ[K] K).comp
      (Ideal.Quotient.mkₐ K M.asIdeal)

lemma ker_pointOfMaximal (M : MaximalSpectrum A) :
    RingHom.ker (pointOfMaximal (K := K) M) = M.asIdeal := by
  ext a
  rw [RingHom.mem_ker]
  simp only [pointOfMaximal, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    AlgEquiv.coe_toAlgHom]
  rw [map_eq_zero_iff _ (AlgEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

variable (K A) in
/-- **Hilbert's Nullstellensatz**: maximal ideals of a finitely generated algebra over an
algebraically closed field `K` are its `K`-points. -/
noncomputable def maximalSpectrumEquivAlgHom : MaximalSpectrum A ≃ (A →ₐ[K] K) where
  toFun := pointOfMaximal
  invFun φ := ⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ
    (fun c ↦ ⟨algebraMap K A c, φ.commutes c⟩)⟩
  left_inv M := MaximalSpectrum.ext (ker_pointOfMaximal M)
  right_inv φ := by
    ext a
    have h : a - algebraMap K A (φ a) ∈
        RingHom.ker (pointOfMaximal (K := K) ⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ
          (fun c ↦ ⟨algebraMap K A c, φ.commutes c⟩)⟩) := by
      rw [ker_pointOfMaximal, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at h
    simpa using h

lemma mem_maximalSpectrumEquivAlgHom_symm_iff (φ : A →ₐ[K] K) (z : A) (c : K) :
    z - algebraMap K A c ∈ ((maximalSpectrumEquivAlgHom K A).symm φ).asIdeal ↔ φ z = c := by
  change _ ∈ RingHom.ker φ ↔ _
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero, Algebra.algebraMap_self,
    RingHom.id_apply]

variable (K) in
/-- The maximal ideals containing `z - c` are the `K`-points with `z ↦ c`. -/
noncomputable def maximalSpectrumMemEquivAlgHom (z : A) (c : K) :
    {M : MaximalSpectrum A // z - algebraMap K A c ∈ M.asIdeal} ≃
      {φ : A →ₐ[K] K // φ z = c} :=
  (Equiv.subtypeEquiv (maximalSpectrumEquivAlgHom K A).symm
    (fun φ ↦ (mem_maximalSpectrumEquivAlgHom_symm_iff φ z c).symm)).symm

end Nullstellensatz

section BaseChange

variable {k Ω B : Type*} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [Algebra k B]

/-- **Points over a finite coordinate are defined over `k`**: if `k[t] → B` is finite and
`ψ : B → Ω` is a `k`-point with `ψ t ∈ k`, then `ψ` takes values in `k`. -/
lemma mem_range_algebraMap_of_finite [IsAlgClosed k] (t : B)
    (hfin : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).Finite) {a : k} (ψ : B →ₐ[k] Ω)
    (hψ : ψ t = algebraMap k Ω a) (b : B) : ψ b ∈ Set.range (algebraMap k Ω) := by
  obtain ⟨p, hpm, hp⟩ := RingHom.Finite.to_isIntegral hfin b
  let ev : MvPolynomial (Fin 1) k →+* k := MvPolynomial.eval fun _ ↦ a
  have hcomp : (ψ : B →+* Ω).comp (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).toRingHom =
      (algebraMap k Ω).comp ev := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun i ↦ ?_
    · simp [ev]
    · simp [ev, hψ]
  have hint : IsIntegral k (ψ b) := by
    refine ⟨p.map ev, hpm.map ev, ?_⟩
    have h := Polynomial.hom_eval₂ p (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).toRingHom
      (ψ : B →+* Ω) b
    rw [hp, map_zero] at h
    rw [Polynomial.eval₂_map, ← hcomp]
    exact h.symm
  haveI : Algebra.IsIntegral k (Algebra.adjoin k {ψ b}) :=
    Algebra.IsIntegral.adjoin (fun x hx ↦ by rw [Set.mem_singleton_iff.mp hx]; exact hint)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := k) (K := Algebra.adjoin k {ψ b})).2 ⟨ψ b, Algebra.self_mem_adjoin_singleton k _⟩
  exact ⟨c, congrArg Subtype.val hc⟩

/-- **`k`-points of `B` with `t ↦ a` are the `Ω`-points with `t ↦ a`**, for `k[t] → B` finite
and `k` algebraically closed. -/
noncomputable def algHomEquivOfFinite [IsAlgClosed k] (t : B)
    (hfin : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).Finite) (a : k) :
    {χ : B →ₐ[k] k // χ t = a} ≃ {ψ : B →ₐ[k] Ω // ψ t = algebraMap k Ω a} :=
  Equiv.ofBijective (fun χ ↦ ⟨(Algebra.ofId k Ω).comp χ.1, by simp [χ.2]⟩)
    ⟨fun χ₁ χ₂ h ↦ Subtype.ext (AlgHom.ext fun b ↦ (algebraMap k Ω).injective
        (DFunLike.congr_fun (congrArg Subtype.val h) b)),
      fun ψ ↦ by
        choose c hc using mem_range_algebraMap_of_finite t hfin ψ.1 ψ.2
        have hinj := (algebraMap k Ω).injective
        let χ : B →ₐ[k] k :=
          { toFun := c
            map_one' := hinj (by rw [hc, map_one, map_one])
            map_mul' := fun x y ↦ hinj (by rw [hc, map_mul, map_mul, hc, hc])
            map_zero' := hinj (by rw [hc, map_zero, map_zero])
            map_add' := fun x y ↦ hinj (by rw [hc, map_add, map_add, hc, hc])
            commutes' := fun r ↦ hinj (by rw [hc, AlgHom.commutes]; rfl) }
        refine ⟨⟨χ, hinj ?_⟩, Subtype.ext (AlgHom.ext fun b ↦ hc b)⟩
        change algebraMap k Ω (c t) = _
        rw [hc, ψ.2]⟩

/-- **Counting maximal ideals in a fibre is invariant under `k ⊆ Ω`.** For `k ⊆ Ω` algebraically
closed fields, `B` a finitely generated `k`-algebra and `t ∈ B` with `k[t] → B` finite, and
`a ∈ k`: the maximal ideals of `Ω ⊗[k] B` containing `1 ⊗ t - a` are as many as the maximal
ideals of `B` containing `t - a`. -/
theorem card_maximalSpectrum_baseChange [IsAlgClosed k] [IsAlgClosed Ω] [Algebra.FiniteType k B]
    (t : B) (hfin : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).Finite) (a : k) :
    Nat.card {M : MaximalSpectrum (Ω ⊗[k] B) //
        (1 ⊗ₜ t : Ω ⊗[k] B) - algebraMap Ω (Ω ⊗[k] B) (algebraMap k Ω a) ∈ M.asIdeal} =
      Nat.card {M : MaximalSpectrum B // t - algebraMap k B a ∈ M.asIdeal} := by
  refine Nat.card_congr ((maximalSpectrumMemEquivAlgHom Ω _ _).trans
    (Equiv.trans ?_ ((algHomEquivOfFinite (Ω := Ω) t hfin a).symm.trans
      (maximalSpectrumMemEquivAlgHom k t a).symm)))
  exact Equiv.subtypeEquiv (AlgHom.liftEquiv k Ω B Ω).symm (fun φ ↦ Iff.rfl)

end BaseChange

end CurvesJacobian
