/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Basic

/-!
# Determinants of endomorphisms of free modules: extensions and perfect pairings

Linear algebra over a commutative ring `R` used for the determinant computations of step B of
`MR3-plan.md` (with `R = ℤ/l^k`). Let `M` be a finite free `R`-module and `A ⊆ M` a submodule.

Main results:
* `CurvesJacobian.CuspChar.det_eq_det_restrict_mul_det_mapQ`: if `A` and `M ⧸ A` are finite free
  and `f` preserves `A`, then `det f = det (f|_A) * det (f mod A)` (a wrapper around Mathlib's
  `LinearMap.det_eq_det_mul_det`).
* `CurvesJacobian.CuspChar.finrank_eq_finrank_add_finrank_quotient`: in the same situation,
  `rank M = rank A + rank (M ⧸ A)`.
* `CurvesJacobian.CuspChar.free_of_free_quotient`,
  `CurvesJacobian.CuspChar.finite_of_free_quotient`: over a local ring, if `M ⧸ A` is finite
  free then so is `A` (it is a direct summand).
* `CurvesJacobian.CuspChar.det_mapQ_eq_pow_of_sub_mem`: if `f` induces `c • id` on `M ⧸ A`, then
  `det (f mod A) = c ^ rank (M ⧸ A)`.
* `CurvesJacobian.CuspChar.det_sq_of_pairing`: if `e : M × M → R` is a perfect bilinear pairing
  with `e (f a) (f b) = c * e a b`, then `det f ^ 2 = c ^ rank M`.
-/

namespace CurvesJacobian.CuspChar

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

section Submodule

variable (A : Submodule R M)

/-- Block-triangular determinant: if `f` preserves `A` and `A`, `M ⧸ A` are finite free, then
`det f` is the product of the determinants of `f|_A` and of the induced map on `M ⧸ A`. -/
theorem det_eq_det_restrict_mul_det_mapQ [Module.Finite R M] [Module.Free R A]
    [Module.Finite R A] [Module.Free R (M ⧸ A)] (f : M →ₗ[R] M) (hA : ∀ a ∈ A, f a ∈ A) :
    LinearMap.det f =
      LinearMap.det (f.restrict hA) * LinearMap.det (A.mapQ A f (fun a ha ↦ hA a ha)) :=
  LinearMap.det_eq_det_mul_det A f (fun a ha ↦ hA a ha)

/-- Rank additivity for a free submodule with free quotient over a nontrivial commutative
ring. -/
theorem finrank_eq_finrank_add_finrank_quotient [Nontrivial R] [Module.Free R A]
    [Module.Finite R A] [Module.Free R (M ⧸ A)] [Module.Finite R (M ⧸ A)] :
    finrank R M = finrank R A + finrank R (M ⧸ A) := by
  let bA := Free.chooseBasis R A
  let bQ := Free.chooseBasis R (M ⧸ A)
  rw [finrank_eq_card_basis (bA.sumQuot bQ), Fintype.card_sum, finrank_eq_card_basis bA,
    finrank_eq_card_basis bQ]

/-- If `M ⧸ A` is projective, then `A` is a direct summand of `M`: there is a retraction
`M → A` of the inclusion. -/
theorem exists_retraction_of_projective_quotient [Projective R (M ⧸ A)] :
    ∃ r : M →ₗ[R] A, r ∘ₗ A.subtype = LinearMap.id := by
  obtain ⟨s, hs⟩ := A.mkQ.exists_rightInverse_of_surjective (A.range_mkQ)
  have hmem : ∀ x : M, x - s (A.mkQ x) ∈ A := fun x ↦ by
    rw [← Submodule.Quotient.eq, ← A.mkQ_apply, ← A.mkQ_apply, ← LinearMap.comp_apply A.mkQ s,
      hs, LinearMap.id_apply]
  refine ⟨(LinearMap.id - s ∘ₗ A.mkQ).codRestrict A hmem, ?_⟩
  ext a
  simp [(Submodule.Quotient.mk_eq_zero A).2 a.2]

/-- If `M` is finite and `M ⧸ A` is projective (e.g. free), then `A` is finite. -/
theorem finite_of_free_quotient [Module.Finite R M] [Projective R (M ⧸ A)] :
    Module.Finite R A := by
  obtain ⟨r, hr⟩ := exists_retraction_of_projective_quotient A
  refine Module.Finite.of_surjective r fun a ↦ ⟨a, ?_⟩
  simpa using LinearMap.congr_fun hr a

/-- Over a local ring, if `M` is finite free and `M ⧸ A` is projective (e.g. free), then `A` is
free (a finite projective module over a local ring is free). -/
theorem free_of_free_quotient [IsLocalRing R] [Module.Finite R M] [Module.Free R M]
    [Projective R (M ⧸ A)] : Module.Free R A := by
  obtain ⟨r, hr⟩ := exists_retraction_of_projective_quotient A
  have : Projective R A := Projective.of_split A.subtype r hr
  have : Module.Finite R A := finite_of_free_quotient A
  exact free_of_flat_of_isLocalRing

/-- If `f` induces multiplication by `c` on `M ⧸ A`, then the determinant of the induced map is
`c ^ rank (M ⧸ A)`. -/
theorem det_mapQ_eq_pow_of_sub_mem [Module.Free R (M ⧸ A)] [Module.Finite R (M ⧸ A)]
    (f : M →ₗ[R] M) (h : A ≤ A.comap f) (c : R) (hc : ∀ x, f x - c • x ∈ A) :
    LinearMap.det (A.mapQ A f h) = c ^ finrank R (M ⧸ A) := by
  have : A.mapQ A f h = c • LinearMap.id := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hc x
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

end Submodule

section Pairing

variable [Module.Free R M] [Module.Finite R M]

/-- Determinant from a perfect pairing: if `e : M → Dual R M` is bijective and
`e (f a) (f b) = c * e a b` for all `a b`, then `det f ^ 2 = c ^ rank M`. -/
theorem det_sq_of_pairing (e : M →ₗ[R] M →ₗ[R] R) (he : Function.Bijective e)
    (f : M →ₗ[R] M) (c : R) (hf : ∀ a b, e (f a) (f b) = c * e a b) :
    LinearMap.det f ^ 2 = c ^ finrank R M := by
  let ε : M ≃ₗ[R] Dual R M := LinearEquiv.ofBijective e he
  have key : (ε.symm : Dual R M →ₗ[R] M) ∘ₗ f.dualMap ∘ₗ (ε : M →ₗ[R] Dual R M) ∘ₗ f =
      c • LinearMap.id := by
    have h1 : f.dualMap ∘ₗ (ε : M →ₗ[R] Dual R M) ∘ₗ f = c • (ε : M →ₗ[R] Dual R M) := by
      ext a b
      simp [ε, hf]
    rw [h1, LinearMap.comp_smul, ← LinearEquiv.coe_trans, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap]
  have h3 : LinearMap.det ((ε.symm : Dual R M →ₗ[R] M) ∘ₗ f.dualMap ∘ₗ
      (ε : M →ₗ[R] Dual R M)) = LinearMap.det f := by
    simpa [LinearMap.det_dualMap] using LinearMap.det_conj f.dualMap ε.symm
  have h2 := congrArg LinearMap.det key
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, ← LinearMap.comp_assoc,
    ← LinearMap.comp_assoc, LinearMap.det_comp, LinearMap.comp_assoc, h3] at h2
  rw [sq, h2]

/-- Unit version of `CurvesJacobian.CuspChar.det_sq_of_pairing` for a linear automorphism. -/
theorem linearEquiv_det_sq_of_pairing (e : M →ₗ[R] M →ₗ[R] R) (he : Function.Bijective e)
    (f : M ≃ₗ[R] M) (c : R) (hf : ∀ a b, e (f a) (f b) = c * e a b) :
    ((LinearEquiv.det f : Rˣ) : R) ^ 2 = c ^ finrank R M := by
  rw [LinearEquiv.coe_det]
  exact det_sq_of_pairing e he f c hf

end Pairing

end CurvesJacobian.CuspChar
