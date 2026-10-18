/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic

/-!
# The content ideal of an element of a module

For an element `s` of an `R`-module `M`, the *content ideal* `c(s) = {μ s | μ ∈ Hom_R(M, R)}` is
the image of the evaluation `Hom_R(M, R) → R` at `s`. For an invertible module `M` this is the
ideal of the zero scheme of `s`: locally `s = f • e` with `e` a generator, and `c(s) = (f)`.

* `CurvesJacobian.contentIdeal_smul`, `contentIdeal_map_equiv`,
  `contentIdeal_smul_of_bijective` (`c(t • e) = (t)` for a generator `e` of a free module of
  rank one).
* `CurvesJacobian.contentIdeal_isLocalizedModule`: for finitely presented `M` the content ideal
  commutes with localization.
* `CurvesJacobian.dual_apply_smul_comm`: for invertible `M`, `μ x • y = μ y • x`.
* For invertible `M`: `contentIdeal_smul_top` (`c(s) • M = R ∙ s`),
  `flat_quotient_contentIdeal` (flatness of `M/(s)` over `A` gives flatness of `R/c(s)`), and
  `dualEquivContentIdeal` (`Hom_R(M, R) ≃ c(s)`, `μ ↦ μ s`, for `s` a nonzerodivisor).
-/

open TensorProduct

noncomputable section

namespace CurvesJacobian

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M']

/-- The content ideal `{μ s | μ ∈ Hom_R(M, R)}` of an element `s` of an `R`-module. -/
def contentIdeal (s : M) : Ideal R :=
  LinearMap.range (Module.Dual.eval R M s)

lemma mem_contentIdeal {s : M} {r : R} : r ∈ contentIdeal s ↔ ∃ μ : Module.Dual R M, μ s = r :=
  Iff.rfl

lemma apply_mem_contentIdeal (μ : Module.Dual R M) (s : M) : μ s ∈ contentIdeal s :=
  ⟨μ, rfl⟩

lemma contentIdeal_smul (r : R) (s : M) :
    contentIdeal (r • s) = Ideal.span {r} * contentIdeal s := by
  apply le_antisymm
  · rintro _ ⟨μ, rfl⟩
    change μ (r • s) ∈ _
    rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self r) (apply_mem_contentIdeal μ s)
  · rw [Ideal.mul_le]
    rintro a ha _ ⟨μ, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨x • μ, ?_⟩
    change x * μ (r • s) = x * r * μ s
    rw [map_smul, smul_eq_mul, mul_assoc]

lemma contentIdeal_map_equiv (e : M ≃ₗ[R] M') (s : M) :
    contentIdeal (R := R) (e s) = contentIdeal s := by
  apply le_antisymm
  · rintro _ ⟨μ, rfl⟩
    exact ⟨μ ∘ₗ e.toLinearMap, rfl⟩
  · rintro _ ⟨μ, rfl⟩
    refine ⟨μ ∘ₗ e.symm.toLinearMap, ?_⟩
    change μ (e.symm (e s)) = μ s
    rw [e.symm_apply_apply]

/-- If `e` generates `M` freely, then `c(e) = R`. -/
lemma contentIdeal_eq_top_of_bijective {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton R M e)) : contentIdeal (R := R) e = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  refine ⟨(LinearEquiv.ofBijective _ he).symm.toLinearMap, ?_⟩
  change (LinearEquiv.ofBijective _ he).symm e = 1
  rw [LinearEquiv.symm_apply_eq]
  simp

/-- If `e` generates `M` freely, then `c(t • e) = (t)`. -/
lemma contentIdeal_smul_of_bijective {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton R M e)) (t : R) :
    contentIdeal (t • e) = Ideal.span {t} := by
  rw [contentIdeal_smul, contentIdeal_eq_top_of_bijective he, Ideal.mul_top]

/-- For a finitely presented module, the content ideal commutes with localization. -/
theorem contentIdeal_isLocalizedModule {R' : Type*} [CommRing R'] [Algebra R R']
    (S : Submonoid R) [IsLocalization S R'] [Module R' M'] [IsScalarTower R R' M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] [Module.FinitePresentation R M] (s : M) :
    contentIdeal (R := R') (f s) = (contentIdeal s).map (algebraMap R R') := by
  let ℓ := IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R R') R'
  apply le_antisymm
  · rintro _ ⟨ν, rfl⟩
    obtain ⟨⟨μ, t⟩, h⟩ := IsLocalizedModule.surj S ℓ ν
    have h' := LinearMap.congr_fun h (f s)
    simp only [ℓ, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
      LinearMap.smul_apply, Algebra.linearMap_apply] at h'
    change ν (f s) ∈ _
    have hu := IsLocalization.map_units R' t
    have : ν (f s) = ((hu.unit⁻¹ : R'ˣ) : R') * algebraMap R R' (μ s) := by
      rw [← h', Submonoid.smul_def, Algebra.smul_def, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (apply_mem_contentIdeal μ s))
  · rw [Ideal.map_le_iff_le_comap]
    rintro _ ⟨μ, rfl⟩
    refine ⟨ℓ μ, ?_⟩
    change ℓ μ (f s) = algebraMap R R' (μ s)
    simp [ℓ, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]

/-- In a module isomorphic to `R`, `μ x • y = μ y • x`. -/
lemma dual_apply_smul_comm_of_linearEquiv (e : M ≃ₗ[R] R) (μ : Module.Dual R M) (x y : M) :
    μ x • y = μ y • x := by
  have key : ∀ z : M, z = e z • e.symm 1 := fun z ↦ by
    rw [← map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
  apply e.injective
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, key x, key y, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, map_smul, map_smul, e.apply_symm_apply, smul_eq_mul, smul_eq_mul]
  ring

section Invertible

variable [Module.Invertible R M]

/-- In an invertible module, `μ x • y = μ y • x` (the module is locally free of rank one). -/
theorem dual_apply_smul_comm (μ : Module.Dual R M) (x y : M) : μ x • y = μ y • x := by
  refine Module.eq_of_localization_maximal
    (Mₚ := fun (P : Ideal R) _ ↦ LocalizedModule P.primeCompl M)
    (f := fun (P : Ideal R) _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) _ _ fun P _ ↦ ?_
  let Rp := Localization.AtPrime P
  let f := LocalizedModule.mkLinearMap P.primeCompl M
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free Rp (LocalizedModule P.primeCompl M))
  let μp := IsLocalizedModule.mapExtendScalars P.primeCompl f (Algebra.linearMap R Rp) Rp μ
  have hμ : ∀ z, μp (f z) = algebraMap R Rp (μ z) := fun z ↦ by
    simp [μp, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  change f (μ x • y) = f (μ y • x)
  rw [map_smul, map_smul, ← algebraMap_smul Rp (μ x), ← algebraMap_smul Rp (μ y), ← hμ, ← hμ]
  exact dual_apply_smul_comm_of_linearEquiv e μp _ _

variable (R M) in
/-- An invertible module has elements `zᵢ` and forms `νᵢ` with `∑ νᵢ zᵢ = 1`. -/
lemma exists_sum_dual_apply_eq_one :
    ∃ S : Finset (Module.Dual R M × M), ∑ i ∈ S, i.1 i.2 = 1 := by
  obtain ⟨S, hS⟩ := ((Module.Invertible.linearEquiv R M).symm 1).exists_finset
  refine ⟨S, ?_⟩
  have := congrArg (Module.Invertible.linearEquiv R M) hS
  rw [LinearEquiv.apply_symm_apply, map_sum] at this
  exact this.symm

/-- For an invertible module, `c(s) • M = R ∙ s`. -/
theorem contentIdeal_smul_top (s : M) :
    contentIdeal (R := R) s • (⊤ : Submodule R M) = R ∙ s := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    rintro _ ⟨μ, rfl⟩ n -
    change μ s • n ∈ _
    rw [dual_apply_smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨S, hS⟩ := exists_sum_dual_apply_eq_one R M
    have : s = ∑ i ∈ S, i.1 s • i.2 := by
      simp_rw [dual_apply_smul_comm _ s]
      rw [← Finset.sum_smul, hS, one_smul]
    have hmem : (∑ i ∈ S, i.1 s • i.2) ∈ contentIdeal (R := R) s • (⊤ : Submodule R M) :=
      Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem_smul (apply_mem_contentIdeal i.1 s) Submodule.mem_top
    rw [SetLike.mem_coe]
    rwa [← this] at hmem

/-- For an invertible module `M` over an `A`-algebra `R`, if `M/(s)` is flat over `A`, then so is
`R/c(s)`: indeed `R/c(s)` is a direct summand of a finite power of `M/(s)`. -/
theorem flat_quotient_contentIdeal {A : Type*} [CommRing A] [Algebra A R] [Module A M]
    [IsScalarTower A R M] (s : M) (h : Module.Flat A (M ⧸ R ∙ s)) :
    Module.Flat A (R ⧸ contentIdeal (R := R) s) := by
  obtain ⟨S, hS⟩ := exists_sum_dual_apply_eq_one R M
  let i : (R ⧸ contentIdeal (R := R) s) →ₗ[R] (S → M ⧸ R ∙ s) :=
    (contentIdeal (R := R) s).liftQ (LinearMap.pi fun j ↦
      (R ∙ s).mkQ ∘ₗ LinearMap.toSpanSingleton R M j.1.2) (by
        rintro _ ⟨μ, rfl⟩
        rw [LinearMap.mem_ker]
        funext j
        change (R ∙ s).mkQ (μ s • j.1.2) = 0
        rw [dual_apply_smul_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s))
  let r : (S → M ⧸ R ∙ s) →ₗ[R] (R ⧸ contentIdeal (R := R) s) :=
    ∑ j : S, (R ∙ s).liftQ ((contentIdeal (R := R) s).mkQ ∘ₗ j.1.1) (by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact apply_mem_contentIdeal _ s) ∘ₗ LinearMap.proj j
  have hri : r ∘ₗ i = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext
    simp only [r, i, LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply,
      Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply]
    change ∑ x : S, (contentIdeal (R := R) s).mkQ (x.1.1 x.1.2) = (contentIdeal (R := R) s).mkQ 1
    rw [← map_sum, ← hS, ← Finset.sum_coe_sort S]
  haveI := h
  haveI : Module.Flat A (S → M ⧸ R ∙ s) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A)
      (M := fun _ : S ↦ M ⧸ R ∙ s)).symm
  exact Module.Flat.of_retract (i.restrictScalars A) (r.restrictScalars A)
    (LinearMap.ext fun x ↦ LinearMap.congr_fun hri x)

/-- For an invertible module and a nonzerodivisor `s`, evaluation at `s` identifies the dual
module with the content ideal of `s`. -/
def dualEquivContentIdeal (s : M) (hs : Function.Injective fun r : R ↦ r • s) :
    Module.Dual R M ≃ₗ[R] contentIdeal (R := R) s :=
  LinearEquiv.ofBijective (Module.Dual.eval R M s).rangeRestrict
    ⟨fun μ ν hμν ↦ by
      have hμν' : μ s = ν s := congrArg Subtype.val hμν
      ext m
      apply hs
      change μ m • s = ν m • s
      rw [← dual_apply_smul_comm, hμν', dual_apply_smul_comm],
    LinearMap.surjective_rangeRestrict _⟩

@[simp]
lemma dualEquivContentIdeal_apply (s : M) (hs : Function.Injective fun r : R ↦ r • s)
    (μ : Module.Dual R M) : (dualEquivContentIdeal s hs μ : R) = μ s :=
  rfl

end Invertible

end CurvesJacobian
