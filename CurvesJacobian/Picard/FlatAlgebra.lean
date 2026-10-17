/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Commutative algebra for relative effective Cartier divisors

* `CurvesJacobian.Module.Flat.of_exact`: in a short exact sequence `0 → M → N → P → 0` with `M`
  and `P` flat, `N` is flat.
* `CurvesJacobian.flat_quotient_mul`: if `g` is a nonzerodivisor of the `A`-algebra `R` and
  `R/g`, `R/h` are `A`-flat, then `R/gh` is `A`-flat (the algebra behind Stacks, Tag 0B8U).
-/

open TensorProduct

namespace CurvesJacobian

universe u

section Extension

variable {A : Type u} [CommRing A] {M N P : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

/-- An extension of flat modules is flat. -/
theorem Module.Flat.of_exact [Module.Flat A M] [Module.Flat A P] (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.Flat A N := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro K K' _ _ _ _ φ hφ
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- the image of `x` in `K ⊗ P` vanishes
  have h1 : g.lTensor K x = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := P) φ hφ
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨y, rfl⟩ := ((lTensor_exact K hfg hg) x).mp h1
  have h2 : f.lTensor K' (φ.rTensor M y) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hx]
  have h3 : φ.rTensor M y = 0 :=
    (LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg K') (h2.trans (map_zero _).symm)
  have h4 : y = 0 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) φ hφ
    (h3.trans (map_zero _).symm)
  rw [h4, map_zero]

end Extension

section Quotients

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-- Multiplication by `g` induces `R/h → R/gh`. -/
noncomputable def mulQuot (g h : R) : (R ⧸ Ideal.span {h}) →ₗ[R] (R ⧸ Ideal.span {g * h}) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R g) (by
    rintro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mem_span_singleton'.mpr ⟨a, by change a * (g * h) = g * (a * h); ring⟩)

/-- The projection `R/gh → R/g`. -/
noncomputable def quotFactor (g h : R) : (R ⧸ Ideal.span {g * h}) →ₗ[R] (R ⧸ Ideal.span {g}) :=
  Submodule.mapQ _ _ LinearMap.id (by
    rintro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mem_span_singleton'.mpr ⟨a * h, by change a * h * g = a * (g * h); ring⟩)

lemma mulQuot_injective {g : R} (hg : IsSMulRegular R g) (h : R) :
    Function.Injective (mulQuot g h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : g * x ∈ Ideal.span {g * h} := (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
  refine (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton'.mpr ⟨a, hg ?_⟩)
  simp only [smul_eq_mul]
  rw [← ha]
  ring

lemma quotFactor_surjective (g h : R) : Function.Surjective (quotFactor g h) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk y, rfl⟩

lemma exact_mulQuot_quotFactor (g h : R) :
    Function.Exact (mulQuot g h) (quotFactor g h) := by
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [quotFactor, Submodule.mapQ_apply, LinearMap.id_apply,
    Submodule.Quotient.mk_eq_zero, Set.mem_range]
  constructor
  · intro hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨Submodule.Quotient.mk a, congrArg _ (mul_comm g a)⟩
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [mulQuot, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hw
    rw [Submodule.Quotient.eq] at hw
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hw
    refine Ideal.mem_span_singleton'.mpr ⟨w - a * h, ?_⟩
    have hz : z = g * w - a * (g * h) := by rw [ha]; ring
    rw [hz]
    ring

/-- If `g` is a nonzerodivisor and `R/g`, `R/h` are flat over `A`, so is `R/gh`. -/
theorem flat_quotient_mul {g : R} (hg : IsSMulRegular R g) (h : R)
    [Module.Flat A (R ⧸ Ideal.span {g})] [Module.Flat A (R ⧸ Ideal.span {h})] :
    Module.Flat A (R ⧸ Ideal.span {g * h}) :=
  Module.Flat.of_exact ((mulQuot g h).restrictScalars A) ((quotFactor g h).restrictScalars A)
    (mulQuot_injective hg h) (quotFactor_surjective g h) (exact_mulQuot_quotFactor g h)

end Quotients

end CurvesJacobian
