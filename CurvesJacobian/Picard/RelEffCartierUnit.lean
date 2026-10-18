/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RelEffCartier
import CurvesJacobian.Picard.CartierCriterion

/-!
# A relative effective Cartier divisor is not divisible by a non-unit of the base

Let `f : X ⟶ T` be surjective with `T` affine, `D` a relative effective Cartier divisor on
`X/T` and `a ∈ Γ(T, 𝒪_T)`. If the ideal of `D` is contained in `a · 𝒪_X` on every affine open,
then `a` is a unit (`AlgebraicGeometry.RelEffCartier.isUnit_of_ideal_le`).

Algebraically (`CurvesJacobian.map_eq_top_of_mem_map`): if `g ∈ B` is a nonzerodivisor with
`B/g` flat over `A` and `g ∈ 𝔭B`, then `𝔭B = B`; indeed flatness gives `(g) ∩ 𝔭B = 𝔭 (g)`
(`CurvesJacobian.CartierCriterion.inf_map_le_mul_of_flat`), so `g = g y` with `y ∈ 𝔭B`. So the
divisor would be empty over the zero locus of `a`.

This is the fibre argument in the proof of Stacks, Lemma 44.6.4 (Tag 0B9X): two divisors in the
open subfunctor `F` with isomorphic line bundles coincide, since their canonical sections differ
by a unit of `Γ(T, 𝒪_T)`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace CurvesJacobian

/-- If `g ∈ B` is a nonzerodivisor with `B/(g)` flat over `A` and `g ∈ 𝔭B`, then `𝔭B = B`. -/
theorem map_eq_top_of_mem_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {g : B}
    (hg : IsSMulRegular B g) [Module.Flat A (B ⧸ Ideal.span {g})] (𝔭 : Ideal A)
    (h : g ∈ 𝔭.map (algebraMap A B)) : 𝔭.map (algebraMap A B) = ⊤ := by
  have hmem := CartierCriterion.inf_map_le_mul_of_flat (Ideal.span {g}) 𝔭
    ⟨Ideal.mem_span_singleton_self g, h⟩
  rw [mul_comm, Ideal.mem_span_singleton_mul] at hmem
  obtain ⟨y, hy, hgy⟩ := hmem
  have h1 : y = 1 := hg (by
    change g * y = g * 1
    rw [hgy, mul_one])
  rw [h1] at hy
  exact (Ideal.eq_top_iff_one _).mpr hy

end CurvesJacobian

namespace AlgebraicGeometry

/-- On an affine scheme, a function vanishing nowhere is a unit. -/
lemma isUnit_of_basicOpen_eq_top {T : Scheme.{u}} [IsAffine T] (a : Γ(T, ⊤))
    (h : ∀ t : T, t ∈ T.basicOpen a) : IsUnit a := by
  have hsurj : Function.Surjective T.toSpecΓ :=
    (Scheme.homeoOfIso (asIso T.toSpecΓ)).surjective
  have key : (⨆ _ : Unit, PrimeSpectrum.basicOpen a) = ⊤ := by
    refine eq_top_iff.mpr fun p _ ↦ ?_
    rw [iSup_const]
    obtain ⟨t, rfl⟩ := hsurj p
    have := h t
    rw [← Scheme.toSpecΓ_preimage_basicOpen] at this
    exact this
  rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Set.range_const,
    Ideal.span_singleton_eq_top] at key
  exact key

namespace RelEffCartier

variable {X T : Scheme.{u}} {f : X ⟶ T} (D : RelEffCartier f)

/-- **A relative effective Cartier divisor is not divisible by a non-unit of the base.** If
`f : X ⟶ T` is surjective, `T` affine, and the ideal of `D` is contained in `a · 𝒪_X` on every
affine open, then `a ∈ Γ(T, 𝒪_T)` is a unit. -/
theorem isUnit_of_ideal_le [IsAffine T] [Surjective f] (a : Γ(T, ⊤))
    (h : ∀ W : X.affineOpens, D.ideal.ideal W ≤ Ideal.span {f.appLE ⊤ W.1 (by simp) a}) :
    IsUnit a := by
  refine isUnit_of_basicOpen_eq_top a fun t ↦ ?_
  obtain ⟨x, rfl⟩ := f.surjective t
  obtain ⟨W, g, hxW, hW, hg⟩ := D.locally_principal x
  have e : W.1 ≤ f ⁻¹ᵁ (⊤ : T.Opens) := by simp
  haveI := D.flat
  have hflat := D.ideal.flat_quotient_of_flat f ⟨⊤, isAffineOpen_top T⟩ W e
  letI : Algebra Γ(T, ⊤) Γ(X, W.1) := (f.appLE ⊤ W.1 e).hom.toAlgebra
  rw [hW] at hflat
  haveI : Module.Flat Γ(T, ⊤) (Γ(X, W.1) ⧸ Ideal.span {g}) := by
    rw [RingHom.Flat] at hflat
    exact hflat
  have hgmem : g ∈ (Ideal.span {a}).map (algebraMap Γ(T, ⊤) Γ(X, W.1)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact h W (hW ▸ Ideal.mem_span_singleton_self g)
  have htop := CurvesJacobian.map_eq_top_of_mem_map hg _ hgmem
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at htop
  have hx : x ∈ X.basicOpen (f.appLE ⊤ W.1 e a) := by
    have htop' : IsUnit (f.appLE ⊤ W.1 e a) := htop
    rw [Scheme.basicOpen_of_isUnit X htop']
    exact hxW
  rw [Scheme.basicOpen_appLE] at hx
  exact hx.2

end RelEffCartier

end AlgebraicGeometry
