/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CechBaseChange
import CurvesJacobian.Picard.FlatAlgebra
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Two-term complexes of flat modules: replacing by finite projectives (Mumford's lemma)

Let `A` be a Noetherian ring and `d : C₀ → C₁` a map of flat `A`-modules whose kernel and
cokernel are finitely generated. Then there is a map `δ : K₀ → K₁` of finite projective
`A`-modules (with `K₁` finite free) such that for every `A`-algebra `B` the base changes
`B ⊗ δ` and `B ⊗ d` have isomorphic kernels and cokernels
(`CurvesJacobian.TwoTerm.exists_finite_projective`).

This is the two-term case of the construction in the proof of the base change statement of
Stacks, Lemma 36.30.4 (Tag 0B91), the algebraic heart of cohomology and base change for curves
(often called Mumford's lemma). The construction: choose a finite free `K₁` with
`γ : K₁ → C₁` such that
`C₁ = d(C₀) + γ(K₁)`, and let `K₀ = C₀ ×_{C₁} K₁`. Then
`0 → K₀ → C₀ × K₁ → C₁ → 0` is exact (`IsBicartesian`), which identifies kernels and cokernels
(`kerEquiv`, `cokerEquiv`); it stays exact after any base change because `C₁` is flat, `K₀` is
flat as the kernel of a surjection of flat modules (`flat_of_ker`), and finite because its
kernel and image in `K₁` are.

For two-set Čech data `f : P → R`, `g : Q → R` (`FormalSchemes.TwoCech`) this gives
`CurvesJacobian.TwoTerm.exists_finite_projective_twoCech`: `H⁰` and `H¹` of the base-changed
Čech data are the kernel and cokernel of `B ⊗ δ`.
-/

open TensorProduct LinearMap

universe u

namespace CurvesJacobian.TwoTerm

section Flat

variable {A : Type u} [CommRing A] {M N P : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

/-- The kernel of a surjection of flat modules is flat. -/
theorem flat_of_ker [Module.Flat A N] [Module.Flat A P] (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro K K' _ _ _ _ φ hφ
  have h1 : Function.Injective (f.lTensor K') :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg K'
  have h2 : Function.Injective (φ.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap φ hφ
  have h3 : (f.lTensor K') ∘ₗ (φ.rTensor M) = (φ.rTensor N) ∘ₗ (f.lTensor K) := by
    rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
  have h4 : Function.Injective ((φ.rTensor N) ∘ₗ (f.lTensor K)) :=
    h2.comp (LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg K)
  rw [← h3] at h4
  exact Function.Injective.of_comp (f := f.lTensor K') h4

/-- A product of flat modules is flat. -/
theorem flat_prod [Module.Flat A M] [Module.Flat A N] : Module.Flat A (M × N) :=
  CurvesJacobian.Module.Flat.of_exact (LinearMap.inl A M N) (LinearMap.snd A M N)
    LinearMap.inl_injective LinearMap.snd_surjective (by
      rintro ⟨x, y⟩
      simp only [LinearMap.snd_apply, Set.mem_range, LinearMap.inl_apply]
      constructor
      · rintro rfl; exact ⟨x, rfl⟩
      · rintro ⟨z, hz⟩; exact (congrArg Prod.snd hz).symm)

end Flat

section Bicartesian

variable {R : Type*} [CommRing R] {K₀ K₁ C₀ C₁ : Type*} [AddCommGroup K₀] [Module R K₀]
  [AddCommGroup K₁] [Module R K₁] [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁]
  [Module R C₁] (δ : K₀ →ₗ[R] K₁) (d : C₀ →ₗ[R] C₁) (α : K₀ →ₗ[R] C₀) (γ : K₁ →ₗ[R] C₁)

/-- A commutative square
```
K₀ --δ--> K₁
|α        |γ
C₀ --d--> C₁
```
is *bicartesian* if `0 → K₀ → C₀ × K₁ → C₁ → 0`, `k ↦ (α k, δ k)`, `(c, k) ↦ d c - γ k`, is
exact. -/
structure IsBicartesian : Prop where
  comm : ∀ k, d (α k) = γ (δ k)
  injective : Function.Injective (α.prod δ)
  exact : Function.Exact (α.prod δ) (d.coprod (-γ))
  surjective : Function.Surjective (d.coprod (-γ))

variable {δ d α γ}

lemma IsBicartesian.mem_ker (H : IsBicartesian δ d α γ) (k : K₀) (hk : k ∈ ker δ) :
    α k ∈ ker d := by
  rw [LinearMap.mem_ker] at hk ⊢
  rw [H.comm, hk, map_zero]

/-- A bicartesian square identifies the kernels of `δ` and `d`. -/
noncomputable def IsBicartesian.kerEquiv (H : IsBicartesian δ d α γ) : ker δ ≃ₗ[R] ker d :=
  LinearEquiv.ofBijective (α.restrict H.mem_ker) <| by
    constructor
    · rintro ⟨k, hk⟩ ⟨k', hk'⟩ h
      have h' : α k = α k' := congrArg Subtype.val h
      rw [LinearMap.mem_ker] at hk hk'
      refine Subtype.ext (H.injective ?_)
      simp [h', hk, hk']
    · rintro ⟨c, hc⟩
      rw [LinearMap.mem_ker] at hc
      obtain ⟨k, hk⟩ := (H.exact (c, 0)).mp (by simp [hc])
      have h1 : α k = c := congrArg Prod.fst hk
      have h2 : δ k = 0 := congrArg Prod.snd hk
      exact ⟨⟨k, h2⟩, Subtype.ext h1⟩

lemma IsBicartesian.kerEquiv_apply (H : IsBicartesian δ d α γ) (k : ker δ) :
    (H.kerEquiv k : C₀) = α k := rfl

lemma IsBicartesian.range_le (H : IsBicartesian δ d α γ) :
    range δ ≤ (range d).comap γ := by
  rintro _ ⟨k, rfl⟩
  exact ⟨α k, H.comm k⟩

/-- A bicartesian square identifies the cokernels of `δ` and `d`. -/
noncomputable def IsBicartesian.cokerEquiv (H : IsBicartesian δ d α γ) :
    (K₁ ⧸ range δ) ≃ₗ[R] (C₁ ⧸ range d) :=
  LinearEquiv.ofBijective ((range δ).mapQ (range d) γ H.range_le) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro z hz
      induction z using Submodule.Quotient.induction_on with | H k₁ => ?_
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨c, hc⟩ := hz
      obtain ⟨k, hk⟩ := (H.exact (c, k₁)).mp (by simp [hc])
      have h2 : δ k = k₁ := congrArg Prod.snd hk
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact ⟨k, h2⟩
    · intro z
      induction z using Submodule.Quotient.induction_on with | H c => ?_
      obtain ⟨⟨c₀, k₁⟩, h⟩ := H.surjective c
      refine ⟨Submodule.Quotient.mk (-k₁), ?_⟩
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
      refine ⟨-c₀, ?_⟩
      simp only [coprod_apply, LinearMap.neg_apply] at h
      rw [← h, map_neg, map_neg]
      abel

lemma IsBicartesian.cokerEquiv_mk (H : IsBicartesian δ d α γ) (k : K₁) :
    H.cokerEquiv (Submodule.Quotient.mk k) = Submodule.Quotient.mk (γ k) := rfl

section BaseChange

variable {A : Type*} [CommRing A] {K₀ K₁ C₀ C₁ : Type*} [AddCommGroup K₀] [Module A K₀]
  [AddCommGroup K₁] [Module A K₁] [AddCommGroup C₀] [Module A C₀] [AddCommGroup C₁]
  [Module A C₁] {δ : K₀ →ₗ[A] K₁} {d : C₀ →ₗ[A] C₁} {α : K₀ →ₗ[A] C₀} {γ : K₁ →ₗ[A] C₁}
  (B : Type*) [CommRing B] [Algebra A B]

lemma prod_baseChange (u : K₀ →ₗ[A] C₀) (v : K₀ →ₗ[A] K₁) (x : B ⊗[A] K₀) :
    (u.baseChange B).prod (v.baseChange B) x =
      TensorProduct.prodRight A B B C₀ K₁ ((u.prod v).baseChange B x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b k => simp

lemma coprod_baseChange (u : C₀ →ₗ[A] C₁) (v : K₁ →ₗ[A] C₁) (x : B ⊗[A] (C₀ × K₁)) :
    (u.baseChange B).coprod (v.baseChange B) (TensorProduct.prodRight A B B C₀ K₁ x) =
      (u.coprod v).baseChange B x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b k => simp [TensorProduct.tmul_add]

/-- Bicartesian squares whose corner `C₁` is flat stay bicartesian after base change. -/
theorem IsBicartesian.baseChange [Module.Flat A C₁] (H : IsBicartesian δ d α γ) :
    IsBicartesian (δ.baseChange B) (d.baseChange B) (α.baseChange B) (γ.baseChange B) where
  comm x := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp]
    congr 2
    exact LinearMap.ext H.comm
  injective := by
    have hinj : Function.Injective ((α.prod δ).baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_injective_of_exact_of_flat _ H.surjective _ H.injective H.exact B
    intro x y hxy
    rw [prod_baseChange, prod_baseChange] at hxy
    exact hinj ((TensorProduct.prodRight A B B C₀ K₁).injective hxy)
  exact := by
    have hex : Function.Exact ((α.prod δ).baseChange B) ((d.coprod (-γ)).baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact _root_.lTensor_exact B H.exact H.surjective
    intro z
    obtain ⟨x, rfl⟩ := (TensorProduct.prodRight A B B C₀ K₁).surjective z
    rw [← LinearMap.baseChange_neg, coprod_baseChange, hex]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, prod_baseChange B _ _ y⟩
    · rintro ⟨y, hy⟩
      rw [prod_baseChange] at hy
      exact ⟨y, (TensorProduct.prodRight A B B C₀ K₁).injective hy⟩
  surjective := by
    intro z
    obtain ⟨x, rfl⟩ := (show Function.Surjective ((d.coprod (-γ)).baseChange B) by
      rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective B H.surjective) z
    exact ⟨TensorProduct.prodRight A B B C₀ K₁ x, by
      rw [← LinearMap.baseChange_neg, coprod_baseChange]⟩

end BaseChange

end Bicartesian

section Construction

variable {A : Type u} [CommRing A] {C₀ C₁ : Type u} [AddCommGroup C₀] [Module A C₀]
  [AddCommGroup C₁] [Module A C₁] (d : C₀ →ₗ[A] C₁)

/-- If the cokernel of `d` is finitely generated, a finite free module maps to `C₁` such that
`C₁ = d(C₀) + γ(K₁)`. -/
lemma exists_finite_free_sup (h : Module.Finite A (C₁ ⧸ range d)) :
    ∃ (n : ℕ) (γ : (Fin n → A) →ₗ[A] C₁), Function.Surjective (d.coprod (-γ)) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A (C₁ ⧸ range d)
  have hlift : ∀ i : Fin n, ∃ c : C₁, (range d).mkQ c = π (Pi.single i 1) := fun i ↦
    (range d).mkQ_surjective _
  choose c hc using hlift
  let γ : (Fin n → A) →ₗ[A] C₁ := Fintype.linearCombination A c
  have hγ : (range d).mkQ ∘ₗ γ = π := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    simp [γ, Fintype.linearCombination_apply_single, hc]
  refine ⟨n, γ, fun z ↦ ?_⟩
  obtain ⟨v, hv⟩ := hπ ((range d).mkQ z)
  have : (range d).mkQ (z - γ v) = 0 := by
    rw [map_sub, ← hv, ← hγ, LinearMap.comp_apply, sub_self]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  obtain ⟨c₀, hc₀⟩ := this
  refine ⟨(c₀, -v), ?_⟩
  simp [hc₀]

/-- **Two-term version of Mumford's lemma** (base change as in
Stacks, Lemma 36.30.4, Tag 0B91): over a Noetherian ring `A`, a map `d : C₀ → C₁` of flat
modules with finitely generated kernel and cokernel is, universally, computed by a map
`δ : K₀ → K₁` of finite projective modules: for every `A`-algebra `B`, the base changes `B ⊗ δ`
and `B ⊗ d` have isomorphic kernels and cokernels. -/
theorem exists_finite_projective [IsNoetherianRing A] [Module.Flat A C₀] [Module.Flat A C₁]
    (hker : Module.Finite A (ker d)) (hcoker : Module.Finite A (C₁ ⧸ range d)) :
    ∃ (K₀ K₁ : ModuleCat.{u} A) (δ : K₀ →ₗ[A] K₁),
      Module.Finite A K₀ ∧ Module.Projective A K₀ ∧ Module.Finite A K₁ ∧ Module.Free A K₁ ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B],
        Nonempty (ker (δ.baseChange B) ≃ₗ[B] ker (d.baseChange B)) ∧
        Nonempty (((B ⊗[A] K₁) ⧸ range (δ.baseChange B)) ≃ₗ[B]
          ((B ⊗[A] C₁) ⧸ range (d.baseChange B))) := by
  obtain ⟨n, γ, hγ⟩ := exists_finite_free_sup d hcoker
  let Ψ : (C₀ × (Fin n → A)) →ₗ[A] C₁ := d.coprod (-γ)
  let K₀ : ModuleCat.{u} A := ModuleCat.of A (ker Ψ)
  let K₁ : ModuleCat.{u} A := ModuleCat.of A (Fin n → A)
  let α : K₀ →ₗ[A] C₀ := LinearMap.fst A C₀ (Fin n → A) ∘ₗ (ker Ψ).subtype
  let δ : K₀ →ₗ[A] K₁ := LinearMap.snd A C₀ (Fin n → A) ∘ₗ (ker Ψ).subtype
  have hprod : α.prod δ = (ker Ψ).subtype := by
    ext x <;> rfl
  have hexΨ : Function.Exact (ker Ψ).subtype Ψ := by
    intro x
    simp only [Set.mem_range, Submodule.coe_subtype]
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2
  have H : IsBicartesian δ d α γ := by
    refine ⟨fun k ↦ ?_, ?_, ?_, hγ⟩
    · have := LinearMap.mem_ker.mp k.2
      simp only [Ψ, coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg, sub_eq_zero] at this
      exact this
    · rw [hprod]; exact Subtype.val_injective
    · rw [hprod]; exact hexΨ
  -- `K₀` is flat
  haveI : Module.Flat A (C₀ × (Fin n → A)) := flat_prod
  have hflat : Module.Flat A K₀ :=
    flat_of_ker (ker Ψ).subtype Ψ Subtype.val_injective hγ hexΨ
  -- `K₀` is finite: its kernel `≅ ker d` and its image in `K₁` are finite
  have hfin : Module.Finite A K₀ := by
    haveI : Module.Finite A (ker δ) := Module.Finite.equiv H.kerEquiv.symm
    have hex : Function.Exact (ker δ).subtype δ.rangeRestrict := by
      intro x
      rw [← Subtype.coe_inj, LinearMap.codRestrict_apply, Submodule.coe_zero]
      simp only [Set.mem_range, Submodule.coe_subtype]
      constructor
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩; exact y.2
    exact Module.Finite.of_exact hex (LinearMap.surjective_rangeRestrict _)
  haveI : Module.FinitePresentation A K₀ := Module.finitePresentation_of_finite A K₀
  refine ⟨K₀, K₁, δ, hfin, Module.Flat.projective_of_finitePresentation, inferInstance,
    inferInstance, fun B _ _ ↦ ?_⟩
  have HB := H.baseChange B
  exact ⟨⟨HB.kerEquiv⟩, ⟨HB.cokerEquiv⟩⟩

section TwoCech

variable {A : Type u} [CommRing A] {P Q R : Type u} [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q] [AddCommGroup R] [Module A R] (f : P →ₗ[A] R) (g : Q →ₗ[A] R)

/-- `H⁰` of base-changed two-set Čech data is the kernel of the base-changed differential. -/
noncomputable def H0BaseChangeEquiv (B : Type u) [CommRing B] [Algebra A B] :
    ker ((TwoCech.d f g).baseChange B) ≃ₗ[B] TwoCech.H0 (f.baseChange B) (g.baseChange B) :=
  LinearEquiv.ofSubmodules (TensorProduct.prodRight A B B P Q) _ _ <| by
    ext x
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker, TwoCech.d_baseChange,
      LinearMap.comp_apply]
    rfl

/-- `H¹` of base-changed two-set Čech data is the cokernel of the base-changed differential. -/
noncomputable def H1BaseChangeEquiv' (B : Type u) [CommRing B] [Algebra A B] :
    ((B ⊗[A] R) ⧸ range ((TwoCech.d f g).baseChange B)) ≃ₗ[B]
      TwoCech.H1 (f.baseChange B) (g.baseChange B) :=
  Submodule.quotEquivOfEq _ _ (TwoCech.range_d_baseChange B f g).symm

/-- **Cohomology and base change for two-set Čech data** (Stacks, Lemma 36.30.4, Tag 0B91, for
a covering by two affines): over a Noetherian ring, if the Čech terms are flat and `H⁰`, `H¹`
are finitely generated, there is a map `δ : K₀ → K₁` of finite projective modules such that
`H⁰` and `H¹` of the base change of the Čech data along any `A → B` are the kernel and cokernel
of `B ⊗ δ`. -/
theorem exists_finite_projective_twoCech [IsNoetherianRing A] [Module.Flat A P]
    [Module.Flat A Q] [Module.Flat A R] (h0 : Module.Finite A (TwoCech.H0 f g))
    (h1 : Module.Finite A (TwoCech.H1 f g)) :
    ∃ (K₀ K₁ : ModuleCat.{u} A) (δ : K₀ →ₗ[A] K₁),
      Module.Finite A K₀ ∧ Module.Projective A K₀ ∧ Module.Finite A K₁ ∧ Module.Free A K₁ ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B],
        Nonempty (ker (δ.baseChange B) ≃ₗ[B] TwoCech.H0 (f.baseChange B) (g.baseChange B)) ∧
        Nonempty (((B ⊗[A] K₁) ⧸ range (δ.baseChange B)) ≃ₗ[B]
          TwoCech.H1 (f.baseChange B) (g.baseChange B)) := by
  haveI : Module.Flat A (P × Q) := flat_prod
  obtain ⟨K₀, K₁, δ, hK₀, hK₀', hK₁, hK₁', H⟩ := exists_finite_projective (TwoCech.d f g) h0 h1
  refine ⟨K₀, K₁, δ, hK₀, hK₀', hK₁, hK₁', fun B _ _ ↦ ?_⟩
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := H B
  exact ⟨⟨e₀ ≪≫ₗ H0BaseChangeEquiv f g B⟩, ⟨e₁ ≪≫ₗ H1BaseChangeEquiv' f g B⟩⟩

end TwoCech

end Construction

end CurvesJacobian.TwoTerm
