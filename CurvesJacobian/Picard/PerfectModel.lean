/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TwoTermPerfect

/-!
# Perfect models of two-set Čech data

For two-set Čech data `f : P → R`, `g : Q → R` over a ring `A` (`FormalSchemes.TwoCech`),
`CurvesJacobian.TwoTerm.HasPerfectModel f g` says that there is a map `δ : K₀ → K₁` of finite
projective `A`-modules (`K₁` free) such that for every `A`-algebra `B` the `H⁰`, `H¹` of the
base-changed Čech data are the kernel and cokernel of `B ⊗ δ`: the Čech complex is, universally,
computed by a two-term perfect complex (the conclusion of Stacks, Lemma 36.30.4, Tag 0B91, for a
covering by two affines).

* `HasPerfectModel.of_equiv`: the property only depends on the Čech data up to isomorphism;
* `HasPerfectModel.baseChange`: it is stable under base change along any `A₀ → A` (this is how
  Noetherian approximation is used: a model over a Noetherian `A₀` gives one over `A`);
* `hasPerfectModel_of_noetherian`: over a Noetherian ring, flat Čech terms with finite `H⁰`, `H¹`
  have a perfect model (`TwoTerm.exists_finite_projective_twoCech`, Mumford's lemma).
-/

open TensorProduct LinearMap

universe u

namespace CurvesJacobian.TwoTerm

section Comm

variable {B : Type*} [CommRing B] {M₀ M₁ N₀ N₁ : Type*} [AddCommGroup M₀] [Module B M₀]
  [AddCommGroup M₁] [Module B M₁] [AddCommGroup N₀] [Module B N₀] [AddCommGroup N₁]
  [Module B N₁] (e₀ : M₀ ≃ₗ[B] N₀) (e₁ : M₁ ≃ₗ[B] N₁) {u : M₀ →ₗ[B] M₁} {v : N₀ →ₗ[B] N₁}
  (h : (e₁ : M₁ →ₗ[B] N₁) ∘ₗ u = v ∘ₗ (e₀ : M₀ →ₗ[B] N₀))

include h in
lemma map_ker_eq : (ker u).map (e₀ : M₀ →ₗ[B] N₀) = ker v := by
  ext y
  rw [Submodule.mem_map_equiv, mem_ker, mem_ker]
  have := LinearMap.congr_fun h (e₀.symm y)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply] at this
  rw [← this, LinearEquiv.map_eq_zero_iff]

include h in
lemma map_range_eq : (range u).map (e₁ : M₁ →ₗ[B] N₁) = range v := by
  rw [← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top _ e₀.range]

/-- Kernels of maps identified by isomorphisms of source and target. -/
def kerEquivOfComm : ker u ≃ₗ[B] ker v :=
  e₀.ofSubmodules _ _ (map_ker_eq e₀ e₁ h)

/-- Cokernels of maps identified by isomorphisms of source and target. -/
def cokerEquivOfComm : (M₁ ⧸ range u) ≃ₗ[B] (N₁ ⧸ range v) :=
  Submodule.Quotient.equiv _ _ e₁ (map_range_eq e₀ e₁ h)

end Comm

variable {A : Type u} [CommRing A] {P Q R : Type u} [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q] [AddCommGroup R] [Module A R] (f : P →ₗ[A] R) (g : Q →ₗ[A] R)

/-- **A perfect model** of two-set Čech data: a map `δ : K₀ → K₁` of finite projective modules
(`K₁` free) computing `H⁰` and `H¹` of the Čech data after every base change (Stacks,
Lemma 36.30.4, Tag 0B91, for a covering by two affines). -/
def HasPerfectModel : Prop :=
  ∃ (K₀ K₁ : ModuleCat.{u} A) (δ : K₀ →ₗ[A] K₁),
    Module.Finite A K₀ ∧ Module.Projective A K₀ ∧ Module.Finite A K₁ ∧ Module.Free A K₁ ∧
    ∀ (B : Type u) [CommRing B] [Algebra A B],
      Nonempty (ker (δ.baseChange B) ≃ₗ[B] TwoCech.H0 (f.baseChange B) (g.baseChange B)) ∧
      Nonempty (((B ⊗[A] K₁) ⧸ range (δ.baseChange B)) ≃ₗ[B]
        TwoCech.H1 (f.baseChange B) (g.baseChange B))

/-- Over a Noetherian ring, Čech data with flat terms and finite `H⁰`, `H¹` have a perfect model
(Mumford's lemma, `TwoTerm.exists_finite_projective_twoCech`). -/
theorem hasPerfectModel_of_noetherian [IsNoetherianRing A] [Module.Flat A P]
    [Module.Flat A Q] [Module.Flat A R] (h0 : Module.Finite A (TwoCech.H0 f g))
    (h1 : Module.Finite A (TwoCech.H1 f g)) : HasPerfectModel f g :=
  exists_finite_projective_twoCech f g h0 h1

variable {f g} {P' Q' R' : Type u} [AddCommGroup P'] [Module A P'] [AddCommGroup Q'] [Module A Q']
  [AddCommGroup R'] [Module A R'] {f' : P' →ₗ[A] R'} {g' : Q' →ₗ[A] R'}

/-- A perfect model only depends on the Čech data up to isomorphism. -/
theorem HasPerfectModel.of_equiv (H : HasPerfectModel f g) (α : P ≃ₗ[A] P') (β : Q ≃ₗ[A] Q')
    (γ : R ≃ₗ[A] R') (hf : f' ∘ₗ (α : P →ₗ[A] P') = (γ : R →ₗ[A] R') ∘ₗ f)
    (hg : g' ∘ₗ (β : Q →ₗ[A] Q') = (γ : R →ₗ[A] R') ∘ₗ g) : HasPerfectModel f' g' := by
  obtain ⟨K₀, K₁, δ, h₁, h₂, h₃, h₄, H⟩ := H
  refine ⟨K₀, K₁, δ, h₁, h₂, h₃, h₄, fun B _ _ ↦ ?_⟩
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := H B
  have hf' : f'.baseChange B ∘ₗ ((α.baseChange A B P P' : _ ≃ₗ[B] _) : B ⊗[A] P →ₗ[B] _) =
      ((γ.baseChange A B R R' : _ ≃ₗ[B] _) : B ⊗[A] R →ₗ[B] _) ∘ₗ f.baseChange B := by
    change f'.baseChange B ∘ₗ (α : P →ₗ[A] P').baseChange B =
      (γ : R →ₗ[A] R').baseChange B ∘ₗ f.baseChange B
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hf]
  have hg' : g'.baseChange B ∘ₗ ((β.baseChange A B Q Q' : _ ≃ₗ[B] _) : B ⊗[A] Q →ₗ[B] _) =
      ((γ.baseChange A B R R' : _ ≃ₗ[B] _) : B ⊗[A] R →ₗ[B] _) ∘ₗ g.baseChange B := by
    change g'.baseChange B ∘ₗ (β : Q →ₗ[A] Q').baseChange B =
      (γ : R →ₗ[A] R').baseChange B ∘ₗ g.baseChange B
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hg]
  exact ⟨⟨e₀ ≪≫ₗ TwoCech.equivH0 _ _ _ hf' hg'⟩, ⟨e₁ ≪≫ₗ TwoCech.equivH1 _ _ _ hf' hg'⟩⟩

section BaseChange

variable {A₀ : Type u} [CommRing A₀] [Algebra A₀ A] {P Q R : Type u} [AddCommGroup P]
  [Module A₀ P] [AddCommGroup Q] [Module A₀ Q] [AddCommGroup R] [Module A₀ R]
  {B : Type u} [CommRing B] [Algebra A B] [Algebra A₀ B] [IsScalarTower A₀ A B]

/-- `B ⊗_A (A ⊗_{A₀} M) ≅ B ⊗_{A₀} M`. -/
abbrev cancelBC (M : Type u) [AddCommGroup M] [Module A₀ M] :
    B ⊗[A] (A ⊗[A₀] M) ≃ₗ[B] B ⊗[A₀] M :=
  AlgebraTensorModule.cancelBaseChange A₀ A B B M

lemma cancelBC_comm {M N : Type u} [AddCommGroup M] [Module A₀ M] [AddCommGroup N] [Module A₀ N]
    (φ : M →ₗ[A₀] N) :
    ((cancelBC (A₀ := A₀) (B := B) (A := A) N : _ ≃ₗ[B] _) : B ⊗[A] (A ⊗[A₀] N) →ₗ[B] _) ∘ₗ
        (φ.baseChange A).baseChange B =
      φ.baseChange B ∘ₗ ((cancelBC (A₀ := A₀) (B := B) (A := A) M : _ ≃ₗ[B] _) :
        B ⊗[A] (A ⊗[A₀] M) →ₗ[B] _) := by
  refine LinearMap.ext fun x ↦ ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [LinearMap.coe_comp, Function.comp_apply] at hx hy ⊢;
                     rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b y =>
    induction y with
    | zero => simp
    | add y z hy hz =>
      simp only [LinearMap.coe_comp, Function.comp_apply, tmul_add] at hy hz ⊢
      rw [map_add, map_add, hy, hz, map_add, map_add]
    | tmul a m =>
      simp [AlgebraTensorModule.cancelBaseChange_tmul]

end BaseChange

/-- **Base change of a perfect model** along any ring map `A₀ → A`. -/
theorem HasPerfectModel.baseChange {A₀ : Type u} [CommRing A₀] [Algebra A₀ A] {P Q R : Type u}
    [AddCommGroup P] [Module A₀ P] [AddCommGroup Q] [Module A₀ Q] [AddCommGroup R] [Module A₀ R]
    {f : P →ₗ[A₀] R} {g : Q →ₗ[A₀] R} (H : HasPerfectModel f g) :
    HasPerfectModel (f.baseChange A) (g.baseChange A) := by
  obtain ⟨K₀, K₁, δ, h₁, h₂, h₃, h₄, H⟩ := H
  refine ⟨ModuleCat.of A (A ⊗[A₀] K₀), ModuleCat.of A (A ⊗[A₀] K₁), δ.baseChange A,
    inferInstanceAs (Module.Finite A (A ⊗[A₀] K₀)),
    inferInstanceAs (Module.Projective A (A ⊗[A₀] K₀)),
    inferInstanceAs (Module.Finite A (A ⊗[A₀] K₁)), inferInstanceAs (Module.Free A (A ⊗[A₀] K₁)),
    fun B _ _ ↦ ?_⟩
  letI : Algebra A₀ B := ((algebraMap A B).comp (algebraMap A₀ A)).toAlgebra
  haveI : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := H B
  have hδ := cancelBC_comm (A₀ := A₀) (A := A) (B := B) δ
  have hf := cancelBC_comm (A₀ := A₀) (A := A) (B := B) f
  have hg := cancelBC_comm (A₀ := A₀) (A := A) (B := B) g
  have hf' := TwoCech.symm_comp_eq (cancelBC (A₀ := A₀) (A := A) (B := B) P)
    (cancelBC (A₀ := A₀) (A := A) (B := B) R) hf.symm
  have hg' := TwoCech.symm_comp_eq (cancelBC (A₀ := A₀) (A := A) (B := B) Q)
    (cancelBC (A₀ := A₀) (A := A) (B := B) R) hg.symm
  exact ⟨⟨kerEquivOfComm _ _ hδ ≪≫ₗ e₀ ≪≫ₗ TwoCech.equivH0 _ _ _ hf' hg'⟩,
    ⟨cokerEquivOfComm _ _ hδ ≪≫ₗ e₁ ≪≫ₗ TwoCech.equivH1 _ _ _ hf' hg'⟩⟩

end CurvesJacobian.TwoTerm
