/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Extending an isomorphism of open normal subgroups to an isomorphism of extensions

This is the group-theoretic step of the existence part of [AbsTopII] Corollary 3.8.

Setting: groups `E₁ E₂ P₁ P₂`, surjections `f₁ : E₁ →* P₁`, `f₂ : E₂ →* P₂`, normal subgroups
`N₁ ⊴ P₁`, `N₂ ⊴ P₂`, an isomorphism `Φ : P₁ ≃* P₂` with `N₁.map Φ = N₂`, and
`Hᵢ := Nᵢ.comap fᵢ`. Given an isomorphism `a : H₁ ≃* H₂` compatible with `Φ`, such that the
`Hᵢ` are centre-free and every automorphism of `Hᵢ` over `Pᵢ` is conjugation by an element
of `ker fᵢ`, there is an isomorphism `φ : E₁ ≃* E₂` over `Φ` extending `a`
(`CurvesJacobian.Cusp.exists_mulEquiv_ext_of_unique`).

The element `φ e₁` is characterised as the unique `e ∈ E₂` with `f₂ e = Φ (f₁ e₁)` and
`e * a h * e⁻¹ = a (e₁ * h * e₁⁻¹)` for all `h ∈ H₁` (`CurvesJacobian.Cusp.IsExtConjLift`,
`CurvesJacobian.Cusp.IsExtConjLift.unique`).

The topological version (`CurvesJacobian.Cusp.exists_continuousMulEquiv_ext_of_unique`) works
with topological groups `Eᵢ`, open `Hᵢ` and `a : H₁ ≃ₜ* H₂`; the extension is then a
`ContinuousMulEquiv`, since a homomorphism which is continuous on an open subgroup is
continuous.
-/

namespace CurvesJacobian.Cusp

section Algebraic

variable {E₁ E₂ P₁ P₂ : Type*} [Group E₁] [Group E₂] [Group P₁] [Group P₂]

/-- `e : E₂` is a lift of `e₁ : E₁` for the data `(Φ, a)`: it lies over `Φ (f₁ e₁)` and
conjugation by `e` on `H₂` corresponds under `a` to conjugation by `e₁` on `H₁`. -/
def IsExtConjLift (f₁ : E₁ →* P₁) (f₂ : E₂ →* P₂) {N₁ : Subgroup P₁} {N₂ : Subgroup P₂}
    [N₁.Normal] [N₂.Normal] (Φ : P₁ ≃* P₂) (a : N₁.comap f₁ ≃* N₂.comap f₂)
    (e₁ : E₁) (e : E₂) : Prop :=
  f₂ e = Φ (f₁ e₁) ∧
    ∀ h : N₁.comap f₁, e * (a h : E₂) * e⁻¹ = (a (MulAut.conjNormal e₁ h) : E₂)

variable {f₁ : E₁ →* P₁} {f₂ : E₂ →* P₂} {N₁ : Subgroup P₁} {N₂ : Subgroup P₂}
  [N₁.Normal] [N₂.Normal] {Φ : P₁ ≃* P₂} {a : N₁.comap f₁ ≃* N₂.comap f₂}

/-- Uniqueness of lifts: if `H₂` is centre-free, an element has at most one lift. -/
theorem IsExtConjLift.unique (hZ : Subgroup.center (N₂.comap f₂) = ⊥) {e₁ : E₁} {e e' : E₂}
    (he : IsExtConjLift f₁ f₂ Φ a e₁ e) (he' : IsExtConjLift f₁ f₂ Φ a e₁ e') : e = e' := by
  obtain ⟨he1, he2⟩ := he
  obtain ⟨he1', he2'⟩ := he'
  have hd : f₂ (e'⁻¹ * e) = 1 := by rw [map_mul, map_inv, he1, he1', inv_mul_cancel]
  have hmem : e'⁻¹ * e ∈ N₂.comap f₂ := by
    rw [Subgroup.mem_comap, hd]; exact N₂.one_mem
  have hc : (⟨e'⁻¹ * e, hmem⟩ : N₂.comap f₂) ∈ Subgroup.center (N₂.comap f₂) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := a.surjective g
    have hk : e * (a k : E₂) * e⁻¹ = e' * (a k : E₂) * e'⁻¹ := (he2 k).trans (he2' k).symm
    apply Subtype.ext
    change (a k : E₂) * (e'⁻¹ * e) = e'⁻¹ * e * (a k : E₂)
    calc (a k : E₂) * (e'⁻¹ * e) = e'⁻¹ * (e' * (a k : E₂) * e'⁻¹) * e := by group
      _ = e'⁻¹ * (e * (a k : E₂) * e⁻¹) * e := by rw [hk]
      _ = e'⁻¹ * e * (a k : E₂) := by group
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : e'⁻¹ * e = 1 := congrArg Subtype.val hc
  exact (inv_mul_eq_one.mp h1).symm

theorem isExtConjLift_one : IsExtConjLift f₁ f₂ Φ a 1 1 := by
  refine ⟨by simp, fun h => ?_⟩
  simp

theorem IsExtConjLift.mul {x y : E₁} {e e' : E₂} (he : IsExtConjLift f₁ f₂ Φ a x e)
    (he' : IsExtConjLift f₁ f₂ Φ a y e') : IsExtConjLift f₁ f₂ Φ a (x * y) (e * e') := by
  refine ⟨by rw [map_mul, map_mul, map_mul, he.1, he'.1], fun h => ?_⟩
  calc e * e' * (a h : E₂) * (e * e')⁻¹ = e * (e' * (a h : E₂) * e'⁻¹) * e⁻¹ := by group
    _ = e * (a (MulAut.conjNormal y h) : E₂) * e⁻¹ := by rw [he'.2 h]
    _ = (a (MulAut.conjNormal x (MulAut.conjNormal y h)) : E₂) := he.2 _
    _ = (a (MulAut.conjNormal (x * y) h) : E₂) := by rw [map_mul, MulAut.mul_apply]

/-- Elements of `H₁` are lifted by `a`. -/
theorem isExtConjLift_self (ha : ∀ h, f₂ (a h) = Φ (f₁ h)) (h₀ : N₁.comap f₁) :
    IsExtConjLift f₁ f₂ Φ a (h₀ : E₁) (a h₀ : E₂) := by
  refine ⟨ha h₀, fun h => ?_⟩
  have hc : MulAut.conjNormal (h₀ : E₁) h = h₀ * h * h₀⁻¹ := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    simp
  rw [hc, map_mul, map_mul, map_inv]
  simp

/-- Lifts are symmetric: a lift for `(Φ, a)` gives a lift for `(Φ⁻¹, a⁻¹)` in reverse. -/
theorem IsExtConjLift.symm {e₁ : E₁} {e₂ : E₂} (he : IsExtConjLift f₁ f₂ Φ a e₁ e₂) :
    IsExtConjLift f₂ f₁ Φ.symm a.symm e₂ e₁ := by
  refine ⟨by rw [he.1, Φ.symm_apply_apply], fun h => ?_⟩
  obtain ⟨k, rfl⟩ := a.surjective h
  have hc : MulAut.conjNormal e₂ (a k) = a (MulAut.conjNormal e₁ k) := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact he.2 k
  rw [hc, a.symm_apply_apply, a.symm_apply_apply, MulAut.conjNormal_apply]

/-- Producing a lift from an element `e₂'` over `Φ (f₁ e₁)` and an element `n ∈ ker f₂`
realising the automorphism `conj(e₂')⁻¹ ∘ a ∘ conj(e₁) ∘ a⁻¹` of `H₂` as a conjugation. -/
theorem isExtConjLift_of_conj {e₁ : E₁} {e₂ n : E₂} (he : f₂ e₂ = Φ (f₁ e₁)) (hn1 : f₂ n = 1)
    (hn : ∀ h : N₂.comap f₂, (MulAut.conjNormal e₂⁻¹
      (a (MulAut.conjNormal e₁ (a.symm h))) : E₂) = n * h * n⁻¹) :
    IsExtConjLift f₁ f₂ Φ a e₁ (e₂ * n) := by
  refine ⟨by rw [map_mul, hn1, mul_one, he], fun k => ?_⟩
  have hk := hn (a k)
  rw [a.symm_apply_apply, MulAut.conjNormal_apply, inv_inv] at hk
  calc e₂ * n * (a k : E₂) * (e₂ * n)⁻¹ = e₂ * (n * (a k : E₂) * n⁻¹) * e₂⁻¹ := by group
    _ = e₂ * (e₂⁻¹ * (a (MulAut.conjNormal e₁ k) : E₂) * e₂) * e₂⁻¹ := by rw [hk]
    _ = (a (MulAut.conjNormal e₁ k) : E₂) := by group

/-- The automorphism `conj(e₂)⁻¹ ∘ a ∘ conj(e₁) ∘ a⁻¹` of `H₂` lies over the identity of `P₂`
when `f₂ e₂ = Φ (f₁ e₁)`. -/
theorem map_conj_conj_eq (ha : ∀ h, f₂ (a h) = Φ (f₁ h)) {e₁ : E₁} {e₂ : E₂}
    (he : f₂ e₂ = Φ (f₁ e₁)) (h : N₂.comap f₂) :
    f₂ (MulAut.conjNormal e₂⁻¹ (a (MulAut.conjNormal e₁ (a.symm h))) : E₂) = f₂ h := by
  have hs : Φ (f₁ (a.symm h : E₁)) = f₂ h := by rw [← ha, a.apply_symm_apply]
  rw [MulAut.conjNormal_apply, map_mul, map_mul, ha, MulAut.conjNormal_apply]
  simp only [map_mul, map_inv, hs, he]
  group

/-- The lift homomorphism `E₁ →* E₂`, assuming lifts exist and `H₂` is centre-free. -/
noncomputable def extLiftHom (hZ : Subgroup.center (N₂.comap f₂) = ⊥)
    (hex : ∀ e₁, ∃ e₂, IsExtConjLift f₁ f₂ Φ a e₁ e₂) : E₁ →* E₂ where
  toFun e₁ := (hex e₁).choose
  map_one' := IsExtConjLift.unique hZ (hex 1).choose_spec isExtConjLift_one
  map_mul' x y :=
    IsExtConjLift.unique hZ (hex (x * y)).choose_spec ((hex x).choose_spec.mul (hex y).choose_spec)

theorem extLiftHom_spec (hZ : Subgroup.center (N₂.comap f₂) = ⊥)
    (hex : ∀ e₁, ∃ e₂, IsExtConjLift f₁ f₂ Φ a e₁ e₂) (e₁ : E₁) :
    IsExtConjLift f₁ f₂ Φ a e₁ (extLiftHom hZ hex e₁) :=
  (hex e₁).choose_spec

/-- If lifts exist in both directions and both `Hᵢ` are centre-free, there is an isomorphism
`φ : E₁ ≃* E₂` such that `φ e` is a lift of `e` for every `e`. -/
theorem exists_mulEquiv_isExtConjLift (hZ₁ : Subgroup.center (N₁.comap f₁) = ⊥)
    (hZ₂ : Subgroup.center (N₂.comap f₂) = ⊥)
    (hex₁ : ∀ e₁, ∃ e₂, IsExtConjLift f₁ f₂ Φ a e₁ e₂)
    (hex₂ : ∀ e₂, ∃ e₁, IsExtConjLift f₂ f₁ Φ.symm a.symm e₂ e₁) :
    ∃ φ : E₁ ≃* E₂, ∀ e, IsExtConjLift f₁ f₂ Φ a e (φ e) := by
  have h1 : (extLiftHom hZ₁ hex₂).comp (extLiftHom hZ₂ hex₁) = MonoidHom.id E₁ := by
    ext e
    exact IsExtConjLift.unique hZ₁ (extLiftHom_spec hZ₁ hex₂ _)
      (extLiftHom_spec hZ₂ hex₁ e).symm
  have h2 : (extLiftHom hZ₂ hex₁).comp (extLiftHom hZ₁ hex₂) = MonoidHom.id E₂ := by
    ext e
    have hs := (extLiftHom_spec hZ₁ hex₂ e).symm
    rw [MulEquiv.symm_symm, MulEquiv.symm_symm] at hs
    exact IsExtConjLift.unique hZ₂ (extLiftHom_spec hZ₂ hex₁ _) hs
  exact ⟨MonoidHom.toMulEquiv _ _ h1 h2, extLiftHom_spec hZ₂ hex₁⟩

/-- Existence of lifts from the uniqueness hypothesis on automorphisms of `H₂` over `P₂`. -/
theorem exists_isExtConjLift (hf₂ : Function.Surjective f₂) (ha : ∀ h, f₂ (a h) = Φ (f₁ h))
    (hU₂ : ∀ β : N₂.comap f₂ ≃* N₂.comap f₂, (∀ h, f₂ (β h) = f₂ h) →
      ∃ n : E₂, f₂ n = 1 ∧ ∀ h, (β h : E₂) = n * h * n⁻¹) (e₁ : E₁) :
    ∃ e₂, IsExtConjLift f₁ f₂ Φ a e₁ e₂ := by
  obtain ⟨e₂, he⟩ := hf₂ (Φ (f₁ e₁))
  obtain ⟨n, hn1, hn⟩ := hU₂
    (a.symm.trans ((MulAut.conjNormal e₁).trans (a.trans (MulAut.conjNormal e₂⁻¹))))
    (map_conj_conj_eq ha he)
  exact ⟨e₂ * n, isExtConjLift_of_conj he hn1 hn⟩

/-- **Extension of isomorphisms** (group step of [AbsTopII] Cor. 3.8): an isomorphism
`a : H₁ ≃* H₂` of the preimages `Hᵢ = fᵢ⁻¹(Nᵢ)` over `Φ` extends to an isomorphism `E₁ ≃* E₂`
over `Φ`, provided the `Hᵢ` are centre-free and every automorphism of `Hᵢ` over `Pᵢ` is a
conjugation by an element of `ker fᵢ`. -/
theorem exists_mulEquiv_ext_of_unique (hf₁ : Function.Surjective f₁)
    (hf₂ : Function.Surjective f₂) (_hN : N₁.map Φ.toMonoidHom = N₂)
    (ha : ∀ h, f₂ (a h) = Φ (f₁ h))
    (hZ₁ : Subgroup.center (N₁.comap f₁) = ⊥) (hZ₂ : Subgroup.center (N₂.comap f₂) = ⊥)
    (hU₁ : ∀ β : N₁.comap f₁ ≃* N₁.comap f₁, (∀ h, f₁ (β h) = f₁ h) →
      ∃ n : E₁, f₁ n = 1 ∧ ∀ h, (β h : E₁) = n * h * n⁻¹)
    (hU₂ : ∀ β : N₂.comap f₂ ≃* N₂.comap f₂, (∀ h, f₂ (β h) = f₂ h) →
      ∃ n : E₂, f₂ n = 1 ∧ ∀ h, (β h : E₂) = n * h * n⁻¹) :
    ∃ φ : E₁ ≃* E₂, (∀ e, f₂ (φ e) = Φ (f₁ e)) ∧ ∀ h : N₁.comap f₁, φ h = a h := by
  have ha' : ∀ h, f₁ (a.symm h) = Φ.symm (f₂ h) := fun h => by
    rw [← Φ.symm_apply_apply (f₁ _), ← ha, a.apply_symm_apply]
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_isExtConjLift hZ₁ hZ₂
    (exists_isExtConjLift hf₂ ha hU₂) (exists_isExtConjLift hf₁ ha' hU₁)
  exact ⟨φ, fun e => (hφ e).1, fun h => IsExtConjLift.unique hZ₂ (hφ h)
    (isExtConjLift_self ha h)⟩

end Algebraic

section Topological

/-- Conjugation by `g` as a continuous automorphism of a normal subgroup. -/
def conjNormalContField {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.Normal] (g : G) : H ≃ₜ* H :=
  { MulAut.conjNormal g with
    continuous_toFun := by
      apply continuous_induced_rng.2
      change Continuous (Subtype.val ∘ fun h : H => MulAut.conjNormal g h)
      have hf : (Subtype.val ∘ fun h : H => MulAut.conjNormal g h) =
          fun h : H => g * (h : G) * g⁻¹ := funext fun h => MulAut.conjNormal_apply g h
      rw [hf]
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    continuous_invFun := by
      apply continuous_induced_rng.2
      change Continuous (Subtype.val ∘ fun h : H => (MulAut.conjNormal g).symm h)
      have hf : (Subtype.val ∘ fun h : H => (MulAut.conjNormal g).symm h) =
          fun h : H => g⁻¹ * (h : G) * g := funext fun h => MulAut.conjNormal_symm_apply g h
      rw [hf]
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const }

/-- A homomorphism of topological groups which is continuous on an open subgroup is
continuous. -/
theorem continuous_of_continuous_openSubgroupField {G K : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group K] [TopologicalSpace K] [IsTopologicalGroup K] (φ : G →* K)
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (hc : Continuous fun h : H => φ h) :
    Continuous φ := by
  apply continuous_of_continuousAt_one φ
  have hon : ContinuousOn φ (H : Set G) := continuousOn_iff_continuous_restrict.2 hc
  exact hon.continuousAt (hH.mem_nhds H.one_mem)

variable {E₁ E₂ P₁ P₂ : Type*} [Group E₁] [Group E₂] [Group P₁] [Group P₂]
  [TopologicalSpace E₁] [IsTopologicalGroup E₁] [TopologicalSpace E₂] [IsTopologicalGroup E₂]
  {f₁ : E₁ →* P₁} {f₂ : E₂ →* P₂} {N₁ : Subgroup P₁} {N₂ : Subgroup P₂}
  [N₁.Normal] [N₂.Normal] {Φ : P₁ ≃* P₂}

/-- Existence of lifts from the uniqueness hypothesis on continuous automorphisms. -/
theorem exists_isExtConjLift_cont {a : N₁.comap f₁ ≃ₜ* N₂.comap f₂}
    (hf₂ : Function.Surjective f₂) (ha : ∀ h, f₂ (a h) = Φ (f₁ h))
    (hU₂ : ∀ β : N₂.comap f₂ ≃ₜ* N₂.comap f₂, (∀ h, f₂ (β h) = f₂ h) →
      ∃ n : E₂, f₂ n = 1 ∧ ∀ h, (β h : E₂) = n * h * n⁻¹) (e₁ : E₁) :
    ∃ e₂, IsExtConjLift f₁ f₂ Φ a.toMulEquiv e₁ e₂ := by
  obtain ⟨e₂, he⟩ := hf₂ (Φ (f₁ e₁))
  obtain ⟨n, hn1, hn⟩ := hU₂
    (a.symm.trans ((conjNormalContField _ e₁).trans (a.trans (conjNormalContField _ e₂⁻¹))))
    (map_conj_conj_eq (a := a.toMulEquiv) ha he)
  exact ⟨e₂ * n, isExtConjLift_of_conj (a := a.toMulEquiv) he hn1 hn⟩

/-- **Extension of isomorphisms, topological version**: for topological groups `Eᵢ` with open
`Hᵢ = fᵢ⁻¹(Nᵢ)`, a topological isomorphism `a : H₁ ≃ₜ* H₂` over `Φ` extends to a topological
isomorphism `E₁ ≃ₜ* E₂` over `Φ`, provided the `Hᵢ` are centre-free and every continuous
automorphism of `Hᵢ` over `Pᵢ` is a conjugation by an element of `ker fᵢ`. -/
theorem exists_continuousMulEquiv_ext_of_unique {a : N₁.comap f₁ ≃ₜ* N₂.comap f₂}
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂)
    (_hN : N₁.map Φ.toMonoidHom = N₂)
    (hH₁ : IsOpen ((N₁.comap f₁ : Subgroup E₁) : Set E₁))
    (hH₂ : IsOpen ((N₂.comap f₂ : Subgroup E₂) : Set E₂))
    (ha : ∀ h, f₂ (a h) = Φ (f₁ h))
    (hZ₁ : Subgroup.center (N₁.comap f₁) = ⊥) (hZ₂ : Subgroup.center (N₂.comap f₂) = ⊥)
    (hU₁ : ∀ β : N₁.comap f₁ ≃ₜ* N₁.comap f₁, (∀ h, f₁ (β h) = f₁ h) →
      ∃ n : E₁, f₁ n = 1 ∧ ∀ h, (β h : E₁) = n * h * n⁻¹)
    (hU₂ : ∀ β : N₂.comap f₂ ≃ₜ* N₂.comap f₂, (∀ h, f₂ (β h) = f₂ h) →
      ∃ n : E₂, f₂ n = 1 ∧ ∀ h, (β h : E₂) = n * h * n⁻¹) :
    ∃ φ : E₁ ≃ₜ* E₂, (∀ e, f₂ (φ e) = Φ (f₁ e)) ∧ ∀ h : N₁.comap f₁, φ h = a h := by
  have ha' : ∀ h, f₁ (a.symm h) = Φ.symm (f₂ h) := fun h => by
    rw [← Φ.symm_apply_apply (f₁ _), ← ha, a.apply_symm_apply]
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_isExtConjLift (a := a.toMulEquiv) hZ₁ hZ₂
    (exists_isExtConjLift_cont hf₂ ha hU₂) (exists_isExtConjLift_cont (a := a.symm) hf₁ ha' hU₁)
  have hres : ∀ h : N₁.comap f₁, φ h = a h := fun h =>
    IsExtConjLift.unique hZ₂ (hφ h) (isExtConjLift_self (a := a.toMulEquiv) ha h)
  have hres' : ∀ h : N₂.comap f₂, φ.symm h = a.symm h := fun h => by
    rw [MulEquiv.symm_apply_eq, hres, a.apply_symm_apply]
  have hc : Continuous φ := by
    refine continuous_of_continuous_openSubgroupField φ.toMonoidHom _ hH₁ ?_
    have hf : (fun h : N₁.comap f₁ => φ.toMonoidHom h) = fun h => (a h : E₂) :=
      funext fun h => hres h
    rw [hf]
    exact continuous_subtype_val.comp a.continuous_toFun
  have hc' : Continuous φ.symm := by
    refine continuous_of_continuous_openSubgroupField φ.symm.toMonoidHom _ hH₂ ?_
    have hf : (fun h : N₂.comap f₂ => φ.symm.toMonoidHom h) = fun h => (a.symm h : E₁) :=
      funext fun h => hres' h
    rw [hf]
    exact continuous_subtype_val.comp a.symm.continuous_toFun
  exact ⟨{ φ with continuous_toFun := hc, continuous_invFun := hc' },
    fun e => (hφ e).1, hres⟩

end Topological

end CurvesJacobian.Cusp
