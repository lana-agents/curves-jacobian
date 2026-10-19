/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Group

/-!
# Homomorphisms of extensions with centre-free kernels and compatible outer actions

Let `p₁ : E₁ →* Q` and `p₂ : E₂ →* Q` be group homomorphisms (extensions of `Q` by their
kernels `N₁ = p₁.ker`, `N₂ = p₂.ker`) and `ψ : N₁ →* N₂` a surjective homomorphism, where `N₂`
is centre-free. Suppose the conjugation actions are compatible: every `e₁ : E₁` has a lift
`e₂ : E₂` over the same element of `Q` with `ψ (e₁ n e₁⁻¹) = e₂ (ψ n) e₂⁻¹` for all `n ∈ N₁`
(`CurvesJacobian.Cusp.IsExtLift`). Then:

* the lift `e₂` is unique (`CurvesJacobian.Cusp.isExtLift_unique`,
  `CurvesJacobian.Cusp.exists_unique_isExtLift`): two lifts differ by an element of `N₂`
  centralising `ψ N₁ = N₂`;
* `e₁ ↦ e₂` is a homomorphism `CurvesJacobian.Cusp.extMap : E₁ →* E₂` over `Q` extending `ψ`,
  and the only such homomorphism (`CurvesJacobian.Cusp.extMap_unique`);
* it is surjective if `p₁` is, and its kernel is the image of `ψ.ker`;
* for topological groups with `N₁` open and `ψ` continuous it is continuous
  (`CurvesJacobian.Cusp.extMapCont`), and a topological isomorphism
  (`CurvesJacobian.Cusp.extMapEquiv`) if moreover `E₁` is compact, `E₂` Hausdorff, `p₁`
  surjective and `ψ` injective.

This is the out-semidirect functoriality used in the `⋎`-steps of [AbsTopI] Thm 4.7 (i), proof
(out-semidirect products, [AbsTopII] Cor 3.7 (b)).
-/

open Function

namespace CurvesJacobian.Cusp

variable {E₁ E₂ Q : Type*} [Group E₁] [Group E₂] [Group Q]

/-- Conjugation by `e : E₁` on the kernel of `p : E₁ →* Q`. -/
def kerConj (p : E₁ →* Q) (e : E₁) (n : p.ker) : p.ker :=
  ⟨e * n * e⁻¹, p.normal_ker.conj_mem n n.2 e⟩

@[simp]
lemma coe_kerConj (p : E₁ →* Q) (e : E₁) (n : p.ker) : (kerConj p e n : E₁) = e * n * e⁻¹ :=
  rfl

lemma kerConj_mul (p : E₁ →* Q) (a b : E₁) (n : p.ker) :
    kerConj p (a * b) n = kerConj p a (kerConj p b n) :=
  Subtype.ext (by simp only [coe_kerConj]; group)

lemma kerConj_one (p : E₁ →* Q) (n : p.ker) : kerConj p 1 n = n :=
  Subtype.ext (by simp)

lemma kerConj_of_mem (p : E₁ →* Q) (m n : p.ker) : kerConj p m n = m * n * m⁻¹ :=
  Subtype.ext rfl

variable (p₁ : E₁ →* Q) (p₂ : E₂ →* Q) (ψ : p₁.ker →* p₂.ker)

/-- `e₂ : E₂` is a compatible lift of `e₁ : E₁`: it lies over the same element of `Q` and
conjugation by `e₂` on `p₂.ker` corresponds under `ψ` to conjugation by `e₁` on `p₁.ker`. -/
def IsExtLift (e₁ : E₁) (e₂ : E₂) : Prop :=
  p₂ e₂ = p₁ e₁ ∧ ∀ n : p₁.ker, (ψ (kerConj p₁ e₁ n) : E₂) = e₂ * ψ n * e₂⁻¹

variable {p₁ p₂ ψ}

/-- Uniqueness of compatible lifts, [AbsTopI] Thm 4.7 (i), proof (out-semidirect products,
[AbsTopII] Cor 3.7 (b)): two lifts differ by an element of `p₂.ker` centralising the image of
`ψ`, which is all of `p₂.ker`, hence by a central element, hence by `1`. -/
theorem isExtLift_unique (hcen : Subgroup.center p₂.ker = ⊥) (hψ : Surjective ψ) {e₁ : E₁}
    {e₂ e₂' : E₂} (h : IsExtLift p₁ p₂ ψ e₁ e₂) (h' : IsExtLift p₁ p₂ ψ e₁ e₂') : e₂ = e₂' := by
  let d : p₂.ker := ⟨e₂⁻¹ * e₂', by simp [MonoidHom.mem_ker, h.1, h'.1]⟩
  have hd : d ∈ Subgroup.center p₂.ker := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨n, rfl⟩ := hψ z
    apply Subtype.ext
    have hn := (h.2 n).symm.trans (h'.2 n)
    change (ψ n : E₂) * (e₂⁻¹ * e₂') = e₂⁻¹ * e₂' * ψ n
    calc (ψ n : E₂) * (e₂⁻¹ * e₂') = e₂⁻¹ * (e₂ * ψ n * e₂⁻¹) * e₂' := by group
      _ = e₂⁻¹ * (e₂' * ψ n * e₂'⁻¹) * e₂' := by rw [hn]
      _ = e₂⁻¹ * e₂' * ψ n := by group
  rw [hcen, Subgroup.mem_bot] at hd
  exact inv_mul_eq_one.mp (congrArg Subtype.val hd)

/-- Under the compatibility hypothesis `hcomp`, every `e₁` has a unique compatible lift. -/
theorem exists_unique_isExtLift (hcen : Subgroup.center p₂.ker = ⊥) (hψ : Surjective ψ)
    (hcomp : ∀ e₁ : E₁, ∃ e₂ : E₂, IsExtLift p₁ p₂ ψ e₁ e₂) (e₁ : E₁) :
    ∃! e₂ : E₂, IsExtLift p₁ p₂ ψ e₁ e₂ :=
  let ⟨e₂, h⟩ := hcomp e₁
  ⟨e₂, h, fun _ h' => isExtLift_unique hcen hψ h' h⟩

lemma isExtLift_one : IsExtLift p₁ p₂ ψ 1 1 :=
  ⟨by simp, fun n => by rw [kerConj_one]; simp⟩

lemma isExtLift_mul {a b : E₁} {a' b' : E₂} (ha : IsExtLift p₁ p₂ ψ a a')
    (hb : IsExtLift p₁ p₂ ψ b b') : IsExtLift p₁ p₂ ψ (a * b) (a' * b') :=
  ⟨by simp [ha.1, hb.1], fun n => by rw [kerConj_mul, ha.2, hb.2]; group⟩

/-- An element of `p₁.ker` is compatibly lifted by its image under `ψ`. -/
lemma isExtLift_of_mem (m : p₁.ker) : IsExtLift p₁ p₂ ψ m (ψ m) :=
  ⟨(MonoidHom.mem_ker.mp (ψ m).2).trans (MonoidHom.mem_ker.mp m.2).symm,
    fun n => by rw [kerConj_of_mem]; simp⟩

/-- A homomorphism over `Q` extending `ψ` sends every element to a compatible lift of it. -/
lemma isExtLift_of_hom (Φ : E₁ →* E₂) (hp : p₂.comp Φ = p₁) (hΦ : ∀ n : p₁.ker, Φ n = ψ n)
    (e₁ : E₁) : IsExtLift p₁ p₂ ψ e₁ (Φ e₁) :=
  ⟨DFunLike.congr_fun hp e₁, fun n => by simp only [← hΦ, coe_kerConj, map_mul, map_inv]⟩

/-- The homomorphism of extensions determined by `ψ` and the compatibility of outer actions,
[AbsTopI] Thm 4.7 (i), proof (out-semidirect products, [AbsTopII] Cor 3.7 (b)): it sends
`e₁` to its unique compatible lift. -/
noncomputable def extMap (hcen : Subgroup.center p₂.ker = ⊥) (hψ : Surjective ψ)
    (hcomp : ∀ e₁ : E₁, ∃ e₂ : E₂, IsExtLift p₁ p₂ ψ e₁ e₂) : E₁ →* E₂ where
  toFun e := (hcomp e).choose
  map_one' := isExtLift_unique hcen hψ (hcomp 1).choose_spec isExtLift_one
  map_mul' a b := isExtLift_unique hcen hψ (hcomp (a * b)).choose_spec
    (isExtLift_mul (hcomp a).choose_spec (hcomp b).choose_spec)

section extMap

variable (hcen : Subgroup.center p₂.ker = ⊥) (hψ : Surjective ψ)
  (hcomp : ∀ e₁ : E₁, ∃ e₂ : E₂, IsExtLift p₁ p₂ ψ e₁ e₂)

/-- `extMap` sends each element to a compatible lift. -/
theorem isExtLift_extMap (e₁ : E₁) : IsExtLift p₁ p₂ ψ e₁ (extMap hcen hψ hcomp e₁) :=
  (hcomp e₁).choose_spec

/-- `extMap` lies over `Q`. -/
theorem comp_extMap : p₂.comp (extMap hcen hψ hcomp) = p₁ :=
  MonoidHom.ext fun e => (isExtLift_extMap hcen hψ hcomp e).1

/-- `extMap` lies over `Q` (pointwise form). -/
theorem apply_extMap (e₁ : E₁) : p₂ (extMap hcen hψ hcomp e₁) = p₁ e₁ :=
  (isExtLift_extMap hcen hψ hcomp e₁).1

/-- `extMap` extends `ψ`. -/
theorem extMap_apply_ker (n : p₁.ker) : extMap hcen hψ hcomp n = ψ n :=
  isExtLift_unique hcen hψ (isExtLift_extMap hcen hψ hcomp n) (isExtLift_of_mem n)

/-- `extMap` is compatible with the conjugation actions on the kernels. -/
theorem extMap_conj (e₁ : E₁) (n : p₁.ker) :
    (ψ (kerConj p₁ e₁ n) : E₂) = extMap hcen hψ hcomp e₁ * ψ n * (extMap hcen hψ hcomp e₁)⁻¹ :=
  (isExtLift_extMap hcen hψ hcomp e₁).2 n

/-- `extMap` is the unique homomorphism over `Q` extending `ψ`. -/
theorem extMap_unique (Φ : E₁ →* E₂) (hp : p₂.comp Φ = p₁) (hΦ : ∀ n : p₁.ker, Φ n = ψ n) :
    Φ = extMap hcen hψ hcomp :=
  MonoidHom.ext fun e => isExtLift_unique hcen hψ (isExtLift_of_hom Φ hp hΦ e)
    (isExtLift_extMap hcen hψ hcomp e)

/-- `extMap` is surjective if `p₁` is. -/
theorem extMap_surjective (hp₁ : Surjective p₁) : Surjective (extMap hcen hψ hcomp) := by
  intro e₂
  obtain ⟨e₁, he⟩ := hp₁ (p₂ e₂)
  have hk : (extMap hcen hψ hcomp e₁)⁻¹ * e₂ ∈ p₂.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, apply_extMap, he, inv_mul_cancel]
  obtain ⟨m, hm⟩ := hψ ⟨_, hk⟩
  refine ⟨e₁ * m, ?_⟩
  rw [map_mul, extMap_apply_ker, hm]
  simp

/-- The kernel of `extMap` is the image of the kernel of `ψ`. -/
theorem ker_extMap : (extMap hcen hψ hcomp).ker = ψ.ker.map p₁.ker.subtype := by
  ext e
  constructor
  · intro he
    have he1 : e ∈ p₁.ker := by
      rw [MonoidHom.mem_ker, ← apply_extMap hcen hψ hcomp e, MonoidHom.mem_ker.mp he, map_one]
    refine ⟨⟨e, he1⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have := extMap_apply_ker hcen hψ hcomp ⟨e, he1⟩
    rw [Subtype.ext_iff, ← this]
    exact MonoidHom.mem_ker.mp he
  · rintro ⟨n, hn, rfl⟩
    change extMap hcen hψ hcomp (n : E₁) = 1
    rw [extMap_apply_ker, MonoidHom.mem_ker.mp hn]
    rfl

/-- `extMap` is injective if `ψ` is. -/
theorem extMap_injective (hψi : Injective ψ) : Injective (extMap hcen hψ hcomp) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_extMap, (MonoidHom.ker_eq_bot_iff ψ).mpr hψi,
    Subgroup.map_bot]

section Topology

variable [TopologicalSpace E₁] [IsTopologicalGroup E₁] [TopologicalSpace E₂]
  [IsTopologicalGroup E₂]

/-- `extMap` is continuous if `p₁.ker` is open and `ψ` is continuous: it is continuous on the
open subgroup `p₁.ker`, where it agrees with `ψ`. -/
theorem continuous_extMap (hN : IsOpen (p₁.ker : Set E₁)) (hψc : Continuous ψ) :
    Continuous (extMap hcen hψ hcomp) := by
  apply continuous_of_continuousAt_one
  have hon : ContinuousOn (extMap hcen hψ hcomp) (p₁.ker : Set E₁) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (p₁.ker : Set E₁).restrict (extMap hcen hψ hcomp) = fun n => (ψ n : E₂) :=
      funext fun n => extMap_apply_ker hcen hψ hcomp n
    rw [this]
    exact continuous_subtype_val.comp hψc
  exact hon.continuousAt (hN.mem_nhds (one_mem _))

/-- `extMap` as a continuous homomorphism, for `p₁.ker` open and `ψ` continuous. -/
noncomputable def extMapCont (hN : IsOpen (p₁.ker : Set E₁)) (hψc : Continuous ψ) :
    E₁ →ₜ* E₂ :=
  { extMap hcen hψ hcomp with continuous_toFun := continuous_extMap hcen hψ hcomp hN hψc }

variable (hN : IsOpen (p₁.ker : Set E₁)) (hψc : Continuous ψ)

@[simp]
theorem coe_extMapCont : ⇑(extMapCont hcen hψ hcomp hN hψc) = extMap hcen hψ hcomp :=
  rfl

theorem extMapCont_toMonoidHom :
    (extMapCont hcen hψ hcomp hN hψc).toMonoidHom = extMap hcen hψ hcomp :=
  rfl

/-- `extMapCont` lies over `Q`. -/
theorem apply_extMapCont (e₁ : E₁) : p₂ (extMapCont hcen hψ hcomp hN hψc e₁) = p₁ e₁ :=
  apply_extMap hcen hψ hcomp e₁

/-- `extMapCont` extends `ψ`. -/
theorem extMapCont_apply_ker (n : p₁.ker) : extMapCont hcen hψ hcomp hN hψc n = ψ n :=
  extMap_apply_ker hcen hψ hcomp n

/-- `extMapCont` is the unique continuous homomorphism over `Q` extending `ψ`. -/
theorem extMapCont_unique (Φ : E₁ →ₜ* E₂) (hp : p₂.comp Φ.toMonoidHom = p₁)
    (hΦ : ∀ n : p₁.ker, Φ n = ψ n) : Φ = extMapCont hcen hψ hcomp hN hψc :=
  ContinuousMonoidHom.ext fun e => DFunLike.congr_fun (extMap_unique hcen hψ hcomp
    Φ.toMonoidHom hp hΦ) e

/-- `extMapCont` is surjective if `p₁` is. -/
theorem extMapCont_surjective (hp₁ : Surjective p₁) :
    Surjective (extMapCont hcen hψ hcomp hN hψc) :=
  extMap_surjective hcen hψ hcomp hp₁

/-- The kernel of `extMapCont` is the image of the kernel of `ψ`. -/
theorem ker_extMapCont :
    (extMapCont hcen hψ hcomp hN hψc).toMonoidHom.ker = ψ.ker.map p₁.ker.subtype :=
  ker_extMap hcen hψ hcomp

/-- For `E₁` compact, `E₂` Hausdorff, `p₁` surjective and `ψ` injective, `extMap` is an
isomorphism of topological groups. -/
noncomputable def extMapEquiv [CompactSpace E₁] [T2Space E₂] (hp₁ : Surjective p₁)
    (hψi : Injective ψ) : E₁ ≃ₜ* E₂ :=
  let m : E₁ ≃* E₂ := MulEquiv.ofBijective (extMap hcen hψ hcomp)
    ⟨extMap_injective hcen hψ hcomp hψi, extMap_surjective hcen hψ hcomp hp₁⟩
  let h : E₁ ≃ₜ E₂ :=
    Continuous.homeoOfEquivCompactToT2 (f := m.toEquiv) (continuous_extMap hcen hψ hcomp hN hψc)
  { m with
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

@[simp]
theorem coe_extMapEquiv [CompactSpace E₁] [T2Space E₂] (hp₁ : Surjective p₁)
    (hψi : Injective ψ) : ⇑(extMapEquiv hcen hψ hcomp hN hψc hp₁ hψi) = extMap hcen hψ hcomp :=
  rfl

end Topology

end extMap

end CurvesJacobian.Cusp
