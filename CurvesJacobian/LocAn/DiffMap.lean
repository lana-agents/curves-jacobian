/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-!
# The group-theoretic difference map `P ×_Γ P → T ⋊ Γ` (MR7 Route T′, step 5)

Route T′ of the MR7 plan (`MR7-plan.md`, R-D3 step 5, reviewed 2026-10-18) computes `π₁` of the
difference morphism `J¹ × J¹ → J`, `(a, b) ↦ a − b`, group-theoretically. Let `π : P → Γ` be a
surjective homomorphism with **abelian** kernel `T` (for `P = Π_{J¹}`, `T = T_p J`). Then:

* `Γ` acts on `T` by conjugation through any lift (`conjHom`), which gives `T ⋊ Γ`;
* **`CurvesJacobian.LocAn.DiffMap.diff : P ×_Γ P →* T ⋊ Γ`**, `(u, v) ↦ (u v⁻¹, π u)`, is a
  homomorphism;
* `diff_left_one`: `(t, 1) ↦ (t, 1)`; `diff_diag`: `(u, u) ↦ (1, π u)` (the diagonal goes to the
  zero section); `fiberProd_eq_mul`: every element of `P ×_Γ P` is a product of an element of
  `T × 1` and a diagonal element;
* **`diff_map`**: functoriality for an isomorphism `α : P ≃* P'` over `Γ`: the `T`-component of
  `diff' (α u, α v)` is `α (u v⁻¹)` and the `Γ`-components agree.

Together with the geometric facts that translations act trivially on `T_pJ` and that the
difference morphism is constant on the diagonal, this identifies `π₁` of the difference
morphism with `diff` up to `T`-conjugation (R-D3 step 5).
-/

namespace CurvesJacobian.LocAn.DiffMap

variable {P Γ : Type*} [Group P] [Group Γ] {π : P →* Γ}

theorem conj_mem_ker (p : P) {t : P} (ht : t ∈ π.ker) : p * t * p⁻¹ ∈ π.ker := by
  rw [MonoidHom.mem_ker] at ht ⊢
  rw [map_mul, map_mul, ht, mul_one, map_inv, mul_inv_cancel]

theorem mul_inv_mem_ker {u v : P} (h : π u = π v) : u * v⁻¹ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

/-- Conjugation of an abelian kernel only depends on the image in `Γ`. -/
theorem conj_eq_of_eq (hab : ∀ a b : π.ker, a * b = b * a) {p q : P} (h : π p = π q) {t : P}
    (ht : t ∈ π.ker) : p * t * p⁻¹ = q * t * q⁻¹ := by
  have hq : q⁻¹ * p ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc := congrArg Subtype.val (hab ⟨q⁻¹ * p, hq⟩ ⟨t, ht⟩)
  simp only [Subgroup.coe_mul] at hc
  calc p * t * p⁻¹ = q * (q⁻¹ * p * t) * p⁻¹ := by group
    _ = q * (t * (q⁻¹ * p)) * p⁻¹ := by rw [hc]
    _ = q * t * q⁻¹ := by group

/-- Conjugation by `p`, as an automorphism of `ker π`. -/
def conjKer (p : P) : π.ker ≃* π.ker where
  toFun t := ⟨p * t * p⁻¹, conj_mem_ker p t.2⟩
  invFun t := ⟨p⁻¹ * t * p, by simpa using conj_mem_ker p⁻¹ t.2⟩
  left_inv t := Subtype.ext (by simp only; group)
  right_inv t := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp]
theorem coe_conjKer (p : P) (t : π.ker) : (conjKer p t : P) = p * t * p⁻¹ := rfl

variable (hab : ∀ a b : π.ker, a * b = b * a) (hπ : Function.Surjective π)

/-- **The action of `Γ` on the abelian kernel** by conjugation through any lift. -/
noncomputable def conjHom : Γ →* MulAut π.ker where
  toFun γ := conjKer (Function.surjInv hπ γ)
  map_one' := by
    ext t
    rw [coe_conjKer, conj_eq_of_eq hab (q := 1) (by rw [Function.surjInv_eq hπ, map_one]) t.2]
    simp
  map_mul' γ γ' := by
    ext t
    change _ = ((conjKer (Function.surjInv hπ γ') t : π.ker) |> conjKer (Function.surjInv hπ γ) :
      π.ker).1
    rw [coe_conjKer, coe_conjKer, coe_conjKer,
      conj_eq_of_eq hab (q := Function.surjInv hπ γ * Function.surjInv hπ γ')
        (by
          rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ]) t.2]
    group

theorem conjHom_apply {γ : Γ} {p : P} (hp : π p = γ) (t : π.ker) :
    (conjHom hab hπ γ t : P) = p * t * p⁻¹ :=
  conj_eq_of_eq hab (by rw [Function.surjInv_eq hπ, hp]) t.2

/-- The fibre product `P ×_Γ P = {(u, v) | π u = π v}`. -/
def fiberProd (π : P →* Γ) : Subgroup (P × P) :=
  MonoidHom.eqLocus (π.comp (MonoidHom.fst P P)) (π.comp (MonoidHom.snd P P))

theorem mem_fiberProd {x : P × P} : x ∈ fiberProd π ↔ π x.1 = π x.2 := Iff.rfl

/-- **The difference map** `P ×_Γ P → T ⋊ Γ`, `(u, v) ↦ (u v⁻¹, π u)`. -/
noncomputable def diff : fiberProd π →* SemidirectProduct π.ker Γ (conjHom hab hπ) where
  toFun x := ⟨⟨x.1.1 * x.1.2⁻¹, mul_inv_mem_ker x.2⟩, π x.1.1⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ ?_
    · exact Subtype.ext (by simp)
    · simp
  map_mul' x y := by
    refine SemidirectProduct.ext ?_ ?_
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, SemidirectProduct.mul_left,
        Subgroup.coe_mul]
      rw [conjHom_apply hab hπ (p := x.1.2) (mem_fiberProd.1 x.2).symm]
      group
    · simp

@[simp]
theorem diff_left (x : fiberProd π) : ((diff hab hπ x).left : P) = x.1.1 * x.1.2⁻¹ := rfl

@[simp]
theorem diff_right (x : fiberProd π) : (diff hab hπ x).right = π x.1.1 := rfl

/-- `(t, 1) ↦ (t, 1)` for `t ∈ T`. -/
theorem diff_left_one {t : P} (ht : t ∈ π.ker) :
    diff hab hπ ⟨(t, 1), by rw [mem_fiberProd, ht, map_one]⟩ =
      SemidirectProduct.inl ⟨t, ht⟩ := by
  refine SemidirectProduct.ext (Subtype.ext ?_) ?_
  · simp
  · simpa using ht

/-- The diagonal goes to the zero section: `(u, u) ↦ (1, π u)`. -/
theorem diff_diag (u : P) :
    diff hab hπ ⟨(u, u), rfl⟩ = SemidirectProduct.inr (π u) := by
  refine SemidirectProduct.ext (Subtype.ext ?_) ?_
  · simp
  · simp

/-- `P ×_Γ P` is generated by `T × 1` and the diagonal: `(u, v) = (u v⁻¹, 1) · (v, v)`. -/
theorem fiberProd_eq_mul (x : fiberProd π) :
    (x : P × P) = (x.1.1 * x.1.2⁻¹, 1) * (x.1.2, x.1.2) := by
  ext <;> simp

/-- **Functoriality**: for `α : P ≃* P'` over `Γ`, `diff' (α u, α v)` has `T`-component
`α (u v⁻¹)` and the same `Γ`-component as `diff (u, v)`. -/
theorem diff_map {P' : Type*} [Group P'] {π' : P' →* Γ}
    (hab' : ∀ a b : π'.ker, a * b = b * a) (hπ' : Function.Surjective π') (α : P ≃* P')
    (hα : ∀ p, π' (α p) = π p) (x : fiberProd π) :
    ((diff hab' hπ' ⟨(α x.1.1, α x.1.2), by rw [mem_fiberProd, hα, hα]; exact x.2⟩).left : P') =
        α ((diff hab hπ x).left : P) ∧
      (diff hab' hπ' ⟨(α x.1.1, α x.1.2), by rw [mem_fiberProd, hα, hα]; exact x.2⟩).right =
        (diff hab hπ x).right := by
  refine ⟨?_, ?_⟩
  · simp [map_mul, map_inv]
  · simp [hα]

end CurvesJacobian.LocAn.DiffMap
