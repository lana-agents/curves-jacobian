/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.EigenH2

/-!
# Transport of symmetric rigidified classes along `Φ : T₁ ⋊ G ≃ T₂ ⋊ G` (MR7 Route T′, step 4)

Route T′ (`MR7-plan.md` R-D3, steps 3–4; reviewed 2026-10-18) compares the Chern classes
`c(L_i) ∈ H²(T_i ⋊ Γ_K, μ_{pⁿ})` of the symmetric rigidified ample bundles `L_i` on the Jacobians
`J_i` along `Φ = α_T ⋊ id : T₁ ⋊ Γ_K ≃ T₂ ⋊ Γ_K`. Two properties hold:
* `ι^* c(L_i) = c(L_i)` and `ε^* c(L_i) = 0`;
* `Φ` commutes with `π`, `ε` and `ι`.

So, **once the restrictions to `T₁` agree up to the scalar `λ`** (`res_T Φ^* c(L₂) = λ·res_T c(L₁)`,
the geometric inputs P5/P6 of the plan), the class `Φ^* c(L₂) − λ·c(L₁)` satisfies the
hypotheses of the eigenspace lemma (`EigenH2.sq_eq_one`), hence it is `2`-torsion.

This file proves that group-theoretic step. It also gives the elementary functoriality of
`ContH2.map` needed for it.

## Main results

* `CurvesJacobian.LocAn.TransportH2.map_map`, `map_congr`: functoriality of `ContH2.map` in the
  group variable (identity on coefficients);
* **`CurvesJacobian.LocAn.TransportH2.sq_eq_one_of_transport`**: with `x = Φ^* c₂ / c₁^λ`,
  `res_T x = 1 ⇒ x² = 1`.
-/

open groupCohomology ContH2

namespace CurvesJacobian.LocAn.TransportH2

section Functoriality

variable {G G' G'' M : Type*} [Group G] [Group G'] [Group G''] [TopologicalSpace G]
  [TopologicalSpace G'] [TopologicalSpace G''] [CommGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction G' M] [MulDistribMulAction G'' M]

/-- `ContH2.map` (identity on coefficients) is functorial in the group: `φ'^* φ^* = (φ ∘ φ')^*`. -/
theorem map_map (φ : G' →* G) (hφ : Continuous φ) (h : ∀ (g : G') (m : M), φ g • m = g • m)
    (φ' : G'' →* G') (hφ' : Continuous φ') (h' : ∀ (g : G'') (m : M), φ' g • m = g • m)
    (x : ContH2 G M) :
    ContH2.map φ' hφ' (MonoidHom.id M) (fun g m ↦ h' g m)
        (ContH2.map φ hφ (MonoidHom.id M) (fun g m ↦ h g m) x) =
      ContH2.map (φ.comp φ') (hφ.comp hφ') (MonoidHom.id M)
        (fun g m ↦ (h (φ' g) m).trans (h' g m)) x := by
  induction x using ContH2.induction_on with
  | h c =>
    simp only [ContH2.map_mk]
    congr 1

/-- `ContH2.map` depends only on the underlying function of the group homomorphism. -/
theorem map_congr (φ φ' : G' →* G) (hφ : Continuous φ) (hφ' : Continuous φ')
    (h : ∀ (g : G') (m : M), φ g • m = g • m) (h' : ∀ (g : G') (m : M), φ' g • m = g • m)
    (he : ∀ g, φ g = φ' g) (x : ContH2 G M) :
    ContH2.map φ hφ (MonoidHom.id M) (fun g m ↦ h g m) x =
      ContH2.map φ' hφ' (MonoidHom.id M) (fun g m ↦ h' g m) x := by
  obtain rfl : φ = φ' := MonoidHom.ext he
  rfl

end Functoriality

section Transport

variable {E₁ E₂ G M : Type*} [Group E₁] [Group E₂] [Group G] [CommGroup M]
  [TopologicalSpace E₁] [IsTopologicalGroup E₁] [TopologicalSpace E₂] [IsTopologicalGroup E₂]
  [TopologicalSpace G] [MulDistribMulAction G M] [MulDistribMulAction E₁ M]
  [MulDistribMulAction E₂ M]

omit [IsTopologicalGroup E₂] in
/-- **Route T′, step 4 (group side).** Let `π_i : E_i → G` be split by `ε_i`, with `E_i` acting on
`M` through `π_i`. Let `ι_i` be endomorphisms with `ι_i ∘ ε_i = ε_i` and `ι_i(t) = t⁻¹` on
`T_i = ker π_i`. Let `Φ : E₁ → E₂` be continuous with `π₂ ∘ Φ = π₁`, `Φ ∘ ε₁ = ε₂` and
`Φ ∘ ι₁ = ι₂ ∘ Φ`. Suppose `c_i ∈ H²(E_i, M)` satisfy `ε_i^* c_i = 1` and `ι_i^* c_i = c_i`. If
`Φ^* c₂` and `c₁^λ` have the same restriction to `T₁`, then `(Φ^* c₂ / c₁^λ)² = 1`.

For `E_i = T_pJ_i ⋊ Γ_K`, `M = μ_{pⁿ}`, `c_i = c(L_i)` this is `2(Φ^* c(L₂) − λ c(L₁)) = 0`
in `H²(T₁ ⋊ Γ_K, μ_{pⁿ})`. -/
theorem sq_eq_one_of_transport
    {π₁ : E₁ →* G} {ε₁ : G →* E₁} (hπ₁ : Continuous π₁) (hε₁ : Continuous ε₁)
    (hπε₁ : ∀ g, π₁ (ε₁ g) = g) (hact₁ : ∀ (e : E₁) (m : M), e • m = π₁ e • m)
    {ι₁ : E₁ →* E₁} (hι₁ : Continuous ι₁) (hιε₁ : ∀ g, ι₁ (ε₁ g) = ε₁ g)
    (hιT₁ : ∀ t, π₁ t = 1 → ι₁ t = t⁻¹)
    {π₂ : E₂ →* G} {ε₂ : G →* E₂} (hε₂ : Continuous ε₂)
    (hπε₂ : ∀ g, π₂ (ε₂ g) = g) (hact₂ : ∀ (e : E₂) (m : M), e • m = π₂ e • m)
    {ι₂ : E₂ →* E₂} (hι₂ : Continuous ι₂)
    (hιε₂ : ∀ g, ι₂ (ε₂ g) = ε₂ g) (hιT₂ : ∀ t, π₂ t = 1 → ι₂ t = t⁻¹)
    {Φ : E₁ →* E₂} (hΦ : Continuous Φ) (hΦπ : ∀ e, π₂ (Φ e) = π₁ e)
    (hΦε : ∀ g, Φ (ε₁ g) = ε₂ g) (hΦι : ∀ e, Φ (ι₁ e) = ι₂ (Φ e))
    (c₁ : ContH2 E₁ M) (c₂ : ContH2 E₂ M)
    (hc₁ε : ContH2.map ε₁ hε₁ (MonoidHom.id M)
      (fun g m ↦ by rw [MonoidHom.id_apply, MonoidHom.id_apply, hact₁, hπε₁]) c₁ = 1)
    (hc₂ε : ContH2.map ε₂ hε₂ (MonoidHom.id M)
      (fun g m ↦ by rw [MonoidHom.id_apply, MonoidHom.id_apply, hact₂, hπε₂]) c₂ = 1)
    (hc₁ι : ContH2.map ι₁ hι₁ (MonoidHom.id M)
      (fun e m ↦ EigenH2.smul_ι hπε₁ (fun e he m ↦ by rw [hact₁, he, one_smul]) ι₁ hιε₁ hιT₁
        e m) c₁ = c₁)
    (hc₂ι : ContH2.map ι₂ hι₂ (MonoidHom.id M)
      (fun e m ↦ EigenH2.smul_ι hπε₂ (fun e he m ↦ by rw [hact₂, he, one_smul]) ι₂ hιε₂ hιT₂
        e m) c₂ = c₂)
    (n : ℤ)
    (hT : ContH2.map π₁.ker.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ ↦ rfl)
        (ContH2.map Φ hΦ (MonoidHom.id M)
          (fun e m ↦ by rw [MonoidHom.id_apply, MonoidHom.id_apply, hact₂, hact₁, hΦπ]) c₂) =
      ContH2.map π₁.ker.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ ↦ rfl)
        (c₁ ^ n)) :
    (ContH2.map Φ hΦ (MonoidHom.id M)
        (fun e m ↦ by rw [MonoidHom.id_apply, MonoidHom.id_apply, hact₂, hact₁, hΦπ]) c₂ /
      c₁ ^ n) ^ 2 = 1 := by
  have hΦa : ∀ (e : E₁) (m : M), Φ e • m = e • m := fun e m ↦ by rw [hact₂, hact₁, hΦπ]
  set Φs := ContH2.map Φ hΦ (MonoidHom.id M) (fun e m ↦ hΦa e m) with hΦs
  refine EigenH2.sq_eq_one hπ₁ hε₁ hπε₁ hact₁ ι₁ hι₁ hιε₁ hιT₁ _ ?_ ?_ ?_
  · rw [map_div, hT, div_self']
  · rw [map_div, map_zpow, hc₁ε, one_zpow, div_one, hΦs, map_map]
    rw [map_congr _ ε₂ _ hε₂ _ (fun g m ↦ by rw [hact₂, hπε₂]) hΦε]
    exact hc₂ε
  · rw [map_div, map_zpow, hc₁ι, hΦs, map_map]
    rw [map_congr _ (ι₂.comp Φ) _ (hι₂.comp hΦ) _
      (fun e m ↦ by
        rw [MonoidHom.comp_apply, hact₂, hact₁]
        rw [← hΦπ e]
        have := EigenH2.smul_ι hπε₂ (fun e he m ↦ by rw [hact₂, he, one_smul]) ι₂ hιε₂ hιT₂
          (Φ e) m
        rw [hact₂, hact₂] at this
        exact this) hΦι]
    rw [← map_map ι₂ hι₂
      (fun e m ↦ EigenH2.smul_ι hπε₂ (fun e he m ↦ by rw [hact₂, he, one_smul]) ι₂ hιε₂ hιT₂ e m)
      Φ hΦ hΦa, hc₂ι]

end Transport

end CurvesJacobian.LocAn.TransportH2
