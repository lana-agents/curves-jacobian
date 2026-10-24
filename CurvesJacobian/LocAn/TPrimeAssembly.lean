/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThetaClass
import CurvesJacobian.LocAn.TransportH2

/-!
# Assembly of Route T′ from the theta-pullback identity (★) and the Weil-pairing transport (P6)

Route T′ of the MR7 plan (`MR7-plan.md` R-D3; lead decision 2026-10-23 "D-d interface ADOPTED")
consumes the Jacobian only through two curve-level statements, both proved on the Jacobian track
(`JAC-plan.md` D-d):

* **(★)** `c^{ar}(P_σ) = π_σ^* θ_b` in `H²(Π_X, μ_n)`, where `π_σ : Π_X → (Δ_X^{ab}/n) ⋊ G_K` is
  the group-theoretic map `u ↦ D(u, σ̃ u σ̃⁻¹)` (`DiffMap.diff`), `θ_b` is the Heisenberg class
  (`ThetaClass.thetaClass`) of `b = halfForm (e^{±2})`, and `e` is the Weil pairing on `Δ_X^{ab}/n`;
* **(P6)** the transport `Φ = α_T ⋊ id` of `α : Π_{X₁} ≃ Π_{X₂}` multiplies the Weil pairing by
  the unit `λ` by which `α` acts on `H²(Δ_X, μ_n)`.

This file proves the **group-theoretic assembly**: given the two statements, the classes of the
divisors `P_{σ_i}` correspond under `α` up to the scalar `λ`:

  `α^* c^{ar}(P_{σ₂}) = α^* π_{σ₂}^* θ_{b₂} = π_{σ₁}^* Φ^* θ_{b₂} = π_{σ₁}^* θ_{b₁^λ}
    = c^{ar}(P_{σ₁})^λ`.

The compatibility `Φ ∘ π_{σ₁} = π_{σ₂} ∘ α` holds in general only up to conjugation by an element
of `T₂` (R-D3 step 5: `π₁(d) = c_s ∘ D`). Such conjugations act trivially on `H²` with coefficients
on which they act trivially (`map_conj_eq`), so the assembly also holds in that form
(`map_pullback_thetaClass_of_conj`).

No geometry enters here. The two inputs are the explicit hypotheses `hstar₁`, `hstar₂` (the
identity (★) for both curves) and `hP6` of `tprime_of_star_P6`. They are recorded as debts (★),
(P6) in `MR7-plan.md` and become theorems when the Jacobian track proves them.

## Main results

* `CurvesJacobian.LocAn.TPrime.map_conj_eq`: inner automorphisms by elements acting trivially on
  `M` act trivially on `ContH2`;
* `CurvesJacobian.LocAn.TPrime.thetaClass_comp_eq_pow`: `θ_{b₂ ∘ Φ} = θ_{b₁}^λ` when
  `b₂ ∘ (Φ × Φ) = b₁^λ` on `T₁`;
* **`CurvesJacobian.LocAn.TPrime.map_pullback_thetaClass`**: `α^* p₂^* θ_{b₂} = (p₁^* θ_{b₁})^λ`
  for `Φ ∘ p₁ = p₂ ∘ α`; `map_pullback_thetaClass_of_conj` up to `T₂`-conjugation;
* **`CurvesJacobian.LocAn.TPrime.tprime_of_star_P6`**: Route T′ (Claim T′ of R-D3, mod `n`): from
  (★) for both curves and (P6), `α^* c₂ = c₁^λ`.
-/

open groupCohomology ContH2

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.TPrime

open ThetaClass EigenH2 TransportH2

/-! ### Inner automorphisms act trivially -/

section Inner

variable {P M : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CommGroup M]
  [MulDistribMulAction P M]

/-- Conjugation `x ↦ g⁻¹ x g`. -/
def conjHom (g : P) : P →* P := (MulAut.conj g⁻¹).toMonoidHom

theorem conjHom_apply (g x : P) : conjHom g x = g⁻¹ * x * g := by
  simp [conjHom]

theorem continuous_conjHom (g : P) : Continuous (conjHom g) := by
  have : (conjHom g : P → P) = fun x ↦ g⁻¹ * x * g := funext (conjHom_apply g)
  rw [this]
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem smul_conjHom {g : P} (hg : ∀ m : M, g • m = m) (x : P) (m : M) :
    conjHom g x • m = x • m := by
  have hg' : ∀ m : M, g⁻¹ • m = m := fun m ↦ by
    conv_lhs => rw [← hg m]
    rw [inv_smul_smul]
  rw [conjHom_apply, mul_smul, mul_smul, hg, hg']

/-- The cocycle identity behind `map_conj_eq` (the same identity as LCFT's `ContH2.cor_res_aux`,
whose module cj does not import). -/
theorem conj_aux {E : P × P → M} (hE : IsMulCocycle₂ E) (a g h B U : P) :
    a • E (a⁻¹ * g * B, B⁻¹ * h * U) =
      E (g, h) * (g • (E (B, B⁻¹ * h * U) / E (h, U)) /
        (E (a, a⁻¹ * (g * h) * U) / E (g * h, U)) * (E (a, a⁻¹ * g * B) / E (g, B))) := by
  have h1 := hE a (a⁻¹ * g * B) (B⁻¹ * h * U)
  rw [show a * (a⁻¹ * g * B) = g * B by group,
    show a⁻¹ * g * B * (B⁻¹ * h * U) = a⁻¹ * (g * h) * U by group] at h1
  have h2 := hE g B (B⁻¹ * h * U)
  rw [show B * (B⁻¹ * h * U) = h * U by group] at h2
  have h3 := hE g h U
  have e1 : a • E (a⁻¹ * g * B, B⁻¹ * h * U) =
      E (g * B, B⁻¹ * h * U) * E (a, a⁻¹ * g * B) / E (a, a⁻¹ * (g * h) * U) := by
    rw [h1]; mul_abel
  have e2 : E (g * B, B⁻¹ * h * U) = g • E (B, B⁻¹ * h * U) * E (g, h * U) / E (g, B) := by
    rw [← h2]; mul_abel
  have e3 : E (g, h * U) = E (g * h, U) * E (g, h) / g • E (h, U) := by
    rw [h3]; mul_abel
  rw [e1, e2, e3, smul_div']
  mul_abel

/-- **Inner automorphisms act trivially on `H²`**: if `g` acts trivially on `M`, then
`(x ↦ g⁻¹ x g)^*` is the identity of `ContH2 P M`. The homotopy is
`f(x) = c(g, g⁻¹ x g) / c(x, g)` (as in LCFT's `conj_res`). -/
theorem map_conj_eq {g : P} (hg : ∀ m : M, g • m = m) (x : ContH2 P M) :
    ContH2.map (conjHom g) (continuous_conjHom g) (MonoidHom.id M)
      (fun u m ↦ smul_conjHom hg u m) x = x := by
  induction x using ContH2.induction_on with
  | h f =>
  rw [map_mk, mk_eq_mk_iff]
  refine ⟨fun x : P ↦ f (g, g⁻¹ * x * g) / f (x, g), ?_, ?_⟩
  · exact ((isLocallyConstant f).comp_continuous (continuous_const.prodMk
      ((continuous_const.mul continuous_id).mul continuous_const))).div
      ((isLocallyConstant f).comp_continuous (continuous_id.prodMk continuous_const))
  · funext ab
    obtain ⟨a, b⟩ := ab
    have key := conj_aux (isMulCocycle₂ f) g a b g g
    rw [hg] at key
    change a • (f (g, g⁻¹ * b * g) / f (b, g)) / (f (g, g⁻¹ * (a * b) * g) / f (a * b, g)) *
        (f (g, g⁻¹ * a * g) / f (a, g)) =
      f (conjHom g a, conjHom g b) / f (a, b)
    rw [conjHom_apply, conjHom_apply, key]
    mul_abel

end Inner

/-! ### The assembly -/

section Assembly

variable {P₁ P₂ E₁ E₂ G M : Type*} [Group P₁] [Group P₂] [Group E₁] [Group E₂] [Group G]
  [CommGroup M] [TopologicalSpace P₁] [TopologicalSpace P₂] [TopologicalSpace E₁]
  [IsTopologicalGroup E₁] [TopologicalSpace E₂] [IsTopologicalGroup E₂] [TopologicalSpace G]
  [MulDistribMulAction P₁ M] [MulDistribMulAction P₂ M] [MulDistribMulAction E₁ M]
  [MulDistribMulAction E₂ M]
  {π₁ : E₁ →* G} {ε₁ : G →* E₁} (hπ₁ : Continuous π₁) (hε₁ : Continuous ε₁)
  (hπε₁ : ∀ g, π₁ (ε₁ g) = g) (hab₁ : ∀ a b : E₁, π₁ a = 1 → π₁ b = 1 → a * b = b * a)
  {π₂ : E₂ →* G} {ε₂ : G →* E₂} (hπ₂ : Continuous π₂) (hε₂ : Continuous ε₂)
  (hπε₂ : ∀ g, π₂ (ε₂ g) = g) (hab₂ : ∀ a b : E₂, π₂ a = 1 → π₂ b = 1 → a * b = b * a)

/-- The pulled-back form `b₂ ∘ (Φ × Φ)` is bilinear on `T₁`. -/
theorem isBilin_comp {Φ : E₁ →* E₂} (hΦπ : ∀ e, π₂ (Φ e) = π₁ e) {b₂ : E₂ → E₂ → M}
    (hb₂ : IsBilin π₂ b₂) : IsBilin π₁ fun t s ↦ b₂ (Φ t) (Φ s) :=
  ⟨fun t t' s ht ht' hs ↦ by
      simp only [map_mul]
      exact hb₂.mul_left _ _ _ (by rw [hΦπ, ht]) (by rw [hΦπ, ht']) (by rw [hΦπ, hs]),
    fun t s s' ht hs hs' ↦ by
      simp only [map_mul]
      exact hb₂.mul_right _ _ _ (by rw [hΦπ, ht]) (by rw [hΦπ, hs]) (by rw [hΦπ, hs'])⟩

/-- The pulled-back form `b₂ ∘ (Φ × Φ)` is equivariant. -/
theorem isEquivar_comp {Φ : E₁ →* E₂} (hΦπ : ∀ e, π₂ (Φ e) = π₁ e)
    (hΦa : ∀ (e : E₁) (m : M), Φ e • m = e • m) {b₂ : E₂ → E₂ → M}
    (hequiv₂ : IsEquivar π₂ b₂) : IsEquivar π₁ fun t s ↦ b₂ (Φ t) (Φ s) := by
  intro e t s ht hs
  simp only [map_mul, map_inv]
  rw [← hΦa, hequiv₂ (Φ e) _ _ (by rw [hΦπ, ht]) (by rw [hΦπ, hs])]

/-- **`θ_{b₂ ∘ Φ} = θ_{b₁}^λ`** if `b₂ ∘ (Φ × Φ) = b₁^λ` on `T₁ × T₁`: the theta cochain only
evaluates its form on `T`. -/
theorem thetaClass_comp_eq_pow {Φ : E₁ →* E₂} (hΦ : Continuous Φ)
    (hΦπ : ∀ e, π₂ (Φ e) = π₁ e) (hΦa : ∀ (e : E₁) (m : M), Φ e • m = e • m)
    {b₁ : E₁ → E₁ → M} (hb₁ : IsBilin π₁ b₁) (hequiv₁ : IsEquivar π₁ b₁)
    (hlc₁ : IsLocallyConstant fun p : E₁ × E₁ ↦ b₁ p.1 p.2)
    {b₂ : E₂ → E₂ → M} (hb₂ : IsBilin π₂ b₂) (hequiv₂ : IsEquivar π₂ b₂)
    (hlc₂ : IsLocallyConstant fun p : E₂ × E₂ ↦ b₂ p.1 p.2) (m : ℕ)
    (hb : ∀ t s, π₁ t = 1 → π₁ s = 1 → b₂ (Φ t) (Φ s) = b₁ t s ^ m) :
    thetaClass hπ₁ hε₁ hπε₁ hab₁ (isBilin_comp hΦπ hb₂) (isEquivar_comp hΦπ hΦa hequiv₂)
        (hlc₂.comp_continuous (hΦ.prodMap hΦ)) =
      thetaClass hπ₁ hε₁ hπε₁ hab₁ hb₁ hequiv₁ hlc₁ ^ m := by
  rw [thetaClass, thetaClass, ← map_pow]
  congr 1
  refine cocycles_ext fun e e' ↦ ?_
  change thetaFun π₁ ε₁ (fun t s ↦ b₂ (Φ t) (Φ s)) (e, e') = thetaFun π₁ ε₁ b₁ (e, e') ^ m
  exact hb _ _ (π_tpart hπε₁ e) (π_cnj_of_ker hπε₁ e (π_tpart hπε₁ e'))

/-- **Route T′, assembly (exact compatibility).** Let `p_i : P_i → E_i` be continuous maps from
the (arithmetic) fundamental groups to the split extensions `E_i = T_i ⋊ G`, `α : P₁ → P₂`, and
`Φ : E₁ → E₂` a morphism of split extensions over `G` with `Φ ∘ p₁ = p₂ ∘ α`. If
`b₂ ∘ (Φ × Φ) = b₁^λ` on `T₁`, then `α^* p₂^* θ_{b₂} = (p₁^* θ_{b₁})^λ`. -/
theorem map_pullback_thetaClass
    {p₁ : P₁ →* E₁} (hp₁ : Continuous p₁) (hp₁a : ∀ (u : P₁) (m : M), p₁ u • m = u • m)
    {p₂ : P₂ →* E₂} (hp₂ : Continuous p₂) (hp₂a : ∀ (u : P₂) (m : M), p₂ u • m = u • m)
    {α : P₁ →* P₂} (hα : Continuous α) (hαa : ∀ (u : P₁) (m : M), α u • m = u • m)
    {Φ : E₁ →* E₂} (hΦ : Continuous Φ) (hΦπ : ∀ e, π₂ (Φ e) = π₁ e)
    (hΦε : ∀ g, Φ (ε₁ g) = ε₂ g) (hΦa : ∀ (e : E₁) (m : M), Φ e • m = e • m)
    (hcomm : ∀ u, Φ (p₁ u) = p₂ (α u))
    {b₁ : E₁ → E₁ → M} (hb₁ : IsBilin π₁ b₁) (hequiv₁ : IsEquivar π₁ b₁)
    (hlc₁ : IsLocallyConstant fun p : E₁ × E₁ ↦ b₁ p.1 p.2)
    {b₂ : E₂ → E₂ → M} (hb₂ : IsBilin π₂ b₂) (hequiv₂ : IsEquivar π₂ b₂)
    (hlc₂ : IsLocallyConstant fun p : E₂ × E₂ ↦ b₂ p.1 p.2) (m : ℕ)
    (hb : ∀ t s, π₁ t = 1 → π₁ s = 1 → b₂ (Φ t) (Φ s) = b₁ t s ^ m) :
    ContH2.map α hα (MonoidHom.id M) (fun u x ↦ hαa u x)
        (ContH2.map p₂ hp₂ (MonoidHom.id M) (fun u x ↦ hp₂a u x)
          (thetaClass hπ₂ hε₂ hπε₂ hab₂ hb₂ hequiv₂ hlc₂)) =
      ContH2.map p₁ hp₁ (MonoidHom.id M) (fun u x ↦ hp₁a u x)
          (thetaClass hπ₁ hε₁ hπε₁ hab₁ hb₁ hequiv₁ hlc₁) ^ m := by
  rw [map_map, map_congr _ (Φ.comp p₁) _ (hΦ.comp hp₁) _
      (fun u x ↦ (hΦa (p₁ u) x).trans (hp₁a u x)) (fun u ↦ (hcomm u).symm),
    ← map_map Φ hΦ hΦa p₁ hp₁ hp₁a,
    map_thetaClass hπ₂ hε₂ hπε₂ hab₂ hπ₁ hε₁ hπε₁ hab₁ Φ hΦ hΦπ hΦε hΦa hb₂ hequiv₂ hlc₂
      (isBilin_comp hΦπ hb₂) (isEquivar_comp hΦπ hΦa hequiv₂)
      (hlc₂.comp_continuous (hΦ.prodMap hΦ)),
    thetaClass_comp_eq_pow hπ₁ hε₁ hπε₁ hab₁ hΦ hΦπ hΦa hb₁ hequiv₁ hlc₁ hb₂ hequiv₂ hlc₂ m hb,
    map_pow]

/-- **Route T′, assembly up to `T₂`-conjugation** (the form R-D3 step 5 provides:
`π₁(d) = c_s ∘ D`): if `Φ ∘ p₁ = δ (p₂ ∘ α) δ⁻¹` for some `δ ∈ T₂`, the conclusion of
`map_pullback_thetaClass` still holds (provided `E₂` acts on `M` through `π₂`). -/
theorem map_pullback_thetaClass_of_conj [MulDistribMulAction G M]
    (hact₂ : ∀ (e : E₂) (x : M), e • x = π₂ e • x)
    {p₁ : P₁ →* E₁} (hp₁ : Continuous p₁) (hp₁a : ∀ (u : P₁) (m : M), p₁ u • m = u • m)
    {p₂ : P₂ →* E₂} (hp₂ : Continuous p₂) (hp₂a : ∀ (u : P₂) (m : M), p₂ u • m = u • m)
    {α : P₁ →* P₂} (hα : Continuous α) (hαa : ∀ (u : P₁) (m : M), α u • m = u • m)
    {Φ : E₁ →* E₂} (hΦ : Continuous Φ) (hΦπ : ∀ e, π₂ (Φ e) = π₁ e)
    (hΦε : ∀ g, Φ (ε₁ g) = ε₂ g) (hΦa : ∀ (e : E₁) (m : M), Φ e • m = e • m)
    {δ : E₂} (hδ : π₂ δ = 1) (hcomm : ∀ u, Φ (p₁ u) = δ * p₂ (α u) * δ⁻¹)
    {b₁ : E₁ → E₁ → M} (hb₁ : IsBilin π₁ b₁) (hequiv₁ : IsEquivar π₁ b₁)
    (hlc₁ : IsLocallyConstant fun p : E₁ × E₁ ↦ b₁ p.1 p.2)
    {b₂ : E₂ → E₂ → M} (hb₂ : IsBilin π₂ b₂) (hequiv₂ : IsEquivar π₂ b₂)
    (hlc₂ : IsLocallyConstant fun p : E₂ × E₂ ↦ b₂ p.1 p.2) (m : ℕ)
    (hb : ∀ t s, π₁ t = 1 → π₁ s = 1 → b₂ (Φ t) (Φ s) = b₁ t s ^ m) :
    ContH2.map α hα (MonoidHom.id M) (fun u x ↦ hαa u x)
        (ContH2.map p₂ hp₂ (MonoidHom.id M) (fun u x ↦ hp₂a u x)
          (thetaClass hπ₂ hε₂ hπε₂ hab₂ hb₂ hequiv₂ hlc₂)) =
      ContH2.map p₁ hp₁ (MonoidHom.id M) (fun u x ↦ hp₁a u x)
          (thetaClass hπ₁ hε₁ hπε₁ hab₁ hb₁ hequiv₁ hlc₁) ^ m := by
  have hδa : ∀ x : M, δ⁻¹ • x = x := fun x ↦ by rw [hact₂, map_inv, hδ, inv_one, one_smul]
  have hc := map_conj_eq hδa (thetaClass hπ₂ hε₂ hπε₂ hab₂ hb₂ hequiv₂ hlc₂)
  have hca : ∀ (u : P₂) (x : M), (conjHom (P := E₂) δ⁻¹).comp p₂ u • x = u • x := fun u x ↦
    (smul_conjHom hδa (p₂ u) x).trans (hp₂a u x)
  have key := map_pullback_thetaClass hπ₁ hε₁ hπε₁ hab₁ hπ₂ hε₂ hπε₂ hab₂ hp₁ hp₁a
    (by rw [MonoidHom.coe_comp]; exact (continuous_conjHom (P := E₂) δ⁻¹).comp hp₂) hca hα hαa
    hΦ hΦπ hΦε hΦa
    (fun u ↦ by rw [hcomm, MonoidHom.comp_apply, conjHom_apply, inv_inv]) hb₁ hequiv₁ hlc₁
    hb₂ hequiv₂ hlc₂ m hb
  rw [← key, ← map_map (conjHom (P := E₂) δ⁻¹) (continuous_conjHom (P := E₂) δ⁻¹)
    (fun u x ↦ smul_conjHom hδa u x) p₂ hp₂ hp₂a, hc]

/-- **Route T′ (Claim T′ of R-D3, mod `n`), from (★) and (P6).** Let `e_i` be alternating
equivariant locally constant bilinear forms on `T_i` (the Weil pairings on `Δ_{X_i}^{ab}/n`),
`M` of exponent `2k + 1`, and `b_i = halfForm e_i k`. Suppose
* **(★)** for both curves: `c_i = p_i^* θ_{b_i}` (`hstar₁`, `hstar₂`; `c_i = c^{ar}(P_{σ_i})`,
  `p_i = π_{σ_i}`);
* **(P6)**: `e₂ ∘ (Φ × Φ) = e₁^λ` on `T₁` (`hP6`);
* `Φ ∘ p₁ = δ (p₂ ∘ α) δ⁻¹` with `δ ∈ T₂` (R-D3 step 5).

Then **`α^* c₂ = c₁^λ`**. -/
theorem tprime_of_star_P6 [MulDistribMulAction G M]
    (hact₂ : ∀ (e : E₂) (x : M), e • x = π₂ e • x)
    {p₁ : P₁ →* E₁} (hp₁ : Continuous p₁) (hp₁a : ∀ (u : P₁) (m : M), p₁ u • m = u • m)
    {p₂ : P₂ →* E₂} (hp₂ : Continuous p₂) (hp₂a : ∀ (u : P₂) (m : M), p₂ u • m = u • m)
    {α : P₁ →* P₂} (hα : Continuous α) (hαa : ∀ (u : P₁) (m : M), α u • m = u • m)
    {Φ : E₁ →* E₂} (hΦ : Continuous Φ) (hΦπ : ∀ e, π₂ (Φ e) = π₁ e)
    (hΦε : ∀ g, Φ (ε₁ g) = ε₂ g) (hΦa : ∀ (e : E₁) (m : M), Φ e • m = e • m)
    {δ : E₂} (hδ : π₂ δ = 1) (hcomm : ∀ u, Φ (p₁ u) = δ * p₂ (α u) * δ⁻¹) (k : ℕ)
    {e₁ : E₁ → E₁ → M} (he₁ : IsBilin π₁ e₁) (hequiv₁ : IsEquivar π₁ e₁)
    (hlc₁ : IsLocallyConstant fun p : E₁ × E₁ ↦ e₁ p.1 p.2)
    {e₂ : E₂ → E₂ → M} (he₂ : IsBilin π₂ e₂) (hequiv₂ : IsEquivar π₂ e₂)
    (hlc₂ : IsLocallyConstant fun p : E₂ × E₂ ↦ e₂ p.1 p.2) (m : ℕ)
    (hP6 : ∀ t s, π₁ t = 1 → π₁ s = 1 → e₂ (Φ t) (Φ s) = e₁ t s ^ m)
    (c₁ : ContH2 P₁ M) (c₂ : ContH2 P₂ M)
    (hstar₁ : c₁ = ContH2.map p₁ hp₁ (MonoidHom.id M) (fun u x ↦ hp₁a u x)
      (thetaClass hπ₁ hε₁ hπε₁ hab₁ (he₁.pow (k + 1)) (hequiv₁.pow (k + 1))
        (hlc₁.comp fun x ↦ x ^ (k + 1))))
    (hstar₂ : c₂ = ContH2.map p₂ hp₂ (MonoidHom.id M) (fun u x ↦ hp₂a u x)
      (thetaClass hπ₂ hε₂ hπε₂ hab₂ (he₂.pow (k + 1)) (hequiv₂.pow (k + 1))
        (hlc₂.comp fun x ↦ x ^ (k + 1)))) :
    ContH2.map α hα (MonoidHom.id M) (fun u x ↦ hαa u x) c₂ = c₁ ^ m := by
  rw [hstar₁, hstar₂]
  exact map_pullback_thetaClass_of_conj hπ₁ hε₁ hπε₁ hab₁ hπ₂ hε₂ hπε₂ hab₂ hact₂ hp₁ hp₁a hp₂
    hp₂a hα hαa hΦ hΦπ hΦε hΦa hδ hcomm _ _ _ _ _ _ m
    (fun t s ht hs ↦ by
      rw [hP6 t s ht hs, ← pow_mul, ← pow_mul, mul_comm])

end Assembly

end CurvesJacobian.LocAn.TPrime
