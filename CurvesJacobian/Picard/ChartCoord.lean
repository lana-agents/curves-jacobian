/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.QcohLocal
import CurvesJacobian.Picard.MatSheaf

/-!
# Coordinates of sections of a quasi-coherent module on basic opens

Let `X` be a scheme, `U ⊆ X` an affine open and `L` a quasi-coherent `𝒪_X`-module. Suppose
`ε₁, …, εₙ ∈ Γ(L, U)` and a `Γ(X, U)`-linear map `s : Γ(L, U) → Γ(X, U)ⁿ` with
`Σ s(x)ᵢ εᵢ = x` (a splitting of the presentation `Γ(X, U)ⁿ → Γ(L, U)` given by the `εᵢ`, which
exists when `Γ(L, U)` is finite projective). Then on every basic open `W = D(g) ⊆ U` there is a
`Γ(X, W)`-linear coordinate map `c : Γ(L, W) → Γ(X, W)ⁿ` with `c(m|_W) = s(m)|_W` and
`Σ c(x)ᵢ εᵢ|_W = x` (`CurvesJacobian.ChartCoord.exists_coord`): the localization of `s`
(`Γ(L, D(g)) = Γ(L, U)_g`, `Scheme.Modules.isLocalizedModule_resBasicOpen`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ChartCoord

open Scheme Scheme.Modules ModulesGlue MatSheaf

variable {X : Scheme.{u}} (L : X.Modules) [L.IsQuasicoherent] {U : X.Opens}

/-- **Coordinates on a basic open.** -/
theorem exists_coord (hU : IsAffineOpen U) {n : ℕ} (ε : Fin n → Γ(L, U))
    (s : Γ(L, U) →ₗ[Γ(X, U)] (Fin n → Γ(X, U))) (hs : ∀ x, ∑ i, s x i • ε i = x)
    (g : Γ(X, U)) (W : X.Opens) (hWU : W ≤ U) (hW : W = X.basicOpen g) :
    ∃ c : Γ(L, W) → (Fin n → Γ(X, W)),
      (∀ m, c (rs L hWU m) = rv hWU (s m)) ∧
      (∀ x, ∑ i, c x i • rs L hWU (ε i) = x) ∧
      (∀ (r : Γ(X, W)) x, c (r • x) = r • c x) ∧
      (∀ x y, c (x + y) = c x + c y) := by
  subst hW
  haveI := isLocalizedModule_resBasicOpen L hU g
  haveI := hU.isLocalization_basicOpen g
  have hunitA : ∀ x : Submonoid.powers g,
      IsUnit (algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(X, X.basicOpen g)) x) :=
    IsLocalizedModule.map_units (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g))
  have hunitL : ∀ x : Submonoid.powers g,
      IsUnit (algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(L, X.basicOpen g)) x) :=
    IsLocalizedModule.map_units (L.resBasicOpen g)
  let f : Fin n → (Γ(L, X.basicOpen g) →ₗ[Γ(X, U)] Γ(X, X.basicOpen g)) := fun i ↦
    IsLocalizedModule.lift (Submonoid.powers g) (L.resBasicOpen g)
      ((Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen g)) ∘ₗ (LinearMap.proj i ∘ₗ s)) hunitA
  let fA : Fin n → (Γ(L, X.basicOpen g) →ₗ[Γ(X, X.basicOpen g)] Γ(X, X.basicOpen g)) :=
    fun i ↦ (f i).extendScalarsOfIsLocalization (Submonoid.powers g) Γ(X, X.basicOpen g)
  have hf : ∀ i m, f i (L.resBasicOpen g m) = algebraMap Γ(X, U) Γ(X, X.basicOpen g) (s m i) :=
    fun i m ↦ IsLocalizedModule.lift_apply _ _ _ _ m
  refine ⟨fun x i ↦ f i x, fun m ↦ funext fun i ↦ hf i m, ?_, fun r x ↦ funext fun i ↦
    (fA i).map_smul r x, fun x y ↦ funext fun i ↦ (f i).map_add x y⟩
  let Pr : Γ(L, X.basicOpen g) →ₗ[Γ(X, U)] Γ(L, X.basicOpen g) :=
    ∑ i, (((fA i).smulRight (L.resBasicOpen g (ε i))).restrictScalars Γ(X, U))
  have hPr : Pr = LinearMap.id := by
    refine IsLocalizedModule.ext (Submonoid.powers g) (L.resBasicOpen g) hunitL ?_
    refine LinearMap.ext fun m ↦ ?_
    simp only [Pr, LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.restrictScalars_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
    conv_rhs => rw [← hs m, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.map_smul]
    exact congrArg (· • L.resBasicOpen g (ε i)) (hf i m)
  intro x
  have := LinearMap.congr_fun hPr x
  simp only [Pr, LinearMap.coe_sum, Finset.sum_apply, LinearMap.restrictScalars_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply] at this
  exact this

end CurvesJacobian.ChartCoord
