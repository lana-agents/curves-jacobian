/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CechLineBundle
import FormalSchemes.ChartModule
import FormalSchemes.ProjectiveLineBridge

/-!
# Chart modules of quasi-coherent modules on schemes with a `ℙ¹`-like covering

Let `Y` be a scheme over `S`, `A = Γ(S, ⊤)`, and let `U`, `V` be affine opens of `Y` with
functions `τ ∈ Γ(Y, U)`, `σ ∈ Γ(Y, V)` such that `D(τ) = U ∩ V = D(σ)` and `τ σ = 1` on
`U ∩ V` (e.g. the preimages of the standard charts of `ℙ¹` under a morphism `Y → ℙ¹`, with the
pulled-back chart coordinates). For a quasi-coherent `𝒪_Y`-module `L`, the sections over `U`,
`V`, `U ∩ V` with multiplication by `τ`, `σ` form a chart module in the sense of
formal-schemes (`ProjectiveLine.ChartModule`, the algebraic model of a quasi-coherent module on
`ℙ¹_A`): `CurvesJacobian.chartModuleOf`. Its `H⁰`, `H¹` are the Čech cohomology of `L` for
`(U, V)` (definitionally), so Serre's finiteness theorems on `ℙ¹_A`
(`ProjectiveLine.ChartModule.finite_H0`, `finite_H1`; Stacks, Lemma 30.14.1, Tag 01YS) give:

* `CurvesJacobian.finite_cechModH0_of_chart`, `CurvesJacobian.finite_cechModH1_of_chart`: if
  `Γ(L, U)` and `Γ(L, V)` are finitely generated over `A[τ]` resp. `A[σ]`, the Čech `H¹` of `L`
  is a finite `A`-module, and so is `H⁰` when `A` is Noetherian.

This is the pushforward to `ℙ¹_A` of `L` along a finite morphism, in Čech form.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

open Cech

variable {S Y : Scheme.{u}} [Y.Over S] (L : Y.Modules)

/-- Multiplication by `r ∈ Γ(Y, W)` on `Γ(L, W)`, as a `Γ(S, ⊤)`-linear map. -/
def smulSec {W : Y.Opens} (r : Γ(Y, W)) : Γ(L, W) →ₗ[Γ(S, ⊤)] Γ(L, W) where
  toFun m := r • m
  map_add' := smul_add r
  map_smul' a m := by
    rw [smul_sections_def, smul_sections_def, smul_smul, smul_smul, mul_comm]
    rfl

lemma smulSec_apply {W : Y.Opens} (r : Γ(Y, W)) (m : Γ(L, W)) :
    smulSec (S := S) L r m = r • m := rfl

lemma smulSec_pow_apply {W : Y.Opens} (r : Γ(Y, W)) (k : ℕ) (m : Γ(L, W)) :
    (smulSec (S := S) L r ^ k) m = r ^ k • m := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, smulSec_apply, smul_smul, ← pow_succ']

variable {U V : Y.Opens} {τ : Γ(Y, U)} {σ : Γ(Y, V)}
  (hτσ : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op τ *
    Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ = 1)

/-- Multiplication by `τ|_{U ∩ V}`, an automorphism with inverse multiplication by `σ`. -/
def chartT : Γ(L, U ⊓ V) ≃ₗ[Γ(S, ⊤)] Γ(L, U ⊓ V) :=
  LinearEquiv.ofLinear (smulSec L (Y.presheaf.map (homOfLE inf_le_left).op τ))
    (smulSec L (Y.presheaf.map (homOfLE inf_le_right).op σ))
    (LinearMap.ext fun m ↦ by
      rw [LinearMap.comp_apply, smulSec_apply, smulSec_apply, smul_smul, hτσ, one_smul]
      rfl)
    (LinearMap.ext fun m ↦ by
      rw [LinearMap.comp_apply, smulSec_apply, smulSec_apply, smul_smul, mul_comm, hτσ, one_smul]
      rfl)

lemma chartT_pow_apply (k : ℕ) (m : Γ(L, U ⊓ V)) :
    (chartT (S := S) L hτσ ^ k) m =
      Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op τ ^ k • m := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih]
    exact (smul_smul (Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op τ) _ m).trans
      (by rw [← pow_succ'])

lemma chartT_symm_pow_apply (k : ℕ) (m : Γ(L, U ⊓ V)) :
    ((chartT (S := S) L hτσ).symm ^ k) m =
      Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ ^ k • m := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih]
    exact (smul_smul (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ) _ m).trans
      (by rw [← pow_succ'])

variable [L.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hτ : Y.basicOpen τ = U ⊓ V) (hσ : Y.basicOpen σ = U ⊓ V)

/-- **The chart module of `L`** for a `ℙ¹`-like covering `(U, V)`. -/
def chartModuleOf : ProjectiveLine.ChartModule Γ(S, ⊤) where
  M0 := ModuleCat.of Γ(S, ⊤) Γ(L, U)
  M1 := ModuleCat.of Γ(S, ⊤) Γ(L, V)
  M01 := ModuleCat.of Γ(S, ⊤) Γ(L, U ⊓ V)
  x0 := smulSec L τ
  x1 := smulSec L σ
  t := chartT L hτσ
  r0 := resModLin S L inf_le_left
  r1 := resModLin S L inf_le_right
  r0_x0 m := Scheme.Modules.map_smul L _ τ m
  r1_x1 m := Scheme.Modules.map_smul L _ σ m
  exists_r0 z := by
    obtain ⟨m, k, hk⟩ := ProjectiveLine.exists_pow_smul_eq_res' hU L τ hτ inf_le_left z
    refine ⟨m, k, ?_⟩
    rw [chartT_pow_apply, ← map_pow]
    exact hk
  ker_r0 m hm := by
    obtain ⟨k, hk⟩ := ProjectiveLine.exists_pow_smul_eq_zero' hU L τ hτ inf_le_left m hm
    exact ⟨k, (smulSec_pow_apply L τ k m).trans hk⟩
  exists_r1 z := by
    obtain ⟨m, k, hk⟩ := ProjectiveLine.exists_pow_smul_eq_res' hV L σ hσ inf_le_right z
    refine ⟨m, k, ?_⟩
    rw [chartT_symm_pow_apply, ← map_pow]
    exact hk
  ker_r1 m hm := by
    obtain ⟨k, hk⟩ := ProjectiveLine.exists_pow_smul_eq_zero' hV L σ hσ inf_le_right m hm
    exact ⟨k, (smulSec_pow_apply L σ k m).trans hk⟩

include hτσ hU hV hτ hσ in
/-- **Finiteness of Čech `H¹`** for a `ℙ¹`-like covering, if `Γ(L, U)` is finitely generated
over `A[τ]` (Serre's theorem on `ℙ¹_A`, no Noetherian hypothesis). -/
theorem finite_cechModH1_of_chart
    (h0 : Module.Finite Γ(S, ⊤)[X] (Module.AEval' (smulSec (S := S) L τ))) :
    Module.Finite Γ(S, ⊤) (cechModH1 S L U V) :=
  @ProjectiveLine.ChartModule.finite_H1 _ _ (chartModuleOf L hτσ hU hV hτ hσ) h0

include hτσ hU hV hτ hσ in
/-- **Finiteness of Čech `H⁰`** for a `ℙ¹`-like covering over a Noetherian ring, if `Γ(L, U)`,
`Γ(L, V)` are finitely generated over `A[τ]`, `A[σ]`. -/
theorem finite_cechModH0_of_chart [IsNoetherianRing Γ(S, ⊤)]
    (h0 : Module.Finite Γ(S, ⊤)[X] (Module.AEval' (smulSec (S := S) L τ)))
    (h1 : Module.Finite Γ(S, ⊤)[X] (Module.AEval' (smulSec (S := S) L σ))) :
    Module.Finite Γ(S, ⊤) (cechModH0 S L U V) :=
  @ProjectiveLine.ChartModule.finite_H0 _ _ (chartModuleOf L hτσ hU hV hτ hσ) _ h0 h1

end CurvesJacobian
