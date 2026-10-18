/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ChartDescent
import CurvesJacobian.Picard.RelEffCartierFinite
import CurvesJacobian.Picard.PicF

/-!
# Cohomology and base change for line bundles on curves over an arbitrary affine base

Let `C` be a curve over a perfect field `k` with a finite map `π : C → ℙ¹_k`, `T` an affine
`k`-scheme (no Noetherian hypothesis) and `L` an invertible sheaf on `X_T = C ×_k T`, with the
covering of `X_T` by the preimages `U_T`, `V_T` of the two standard charts of `ℙ¹`.

**`CurvesJacobian.hasPerfectModel_cech`**: the Čech data of `L` for `(U_T, V_T)` have a perfect
model: there is a map `δ : K₀ → K₁` of finite projective `Γ(T)`-modules computing the Čech `H⁰`,
`H¹` of `L` after every base change (Stacks, Lemma 36.30.4, Tag 0B91, for `X_T → T`). The proof is
by Noetherian approximation: `Γ(L, U_T)`, `Γ(L, V_T)` and the gluing are described by finitely
many matrices over `Γ(T) ⊗_k Γ(C, U)` etc. (`ChartMatrix.exists_matData`), which are defined over a
finitely generated `k`-subalgebra of `Γ(T)` (`ChartDescent.hasPerfectModel`).

`CurvesJacobian.exists_finite_projective_cech'` is the resulting version of
`exists_finite_projective_cech` without the Noetherian hypothesis.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry TensorProduct Polynomial
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

section Generic

variable {S Y : Scheme.{u}} [Y.Over S]

/-- Restriction of sections, as a `Γ(S)`-algebra map. -/
def resAlg {W W' : Y.Opens} (h : W' ≤ W) : Γ(Y, W) →ₐ[Γ(S, ⊤)] Γ(Y, W') :=
  { (Y.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r ↦ by
      change ((Y ↘ S).appLE ⊤ W (by simp) ≫ Y.presheaf.map (homOfLE h).op) r = _
      rw [Scheme.Hom.appLE_map]
      rfl }

@[simp]
lemma resAlg_apply {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(Y, W)) :
    resAlg (S := S) h s = Y.presheaf.map (homOfLE h).op s := rfl

/-- Sections over a basic open of an affine open are a localization. -/
lemma isLocalization_resAlg {W V : Y.Opens} (hW : IsAffineOpen W) (f : Γ(Y, W))
    (hV : Y.basicOpen f = V) (hVW : V ≤ W) :
    letI := (resAlg (S := S) hVW).toRingHom.toAlgebra
    IsLocalization.Away f Γ(Y, V) := by
  subst hV
  exact hW.isLocalization_basicOpen f

end Generic

section Loc

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (f : R)

lemma IsLocalization.Away.exists_pow_mul_eq [IsLocalization.Away f S] (w : S) :
    ∃ (r : R) (k : ℕ), algebraMap R S f ^ k * w = algebraMap R S r := by
  obtain ⟨⟨r, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) w
  exact ⟨r, k, by rw [← map_pow, mul_comm]; exact h⟩

lemma IsLocalization.Away.exists_pow_mul_eq_zero [IsLocalization.Away f S] (r : R)
    (h : algebraMap R S r = 0) : ∃ k : ℕ, f ^ k * r = 0 := by
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) S r).mp h
  exact ⟨k, hc⟩

end Loc

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]
  (π : C ⟶ ProjectiveLine.scheme k)

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T ↘ Sk)
local notation "pX" => pullback.fst (C ↘ Sk) (T ↘ Sk)

/-- `Γ(X_T, W_T) = Γ(T) ⊗ Γ(C, W)` for an affine open `W ⊆ C`, as an algebra isomorphism. -/
def sectionsAlgEquiv (W : C.Opens) (hW : IsAffineOpen W) (W' : (XT).Opens)
    (hW' : W' = pX ⁻¹ᵁ W) : Γ(T, ⊤) ⊗[Γ(Sk, ⊤)] Γ(C, W) ≃ₐ[Γ(T, ⊤)] Γ(XT, W') :=
  AlgEquiv.ofLinearEquiv (sectionsBaseChangeEquiv W hW W' hW')
    (map_one (pushoutTensorEquiv (isPushout_sections W hW W' hW')))
    (map_mul (pushoutTensorEquiv (isPushout_sections W hW W' hW')))

variable [PerfectField k] [IsCurveOver k C] [IsFinite π]

/-- **Cohomology and base change for line bundles on curves over an arbitrary affine base**
(Stacks, Lemma 36.30.4, Tag 0B91, for `X_T → T`, via Noetherian approximation as in the proof of
Lemma 36.30.1, Tag 0A1H): for `L` invertible on `X_T`, `T` affine over `k` (no Noetherian
hypothesis), the Čech data of `L` for the chart covering `(U_T, V_T)` have a perfect model. -/
theorem hasPerfectModel_cech (L : (XT).Modules) [L.IsInvertible] :
    TwoTerm.HasPerfectModel
      (resModLin T L (inf_le_left : curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
        curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _))
      (resModLin T L (inf_le_right : curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
        curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _)) := by
  letI : Field Γ(Sk, ⊤) := isField_ΓSpec.toField
  have hU := isAffineOpen_chart (T₀ := T) π 0
  have hV := isAffineOpen_chart (T₀ := T) π 1
  haveI := finite_sections L hU
  haveI := projective_sections L hU
  haveI := finite_sections L hV
  haveI := projective_sections L hV
  have hUC : IsAffineOpen (π ⁻¹ᵁ ProjectiveLine.U k 0) :=
    (ProjectiveLine.isAffineOpen_U k 0).preimage π
  have hVC : IsAffineOpen (π ⁻¹ᵁ ProjectiveLine.U k 1) :=
    (ProjectiveLine.isAffineOpen_U k 1).preimage π
  have hWC : IsAffineOpen (π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓ π ⁻¹ᵁ ProjectiveLine.U k 1) :=
    (ProjectiveLine.isAffineOpen_U_inf k).preimage π
  -- compatibility of the tensor identifications with restriction
  have tens_eq : ∀ {W₁ W₂ : C.Opens} (h : W₂ ≤ W₁) (x : Γ(T, ⊤) ⊗[Γ(Sk, ⊤)] Γ(C, W₁)),
      ChartDescent.tens Γ(T, ⊤) (resAlg (S := Sk) h) x =
        (resLin Sk C h).baseChange Γ(T, ⊤) x := fun h x ↦ by
    induction x with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a r => rfl
  have comm : ∀ {W₁ W₂ : C.Opens} (h₁ : IsAffineOpen W₁) (h₂ : IsAffineOpen W₂) (h : W₂ ≤ W₁)
      {W₁' W₂' : (XT).Opens} (e₁ : W₁' = pX ⁻¹ᵁ W₁) (e₂ : W₂' = pX ⁻¹ᵁ W₂) (h' : W₂' ≤ W₁')
      (s : Γ(XT, W₁')),
      ChartDescent.tens Γ(T, ⊤) (resAlg (S := Sk) h) ((sectionsAlgEquiv W₁ h₁ _ e₁).symm s) =
        (sectionsAlgEquiv W₂ h₂ _ e₂).symm (resAlg (S := T) h' s) := by
    intro W₁ W₂ h₁ h₂ h W₁' W₂' e₁ e₂ h' s
    obtain ⟨x, rfl⟩ := (sectionsAlgEquiv (T := T) _ h₁ _ e₁).surjective s
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.eq_symm_apply, tens_eq]
    exact (LinearMap.congr_fun
      (sectionsBaseChangeEquiv_comp_res (T := T) h₁ h₂ h _ _ e₁ e₂ h') x).symm
  -- the matrix presentation over the rings of `X_T`
  obtain ⟨D, hD⟩ := ChartMatrix.exists_matData
    (iU := resAlg (S := T) (inf_le_left : curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _))
    (iV := resAlg (S := T) (inf_le_right : curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _))
    (chartτ (curveChartMap (T₀ := T) π)) (chartσ (curveChartMap (T₀ := T) π))
    (isLocalization_resAlg hU _ (basicOpen_chartτ _) inf_le_left)
    (isLocalization_resAlg hV _ (basicOpen_chartσ _) inf_le_right)
    (resModLin T L inf_le_left) (fun s p ↦ Scheme.Modules.map_smul L _ s p)
    (fun z ↦ by
      obtain ⟨m, j, hj⟩ := ProjectiveLine.exists_pow_smul_eq_res' hU L _
        (basicOpen_chartτ _) inf_le_left z
      exact ⟨m, j, by rw [← map_pow]; exact hj⟩)
    (fun m hm ↦ ProjectiveLine.exists_pow_smul_eq_zero' hU L _ (basicOpen_chartτ _)
      inf_le_left m hm)
    (resModLin T L inf_le_right) (fun s p ↦ Scheme.Modules.map_smul L _ s p)
    (fun z ↦ by
      obtain ⟨m, j, hj⟩ := ProjectiveLine.exists_pow_smul_eq_res' hV L _
        (basicOpen_chartσ _) inf_le_right z
      exact ⟨m, j, by rw [← map_pow]; exact hj⟩)
    (fun m hm ↦ ProjectiveLine.exists_pow_smul_eq_zero' hV L _ (basicOpen_chartσ _)
      inf_le_right m hm)
  refine hD ?_
  -- transport to `Γ(T) ⊗ Γ(C, -)`
  refine D.hasPerfectModel_of_map
    (iU' := ChartDescent.tens Γ(T, ⊤) (resAlg (S := Sk) (inf_le_left :
      π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓ π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _)))
    (iV' := ChartDescent.tens Γ(T, ⊤) (resAlg (S := Sk) (inf_le_right :
      π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓ π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _)))
    (sectionsAlgEquiv (T := T) _ hUC _ rfl).symm (sectionsAlgEquiv (T := T) _ hVC _ rfl).symm
    (sectionsAlgEquiv (T := T) _ hWC _ rfl).symm
    (AlgHom.ext fun s ↦ comm hUC hWC inf_le_left rfl rfl
      (Scheme.Hom.preimage_mono (pullback.fst (C ↘ Sk) (T ↘ Sk)) inf_le_left) s)
    (AlgHom.ext fun s ↦ comm hVC hWC inf_le_right rfl rfl
      (Scheme.Hom.preimage_mono (pullback.fst (C ↘ Sk) (T ↘ Sk)) inf_le_right) s) ?_
  -- the descent theorem
  letI := (resAlg (S := Sk) (inf_le_left :
    π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓ π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _)).toRingHom.toAlgebra
  letI := (resAlg (S := Sk) (inf_le_right :
    π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓ π ⁻¹ᵁ ProjectiveLine.U k 1 ≤ _)).toRingHom.toAlgebra
  haveI hlU := isLocalization_resAlg (S := Sk) hUC (chartτ π) (basicOpen_chartτ π) inf_le_left
  haveI hlV := isLocalization_resAlg (S := Sk) hVC (chartσ π) (basicOpen_chartσ π) inf_le_right
  exact ChartDescent.hasPerfectModel _ _ (chartτ π) (chartσ π) (chartτ_mul_chartσ π)
    (IsLocalization.Away.exists_pow_mul_eq (chartτ π))
    (IsLocalization.Away.exists_pow_mul_eq_zero (chartτ π))
    (IsLocalization.Away.exists_pow_mul_eq (chartσ π))
    (IsLocalization.Away.exists_pow_mul_eq_zero (chartσ π))
    (finite_curveChart π 0) (finite_curveChart π 1) _

/-- **`exists_finite_projective_cech` without the Noetherian hypothesis** (Stacks, Lemma 36.30.4,
Tag 0B91, for `X_T → T`): for `L` invertible on `X_T`, `T` any affine `k`-scheme, there is a map
`δ : K₀ → K₁` of finite projective `Γ(T)`-modules such that for every affine `T`-scheme `T'` the
Čech `H⁰`, `H¹` of `L_{T'}` for the covering `(U_{T'}, V_{T'})` are `ker`, `coker` of
`Γ(T') ⊗ δ`. -/
theorem exists_finite_projective_cech' (L : (XT).Modules) [L.IsInvertible] :
    ∃ (K₀ K₁ : ModuleCat.{u} Γ(T, ⊤)) (δ : K₀ →ₗ[Γ(T, ⊤)] K₁),
      Module.Finite Γ(T, ⊤) K₀ ∧ Module.Projective Γ(T, ⊤) K₀ ∧
      Module.Finite Γ(T, ⊤) K₁ ∧ Module.Free Γ(T, ⊤) K₁ ∧
      ∀ (T' : Scheme.{u}) [T'.Over T] [IsAffine T'],
        Nonempty (LinearMap.ker (δ.baseChange Γ(T', ⊤)) ≃ₗ[Γ(T', ⊤)]
          cechModH0 T' (lineBundleBaseChange (S := T) (T := T') L)
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0))
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1))) ∧
        Nonempty (((Γ(T', ⊤) ⊗[Γ(T, ⊤)] K₁) ⧸ LinearMap.range (δ.baseChange Γ(T', ⊤))) ≃ₗ[Γ(T', ⊤)]
          cechModH1 T' (lineBundleBaseChange (S := T) (T := T') L)
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0))
            (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
              (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1))) := by
  obtain ⟨K₀, K₁, δ, hK₀, hK₀', hK₁, hK₁', H⟩ := hasPerfectModel_cech (T := T) π L
  refine ⟨K₀, K₁, δ, hK₀, hK₀', hK₁, hK₁', fun T' _ _ ↦ ?_⟩
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := H Γ(T', ⊤)
  exact ⟨⟨e₀ ≪≫ₗ (lineBundleH0BaseChange L _ _ (isAffineOpen_chart π 0)
      (isAffineOpen_chart π 1) (isAffineOpen_chart_inf π)).symm⟩,
    ⟨e₁ ≪≫ₗ (lineBundleH1BaseChange L _ _ (isAffineOpen_chart π 0)
      (isAffineOpen_chart π 1) (isAffineOpen_chart_inf π)).symm⟩⟩

end Curve

end CurvesJacobian
