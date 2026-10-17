/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ChartSheaf
import CurvesJacobian.Picard.CurveCover
import FormalSchemes.ProjectiveLineGlueIso

/-!
# Cohomology and base change for line bundles on curves

Let `X` be a curve over a perfect field `k` (`Belyi.IsCurveOver`), `T₀` an affine `k`-scheme
with Noetherian ring of functions `A = Γ(T₀)`, and `L` an invertible sheaf on
`X_{T₀} = X ×_k T₀`. Choose a finite morphism `π : X → ℙ¹_k` (belyi) and let `U`, `V` be the
preimages in `X_{T₀}` of the two standard charts, with the pulled-back chart coordinates
`τ`, `σ`. Then:

* `Γ(X_{T₀}, U)` is finite over `A[τ]` (`π` is finite and `Γ(ℙ¹, D₊(x₀)) = k[x]`), and is flat
  over `A` (it is `A ⊗_k Γ(X, π⁻¹D₊(x₀))`);
* hence the sections of `L` over `U`, `V` are finite over `A[τ]`, `A[σ]`, and by Serre's
  finiteness on `ℙ¹_A` (formal-schemes' chart modules) the Čech `H⁰`, `H¹` of `L` are finite
  `A`-modules (`CurvesJacobian.finite_cechModH0_H1`);
* **cohomology and base change** (`CurvesJacobian.exists_finite_projective_cech`;
  Stacks, Lemma 36.30.4, Tag 0B91, for curves): there is a map `δ : K₀ → K₁` of finite
  projective `A`-modules such that for every affine `T₀`-scheme `T`, the Čech `H⁰` and `H¹` of
  `L_T` (for the covering `U_T`, `V_T` of `X_T`) are the kernel and cokernel of `Γ(T) ⊗_A δ`.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Polynomial Belyi
open TensorProduct
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

open Cech

/-! ### Charts pulled back from `ℙ¹` -/

section ChartData

variable {A₀ : Type u} [CommRing A₀] {Y : Scheme.{u}} (g : Y ⟶ ProjectiveLine.scheme A₀)

/-- The pulled-back chart coordinate on `g⁻¹ D₊(x₀)`. -/
def chartτ : Γ(Y, g ⁻¹ᵁ ProjectiveLine.U A₀ 0) := g.app _ (ProjectiveLine.coord A₀ 0)

/-- The pulled-back chart coordinate on `g⁻¹ D₊(x₁)`. -/
def chartσ : Γ(Y, g ⁻¹ᵁ ProjectiveLine.U A₀ 1) := g.app _ (ProjectiveLine.coord A₀ 1)

lemma basicOpen_chartτ :
    Y.basicOpen (chartτ g) = g ⁻¹ᵁ ProjectiveLine.U A₀ 0 ⊓ g ⁻¹ᵁ ProjectiveLine.U A₀ 1 := by
  rw [chartτ, ← Scheme.preimage_basicOpen, ProjectiveLine.basicOpen_coord_zero]
  rfl

lemma basicOpen_chartσ :
    Y.basicOpen (chartσ g) = g ⁻¹ᵁ ProjectiveLine.U A₀ 0 ⊓ g ⁻¹ᵁ ProjectiveLine.U A₀ 1 := by
  rw [chartσ, ← Scheme.preimage_basicOpen, ProjectiveLine.basicOpen_coord_one]
  rfl

lemma app_res_apply {W W' : (ProjectiveLine.scheme A₀).Opens} (h : W' ≤ W)
    (s : Γ(ProjectiveLine.scheme A₀, W)) :
    Y.presheaf.map (homOfLE (g.preimage_mono h)).op (g.app W s) =
      g.app W' ((ProjectiveLine.scheme A₀).presheaf.map (homOfLE h).op s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

lemma chartτ_mul_chartσ :
    Y.presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ ProjectiveLine.U A₀ 0 ⊓
        g ⁻¹ᵁ ProjectiveLine.U A₀ 1 ≤ _)).op (chartτ g) *
      Y.presheaf.map (homOfLE (inf_le_right : g ⁻¹ᵁ ProjectiveLine.U A₀ 0 ⊓
        g ⁻¹ᵁ ProjectiveLine.U A₀ 1 ≤ _)).op (chartσ g) = 1 := by
  have h0 := app_res_apply g (inf_le_left : ProjectiveLine.U A₀ 0 ⊓ ProjectiveLine.U A₀ 1 ≤ _)
    (ProjectiveLine.coord A₀ 0)
  have h1 := app_res_apply g (inf_le_right : ProjectiveLine.U A₀ 0 ⊓ ProjectiveLine.U A₀ 1 ≤ _)
    (ProjectiveLine.coord A₀ 1)
  rw [ProjectiveLine.res_coord_zero] at h0
  rw [ProjectiveLine.res_coord_one] at h1
  rw [chartτ, chartσ]
  erw [h0, h1]
  refine (map_mul (ConcreteCategory.hom (g.app (ProjectiveLine.U A₀ 0 ⊓ ProjectiveLine.U A₀ 1)))
    _ _).symm.trans ?_
  rw [ProjectiveLine.transition_mul_neg A₀ 1]
  exact map_one _

end ChartData

/-! ### Finiteness over `A[τ]` -/

section FiniteAEval

variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
  [Module A M] [IsScalarTower A B M]

/-- If `B` is finite over `A[X]` via `X ↦ τ` and `M` is finite over `B`, then `M` is finite over
`A[X]` with `X` acting as multiplication by `τ`. -/
theorem finite_aeval_of_finite (τ : B) (φ : M →ₗ[A] M) (hφ : ∀ m, φ m = τ • m)
    (hB : letI := (aeval (R := A) τ).toRingHom.toAlgebra; Module.Finite A[X] B)
    [Module.Finite B M] :
    Module.Finite A[X] (Module.AEval' φ) := by
  letI := (aeval (R := A) τ).toRingHom.toAlgebra
  letI : Module A[X] M := Module.compHom M (aeval (R := A) τ).toRingHom
  haveI : IsScalarTower A[X] B M := IsScalarTower.of_compHom _ _ _
  haveI : Module.Finite A[X] M := Module.Finite.trans B M
  haveI : IsScalarTower A A[X] M := ⟨fun a q m ↦ by
    change (aeval τ (a • q)) • m = a • ((aeval τ q) • m)
    rw [_root_.map_smul, smul_assoc]⟩
  let e : Module.AEval' φ ≃ₗ[A[X]] M := LinearEquiv.ofAEval φ (LinearEquiv.refl A M) fun m ↦ by
    change φ m = (aeval (R := A) τ Polynomial.X) • m
    rw [aeval_X, hφ]
  exact Module.Finite.equiv e.symm

end FiniteAEval

/-! ### Curves -/

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  {T₀ : Scheme.{u}} [T₀.Over (Spec (CommRingCat.of k))] [IsAffine T₀]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T₀ ↘ Sk)
local notation "pX" => pullback.fst (C ↘ Sk) (T₀ ↘ Sk)

lemma isField_ΓSpec : IsField Γ(Sk, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)

/-- Sections of `X_{T₀}` over the preimage of an affine open of `C` are flat over `Γ(T₀)`. -/
theorem flat_sections_baseChange (W : C.Opens) (hW : IsAffineOpen W) (W' : (XT).Opens)
    (hW' : W' = pX ⁻¹ᵁ W) : Module.Flat Γ(T₀, ⊤) Γ(XT, W') := by
  haveI : Module.Flat Γ(Sk, ⊤) Γ(C, W) :=
    RingHom.Flat.of_isField isField_ΓSpec ((C ↘ Sk).appLE ⊤ W (by simp)).hom
  exact Module.Flat.of_linearEquiv (sectionsBaseChangeEquiv W hW W' hW').symm

variable (π : C ⟶ ProjectiveLine.scheme k)

/-- The composite `X_{T₀} → C → ℙ¹_k`. -/
abbrev curveChartMap : XT ⟶ ProjectiveLine.scheme k := pX ≫ π

/-- The pulled-back chart coordinate on the preimage of `D₊(x_i)`. -/
def chartCoord (i : Fin 2) : Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i) :=
  (curveChartMap π).app _ (ProjectiveLine.coord k i)

lemma chartSections_coord (i : Fin 2) :
    ProjectiveLine.chartSections k i (ProjectiveLine.coord k i) = Polynomial.X :=
  (ProjectiveLine.chartSections_awayToSection k i _).trans (ProjectiveLine.chartEquiv_chartCoord i)

variable [PerfectField k] [IsCurveOver k C]

omit [IsAffine T₀] in
/-- Pulled back to `X_{T₀}`, every function on the chart `D₊(x_i)` of `ℙ¹_k` is a polynomial
with coefficients in `Γ(T₀)` in the chart coordinate. -/
lemma exists_aeval_eq (i : Fin 2) (q : k[X]) :
    ∃ q' : Γ(T₀, ⊤)[X], aeval (chartCoord (T₀ := T₀) π i) q' =
      (pX).app (π ⁻¹ᵁ ProjectiveLine.U k i)
        (π.app _ ((ProjectiveLine.chartSections k i).symm q)) := by
  induction q using Polynomial.induction_on with
  | C a =>
    -- constants come from `Γ(C, ⊤) = k`, hence from `Γ(T₀)`
    have hs := (IsCurveOver.bijective_structureToGlobal k C).2
    have e1 : (ProjectiveLine.chartSections k i).symm (Polynomial.C a) =
        ProjectiveLine.secMap k (ProjectiveLine.U k i) a := by
      rw [(ProjectiveLine.chartSections k i).symm_apply_eq, ProjectiveLine.chartSections_secMap]
    obtain ⟨c, hc⟩ := hs (π.app ⊤ (ProjectiveLine.structMap k a))
    refine ⟨Polynomial.C ((T₀ ↘ Sk).appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso _).inv c)), ?_⟩
    rw [aeval_C, e1, ProjectiveLine.secMap, RingHom.comp_apply, ← app_res_apply π le_top, ← hc]
    rw [algebraMap_sections]
    have := appLE_condition (S := Sk) (Y := C) (T := T₀) (π ⁻¹ᵁ ProjectiveLine.U k i)
      (pX ⁻¹ᵁ π ⁻¹ᵁ ProjectiveLine.U k i) le_rfl ((Scheme.ΓSpecIso _).inv c)
    refine this.symm.trans ?_
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p' + q', by rw [map_add, map_add, map_add, map_add, hp', hq']; try rfl⟩
  | monomial n a h =>
    obtain ⟨p', hp'⟩ := h
    refine ⟨p' * Polynomial.X, ?_⟩
    have hX : (ProjectiveLine.chartSections k i).symm Polynomial.X = ProjectiveLine.coord k i :=
      (ProjectiveLine.chartSections k i).symm_apply_eq.mpr (chartSections_coord i).symm
    have e : (pX).app (π ⁻¹ᵁ ProjectiveLine.U k i) (π.app _
        ((ProjectiveLine.chartSections k i).symm (Polynomial.C a * Polynomial.X ^ (n + 1)))) =
        (pX).app (π ⁻¹ᵁ ProjectiveLine.U k i) (π.app _
          ((ProjectiveLine.chartSections k i).symm (Polynomial.C a * Polynomial.X ^ n))) *
          chartCoord π i := by
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, hX]
      rfl
    rw [e, map_mul, aeval_X, hp']
    try rfl

/-- `Γ(T₀)[X]` acting on `Γ(X_{T₀}, U_i)` through the chart coordinate. -/
abbrev chartAlgebra (i : Fin 2) : Algebra Γ(T₀, ⊤)[X]
    ((XT).presheaf.obj (op (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i))) :=
  (aeval (R := Γ(T₀, ⊤)) (chartCoord (T₀ := T₀) π i)).toRingHom.toAlgebra

attribute [local instance] chartAlgebra

include π in
/-- `Γ(X_{T₀}, U_i)` is finite over `Γ(T₀)[X]` acting through the chart coordinate. -/
theorem finite_sections_chart [IsFinite π] (i : Fin 2) :
    Module.Finite Γ(T₀, ⊤)[X]
      ((XT).presheaf.obj (op (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i))) := by
  set W := π ⁻¹ᵁ ProjectiveLine.U k i
  have hW : IsAffineOpen W := (ProjectiveLine.isAffineOpen_U k i).preimage π
  -- generators of `Γ(C, W)` over `Γ(ℙ¹, D₊(x_i))`
  have hfin := π.finite_app (ProjectiveLine.U k i) (ProjectiveLine.isAffineOpen_U k i)
  letI := (π.app (ProjectiveLine.U k i)).hom.toAlgebra
  obtain ⟨G, hG⟩ := (show Module.Finite Γ(ProjectiveLine.scheme k, ProjectiveLine.U k i) Γ(C, W)
    from hfin).fg_top
  classical
  set W' := curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i
  let pr : Γ(C, W) →+* (XT).presheaf.obj (op W') := ((pX).app W).hom
  set P : Submodule Γ(T₀, ⊤)[X] ((XT).presheaf.obj (op W')) :=
    Submodule.span Γ(T₀, ⊤)[X] (pr '' (G : Set Γ(C, W)))
  have h1 : ∀ r : Γ(C, W), pr r ∈ P := by
    intro r
    have hr : r ∈ Submodule.span Γ(ProjectiveLine.scheme k, ProjectiveLine.U k i)
        (G : Set Γ(C, W)) := hG ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact P.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
    | smul s x _ hx =>
      obtain ⟨q', hq'⟩ := exists_aeval_eq (T₀ := T₀) π i (ProjectiveLine.chartSections k i s)
      rw [RingEquiv.symm_apply_apply] at hq'
      rw [Algebra.smul_def, map_mul]
      have : pr (algebraMap _ Γ(C, W) s) = aeval (R := Γ(T₀, ⊤)) (chartCoord (T₀ := T₀) π i) q' :=
        hq'.symm
      rw [this]
      have h2 := P.smul_mem q' hx
      rw [Algebra.smul_def] at h2
      exact h2
  refine ⟨⟨(G.image pr), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := (sectionsBaseChangeEquiv W hW (pX ⁻¹ᵁ W) rfl).surjective y
  induction x with
  | zero => rw [map_zero]; exact P.zero_mem
  | add x y hx hy => rw [map_add]; exact P.add_mem hx hy
  | tmul b r =>
    rw [sectionsBaseChangeEquiv_tmul, ← Scheme.Hom.app_eq_appLE]
    have : (pullback.snd (C ↘ Sk) (T₀ ↘ Sk)).appLE ⊤ (pX ⁻¹ᵁ W) (by simp) b * (pX).app W r =
        (Polynomial.C b : Γ(T₀, ⊤)[X]) • pr r := by
      rw [Algebra.smul_def]
      change _ = aeval (R := Γ(T₀, ⊤)) (chartCoord (T₀ := T₀) π i) (Polynomial.C b) * _
      rw [aeval_C]
      rfl
    rw [this]
    exact P.smul_mem _ (h1 r)

include π in
/-- The sections of an invertible sheaf on `X_{T₀}` over `U_i` are finite over `Γ(T₀)[X]`. -/
theorem finite_aeval_lineBundle [IsFinite π] (L : (XT).Modules) [L.IsInvertible] (i : Fin 2) :
    Module.Finite Γ(T₀, ⊤)[X]
      (Module.AEval' (smulSec (S := T₀) L (chartCoord (T₀ := T₀) π i))) := by
  have hU : IsAffineOpen (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i) := by
    haveI : IsAffineHom (T₀ ↘ Sk) := isAffineHom_of_isAffine _
    haveI : IsAffineHom pX :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
    exact (ProjectiveLine.isAffineOpen_U k i).preimage _
  haveI := finite_sections L hU
  exact finite_aeval_of_finite (chartCoord π i) (smulSec L (chartCoord π i)) (fun _ ↦ rfl)
    (finite_sections_chart π i)

omit [PerfectField k] [IsCurveOver k C] in
lemma isAffineOpen_chart [IsFinite π] (i : Fin 2) :
    IsAffineOpen (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k i) := by
  haveI : IsAffineHom (T₀ ↘ Sk) := isAffineHom_of_isAffine _
  haveI : IsAffineHom pX :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  exact (ProjectiveLine.isAffineOpen_U k i).preimage _

omit [PerfectField k] [IsCurveOver k C] in
lemma isAffineOpen_chart_inf [IsFinite π] :
    IsAffineOpen (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) := by
  haveI : IsAffineHom (T₀ ↘ Sk) := isAffineHom_of_isAffine _
  haveI : IsAffineHom pX :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  exact (ProjectiveLine.isAffineOpen_U_inf k).preimage (curveChartMap π)

include π in
/-- **Finiteness of the Čech cohomology** of an invertible sheaf on `X_{T₀}`, `Γ(T₀)`
Noetherian (Stacks, Lemma 30.19.2, Tag 02O5, for curves; via Serre's theorem on `ℙ¹`). -/
theorem finite_cechModH0_H1 [IsFinite π] [IsNoetherianRing Γ(T₀, ⊤)] (L : (XT).Modules)
    [L.IsInvertible] :
    Module.Finite Γ(T₀, ⊤) (cechModH0 T₀ L (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0)
      (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1)) ∧
    Module.Finite Γ(T₀, ⊤) (cechModH1 T₀ L (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0)
      (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1)) := by
  haveI := isQuasicoherent_of_isInvertible L
  exact ⟨finite_cechModH0_of_chart L (chartτ_mul_chartσ (curveChartMap π))
      (isAffineOpen_chart π 0) (isAffineOpen_chart π 1) (basicOpen_chartτ _) (basicOpen_chartσ _)
      (finite_aeval_lineBundle π L 0) (finite_aeval_lineBundle π L 1),
    finite_cechModH1_of_chart L (chartτ_mul_chartσ (curveChartMap π))
      (isAffineOpen_chart π 0) (isAffineOpen_chart π 1) (basicOpen_chartτ _) (basicOpen_chartσ _)
      (finite_aeval_lineBundle π L 0)⟩

include π in
/-- **Cohomology and base change for line bundles on curves** (Stacks, Lemma 36.30.4,
Tag 0B91, for `X_{T₀} → T₀`; Mumford's lemma in two-term form). Let `C` be a curve over a
perfect field `k`, `π : C → ℙ¹_k` finite, `T₀` affine over `k` with `Γ(T₀)` Noetherian and `L`
invertible on `X_{T₀}`; let `U`, `V` be the preimages of the standard charts. There is a map
`δ : K₀ → K₁` of finite projective `Γ(T₀)`-modules such that for every affine `T₀`-scheme `T`
the Čech `H⁰`, `H¹` of `L_T` for the covering `(U_T, V_T)` of `X_T` are `ker`, `coker` of
`Γ(T) ⊗ δ`. -/
theorem exists_finite_projective_cech [IsFinite π] [IsNoetherianRing Γ(T₀, ⊤)]
    (L : (XT).Modules) [L.IsInvertible] :
    ∃ (K₀ K₁ : ModuleCat.{u} Γ(T₀, ⊤)) (δ : K₀ →ₗ[Γ(T₀, ⊤)] K₁),
      Module.Finite Γ(T₀, ⊤) K₀ ∧ Module.Projective Γ(T₀, ⊤) K₀ ∧
      Module.Finite Γ(T₀, ⊤) K₁ ∧ Module.Free Γ(T₀, ⊤) K₁ ∧
      ∀ (T : Scheme.{u}) [T.Over T₀] [IsAffine T],
        Nonempty (LinearMap.ker (δ.baseChange Γ(T, ⊤)) ≃ₗ[Γ(T, ⊤)]
          cechModH0 T (lineBundleBaseChange (S := T₀) (T := T) L)
            (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
              (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0))
            (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
              (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1))) ∧
        Nonempty (((Γ(T, ⊤) ⊗[Γ(T₀, ⊤)] K₁) ⧸ LinearMap.range (δ.baseChange Γ(T, ⊤))) ≃ₗ[Γ(T, ⊤)]
          cechModH1 T (lineBundleBaseChange (S := T₀) (T := T) L)
            (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
              (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0))
            (pullback.fst ((XT) ↘ T₀) (T ↘ T₀) ⁻¹ᵁ
              (curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1))) := by
  haveI : Module.Flat Γ(T₀, ⊤) Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0) :=
    flat_sections_baseChange _ ((ProjectiveLine.isAffineOpen_U k 0).preimage π) _ rfl
  haveI : Module.Flat Γ(T₀, ⊤) Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) :=
    flat_sections_baseChange _ ((ProjectiveLine.isAffineOpen_U k 1).preimage π) _ rfl
  haveI : Module.Flat Γ(T₀, ⊤) Γ(XT, curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T₀) π ⁻¹ᵁ ProjectiveLine.U k 1) :=
    flat_sections_baseChange _ ((ProjectiveLine.isAffineOpen_U_inf k).preimage π) _ rfl
  obtain ⟨h0, h1⟩ := finite_cechModH0_H1 π L
  exact exists_finite_projective_lineBundle L _ _ (isAffineOpen_chart π 0)
    (isAffineOpen_chart π 1) (isAffineOpen_chart_inf π) h0 h1

end Curve

end CurvesJacobian
