/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CechBaseChange
import CurvesJacobian.Picard.QcohBaseChange
import CurvesJacobian.Picard.BaseChangeSquare
import CurvesJacobian.Picard.TwoTermPerfect

/-!
# Čech cohomology of line bundles and affine base change

Let `Y` be a scheme over an affine scheme `S`, `L` an invertible `𝒪_Y`-module and `U ⊆ Y` an
affine open. For an affine `S`-scheme `T`, with `p : Y_T = Y ×_S T → Y`, the sections of
`L_T = p^*L` over `U_T = p⁻¹U` are the base change of the sections of `L` over `U`:

* `CurvesJacobian.Cech.sectionsBaseChangeL`:
  `Γ(T) ⊗_{Γ(S)} Γ(L, U) ≃ Γ(L_T, U_T)`, `b ⊗ m ↦ b • (p^* m)|_{U_T}`, compatible with
  restrictions (`sectionsBaseChangeL_comp_res`). This combines the sections of pullbacks over
  affines (`Scheme.Modules.isBaseChange_pullbackRes`) with `Γ(U_T) = Γ(T) ⊗_{Γ(S)} Γ(U)`
  (`Cech.isPushout_sections`) via `CurvesJacobian.bijective_baseChangeMap`.

Consequently the two-set Čech complex of `L_T` for the covering `(U_T, V_T)` is the base change
of the Čech complex of `L` (`Cech.lineBundleH0BaseChange`, `Cech.lineBundleH1BaseChange`), and
over a Noetherian `Γ(S)`, if the Čech terms are flat and `H⁰`, `H¹` finite, there is a two-term
complex of finite projective `Γ(S)`-modules computing `H⁰` and `H¹` of `L_T` for all affine
`T → S` (`Cech.exists_finite_projective_lineBundle`; Stacks, Lemma 36.30.4, Tag 0B91, for a
covering by two affines).
-/

open CategoryTheory Limits TopologicalSpace TensorProduct AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian.Cech

variable {S : Scheme.{u}}

/-- For `Y` over `S`, the sections of an `𝒪_Y`-module form `Γ(S, ⊤)`-modules. -/
scoped instance sectionsModule (Y : Scheme.{u}) [Y.Over S] (L : Y.Modules) (W : Y.Opens) :
    Module Γ(S, ⊤) Γ(L, W) :=
  Module.compHom _ (algebraMap Γ(S, ⊤) Γ(Y, W))

scoped instance sectionsModule_isScalarTower (Y : Scheme.{u}) [Y.Over S] (L : Y.Modules)
    (W : Y.Opens) : IsScalarTower Γ(S, ⊤) Γ(Y, W) Γ(L, W) :=
  IsScalarTower.of_compHom _ _ _

lemma smul_sections_def (Y : Scheme.{u}) [Y.Over S] (L : Y.Modules) (W : Y.Opens)
    (r : Γ(S, ⊤)) (x : Γ(L, W)) : r • x = algebraMap Γ(S, ⊤) Γ(Y, W) r • x := rfl

/-- Restriction of sections of an `𝒪_Y`-module, as a `Γ(S, ⊤)`-linear map. -/
def resModLin (S : Scheme.{u}) {Y : Scheme.{u}} [Y.Over S] (L : Y.Modules) {W W' : Y.Opens}
    (h : W' ≤ W) : Γ(L, W) →ₗ[Γ(S, ⊤)] Γ(L, W') where
  toFun := L.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r x := by
    rw [smul_sections_def, smul_sections_def, Scheme.Modules.map_smul]
    congr 1
    rw [algebraMap_sections, algebraMap_sections, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map]
    rfl

@[simp]
lemma resModLin_apply (S : Scheme.{u}) {Y : Scheme.{u}} [Y.Over S] (L : Y.Modules)
    {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(L, W)) :
    resModLin S L h x = L.presheaf.map (homOfLE h).op x := rfl

/-- Two-set Čech `H⁰` of an `𝒪_Y`-module, as a `Γ(S, ⊤)`-module. -/
abbrev cechModH0 (S : Scheme.{u}) {Y : Scheme.{u}} [Y.Over S] (L : Y.Modules) (U V : Y.Opens) :=
  TwoCech.H0 (resModLin S L (inf_le_left : U ⊓ V ≤ U)) (resModLin S L (inf_le_right : U ⊓ V ≤ V))

/-- Two-set Čech `H¹` of an `𝒪_Y`-module, as a `Γ(S, ⊤)`-module. -/
abbrev cechModH1 (S : Scheme.{u}) {Y : Scheme.{u}} [Y.Over S] (L : Y.Modules) (U V : Y.Opens) :=
  TwoCech.H1 (resModLin S L (inf_le_left : U ⊓ V ≤ U)) (resModLin S L (inf_le_right : U ⊓ V ≤ V))

variable {Y T : Scheme.{u}} [Y.Over S] [T.Over S] [IsAffine S] [IsAffine T]

local notation "YT" => pullback (Y ↘ S) (T ↘ S)
local notation "pY" => pullback.fst (Y ↘ S) (T ↘ S)

/-- `Γ(U) ⊗_{Γ(S)} Γ(T) ≃ Γ(U_T)` as `Γ(U)`-modules. -/
def sectionsPushoutEquiv (U : Y.Opens) (hU : IsAffineOpen U) (W' : (YT).Opens)
    (hW' : W' = pY ⁻¹ᵁ U) :
    letI := ((pY).appLE U W' hW'.le).hom.toAlgebra
    Γ(Y, U) ⊗[Γ(S, ⊤)] Γ(T, ⊤) ≃ₗ[Γ(Y, U)] Γ(YT, W') :=
  letI := ((pY).appLE U W' hW'.le).hom.toAlgebra
  { pushoutTensorEquiv (isPushout_sections U hU W' hW').flip with
    map_smul' a x := by
      change pushoutTensorEquiv _ (a • x) = algebraMap Γ(Y, U) Γ(YT, W') a *
        pushoutTensorEquiv _ x
      induction x with
      | zero => simp
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]
      | tmul a₀ b =>
        rw [TensorProduct.smul_tmul', pushoutTensorEquiv_tmul, pushoutTensorEquiv_tmul,
          smul_eq_mul, map_mul, mul_assoc]
        rfl }

lemma sectionsPushoutEquiv_tmul (U : Y.Opens) (hU : IsAffineOpen U) (W' : (YT).Opens)
    (hW' : W' = pY ⁻¹ᵁ U) (a : Γ(Y, U)) (b : Γ(T, ⊤)) :
    letI := ((pY).appLE U W' hW'.le).hom.toAlgebra
    sectionsPushoutEquiv U hU W' hW' (a ⊗ₜ b) =
      algebraMap Γ(Y, U) Γ(YT, W') a * algebraMap Γ(T, ⊤) Γ(YT, W') b :=
  pushoutTensorEquiv_tmul _ a b

lemma appLE_eq_of_eq {X X' : Scheme.{u}} {f g : X ⟶ X'} (h : f = g) (U : X'.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

omit [IsAffine S] [IsAffine T] in
/-- The two structure maps `Γ(S) → Γ(Y_T, W')` agree (`pullback.condition`). -/
lemma appLE_condition (U : Y.Opens) (W' : (YT).Opens) (hW' : W' ≤ pY ⁻¹ᵁ U) (r : Γ(S, ⊤)) :
    (pY).appLE U W' hW' ((Y ↘ S).appLE ⊤ U (by simp) r) =
      (pullback.snd (Y ↘ S) (T ↘ S)).appLE ⊤ W' (by simp) ((T ↘ S).appLE ⊤ ⊤ (by simp) r) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq pullback.condition]

/-- The pullback `L_T = p^*L` of `L` to `Y_T`. -/
abbrev lineBundleBaseChange (L : Y.Modules) : (YT).Modules := (Scheme.Modules.pullback pY).obj L

variable (L : Y.Modules) [L.IsInvertible]

/-- The base change map `Γ(T) ⊗_{Γ(S)} Γ(L, U) → Γ(L_T, U_T)`, `b ⊗ m ↦ b • (p^* m)|`. -/
def sectionsBaseChangeMap (U : Y.Opens) (W' : (YT).Opens) (hW' : W' = pY ⁻¹ᵁ U) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(L, U) →ₗ[Γ(T, ⊤)] Γ(lineBundleBaseChange (T := T) L, W') :=
  letI : Module Γ(S, ⊤) Γ(lineBundleBaseChange (T := T) L, W') :=
    Module.compHom _ (algebraMap Γ(S, ⊤) Γ(T, ⊤))
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(lineBundleBaseChange (T := T) L, W') :=
    IsScalarTower.of_compHom _ _ _
  LinearMap.liftBaseChange Γ(T, ⊤)
    { toFun := pullbackRes pY L hW'.le
      map_add' := map_add _
      map_smul' r m := by
        rw [smul_sections_def, pullbackRes_smul]
        exact congrArg (· • pullbackRes pY L hW'.le m) (appLE_condition U W' hW'.le r) }

omit [IsAffine S] [IsAffine T] [L.IsInvertible] in
lemma sectionsBaseChangeMap_tmul (U : Y.Opens) (W' : (YT).Opens) (hW' : W' = pY ⁻¹ᵁ U)
    (b : Γ(T, ⊤)) (m : Γ(L, U)) :
    sectionsBaseChangeMap L U W' hW' (b ⊗ₜ m) = b • pullbackRes pY L hW'.le m := by
  simp [sectionsBaseChangeMap, LinearMap.liftBaseChange_tmul]

lemma isAffineOpen_preimage_fst (U : Y.Opens) (hU : IsAffineOpen U) (W' : (YT).Opens)
    (hW' : W' = pY ⁻¹ᵁ U) : IsAffineOpen W' := by
  subst hW'
  haveI : IsAffineHom (T ↘ S) := isAffineHom_of_isAffine _
  haveI : IsAffineHom (pY) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  exact hU.preimage _

/-- **Sections of `L_T` over `U_T`** (`U` affine): `Γ(L_T, U_T) = Γ(T) ⊗_{Γ(S)} Γ(L, U)`. -/
theorem bijective_sectionsBaseChangeMap (U : Y.Opens) (hU : IsAffineOpen U) (W' : (YT).Opens)
    (hW' : W' = pY ⁻¹ᵁ U) : Function.Bijective (sectionsBaseChangeMap L U W' hW') := by
  have hW'aff := isAffineOpen_preimage_fst U hU W' hW'
  letI := ((pY).appLE U W' hW'.le).hom.toAlgebra
  letI : Module Γ(Y, U) Γ(lineBundleBaseChange (T := T) L, W') :=
    Module.compHom _ (algebraMap Γ(Y, U) Γ(YT, W'))
  haveI : IsScalarTower Γ(Y, U) Γ(YT, W') Γ(lineBundleBaseChange (T := T) L, W') :=
    IsScalarTower.of_compHom _ _ _
  letI : Module Γ(S, ⊤) Γ(lineBundleBaseChange (T := T) L, W') :=
    Module.compHom _ (algebraMap Γ(S, ⊤) Γ(T, ⊤))
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(lineBundleBaseChange (T := T) L, W') :=
    IsScalarTower.of_compHom _ _ _
  haveI : IsScalarTower Γ(S, ⊤) Γ(Y, U) Γ(lineBundleBaseChange (T := T) L, W') := by
    refine ⟨fun r a n ↦ ?_⟩
    change (algebraMap Γ(Y, U) Γ(YT, W') (algebraMap Γ(S, ⊤) Γ(Y, U) r * a)) • n =
      algebraMap Γ(T, ⊤) Γ(YT, W') (algebraMap Γ(S, ⊤) Γ(T, ⊤) r) •
        algebraMap Γ(Y, U) Γ(YT, W') a • n
    rw [map_mul, mul_smul]
    exact congrArg (· • (algebraMap Γ(Y, U) Γ(YT, W') a • n)) (appLE_condition U W' hW'.le r)
  have hθ := isBaseChange_pullbackRes pY L hW'.le hU hW'aff
  have := bijective_baseChangeMap (R₀ := Γ(S, ⊤)) (R₀' := Γ(T, ⊤)) (pullbackResₗ pY L hW'.le)
    hθ (sectionsPushoutEquiv U hU W' hW') (sectionsPushoutEquiv_tmul U hU W' hW')
  have heq : ∀ x, sectionsBaseChangeMap L U W' hW' x =
      baseChangeMap (R₀ := Γ(S, ⊤)) (pullbackResₗ pY L hW'.le) x := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b m => rw [sectionsBaseChangeMap_tmul, baseChangeMap_tmul]; rfl
  rwa [show ⇑(sectionsBaseChangeMap L U W' hW') =
    ⇑(baseChangeMap (R₀ := Γ(S, ⊤)) (pullbackResₗ pY L hW'.le)) from funext heq]

/-- **Sections of `L_T` over affines**: `Γ(T) ⊗_{Γ(S)} Γ(L, U) ≃ Γ(L_T, U_T)`. -/
def sectionsBaseChangeL (U : Y.Opens) (hU : IsAffineOpen U) (W' : (YT).Opens)
    (hW' : W' = pY ⁻¹ᵁ U) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(L, U) ≃ₗ[Γ(T, ⊤)] Γ(lineBundleBaseChange (T := T) L, W') :=
  LinearEquiv.ofBijective _ (bijective_sectionsBaseChangeMap L U hU W' hW')

lemma sectionsBaseChangeL_tmul (U : Y.Opens) (hU : IsAffineOpen U) (W' : (YT).Opens)
    (hW' : W' = pY ⁻¹ᵁ U) (b : Γ(T, ⊤)) (m : Γ(L, U)) :
    sectionsBaseChangeL L U hU W' hW' (b ⊗ₜ m) = b • pullbackRes pY L hW'.le m :=
  sectionsBaseChangeMap_tmul L U W' hW' b m

/-- The identifications `sectionsBaseChangeL` commute with restrictions. -/
lemma sectionsBaseChangeL_comp_res {U₁ U₂ : Y.Opens} (h₁ : IsAffineOpen U₁)
    (h₂ : IsAffineOpen U₂) (h : U₂ ≤ U₁) (W₁ W₂ : (YT).Opens) (hW₁ : W₁ = pY ⁻¹ᵁ U₁)
    (hW₂ : W₂ = pY ⁻¹ᵁ U₂) (h' : W₂ ≤ W₁) :
    resModLin T (lineBundleBaseChange (T := T) L) h' ∘ₗ
        (sectionsBaseChangeL L U₁ h₁ W₁ hW₁).toLinearMap =
      (sectionsBaseChangeL L U₂ h₂ W₂ hW₂).toLinearMap ∘ₗ
        (resModLin S L h).baseChange Γ(T, ⊤) := by
  refine LinearMap.ext fun x ↦ ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | tmul b m =>
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, sectionsBaseChangeL_tmul, sectionsBaseChangeL_tmul,
      (resModLin T (lineBundleBaseChange (T := T) L) h').map_smul, resModLin_apply,
      resModLin_apply, ← pullbackRes_res pY L hW₁.le h h' hW₂.le]

/-! ### Čech cohomology of `L_T` -/

section CechComplex

variable (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))

include hU hUV in
lemma comp_res_left :
    (resModLin S L (inf_le_left : U ⊓ V ≤ U)).baseChange Γ(T, ⊤) ∘ₗ
        (sectionsBaseChangeL L U hU _ rfl).symm.toLinearMap =
      (sectionsBaseChangeL L (U ⊓ V) hUV (pY ⁻¹ᵁ U ⊓ pY ⁻¹ᵁ V) rfl).symm.toLinearMap ∘ₗ
        resModLin T (lineBundleBaseChange (T := T) L) (inf_le_left : pY ⁻¹ᵁ U ⊓ pY ⁻¹ᵁ V ≤ _) :=
  symm_comp_of_comp_eq _ _ _ _ (sectionsBaseChangeL_comp_res L hU hUV inf_le_left _ _ rfl rfl _)

include hV hUV in
lemma comp_res_right :
    (resModLin S L (inf_le_right : U ⊓ V ≤ V)).baseChange Γ(T, ⊤) ∘ₗ
        (sectionsBaseChangeL L V hV _ rfl).symm.toLinearMap =
      (sectionsBaseChangeL L (U ⊓ V) hUV (pY ⁻¹ᵁ U ⊓ pY ⁻¹ᵁ V) rfl).symm.toLinearMap ∘ₗ
        resModLin T (lineBundleBaseChange (T := T) L) (inf_le_right : pY ⁻¹ᵁ U ⊓ pY ⁻¹ᵁ V ≤ _) :=
  symm_comp_of_comp_eq _ _ _ _ (sectionsBaseChangeL_comp_res L hV hUV inf_le_right _ _ rfl rfl _)

/-- Čech `H⁰` of `L_T` for `(U_T, V_T)` is `H⁰` of the base change of the Čech data of `L`. -/
def lineBundleH0BaseChange :
    cechModH0 T (lineBundleBaseChange (T := T) L) (pY ⁻¹ᵁ U) (pY ⁻¹ᵁ V) ≃ₗ[Γ(T, ⊤)]
      TwoCech.H0 ((resModLin S L (inf_le_left : U ⊓ V ≤ U)).baseChange Γ(T, ⊤))
        ((resModLin S L (inf_le_right : U ⊓ V ≤ V)).baseChange Γ(T, ⊤)) :=
  TwoCech.equivH0 (sectionsBaseChangeL L U hU _ rfl).symm (sectionsBaseChangeL L V hV _ rfl).symm
    (sectionsBaseChangeL L (U ⊓ V) hUV _ rfl).symm (comp_res_left L U V hU hUV)
    (comp_res_right L U V hV hUV)

/-- Čech `H¹` of `L_T` for `(U_T, V_T)` is `H¹` of the base change of the Čech data of `L`. -/
def lineBundleH1BaseChange :
    cechModH1 T (lineBundleBaseChange (T := T) L) (pY ⁻¹ᵁ U) (pY ⁻¹ᵁ V) ≃ₗ[Γ(T, ⊤)]
      TwoCech.H1 ((resModLin S L (inf_le_left : U ⊓ V ≤ U)).baseChange Γ(T, ⊤))
        ((resModLin S L (inf_le_right : U ⊓ V ≤ V)).baseChange Γ(T, ⊤)) :=
  TwoCech.equivH1 (sectionsBaseChangeL L U hU _ rfl).symm (sectionsBaseChangeL L V hV _ rfl).symm
    (sectionsBaseChangeL L (U ⊓ V) hUV _ rfl).symm (comp_res_left L U V hU hUV)
    (comp_res_right L U V hV hUV)

/-- `H¹` of `L_T` is the base change of `H¹` of `L` (right exactness; no flatness needed). -/
def lineBundleH1BaseChange' :
    cechModH1 T (lineBundleBaseChange (T := T) L) (pY ⁻¹ᵁ U) (pY ⁻¹ᵁ V) ≃ₗ[Γ(T, ⊤)]
      Γ(T, ⊤) ⊗[Γ(S, ⊤)] cechModH1 S L U V :=
  lineBundleH1BaseChange L U V hU hV hUV ≪≫ₗ TwoCech.H1BaseChangeEquiv _ _ _

end CechComplex

end CurvesJacobian.Cech

namespace CurvesJacobian.Cech

variable {S Y : Scheme.{u}} [Y.Over S] [IsAffine S] (L : Y.Modules) [L.IsInvertible]

omit [IsAffine S] in
/-- Sections of an invertible sheaf over an affine open `U` of `Y` are flat over `Γ(S)` if
`Γ(Y, U)` is. -/
theorem flat_sections {U : Y.Opens} (hU : IsAffineOpen U) [Module.Flat Γ(S, ⊤) Γ(Y, U)] :
    Module.Flat Γ(S, ⊤) Γ(L, U) :=
  haveI := projective_sections L hU
  Module.Flat.trans Γ(S, ⊤) Γ(Y, U) Γ(L, U)

/-- **Cohomology and base change for line bundles on a scheme covered by two affines**
(Stacks, Lemma 36.30.4, Tag 0B91, in the Čech form): let `Γ(S)` be Noetherian, `L` invertible
on `Y`, `U`, `V`, `U ∩ V` affine with `Γ(Y, U)`, `Γ(Y, V)`, `Γ(Y, U ∩ V)` flat over `Γ(S)`, and
the Čech `H⁰`, `H¹` of `L` finite over `Γ(S)`. Then there is a map `δ : K₀ → K₁` of finite
projective `Γ(S)`-modules such that for every affine `S`-scheme `T` the Čech cohomology of
`L_T` for the covering `(U_T, V_T)` is the kernel and cokernel of `Γ(T) ⊗ δ`. -/
theorem exists_finite_projective_lineBundle [IsNoetherianRing Γ(S, ⊤)] (U V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    [Module.Flat Γ(S, ⊤) Γ(Y, U)] [Module.Flat Γ(S, ⊤) Γ(Y, V)]
    [Module.Flat Γ(S, ⊤) Γ(Y, U ⊓ V)]
    (h0 : Module.Finite Γ(S, ⊤) (cechModH0 S L U V))
    (h1 : Module.Finite Γ(S, ⊤) (cechModH1 S L U V)) :
    ∃ (K₀ K₁ : ModuleCat.{u} Γ(S, ⊤)) (δ : K₀ →ₗ[Γ(S, ⊤)] K₁),
      Module.Finite Γ(S, ⊤) K₀ ∧ Module.Projective Γ(S, ⊤) K₀ ∧
      Module.Finite Γ(S, ⊤) K₁ ∧ Module.Free Γ(S, ⊤) K₁ ∧
      ∀ (T : Scheme.{u}) [T.Over S] [IsAffine T],
        Nonempty (LinearMap.ker (δ.baseChange Γ(T, ⊤)) ≃ₗ[Γ(T, ⊤)]
          cechModH0 T (lineBundleBaseChange (T := T) L)
            (pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ U) (pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ V)) ∧
        Nonempty (((Γ(T, ⊤) ⊗[Γ(S, ⊤)] K₁) ⧸ LinearMap.range (δ.baseChange Γ(T, ⊤))) ≃ₗ[Γ(T, ⊤)]
          cechModH1 T (lineBundleBaseChange (T := T) L)
            (pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ U) (pullback.fst (Y ↘ S) (T ↘ S) ⁻¹ᵁ V)) := by
  haveI := flat_sections (S := S) L hU
  haveI := flat_sections (S := S) L hV
  haveI := flat_sections (S := S) L hUV
  obtain ⟨K₀, K₁, δ, hK₀, hK₀', hK₁, hK₁', H⟩ :=
    TwoTerm.exists_finite_projective_twoCech (resModLin S L (inf_le_left : U ⊓ V ≤ U))
      (resModLin S L (inf_le_right : U ⊓ V ≤ V)) h0 h1
  refine ⟨K₀, K₁, δ, hK₀, hK₀', hK₁, hK₁', fun T _ _ ↦ ?_⟩
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := H Γ(T, ⊤)
  exact ⟨⟨e₀ ≪≫ₗ (lineBundleH0BaseChange L U V hU hV hUV).symm⟩,
    ⟨e₁ ≪≫ₗ (lineBundleH1BaseChange L U V hU hV hUV).symm⟩⟩

end CurvesJacobian.Cech
