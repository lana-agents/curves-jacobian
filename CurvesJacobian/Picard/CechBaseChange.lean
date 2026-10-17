/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.TwoCech
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Two-set Čech `H¹` of the structure sheaf commutes with affine base change

Let `f : X ⟶ S` with `S` affine and let `U`, `V` be affine opens of `X` with affine
intersection. The ordered Čech complex of the covering `(U, V)` of `U ∪ V` with coefficients in
`𝒪_X` is the `Γ(S)`-linear map `Γ(U) × Γ(V) → Γ(U ∩ V)` (`FormalSchemes.TwoCech`); write
`Ȟ¹(U, V; 𝒪_X)` for its cokernel (`CurvesJacobian.cechH1`).

For any morphism `g : T ⟶ S` with `T` affine, the sections of `X_T = X ×_S T` over the preimages
of `U`, `V`, `U ∩ V` are the base changes `Γ(T) ⊗_{Γ(S)} Γ(-)` (Mathlib's
`isIso_pushoutSection_of_isAffineOpen`), compatibly with restrictions. Since cokernels commute
with base change (right exactness of `⊗`, no flatness needed), we get
`Ȟ¹(U_T, V_T; 𝒪_{X_T}) ≅ Γ(T) ⊗_{Γ(S)} Ȟ¹(U, V; 𝒪_X)` (`CurvesJacobian.cechH1BaseChange`): the
algebraic content of cohomology and base change for the top cohomology of a curve
(Stacks, Tag 0B91 / Lemma 30.5.2 for `H¹`, here with an explicit two-term Čech complex).

* `TwoCech.H1BaseChangeEquiv`: `H¹` of the base-changed data is the base change of `H¹`.
* `CurvesJacobian.pushoutTensorEquiv`: the ring isomorphism `B ⊗_A R ≅ D` of a pushout square.
-/

open CategoryTheory Limits TopologicalSpace TensorProduct AlgebraicGeometry

universe u

noncomputable section

namespace TwoCech

variable {A : Type*} [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
variable {P Q R : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  [AddCommGroup R] [Module A R] (f : P →ₗ[A] R) (g : Q →ₗ[A] R)

lemma d_baseChange :
    d (f.baseChange B) (g.baseChange B) =
      (d f g).baseChange B ∘ₗ (TensorProduct.prodRight A B B P Q).symm.toLinearMap := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rw [← (TensorProduct.prodRight A B B P Q).apply_symm_apply (x, y)]
  generalize (TensorProduct.prodRight A B B P Q).symm (x, y) = z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction z with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b p => simp [TensorProduct.tmul_sub]

lemma range_d_baseChange :
    LinearMap.range (d (f.baseChange B) (g.baseChange B)) =
      LinearMap.range ((d f g).baseChange B) := by
  rw [d_baseChange, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (TensorProduct.prodRight A B B P Q).symm.surjective

lemma range_d_baseChange_eq_range_lTensor :
    LinearMap.range (d (f.baseChange B) (g.baseChange B)) =
      LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor B B
        ((LinearMap.range (d f g)).subtype.restrictScalars A)) := by
  rw [range_d_baseChange]
  have h : (d f g).baseChange B = TensorProduct.AlgebraTensorModule.lTensor B B
      ((LinearMap.range (d f g)).subtype.restrictScalars A) ∘ₗ
      TensorProduct.AlgebraTensorModule.lTensor B B (d f g).rangeRestrict := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    rfl
  rw [h, LinearMap.range_comp_of_range_eq_top]
  rw [LinearMap.range_eq_top]
  exact LinearMap.lTensor_surjective B (LinearMap.surjective_rangeRestrict _)

/-- `H¹` of two-set Čech data commutes with base change: `H¹(f_B, g_B) ≅ B ⊗_A H¹(f, g)`. -/
def H1BaseChangeEquiv :
    H1 (f.baseChange B) (g.baseChange B) ≃ₗ[B] B ⊗[A] H1 f g :=
  Submodule.quotEquivOfEq _ _ (range_d_baseChange_eq_range_lTensor B f g) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv B A B (LinearMap.range (d f g))).symm

@[simp]
lemma H1BaseChangeEquiv_mk_tmul (b : B) (r : R) :
    H1BaseChangeEquiv B f g (Submodule.Quotient.mk (b ⊗ₜ r)) =
      b ⊗ₜ Submodule.Quotient.mk r := rfl

end TwoCech

namespace CurvesJacobian

section PushoutTensor

variable {A R B D : CommRingCat.{u}} {φ : A ⟶ R} {ψ : A ⟶ B} {φ' : R ⟶ D} {ψ' : B ⟶ D}

/-- The ring isomorphism `B ⊗_A R ≅ D` of a pushout square of commutative rings. -/
def pushoutTensorEquiv (h : IsPushout ψ φ ψ' φ') :
    letI := ψ.hom.toAlgebra; letI := φ.hom.toAlgebra; B ⊗[A] R ≃+* D :=
  letI := ψ.hom.toAlgebra; letI := φ.hom.toAlgebra
  ((CommRingCat.isPushout_tensorProduct A B R).isoPushout ≪≫
    h.isoPushout.symm).commRingCatIsoToRingEquiv

lemma pushoutTensorEquiv_tmul (h : IsPushout ψ φ ψ' φ') (b : B) (r : R) :
    letI := ψ.hom.toAlgebra; letI := φ.hom.toAlgebra
    pushoutTensorEquiv h (b ⊗ₜ r) = ψ' b * φ' r := by
  letI := ψ.hom.toAlgebra; letI := φ.hom.toAlgebra
  have hl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      B →+* B ⊗[A] R) ≫ ((CommRingCat.isPushout_tensorProduct A B R).isoPushout ≪≫
        h.isoPushout.symm).hom = ψ' := by
    simp
  have hr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      R →ₐ[A] B ⊗[A] R).toRingHom ≫ ((CommRingCat.isPushout_tensorProduct A B R).isoPushout ≪≫
        h.isoPushout.symm).hom = φ' := by
    simp
  have e : b ⊗ₜ[A] r = (b ⊗ₜ[A] (1 : R)) * ((1 : B) ⊗ₜ[A] r) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hl' := ConcreteCategory.congr_hom hl b
  have hr' := ConcreteCategory.congr_hom hr r
  rw [e, map_mul, ← hl', ← hr']
  rfl

end PushoutTensor

namespace Cech

variable {S : Scheme.{u}}

/-- For `X` over `S`, the sections of `X` over any open are a `Γ(S, ⊤)`-algebra. -/
scoped instance sectionsAlgebra (X : Scheme.{u}) [X.Over S] (W : X.Opens) :
    Algebra Γ(S, ⊤) Γ(X, W) :=
  ((X ↘ S).appLE ⊤ W (by simp)).hom.toAlgebra

lemma algebraMap_sections (X : Scheme.{u}) [X.Over S] (W : X.Opens) :
    algebraMap Γ(S, ⊤) Γ(X, W) = ((X ↘ S).appLE ⊤ W (by simp)).hom := rfl

/-- Restriction of sections, as a `Γ(S, ⊤)`-linear map. -/
def resLin (S : Scheme.{u}) (X : Scheme.{u}) [X.Over S] {W W' : X.Opens} (h : W' ≤ W) :
    Γ(X, W) →ₗ[Γ(S, ⊤)] Γ(X, W') :=
  AlgHom.toLinearMap
    { (X.presheaf.map (homOfLE h).op).hom with
      commutes' := fun r ↦ by
        change ((X ↘ S).appLE ⊤ W (by simp) ≫ X.presheaf.map (homOfLE h).op) r = _
        rw [Scheme.Hom.appLE_map]
        rfl }

@[simp]
lemma resLin_apply (S : Scheme.{u}) (X : Scheme.{u}) [X.Over S] {W W' : X.Opens} (h : W' ≤ W)
    (s : Γ(X, W)) : resLin S X h s = X.presheaf.map (homOfLE h).op s := rfl

/-- The two-set Čech `H¹` of `𝒪_X` for opens `U`, `V` of `X` (computing `H¹(U ∪ V, 𝒪_X)` when
`U`, `V` and `U ∩ V` are affine and `X` is separated), as a `Γ(S, ⊤)`-module. -/
abbrev cechH1 (S : Scheme.{u}) (X : Scheme.{u}) [X.Over S] (U V : X.Opens) : Type u :=
  TwoCech.H1 (resLin S X (inf_le_left : U ⊓ V ≤ U)) (resLin S X (inf_le_right : U ⊓ V ≤ V))

variable {X T : Scheme.{u}} [X.Over S] [T.Over S] [IsAffine S] [IsAffine T]

local notation "XT" => pullback (X ↘ S) (T ↘ S)

lemma isPushout_sections (W : X.Opens) (hW : IsAffineOpen W) (W' : (XT).Opens)
    (hW' : W' = pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ W) :
    IsPushout ((T ↘ S).appLE ⊤ ⊤ (by simp)) ((X ↘ S).appLE ⊤ W (by simp))
      ((pullback.snd (X ↘ S) (T ↘ S)).appLE ⊤ W' (by simp))
      ((pullback.fst (X ↘ S) (T ↘ S)).appLE W W' hW'.le) := by
  have H := IsPullback.of_hasPullback (X ↘ S) (T ↘ S)
  have hUY : W' = pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ W ⊓ pullback.snd (X ↘ S) (T ↘ S) ⁻¹ᵁ ⊤ := by
    simp [hW']
  exact ((isIso_pushoutSection_iff H (show (⊤ : T.Opens) ≤ (T ↘ S) ⁻¹ᵁ ⊤ by simp)
    (show W ≤ (X ↘ S) ⁻¹ᵁ ⊤ by simp) hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ hUY (isAffineOpen_top S) (isAffineOpen_top T)
      hW)).flip

/-- Sections of `X_T = X ×_S T` over the preimage of an affine open `W ⊆ X` are
`Γ(T) ⊗_{Γ(S)} Γ(X, W)`. -/
def sectionsBaseChangeEquiv (W : X.Opens) (hW : IsAffineOpen W) (W' : (XT).Opens)
    (hW' : W' = pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ W) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X, W) ≃ₗ[Γ(T, ⊤)] Γ(XT, W') where
  __ := pushoutTensorEquiv (isPushout_sections W hW W' hW')
  map_smul' b x := by
    rw [Algebra.smul_def, Algebra.smul_def]
    change pushoutTensorEquiv _ (_ * x) = _ * pushoutTensorEquiv _ x
    rw [map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      pushoutTensorEquiv_tmul, map_one, mul_one]
    rfl

lemma sectionsBaseChangeEquiv_tmul (W : X.Opens) (hW : IsAffineOpen W) (W' : (XT).Opens)
    (hW' : W' = pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ W) (b : Γ(T, ⊤)) (r : Γ(X, W)) :
    sectionsBaseChangeEquiv W hW W' hW' (b ⊗ₜ r) =
      (pullback.snd (X ↘ S) (T ↘ S)).appLE ⊤ W' (by simp) b *
        (pullback.fst (X ↘ S) (T ↘ S)).appLE W W' hW'.le r :=
  pushoutTensorEquiv_tmul _ b r

/-- The identifications `sectionsBaseChangeEquiv` commute with restrictions. -/
lemma sectionsBaseChangeEquiv_comp_res {W₁ W₂ : X.Opens} (h₁ : IsAffineOpen W₁)
    (h₂ : IsAffineOpen W₂) (h : W₂ ≤ W₁) (W₁' W₂' : (XT).Opens)
    (hW₁' : W₁' = pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ W₁)
    (hW₂' : W₂' = pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ W₂) (h' : W₂' ≤ W₁') :
    resLin T (XT) h' ∘ₗ
        (sectionsBaseChangeEquiv W₁ h₁ W₁' hW₁').toLinearMap =
      (sectionsBaseChangeEquiv W₂ h₂ W₂' hW₂').toLinearMap ∘ₗ
        (resLin S X h).baseChange Γ(T, ⊤) := by
  apply LinearMap.ext
  intro x
  induction x with
  | zero => simp
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply] at hx hy ⊢
    rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b r =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, resLin_apply,
      sectionsBaseChangeEquiv_tmul, map_mul]
    congr 1
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
        Scheme.Hom.map_appLE]

lemma symm_comp_of_comp_eq {M₁ M₂ N₁ N₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [AddCommGroup N₁] [AddCommGroup N₂] {Rg : Type*} [CommRing Rg] [Module Rg M₁] [Module Rg M₂]
    [Module Rg N₁] [Module Rg N₂] (L : N₁ →ₗ[Rg] N₂) (M : M₁ →ₗ[Rg] M₂) (e₁ : M₁ ≃ₗ[Rg] N₁)
    (e₂ : M₂ ≃ₗ[Rg] N₂) (h : L ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ M) :
    M ∘ₗ e₁.symm.toLinearMap = e₂.symm.toLinearMap ∘ₗ L := by
  ext x
  apply e₂.injective
  have := LinearMap.congr_fun h (e₁.symm x)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at this ⊢
  exact this.symm

/-- **Čech `H¹` of `𝒪` commutes with affine base change**: for `X` over an affine `S`, affine
opens `U`, `V` of `X` with affine intersection and an affine `S`-scheme `T`,
`Ȟ¹(U_T, V_T; 𝒪_{X_T}) ≅ Γ(T) ⊗_{Γ(S)} Ȟ¹(U, V; 𝒪_X)` as `Γ(T)`-modules. -/
def cechH1BaseChange (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) :
    cechH1 T (XT) (pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ U) (pullback.fst (X ↘ S) (T ↘ S) ⁻¹ᵁ V)
      ≃ₗ[Γ(T, ⊤)] Γ(T, ⊤) ⊗[Γ(S, ⊤)] cechH1 S X U V :=
  TwoCech.equivH1 (sectionsBaseChangeEquiv U hU _ rfl).symm
      (sectionsBaseChangeEquiv V hV _ rfl).symm
      (sectionsBaseChangeEquiv (U ⊓ V) hUV _ rfl).symm
      (symm_comp_of_comp_eq _ _ _ _ (sectionsBaseChangeEquiv_comp_res hU hUV inf_le_left _ _
        rfl rfl ((pullback.fst (X ↘ S) (T ↘ S)).preimage_mono inf_le_left)))
      (symm_comp_of_comp_eq _ _ _ _ (sectionsBaseChangeEquiv_comp_res hV hUV inf_le_right _ _
        rfl rfl ((pullback.fst (X ↘ S) (T ↘ S)).preimage_mono inf_le_right))) ≪≫ₗ
    TwoCech.H1BaseChangeEquiv _ _ _

end Cech

end CurvesJacobian
