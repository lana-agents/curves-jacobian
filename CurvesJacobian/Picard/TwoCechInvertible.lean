/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CechLineBundle
import Mathlib.RingTheory.PicardGroup

/-!
# Cohomology concentrated in degree `0` and invertible is stable under base change

Let `δ : C₀ → C₁` be a linear map of `A`-modules with `C₁` flat. If `δ` is surjective, then
`0 → ker δ → C₀ → C₁ → 0` stays exact after any base change `A → B`, so
`B ⊗_A ker δ ≅ ker (B ⊗ δ)` (`TwoTerm.kerBaseChangeEquiv`). Hence the condition
"`coker δ = 0` and `ker δ` is an invertible `A`-module" is stable under base change
(`TwoTerm.surjective_baseChange`, `TwoTerm.invertible_ker_baseChange`); no finiteness or
Noetherian hypotheses are needed.

Applied to the two-set Čech differential, this gives `TwoCech.IsInvertibleH0`, stable under
base change (`TwoCech.IsInvertibleH0.baseChange`), and for an invertible sheaf `L` on a scheme
`Y` over an affine `S` with a covering by affine opens `U`, `V` (with `U ∩ V` affine and
`Γ(Y, U ∩ V)` flat over `Γ(S)`), the predicate `Cech.IsFPoint S L U V` ("the Čech `H¹` of `L`
vanishes and the Čech `H⁰` is an invertible `Γ(S)`-module"), which is stable under base change
to affine `S`-schemes `T` (`Cech.IsFPoint.baseChange`). This is the defining condition of the
subfunctor `F ⊆ Pic_{X/k,σ}` of Stacks, Lemma 44.6.2 (Tag 0B9V): `R f_{T,*} L` is an invertible
module placed in degree `0`, compatibly with base change (Stacks, Lemma 36.30.4, Tag 0B91).
-/

open TensorProduct LinearMap

universe u v

noncomputable section

namespace CurvesJacobian.TwoTerm

variable {A : Type u} [CommRing A] {C₀ C₁ : Type u} [AddCommGroup C₀] [Module A C₀]
  [AddCommGroup C₁] [Module A C₁] (δ : C₀ →ₗ[A] C₁)
  (B : Type v) [CommRing B] [Algebra A B]

/-- Base change preserves surjectivity. -/
theorem surjective_baseChange (h : Function.Surjective δ) :
    Function.Surjective (δ.baseChange B) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective B h

/-- The base change of the inclusion `ker δ → C₀` lands in `ker (B ⊗ δ)`. -/
def kerBaseChangeMap : B ⊗[A] ker δ →ₗ[B] ker (δ.baseChange B) :=
  ((ker δ).subtype.baseChange B).codRestrict _ fun x ↦ by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have : δ ∘ₗ (ker δ).subtype = 0 := by ext x; exact x.2
    rw [this, LinearMap.baseChange_zero, LinearMap.zero_apply]

@[simp]
lemma kerBaseChangeMap_tmul (b : B) (x : ker δ) :
    (kerBaseChangeMap δ B (b ⊗ₜ x) : B ⊗[A] C₀) = b ⊗ₜ (x : C₀) := rfl

variable {δ}

/-- If `δ` is surjective and `C₁` is flat, `B ⊗ ker δ → ker (B ⊗ δ)` is bijective. -/
theorem kerBaseChangeMap_bijective [Module.Flat A C₁] (h : Function.Surjective δ) :
    Function.Bijective (kerBaseChangeMap δ B) := by
  have hex : Function.Exact (ker δ).subtype δ := LinearMap.exact_subtype_ker_map δ
  have hinj : Function.Injective ((ker δ).subtype.baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_injective_of_exact_of_flat _ h _ (ker δ).injective_subtype hex B
  have hex' : Function.Exact ((ker δ).subtype.baseChange B) (δ.baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact _root_.lTensor_exact B hex h
  refine ⟨fun x y hxy ↦ hinj (congrArg Subtype.val hxy), fun ⟨y, hy⟩ ↦ ?_⟩
  obtain ⟨x, hx⟩ := (hex' y).mp hy
  exact ⟨x, Subtype.ext hx⟩

/-- **Base change of the kernel of a surjection onto a flat module**:
`B ⊗_A ker δ ≃ ker (B ⊗ δ)`. -/
def kerBaseChangeEquiv [Module.Flat A C₁] (h : Function.Surjective δ) :
    B ⊗[A] ker δ ≃ₗ[B] ker (δ.baseChange B) :=
  LinearEquiv.ofBijective _ (kerBaseChangeMap_bijective B h)

/-- The kernel of a surjection between flat modules is flat. -/
theorem flat_ker [Module.Flat A C₀] [Module.Flat A C₁] (h : Function.Surjective δ) :
    Module.Flat A (ker δ) :=
  flat_of_ker (ker δ).subtype δ (ker δ).injective_subtype h (LinearMap.exact_subtype_ker_map δ)

/-- If `δ` is surjective onto a flat module and `ker δ` is invertible, then `ker (B ⊗ δ)` is
an invertible `B`-module. -/
theorem invertible_ker_baseChange [Module.Flat A C₁] (h : Function.Surjective δ)
    [Module.Invertible A (ker δ)] : Module.Invertible B (ker (δ.baseChange B)) :=
  .congr (kerBaseChangeEquiv B h)

end CurvesJacobian.TwoTerm

namespace CurvesJacobian.TwoTerm

variable {A : Type u} [CommRing A] {P Q R : Type u} [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q] [AddCommGroup R] [Module A R] (f : P →ₗ[A] R) (g : Q →ₗ[A] R)

/-- Two-set Čech data whose cohomology is an invertible module placed in degree `0`:
`H¹ = 0` and `H⁰` is an invertible `A`-module. -/
def IsInvertibleH0 : Prop :=
  Subsingleton (TwoCech.H1 f g) ∧ Module.Invertible A (TwoCech.H0 f g)

lemma subsingleton_H1_iff :
    Subsingleton (TwoCech.H1 f g) ↔ Function.Surjective (TwoCech.d f g) := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

variable {f g}

/-- If `H¹ = 0` and the overlap term is flat, `H⁰` commutes with base change:
`H⁰(f_B, g_B) ≃ B ⊗_A H⁰(f, g)`. -/
def H0BaseChangeEquivTensor [Module.Flat A R] (h : Subsingleton (TwoCech.H1 f g))
    (B : Type u) [CommRing B] [Algebra A B] :
    TwoCech.H0 (f.baseChange B) (g.baseChange B) ≃ₗ[B] B ⊗[A] TwoCech.H0 f g :=
  (H0BaseChangeEquiv f g B).symm ≪≫ₗ
    (kerBaseChangeEquiv B ((subsingleton_H1_iff f g).mp h)).symm

/-- **The condition "`H¹ = 0` and `H⁰` invertible" is stable under base change** when the
overlap term is flat (the defining condition of Stacks, Lemma 44.6.2, Tag 0B9V, in two-set Čech
form; cf. Stacks, Lemma 36.30.4, Tag 0B91). -/
theorem IsInvertibleH0.baseChange [Module.Flat A R] (h : IsInvertibleH0 f g)
    (B : Type u) [CommRing B] [Algebra A B] :
    IsInvertibleH0 (f.baseChange B) (g.baseChange B) := by
  obtain ⟨h1, h0⟩ := h
  rw [subsingleton_H1_iff] at h1
  refine ⟨?_, ?_⟩
  · rw [subsingleton_H1_iff, TwoCech.d_baseChange, LinearMap.coe_comp]
    exact (surjective_baseChange _ B h1).comp (LinearEquiv.surjective _)
  · haveI := invertible_ker_baseChange B h1
    exact .congr (H0BaseChangeEquiv f g B)

end CurvesJacobian.TwoTerm

open CategoryTheory Limits AlgebraicGeometry

namespace CurvesJacobian.Cech

variable {S Y : Scheme.{u}} [Y.Over S]

variable (S) in
/-- **The `F`-condition of Stacks, Lemma 44.6.2 (Tag 0B9V)**, in two-set Čech form: for the
covering `(U, V)`, the Čech `H¹` of `L` vanishes and the Čech `H⁰` is an invertible
`Γ(S)`-module, i.e. `R f_* L` is an invertible module placed in degree `0`. -/
def IsFPoint (L : Y.Modules) (U V : Y.Opens) : Prop :=
  TwoTerm.IsInvertibleH0 (resModLin S L (inf_le_left : U ⊓ V ≤ U))
    (resModLin S L (inf_le_right : U ⊓ V ≤ V))

lemma isFPoint_iff (L : Y.Modules) (U V : Y.Opens) :
    IsFPoint S L U V ↔
      Subsingleton (cechModH1 S L U V) ∧ Module.Invertible Γ(S, ⊤) (cechModH0 S L U V) :=
  Iff.rfl

variable [IsAffine S] {T : Scheme.{u}} [T.Over S] [IsAffine T] (L : Y.Modules) [L.IsInvertible]
  {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))

local notation "pY" => pullback.fst (Y ↘ S) (T ↘ S)

include hU hV hUV in
/-- **Stability of the `F`-condition under base change** (Stacks, Lemma 44.6.2, Tag 0B9V;
cohomology and base change, Stacks, Lemma 36.30.4, Tag 0B91): let `L` be invertible on `Y`
over an affine `S`, `U`, `V`, `U ∩ V` affine with `Γ(Y, U ∩ V)` flat over `Γ(S)`. If the Čech
`H¹` of `L` for `(U, V)` vanishes and its `H⁰` is invertible over `Γ(S)`, the same holds for
`L_T` and `(U_T, V_T)` for every affine `S`-scheme `T`. -/
theorem IsFPoint.baseChange [Module.Flat Γ(S, ⊤) Γ(Y, U ⊓ V)] (h : IsFPoint S L U V) :
    IsFPoint T (lineBundleBaseChange (T := T) L) (pY ⁻¹ᵁ U) (pY ⁻¹ᵁ V) := by
  haveI := flat_sections (S := S) L hUV
  obtain ⟨h1, h0⟩ := TwoTerm.IsInvertibleH0.baseChange h Γ(T, ⊤)
  exact ⟨(lineBundleH1BaseChange L U V hU hV hUV).toEquiv.subsingleton_congr.mpr h1,
    .congr (lineBundleH0BaseChange L U V hU hV hUV).symm⟩

include hU hV hUV in
/-- Under the `F`-condition, `H⁰` of `L_T` is the base change of `H⁰` of `L`:
`H⁰(L_T) ≃ Γ(T) ⊗_{Γ(S)} H⁰(L)`. -/
def lineBundleH0BaseChange' [Module.Flat Γ(S, ⊤) Γ(Y, U ⊓ V)]
    (h : Subsingleton (cechModH1 S L U V)) :
    cechModH0 T (lineBundleBaseChange (T := T) L) (pY ⁻¹ᵁ U) (pY ⁻¹ᵁ V) ≃ₗ[Γ(T, ⊤)]
      Γ(T, ⊤) ⊗[Γ(S, ⊤)] cechModH0 S L U V :=
  haveI := flat_sections (S := S) L hUV
  lineBundleH0BaseChange L U V hU hV hUV ≪≫ₗ TwoTerm.H0BaseChangeEquivTensor h Γ(T, ⊤)

end CurvesJacobian.Cech
