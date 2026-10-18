/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TwistCech
import CurvesJacobian.Picard.CechGlobal
import CurvesJacobian.Picard.PicDegree

/-!
# Sections vanishing at a rational point

Let `S` be the spectrum of a field, `Y` an `S`-scheme covered by two affine opens `U`, `V` with
affine intersection, `σ : S ⟶ Y` a section landing in `U`, and `D` the divisor of `σ`
(ideal `ker σ`). For an invertible sheaf `M` on `Y`:

* `CurvesJacobian.Cech.mem_range_twistLin_of_preimage_eq_bot`: on an affine open `W` missing
  `σ`, every section of `M ⊗ 𝒪(D)` is a twist of a section of `M`;
* **`CurvesJacobian.Cech.eq_zero_of_pullbackRes_eq_zero`**: if `M` has no nonzero global
  sections, a global section of `M ⊗ 𝒪(D)` vanishing at `σ` is zero (it is the twist of a
  global section of `M`, glued from the two charts);
* **`CurvesJacobian.Cech.exists_eq_smul_of_subsingleton`**: hence, if `Γ(Y, M) = 0`, the global
  sections of `M ⊗ 𝒪(D)` form a space of dimension at most one (evaluation at `σ` is injective
  and the fibre of `M ⊗ 𝒪(D)` at `σ` is one-dimensional).

This is the step `h⁰(M(σ)) ≤ h⁰(M) + 1` of Stacks, Lemma 44.6.5 (Tag 0B9Y), without the
hypotheses `H¹ = 0` and `σ ∈ U ∩ V` of `CurvesJacobian.Cech.removePoint`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite Function
open AlgebraicGeometry.Scheme.Modules MonoidalCategory

universe u

noncomputable section

namespace CurvesJacobian.Cech

variable {S Y : Scheme.{u}} [Y.Over S] [IsAffine S] (σ : S ⟶ Y) (hσ : σ ≫ (Y ↘ S) = 𝟙 S)
  {T : Scheme.{u}} {fD : Y ⟶ T} (D : RelEffCartier fD) [QuasiCompact σ] (hD : D.ideal = σ.ker)
  (M : Y.Modules) [M.IsInvertible]

omit [IsAffine S] in
include hD in
/-- On an affine open missing `σ`, twisting by the divisor of `σ` is surjective. -/
lemma mem_range_twistLin_of_preimage_eq_bot {W : Y.Opens} (hW : IsAffineOpen W)
    (hσW : σ ⁻¹ᵁ W = ⊥) (y : Γ(M ⊗ D.lineBundle, W)) :
    y ∈ LinearMap.range (twistLin (S := S) M D.lineBundle D.canonicalSection W) := by
  rw [mem_range_twistLin_iff M D.lineBundle D.canonicalSection hW,
    D.contentIdeal_canonicalSection ⟨W, hW⟩, hD, Scheme.Hom.ker_apply]
  have htop : RingHom.ker (σ.app W).hom = ⊤ := by
    rw [eq_top_iff]
    intro r _
    rw [RingHom.mem_ker]
    haveI : Subsingleton Γ(S, σ ⁻¹ᵁ W) := by rw [hσW]; infer_instance
    exact Subsingleton.elim _ _
  rw [htop, Submodule.top_smul]
  exact Submodule.mem_top

include hσ hD in
/-- On an affine open containing `σ`, the sections of `M ⊗ 𝒪(D)` vanishing at `σ` are twists
of sections of `M`. -/
lemma mem_range_twistLin_of_pullbackRes_eq_zero {W : Y.Opens} (hW : IsAffineOpen W)
    (hσW : ⊤ ≤ σ ⁻¹ᵁ W) (y : Γ(M ⊗ D.lineBundle, W))
    (hy : pullbackRes σ (M ⊗ D.lineBundle) hσW y = 0) :
    y ∈ LinearMap.range (twistLin (S := S) M D.lineBundle D.canonicalSection W) := by
  rw [mem_range_twistLin_iff M D.lineBundle D.canonicalSection hW,
    D.contentIdeal_canonicalSection ⟨W, hW⟩, hD, Scheme.Hom.ker_apply,
    ker_app_eq_ker_appLE σ hσW]
  exact (pullbackRes_eq_zero_iff σ _ hW hσW (surjective_appLE σ hσ hσW) y).mp hy

omit [Y.Over S] [IsAffine S] [QuasiCompact σ] in
/-- Evaluation at `σ` of a section on `W ∋ σ` only depends on its restriction to `W' ∋ σ`. -/
lemma pullbackRes_res_top (L : Y.Modules) {W W' : Y.Opens} (h : W' ≤ W) (hσW : ⊤ ≤ σ ⁻¹ᵁ W)
    (hσW' : ⊤ ≤ σ ⁻¹ᵁ W') (y : Γ(L, W)) :
    pullbackRes σ L hσW' (L.presheaf.map (homOfLE h).op y) = pullbackRes σ L hσW y := by
  have hid : (homOfLE (le_rfl : (⊤ : S.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := rfl
  rw [pullbackRes_res σ L hσW h le_rfl hσW' y, hid, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

/-- An open of the spectrum of a field is empty or everything. -/
lemma opens_eq_bot_or_top (hF : IsField Γ(S, ⊤)) (O : S.Opens) : O = ⊥ ∨ ⊤ ≤ O := by
  haveI := subsingleton_of_isField hF
  by_cases h : ∃ s, s ∈ O
  · obtain ⟨s, hs⟩ := h
    exact Or.inr fun t _ ↦ Subsingleton.elim s t ▸ hs
  · simp only [not_exists] at h
    exact Or.inl (eq_bot_iff.mpr fun s hs ↦ (h s hs).elim)

include hσ hD in
/-- **A global section of `M ⊗ 𝒪(D)` vanishing at `σ` is zero if `Γ(Y, M) = 0`.** -/
theorem eq_zero_of_pullbackRes_eq_zero (hF : IsField Γ(S, ⊤)) {U V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) (hcov : U ⊔ V = ⊤)
    (hσU : ⊤ ≤ σ ⁻¹ᵁ U) (hM : Subsingleton Γ(M, ⊤)) (t : Γ(M ⊗ D.lineBundle, ⊤))
    (ht : pullbackRes σ (M ⊗ D.lineBundle) hσU
      ((M ⊗ D.lineBundle).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) = 0) : t = 0 := by
  have htop : ⊤ ≤ σ ⁻¹ᵁ (⊤ : Y.Opens) := le_top
  have ht0 : pullbackRes σ (M ⊗ D.lineBundle) htop t = 0 := by
    rw [← pullbackRes_res_top σ (M ⊗ D.lineBundle) le_top htop hσU t]
    exact ht
  obtain ⟨a, ha⟩ := mem_range_twistLin_of_pullbackRes_eq_zero σ hσ D hD M hU hσU _ ht
  obtain ⟨b, hb⟩ : (M ⊗ D.lineBundle).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t ∈
      LinearMap.range (twistLin (S := S) M D.lineBundle D.canonicalSection V) := by
    rcases opens_eq_bot_or_top hF (σ ⁻¹ᵁ V) with hσV | hσV
    · exact mem_range_twistLin_of_preimage_eq_bot σ D hD M hV hσV _
    · refine mem_range_twistLin_of_pullbackRes_eq_zero σ hσ D hD M hV hσV _ ?_
      rw [pullbackRes_res_top σ (M ⊗ D.lineBundle) le_top htop hσV t]
      exact ht0
  have hinj : Injective (twistLin (S := S) M D.lineBundle D.canonicalSection (U ⊓ V)) :=
    injective_twistLin M _ _ hUV (D.injective_smul_canonicalSection _)
  have hab : (a, b) ∈ cechModH0 S M U V := by
    rw [TwoCech.mem_H0]
    apply hinj
    have h1 := LinearMap.congr_fun (twistLin_comp_res (S := S) M D.lineBundle
      D.canonicalSection (inf_le_left : U ⊓ V ≤ U)) a
    have h2 := LinearMap.congr_fun (twistLin_comp_res (S := S) M D.lineBundle
      D.canonicalSection (inf_le_right : U ⊓ V ≤ V)) b
    simp only [LinearMap.comp_apply] at h1 h2
    rw [← h1, ← h2, ha, hb]
    change ((M ⊗ D.lineBundle).presheaf.map _ ≫ (M ⊗ D.lineBundle).presheaf.map _) t =
      ((M ⊗ D.lineBundle).presheaf.map _ ≫ (M ⊗ D.lineBundle).presheaf.map _) t
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hzero : (⟨(a, b), hab⟩ : cechModH0 S M U V) = 0 := by
    have := (globalSectionsEquivH0 S M hcov).symm.injective.subsingleton
    exact Subsingleton.elim _ _
  have ha0 : a = 0 := congrArg (fun x : cechModH0 S M U V ↦ x.1.1) hzero
  have hb0 : b = 0 := congrArg (fun x : cechModH0 S M U V ↦ x.1.2) hzero
  apply (globalSectionsEquivH0 S (M ⊗ D.lineBundle) hcov).injective
  rw [map_zero, globalSectionsEquivH0_apply]
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change (M ⊗ D.lineBundle).presheaf.map _ t = 0
    rw [← ha, ha0, map_zero]
  · change (M ⊗ D.lineBundle).presheaf.map _ t = 0
    rw [← hb, hb0, map_zero]

include hσ hD in
/-- **If `Γ(Y, M) = 0`, then `Γ(Y, M ⊗ 𝒪(D))` has dimension at most one.** -/
theorem exists_eq_smul_of_subsingleton (hF : IsField Γ(S, ⊤)) {U V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) (hcov : U ⊔ V = ⊤)
    (hσU : ⊤ ≤ σ ⁻¹ᵁ U) (hM : Subsingleton Γ(M, ⊤)) {t₁ : Γ(M ⊗ D.lineBundle, ⊤)}
    (h₁ : t₁ ≠ 0) (t₂ : Γ(M ⊗ D.lineBundle, ⊤)) : ∃ μ : Γ(S, ⊤), t₂ = μ • t₁ := by
  have hev : ∀ t : Γ(M ⊗ D.lineBundle, ⊤), pullbackRes σ (M ⊗ D.lineBundle) hσU
      ((M ⊗ D.lineBundle).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) = 0 → t = 0 :=
    eq_zero_of_pullbackRes_eq_zero σ hσ D hD M hF hU hV hUV hcov hσU hM
  have hev₁ : pullbackRes σ (M ⊗ D.lineBundle) hσU
      ((M ⊗ D.lineBundle).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t₁) ≠ 0 :=
    fun h ↦ h₁ (hev t₁ h)
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_ne_zero hF ((Scheme.Modules.pullback σ).obj
    (M ⊗ D.lineBundle)) hev₁ (pullbackRes σ (M ⊗ D.lineBundle) hσU
      ((M ⊗ D.lineBundle).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t₂))
  refine ⟨μ, sub_eq_zero.mp (hev _ ?_)⟩
  change pullbackRes σ (M ⊗ D.lineBundle) hσU
    (resModLin S (M ⊗ D.lineBundle) (le_top : U ≤ ⊤) (t₂ - μ • t₁)) = 0
  rw [map_sub, map_sub, LinearMap.map_smul, smul_sections_def, pullbackRes_smul,
    appLE_algebraMap σ hσ hσU]
  exact sub_eq_zero.mpr hμ

end CurvesJacobian.Cech
