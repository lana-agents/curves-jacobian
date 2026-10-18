/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.EulerCharDivisor
import CurvesJacobian.Picard.PicDegreeZero
import CurvesJacobian.Picard.RelEffCartierFinite

/-!
# `deg 𝒪(D) = deg D` on curves over fields (Stacks, Lemma 44.6.7, Tag 0BA0)

For `C` a curve over a perfect field `k`, `T` affine over `k` with `Γ(T)` a field, `M` an
invertible sheaf and `D` a relative effective Cartier divisor on `C ×_k T`,
`χ(M ⊗ 𝒪(D)) = χ(M) + deg D` for the chart Čech complexes
(`CurvesJacobian.chiCurve_add_divisor`). In particular `χ(𝒪(D)) = deg D + 1 − g`, i.e. with the
normalisation of Stacks, Tag 0BA0, `𝒪(D)` has degree `deg D` (`chiCurve_ofDivisor`).
Consequently the degree `χ − (1 − g)` is additive on sums `z + z'` where `z` is a difference of
effective divisor classes (`chiCurve_add_sub_divisor`, `chiCurve_add_of_divisors`).

The divisor `D` is finite over `T` (Stacks, Lemma 44.3.1, Tag 0B9D), so its underlying scheme is
Artinian and `Cech.chi_twist_divisor` applies; `h⁰(D, M(D)|_D) = deg D` is the rank of an
invertible module over the finite flat algebra `Γ(D, 𝒪_D)` (`rankAtStalk_sections_pullback`).
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MonoidalCategory

universe u

noncomputable section

namespace CurvesJacobian

/-- Sections of the restriction of an invertible sheaf to a closed subscheme finite over the
affine `S` form a finite `Γ(S)`-module. -/
lemma finite_sections_pullback_subscheme {S Y : Scheme.{u}} [Y.Over S] [IsAffine S]
    (L : Y.Modules) [L.IsInvertible] (I : Y.IdealSheafData) [IsFinite (I.subschemeι ≫ (Y ↘ S))] :
    letI := ((I.subschemeι ≫ (Y ↘ S)).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) :=
      Module.compHom _ (algebraMap Γ(S, ⊤) Γ(I.subscheme, ⊤))
    Module.Finite Γ(S, ⊤) Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) := by
  letI := ((I.subschemeι ≫ (Y ↘ S)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) :=
    Module.compHom _ (algebraMap Γ(S, ⊤) Γ(I.subscheme, ⊤))
  haveI : IsScalarTower Γ(S, ⊤) Γ(I.subscheme, ⊤)
      Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) := IsScalarTower.of_compHom _ _ _
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ (Y ↘ S))
  haveI := finite_sections ((Scheme.Modules.pullback I.subschemeι).obj L)
    (isAffineOpen_top I.subscheme)
  haveI : Module.Finite Γ(S, ⊤) Γ(I.subscheme, ⊤) := by
    have := Scheme.Hom.finite_appTop (I.subschemeι ≫ (Y ↘ S))
    rw [← appLE_top_eq_appTop] at this
    exact this
  exact Module.Finite.trans Γ(I.subscheme, ⊤) _

open Cech Belyi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k) [PerfectField k] [IsCurveOver k C] [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)

variable {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]

attribute [local instance] subschemeOver

/-- The underlying scheme of a relative effective Cartier divisor on `C ×_k T`, `Γ(T)` a
field, is Artinian. -/
lemma isLocallyArtinian_divisor (hF : IsField Γ(T, ⊤))
    (D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk))) :
    IsLocallyArtinian D.ideal.subscheme := by
  letI := hF.toField
  haveI := D.isFinite C (T ↘ Sk)
  haveI : IsAffine D.ideal.subscheme :=
    isAffine_of_isAffineHom (D.ideal.subschemeι ≫ pullback.snd (C ↘ Sk) (T ↘ Sk))
  letI := ((D.ideal.subschemeι ≫ pullback.snd (C ↘ Sk) (T ↘ Sk)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  haveI : Module.Finite Γ(T, ⊤) Γ(D.ideal.subscheme, ⊤) := by
    have := Scheme.Hom.finite_appTop (D.ideal.subschemeι ≫ pullback.snd (C ↘ Sk) (T ↘ Sk))
    rw [← appLE_top_eq_appTop] at this
    exact this
  haveI : IsArtinianRing Γ(D.ideal.subscheme, ⊤) := IsArtinianRing.of_finite Γ(T, ⊤) _
  haveI : IsLocallyArtinian (Spec Γ(D.ideal.subscheme, ⊤)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact IsLocallyArtinian.of_isImmersion D.ideal.subscheme.isoSpec.hom

/-- **`χ(M ⊗ 𝒪(D)) = χ(M) + deg D`** on `C ×_k T` for `Γ(T)` a field. -/
theorem chiCurve_add_divisor (hF : IsField Γ(T, ⊤))
    (M : (pullback (C ↘ Sk) (T ↘ Sk)).Modules) [M.IsInvertible]
    (D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk))) (t : T) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (Scheme.Pic.mk M + D.picClass)) =
      chiCurve π (T ↘ Sk) M + D.degree t := by
  letI := hF.toField
  haveI := isLocallyArtinian_divisor hF D
  haveI : IsFinite (D.ideal.subschemeι ≫ (pullback (C ↘ Sk) (T ↘ Sk) ↘ T)) :=
    D.isFinite C (T ↘ Sk)
  haveI : Flat (D.ideal.subschemeι ≫ (pullback (C ↘ Sk) (T ↘ Sk) ↘ T)) := D.flat
  have e : Scheme.Pic.rep (Scheme.Pic.mk M + D.picClass) ≅ M ⊗ D.lineBundle := by
    refine (Scheme.Pic.mk_eq_mk_iff.mp ?_).some
    rw [Scheme.Pic.mk_tensor, Scheme.Pic.mk_rep]
    rfl
  rw [chiCurve_congr π _ e]
  have hU := isAffineOpen_chart (T₀ := T) π 0
  have hV := isAffineOpen_chart (T₀ := T) π 1
  have hUV := isAffineOpen_chart_inf (T₀ := T) π
  have hcov : (pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0 ⊔
      (pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1 = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ProjectiveLine.U_sup, Scheme.Hom.preimage_top]
  haveI := (finite_cechModH0_H1 (T₀ := T) π M).1
  haveI := (finite_cechModH0_H1 (T₀ := T) π M).2
  haveI := (finite_cechModH0_H1 (T₀ := T) π (M ⊗ D.lineBundle)).1
  haveI := (finite_cechModH0_H1 (T₀ := T) π (M ⊗ D.lineBundle)).2
  -- `Γ(D, M(D)|_D)` has dimension `deg D`
  haveI : Module.Finite Γ(T, ⊤)
      Γ((Scheme.Modules.pullback D.ideal.subschemeι).obj (M ⊗ D.lineBundle), ⊤) :=
    finite_sections_pullback_subscheme (S := T) (M ⊗ D.lineBundle) D.ideal
  have key := chi_twist_divisor D hF hU hV hUV hcov _ (basicOpen_chartτ _) M
  have hdeg : (Module.finrank Γ(T, ⊤)
      Γ((Scheme.Modules.pullback D.ideal.subschemeι).obj (M ⊗ D.lineBundle), ⊤) : ℤ) =
      D.degree t := by
    have h1 := finrank_eq_rankAtStalk_sections (S := T) D.ideal t
    have h2 := rankAtStalk_sections_pullback (S := T) (M ⊗ D.lineBundle) D.ideal
      ((isAffineOpen_top T).primeIdealOf ⟨t, trivial⟩)
    have h3 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Γ(T, ⊤))
      (M := Γ((Scheme.Modules.pullback D.ideal.subschemeι).obj (M ⊗ D.lineBundle), ⊤)))
      ((isAffineOpen_top T).primeIdealOf ⟨t, trivial⟩)
    change _ = ((D.ideal.subschemeι ≫ (pullback (C ↘ Sk) (T ↘ Sk) ↘ T)).finrank t : ℤ)
    rw [h1, ← h2]
    exact_mod_cast h3.symm
  rw [chiCurve, chiCurve, ← hdeg]
  exact key

/-- **`𝒪(D)` has degree `deg D`**: `χ(𝒪(D)) = deg D + 1 − g` on `C ×_k T`, `Γ(T)` a field. -/
theorem chiCurve_ofDivisor (hF : IsField Γ(T, ⊤))
    (D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk))) (t : T) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep D.picClass) = D.degree t + 1 - genusNat k C := by
  have h := chiCurve_add_divisor π hF (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk))) D t
  have h0 : Scheme.Pic.mk (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk))) = 0 := by
    rw [Scheme.Pic.mk_eq_zero_iff]
    exact ⟨structureSheafIsoUnit _⟩
  rw [h0, zero_add, chiCurve_structureSheaf π hF] at h
  rw [h]
  ring

/-- Twisting by a difference of effective divisors:
`χ(M + [𝒪(D)] − [𝒪(E)]) = χ(M) + deg D − deg E`. -/
theorem chiCurve_add_sub_divisor (hF : IsField Γ(T, ⊤))
    (M : (pullback (C ↘ Sk) (T ↘ Sk)).Modules) [M.IsInvertible]
    (D E : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk))) (t : T) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (Scheme.Pic.mk M + D.picClass - E.picClass)) =
      chiCurve π (T ↘ Sk) M + D.degree t - E.degree t := by
  set M' := Scheme.Pic.rep (Scheme.Pic.mk M - E.picClass)
  have h1 := chiCurve_add_divisor π hF M' E t
  have h2 := chiCurve_add_divisor π hF M' D t
  have hM : Scheme.Pic.mk M' + E.picClass = Scheme.Pic.mk M := by
    rw [Scheme.Pic.mk_rep]
    abel
  have hM' : Scheme.Pic.mk M' + D.picClass = Scheme.Pic.mk M + D.picClass - E.picClass := by
    rw [Scheme.Pic.mk_rep]
    abel
  have e : Scheme.Pic.rep (Scheme.Pic.mk M) ≅ M :=
    (Scheme.Pic.mk_eq_mk_iff.mp (Scheme.Pic.mk_rep _)).some
  rw [hM, chiCurve_congr π _ e] at h1
  rw [hM'] at h2
  rw [h2]
  linarith

/-- **Additivity of the degree** on classes of differences of effective divisors: if
`z = [𝒪(D)] − [𝒪(E)]`, then `χ(z + z') = χ(z) + χ(z') − χ(𝒪)` for every `z'`, i.e.
`deg (z + z') = deg z + deg z'` with `deg = χ − (1 − g)`. -/
theorem chiCurve_add_of_divisors (hF : IsField Γ(T, ⊤))
    (D E : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)))
    (z' : (pullback (C ↘ Sk) (T ↘ Sk)).Pic) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (D.picClass - E.picClass + z')) =
      chiCurve π (T ↘ Sk) (Scheme.Pic.rep (D.picClass - E.picClass)) +
        chiCurve π (T ↘ Sk) (Scheme.Pic.rep z') - (1 - genusNat k C) := by
  obtain ⟨t⟩ := nonempty_of_isField hF
  have h1 := chiCurve_add_sub_divisor π hF (Scheme.Pic.rep z') D E t
  have h2 := chiCurve_add_sub_divisor π hF (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk))) D E t
  have h0 : Scheme.Pic.mk (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk))) = 0 := by
    rw [Scheme.Pic.mk_eq_zero_iff]
    exact ⟨structureSheafIsoUnit _⟩
  rw [h0, zero_add, chiCurve_structureSheaf π hF] at h2
  rw [Scheme.Pic.mk_rep] at h1
  rw [show D.picClass - E.picClass + z' = z' + D.picClass - E.picClass by abel, h1, h2]
  ring

end CurvesJacobian
