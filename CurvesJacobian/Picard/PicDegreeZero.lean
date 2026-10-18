/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicDegreeTranslate
import CurvesJacobian.Picard.PicSpecEquiv
import CurvesJacobian.Picard.CurveGenus

/-!
# The structure sheaf has degree zero (Stacks, Lemma 44.6.7, Tag 0BA0)

For a curve `C` of genus `g` over a perfect field `k` and `T` affine over `k` with `Γ(T)` a
field, the chart Čech complex of `𝒪` on `C ×_k T` has `h⁰ = 1` (Stacks, Lemma 44.6.1,
Tag 0B9U: `Γ(C ×_k T, 𝒪) = Γ(T)`) and `h¹ = g` (base change of `Ȟ¹(C, 𝒪) ≅ k^g`), so
`χ(𝒪) = 1 − g`: with the normalisation `χ = d + 1 − g` of Stacks, Tag 0BA0, the neutral element
of `Pic_{C/k,σ}` lies in `Pic⁰`.

* `CurvesJacobian.finrank_cechModH0_structureSheaf`, `finrank_cechModH1_structureSheaf`,
  `chiCurve_structureSheaf`;
* `CurvesJacobian.picDeg_zero_zero`: `0 ∈ Pic⁰(T)` for every scheme `T`;
* `CurvesJacobian.picDeg_nsmul_pointClass`: `n · [𝒪(x)] ∈ Pic^n(T)` for a `k`-point `x` in both
  charts.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k) [PerfectField k] [IsCurveOver k C] [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)

section Structure

variable {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]

omit [IsFinite π] in
/-- `h⁰(𝒪) = 1` on `C ×_k T` for `Γ(T)` a field (Stacks, Tag 0B9U). -/
theorem finrank_cechModH0_structureSheaf (hF : IsField Γ(T, ⊤)) :
    Module.finrank Γ(T, ⊤) (cechModH0 T (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk)))
      ((pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
      ((pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)) = 1 := by
  letI := hF.toField
  have hcov : (pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0 ⊔
      (pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1 = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ProjectiveLine.U_sup, Scheme.Hom.preimage_top]
  rw [← (globalSectionsEquivH0 T (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk))) hcov).finrank_eq]
  haveI := IsCurveOver.isIso_app_pullback_snd k C (T ↘ Sk) ⊤ (isAffineOpen_top T).isCompact
    (isAffineOpen_top T).isQuasiSeparated
  change Module.finrank Γ(T, ⊤) Γ(pullback (C ↘ Sk) (T ↘ Sk), ⊤) = 1
  have hb : Function.Bijective (algebraMap Γ(T, ⊤) Γ(pullback (C ↘ Sk) (T ↘ Sk), ⊤)) := by
    have := ConcreteCategory.bijective_of_isIso ((pullback.snd (C ↘ Sk) (T ↘ Sk)).app ⊤)
    rwa [Scheme.Hom.app_eq_appLE] at this
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap _ _) hb).finrank_eq, Module.finrank_self]

/-- `h¹(𝒪) = g` on `C ×_k T` for `Γ(T)` a field. -/
theorem finrank_cechModH1_structureSheaf (hF : IsField Γ(T, ⊤)) :
    (Module.finrank Γ(T, ⊤) (cechModH1 T (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk)))
      ((pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
      ((pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)) : ℤ) =
        genusNat k C := by
  letI := hF.toField
  letI : Field Γ(Sk, ⊤) := isField_ΓSpec.toField
  haveI : IsIntegral C := IsCurveOver.isIntegral k C
  have hU := (ProjectiveLine.isAffineOpen_U k 0).preimage π
  have hV := (ProjectiveLine.isAffineOpen_U k 1).preimage π
  have hUV := (ProjectiveLine.isAffineOpen_U_inf k).preimage π
  have hcov : π ⁻¹ᵁ ProjectiveLine.U k 0 ⊔ π ⁻¹ᵁ ProjectiveLine.U k 1 = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ProjectiveLine.U_sup, Scheme.Hom.preimage_top]
  have e := cechH1BaseChange (S := Sk) (T := T) _ _ hU hV hUV
  have h1 := finrank_cechH1_eq_curveGenus k C hU hV hcov
  have h2 : Module.finrank Γ(T, ⊤) (cechModH1 T (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk)))
      ((pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
      ((pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)) =
      Module.finrank Γ(Sk, ⊤) (cechH1 Sk C (π ⁻¹ᵁ ProjectiveLine.U k 0)
        (π ⁻¹ᵁ ProjectiveLine.U k 1)) :=
    e.finrank_eq.trans Module.finrank_baseChange
  rw [h2, h1, genusNat, Int.toNat_of_nonneg (h1 ▸ Int.natCast_nonneg _)]

/-- **`χ(𝒪) = 1 − g`** on `C ×_k T` for `Γ(T)` a field. -/
theorem chiCurve_structureSheaf (hF : IsField Γ(T, ⊤)) :
    chiCurve π (T ↘ Sk) (structureSheaf (pullback (C ↘ Sk) (T ↘ Sk))) = 1 - genusNat k C := by
  rw [chiCurve, finrank_cechModH0_structureSheaf π hF, finrank_cechModH1_structureSheaf π hF]
  rfl

end Structure

section Degree

variable (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- **The neutral element lies in `Pic⁰`** (Stacks, Lemma 44.6.7, Tag 0BA0). -/
theorem picDeg_zero_zero {T : Scheme.{u}} (g : T ⟶ Sk) :
    picDeg σ hσ π 0 T ⟨g, 0⟩ := by
  intro T' _ hF h
  have h0 : (sigmaG G).map h.op ⟨g, 0⟩ = ⟨h ≫ g, 0⟩ := by
    rw [sigmaG_map_mk]
    exact Sigma.ext rfl (heq_of_eq (map_zero _))
  rw [h0]
  letI : T'.Over Sk := ⟨h ≫ g⟩
  change chiCurve π (T' ↘ Sk) (Scheme.Pic.rep (0 : (pullback (C ↘ Sk) (T' ↘ Sk)).Pic)) = _
  have e : Scheme.Pic.rep (0 : (pullback (C ↘ Sk) (T' ↘ Sk)).Pic) ≅
      structureSheaf (pullback (C ↘ Sk) (T' ↘ Sk)) :=
    ((Scheme.Pic.mk_eq_zero_iff _).mp (Scheme.Pic.mk_rep _)).some ≪≫
      (structureSheafIsoUnit _).symm
  rw [chiCurve_congr π _ e, chiCurve_structureSheaf π hF]
  ring

/-- `n · [𝒪(x)] ∈ Pic^n(T)` for a `k`-point `x` in both charts: every `Pic^d`, `d ≥ 0`, has
points over every `k`-scheme. -/
theorem picDeg_nsmul_pointClass (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk)
    (hxW : ⊤ ≤ xC ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)))
    {T : Scheme.{u}} (g : T ⟶ Sk) (n : ℕ) :
    picDeg σ hσ π n T (translate G (n • pointClass C σ hσ xC hx) ⟨g, 0⟩) := by
  induction n with
  | zero =>
    rw [zero_smul, translate_zero]
    exact_mod_cast picDeg_zero_zero π σ hσ g
  | succ n ih =>
    rw [succ_nsmul', ← translate_translate]
    push_cast
    exact (picDeg_translate_iff C π σ hσ xC hx hxW (n : ℤ) _).mpr ih

end Degree

end CurvesJacobian
