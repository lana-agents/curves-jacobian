/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CurveGenus
import CurvesJacobian.Cusp.BaseChange

/-!
# The genus of a curve is invariant under extension of the base field

Let `k ⊆ Ω` be perfect fields and `X` a curve over `k` (`Belyi.IsCurveOver`). Then
`g(X_Ω) = g(X)` (`CurvesJacobian.Cusp.curveGenus_baseChange`), for the genus
`CurvesJacobian.curveGenus` of the function field (weil-curves).

Proof: cover `X` by two affine opens `U`, `V` (`IsCurveOver.exists_two_affine_cover`); their
preimages cover `X_Ω` and are affine, so `g(X_Ω) = dim_Ω Ȟ¹(U_Ω, V_Ω; 𝒪)` and
`g(X) = dim_k Ȟ¹(U, V; 𝒪)` (`CurvesJacobian.finrank_cechH1_eq_curveGenus`), and
`Ȟ¹(U_Ω, V_Ω; 𝒪) ≅ Ω ⊗_k Ȟ¹(U, V; 𝒪)` (`CurvesJacobian.Cech.cechH1BaseChange`).
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi Module
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

open Cech

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- `Spec Ω` as a scheme over `Spec k`. -/
local instance specOver : (Spec (.of Ω)).Over (Spec (.of k)) := ⟨specAlgebraMap k Ω⟩

/-- `Γ(Spec k, ⊤)` is a field. -/
lemma isField_ΓSpec : IsField Γ(Spec (.of k), ⊤) :=
  MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

variable {k} in
/-- Over a field (here `Γ(Spec k, ⊤)`), every module is free. -/
lemma free_ΓSpec (M : Type*) [AddCommGroup M] [Module Γ(Spec (.of k), ⊤) M] :
    Module.Free Γ(Spec (.of k), ⊤) M := by
  letI := (isField_ΓSpec k).toField
  exact Module.Free.of_divisionRing _ _

variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- **The genus is invariant under base change** `k ⊆ Ω` of perfect fields. -/
theorem curveGenus_baseChange [PerfectField k] [PerfectField Ω] [IsCurveOver k X] :
    haveI := IsCurveOver.isIntegral k X
    haveI := IsCurveOver.isIntegral Ω (baseChange k Ω X)
    curveGenus Ω (baseChange k Ω X) = curveGenus k X := by
  haveI := IsCurveOver.isIntegral k X
  haveI := IsCurveOver.isIntegral Ω (baseChange k Ω X)
  obtain ⟨⟨U, hU⟩, ⟨V, hV⟩, hUV⟩ := IsCurveOver.exists_two_affine_cover k X
  have hUV' : IsAffineOpen (U ⊓ V) := IsCurveOver.isAffineOpen_inf k X hU hV
  set p := pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω)
  haveI : IsAffineHom p := MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  have hU' : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
  have hV' : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have hcov : p ⁻¹ᵁ U ⊔ p ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  have h1 := finrank_cechH1_eq_curveGenus Ω (baseChange k Ω X) hU' hV' hcov
  have h2 := finrank_cechH1_eq_curveGenus k X hU hV hUV
  rw [← h1, ← h2]
  congr 1
  haveI := free_ΓSpec (k := k) (cechH1 (Spec (.of k)) X U V)
  exact ((cechH1BaseChange (T := Spec (.of Ω)) U V hU hV hUV').finrank_eq).trans
    (Module.finrank_baseChange)

end CurvesJacobian.Cusp
