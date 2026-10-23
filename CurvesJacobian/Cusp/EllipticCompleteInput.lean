/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EllipticComplete
import CurvesJacobian.Cusp.EllipticInputE
import CurvesJacobian.Cusp.GaloisDescentOpen
import CurvesJacobian.Cusp.CandidateLiftX1

/-!
# Completeness of the elliptic cuspidalisation for a general elliptic input (MR8.7, round 30)

[AbsTopII] Corollary 3.3 (iii)(a),(b) (`Topics in Absolute Anabelian Geometry II.txt`
l.4459–4510) in the setting of Example 3.2 (ii) (l.4381–4400): `X = CX` an affine hyperbolic curve
over a number field `K`, `D = E ∖ {O}` over a number field `M ⊇ K` with `M`-rational `E[2]`,
`U = E ∖ E[2] ⊆ D`, a hyperbolic curve `V` over `M` with a finite étale Galois cover `V → X` and a
finite étale `V → D`, such that `Gal(V/X)` preserves `U_V = V ×_D U` (`hstab`). Then `U_V`
descends to a nonempty open `U_X ⊆ X` with `U_V = V ×_X U_X`, and the elliptic chain of
`ellipticDataOfInput` gives a candidate in `ellipticCusp (Π_X)` which recovers
`Π_{U_X} ↠ Π_X`: `Π_U ×_{Π_D} Π_V ≅ Π_V ×_{Π_X} Π_{U_X}` over `Π_X` up to conjugation, with
normal `Π_V` and the lifting property of Cor 3.3 (iii)(b)
(**`ellipticCusp_complete_input`**). No DGC is used.

* `ellipticUV`: `U_V = V ×_{D'} U` as an open of `V̄` (`D' = U_n`, the end of the run of
  fillings, identified with `D`), with `isPullback_ellipticUV` (the cartesian square).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M] {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)

namespace EllipticData

variable (D : EllipticData (M := M) CX)

omit [NumberField K] in
/-- `D' = U_n` is affine. -/
lemma isAffineOpen_Dp : IsAffineOpen (D.UW (Fin.last D.n)) :=
  isAffineOpen_of_le D.CW (D.hleW _) (D.hcUW _)

omit [NumberField K] in
/-- `U = UW 0` is affine. -/
lemma isAffineOpen_UW0 : IsAffineOpen (D.UW ⟨0, Nat.succ_pos _⟩) :=
  isAffineOpen_of_le D.CW (D.hleW _) (D.hcUW _)

/-- **`U_V = V ×_{D'} U`** as an open of `V̄`. -/
def ellipticUV : D.CV.Xbar.Opens :=
  (isAffineOpen_U D.CV D.hcV).fromSpec ''ᵁ
    (D.FD ⁻¹ᵁ ((D.isAffineOpen_Dp).fromSpec ⁻¹ᵁ D.UW ⟨0, Nat.succ_pos _⟩))

omit [NumberField K] in
lemma ellipticUV_le : D.ellipticUV ≤ D.CV.U := by
  rintro _ ⟨x, -, rfl⟩
  change _ ∈ (D.CV.U : Set D.CV.Xbar)
  rw [← (isAffineOpen_U D.CV D.hcV).range_fromSpec]
  exact ⟨x, rfl⟩

lemma ellipticUV_nonempty : ((D.ellipticUV : D.CV.Xbar.Opens) : Set D.CV.Xbar).Nonempty := by
  haveI := isIntegral_specSections D.CV D.hcV
  haveI : IsIntegral (Spec Γ(D.CW.Xbar, D.UW (Fin.last D.n))) :=
    isIntegral_specSections D.CDp D.hcDp
  obtain ⟨y, hy⟩ := D.CW.nonempty
  have hy' : y ∈ Set.range (D.isAffineOpen_Dp).fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    exact D.hleW _ hy
  obtain ⟨t, rfl⟩ := hy'
  obtain ⟨s, rfl⟩ := surjective_of_isFiniteEtale D.FD t
  refine ⟨_, ⟨s, ?_, rfl⟩⟩
  change (D.isAffineOpen_Dp).fromSpec (D.FD s) ∈ D.UW ⟨0, Nat.succ_pos _⟩
  have h0 : D.UW ⟨0, Nat.succ_pos _⟩ = D.CW.U := D.hUW0
  rw [h0]
  exact hy

lemma isAffineOpen_ellipticUV : IsAffineOpen D.ellipticUV :=
  isAffineOpen_U (subCurve D.CV D.ellipticUV D.ellipticUV_le D.ellipticUV_nonempty)
    (compl_nonempty_of_le D.ellipticUV_le D.hcV)

/-- `FWU : U_V ⟶ U`. -/
def ellipticFWU : Spec Γ(D.CV.Xbar, D.ellipticUV) ⟶ Spec Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩) :=
  resSquareFU M M D.isAffineOpen_Dp D.isAffineOpen_UW0 (D.monoW (Fin.le_last _))
    (isAffineOpen_U D.CV D.hcV) D.isAffineOpen_ellipticUV D.ellipticUV_le D.FD rfl

/-- **The square `U_V = V ×_{D'} U` is cartesian.** -/
theorem isPullback_ellipticUV :
    IsPullback (Spec.map (CommRingCat.ofHom (resAlg M D.ellipticUV_le).toRingHom))
      D.ellipticFWU D.FD
      (Spec.map (CommRingCat.ofHom
        (resAlg M (D.monoW (Fin.le_last (⟨0, Nat.succ_pos _⟩ : Fin (D.n + 1))))).toRingHom)) :=
  isPullback_resSquareFU M M _ _ _ _ _ _ _ rfl

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [Algebra M Ω] [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopII] Cor 3.3 (iii)(a),(b), completeness for elliptic data with a Galois-stable
`U_V`**: if `V → X` is Galois and `Gal(V/X)` preserves `U_V = V ×_{D'} U`, then `U_V` descends to
a nonempty open `U_X ⊆ X` (`U_V = V ×_X U_X`) and, for every change of base point `α₀`, the
elliptic candidate recovers `Π_V ×_{Π_X} Π_{U_X} ↠ Π_V` over `Π_X` up to conjugation (normal
`Π_V`, lifting of automorphisms of `Π_V` induced by `Π_X`). -/
theorem ellipticCusp_complete_of_stable
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV))
    (hstab : ∀ σ : Aut (coverObj D.FV),
      ∀ z ∈ (isAffineOpen_U D.CV D.hcV).fromSpec ⁻¹ᵁ D.ellipticUV,
        σ.hom.left z ∈ (isAffineOpen_U D.CV D.hcV).fromSpec ⁻¹ᵁ D.ellipticUV) :
    ∃ (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty),
      D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX) =
          (isAffineOpen_U D.CV D.hcV).fromSpec ⁻¹ᵁ D.ellipticUV ∧
      ∀ α₀ : fiber (basePoint Ω CX hcX) ≅
          fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX),
        ∃ x ∈ ellipticCusp (arithmeticExt Ω CX hcX),
          x.toCuspCandidate.emb.toMonoidHom.range.Normal ∧
          (∀ (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω CX hcX).Pi),
            (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
              ∃ ψ : x.fibre ≃ₜ* x.fibre, ∀ p, x.fibreProj (ψ p) = B (x.fibreProj p)) ∧
          ∃ (k : (arithmeticExt Ω CX hcX).Pi)
            (J : x.fibre ≃ₜ* x.emb.toMonoidHom.range.comap
              (cor38Fill Ω CX hcX UX hUX hne α₀)),
            ∀ p, cor38Fill Ω CX hcX UX hUX hne α₀ (J p) = k * x.emb (x.fibreProj p) * k⁻¹ := by
  obtain ⟨UX, hUX, hne, hpre, FU, -, hsqX⟩ := exists_isPullback_of_stable hcX D.hcV D.FV
    D.ellipticUV D.ellipticUV_le D.ellipticUV_nonempty hgal hstab
  exact ⟨UX, hUX, hne, hpre, fun α₀ ↦ ellipticCusp_complete Ω hcX D UX hUX hne α₀ D.ellipticUV
    D.ellipticUV_le D.ellipticUV_nonempty D.ellipticFWU D.isPullback_ellipticUV FU hsqX hgal⟩

end EllipticData

end CurvesJacobian.Cusp
