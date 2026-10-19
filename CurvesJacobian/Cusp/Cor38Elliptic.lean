/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.Cor38Exists
import CurvesJacobian.Cusp.EllipticGalois

/-!
# [AbsTopII] Corollary 3.8, existence, for IUT's `X = E ∖ {O}` (MR8, round 28)

`Topics in Absolute Anabelian Geometry II.txt` l.4794–4842. For an elliptic curve `E` over a
number field `K` with `K`-rational `2`-torsion (`E.Ψ₂Sq` splits; IUT I Def 3.1 (b) assumes the
`2·3`-torsion rational), `X₁ = E ∖ {O}` has a Galois Belyi input (`nonempty_galoisBelyiInput`),
so `cor38_exists` applies (**`CurvesJacobian.Cusp.cor38_exists_oncePunctured`**): every
isomorphism of cuspidal extensions `Φ : Π_{X₁} ≅ Π_{X₂}` to an affine hyperbolic curve `X₂` over a
number field lifts, for every nonempty open `U_{X₁} ⊆ X₁`, to `φ_U : Π_{U_{X₁}} ≅ Π_{U_{X₂}}` over
`Φ` for some nonempty open `U_{X₂} ⊆ X₂`. The only DGC input is `hDGC`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- **[AbsTopII] Corollary 3.8, existence, for `X₁ = E ∖ {O}`** with `K`-rational `E[2]`. -/
theorem cor38_exists_oncePunctured
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    {K₁ K₂ : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    {E : WeierstrassCurve K₁} [E.IsElliptic] (hE : E.Ψ₂Sq.Splits)
    (Ω₁ Ω₂ : Type u) [Field Ω₁] [Algebra K₁ Ω₁] [IsAlgClosed Ω₁] [Algebra.IsAlgebraic K₁ Ω₁]
    [CharZero Ω₁] [Field Ω₂] [Algebra K₂ Ω₂] [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂]
    [CharZero Ω₂] (CX₂ : HypCurve K₂) (hcX₂ : (CX₂.U : Set CX₂.Xbar)ᶜ.Nonempty)
    (Φ : (arithmeticExt Ω₁ (hypCurveX E) (compl_XE_nonempty E)).Iso
      (arithmeticExt Ω₂ CX₂ hcX₂))
    (UX₁ : (hypCurveX E).Xbar.Opens) (hUX₁ : UX₁ ≤ (hypCurveX E).U)
    (hne₁ : (UX₁ : Set (hypCurveX E).Xbar).Nonempty)
    (α₁ : fiber (basePoint Ω₁ (hypCurveX E) (compl_XE_nonempty E)) ≅
      fiber (fillPoint Ω₁ (subCurve (hypCurveX E) UX₁ hUX₁ hne₁)
        (compl_nonempty_of_le hUX₁ (compl_XE_nonempty E)) hUX₁)) :
    ∃ (UX₂ : CX₂.Xbar.Opens) (hUX₂ : UX₂ ≤ CX₂.U) (hne₂ : (UX₂ : Set CX₂.Xbar).Nonempty),
      ∀ α₂ : fiber (basePoint Ω₂ CX₂ hcX₂) ≅
          fiber (fillPoint Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂) hUX₂),
        ∃ φU : (arithmeticExt Ω₁ (subCurve (hypCurveX E) UX₁ hUX₁ hne₁)
              (compl_nonempty_of_le hUX₁ (compl_XE_nonempty E))).Pi ≃ₜ*
            (arithmeticExt Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂)).Pi,
          ∀ e, cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ (φU e) =
            Φ.pi (cor38Fill Ω₁ (hypCurveX E) (compl_XE_nonempty E) UX₁ hUX₁ hne₁ α₁ e) := by
  haveI : CharZero K₁ := inferInstance
  obtain ⟨S⟩ := nonempty_galoisBelyiInput E hE
  exact cor38_exists hDGC (M := K₁) Ω₁ Ω₂ (hypCurveX E) (compl_XE_nonempty E) S CX₂ hcX₂ Φ UX₁
    hUX₁ hne₁ α₁

end CurvesJacobian.Cusp
