/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.InnerRigidAffine

/-!
# Uniqueness in the rel-isom-DGC from inner rigidity (MR7, step G1)

In MR8's arithmetic model (`CurvesJacobian/Cusp/DGCArith.lean`: an affine hyperbolic curve `C`
over a number field `K`, `Π_U = π₁ᵉᵗ(Spec Γ(U))` at `basePoint`), the uniqueness half of the
rel-isom-DGC says that two `K`-isomorphisms `F, F' : Spec Γ(U₁) ≅ Spec Γ(U₂)` inducing the same
`φ : Π_{U₁} ≃ Π_{U₂}` (up to a change of base point, `IsConjInduced`) are equal. This reduces to
**inner rigidity** of `U₁` (`CurvesJacobian.LocAn.InnerRigid`): a `K`-automorphism of
`Spec Γ(U₁)` inducing the identity of `Π_{U₁}` up to a change of base point (i.e. an inner
automorphism) is the identity. Apply it to `F ≫ F'⁻¹`, which induces `φ⁻¹ ∘ φ = id`
(`CurvesJacobian.LocAn.eq_of_isConjInduced_of_innerRigid`).

This is the formal step (G1) of the MR7 uniqueness route; inner rigidity itself is the content
(MR7 plan, steps G2–G3 with the function-field lemmas of `LocAn/PlaceAut.lean`,
`LocAn/FixedPlaceOrder.lean`, `LocAn/Stabilizer.lean`).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
open CurvesJacobian.Cusp

namespace CurvesJacobian.LocAn

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω]

variable {Ω} {C₁ C₂ : HypCurve K} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

/-- **Uniqueness from inner rigidity**: if `U₁` is inner rigid, two `K`-isomorphisms
`Spec Γ(U₁) ≅ Spec Γ(U₂)` inducing the same `φ : Π_{U₁} ≃ Π_{U₂}` up to a change of base point
are equal. -/
theorem eq_of_isConjInduced_of_innerRigid (hR : InnerRigid Ω C₁ hc₁)
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) ≃*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec K Ω Γ(C₂.Xbar, C₂.U)))
    {F F' : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)}
    (hF : F.hom ≫ sKU C₂ = sKU C₁) (hF' : F'.hom ≫ sKU C₂ = sKU C₁)
    (H : IsConjInduced F.hom φ) (H' : IsConjInduced F'.hom φ) : F = F' := by
  have H'' := IsConjInduced.symm_of_iso F' φ H'
  have Hc : IsConjInduced (F ≪≫ F'.symm).hom
      (id : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) → _) :=
    (H.comp H'').congr_fun fun σ ↦ by simp
  have hG : (F ≪≫ F'.symm).hom ≫ sKU C₁ = sKU C₁ := by
    have : F'.inv ≫ sKU C₁ = sKU C₂ := by rw [← hF', Iso.inv_hom_id_assoc]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, this, hF]
  have e := hR _ hG Hc
  ext1
  have := congrArg (fun G : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₁.Xbar, C₁.U) ↦ G.hom ≫ F'.hom) e
  simpa using this

/-- **Uniqueness in the rel-isom-DGC, unconditionally** (MR7 S2): two `K`-isomorphisms
`Spec Γ(U₁) ≅ Spec Γ(U₂)` inducing the same `φ : Π_{U₁} ≃ Π_{U₂}` up to a change of base point
are equal (`innerRigid`). -/
theorem eq_of_isConjInduced [Algebra.IsAlgebraic K Ω] [CharZero Ω]
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) ≃*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec K Ω Γ(C₂.Xbar, C₂.U)))
    {F F' : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)}
    (hF : F.hom ≫ sKU C₂ = sKU C₁) (hF' : F'.hom ≫ sKU C₂ = sKU C₁)
    (H : IsConjInduced F.hom φ) (H' : IsConjInduced F'.hom φ) : F = F' :=
  eq_of_isConjInduced_of_innerRigid (innerRigid Ω C₁ hc₁) φ hF hF' H H'

end CurvesJacobian.LocAn

/-! ### The uniqueness statements of MR8's arithmetic model, without DGC hypothesis -/

namespace CurvesJacobian.Cusp

open CurvesJacobian.LocAn

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  {C₁ C₂ : HypCurve K} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

/-- **The rel-isom-DGC in the arithmetic model, uniqueness** (a theorem, MR7 `innerRigid`): the
`K`-isomorphism inducing a continuous isomorphism over `G_K` is unique. -/
theorem eq_of_isConjInduced_of_relIsomDGC
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec K Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec K Ω Γ(C₂.Xbar, C₂.U)))
    (_hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = projGk Ω C₁ hc₁ σ)
    {F F' : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)}
    (hF : F.hom ≫ sKU C₂ = sKU C₁) (hF' : F'.hom ≫ sKU C₂ = sKU C₁)
    (H : IsConjInduced F.hom φ) (H' : IsConjInduced F'.hom φ) : F = F' := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  exact eq_of_isConjInduced φ.toMulEquiv hF hF' H H'

variable (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

/-- **A `K`-automorphism of `Spec Γ(U)` inducing an inner automorphism of `Π_U` is the identity**
(a theorem, MR7 `innerRigid`). -/
theorem eq_refl_of_isConjInduced_conj
    (t : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (_ht : ∀ σ, projGk Ω C hc (t * σ * t⁻¹) = projGk Ω C hc σ)
    {F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U)} (hF : F.hom ≫ sKU C = sKU C)
    (H : IsConjInduced F.hom fun σ ↦ t * σ * t⁻¹) : F = Iso.refl _ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  refine innerRigid Ω C hc F hF ((H.conj t⁻¹).congr_fun fun σ ↦ ?_)
  simp [mul_assoc]

end CurvesJacobian.Cusp
