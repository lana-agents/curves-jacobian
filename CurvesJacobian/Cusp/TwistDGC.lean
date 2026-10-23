/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FillAutUnique
import CurvesJacobian.Cusp.HypBaseChange
import CurvesJacobian.LocAn.UniqueReduction

/-!
# Galois twists of hyperbolic curves and the twisted rel-isom-DGC (MR8.6)

For an automorphism `α` of a field `M`, the **Galois twist** `C^α` of a hyperbolic curve `C` over
`M` is its base change along `Spec α : Spec M ⟶ Spec M`
(`Belyi.Anabelian.HypCurve.twist`, built from `Belyi.Anabelian.HypCurve.bc` for the `M`-algebra
`CurvesJacobian.Cusp.TwistField α`, i.e. `M` with structure map `α`). The projection
`X̄^α ⟶ X̄` is an isomorphism of schemes lying over `Spec α`, and so is
`Spec Γ(U^α) ⟶ Spec Γ(U)` (`CurvesJacobian.Cusp.twistSpecIso`, `twistSpecIso_hom_sKU`).

**`CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_twist`** (the *twisted* rel-isom-DGC):
for hyperbolic curves `C₁, C₂` over a number field `M` with cusps, a continuous isomorphism
`φ : Π_{U₁} ≃ₜ* Π_{U₂}` lying over an automorphism `Θ` of `G_M` that is itself induced by `Spec α`
(`IsConjInduced (Spec α) Θ`) is induced, up to a change of base point, by an isomorphism of schemes
`Spec Γ(U₁) ≅ Spec Γ(U₂)` lying over `Spec α`; it is unique
(`CurvesJacobian.Cusp.eq_of_isConjInduced_of_relIsomDGC_twist`). Proof: compose `φ` with the
inverse of `π₁ᵉᵗ(U₂^α) ≅ π₁ᵉᵗ(U₂)`; the result lies over an inner automorphism of `G_M`, and
`exists_isConjInduced_of_relIsomDGC_conj` (the rel-isom-DGC over `M`, applied to `C₁` and `C₂^α`)
applies. No hypothesis beyond `RelIsomDGC M` is used.

This is the semilinear form of the DGC needed for the action of a chain object `A` on a geometric
model `N ≅ Π_Y ⊴ A` when `pr(g) ∉ pr(N)` ([AbsTopI] Thm 4.7 (i), proof; [AbsTopII] Cor 3.7).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Twist

variable {M : Type u} [Field M]

/-- The field `M` viewed as an `M`-algebra through an automorphism `α` (a type synonym, so that
the base change along `Spec α` is `bcX M (TwistField α)`). -/
def TwistField (_α : M ≃+* M) : Type u := M

variable (α : M ≃+* M)

instance : Field (TwistField α) := inferInstanceAs (Field M)

instance : Algebra M (TwistField α) := RingHom.toAlgebra (show M →+* M from α)

lemma algebraMap_twistField (x : M) : algebraMap M (TwistField α) x = α x := rfl

instance : Algebra.IsAlgebraic M (TwistField α) :=
  ⟨fun x ↦ ⟨Polynomial.X - Polynomial.C (α.symm x), Polynomial.X_sub_C_ne_zero _, by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_twistField]
    exact sub_eq_zero.2 (α.apply_symm_apply x).symm⟩⟩

/-- `Spec α : Spec M ⟶ Spec M`. -/
abbrev specRingEquiv : Spec (.of M) ⟶ Spec (.of M) :=
  Spec.map (CommRingCat.ofHom (α : M →+* M))

instance : IsIso (specRingEquiv α) := by
  haveI : IsIso (CommRingCat.ofHom (α : M →+* M)) := α.toCommRingCatIso.isIso_hom
  dsimp only [specRingEquiv]
  infer_instance

variable [CharZero M]

/-- **The Galois twist `C^α`** of a hyperbolic curve `C` over `M` along an automorphism `α` of
`M`: the base change `(X̄_{M'}, U_{M'})` along `Spec α`, `M' = TwistField α`, regarded as a
hyperbolic curve over `M`. -/
def _root_.Belyi.Anabelian.HypCurve.twist (C : HypCurve M) : HypCurve M :=
  let C' := C.bc (TwistField α)
  @HypCurve.mk M _ C'.Xbar C'.over C'.isCurve C'.U C'.nonempty C'.cusps_finite C'.hyperbolic

variable (C : HypCurve M)

/-- The projection `X̄^α ⟶ X̄` (an isomorphism of schemes over `Spec α`). -/
abbrev twistπ : (C.twist α).Xbar ⟶ C.Xbar := bcπ M (TwistField α) C.Xbar

lemma twist_U : (C.twist α).U = twistπ α C ⁻¹ᵁ C.U := rfl

/-- The twisting square `X̄^α ⟶ X̄` over `Spec α` is cartesian. -/
lemma isPullback_twistπ :
    IsPullback (twistπ α C) ((C.twist α).Xbar ↘ Spec (.of M)) (C.Xbar ↘ Spec (.of M))
      (specRingEquiv α) :=
  isPullback_bcπ M (TwistField α) C.Xbar

lemma twist_cusp (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    ((C.twist α).U : Set (C.twist α).Xbar)ᶜ.Nonempty :=
  HypCurve.bc_cusp (TwistField α) C hc

end Twist

/-! ### `Spec Γ(U^α) ≅ Spec Γ(U)` -/

section TwistSpec

variable {M : Type u} [Field M] [NumberField M] (α : M ≃+* M) (C : HypCurve M)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

include hc in
/-- The square `Spec Γ(U^α) ⟶ Spec Γ(U)` over `Spec α` is cartesian. -/
lemma isPullback_twistSpec :
    IsPullback (Spec.map ((twistπ α C).appLE C.U (C.twist α).U le_rfl)) (sKU (C.twist α))
      (sKU C) (specRingEquiv α) :=
  letI : (C.twist α).Xbar.Over (Spec (.of (TwistField α))) := (C.twist α).over
  isPullback_specΓ (M := M) (M' := TwistField α) (twistπ α C)
    (isPullback_bcπ M (TwistField α) C.Xbar) rfl (isAffineOpen_U C hc)

/-- **`Spec Γ(U^α) ≅ Spec Γ(U)`**, lying over `Spec α` (`twistSpecIso_hom_sKU`). -/
def twistSpecIso : Spec Γ((C.twist α).Xbar, (C.twist α).U) ≅ Spec Γ(C.Xbar, C.U) :=
  haveI := (isPullback_twistSpec α C hc).isIso_fst_of_isIso
  asIso (Spec.map ((twistπ α C).appLE C.U (C.twist α).U le_rfl))

@[reassoc]
lemma twistSpecIso_hom_sKU :
    (twistSpecIso α C hc).hom ≫ sKU C = sKU (C.twist α) ≫ specRingEquiv α :=
  (isPullback_twistSpec α C hc).w

@[reassoc]
lemma twistSpecIso_inv_sKU :
    (twistSpecIso α C hc).inv ≫ sKU (C.twist α) ≫ specRingEquiv α = sKU C := by
  rw [← twistSpecIso_hom_sKU α C hc, Iso.inv_hom_id_assoc]

end TwistSpec

/-! ### The twisted rel-isom-DGC -/

section TwistDGC

variable {M : Type u} [Field M] [NumberField M] (Ω : Type u) [Field Ω] [Algebra M Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic M Ω] (α : M ≃+* M)

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {C₁ C₂ : HypCurve M} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

/-- The point `Spec Ω ⟶ Spec M`. -/
local notation "sM" => Spec.map (CommRingCat.ofHom (algebraMap M Ω))

/-- A change of base point `fiber (x' ≫ P) ≅ fiber x₂` for `P = twistSpecIso`. -/
def twistFib (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    fiber ((basePoint Ω (C.twist α) (twist_cusp α C hc) ≫
        baseChangeSpec M Ω Γ((C.twist α).Xbar, (C.twist α).U)) ≫ (twistSpecIso α C hc).hom) ≅
      fiber (basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) :=
  (nonempty_iso_of_fiberFunctor _ _).some

/-- **`Π_{U^α} ≃ₜ* Π_U`**: `π₁ᵉᵗ` of `twistSpecIso`, followed by `twistFib`. -/
def twistPiEquiv (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    π₁ᵉᵗ(basePoint Ω (C.twist α) (twist_cusp α C hc) ≫
        baseChangeSpec M Ω Γ((C.twist α).Xbar, (C.twist α).U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) :=
  (fundamentalGroupEquivOfIso (twistSpecIso α C hc) _).trans
    (autContinuousMulEquivOfIso (twistFib Ω α C hc))

omit [Algebra.IsAlgebraic M Ω] in
lemma isConjInduced_twistPiEquiv (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    IsConjInduced (twistSpecIso α C hc).hom (twistPiEquiv Ω α C hc) :=
  ⟨twistFib Ω α C hc, fun _ ↦ rfl⟩

omit [Algebra.IsAlgebraic M Ω] in
lemma basePoint_twist_comp (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    ((basePoint Ω (C.twist α) (twist_cusp α C hc) ≫
        baseChangeSpec M Ω Γ((C.twist α).Xbar, (C.twist α).U)) ≫ (twistSpecIso α C hc).hom) ≫
      sKU C = sM ≫ specRingEquiv α := by
  rw [Category.assoc, twistSpecIso_hom_sKU, ← Category.assoc, basePoint_spec₂]

/-- The change of base point of `Spec M` induced by `twistFib`. -/
def twistFibM (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    fiber (sM ≫ specRingEquiv α) ≅ fiber sM :=
  fiberIsoMap (sKU C) (basePoint_twist_comp Ω α C hc) (basePoint_spec₂ Ω C hc)
    (twistFib Ω α C hc)

/-- `Θ₀ = (twistFibM)_* ∘ π₁ᵉᵗ(Spec α)`: the automorphism of `G_M` under `twistPiEquiv`. -/
def twistTheta (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    π₁ᵉᵗ(sM) →* π₁ᵉᵗ(sM) :=
  (autContinuousMulEquivOfIso (twistFibM Ω α C hc)).toMulEquiv.toMonoidHom.comp
    (fundamentalGroupMap (specRingEquiv α) (rfl : sM ≫ specRingEquiv α = _)).toMonoidHom

omit [Algebra.IsAlgebraic M Ω] in
lemma twistTheta_bijective (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    Function.Bijective (twistTheta Ω α C hc) :=
  (autContinuousMulEquivOfIso (twistFibM Ω α C hc)).bijective.comp
    (fundamentalGroupMap_bijective_of_isIso (specRingEquiv α) rfl)

omit [Algebra.IsAlgebraic M Ω] in
/-- **`twistPiEquiv` lies over `Θ₀ = twistTheta`.** -/
lemma projGk_twistPiEquiv (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (σ : π₁ᵉᵗ(basePoint Ω (C.twist α) (twist_cusp α C hc) ≫
      baseChangeSpec M Ω Γ((C.twist α).Xbar, (C.twist α).U))) :
    projGk Ω C hc (twistPiEquiv Ω α C hc σ) =
      twistTheta Ω α C hc (projGk Ω (C.twist α) (twist_cusp α C hc) σ) := by
  have hx := basePoint_spec₂ Ω (C.twist α) (twist_cusp α C hc)
  have h3 : (basePoint Ω (C.twist α) (twist_cusp α C hc) ≫
      baseChangeSpec M Ω Γ((C.twist α).Xbar, (C.twist α).U)) ≫ (twistSpecIso α C hc).hom ≫
        sKU C = sM ≫ specRingEquiv α := by
    rw [← Category.assoc]
    exact basePoint_twist_comp Ω α C hc
  have h4 : (basePoint Ω (C.twist α) (twist_cusp α C hc) ≫
      baseChangeSpec M Ω Γ((C.twist α).Xbar, (C.twist α).U)) ≫ sKU (C.twist α) ≫
        specRingEquiv α = sM ≫ specRingEquiv α := by
    rw [← Category.assoc, hx]
  have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp (twistSpecIso α C hc).hom (sKU C) rfl
    (basePoint_twist_comp Ω α C hc) h3) σ
  have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp (sKU (C.twist α)) (specRingEquiv α)
    hx rfl h4) σ
  have c3 := DFunLike.congr_fun (fundamentalGroupMap_congr (twistSpecIso_hom_sKU α C hc) h3 h4) σ
  change fundamentalGroupMap (sKU C) (basePoint_spec₂ Ω C hc)
      (autContinuousMulEquivOfIso (twistFib Ω α C hc)
        (fundamentalGroupMap (twistSpecIso α C hc).hom rfl σ)) =
    autContinuousMulEquivOfIso (twistFibM Ω α C hc)
      (fundamentalGroupMap (specRingEquiv α) rfl (fundamentalGroupMap (sKU (C.twist α)) hx σ))
  rw [fundamentalGroupMap_autContinuousMulEquivOfIso (sKU C) (basePoint_twist_comp Ω α C hc)]
  exact congrArg (autContinuousMulEquivOfIso (twistFibM Ω α C hc)) ((c1.symm.trans c3).trans c2)

set_option linter.unusedSectionVars false in
/-- After `twistPiEquiv⁻¹`, an isomorphism over `Θ` (induced by `Spec α`) lies over an inner
automorphism of `G_M` coming from `Π_{U₂^α}`. -/
lemma exists_projGk_twist_conj
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)))
    (Θ : π₁ᵉᵗ(sM) → π₁ᵉᵗ(sM)) (hΘ : IsConjInduced (specRingEquiv α) Θ)
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ)) :
    ∃ t, ∀ σ, projGk Ω (C₂.twist α) (twist_cusp α C₂ hc₂)
        ((φ.trans (twistPiEquiv Ω α C₂ hc₂).symm) σ) =
      projGk Ω (C₂.twist α) (twist_cusp α C₂ hc₂) t * projGk Ω C₁ hc₁ σ *
        (projGk Ω (C₂.twist α) (twist_cusp α C₂ hc₂) t)⁻¹ := by
  obtain ⟨u, hu⟩ :=
    (isConjInduced_iff_exists_conj (specRingEquiv α) (twistFibM Ω α C₂ hc₂) Θ).1 hΘ
  obtain ⟨v, hv⟩ := (twistTheta_bijective Ω α C₂ hc₂).2 u
  obtain ⟨t, rfl⟩ := projGk_surjective Ω (C₂.twist α) (twist_cusp α C₂ hc₂) v
  refine ⟨t, fun σ ↦ (twistTheta_bijective Ω α C₂ hc₂).1 ?_⟩
  rw [← projGk_twistPiEquiv, map_mul, map_mul, map_inv, hv]
  change projGk Ω C₂ hc₂ (twistPiEquiv Ω α C₂ hc₂ ((twistPiEquiv Ω α C₂ hc₂).symm (φ σ))) = _
  rw [ContinuousMulEquiv.apply_symm_apply, hφ, hu]
  rfl

/-- **The twisted rel-isom-DGC, existence** (`Y₁ → Y₂^α`): for hyperbolic curves `C₁, C₂` over a
number field `M` with cusps and an automorphism `α` of `M`, every continuous isomorphism
`φ : Π_{U₁} ≃ₜ* Π_{U₂}` lying over an automorphism `Θ` of `G_M` induced by `Spec α` is induced, up
to a change of base point, by an isomorphism of schemes `Spec Γ(U₁) ≅ Spec Γ(U₂)` lying over
`Spec α`. -/
theorem exists_isConjInduced_of_relIsomDGC_twist (hDGC : RelIsomDGC.Exists M)
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)))
    (Θ : π₁ᵉᵗ(sM) → π₁ᵉᵗ(sM)) (hΘ : IsConjInduced (specRingEquiv α) Θ)
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ)) :
    ∃ F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U),
      F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv α ∧ IsConjInduced F.hom φ := by
  obtain ⟨t, ht⟩ := exists_projGk_twist_conj Ω α φ Θ hΘ hφ
  obtain ⟨F', hF', H'⟩ := exists_isConjInduced_of_relIsomDGC_conj Ω hDGC
    (φ.trans (twistPiEquiv Ω α C₂ hc₂).symm) t ht
  refine ⟨F' ≪≫ twistSpecIso α C₂ hc₂, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, twistSpecIso_hom_sKU, ← Category.assoc, hF']
  · refine (H'.comp (isConjInduced_twistPiEquiv Ω α C₂ hc₂)).congr_fun fun σ ↦ ?_
    change φ σ = twistPiEquiv Ω α C₂ hc₂ ((twistPiEquiv Ω α C₂ hc₂).symm (φ σ))
    rw [ContinuousMulEquiv.apply_symm_apply]

/-- **The twisted rel-isom-DGC, uniqueness**: the isomorphism over `Spec α` inducing `φ` is
unique. -/
theorem eq_of_isConjInduced_of_relIsomDGC_twist
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M Ω Γ(C₂.Xbar, C₂.U)))
    (Θ : π₁ᵉᵗ(sM) → π₁ᵉᵗ(sM)) (hΘ : IsConjInduced (specRingEquiv α) Θ)
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ))
    {F G : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)}
    (hF : F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv α)
    (hG : G.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv α)
    (HF : IsConjInduced F.hom φ) (HG : IsConjInduced G.hom φ) : F = G := by
  obtain ⟨t, ht⟩ := exists_projGk_twist_conj Ω α φ Θ hΘ hφ
  have hP := IsConjInduced.symm_of_iso (twistSpecIso α C₂ hc₂)
    (twistPiEquiv Ω α C₂ hc₂).toMulEquiv (isConjInduced_twistPiEquiv Ω α C₂ hc₂)
  set ψ := φ.trans ((twistPiEquiv Ω α C₂ hc₂).symm.trans (conjCMEquiv t⁻¹))
  have hψ : ∀ σ, projGk Ω (C₂.twist α) (twist_cusp α C₂ hc₂) (ψ σ) = projGk Ω C₁ hc₁ σ :=
    fun σ ↦ by
      change projGk Ω (C₂.twist α) _ (t⁻¹ * (φ.trans (twistPiEquiv Ω α C₂ hc₂).symm) σ *
        t⁻¹⁻¹) = _
      rw [map_mul, map_mul, ht, map_inv, inv_inv]
      group
  have key : ∀ F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U),
      F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv α → IsConjInduced F.hom φ →
        (F ≪≫ (twistSpecIso α C₂ hc₂).symm).hom ≫ sKU (C₂.twist α) = sKU C₁ ∧
        IsConjInduced (F ≪≫ (twistSpecIso α C₂ hc₂).symm).hom ψ := by
    intro F hF HF
    refine ⟨(cancel_mono (specRingEquiv α)).1 ?_, ((HF.comp hP).conj t⁻¹).congr_fun fun σ ↦ rfl⟩
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      twistSpecIso_inv_sKU, hF]
  obtain ⟨h₁, H₁⟩ := key F hF HF
  obtain ⟨h₂, H₂⟩ := key G hG HG
  have e := eq_of_isConjInduced_of_relIsomDGC Ω ψ hψ h₁ h₂ H₁ H₂
  simpa using congrArg (· ≪≫ twistSpecIso α C₂ hc₂) e

end TwistDGC

end CurvesJacobian.Cusp
