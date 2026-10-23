/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.TwistGalois
import CurvesJacobian.LocAn.UniqueReduction

/-!
# The twisted rel-isom-DGC across two fields

This file generalises `CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_twist` and
`CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_gal` from one field `M` (with an
automorphism `α : M ≃+* M`) to two number fields `M₁, M₂` and a field isomorphism
`α : M₂ ≃+* M₁`.

* `Belyi.Anabelian.HypCurve.twist₂`: the twist `C^α` over `M₁` of a hyperbolic curve `C` over
  `M₂`, i.e. its base change along `Spec α : Spec M₁ ⟶ Spec M₂`;
  `CurvesJacobian.Cusp.twistSpecIso₂ : Spec Γ(U^α) ≅ Spec Γ(U)` lies over `Spec α`.
* **`CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_twist₂`** (theorem A): a continuous
  isomorphism `φ : Π_{U₁} ≃ₜ* Π_{U₂}` (`U₁` over `M₁`, `U₂` over `M₂`) lying over a map
  `Θ : G_{M₁} → G_{M₂}` induced by `Spec α` is induced, up to a change of base point, by an
  isomorphism of schemes `Spec Γ(U₁) ≅ Spec Γ(U₂)` lying over `Spec α` (assuming only
  `RelIsomDGC M₁`); it is unique (`eq_of_isConjInduced_of_relIsomDGC_twist₂`).
* `CurvesJacobian.Cusp.isConjInduced_of_res_conj₂`: for `K ⊆ M₁, M₂ ⊆ Ω`, `τ ∈ Gal(Ω/K)` with
  `τ|_{M₂} = α : M₂ ≃ₐ[K] M₁`, every `Θ : G_{M₁} → G_{M₂}` with `res ∘ Θ = conj(τ⁻¹) ∘ res` is
  induced by `Spec α`; `CurvesJacobian.Cusp.exists_algEquiv_of_conj_range` is the Galois
  correspondence producing `α` from `τ`.
* **`CurvesJacobian.Cusp.exists_isConjInduced_of_relIsomDGC_field`** (theorem B): if
  `res₂ ∘ pr₂ ∘ φ = conj(c) ∘ res₁ ∘ pr₁` for some `c ∈ G_K`, then there are a `K`-isomorphism
  `α : M₂ ≃ₐ[K] M₁` and an isomorphism `Spec Γ(U₁) ≅ Spec Γ(U₂)` over `Spec α` inducing `φ`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Twist

variable {M₁ M₂ : Type u} [Field M₁] [Field M₂]

/-- The field `M₁` viewed as an `M₂`-algebra through an isomorphism `α : M₂ ≃+* M₁`. -/
def TwistField₂ (_α : M₂ ≃+* M₁) : Type u := M₁

variable (α : M₂ ≃+* M₁)

instance : Field (TwistField₂ α) := inferInstanceAs (Field M₁)

instance : Algebra M₂ (TwistField₂ α) := RingHom.toAlgebra (show M₂ →+* M₁ from α)

lemma algebraMap_twistField₂ (x : M₂) : algebraMap M₂ (TwistField₂ α) x = α x := rfl

instance : Algebra.IsAlgebraic M₂ (TwistField₂ α) :=
  ⟨fun x ↦ ⟨Polynomial.X - Polynomial.C (α.symm x), Polynomial.X_sub_C_ne_zero _, by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_twistField₂]
    exact sub_eq_zero.2 (α.apply_symm_apply x).symm⟩⟩

/-- `Spec α : Spec M₁ ⟶ Spec M₂`. -/
abbrev specRingEquiv₂ : Spec (.of M₁) ⟶ Spec (.of M₂) :=
  Spec.map (CommRingCat.ofHom (α : M₂ →+* M₁))

instance : IsIso (specRingEquiv₂ α) := by
  haveI : IsIso (CommRingCat.ofHom (α : M₂ →+* M₁)) := α.toCommRingCatIso.isIso_hom
  dsimp only [specRingEquiv₂]
  infer_instance

variable [CharZero M₂]

/-- **The twist `C^α`** over `M₁` of a hyperbolic curve `C` over `M₂`: the base change along
`Spec α`, regarded as a hyperbolic curve over `M₁`. -/
def _root_.Belyi.Anabelian.HypCurve.twist₂ (C : HypCurve M₂) : HypCurve M₁ :=
  let C' := C.bc (TwistField₂ α)
  @HypCurve.mk M₁ _ C'.Xbar C'.over C'.isCurve C'.U C'.nonempty C'.cusps_finite C'.hyperbolic

variable (C : HypCurve M₂)

/-- The projection `X̄^α ⟶ X̄` (an isomorphism of schemes over `Spec α`). -/
abbrev twistπ₂ : (C.twist₂ α).Xbar ⟶ C.Xbar := bcπ M₂ (TwistField₂ α) C.Xbar

lemma twist₂_U : (C.twist₂ α).U = twistπ₂ α C ⁻¹ᵁ C.U := rfl

/-- The twisting square `X̄^α ⟶ X̄` over `Spec α` is cartesian. -/
lemma isPullback_twistπ₂ :
    IsPullback (twistπ₂ α C) ((C.twist₂ α).Xbar ↘ Spec (.of M₁)) (C.Xbar ↘ Spec (.of M₂))
      (specRingEquiv₂ α) :=
  isPullback_bcπ M₂ (TwistField₂ α) C.Xbar

lemma twist₂_cusp (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    ((C.twist₂ α).U : Set (C.twist₂ α).Xbar)ᶜ.Nonempty :=
  HypCurve.bc_cusp (TwistField₂ α) C hc

end Twist

/-! ### `Spec Γ(U^α) ≅ Spec Γ(U)` -/

section TwistSpec

variable {M₁ M₂ : Type u} [Field M₁] [Field M₂] [NumberField M₂]
  (α : M₂ ≃+* M₁) (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

include hc in
/-- The square `Spec Γ(U^α) ⟶ Spec Γ(U)` over `Spec α` is cartesian. -/
lemma isPullback_twistSpec₂ :
    IsPullback (Spec.map ((twistπ₂ α C).appLE C.U (C.twist₂ α).U le_rfl)) (sKU (C.twist₂ α))
      (sKU C) (specRingEquiv₂ α) :=
  letI : (C.twist₂ α).Xbar.Over (Spec (.of (TwistField₂ α))) := (C.twist₂ α).over
  isPullback_specΓ (M := M₂) (M' := TwistField₂ α) (twistπ₂ α C)
    (isPullback_bcπ M₂ (TwistField₂ α) C.Xbar) rfl (isAffineOpen_U C hc)

/-- **`Spec Γ(U^α) ≅ Spec Γ(U)`**, lying over `Spec α` (`twistSpecIso₂_hom_sKU`). -/
def twistSpecIso₂ : Spec Γ((C.twist₂ α).Xbar, (C.twist₂ α).U) ≅ Spec Γ(C.Xbar, C.U) :=
  haveI := (isPullback_twistSpec₂ α C hc).isIso_fst_of_isIso
  asIso (Spec.map ((twistπ₂ α C).appLE C.U (C.twist₂ α).U le_rfl))

@[reassoc]
lemma twistSpecIso₂_hom_sKU :
    (twistSpecIso₂ α C hc).hom ≫ sKU C = sKU (C.twist₂ α) ≫ specRingEquiv₂ α :=
  (isPullback_twistSpec₂ α C hc).w

@[reassoc]
lemma twistSpecIso₂_inv_sKU :
    (twistSpecIso₂ α C hc).inv ≫ sKU (C.twist₂ α) ≫ specRingEquiv₂ α = sKU C := by
  rw [← twistSpecIso₂_hom_sKU α C hc, Iso.inv_hom_id_assoc]

end TwistSpec

/-! ### The twisted rel-isom-DGC across two fields -/

section TwistDGC

variable {M₁ M₂ : Type u} [Field M₁] [Field M₂] [NumberField M₁] [NumberField M₂]
  (Ω : Type u) [Field Ω] [Algebra M₁ Ω] [Algebra M₂ Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic M₁ Ω] (α : M₂ ≃+* M₁)

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {C₁ : HypCurve M₁} {C₂ : HypCurve M₂} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

/-- The point `Spec Ω ⟶ Spec M₁`. -/
local notation "sM₁" => Spec.map (CommRingCat.ofHom (algebraMap M₁ Ω))

/-- The point `Spec Ω ⟶ Spec M₂`. -/
local notation "sM₂" => Spec.map (CommRingCat.ofHom (algebraMap M₂ Ω))

/-- A change of base point `fiber (x' ≫ P) ≅ fiber x₂` for `P = twistSpecIso₂`. -/
def twistFib₂ (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    fiber ((basePoint Ω (C.twist₂ α) (twist₂_cusp α C hc) ≫
        baseChangeSpec M₁ Ω Γ((C.twist₂ α).Xbar, (C.twist₂ α).U)) ≫
          (twistSpecIso₂ α C hc).hom) ≅
      fiber (basePoint Ω C hc ≫ baseChangeSpec M₂ Ω Γ(C.Xbar, C.U)) :=
  (nonempty_iso_of_fiberFunctor _ _).some

/-- **`Π_{U^α} ≃ₜ* Π_U`**: `π₁ᵉᵗ` of `twistSpecIso₂`, followed by `twistFib₂`. -/
def twistPiEquiv₂ (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    π₁ᵉᵗ(basePoint Ω (C.twist₂ α) (twist₂_cusp α C hc) ≫
        baseChangeSpec M₁ Ω Γ((C.twist₂ α).Xbar, (C.twist₂ α).U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M₂ Ω Γ(C.Xbar, C.U)) :=
  (fundamentalGroupEquivOfIso (twistSpecIso₂ α C hc) _).trans
    (autContinuousMulEquivOfIso (twistFib₂ Ω α C hc))

omit [Algebra.IsAlgebraic M₁ Ω] in
lemma isConjInduced_twistPiEquiv₂ (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    IsConjInduced (twistSpecIso₂ α C hc).hom (twistPiEquiv₂ Ω α C hc) :=
  ⟨twistFib₂ Ω α C hc, fun _ ↦ rfl⟩

omit [Algebra.IsAlgebraic M₁ Ω] [Algebra M₂ Ω] in
lemma basePoint_twist₂_comp (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    ((basePoint Ω (C.twist₂ α) (twist₂_cusp α C hc) ≫
        baseChangeSpec M₁ Ω Γ((C.twist₂ α).Xbar, (C.twist₂ α).U)) ≫
          (twistSpecIso₂ α C hc).hom) ≫ sKU C = sM₁ ≫ specRingEquiv₂ α := by
  rw [Category.assoc, twistSpecIso₂_hom_sKU, ← Category.assoc, basePoint_spec₂]

/-- The change of base point `Spec M₁ → Spec M₂` induced by `twistFib₂`. -/
def twistFibM₂ (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    fiber (sM₁ ≫ specRingEquiv₂ α) ≅ fiber sM₂ :=
  fiberIsoMap (sKU C) (basePoint_twist₂_comp Ω α C hc) (basePoint_spec₂ Ω C hc)
    (twistFib₂ Ω α C hc)

/-- `Θ₀ = (twistFibM₂)_* ∘ π₁ᵉᵗ(Spec α) : G_{M₁} → G_{M₂}`, the map under `twistPiEquiv₂`. -/
def twistTheta₂ (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    π₁ᵉᵗ(sM₁) →* π₁ᵉᵗ(sM₂) :=
  (autContinuousMulEquivOfIso (twistFibM₂ Ω α C hc)).toMulEquiv.toMonoidHom.comp
    (fundamentalGroupMap (specRingEquiv₂ α) (rfl : sM₁ ≫ specRingEquiv₂ α = _)).toMonoidHom

omit [Algebra.IsAlgebraic M₁ Ω] in
lemma twistTheta₂_bijective (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    Function.Bijective (twistTheta₂ Ω α C hc) :=
  (autContinuousMulEquivOfIso (twistFibM₂ Ω α C hc)).bijective.comp
    (fundamentalGroupMap_bijective_of_isIso (specRingEquiv₂ α) rfl)

omit [Algebra.IsAlgebraic M₁ Ω] in
/-- **`twistPiEquiv₂` lies over `Θ₀ = twistTheta₂`.** -/
lemma projGk_twistPiEquiv₂ (C : HypCurve M₂) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (σ : π₁ᵉᵗ(basePoint Ω (C.twist₂ α) (twist₂_cusp α C hc) ≫
      baseChangeSpec M₁ Ω Γ((C.twist₂ α).Xbar, (C.twist₂ α).U))) :
    projGk Ω C hc (twistPiEquiv₂ Ω α C hc σ) =
      twistTheta₂ Ω α C hc (projGk Ω (C.twist₂ α) (twist₂_cusp α C hc) σ) := by
  have hx := basePoint_spec₂ Ω (C.twist₂ α) (twist₂_cusp α C hc)
  have h3 : (basePoint Ω (C.twist₂ α) (twist₂_cusp α C hc) ≫
      baseChangeSpec M₁ Ω Γ((C.twist₂ α).Xbar, (C.twist₂ α).U)) ≫ (twistSpecIso₂ α C hc).hom ≫
        sKU C = sM₁ ≫ specRingEquiv₂ α := by
    rw [← Category.assoc]
    exact basePoint_twist₂_comp Ω α C hc
  have h4 : (basePoint Ω (C.twist₂ α) (twist₂_cusp α C hc) ≫
      baseChangeSpec M₁ Ω Γ((C.twist₂ α).Xbar, (C.twist₂ α).U)) ≫ sKU (C.twist₂ α) ≫
        specRingEquiv₂ α = sM₁ ≫ specRingEquiv₂ α := by
    rw [← Category.assoc, hx]
  have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp (twistSpecIso₂ α C hc).hom (sKU C) rfl
    (basePoint_twist₂_comp Ω α C hc) h3) σ
  have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp (sKU (C.twist₂ α)) (specRingEquiv₂ α)
    hx rfl h4) σ
  have c3 := DFunLike.congr_fun
    (fundamentalGroupMap_congr (twistSpecIso₂_hom_sKU α C hc) h3 h4) σ
  change fundamentalGroupMap (sKU C) (basePoint_spec₂ Ω C hc)
      (autContinuousMulEquivOfIso (twistFib₂ Ω α C hc)
        (fundamentalGroupMap (twistSpecIso₂ α C hc).hom rfl σ)) =
    autContinuousMulEquivOfIso (twistFibM₂ Ω α C hc)
      (fundamentalGroupMap (specRingEquiv₂ α) rfl
        (fundamentalGroupMap (sKU (C.twist₂ α)) hx σ))
  rw [fundamentalGroupMap_autContinuousMulEquivOfIso (sKU C) (basePoint_twist₂_comp Ω α C hc)]
  exact congrArg (autContinuousMulEquivOfIso (twistFibM₂ Ω α C hc))
    ((c1.symm.trans c3).trans c2)

set_option linter.unusedSectionVars false in
/-- After `twistPiEquiv₂⁻¹`, an isomorphism over `Θ` (induced by `Spec α`) lies over an inner
automorphism of `G_{M₁}` coming from `Π_{U₂^α}`. -/
lemma exists_projGk_twist₂_conj
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M₂ Ω Γ(C₂.Xbar, C₂.U)))
    (Θ : π₁ᵉᵗ(sM₁) → π₁ᵉᵗ(sM₂)) (hΘ : IsConjInduced (specRingEquiv₂ α) Θ)
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ)) :
    ∃ t, ∀ σ, projGk Ω (C₂.twist₂ α) (twist₂_cusp α C₂ hc₂)
        ((φ.trans (twistPiEquiv₂ Ω α C₂ hc₂).symm) σ) =
      projGk Ω (C₂.twist₂ α) (twist₂_cusp α C₂ hc₂) t * projGk Ω C₁ hc₁ σ *
        (projGk Ω (C₂.twist₂ α) (twist₂_cusp α C₂ hc₂) t)⁻¹ := by
  obtain ⟨u, hu⟩ :=
    (isConjInduced_iff_exists_conj (specRingEquiv₂ α) (twistFibM₂ Ω α C₂ hc₂) Θ).1 hΘ
  obtain ⟨v, hv⟩ := (twistTheta₂_bijective Ω α C₂ hc₂).2 u
  obtain ⟨t, rfl⟩ := projGk_surjective Ω (C₂.twist₂ α) (twist₂_cusp α C₂ hc₂) v
  refine ⟨t, fun σ ↦ (twistTheta₂_bijective Ω α C₂ hc₂).1 ?_⟩
  rw [← projGk_twistPiEquiv₂, map_mul, map_mul, map_inv, hv]
  change projGk Ω C₂ hc₂ (twistPiEquiv₂ Ω α C₂ hc₂ ((twistPiEquiv₂ Ω α C₂ hc₂).symm (φ σ))) = _
  rw [ContinuousMulEquiv.apply_symm_apply, hφ, hu]
  rfl

/-- **The twisted rel-isom-DGC across two fields, existence**: for hyperbolic curves `C₁` over
`M₁` and `C₂` over `M₂` (number fields) with cusps and `α : M₂ ≃+* M₁`, every continuous
isomorphism `φ : Π_{U₁} ≃ₜ* Π_{U₂}` lying over a map `Θ : G_{M₁} → G_{M₂}` induced by `Spec α`
is induced, up to a change of base point, by an isomorphism of schemes
`Spec Γ(U₁) ≅ Spec Γ(U₂)` lying over `Spec α`. -/
theorem exists_isConjInduced_of_relIsomDGC_twist₂ (hDGC : RelIsomDGC.Exists M₁)
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M₂ Ω Γ(C₂.Xbar, C₂.U)))
    (Θ : π₁ᵉᵗ(sM₁) → π₁ᵉᵗ(sM₂)) (hΘ : IsConjInduced (specRingEquiv₂ α) Θ)
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ)) :
    ∃ F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U),
      F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv₂ α ∧ IsConjInduced F.hom φ := by
  obtain ⟨t, ht⟩ := exists_projGk_twist₂_conj Ω α φ Θ hΘ hφ
  obtain ⟨F', hF', H'⟩ := exists_isConjInduced_of_relIsomDGC_conj Ω hDGC
    (φ.trans (twistPiEquiv₂ Ω α C₂ hc₂).symm) t ht
  refine ⟨F' ≪≫ twistSpecIso₂ α C₂ hc₂, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, twistSpecIso₂_hom_sKU, ← Category.assoc, hF']
  · refine (H'.comp (isConjInduced_twistPiEquiv₂ Ω α C₂ hc₂)).congr_fun fun σ ↦ ?_
    change φ σ = twistPiEquiv₂ Ω α C₂ hc₂ ((twistPiEquiv₂ Ω α C₂ hc₂).symm (φ σ))
    rw [ContinuousMulEquiv.apply_symm_apply]

/-- **The twisted rel-isom-DGC across two fields, uniqueness**: the isomorphism over `Spec α`
inducing `φ` is unique. -/
theorem eq_of_isConjInduced_of_relIsomDGC_twist₂
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M₂ Ω Γ(C₂.Xbar, C₂.U)))
    (Θ : π₁ᵉᵗ(sM₁) → π₁ᵉᵗ(sM₂)) (hΘ : IsConjInduced (specRingEquiv₂ α) Θ)
    (hφ : ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ))
    {F G : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)}
    (hF : F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv₂ α)
    (hG : G.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv₂ α)
    (HF : IsConjInduced F.hom φ) (HG : IsConjInduced G.hom φ) : F = G := by
  obtain ⟨t, ht⟩ := exists_projGk_twist₂_conj Ω α φ Θ hΘ hφ
  have hP := IsConjInduced.symm_of_iso (twistSpecIso₂ α C₂ hc₂)
    (twistPiEquiv₂ Ω α C₂ hc₂).toMulEquiv (isConjInduced_twistPiEquiv₂ Ω α C₂ hc₂)
  set ψ := φ.trans ((twistPiEquiv₂ Ω α C₂ hc₂).symm.trans (conjCMEquiv t⁻¹))
  have hψ : ∀ σ, projGk Ω (C₂.twist₂ α) (twist₂_cusp α C₂ hc₂) (ψ σ) = projGk Ω C₁ hc₁ σ :=
    fun σ ↦ by
      change projGk Ω (C₂.twist₂ α) _ (t⁻¹ * (φ.trans (twistPiEquiv₂ Ω α C₂ hc₂).symm) σ *
        t⁻¹⁻¹) = _
      rw [map_mul, map_mul, ht, map_inv, inv_inv]
      group
  have key : ∀ F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U),
      F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv₂ α → IsConjInduced F.hom φ →
        (F ≪≫ (twistSpecIso₂ α C₂ hc₂).symm).hom ≫ sKU (C₂.twist₂ α) = sKU C₁ ∧
        IsConjInduced (F ≪≫ (twistSpecIso₂ α C₂ hc₂).symm).hom ψ := by
    intro F hF HF
    refine ⟨(cancel_mono (specRingEquiv₂ α)).1 ?_,
      ((HF.comp hP).conj t⁻¹).congr_fun fun σ ↦ rfl⟩
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      twistSpecIso₂_inv_sKU, hF]
  obtain ⟨h₁, H₁⟩ := key F hF HF
  obtain ⟨h₂, H₂⟩ := key G hG HG
  have e := eq_of_isConjInduced_of_relIsomDGC Ω ψ hψ h₁ h₂ H₁ H₂
  simpa using congrArg (· ≪≫ twistSpecIso₂ α C₂ hc₂) e

end TwistDGC

/-! ### Galois side: conjugation by `τ ∈ Gal(Ω/K)` carrying `G_{M₁}` to `G_{M₂}` -/

section Res

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω] {M₁ M₂ : Type u} [Field M₁] [Field M₂] [Algebra K M₁] [Algebra K M₂]
  [Algebra M₁ Ω] [Algebra M₂ Ω] [IsScalarTower K M₁ Ω] [IsScalarTower K M₂ Ω]

/-- The point `Spec Ω ⟶ Spec K`. -/
local notation "sK" => Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-- The point `Spec Ω ⟶ Spec M₁`. -/
local notation "sM₁" => Spec.map (CommRingCat.ofHom (algebraMap M₁ Ω))

/-- The point `Spec Ω ⟶ Spec M₂`. -/
local notation "sM₂" => Spec.map (CommRingCat.ofHom (algebraMap M₂ Ω))

omit [IsSepClosed Ω] [IsGalois K Ω] [IsScalarTower K M₁ Ω] [IsScalarTower K M₂ Ω] in
lemma sM_specRingEquiv₂ {τ : Ω ≃ₐ[K] Ω} {α : M₂ ≃ₐ[K] M₁}
    (hα : ∀ x, algebraMap M₁ Ω (α x) = τ (algebraMap M₂ Ω x)) :
    sM₁ ≫ specRingEquiv₂ α.toRingEquiv = specIso τ.toRingEquiv ≫ sM₂ := by
  rw [specIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hα x

omit [IsSepClosed Ω] [IsGalois K Ω] [IsScalarTower K M₁ Ω] [IsScalarTower K M₂ Ω]
  [Algebra M₁ Ω] [Algebra M₂ Ω] [Algebra K Ω] in
lemma specRingEquiv₂_sKM (α : M₂ ≃ₐ[K] M₁) :
    specRingEquiv₂ α.toRingEquiv ≫ sKM K M₂ = sKM K M₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  exact α.commutes c

/-- **Conjugation by a Galois element carrying `M₂` to `M₁` is induced by `Spec` of its
restriction**: if `α : M₂ ≃ₐ[K] M₁` is the restriction of `τ ∈ Gal(Ω/K)` and
`Θ : G_{M₁} → G_{M₂}` satisfies `res ∘ Θ = conj(τ⁻¹) ∘ res`, then `Θ` is induced by `Spec α` up
to a change of base point (the field change along `τ`). -/
theorem isConjInduced_of_res_conj₂ [FiniteDimensional K M₂] [Algebra.IsSeparable K M₂]
    {τ : Ω ≃ₐ[K] Ω} {α : M₂ ≃ₐ[K] M₁} (hα : ∀ x, algebraMap M₁ Ω (α x) = τ (algebraMap M₂ Ω x))
    (Θ : π₁ᵉᵗ(sM₁) → π₁ᵉᵗ(sM₂))
    (hΘ : ∀ σ, resGal K Ω M₂ (Θ σ) =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M₁ σ * mulEquivAutFiber K Ω τ) :
    IsConjInduced (specRingEquiv₂ α.toRingEquiv) Θ := by
  refine (isConjInduced_iff _ (sM_specRingEquiv₂ hα) Θ).2
    ⟨fieldChangeIso τ.toRingEquiv sM₂, fun σ ↦ resGal_injective (K := K) (Ω := Ω) M₂ ?_⟩
  rw [hΘ, fundamentalGroupMap_autContinuousMulEquivOfIso (sKM K M₂)
    (specIso_sM_sKM (M := M₂) τ) (sM_sKM M₂), fiberIsoMap_fieldChangeIso]
  have h3 : sM₁ ≫ specRingEquiv₂ α.toRingEquiv ≫ sKM K M₂ = sK := by
    rw [specRingEquiv₂_sKM, sM_sKM]
  have c := DFunLike.congr_fun (fundamentalGroupMap_comp (specRingEquiv₂ α.toRingEquiv)
    (sKM K M₂) (sM_specRingEquiv₂ hα) (specIso_sM_sKM (M := M₂) τ) h3) σ
  have c' := DFunLike.congr_fun (fundamentalGroupMap_congr (specRingEquiv₂_sKM α) h3
    (sM_sKM M₁)) σ
  change _ = (mulEquivAutFiber K Ω τ⁻¹).conjAut
    (fundamentalGroupMap (sKM K M₂) (specIso_sM_sKM (M := M₂) τ)
      (fundamentalGroupMap (specRingEquiv₂ α.toRingEquiv) (sM_specRingEquiv₂ hα) σ))
  rw [Aut_conjAut_eq, map_inv, inv_inv]
  exact congrArg (fun s ↦ (mulEquivAutFiber K Ω τ)⁻¹ * s * mulEquivAutFiber K Ω τ)
    (c'.symm.trans c)

omit [IsSepClosed Ω] [Algebra K M₁] [Algebra K M₂] [Algebra M₁ Ω] [Algebra M₂ Ω]
  [IsScalarTower K M₁ Ω] [IsScalarTower K M₂ Ω] in
/-- If conjugation by `τ` carries the fixing subgroup of `A` into that of `B`, then
`B ⊆ τ(A)`. -/
lemma le_map_of_conj_fixingSubgroup {A B : IntermediateField K Ω} (τ : Ω ≃ₐ[K] Ω)
    (h : ∀ g ∈ A.fixingSubgroup, τ * g * τ⁻¹ ∈ B.fixingSubgroup) :
    B ≤ A.map (τ : Ω →ₐ[K] Ω) := by
  intro x hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup (A.map (τ : Ω →ₐ[K] Ω))]
  rintro ⟨g, hg⟩
  have hg' : τ⁻¹ * g * τ ∈ A.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy ↦ by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg (τ y) ⟨y, hy, rfl⟩
      change τ.symm (g (τ y)) = y
      rw [this, AlgEquiv.symm_apply_apply]
  have := h _ hg'
  rw [show τ * (τ⁻¹ * g * τ) * τ⁻¹ = g by group] at this
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x hx

variable (M : Type u) [Field M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]

omit [IsSepClosed Ω] [IsGalois K Ω] in
lemma mem_fixingSubgroup_fieldRange_iff (g : Ω ≃ₐ[K] Ω) :
    g ∈ (IsScalarTower.toAlgHom K M Ω).fieldRange.fixingSubgroup ↔
      ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · exact fun hg x ↦ hg _ ⟨x, rfl⟩
  · rintro hg _ ⟨x, rfl⟩
    exact hg x

/-- `Gal(Ω/M) ⊆ Gal(Ω/K)` is the image of `res : G_M → G_K`. -/
lemma mem_fixingSubgroup_iff_mem_range [IsGalois M Ω] (g : Ω ≃ₐ[K] Ω) :
    g ∈ (IsScalarTower.toAlgHom K M Ω).fieldRange.fixingSubgroup ↔
      mulEquivAutFiber K Ω g ∈ (resGal K Ω M).toMonoidHom.range := by
  rw [mem_fixingSubgroup_fieldRange_iff, mem_range_resGal_iff, MulEquiv.symm_apply_apply]

/-- **Galois correspondence across two fields**: if conjugation by `τ ∈ Gal(Ω/K)` carries the
image of `res : G_{M₂} → G_K` into that of `res : G_{M₁} → G_K`, and conjugation by `τ⁻¹`
carries the image of `G_{M₁}` into that of `G_{M₂}`, then `τ(M₂) = M₁`, i.e. there is a
`K`-isomorphism `α : M₂ ≃ₐ[K] M₁` with `algebraMap (α x) = τ (algebraMap x)`. -/
theorem exists_algEquiv_of_conj_range [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    [IsGalois M₁ Ω] [IsGalois M₂ Ω] (τ : Ω ≃ₐ[K] Ω)
    (h₁ : ∀ γ ∈ (resGal K Ω M₂).toMonoidHom.range,
      mulEquivAutFiber K Ω τ * γ * (mulEquivAutFiber K Ω τ)⁻¹ ∈
        (resGal K Ω M₁).toMonoidHom.range)
    (h₂ : ∀ γ ∈ (resGal K Ω M₁).toMonoidHom.range,
      (mulEquivAutFiber K Ω τ)⁻¹ * γ * mulEquivAutFiber K Ω τ ∈
        (resGal K Ω M₂).toMonoidHom.range) :
    ∃ α : M₂ ≃ₐ[K] M₁, ∀ x, algebraMap M₁ Ω (α x) = τ (algebraMap M₂ Ω x) := by
  set L₁ : IntermediateField K Ω := (IsScalarTower.toAlgHom K M₁ Ω).fieldRange
  set L₂ : IntermediateField K Ω := (IsScalarTower.toAlgHom K M₂ Ω).fieldRange
  have hle₁ : L₁ ≤ L₂.map (τ : Ω →ₐ[K] Ω) := le_map_of_conj_fixingSubgroup τ fun g hg ↦ by
    have hγ := h₁ _ ((mem_fixingSubgroup_iff_mem_range M₂ g).1 hg)
    rw [← map_inv, ← map_mul, ← map_mul] at hγ
    exact (mem_fixingSubgroup_iff_mem_range M₁ _).2 hγ
  have hle₂ : L₂ ≤ L₁.map ((τ⁻¹ : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω) :=
    le_map_of_conj_fixingSubgroup τ⁻¹ fun g hg ↦ by
      have hγ := h₂ _ ((mem_fixingSubgroup_iff_mem_range M₁ g).1 hg)
      rw [← map_inv, ← map_mul, ← map_mul] at hγ
      rw [inv_inv]
      exact (mem_fixingSubgroup_iff_mem_range M₂ _).2 hγ
  haveI : FiniteDimensional K L₁ :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField
      (IsScalarTower.toAlgHom K M₁ Ω)).toLinearEquiv
  haveI : FiniteDimensional K L₂ :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField
      (IsScalarTower.toAlgHom K M₂ Ω)).toLinearEquiv
  haveI : FiniteDimensional K (L₂.map (τ : Ω →ₐ[K] Ω)) :=
    LinearEquiv.finiteDimensional (L₂.equivMap (τ : Ω →ₐ[K] Ω)).toLinearEquiv
  haveI : FiniteDimensional K (L₁.map ((τ⁻¹ : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω)) :=
    LinearEquiv.finiteDimensional (L₁.equivMap ((τ⁻¹ : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω)).toLinearEquiv
  have hr : Module.finrank K L₂ ≤ Module.finrank K L₁ :=
    (IntermediateField.finrank_le_of_le_right hle₂).trans_eq
      (L₁.equivMap ((τ⁻¹ : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω)).toLinearEquiv.finrank_eq.symm
  have hL : L₂.map (τ : Ω →ₐ[K] Ω) = L₁ := (IntermediateField.eq_of_le_of_finrank_le hle₁
    ((L₂.equivMap (τ : Ω →ₐ[K] Ω)).toLinearEquiv.finrank_eq.symm.trans_le hr)).symm
  let e₁ : M₁ ≃ₐ[K] L₁ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M₁ Ω)
  let e₂ : M₂ ≃ₐ[K] L₂ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M₂ Ω)
  refine ⟨e₂.trans (((L₂.equivMap (τ : Ω →ₐ[K] Ω)).trans (IntermediateField.equivOfEq hL)).trans
    e₁.symm), fun x ↦ ?_⟩
  have := congrArg Subtype.val (e₁.apply_symm_apply
    ((IntermediateField.equivOfEq hL) (L₂.equivMap (τ : Ω →ₐ[K] Ω) (e₂ x))))
  exact this

end Res

/-! ### The rel-isom-DGC across fields, Galois form -/

section DGC

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] {M₁ M₂ : Type u} [Field M₁] [Field M₂]
  [NumberField M₁] [NumberField M₂] [Algebra K M₁] [Algebra K M₂] [Algebra M₁ Ω] [Algebra M₂ Ω]
  [IsScalarTower K M₁ Ω] [IsScalarTower K M₂ Ω] [Algebra.IsAlgebraic M₁ Ω]
  [Algebra.IsAlgebraic M₂ Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {C₁ : HypCurve M₁} {C₂ : HypCurve M₂} {hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty}
  {hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty}

omit [Algebra.IsAlgebraic K Ω] [Algebra.IsAlgebraic M₁ Ω] [Algebra.IsAlgebraic M₂ Ω] in
include hc₁ in
/-- Auxiliary: the map `G_{M₁} → G_{M₂}` under an isomorphism over conjugation by `c`. -/
lemma exists_theta_of_res_conj₂ [FiniteDimensional K M₂]
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M₂ Ω Γ(C₂.Xbar, C₂.U)))
    (c : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (hφ : ∀ σ, resGal K Ω M₂ (projGk Ω C₂ hc₂ (φ σ)) =
      c * resGal K Ω M₁ (projGk Ω C₁ hc₁ σ) * c⁻¹) :
    ∃ Θ : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M₁ Ω))) →
        π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M₂ Ω))),
      (∀ s, resGal K Ω M₂ (Θ s) = c * resGal K Ω M₁ s * c⁻¹) ∧
      ∀ σ, projGk Ω C₂ hc₂ (φ σ) = Θ (projGk Ω C₁ hc₁ σ) := by
  let Θ := fun s ↦ projGk Ω C₂ hc₂ (φ (projGk_surjective Ω C₁ hc₁ s).choose)
  have hΘ : ∀ s, resGal K Ω M₂ (Θ s) = c * resGal K Ω M₁ s * c⁻¹ := fun s ↦ by
    change resGal K Ω M₂ (projGk Ω C₂ hc₂ (φ (projGk_surjective Ω C₁ hc₁ s).choose)) = _
    rw [hφ, (projGk_surjective Ω C₁ hc₁ s).choose_spec]
  refine ⟨Θ, hΘ, fun σ ↦ resGal_injective (K := K) (Ω := Ω) M₂ ?_⟩
  rw [hφ, hΘ]

/-- **The rel-isom-DGC across two fields, Galois form**: for number fields `K ⊆ M₁, M₂ ⊆ Ω`
(finite over `K`), hyperbolic curves `C₁` over `M₁` and `C₂` over `M₂` with cusps, and
`c ∈ G_K`, every continuous isomorphism `φ : Π_{U₁} ≃ₜ* Π_{U₂}` with
`res₂ ∘ pr₂ ∘ φ = conj(c) ∘ res₁ ∘ pr₁` is induced, up to a change of base point, by an
isomorphism of schemes `Spec Γ(U₁) ≅ Spec Γ(U₂)` lying over `Spec α` for a `K`-isomorphism
`α : M₂ ≃ₐ[K] M₁` (the restriction of `c⁻¹`). Only `RelIsomDGC M₁` is assumed. -/
theorem exists_isConjInduced_of_relIsomDGC_field [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    (hDGC : RelIsomDGC.Exists M₁)
    (φ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ*
      π₁ᵉᵗ(basePoint Ω C₂ hc₂ ≫ baseChangeSpec M₂ Ω Γ(C₂.Xbar, C₂.U)))
    (c : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (hφ : ∀ σ, resGal K Ω M₂ (projGk Ω C₂ hc₂ (φ σ)) =
      c * resGal K Ω M₁ (projGk Ω C₁ hc₁ σ) * c⁻¹) :
    ∃ (α : M₂ ≃ₐ[K] M₁) (F : Spec Γ(C₁.Xbar, C₁.U) ≅ Spec Γ(C₂.Xbar, C₂.U)),
      F.hom ≫ sKU C₂ = sKU C₁ ≫ specRingEquiv₂ α.toRingEquiv ∧ IsConjInduced F.hom φ := by
  set τ : Ω ≃ₐ[K] Ω := (mulEquivAutFiber K Ω).symm c⁻¹
  have hτ : mulEquivAutFiber K Ω τ = c⁻¹ := MulEquiv.apply_symm_apply _ _
  have h₁ : ∀ γ ∈ (resGal K Ω M₂).toMonoidHom.range,
      mulEquivAutFiber K Ω τ * γ * (mulEquivAutFiber K Ω τ)⁻¹ ∈
        (resGal K Ω M₁).toMonoidHom.range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨σ', rfl⟩ := projGk_surjective Ω C₂ hc₂ s
    obtain ⟨σ, rfl⟩ := φ.surjective σ'
    refine ⟨projGk Ω C₁ hc₁ σ, ?_⟩
    change resGal K Ω M₁ _ =
      mulEquivAutFiber K Ω τ * resGal K Ω M₂ (projGk Ω C₂ hc₂ (φ σ)) *
        (mulEquivAutFiber K Ω τ)⁻¹
    rw [hφ, hτ]
    group
  have h₂ : ∀ γ ∈ (resGal K Ω M₁).toMonoidHom.range,
      (mulEquivAutFiber K Ω τ)⁻¹ * γ * mulEquivAutFiber K Ω τ ∈
        (resGal K Ω M₂).toMonoidHom.range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨σ, rfl⟩ := projGk_surjective Ω C₁ hc₁ s
    refine ⟨projGk Ω C₂ hc₂ (φ σ), ?_⟩
    change resGal K Ω M₂ _ =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M₁ (projGk Ω C₁ hc₁ σ) * mulEquivAutFiber K Ω τ
    rw [hφ, hτ, inv_inv]
  obtain ⟨α, hα⟩ := exists_algEquiv_of_conj_range τ h₁ h₂
  obtain ⟨Θ, hΘ, hφ'⟩ := exists_theta_of_res_conj₂ φ c hφ
  have hΘ' : ∀ s, resGal K Ω M₂ (Θ s) =
      (mulEquivAutFiber K Ω τ)⁻¹ * resGal K Ω M₁ s * mulEquivAutFiber K Ω τ := fun s ↦ by
    rw [hτ, inv_inv]
    exact hΘ s
  obtain ⟨F, hF, HF⟩ := exists_isConjInduced_of_relIsomDGC_twist₂ Ω α.toRingEquiv hDGC φ Θ
    (isConjInduced_of_res_conj₂ hα Θ hΘ') hφ'
  exact ⟨α, F, hF, HF⟩

end DGC

end CurvesJacobian.Cusp
