/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverCusps

/-!
# Lifting maps of curves to the algebraic closure of the function field, element by element

For affine hyperbolic curves `C = (X̄, U)` over `K` and `C' = (X̄', U')` over `K'` and a finite
étale `F : Spec Γ(U') ⟶ Spec Γ(U)`, `CurvesJacobian.Cusp.coverPiHom : Π_{U'} → Π_U` is `π₁ᵉᵗ(F)`
followed by a change of base point. `CoverCusps.lean` compares the cuspidal inertia groups on both
sides through an isomorphism `σ : K(X̄_Ω)^alg ≅ K(X̄'_Ω)^alg` over `ℓ : K(X̄) → K(X̄')`
(`coverσ`). Here the comparison is made **element by element**, for any such `s`:

* `CurvesJacobian.Cusp.arithConj s hs g`: for `g ∈ Gal(K(X̄'_Ω)^alg / K(X̄'))`, the conjugate
  `s⁻¹ ∘ g ∘ s ∈ Gal(K(X̄_Ω)^alg / K(X̄))`;
* **`CurvesJacobian.Cusp.exists_coverPiHom_arithAction`**: there is `t₀ ∈ Π_U` with
  `coverPiHom (arithAction g) = t₀ · arithAction (s⁻¹ g s) · t₀⁻¹` for all `g`.

This is the functoriality of the arithmetic Galois action used for automorphisms of a curve
(`C' = C`, `F` an automorphism) in the MR7 uniqueness argument (`LocAn/InnerRigidAffine.lean`).

## Proof

As in `exists_map_cuspAt_coverHom_le`: naturality of the Galois action along `F` at the arithmetic
generic points (`fundamentalGroupMap_galoisAction_generic`), the change of field along `s`
(`galoisAction_fieldChange`), and the comparison of two changes of base point
(`exists_conjAut_eq_conj`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve
open scoped TensorProduct

universe u

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (F : Type u) [Field F]
  [Algebra F Ω] [IsGalois F Ω] (j : Spec (.of F) ⟶ X)

/-- **Transport of the Galois action along an equality of geometric points.** -/
lemma galoisAction_eqToIso {η η' : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η) (e : η = η') (g : Ω ≃ₐ[F] Ω) :
    autContinuousMulEquivOfIso (eqToIso (congrArg fiber e)) (galoisAction F j h g) =
      galoisAction F j (h.trans e) g := by
  subst e
  change Iso.conjAut _ _ = _
  simp [Iso.conjAut_apply]

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

section Curve

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `arithAction` through the point `arithPt` and the change of base point `arithIso`. -/
lemma arithIso_galoisAction
    (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    autContinuousMulEquivOfIso (arithIso Ω C hc)
        (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc) rfl g) =
      arithAction Ω C hc g := by
  change (eqToIso _ ≪≫ arithFiberIso Ω C hc).conjAut _ = _
  rw [Iso.trans_conjAut]
  change autContinuousMulEquivOfIso (arithFiberIso Ω C hc)
      (autContinuousMulEquivOfIso (eqToIso (congrArg fiber
        (specMap_algebraMap_arithGenPt Ω C hc))) _) = _
  rw [galoisAction_eqToIso _ _ rfl (specMap_algebraMap_arithGenPt Ω C hc)]
  rfl


/-! ### Extending automorphisms of `Ω ⊗ Γ(U)` to `K(X̄_Ω)^alg` -/

/-- `Γ(U_Ω) ≃ Ω ⊗ Γ(U)` (`secToTensor` is bijective). -/
def secTensorEquiv : Γ(geomCurve Ω C, geomOpen Ω C) ≃+* Ω ⊗[K] Γ(C.Xbar, C.U) :=
  RingEquiv.ofBijective (secToTensor Ω C (isAffineOpen_U C hc))
    ⟨fun a b hab ↦ by
      have := congrArg (tensorEmb Ω C (isAffineOpen_U C hc)) hab
      rw [tensorEmb_secToTensor, tensorEmb_secToTensor] at this
      exact Scheme.germToFunctionField_injective _ _ ((curveEquivL Ω _).injective this),
    secToTensor_surjective Ω C (isAffineOpen_U C hc)⟩

/-- **Automorphisms of `Ω ⊗ Γ(U)` extend to `K(X̄_Ω)^alg`.** -/
theorem exists_ringEquiv_tensorEmb (θ : Ω ⊗[K] Γ(C.Xbar, C.U) ≃+* Ω ⊗[K] Γ(C.Xbar, C.U)) :
    ∃ s : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C),
      ∀ r, s (tensorEmb Ω C (isAffineOpen_U C hc) r) =
        (tensorEmb Ω C (isAffineOpen_U C hc) (θ r) : FFClosure (geomCurve Ω C)) := by
  have hU := isAffineOpen_baseChangeOpen Ω C (isAffineOpen_U C hc)
  haveI := functionField_isFractionRing_of_isAffineOpen (geomCurve Ω C) (geomOpen Ω C) hU
  let e := secTensorEquiv Ω C hc
  let θ' : Γ(geomCurve Ω C, geomOpen Ω C) ≃+* Γ(geomCurve Ω C, geomOpen Ω C) :=
    (e.trans θ).trans e.symm
  let ρ₀ : (geomCurve Ω C).functionField ≃+* (geomCurve Ω C).functionField :=
    IsFractionRing.ringEquivOfRingEquiv θ'
  let eL := curveEquivL Ω (transcendental_geomCoord Ω C)
  let ρ₁ : (geomData Ω C).L ≃+* (geomData Ω C).L := (eL.symm.trans ρ₀).trans eL
  haveI := isTorsionFree_of_fields (geomData Ω C).L (FFClosure (geomCurve Ω C))
  haveI : Algebra.IsAlgebraic (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
    Algebra.IsAlgebraic.tower_top (K := K₀ Ω (coordT (geomCoord Ω C))) _
  haveI : IsAlgClosure (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
    ⟨inferInstance, inferInstance⟩
  refine ⟨IsAlgClosure.equivOfEquiv (FFClosure (geomCurve Ω C)) (FFClosure (geomCurve Ω C)) ρ₁,
    fun r ↦ ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective r
  have h1 : tensorEmb Ω C (isAffineOpen_U C hc) (e a) =
      eL ((geomCurve Ω C).germToFunctionField (geomOpen Ω C) a) :=
    tensorEmb_secToTensor Ω C (isAffineOpen_U C hc) a
  have h2 : tensorEmb Ω C (isAffineOpen_U C hc) (θ (e a)) =
      eL ((geomCurve Ω C).germToFunctionField (geomOpen Ω C) (θ' a)) := by
    rw [← tensorEmb_secToTensor]
    change _ = tensorEmb Ω C (isAffineOpen_U C hc) (e (e.symm (θ (e a))))
    rw [RingEquiv.apply_symm_apply]
  change IsAlgClosure.equivOfEquiv _ _ ρ₁ (algebraMap (geomData Ω C).L _ _) =
    algebraMap (geomData Ω C).L _ _
  rw [IsAlgClosure.equivOfEquiv_algebraMap, h1, h2]
  congr 1
  change eL (ρ₀ (eL.symm (eL _))) = _
  rw [RingEquiv.symm_apply_apply]
  exact congrArg eL (IsFractionRing.ringEquivOfRingEquiv_algebraMap θ' a)

/-- **A `K`-automorphism `α` of `Γ(U)` lifts to `K(X̄_Ω)^alg`, fixing `Ω`.** -/
theorem exists_lift_algEquiv (α : Γ(C.Xbar, C.U) ≃ₐ[K] Γ(C.Xbar, C.U)) :
    ∃ s : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C),
      (∀ r, s (tensorEmb Ω C (isAffineOpen_U C hc) r) =
        (tensorEmb Ω C (isAffineOpen_U C hc)
          (Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[K] Ω) α r) :
            FFClosure (geomCurve Ω C))) ∧
      (∀ c : Ω, s (algebraMap Ω _ c) = algebraMap Ω _ c) ∧
        ∀ a, s (secEmb Ω C (isAffineOpen_U C hc) a) = secEmb Ω C (isAffineOpen_U C hc) (α a) := by
  obtain ⟨s, hs⟩ := exists_ringEquiv_tensorEmb Ω C hc
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[K] Ω) α).toRingEquiv
  refine ⟨s, hs, fun c ↦ ?_, fun a ↦ ?_⟩
  · have := hs (c ⊗ₜ 1)
    rw [coe_tensorEmb_tmul, map_one, mul_one] at this
    rw [this]
    simp [coe_tensorEmb_tmul]
  · rw [secEmb_apply, secEmb_apply, hs]
    rfl

/-- **Every `ψ ∈ Gal(Ω/K)` is the restriction of an element of `Gal(K(X̄_Ω)^alg / K(X̄))`.** -/
theorem exists_arithAut_restrict (ψ : Ω ≃ₐ[K] Ω) :
    ∃ g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C),
      ∀ c : Ω, g (algebraMap Ω _ c) = algebraMap Ω _ (ψ c) := by
  obtain ⟨s, hs⟩ := exists_ringEquiv_tensorEmb Ω C hc
    (Algebra.TensorProduct.congr ψ
      (AlgEquiv.refl : Γ(C.Xbar, C.U) ≃ₐ[K] Γ(C.Xbar, C.U))).toRingEquiv
  have hsec : ∀ a, s (secEmb Ω C (isAffineOpen_U C hc) a) = secEmb Ω C (isAffineOpen_U C hc) a :=
    fun a ↦ by
      rw [secEmb_apply, hs]
      simp
  have hfix : ∀ x : arithFF Ω C hc, s x = x := fun x ↦ by
    obtain ⟨a, b, rfl⟩ := exists_eq_div_secToArithFF Ω C hc x
    rw [Subfield.coe_div, map_div₀]
    exact congrArg₂ (· / ·) (hsec a) (hsec b)
  refine ⟨{ s with commutes' := fun x ↦ hfix x }, fun c ↦ ?_⟩
  change s _ = _
  have := hs (c ⊗ₜ 1)
  rw [coe_tensorEmb_tmul, map_one, mul_one] at this
  rw [this]
  simp [coe_tensorEmb_tmul]

/-- The restriction to `Ω` of `g ∈ Gal(K(X̄_Ω)^alg / K(X̄))` (`g` maps `Ω` onto `Ω`). -/
def resOmegaFun
    (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) (c : Ω) : Ω :=
  (exists_algebraMap_eq_apply (K₀ := K) Ω C ((g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc]
    FFClosure (geomCurve Ω C)) : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C))
    (algEquiv_algebraMap_K Ω C hc g) c).choose

lemma algebraMap_resOmegaFun
    (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) (c : Ω) :
    algebraMap Ω (FFClosure (geomCurve Ω C)) (resOmegaFun Ω C hc g c) =
      g (algebraMap Ω (FFClosure (geomCurve Ω C)) c) :=
  (exists_algebraMap_eq_apply (K₀ := K) Ω C ((g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc]
    FFClosure (geomCurve Ω C)) : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C))
    (algEquiv_algebraMap_K Ω C hc g) c).choose_spec

/-- **The restriction `Gal(K(X̄_Ω)^alg / K(X̄)) → Gal(Ω / K)`** (surjective:
`resOmega_surjective`). -/
def resOmega : (FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) →*
    (Ω ≃ₐ[K] Ω) where
  toFun g :=
    { toFun := resOmegaFun Ω C hc g
      invFun := resOmegaFun Ω C hc g⁻¹
      left_inv c := (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
        rw [algebraMap_resOmegaFun, algebraMap_resOmegaFun, AlgEquiv.aut_inv,
          AlgEquiv.symm_apply_apply])
      right_inv c := (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
        rw [algebraMap_resOmegaFun, algebraMap_resOmegaFun, AlgEquiv.aut_inv,
          AlgEquiv.apply_symm_apply])
      map_mul' c d := (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
        simp only [map_mul, algebraMap_resOmegaFun])
      map_add' c d := (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
        simp only [map_add, algebraMap_resOmegaFun])
      commutes' c := (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
        rw [algebraMap_resOmegaFun, ← ffEmb_algebraMap Ω C hc]
        exact g.commutes (⟨ffEmb Ω C hc (algebraMap K C.Xbar.functionField c),
          algebraMap K C.Xbar.functionField c, rfl⟩ : arithFF Ω C hc)) }
  map_one' := AlgEquiv.ext fun c ↦ (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
    change algebraMap Ω _ (resOmegaFun Ω C hc 1 c) = _
    rw [algebraMap_resOmegaFun]
    rfl)
  map_mul' g h := AlgEquiv.ext fun c ↦ (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
    change algebraMap Ω _ (resOmegaFun Ω C hc (g * h) c) =
      algebraMap Ω _ (resOmegaFun Ω C hc g (resOmegaFun Ω C hc h c))
    rw [algebraMap_resOmegaFun, algebraMap_resOmegaFun, algebraMap_resOmegaFun]
    rfl)

lemma algebraMap_resOmega
    (g : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) (c : Ω) :
    algebraMap Ω (FFClosure (geomCurve Ω C)) (resOmega Ω C hc g c) =
      g (algebraMap Ω (FFClosure (geomCurve Ω C)) c) :=
  algebraMap_resOmegaFun Ω C hc g c

theorem resOmega_surjective : Function.Surjective (resOmega Ω C hc) := fun ψ ↦ by
  obtain ⟨g, hg⟩ := exists_arithAut_restrict Ω C hc ψ
  refine ⟨g, AlgEquiv.ext fun c ↦ (algebraMap Ω (FFClosure (geomCurve Ω C))).injective ?_⟩
  rw [algebraMap_resOmega, hg]

end Curve

section Cover

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {K' : Type u} [Field K'] [CharZero K'] [Algebra K' Ω] [Algebra.IsAlgebraic K' Ω]
  (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
  (F : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale F]
  (s : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C'))
  (hs : ∀ c : arithFF Ω C hc, s (algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C)) c) =
    algebraMap (arithFF Ω C' hc') (FFClosure (geomCurve Ω C')) (coverFF Ω C hc C' hc' F c))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **The conjugate `s⁻¹ ∘ g ∘ s`** of `g ∈ Gal(K(X̄'_Ω)^alg / K(X̄'))`, an element of
`Gal(K(X̄_Ω)^alg / K(X̄))`. -/
def arithConj
    (g : FFClosure (geomCurve Ω C') ≃ₐ[arithFF Ω C' hc'] FFClosure (geomCurve Ω C')) :
    FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C) :=
  { (s.trans g.toRingEquiv).trans s.symm with
    commutes' := fun c ↦ by
      change s.symm (g (s (algebraMap (arithFF Ω C hc) _ c))) = _
      rw [hs, g.commutes, ← hs, RingEquiv.symm_apply_apply] }

include hs in
/-- The point equation `x_{U'} ≫ F = Spec s ≫ x_U` for any `s` over `ℓ` (`arithPt_comp_cover`
for `coverσ`). -/
lemma arithPt_comp_cover_of :
    arithPt Ω C' hc' ≫ F = specIso s ≫ arithPt Ω C hc := by
  letI := (coverFF Ω C hc C' hc' F).toAlgebra
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap (arithFF Ω C' hc')
        (FFClosure (geomCurve Ω C')))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (arithFF Ω C hc) (arithFF Ω C' hc'))) =
      specIso s ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C)))) := by
    rw [specIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ (hs c).symm
  rw [arithPt, arithPt, Category.assoc, arithGenPt_comp_cover Ω C hc C' hc' F, ← Category.assoc,
    e1, Category.assoc]

lemma arithConj_apply
    (g : FFClosure (geomCurve Ω C') ≃ₐ[arithFF Ω C' hc'] FFClosure (geomCurve Ω C'))
    (x : FFClosure (geomCurve Ω C)) :
    arithConj Ω C hc C' hc' F s hs g x = s.symm (g (s x)) := rfl

lemma arithConj_mul
    (g g' : FFClosure (geomCurve Ω C') ≃ₐ[arithFF Ω C' hc'] FFClosure (geomCurve Ω C')) :
    arithConj Ω C hc C' hc' F s hs (g * g') =
      arithConj Ω C hc C' hc' F s hs g * arithConj Ω C hc C' hc' F s hs g' := by
  ext x
  simp [arithConj_apply]

set_option maxHeartbeats 800000 in
-- the naturality and change-of-field rewrites unfold large fibre-functor terms
/-- **Element-wise functoriality of the arithmetic Galois action**: for every `L₀`-isomorphism
`s : K(X̄_Ω)^alg ≅ K(X̄'_Ω)^alg` over `ℓ` there is `t₀ ∈ Π_U` with
`coverPiHom (arithAction g) = t₀ · arithAction (s⁻¹ g s) · t₀⁻¹`. -/
theorem exists_coverPiHom_arithAction [IsSlimGk K Ω] [IsSlimGk K' Ω] :
    ∃ t₀ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
      ∀ g : FFClosure (geomCurve Ω C') ≃ₐ[arithFF Ω C' hc'] FFClosure (geomCurve Ω C'),
        coverPiHom Ω C hc C' hc' F (arithAction Ω C' hc' g) =
          t₀ * arithAction Ω C hc (arithConj Ω C hc C' hc' F s hs g) * t₀⁻¹ := by
  letI := (coverFF Ω C hc C' hc' F).toAlgebra
  letI := coverAlgFV Ω C hc C' hc' F
  haveI : IsScalarTower (arithFF Ω C hc) (arithFF Ω C' hc') (FFClosure (geomCurve Ω C')) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := finiteDimensional_coverFF Ω C hc C' hc' F
  haveI := isTorsionFree_of_fields (arithFF Ω C hc) (FFClosure (geomCurve Ω C'))
  haveI : Algebra.IsAlgebraic (arithFF Ω C hc) (FFClosure (geomCurve Ω C')) :=
    Algebra.IsAlgebraic.trans (arithFF Ω C hc) (arithFF Ω C' hc') _
  haveI : IsAlgClosure (arithFF Ω C hc) (FFClosure (geomCurve Ω C')) :=
    ⟨inferInstance, inferInstance⟩
  let δ := fiberIsoMap F rfl rfl (arithIso Ω C' hc') ≪≫ coverFib Ω C hc C' hc' F
  let γ := eqToIso (congrArg fiber (arithPt_comp_cover_of Ω C hc C' hc' F s hs)) ≪≫
    fieldChangeIso s (arithPt Ω C hc)
  obtain ⟨t₀, ht₀⟩ := exists_conjAut_eq_conj (arithIso Ω C hc) (γ.symm ≪≫ δ)
  refine ⟨t₀, fun g ↦ ?_⟩
  have hj := arithGenPt_comp_cover Ω C hc C' hc' F
  -- naturality along `F`
  have h1 := fundamentalGroupMap_galoisAction_generic F (arithGenPt Ω C' hc')
    (arithGenPt Ω C hc) hj g
  -- the change of field along `s`
  have h2 := galoisAction_fieldChange s (arithPt Ω C hc) (arithFF Ω C hc) hs
    (arithGenPt Ω C hc) rfl (g.restrictScalars (arithFF Ω C hc))
  have h3 := galoisAction_eqToIso (arithFF Ω C hc) (arithGenPt Ω C hc)
    (specAlgebraMap_comp_generic F (arithGenPt Ω C' hc') (arithGenPt Ω C hc) hj)
    (arithPt_comp_cover_of Ω C hc C' hc' F s hs) (g.restrictScalars (arithFF Ω C hc))
  have hγ : autContinuousMulEquivOfIso γ (fundamentalGroupMap F rfl
      (galoisAction (arithFF Ω C' hc') (arithGenPt Ω C' hc') rfl g)) =
      galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc) rfl
        (arithConj Ω C hc C' hc' F s hs g) := by
    change (eqToIso _ ≪≫ fieldChangeIso s (arithPt Ω C hc)).conjAut _ = _
    rw [Iso.trans_conjAut]
    change autContinuousMulEquivOfIso (fieldChangeIso s (arithPt Ω C hc))
      (autContinuousMulEquivOfIso (eqToIso _) _) = _
    rw [h1, h3]
    refine h2.trans ?_
    exact galoisAction_eq_of_apply_eq _ _ _ _ _ _ _ fun _ ↦ rfl
  set z := fundamentalGroupMap F rfl
    (galoisAction (arithFF Ω C' hc') (arithGenPt Ω C' hc') rfl g) with hz
  have e1 : coverPiHom Ω C hc C' hc' F (arithAction Ω C' hc' g) = δ.conjAut z := by
    rw [← arithIso_galoisAction Ω C' hc' g, coverPiHom_apply,
      fundamentalGroupMap_autContinuousMulEquivOfIso F rfl rfl]
    exact (Iso.trans_conjAut _ _ _).symm
  have e2 : arithAction Ω C hc (arithConj Ω C hc C' hc' F s hs g) =
      (arithIso Ω C hc).conjAut (γ.conjAut z) := by
    rw [← arithIso_galoisAction Ω C hc, ← hγ]
    rfl
  have e3 : (γ.symm ≪≫ δ).conjAut (γ.conjAut z) = δ.conjAut z := by
    rw [← Iso.trans_conjAut, Iso.self_symm_id_assoc]
  rw [e1, e2, ← ht₀, e3]

end Cover

end CurvesJacobian.Cusp
