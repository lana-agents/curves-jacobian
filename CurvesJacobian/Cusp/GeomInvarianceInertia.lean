/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GeomInvariance
import CurvesJacobian.Cusp.FieldExtIso
import CurvesJacobian.Cusp.NonRationalFill
import CurvesJacobian.Cusp.CurveInertiaIsoAny
import CurvesJacobian.Cusp.CuspConj
import CurvesJacobian.Cusp.FillElemOp

/-!
# `Δ_{U,Ω'} ≅ Δ_{U,Ω}` respects the cuspidal inertia groups

Let `C = (X̄, U)` be an affine hyperbolic curve over a number field `K` (with a cusp), `Ω` an
algebraic closure of `K` and `Ω' ⊇ Ω` any algebraically closed field (e.g. `Ω' = \bar{K_v}`). By
`CurvesJacobian.Cusp.geomExtend_bijective`, `U_{Ω'} ⟶ U_Ω` induces `π₁ᵉᵗ(U_{Ω'}) ≅ π₁ᵉᵗ(U_Ω)`.
Here we show that this isomorphism matches the cuspidal inertia groups (lead decision D-c, for
[LocAn] Cor. 15.5 and for filling in cusps after base change).

* `CurvesJacobian.Cusp.extL : L →+* L'` (function fields of `X̄_Ω`, `X̄_{Ω'}`), induced by
  `Ω ⊗[K] Γ(U) → Ω' ⊗[K] Γ(U)`, and an extension `CurvesJacobian.Cusp.extF : F →+* F'` to the
  algebraic closures `F = K(X̄_Ω)^alg`, `F' = K(X̄_{Ω'})^alg`; `extResGal : Gal(F'/L') → Gal(F/L)`.
* `CurvesJacobian.Cusp.geomCompare : π₁ᵉᵗ(U_{Ω'}) ≃* π₁ᵉᵗ(U_Ω)` at the geometric generic points
  (the map of `U_{Ω'} ⟶ U_Ω` followed by the change of field `Spec F' ⟶ Spec F` of the geometric
  point, `AlgebraicGeometry.FiniteEtale.fieldExtEquiv`).
* `CurvesJacobian.Cusp.map_cuspInertia_geomCompare`: the cuspidal inertia group of a place `W'`
  of `F'` over a cusp goes **onto** that of `W' ∩ F`.
* **`CurvesJacobian.Cusp.map_geomCusps_geomCompare`**: `I ∈ geomCusps Ω' C ↔ Ψ(I) ∈ geomCusps Ω C`.

## Proof

1. Inertia goes into inertia (`map_cuspInertia_geomCompare_le`): naturality of the Galois action
   (`fundamentalGroupMap_galoisAction`, `galoisAction_fieldExt`) and restriction of inertia
   elements along `extF` (`mem_inertia_comap_of_mem`).
2. Equality: `I = I_{W' ∩ F}` is commutative (`cuspInertia_mul_comm`, via
   `π₁ᵉᵗ(U_Ω) ≃ₜ* Π̂_{g,r}`), so `Ψ⁻¹(I)` is a commutative subgroup containing `I' = I_{W'}`; it
   normalises `I'`, hence lies in its commensurator, which is `I'` (`geomCusps_commensurator`).
3. Every cusp is hit (`exists_cusp_lift`): for a place `W` of `F` over a cusp, its restriction to
   `K(X̄_Ω)` is the local ring at a closed point `y ∉ U_Ω`; a function `τ` with poles exactly at `y`
   (`exists_chartOne_eq`) stays transcendental over `Ω'` (`transcendental_extF`, using
   `Ω' ⊗[K] Γ(U) = Ω' ⊗[Ω] (Ω ⊗[K] Γ(U))` and duals of `Ω'` over `Ω`), so some place `W' ⊇ Ω'`
   of `F'` has a pole at `τ` (`exists_valuationSubring_notMem`); then `W' ∩ F` and `W` agree on `L`,
   their inertia groups are conjugate (`exists_cuspInertia_eq_conj`), and conjugates of cuspidal
   inertia groups of `U_{Ω'}` are cuspidal inertia groups (`cuspInertia_comap`, `genericL_spec`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Orbifold AffOrbicurve PreGaloisCategory
open scoped TensorProduct Pointwise

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω Ω' : Type u) [Field Ω] [Field Ω']
  [Algebra K Ω] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω]
  [IsAlgClosed Ω'] [CharZero Ω] [CharZero Ω'] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

omit [NumberField K] [IsAlgClosed Ω] [IsAlgClosed Ω'] [CharZero Ω] [CharZero Ω'] in
/-- `Γ(U) ⊗` is injective on `Ω → Ω'` (`Γ(U)` is flat over the field `K`). -/
lemma extendTensor_injective (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (extendTensor K Ω Ω' R) := by
  have h : (extendTensor K Ω Ω' R).toLinearMap =
      LinearMap.rTensor R (IsScalarTower.toAlgHom K Ω Ω').toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have hi : Function.Injective (IsScalarTower.toAlgHom K Ω Ω').toLinearMap :=
    (algebraMap Ω Ω').injective
  have := Module.Flat.rTensor_preserves_injective_linearMap (M := R)
    (IsScalarTower.toAlgHom K Ω Ω').toLinearMap hi
  rw [← h] at this
  exact this

omit [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω'] [CharZero Ω'] in
include hc in
lemma secToTensor_injective :
    Function.Injective (secToTensor Ω C (isAffineOpen_U C hc)) := by
  intro a b hab
  have h := congrArg (tensorEmb Ω C (isAffineOpen_U C hc)) hab
  rw [tensorEmb_secToTensor, tensorEmb_secToTensor] at h
  exact Scheme.germToFunctionField_injective _ _ ((curveEquivL Ω _).injective h)

/-- The ring map `Γ(U_Ω) → L'`, `s ↦ θ'(ext(s))`. -/
def secToL' : Γ(geomCurve Ω C, geomOpen Ω C) →+* (geomData Ω' C).L :=
  (tensorEmb Ω' C (isAffineOpen_U C hc)).comp
    ((extendTensor K Ω Ω' Γ(C.Xbar, C.U)).toRingHom.comp (secToTensor Ω C (isAffineOpen_U C hc)))

include hc in
lemma secToL'_injective : Function.Injective (secToL' Ω Ω' C hc) :=
  (tensorEmb_injective Ω' C (isAffineOpen_U C hc)).comp
    ((extendTensor_injective Ω Ω' _).comp (secToTensor_injective Ω C hc))

omit [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω'] [CharZero Ω']
  [IsAlgClosed Ω] [CharZero Ω] in
include hc in
lemma isFractionRing_geomOpen :
    IsFractionRing Γ(geomCurve Ω C, geomOpen Ω C) (geomCurve Ω C).functionField :=
  functionField_isFractionRing_of_isAffineOpen (geomCurve Ω C) (geomOpen Ω C)
    (isAffineOpen_baseChangeOpen Ω C (isAffineOpen_U C hc))

/-- **The map of function fields `K(X̄_Ω) → L' ≅ K(X̄_{Ω'})`** extending
`Ω ⊗ Γ(U) → Ω' ⊗ Γ(U)`. -/
def extFF : (geomCurve Ω C).functionField →+* (geomData Ω' C).L :=
  haveI := isFractionRing_geomOpen Ω C hc
  IsFractionRing.lift (secToL'_injective Ω Ω' C hc)

/-- **`L → L'`**. -/
def extL : (geomData Ω C).L →+* (geomData Ω' C).L :=
  (extFF Ω Ω' C hc).comp (curveEquivL Ω (transcendental_geomCoord Ω C)).symm.toRingHom

lemma extL_tensorEmb (t : Ω ⊗[K] Γ(C.Xbar, C.U)) :
    extL Ω Ω' C hc (tensorEmb Ω C (isAffineOpen_U C hc) t) =
      tensorEmb Ω' C (isAffineOpen_U C hc) (extendTensor K Ω Ω' _ t) := by
  haveI := isFractionRing_geomOpen Ω C hc
  obtain ⟨s, rfl⟩ := secToTensor_surjective Ω C (isAffineOpen_U C hc) t
  rw [extL, RingHom.comp_apply, tensorEmb_secToTensor]
  change extFF Ω Ω' C hc ((curveEquivL Ω _).symm (curveEquivL Ω _ _)) = _
  rw [RingEquiv.symm_apply_apply, extFF]
  exact IsFractionRing.lift_algebraMap (secToL'_injective Ω Ω' C hc) s

/-- `F' = K(X̄_{Ω'})^alg` as an `L`-algebra through `extL`. -/
abbrev algLF' : Algebra (geomData Ω C).L (FFClosure (geomCurve Ω' C)) :=
  ((algebraMap (geomData Ω' C).L (FFClosure (geomCurve Ω' C))).comp (extL Ω Ω' C hc)).toAlgebra

omit [NumberField K] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω']
  [CharZero Ω'] in
lemma isAlgebraic_geomL : Algebra.IsAlgebraic (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
  Algebra.IsAlgebraic.tower_top (K := K₀ Ω (coordT (geomCoord Ω C))) _

omit [NumberField K] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω']
  [CharZero Ω'] in
lemma isTorsionFree_geomL : Module.IsTorsionFree (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
  haveI : FaithfulSMul (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (RingHom.injective (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C))))
  FaithfulSMul.to_isTorsionFree _ _

omit [NumberField K] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω']
  [CharZero Ω'] in
lemma isGalois_geomL : IsGalois (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
  haveI := isAlgebraic_geomL Ω C
  haveI := isTorsionFree_geomL Ω C
  haveI : IsAlgClosure (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
    ⟨inferInstance, inferInstance⟩
  inferInstance

/-- **`F → F'`**: an extension of `extL` to the algebraic closures. -/
def extF : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω' C) :=
  letI := algLF' Ω Ω' C hc
  haveI := isAlgebraic_geomL Ω C
  haveI := isTorsionFree_geomL Ω C
  haveI : FaithfulSMul (geomData Ω C).L (FFClosure (geomCurve Ω' C)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (RingHom.injective (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω' C))))
  haveI : Module.IsTorsionFree (geomData Ω C).L (FFClosure (geomCurve Ω' C)) :=
    FaithfulSMul.to_isTorsionFree _ _
  (IsAlgClosed.lift (R := (geomData Ω C).L) (S := FFClosure (geomCurve Ω C))
    (M := FFClosure (geomCurve Ω' C))).toRingHom

lemma extF_algebraMap (z : (geomData Ω C).L) :
    extF Ω Ω' C hc (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C)) z) =
      algebraMap (geomData Ω' C).L (FFClosure (geomCurve Ω' C)) (extL Ω Ω' C hc z) := by
  letI := algLF' Ω Ω' C hc
  haveI := isAlgebraic_geomL Ω C
  haveI := isTorsionFree_geomL Ω C
  haveI : FaithfulSMul (geomData Ω C).L (FFClosure (geomCurve Ω' C)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (RingHom.injective (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω' C))))
  haveI : Module.IsTorsionFree (geomData Ω C).L (FFClosure (geomCurve Ω' C)) :=
    FaithfulSMul.to_isTorsionFree _ _
  exact (IsAlgClosed.lift (R := (geomData Ω C).L) (S := FFClosure (geomCurve Ω C))
    (M := FFClosure (geomCurve Ω' C))).commutes z

/-- **Restriction `Gal(F'/L') → Gal(F/L)`** along `extF` (`F/L` is normal). -/
def extResGal (g' : FFClosure (geomCurve Ω' C) ≃ₐ[(geomData Ω' C).L] FFClosure (geomCurve Ω' C)) :
    FFClosure (geomCurve Ω C) ≃ₐ[(geomData Ω C).L] FFClosure (geomCurve Ω C) :=
  letI : Algebra (FFClosure (geomCurve Ω C)) (FFClosure (geomCurve Ω' C)) :=
    (extF Ω Ω' C hc).toAlgebra
  letI : Algebra (geomData Ω C).L (geomData Ω' C).L := (extL Ω Ω' C hc).toAlgebra
  haveI : IsScalarTower (geomData Ω C).L (geomData Ω' C).L (FFClosure (geomCurve Ω' C)) :=
    IsScalarTower.of_algebraMap_eq fun z ↦ extF_algebraMap Ω Ω' C hc z
  haveI := isGalois_geomL Ω C
  (g'.restrictScalars (geomData Ω C).L).restrictNormal (FFClosure (geomCurve Ω C))

lemma extF_extResGal
    (g' : FFClosure (geomCurve Ω' C) ≃ₐ[(geomData Ω' C).L] FFClosure (geomCurve Ω' C))
    (z : FFClosure (geomCurve Ω C)) :
    extF Ω Ω' C hc (extResGal Ω Ω' C hc g' z) = g' (extF Ω Ω' C hc z) := by
  letI : Algebra (FFClosure (geomCurve Ω C)) (FFClosure (geomCurve Ω' C)) :=
    (extF Ω Ω' C hc).toAlgebra
  letI : Algebra (geomData Ω C).L (geomData Ω' C).L := (extL Ω Ω' C hc).toAlgebra
  haveI : IsScalarTower (geomData Ω C).L (geomData Ω' C).L (FFClosure (geomCurve Ω' C)) :=
    IsScalarTower.of_algebraMap_eq fun z ↦ extF_algebraMap Ω Ω' C hc z
  haveI := isGalois_geomL Ω C
  exact AlgEquiv.restrictNormal_commutes (g'.restrictScalars (geomData Ω C).L)
    (FFClosure (geomCurve Ω C)) z

/-! ### The generic geometric points of `U_Ω = Spec (Ω ⊗ Γ(U))` -/

/-- The generic point `Spec L ⟶ U_Ω = Spec (Ω ⊗[K] Γ(U))`. -/
abbrev genT : Spec (.of (geomData Ω C).L) ⟶ Spec (.of (Ω ⊗[K] Γ(C.Xbar, C.U))) :=
  Spec.map (CommRingCat.ofHom (tensorEmb Ω C (isAffineOpen_U C hc)))

/-- The geometric generic point `Spec F ⟶ U_Ω`. -/
abbrev genPt : Spec (.of (FFClosure (geomCurve Ω C))) ⟶ Spec (.of (Ω ⊗[K] Γ(C.Xbar, C.U))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C)))) ≫
    genT Ω C hc

/-- `U_{Ω'} ⟶ U_Ω` maps the geometric generic point to the geometric generic point. -/
lemma genPt_extendSpec :
    genPt Ω' C hc ≫ extendSpec K Ω Ω' Γ(C.Xbar, C.U) =
      specHom (extF Ω Ω' C hc) ≫ genPt Ω C hc := by
  simp only [genPt, genT, extendSpec, specHom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun t ↦ ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [extF_algebraMap, extL_tensorEmb]

lemma genPt_extendSpec' :
    Spec.map (CommRingCat.ofHom (algebraMap (geomData Ω' C).L (FFClosure (geomCurve Ω' C)))) ≫
        genT Ω' C hc ≫ extendSpec K Ω Ω' Γ(C.Xbar, C.U) =
      specHom (extF Ω Ω' C hc) ≫ genPt Ω C hc := by
  rw [← genPt_extendSpec, genPt, Category.assoc]

include hc in
omit [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω'] [CharZero Ω']
  [IsAlgClosed Ω] [CharZero Ω] in
lemma connectedSpace_specTensor' : ConnectedSpace (Spec (.of (Ω ⊗[K] Γ(C.Xbar, C.U)))) := by
  haveI := isIntegral_specTensor Ω C hc
  infer_instance

/-- **`π₁ᵉᵗ(U_{Ω'}) → π₁ᵉᵗ(U_Ω)` maps inertia into inertia**: the image of the inertia subgroup of a
place `W'` of `F'` (Galois action through the generic point) lies in the image under the change
of field `fieldExtEquiv` of the inertia subgroup of `W' ∩ F`. -/
theorem map_galInertia_extendSpec_le (W' : ValuationSubring (FFClosure (geomCurve Ω' C))) :
    haveI := connectedSpace_specTensor' Ω C hc
    haveI := isGalois_geomL Ω C
    haveI := isGalois_geomL Ω' C
    (galInertia (genPt Ω' C hc) (geomData Ω' C).L (genT Ω' C hc) rfl W').map
        (fundamentalGroupMap (extendSpec K Ω Ω' Γ(C.Xbar, C.U))
          (genPt_extendSpec Ω Ω' C hc)).toMonoidHom ≤
      (galInertia (genPt Ω C hc) (geomData Ω C).L (genT Ω C hc) rfl
        (W'.comap (extF Ω Ω' C hc))).map
          (fieldExtEquiv (extF Ω Ω' C hc) (genPt Ω C hc)).toMulEquiv.toMonoidHom := by
  haveI := connectedSpace_specTensor' Ω C hc
  haveI := isGalois_geomL Ω C
  haveI := isGalois_geomL Ω' C
  rw [galInertia, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨g', hg', rfl⟩, rfl⟩
  change fundamentalGroupMap (extendSpec K Ω Ω' Γ(C.Xbar, C.U)) (genPt_extendSpec Ω Ω' C hc)
    (galoisAction (geomData Ω' C).L (genT Ω' C hc) rfl g') ∈ _
  rw [fundamentalGroupMap_galoisAction (geomData Ω' C).L (genT Ω' C hc)
    (extendSpec K Ω Ω' Γ(C.Xbar, C.U)) rfl (genPt_extendSpec Ω Ω' C hc)
    (genPt_extendSpec' Ω Ω' C hc) g']
  refine galInertia_le_map_fieldExt (extF Ω Ω' C hc) (genPt Ω C hc) (geomData Ω C).L
    (geomData Ω' C).L (genT Ω C hc) (genT Ω' C hc ≫ extendSpec K Ω Ω' Γ(C.Xbar, C.U)) rfl
    (genPt_extendSpec' Ω Ω' C hc) (extResGal Ω Ω' C hc) (extF_extResGal Ω Ω' C hc) W' ?_
  exact Subgroup.subset_closure ⟨g', hg', rfl⟩

/-! ### Constants, sections and centredness under `extF` -/

lemma extF_tensorEmb (t : Ω ⊗[K] Γ(C.Xbar, C.U)) :
    extF Ω Ω' C hc (tensorEmb Ω C (isAffineOpen_U C hc) t : FFClosure (geomCurve Ω C)) =
      (tensorEmb Ω' C (isAffineOpen_U C hc) (extendTensor K Ω Ω' _ t) :
        FFClosure (geomCurve Ω' C)) := by
  have := extF_algebraMap Ω Ω' C hc (tensorEmb Ω C (isAffineOpen_U C hc) t)
  rw [extL_tensorEmb] at this
  exact this

lemma extF_secEmb (a : Γ(C.Xbar, C.U)) :
    extF Ω Ω' C hc (secEmb Ω C (isAffineOpen_U C hc) a) = secEmb Ω' C (isAffineOpen_U C hc) a := by
  rw [secEmb_apply, secEmb_apply, extF_tensorEmb, extendTensor_tmul, map_one]

lemma extF_algebraMap_Omega (c : Ω) :
    extF Ω Ω' C hc (algebraMap Ω (FFClosure (geomCurve Ω C)) c) =
      algebraMap Ω' (FFClosure (geomCurve Ω' C)) (algebraMap Ω Ω' c) := by
  rw [← coe_tensorEmb_algebraMap Ω C (isAffineOpen_U C hc), extF_tensorEmb,
    ← coe_tensorEmb_algebraMap Ω' C (isAffineOpen_U C hc)]
  congr 2

omit [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω'] [CharZero Ω'] in
/-- **Centred places** (any algebraically closed `Ω`): `W` is centred on `U_Ω` iff `W ⊇ Ω` and
`W ⊇ Γ(U)`. -/
lemma isCentredOn_geomOpen_iff' (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C) W ↔
      (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W) ∧
        ∀ a : Γ(C.Xbar, C.U), secEmb Ω C (isAffineOpen_U C hc) a ∈ W := by
  refine ⟨fun hW ↦ ⟨hW.1, fun a ↦ ?_⟩, fun hW ↦ ⟨hW.1, fun s ↦ ?_⟩⟩
  · obtain ⟨s, hs⟩ := secToTensor_surjective Ω C (isAffineOpen_U C hc) (1 ⊗ₜ a)
    have := hW.2 s
    rw [secEmb_apply, ← hs, tensorEmb_secToTensor]
    exact this
  · have key : ∀ t : Ω ⊗[K] Γ(C.Xbar, C.U),
        (tensorEmb Ω C (isAffineOpen_U C hc) t : FFClosure (geomCurve Ω C)) ∈ W := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        rw [coe_tensorEmb_tmul]
        exact mul_mem (hW.1 c) (hW.2 a)
      | add x y hx hy =>
        rw [map_add, IntermediateField.coe_add]
        exact add_mem hx hy
    have := key (secToTensor Ω C (isAffineOpen_U C hc) s)
    rw [tensorEmb_secToTensor] at this
    exact this

/-- A place of `F'` over a cusp of `U_{Ω'}` restricts to a place of `F` over a cusp of `U_Ω`. -/
lemma comap_extF_cusp {W' : ValuationSubring (FFClosure (geomCurve Ω' C))}
    (hkW : ∀ c : Ω', algebraMap Ω' (FFClosure (geomCurve Ω' C)) c ∈ W')
    (hWU : ¬ IsCentredOn (geomData Ω' C) (geomCurve Ω' C)
      (curveEquivL Ω' (transcendental_geomCoord Ω' C)) (geomOpen Ω' C) W') :
    (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W'.comap (extF Ω Ω' C hc)) ∧
      ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C)
          (W'.comap (extF Ω Ω' C hc)) := by
  have hk : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W'.comap (extF Ω Ω' C hc) :=
    fun c ↦ by
      rw [ValuationSubring.mem_comap, extF_algebraMap_Omega]
      exact hkW _
  refine ⟨hk, fun hW ↦ hWU ((isCentredOn_geomOpen_iff' Ω' C hc W').2 ⟨hkW, fun a ↦ ?_⟩)⟩
  have := ((isCentredOn_geomOpen_iff' Ω C hc _).1 hW).2 a
  rw [ValuationSubring.mem_comap, extF_secEmb] at this
  exact this

/-! ### The comparison isomorphism at the generic points -/

/-- `U_Ω ≅ Spec (Ω ⊗ Γ(U))` at the generic points. -/
lemma genOpen_iso :
    (specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫ genOpen Ω C C.U) ≫
        (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).inv = genPt Ω C hc := by
  rw [Category.assoc, ← specMap_tensorEmb]

omit [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω'] [CharZero Ω'] in
/-- **cj's cuspidal inertia groups are the Galois inertia groups at the generic point of
`Spec (Ω ⊗ Γ(U))`.** -/
lemma map_cuspInertia_iso (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    haveI := isGalois_geomL Ω C
    (cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (curveGaloisData_H_le Ω _) (geomOpen Ω C) W).map
      (fundamentalGroupMap (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).inv
        (genOpen_iso Ω C hc)).toMonoidHom =
      galInertia (genPt Ω C hc) (geomData Ω C).L (genT Ω C hc) rfl W := by
  haveI := isGalois_geomL Ω C
  have key : ∀ σ : (geomData Ω C).H,
      fundamentalGroupMap (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).inv
        (genOpen_iso Ω C hc) ((geomData Ω C).chartHom (curveGaloisData_H_le Ω _)
          (genOpen Ω C C.U) σ) =
        galoisAction (geomData Ω C).L (genT Ω C hc) rfl
          ((geomData Ω C).toGalL (Subgroup.inclusion (curveGaloisData_H_le Ω _) σ)) := by
    intro σ
    rw [GaloisData.chartHom_apply, fundamentalGroupMap_galoisAction
      (Ω := FFClosure (geomCurve Ω C)) (geomData Ω C).L
      (genOpen Ω C C.U) (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).inv rfl
      (genOpen_iso Ω C hc) (by rw [← genOpen_iso]; simp only [Category.assoc])]
    exact DFunLike.congr_fun (galoisAction_congr (Ω := FFClosure (geomCurve Ω C)) _
      (specMap_tensorEmb Ω C (isAffineOpen_U C hc)).symm _ _) _
  rw [cuspInertia, galInertia, MonoidHom.map_closure, Set.image_image]
  congr 1
  ext γ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, hσ, (key σ).symm⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨σ, rfl⟩ := (geomData Ω C).toGalL_surjective g
    exact ⟨⟨σ, σ.2⟩, hg, key _⟩

/-- The generic point of `U_Ω`, in cj's normalisation. -/
abbrev genU : Spec (.of (FFClosure (geomCurve Ω C))) ⟶ (geomOpen Ω C).toScheme :=
  specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫ genOpen Ω C C.U

/-- `π₁ᵉᵗ(U_Ω, generic) ≃* π₁ᵉᵗ(Spec (Ω ⊗ Γ(U)), generic)`. -/
def isoPi : π₁ᵉᵗ(genU Ω C) ≃* π₁ᵉᵗ(genPt Ω C hc) :=
  MulEquiv.ofBijective (fundamentalGroupMap (specTensorIsoBaseChangeOpen K Ω
    (isAffineOpen_U C hc)).inv (genOpen_iso Ω C hc)).toMonoidHom
    (fundamentalGroupMap_bijective_of_isIso (specTensorIsoBaseChangeOpen K Ω
      (isAffineOpen_U C hc)).inv (genOpen_iso Ω C hc))

lemma bijective_of_eq {X Y : Scheme.{u}} {M : Type u} [Field M] [IsSepClosed M] (f : Y ⟶ X)
    (x : Spec (.of M) ⟶ Y) (hb : Function.Bijective (fundamentalGroupMap f (rfl : x ≫ f = _)))
    {η : Spec (.of M) ⟶ X} (h : x ≫ f = η) : Function.Bijective (fundamentalGroupMap f h) := by
  subst h
  exact hb

variable [Algebra.IsAlgebraic K Ω]

/-- `π₁ᵉᵗ(Spec (Ω' ⊗ Γ(U)), generic) ≃* π₁ᵉᵗ(Spec (Ω ⊗ Γ(U)), Spec F' ⟶ Spec F ⟶ generic)`
(invariance under `Ω ⊆ Ω'`, `fundamentalGroupMap_extendSpec_bijective`). -/
def extPi : π₁ᵉᵗ(genPt Ω' C hc) ≃* π₁ᵉᵗ(specHom (extF Ω Ω' C hc) ≫ genPt Ω C hc) :=
  haveI := connectedSpace_specTensor Ω C hc
  haveI := countable_of_numberField Ω K
  haveI := finiteType_sectionsU C hc
  MulEquiv.ofBijective (fundamentalGroupMap (extendSpec K Ω Ω' Γ(C.Xbar, C.U))
    (genPt_extendSpec Ω Ω' C hc)).toMonoidHom
    (bijective_of_eq (extendSpec K Ω Ω' Γ(C.Xbar, C.U)) (genPt Ω' C hc)
      (fundamentalGroupMap_extendSpec_bijective K (genPt Ω' C hc)) (genPt_extendSpec Ω Ω' C hc))

/-- **The comparison isomorphism `Ψ : π₁ᵉᵗ(U_{Ω'}) ≃* π₁ᵉᵗ(U_Ω)`** at the generic points: the map
induced by `U_{Ω'} ⟶ U_Ω` followed by the change of field of the geometric point. -/
def geomCompare : π₁ᵉᵗ(genU Ω' C) ≃* π₁ᵉᵗ(genU Ω C) :=
  haveI := connectedSpace_specTensor' Ω C hc
  (isoPi Ω' C hc).trans ((extPi Ω Ω' C hc).trans
    ((fieldExtEquiv (extF Ω Ω' C hc) (genPt Ω C hc)).toMulEquiv.symm.trans
      (isoPi Ω C hc).symm))

/-- **`Ψ` maps the cuspidal inertia group of a place `W'` over a cusp into the cuspidal inertia
group of `W' ∩ F`.** -/
theorem map_cuspInertia_geomCompare_le (W' : ValuationSubring (FFClosure (geomCurve Ω' C))) :
    (cuspInertia (geomData Ω' C) (geomCurve Ω' C) (curveEquivL Ω' (transcendental_geomCoord Ω' C))
        (curveGaloisData_H_le Ω' _) (geomOpen Ω' C) W').map
        (geomCompare Ω Ω' C hc).toMonoidHom ≤
      cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (curveGaloisData_H_le Ω _) (geomOpen Ω C) (W'.comap (extF Ω Ω' C hc)) := by
  haveI := connectedSpace_specTensor' Ω C hc
  haveI := isGalois_geomL Ω C
  haveI := isGalois_geomL Ω' C
  have h1 := map_cuspInertia_iso Ω' C hc W'
  have h2 := map_cuspInertia_iso Ω C hc (W'.comap (extF Ω Ω' C hc))
  have h3 := map_galInertia_extendSpec_le Ω Ω' C hc W'
  intro γ hγ
  obtain ⟨δ, hδ, rfl⟩ := hγ
  -- push `δ` through the four maps
  have hδ1 : isoPi Ω' C hc δ ∈ galInertia (genPt Ω' C hc) (geomData Ω' C).L (genT Ω' C hc) rfl W' :=
    h1 ▸ ⟨δ, hδ, rfl⟩
  have hδ2 : extPi Ω Ω' C hc (isoPi Ω' C hc δ) ∈ (galInertia (genPt Ω C hc) (geomData Ω C).L
      (genT Ω C hc) rfl (W'.comap (extF Ω Ω' C hc))).map
        (fieldExtEquiv (extF Ω Ω' C hc) (genPt Ω C hc)).toMulEquiv.toMonoidHom :=
    h3 ⟨_, hδ1, rfl⟩
  obtain ⟨ε, hε, hεe⟩ := hδ2
  rw [← h2] at hε
  obtain ⟨θ, hθ, rfl⟩ := hε
  have : geomCompare Ω Ω' C hc δ = θ := by
    change (isoPi Ω C hc).symm ((fieldExtEquiv (extF Ω Ω' C hc) (genPt Ω C hc)).toMulEquiv.symm
      (extPi Ω Ω' C hc (isoPi Ω' C hc δ))) = θ
    rw [← hεe]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact (isoPi Ω C hc).symm_apply_apply θ
  rw [MulEquiv.coe_toMonoidHom, this]
  exact hθ

/-! ### Equality: commutativity and commensurable terminality -/

/-- Elements of the closure of a cyclic subgroup commute. -/
lemma mul_comm_of_mem_closure_zpowers {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (e : G) {x y : G}
    (hx : x ∈ (Subgroup.zpowers e).topologicalClosure)
    (hy : y ∈ (Subgroup.zpowers e).topologicalClosure) : x * y = y * x := by
  letI := Subgroup.commGroupTopologicalClosure (Subgroup.zpowers e) fun a b ↦ by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : (Subgroup.zpowers e).topologicalClosure) ⟨y, hy⟩)

omit [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω'] [CharZero Ω']
  [Algebra.IsAlgebraic K Ω] [NumberField K] in
include hc in
/-- **Cuspidal inertia groups are commutative** (they are conjugate to `⟨cⱼ⟩‾` under
`π₁ᵉᵗ(U_Ω) ≃ₜ* Π̂_{g,r}`). -/
lemma cuspInertia_mul_comm {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hkW : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W)
    (hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W)
    {a b} (ha : a ∈ cuspInertia (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _) (geomOpen Ω C) W)
    (hb : b ∈ cuspInertia (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _) (geomOpen Ω C) W) :
    a * b = b * a := by
  obtain ⟨Θ, hΘ⟩ := exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed (geomData Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (geomOpen Ω C)
    (compl_finite_baseChangeOpen K Ω C.nonempty) (compl_nonempty_baseChangeOpen K Ω hc)
  obtain ⟨j, σ, hj⟩ := hΘ W hkW hWU
  set ψ := Θ.toMulEquiv.toMonoidHom.comp (MulAut.conj σ).toMonoidHom
  have hψ : Function.Injective ψ := Θ.injective.comp (MulAut.conj σ).injective
  have hmem : ∀ x ∈ cuspInertia (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
      (geomOpen Ω C) W, ψ x ∈ Pi1.SurfaceGroup.inertia j := fun x hx ↦ by
    rw [← hj]
    exact ⟨x, hx, rfl⟩
  apply hψ
  rw [map_mul, map_mul]
  exact mul_comm_of_mem_closure_zpowers _ (hmem a ha) (hmem b hb)

/-- **`Ψ` maps the cuspidal inertia group of `W'` onto that of `W' ∩ F`.** -/
theorem map_cuspInertia_geomCompare {W' : ValuationSubring (FFClosure (geomCurve Ω' C))}
    (hkW : ∀ c : Ω', algebraMap Ω' (FFClosure (geomCurve Ω' C)) c ∈ W')
    (hWU : ¬ IsCentredOn (geomData Ω' C) (geomCurve Ω' C)
      (curveEquivL Ω' (transcendental_geomCoord Ω' C)) (geomOpen Ω' C) W') :
    (cuspInertia (geomData Ω' C) (geomCurve Ω' C) (curveEquivL Ω' (transcendental_geomCoord Ω' C))
        (curveGaloisData_H_le Ω' _) (geomOpen Ω' C) W').map
        (geomCompare Ω Ω' C hc).toMonoidHom =
      cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (curveGaloisData_H_le Ω _) (geomOpen Ω C) (W'.comap (extF Ω Ω' C hc)) := by
  set I' := cuspInertia (geomData Ω' C) (geomCurve Ω' C)
    (curveEquivL Ω' (transcendental_geomCoord Ω' C)) (curveGaloisData_H_le Ω' _) (geomOpen Ω' C) W'
  set I := cuspInertia (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _) (geomOpen Ω C)
    (W'.comap (extF Ω Ω' C hc))
  obtain ⟨hk, hU⟩ := comap_extF_cusp Ω Ω' C hc hkW hWU
  have hle := map_cuspInertia_geomCompare_le Ω Ω' C hc W'
  set Ψ := geomCompare Ω Ω' C hc
  -- `J = Ψ⁻¹(I)` is commutative and contains `I'`, so it normalises `I'`
  have hJ : I.comap Ψ.toMonoidHom ≤ I' := by
    intro j hj
    have hcj : ∀ y ∈ I', j * y = y * j := fun y hy ↦ by
      have hyJ : Ψ y ∈ I := hle ⟨y, hy, rfl⟩
      refine Ψ.injective ?_
      rw [map_mul, map_mul]
      exact cuspInertia_mul_comm Ω C hc hk hU hj hyJ
    have hfix : ∀ y ∈ I', j⁻¹ * y * j = y := fun y hy ↦ by
      rw [mul_assoc, ← hcj y hy, inv_mul_cancel_left]
    have hconj : ConjAct.toConjAct j • I' = I' := by
      ext x
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
        ConjAct.ofConjAct_toConjAct, inv_inv]
      constructor
      · intro hx
        have h1 := hcj _ hx
        have : x = j * (j⁻¹ * x * j) * j⁻¹ := by group
        rw [this, h1, mul_inv_cancel_right]
        exact hx
      · intro hx
        rw [hfix x hx]
        exact hx
    have hcomm : j ∈ Subgroup.Commensurable.commensurator I' := by
      rw [Subgroup.Commensurable.commensurator_mem_iff, hconj]
    rw [geomCusps_commensurator Ω' C ⟨W', hkW, hWU, rfl⟩] at hcomm
    exact hcomm
  refine le_antisymm hle fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := Ψ.surjective x
  exact ⟨y, hJ hx, rfl⟩

/-! ### Surjectivity on cusps: lifting places along `extF` -/

/-- If `1 ⊗ a = w ⊗ b` in `Ω' ⊗[Ω] M` with `b ≠ 0`, then `w ∈ Ω` and `a = w • b`. -/
lemma exists_eq_algebraMap_of_tmul_eq {E E' M : Type*} [Field E] [Field E'] [Algebra E E']
    [AddCommGroup M] [Module E M] {a b : M} (hb : b ≠ 0) {w : E'}
    (h : (1 : E') ⊗ₜ[E] a = w ⊗ₜ[E] b) : ∃ c : E, algebraMap E E' c = w ∧ a = c • b := by
  have key (g : Module.Dual E E') : g 1 • a = g w • b := by
    have := congrArg (fun z ↦ TensorProduct.lid E M (TensorProduct.map g LinearMap.id z)) h
    simpa using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual E E', φ 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff E (1 : E')).1 hcon)
  set g₀ : Module.Dual E E' := (φ 1)⁻¹ • φ
  have hg₀ : g₀ 1 = 1 := by simp [g₀, hφ]
  refine ⟨g₀ w, ?_, by simpa [hg₀] using key g₀⟩
  have ha : a = g₀ w • b := by simpa [hg₀] using key g₀
  have hall : ∀ g : Module.Dual E E', g (g₀ w • (1 : E') - w) = 0 := fun g ↦ by
    have h1 := key g
    rw [ha, smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [map_sub, map_smul, smul_eq_mul, mul_comm]
      exact h1
    · exact absurd h1 hb
  have := (Module.forall_dual_apply_eq_zero_iff E _).1 hall
  rw [sub_eq_zero] at this
  rw [Algebra.algebraMap_eq_smul_one, this]

/-- A transcendental element has a pole at some place over the base field. -/
lemma exists_valuationSubring_notMem {E M : Type*} [Field E] [Field M] [Algebra E M] {σ : M}
    (hσ : Transcendental E σ) :
    ∃ B : ValuationSubring M, (∀ c : E, algebraMap E M c ∈ B) ∧ σ ∉ B := by
  have hσ0 : σ ≠ 0 := fun h ↦ hσ (h ▸ isAlgebraic_zero)
  have hu : Transcendental E σ⁻¹ := fun h ↦ hσ (IsAlgebraic.inv_iff.1 h)
  set A : Subring M := (Algebra.adjoin E {σ⁻¹}).toSubring
  have huA : σ⁻¹ ∈ A := Algebra.subset_adjoin (Set.mem_singleton _)
  set I : Ideal A := Ideal.span {⟨σ⁻¹, huA⟩}
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := htop ▸ Submodule.mem_top
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h1
    have hs' : (s : M) * σ⁻¹ = 1 := congrArg Subtype.val hs
    have hsA : (s : M) ∈ Algebra.adjoin E {σ⁻¹} := s.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hsA
    obtain ⟨p, hp⟩ := hsA
    have hp' : Polynomial.aeval σ⁻¹ (p * Polynomial.X - 1) = 0 := by
      simp only [map_sub, map_mul, Polynomial.aeval_X, map_one]
      rw [show Polynomial.aeval σ⁻¹ p = (s : M) from hp, hs', sub_self]
    have h0 : p * Polynomial.X - 1 = 0 := by
      by_contra hne
      exact hu ⟨_, hne, hp'⟩
    have := congrArg (fun q ↦ Polynomial.coeff q 0) h0
    simp at this
  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨B, fun c ↦ hAB (Subalgebra.algebraMap_mem _ c), fun hσB ↦ ?_⟩
  have huB : σ⁻¹ ∈ B.nonunits := hIB ⟨⟨σ⁻¹, huA⟩, Ideal.subset_span (Set.mem_singleton _), rfl⟩
  have huB' : σ⁻¹ ∈ B := hAB huA
  have hv := B.valuation_unit ⟨⟨σ⁻¹, huB'⟩, ⟨σ, hσB⟩, Subtype.ext (inv_mul_cancel₀ hσ0),
    Subtype.ext (mul_inv_cancel₀ hσ0)⟩
  rw [ValuationSubring.mem_nonunits_iff] at huB
  exact absurd hv (ne_of_lt huB)

omit [NumberField K] [IsAlgClosed Ω] [IsAlgClosed Ω'] [CharZero Ω] [CharZero Ω']
  [Algebra.IsAlgebraic K Ω] in
lemma cancelTensor_tmul_eq (R : Type u) [CommRing R] [Algebra K R] (w : Ω') (m : Ω ⊗[K] R) :
    cancelTensor K Ω Ω' R (w ⊗ₜ m) = w • extendTensor K Ω Ω' R m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s r =>
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, extendTensor_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, smul_add]

omit [Algebra.IsAlgebraic K Ω] in
include hc in
/-- **Non-constant functions stay non-constant after `Ω ⊆ Ω'`**: for `τ ∈ K(X̄_Ω) ∖ Ω`, the image
of `τ` in `F'` is transcendental over `Ω'`. -/
lemma transcendental_extF {τ : (geomCurve Ω C).functionField}
    (hτc : ∀ c : Ω, τ ≠ algebraMap Ω (geomCurve Ω C).functionField c) :
    Transcendental Ω' (extF Ω Ω' C hc
      (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C)) τ)) := by
  intro halg
  obtain ⟨w, hw⟩ : ∃ w : Ω', algebraMap Ω' (FFClosure (geomCurve Ω' C)) w =
      extF Ω Ω' C hc (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C)) τ) := by
    set σ := extF Ω Ω' C hc
      (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C)) τ)
    have hint : IsIntegral Ω' σ := halg.isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hint
    haveI := Algebra.IsAlgebraic.of_finite Ω' (IntermediateField.adjoin Ω' {σ})
    have hbot := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
      (IntermediateField.adjoin Ω' {σ})
    have : σ ∈ (⊥ : IntermediateField Ω' (FFClosure (geomCurve Ω' C))) :=
      hbot ▸ IntermediateField.mem_adjoin_simple_self Ω' σ
    exact IntermediateField.mem_bot.1 this
  haveI := isFractionRing_geomOpen Ω C hc
  have hU := isAffineOpen_U C hc
  obtain ⟨a₀, b₀, hb₀, rfl⟩ := IsFractionRing.div_surjective
    (A := Γ(geomCurve Ω C, geomOpen Ω C)) τ
  set ta := secToTensor Ω C hU a₀
  set tb := secToTensor Ω C hU b₀
  have htb : tb ≠ 0 := fun h ↦ nonZeroDivisors.ne_zero hb₀
    (secToTensor_injective Ω C hc (h.trans (map_zero _).symm))
  have hA : algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))
      (algebraMap Γ(geomCurve Ω C, geomOpen Ω C) _ a₀) =
        (tensorEmb Ω C hU ta : FFClosure (geomCurve Ω C)) := by
    rw [tensorEmb_secToTensor, curveEquivL_apply]
    rfl
  have hB : algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))
      (algebraMap Γ(geomCurve Ω C, geomOpen Ω C) _ b₀) =
        (tensorEmb Ω C hU tb : FFClosure (geomCurve Ω C)) := by
    rw [tensorEmb_secToTensor, curveEquivL_apply]
    rfl
  have hne : (tensorEmb Ω' C hU (extendTensor K Ω Ω' _ tb) : FFClosure (geomCurve Ω' C)) ≠ 0 := by
    intro h0
    have : tensorEmb Ω' C hU (extendTensor K Ω Ω' _ tb) = 0 := Subtype.ext h0
    exact htb (extendTensor_injective Ω Ω' _ ((tensorEmb_injective Ω' C hU)
      (this.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  rw [map_div₀, map_div₀, hA, hB, extF_tensorEmb, extF_tensorEmb] at hw
  have h1 : (tensorEmb Ω' C hU (extendTensor K Ω Ω' _ ta) : FFClosure (geomCurve Ω' C)) =
      (tensorEmb Ω' C hU (algebraMap Ω' (Ω' ⊗[K] Γ(C.Xbar, C.U)) w *
        extendTensor K Ω Ω' _ tb) : FFClosure (geomCurve Ω' C)) := by
    rw [map_mul, IntermediateField.coe_mul, coe_tensorEmb_algebraMap, hw, div_mul_cancel₀ _ hne]
  have h2 : extendTensor K Ω Ω' _ ta = w • extendTensor K Ω Ω' _ tb := by
    rw [Algebra.smul_def]
    exact tensorEmb_injective Ω' C hU (Subtype.ext h1)
  have h3 : (1 : Ω') ⊗ₜ[Ω] ta = w ⊗ₜ[Ω] tb := by
    apply (cancelTensor K Ω Ω' Γ(C.Xbar, C.U)).injective
    rw [cancelTensor_tmul_eq, cancelTensor_tmul_eq, one_smul, h2]
  obtain ⟨c, -, hab⟩ := exists_eq_algebraMap_of_tmul_eq htb h3
  apply hτc c
  apply (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))).injective
  have htb' : (tensorEmb Ω C hU tb : FFClosure (geomCurve Ω C)) ≠ 0 := by
    intro h0
    exact htb (tensorEmb_injective Ω C hU (Subtype.ext (h0.trans (by simp))))
  rw [map_div₀, hA, hB, hab, Algebra.smul_def, map_mul, IntermediateField.coe_mul,
    coe_tensorEmb_algebraMap, mul_div_cancel_right₀ _ htb',
    ← IsScalarTower.algebraMap_apply]

omit [Algebra.IsAlgebraic K Ω] in
include hc in
/-- **Every place of `F` over a cusp of `U_Ω` is, over `L`, the restriction of a place of `F'` over
a cusp of `U_{Ω'}`.** Proof: the restriction of `W` to `K(X̄_Ω)` is the local ring at a closed
point `y ∉ U_Ω`; a function `τ` with poles exactly at `y` stays transcendental over `Ω'`
(`transcendental_extF`), so some place `W' ⊇ Ω'` of `F'` has a pole at `τ`
(`exists_valuationSubring_notMem`); its restriction to `K(X̄_Ω)` is a place with a pole at `τ`, i.e.
the local ring at `y`. -/
lemma exists_cusp_lift {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hkW : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W)
    (hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W) :
    ∃ W' : ValuationSubring (FFClosure (geomCurve Ω' C)),
      (∀ c : Ω', algebraMap Ω' (FFClosure (geomCurve Ω' C)) c ∈ W') ∧
      ¬ IsCentredOn (geomData Ω' C) (geomCurve Ω' C)
        (curveEquivL Ω' (transcendental_geomCoord Ω' C)) (geomOpen Ω' C) W' ∧
      (W'.comap (extF Ω Ω' C hc)).comap (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C))) =
        W.comap (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C))) := by
  haveI := isSeparated_of_over Ω (geomCurve Ω C)
  have hX := valuationRing_stalk_of_isCurveOver Ω (geomCurve Ω C)
  -- constants lie in the restriction of a place containing `Ω`
  have hconst : ∀ (V : ValuationSubring (FFClosure (geomCurve Ω C))),
      (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ V) →
      ∀ c : Ω, algebraMap Ω (geomCurve Ω C).functionField c ∈
        V.comap (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))) :=
    fun V hV c ↦ by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hV c
  -- the point `y` under `W`
  set y := (pointEquivValuationSubringOver Ω hX).symm
    ⟨W.comap (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))),
      hconst W hkW⟩ with hydef
  have hy : stalkVS Ω y =
      W.comap (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))) := by
    have := congrArg Subtype.val ((pointEquivValuationSubringOver Ω hX).apply_symm_apply
      ⟨W.comap (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))),
        hconst W hkW⟩)
    rw [pointEquivValuationSubringOver_apply] at this
    exact this
  -- `L`-membership is `K(X̄_Ω)`-membership
  have hLmem : ∀ (V : ValuationSubring (FFClosure (geomCurve Ω C))) (z : (geomData Ω C).L),
      z ∈ V.comap (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C))) ↔
        (curveEquivL Ω (transcendental_geomCoord Ω C)).symm z ∈
          V.comap (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))) :=
    fun V z ↦ by
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
        ← curveEquivL_apply Ω (transcendental_geomCoord Ω C), RingEquiv.apply_symm_apply]
      rfl
  -- `y ∉ U_Ω`
  have hyU : y ∉ geomOpen Ω C := fun hyU ↦ hWU ⟨hkW, fun a ↦ by
    have hmem : (geomCurve Ω C).germToFunctionField (geomOpen Ω C) a ∈ stalkVS Ω y :=
      ⟨(geomCurve Ω C).presheaf.germ _ y hyU a,
        by rw [Scheme.algebraMap_germ_eq_germToFunctionField]⟩
    rw [hy, ValuationSubring.mem_comap] at hmem
    rw [curveEquivL_apply]
    exact hmem⟩
  have hygen : y ≠ genericPoint (geomCurve Ω C) := by
    intro hgen
    apply hyU
    rw [hgen]
    exact genericPoint_mem_of_nonempty _
  -- a function with poles exactly at `y`
  have hycl : IsClosed ({y} : Set (geomCurve Ω C)) :=
    CurvesJacobian.isClosed_closedPoint Ω (geomCurve Ω C) ⟨y, hygen⟩
  set V : (geomCurve Ω C).Opens := ⟨{y}ᶜ, hycl.isOpen_compl⟩
  have hVfin : (V : Set (geomCurve Ω C))ᶜ.Finite := by
    change ({y}ᶜᶜ : Set (geomCurve Ω C)).Finite
    rw [compl_compl]
    exact Set.finite_singleton y
  have hVne : V ≠ ⊤ := fun h ↦ by
    have : y ∈ (V : Set (geomCurve Ω C)) := h ▸ trivial
    exact this rfl
  haveI : Nonempty V := ⟨⟨genericPoint (geomCurve Ω C), fun h ↦ hygen h.symm⟩⟩
  obtain ⟨τ, hτ, hVτ⟩ := exists_chartOne_eq Ω V hVfin hVne
  have hτy : τ ∉ stalkVS Ω y := fun h ↦ by
    have : y ∈ chartOne Ω (geomCurve Ω C) τ := (mem_chartOne_iff Ω hτ y).2 h
    rw [← hVτ] at this
    exact this rfl
  have hτc : ∀ c : Ω, τ ≠ algebraMap Ω (geomCurve Ω C).functionField c := fun c hc' ↦ by
    apply hτy
    rw [hc', hy]
    exact hconst W hkW c
  -- a place of `F'` over `Ω'` with a pole at `τ`
  obtain ⟨B, hBk, hBτ⟩ := exists_valuationSubring_notMem (transcendental_extF Ω Ω' C hc hτc)
  -- its restriction to `K(X̄_Ω)` is the stalk at `y`
  have hres : (B.comap (extF Ω Ω' C hc)).comap
        (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))) =
      W.comap (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))) := by
    have hk' := hconst (B.comap (extF Ω Ω' C hc)) fun c ↦ by
      rw [ValuationSubring.mem_comap, extF_algebraMap_Omega]
      exact hBk _
    set z := (pointEquivValuationSubringOver Ω hX).symm ⟨_, hk'⟩
    have hz : stalkVS Ω z = (B.comap (extF Ω Ω' C hc)).comap
        (algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C))) := by
      have := congrArg Subtype.val ((pointEquivValuationSubringOver Ω hX).apply_symm_apply
        ⟨_, hk'⟩)
      rw [pointEquivValuationSubringOver_apply] at this
      exact this
    have hτz : τ ∉ stalkVS Ω z := by
      rw [hz, ValuationSubring.mem_comap, ValuationSubring.mem_comap]
      exact hBτ
    have hzy : z = y := by
      by_contra hne
      apply hτz
      have hzV : z ∈ chartOne Ω (geomCurve Ω C) τ := by
        rw [← hVτ]
        exact hne
      exact (mem_chartOne_iff Ω hτ z).1 hzV
    rw [← hz, ← hy, hzy]
  refine ⟨B, hBk, fun hcent ↦ hWU ?_, ?_⟩
  · refine (isCentredOn_geomOpen_iff' Ω C hc W).2 ⟨hkW, fun a ↦ ?_⟩
    have h1 := ((isCentredOn_geomOpen_iff' Ω' C hc B).1 hcent).2 a
    rw [← extF_secEmb Ω Ω' C hc a, secEmb_apply] at h1
    have h3 : tensorEmb Ω C (isAffineOpen_U C hc) (1 ⊗ₜ a) ∈ (B.comap (extF Ω Ω' C hc)).comap
        (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C))) := h1
    rw [hLmem, hres, ← hLmem] at h3
    rw [secEmb_apply]
    exact h3
  · ext z
    rw [hLmem, hLmem, hres]

/-- **Invariance of `Δ_U` with its cuspidal inertia groups under `K̄ ⊆ Ω'`**: for an affine
hyperbolic curve `U` over a number field `K`, an algebraic closure `Ω` of `K` and an algebraically
closed `Ω' ⊇ Ω`, the isomorphism `Ψ : π₁ᵉᵗ(U_{Ω'}) ≃* π₁ᵉᵗ(U_Ω)` (`geomCompare`; induced by
`U_{Ω'} ⟶ U_Ω` and the change of field of the geometric generic point) maps the set of cuspidal
inertia groups of `U_{Ω'}` (`geomCusps`) **onto** that of `U_Ω`. -/
theorem map_geomCusps_geomCompare (I : Subgroup π₁ᵉᵗ(genU Ω' C)) :
    I ∈ geomCusps Ω' C ↔ I.map (geomCompare Ω Ω' C hc).toMonoidHom ∈ geomCusps Ω C := by
  constructor
  · rintro ⟨W', hkW, hWU, rfl⟩
    obtain ⟨hk, hU⟩ := comap_extF_cusp Ω Ω' C hc hkW hWU
    exact ⟨_, hk, hU, map_cuspInertia_geomCompare Ω Ω' C hc hkW hWU⟩
  · rintro ⟨W, hkW, hWU, hI⟩
    obtain ⟨W', hkW', hWU', hres⟩ := exists_cusp_lift Ω Ω' C hc hkW hWU
    obtain ⟨hk₀, hU₀⟩ := comap_extF_cusp Ω Ω' C hc hkW' hWU'
    -- `W` and `W' ∩ F` restrict to the same place of `L`
    obtain ⟨γ, hγ⟩ := exists_cuspInertia_eq_conj (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _) (geomOpen Ω C)
      (W'.comap (extF Ω Ω' C hc)) W hres
    -- `Ψ⁻¹ γ` is the image of some `σ' ∈ H'`
    obtain ⟨σ', hσ'⟩ := (genericL_spec (geomData Ω' C) (geomCurve Ω' C)
      (curveEquivL Ω' (transcendental_geomCoord Ω' C)) (curveEquivL_algebraMap Ω' _)
      (curveGaloisData_H_le Ω' _) (curveEquivL_τ Ω' _) (geomOpen Ω' C)
      (compl_finite_baseChangeOpen K Ω' C.nonempty)).2 ((geomCompare Ω Ω' C hc).symm γ)
    set Ψ := geomCompare Ω Ω' C hc
    have hσL : σ'.1 ∈ (geomData Ω' C).HL := curveGaloisData_H_le Ω' _ σ'.2
    refine ⟨W'.comap (σ'.1.symm : FFClosure (geomCurve Ω' C) →+* FFClosure (geomCurve Ω' C)),
      fun c ↦ ?_, fun h ↦ hWU' ((isCentredOn_comap_iff (geomData Ω' C) (geomCurve Ω' C)
        (curveEquivL Ω' (transcendental_geomCoord Ω' C)) (geomOpen Ω' C) hσL W').1 h), ?_⟩
    · rw [ValuationSubring.mem_comap, RingHom.coe_coe,
        IsScalarTower.algebraMap_apply Ω' (K₀ Ω' (coordT (geomCoord Ω' C))), AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply]
      exact hkW' c
    · rw [cuspInertia_comap]
      apply Subgroup.map_injective (f := Ψ.toMonoidHom) Ψ.injective
      rw [Subgroup.map_map, hI, hγ, ← map_cuspInertia_geomCompare Ω Ω' C hc hkW' hWU',
        Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun x ↦ ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv, hσ', MulEquiv.apply_symm_apply]
      rfl

end CurvesJacobian.Cusp
