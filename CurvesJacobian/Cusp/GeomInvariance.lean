/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.Pi1Invariance
import CurvesJacobian.Cusp.ArithmeticSlim

/-!
# Invariance of `Δ_U` under an extension `Ω ⊆ Ω'` of algebraically closed fields

Let `K` be a field, `R` a finitely generated `K`-algebra (e.g. `R = Γ(X̄, U)` for an affine curve
`U` over `K`) and `K ⊆ Ω ⊆ Ω'` with `Ω`, `Ω'` algebraically closed of characteristic `0` and `Ω`
**countable** (e.g. `Ω = K̄` for a number field `K` and `Ω' = \bar{K_v}` for a place `v`). The
natural map `U_{Ω'} = Spec (Ω' ⊗[K] R) ⟶ U_Ω = Spec (Ω ⊗[K] R)` induces an isomorphism

  `π₁ᵉᵗ(U_{Ω'}) ≃ₜ* π₁ᵉᵗ(U_Ω)`

(SGA 1 X.1.8 / XIII 4.6 in characteristic `0`; used in the proof of [LocAn] Corollary 15.5,
`The Local Pro-p Anabelian Geometry of Curves.txt` l.4340–4370, to pass from `K` to a finitely
generated extension `L ⊇ K` of `ℚ_p`).

This is belyi's `AlgebraicGeometry.FiniteEtale.fundamentalGroupBaseChangeEquiv` (finite étale
descent along `Ω ⊆ Ω'`, proved from the Riemann existence theorem) applied to the `Ω`-algebra
`Ω ⊗[K] R`, after the identification `Ω' ⊗[Ω] (Ω ⊗[K] R) ≅ Ω' ⊗[K] R`
(`Algebra.TensorProduct.cancelBaseChange`).

## Main results

* `AlgebraicGeometry.FiniteEtale.extendSpec`: `Spec (Ω' ⊗[K] R) ⟶ Spec (Ω ⊗[K] R)`;
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_extendSpec_bijective`,
  `AlgebraicGeometry.FiniteEtale.extendSpecEquiv`: `π₁ᵉᵗ(U_{Ω'}) ≃ₜ* π₁ᵉᵗ(U_Ω)` via `extendSpec`;
* `CurvesJacobian.Cusp.geomExtendEquiv`: the same for an affine hyperbolic curve over a number
  field `K` and `Ω` algebraic over `K` (no countability hypothesis).
-/

universe u

open CategoryTheory Limits TensorProduct AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

variable (K : Type u) {Ω Ω' R : Type u} [Field K] [Field Ω] [Field Ω'] [CommRing R] [Algebra K R]
  [Algebra K Ω] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω']

variable (Ω Ω' R) in
/-- `Ω ⊗[K] R → Ω' ⊗[K] R`, `s ⊗ b ↦ s ⊗ b`. -/
def extendTensor : Ω ⊗[K] R →ₐ[K] Ω' ⊗[K] R :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K Ω Ω') (AlgHom.id K R)

@[simp]
lemma extendTensor_tmul (s : Ω) (b : R) :
    extendTensor K Ω Ω' R (s ⊗ₜ b) = algebraMap Ω Ω' s ⊗ₜ b := rfl

variable (Ω Ω' R) in
/-- **`U_{Ω'} ⟶ U_Ω`**: `Spec (Ω' ⊗[K] R) ⟶ Spec (Ω ⊗[K] R)`. -/
def extendSpec : Spec (.of (Ω' ⊗[K] R)) ⟶ Spec (.of (Ω ⊗[K] R)) :=
  Spec.map (CommRingCat.ofHom (extendTensor K Ω Ω' R).toRingHom)

variable (Ω Ω' R) in
/-- `Ω' ⊗[Ω] (Ω ⊗[K] R) ≅ Ω' ⊗[K] R`. -/
abbrev cancelTensor : Ω' ⊗[Ω] (Ω ⊗[K] R) ≃ₐ[Ω'] Ω' ⊗[K] R :=
  Algebra.TensorProduct.cancelBaseChange K Ω Ω' Ω' R

variable (Ω Ω' R) in
/-- `Spec (Ω' ⊗[K] R) ≅ Spec (Ω' ⊗[Ω] (Ω ⊗[K] R))`. -/
def cancelSpecIso : Spec (.of (Ω' ⊗[K] R)) ≅ Spec (.of (Ω' ⊗[Ω] (Ω ⊗[K] R))) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso (cancelTensor K Ω Ω' R).toRingEquiv).op

lemma cancelSpecIso_hom :
    (cancelSpecIso K Ω Ω' R).hom =
      Spec.map (CommRingCat.ofHom (cancelTensor K Ω Ω' R).toRingEquiv.toRingHom) := rfl

/-- **`U_{Ω'} ⟶ U_Ω` is the base change of `Spec Ω' ⟶ Spec Ω`** after the identification
`Ω' ⊗[K] R ≅ Ω' ⊗[Ω] (Ω ⊗[K] R)`. -/
lemma extendSpec_eq :
    extendSpec K Ω Ω' R = (cancelSpecIso K Ω Ω' R).hom ≫ baseChangeSpec Ω Ω' (Ω ⊗[K] R) := by
  rw [cancelSpecIso_hom, baseChangeSpec, ← Spec.map_comp, extendSpec]
  congr 1
  ext1
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    change extendTensor K Ω Ω' R (s ⊗ₜ b) =
      cancelTensor K Ω Ω' R (Algebra.TensorProduct.includeRight (R := Ω) (s ⊗ₜ[K] b))
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
      extendTensor_tmul, Algebra.smul_def, mul_one]
  | add z w hz hw => simp only [map_add, hz, hw]

variable [IsAlgClosed Ω] [CharZero Ω] [Countable Ω] [IsAlgClosed Ω'] [Algebra.FiniteType K R]

omit [IsScalarTower K Ω Ω'] [Algebra K Ω'] in
lemma fundamentalGroupMap_baseChangeSpec_bijective_aux [ConnectedSpace (Spec (.of (Ω ⊗[K] R)))]
    {L : Type u} [Field L] [IsSepClosed L]
    (y : Spec (.of L) ⟶ Spec (.of (Ω' ⊗[Ω] (Ω ⊗[K] R)))) {η : Spec (.of L) ⟶ _}
    (h : y ≫ baseChangeSpec Ω Ω' (Ω ⊗[K] R) = η) :
    Function.Bijective (fundamentalGroupMap (baseChangeSpec Ω Ω' (Ω ⊗[K] R)) h) := by
  subst h
  exact fundamentalGroupMap_baseChange_bijective_of_isAlgClosed (k := Ω) (Ω := Ω') y

/-- **Invariance of `π₁ᵉᵗ` under `Ω ⊆ Ω'`** (algebraically closed, characteristic `0`, `Ω`
countable): for `R` of finite type over `K` with `Spec (Ω ⊗[K] R)` connected, the map
`U_{Ω'} = Spec (Ω' ⊗[K] R) ⟶ U_Ω = Spec (Ω ⊗[K] R)` induces a bijection on `π₁ᵉᵗ` at every
geometric point. -/
theorem fundamentalGroupMap_extendSpec_bijective [ConnectedSpace (Spec (.of (Ω ⊗[K] R)))]
    {L : Type u} [Field L] [IsSepClosed L] (x : Spec (.of L) ⟶ Spec (.of (Ω' ⊗[K] R))) :
    Function.Bijective (fundamentalGroupMap (extendSpec K Ω Ω' R) (rfl :
      x ≫ extendSpec K Ω Ω' R = _)) := by
  have h₂ : (x ≫ (cancelSpecIso K Ω Ω' R).hom) ≫ baseChangeSpec Ω Ω' (Ω ⊗[K] R) =
      x ≫ extendSpec K Ω Ω' R := by
    rw [Category.assoc, ← extendSpec_eq]
  have h : x ≫ (cancelSpecIso K Ω Ω' R).hom ≫ baseChangeSpec Ω Ω' (Ω ⊗[K] R) =
      x ≫ extendSpec K Ω Ω' R := by rw [extendSpec_eq]
  rw [fundamentalGroupMap_congr (extendSpec_eq K) rfl h,
    fundamentalGroupMap_comp _ _ rfl h₂ h]
  exact (fundamentalGroupMap_baseChangeSpec_bijective_aux K _ h₂).comp
    (fundamentalGroupMap_bijective_of_isIso _ rfl)

/-- **`π₁ᵉᵗ(U_{Ω'}, x) ≃ₜ* π₁ᵉᵗ(U_Ω, x)`** through `extendSpec`, as in
`fundamentalGroupMap_extendSpec_bijective`. The inverse is continuous because `π₁ᵉᵗ(U_{Ω'})` is
compact and `π₁ᵉᵗ(U_Ω)` is Hausdorff. -/
def extendSpecEquiv [ConnectedSpace (Spec (.of (Ω ⊗[K] R)))] {L : Type u} [Field L]
    [IsSepClosed L] (x : Spec (.of L) ⟶ Spec (.of (Ω' ⊗[K] R))) :
    π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(x ≫ extendSpec K Ω Ω' R) :=
  let f := fundamentalGroupMap (extendSpec K Ω Ω' R) (rfl : x ≫ extendSpec K Ω Ω' R = _)
  let e : π₁ᵉᵗ(x) ≃* π₁ᵉᵗ(x ≫ extendSpec K Ω Ω' R) := MulEquiv.ofBijective f.toMonoidHom
    (fundamentalGroupMap_extendSpec_bijective K x)
  let h : π₁ᵉᵗ(x) ≃ₜ π₁ᵉᵗ(x ≫ extendSpec K Ω Ω' R) :=
    Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) f.continuous_toFun
  { e with
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

@[simp]
lemma extendSpecEquiv_apply [ConnectedSpace (Spec (.of (Ω ⊗[K] R)))] {L : Type u} [Field L]
    [IsSepClosed L] (x : Spec (.of L) ⟶ Spec (.of (Ω' ⊗[K] R))) (γ : π₁ᵉᵗ(x)) :
    extendSpecEquiv K x γ = fundamentalGroupMap (extendSpec K Ω Ω' R) rfl γ := rfl

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

open AlgebraicGeometry.FiniteEtale Belyi.Anabelian

variable {K : Type u} [Field K] [NumberField K] (Ω Ω' : Type u) [Field Ω] [Field Ω']
  [Algebra K Ω] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω'] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] in
include hc in
lemma connectedSpace_specTensor : ConnectedSpace (Spec (.of (Ω ⊗[K] Γ(C.Xbar, C.U)))) := by
  haveI := isIntegral_specTensor Ω C hc
  infer_instance

omit [Algebra Ω Ω'] [IsAlgClosed Ω] in
lemma countable_of_numberField (K : Type u) [Field K] [NumberField K] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] : Countable Ω := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  exact Belyi.Converse.countable_of_isAlgebraic_rat Ω

include hc in
lemma finiteType_sectionsU : Algebra.FiniteType K Γ(C.Xbar, C.U) :=
  finiteType_sections K (isAffineOpen_U C hc)

include hc in
/-- **Invariance of `Δ_U` under `K̄ ⊆ Ω'`** for an affine hyperbolic curve `U` over a number
field `K` (with a cusp), `Ω = K̄` (any algebraic closure of `K`) and any algebraically closed
`Ω' ⊇ Ω` (e.g. `Ω' = \bar{K_v}`): `U_{Ω'} ⟶ U_Ω` induces a bijection on `π₁ᵉᵗ`. -/
theorem geomExtend_bijective {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Spec (.of (Ω' ⊗[K] Γ(C.Xbar, C.U)))) :
    Function.Bijective (fundamentalGroupMap (extendSpec K Ω Ω' Γ(C.Xbar, C.U)) (rfl :
      x ≫ extendSpec K Ω Ω' Γ(C.Xbar, C.U) = _)) := by
  haveI := connectedSpace_specTensor Ω C hc
  haveI := countable_of_numberField Ω K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI := finiteType_sectionsU C hc
  exact fundamentalGroupMap_extendSpec_bijective K x

include hc in
/-- **`Δ_{U, Ω'} ≃ₜ* Δ_{U, K̄}`** (`geomExtend_bijective`). -/
def geomExtendEquiv {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Spec (.of (Ω' ⊗[K] Γ(C.Xbar, C.U)))) :
    π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(x ≫ extendSpec K Ω Ω' Γ(C.Xbar, C.U)) :=
  haveI := connectedSpace_specTensor Ω C hc
  haveI := countable_of_numberField Ω K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI := finiteType_sectionsU C hc
  extendSpecEquiv K x

include hc in
lemma geomExtendEquiv_apply {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Spec (.of (Ω' ⊗[K] Γ(C.Xbar, C.U)))) (γ : π₁ᵉᵗ(x)) :
    geomExtendEquiv Ω Ω' C hc x γ =
      fundamentalGroupMap (extendSpec K Ω Ω' Γ(C.Xbar, C.U)) rfl γ := rfl

end CurvesJacobian.Cusp
