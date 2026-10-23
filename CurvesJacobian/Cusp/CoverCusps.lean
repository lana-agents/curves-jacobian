/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.NonRationalFill
import CurvesJacobian.Cusp.GalInertia
import CurvesJacobian.Cusp.CoverComparison
import CurvesJacobian.Cusp.FillStep
import Belyi.Converse.Normalization

/-!
# Cuspidal inertia groups along finite étale maps of affine hyperbolic curves (MR8.5)

[AbsTopI] Definition 4.2 (`Topics in Absolute Anabelian Geometry I.txt` l.2950–3030) and
[AbsTopII] Example 3.6 (ii) (`Topics in Absolute Anabelian Geometry II.txt` l.4669–4680): in a
Belyi chain the operations `⋏`/`⋎` come from finite étale maps of curves, and the cuspidal
decomposition groups of the curves along the chain have to be matched (the hypothesis
`Belyi.Anabelian.ChainObj.CuspMatch` of `ChainObj.push`). Here, for affine hyperbolic curves
`C = (X̄, U)` over a number field `K` and `C' = (X̄', U')` over a number field `K' ⊇ K` (both with
a cusp, i.e. `U`, `U'` affine), and a finite étale `F : U' = Spec Γ(U') ⟶ U = Spec Γ(U)`:

* `coverPiHom : Π_{U'} →ₜ* Π_U` (`π₁ᵉᵗ(F)` followed by a change of base point), injective with
  open image (`coverPiHom_injective`, `isOpen_range_coverPiHom`), and `coverι : G_{K'} →ₜ* G_K`
  (`ι ∘ conj`) with `pr ∘ coverPiHom = coverι ∘ pr'` (`pr_coverPiHom`) if `F` lies over
  `Spec K' ⟶ Spec K`;
* **`exists_arithCusps_map_coverPiHom`**: every cuspidal inertia group `J` of `Π_{U'}` maps into a
  cuspidal inertia group `I` of `Π_U` with finite index;
* **`exists_arithCusps_coverHom_le`**: every cuspidal inertia group `I` of `Π_U` contains, with
  finite index, the image of a cuspidal inertia group of `Π_{U'}`.

## Proof

Per curve (`arithAction_surjective`, `mem_arithCusps_iff`, `cuspAt`): the cuspidal inertia
groups of `Π_U` are exactly the images `arithInertia W` of the inertia groups over `L₀ = K(X̄)`
of the places `W ⊇ Ω` of `K(X̄_Ω)^alg` not containing `Γ(U)` (`IsCuspPlace`), because the
arithmetic Galois action `Gal(K(X̄_Ω)^alg / K(X̄)) → Π_U` is surjective (`Γ(U)` is integrally
closed, pi1 `galoisAction_surjective`) and conjugating by it moves the place
(`map_geomCuspInertia_comap`). Moving them to the base point by any isomorphism of fibre functors
`β` (`cuspAt β W`) only conjugates.

For the cover: `ℓ : K(X̄) → K(X̄')` (`coverFF`, finite: `finiteDimensional_coverFF`) and an
`L₀`-isomorphism `σ : K(X̄_Ω)^alg ≅ K(X̄'_Ω)^alg` of algebraic closures of `L₀` (`coverσ`).
Naturality of Galois inertia (`map_galInertia_le`, `relIndex_map_galInertia_ne_zero`) and the change
of field (`map_galInertia_fieldChange`) give `coverPiHom (cuspAt W) ⊆ cuspAt (σ⁻¹ W)` with finite
index (`exists_map_cuspAt_coverHom_le`), and `W` lies over a cusp of `U'` iff `σ⁻¹ W` lies over a
cusp of `U` (`isCuspPlace_comap_coverσ`: `σ` maps `Ω` onto `Ω`, and `Γ(U')` is integral over
`Γ(U)` while valuation rings are integrally closed).
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

/-- **Transport of `galInertia` along an equality of geometric points.** -/
lemma map_galInertia_eqToIso {η η' : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η) (e : η = η')
    (W : ValuationSubring Ω) :
    (galInertia η F j h W).map
        (autContinuousMulEquivOfIso (eqToIso (congrArg fiber e))).toMulEquiv.toMonoidHom =
      galInertia η' F j (h.trans e) W := by
  subst e
  have key : ∀ γ : π₁ᵉᵗ(η),
      autContinuousMulEquivOfIso (eqToIso (congrArg fiber (rfl : η = η))) γ = γ := fun γ ↦ by
    change Iso.conjAut _ γ = γ
    simp [Iso.conjAut_apply]
  ext γ
  constructor
  · rintro ⟨x, hx, rfl⟩
    change autContinuousMulEquivOfIso _ x ∈ _
    rwa [key]
  · intro hγ
    exact ⟨γ, hγ, key γ⟩

/-- Surjectivity of a Galois action does not depend on the name of the geometric point. -/
lemma galoisAction_surjective_of_eq {η η' : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η)
    (h' : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η')
    (hs : Function.Surjective (galoisAction F j h)) :
    Function.Surjective (galoisAction F j h') := by
  obtain rfl : η = η' := h.symm.trans h'
  exact hs

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp

section AutIso

variable {𝒞 : Type*} [Category 𝒞] {P Q R : 𝒞 ⥤ FintypeCat.{u}}

/-- `(α ≪≫ β)_* = β_* ∘ α_*` on subgroups. -/
lemma map_autIso_trans (α : P ≅ Q) (β : Q ≅ R) (S : Subgroup (Aut P)) :
    S.map (autContinuousMulEquivOfIso (α ≪≫ β)).toMulEquiv.toMonoidHom =
      (S.map (autContinuousMulEquivOfIso α).toMulEquiv.toMonoidHom).map
        (autContinuousMulEquivOfIso β).toMulEquiv.toMonoidHom := by
  rw [Subgroup.map_map]
  exact congrArg (fun φ ↦ S.map φ) (MonoidHom.ext fun σ ↦ Iso.trans_conjAut α β σ)

/-- Two isomorphisms of fibre functors move subgroups to conjugate subgroups. -/
lemma exists_map_autIso_eq_conj (α α' : P ≅ Q) :
    ∃ t : Aut Q, ∀ S : Subgroup (Aut P),
      S.map (autContinuousMulEquivOfIso α').toMulEquiv.toMonoidHom =
        (S.map (autContinuousMulEquivOfIso α).toMulEquiv.toMonoidHom).map
          (MulAut.conj t).toMonoidHom := by
  obtain ⟨t, ht⟩ := exists_conjAut_eq_conj α α'
  refine ⟨t, fun S ↦ ?_⟩
  rw [Subgroup.map_map]
  exact congrArg (fun φ ↦ S.map φ) (MonoidHom.ext fun σ ↦ ht σ)

end AutIso

/-! ### The cuspidal inertia groups of `Π_U` through the arithmetic generic point -/

section Curve

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- A place `W` of `K(X̄_Ω)^alg` **over a cusp of `U`**: `W ⊇ Ω` and `W ⊉ Γ(U)`. -/
def IsCuspPlace (W : ValuationSubring (FFClosure (geomCurve Ω C))) : Prop :=
  (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W) ∧
    ¬ ∀ a : Γ(C.Xbar, C.U), secEmb Ω C (isAffineOpen_U C hc) a ∈ W

/-- **Centred places**: `W` is centred on `U_Ω` iff `W ⊇ Ω` and `W ⊇ Γ(U)`. -/
lemma isCentredOn_geomOpen_iff (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
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

/-- Automorphisms over `L₀` map `Ω` into `Ω`. -/
lemma exists_algebraMap_eq_apply {M : Type u} [Field M] [Algebra Ω M]
    (τ : M →+* FFClosure (geomCurve Ω C)) (c : Ω) :
    ∃ c' : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c' = τ (algebraMap Ω M c) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  exact exists_algebraMap_eq_of_isAlgebraic Ω C _
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c).algHom (τ.comp (algebraMap Ω M)).toRatAlgHom)

/-- Places over cusps are moved to places over cusps by `Gal(K(X̄_Ω)^alg / L₀)`. -/
lemma isCuspPlace_comap
    (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C))
    {W : ValuationSubring (FFClosure (geomCurve Ω C))} (hW : IsCuspPlace Ω C hc W) :
    IsCuspPlace Ω C hc
      (W.comap (τ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C))) := by
  refine ⟨fun c ↦ ?_, fun h ↦ hW.2 fun a ↦ ?_⟩
  · rw [ValuationSubring.mem_comap]
    obtain ⟨c', hc'⟩ := exists_algebraMap_eq_apply Ω C
      (τ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C)) c
    rw [← hc']
    exact hW.1 c'
  · have h1 := h a
    rw [ValuationSubring.mem_comap] at h1
    have hfix : τ (secEmb Ω C (isAffineOpen_U C hc) a) = secEmb Ω C (isAffineOpen_U C hc) a :=
      τ.commutes ⟨_, secEmb_mem_arithFF Ω C hc a⟩
    simpa only [RingHom.coe_coe, hfix] using h1

/-- The image in `Π_U` of the inertia group over `L₀ = K(X̄)` of a place `W` of
`K(X̄_Ω)^alg`, under the arithmetic Galois action. -/
def arithInertia (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  Subgroup.closure (arithAction Ω C hc ''
    {σ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C) |
      σ ∈ GaloisPi1.inertia W})

/-- **The arithmetic Galois action `Gal(K(X̄_Ω)^alg / K(X̄)) → Π_U` is surjective** (`Γ(U)` is
integrally closed in `K(X̄)`). -/
theorem arithAction_surjective : Function.Surjective (arithAction Ω C hc) := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  have hU := isAffineOpen_U C hc
  haveI : IsIntegrallyClosed Γ(C.Xbar, C.U) := isIntegrallyClosed_of_isAffineOpen hU
    fun x _ ↦ IsCurveOver.isIntegrallyClosed_stalk K C.Xbar x
  haveI := isFractionRing_sections C hc
  letI : Algebra Γ(C.Xbar, C.U) (arithFF Ω C hc) := (secToArithFF Ω C hc).toAlgebra
  letI : Algebra Γ(C.Xbar, C.U) (FFClosure (geomCurve Ω C)) := (secEmb Ω C hU).toAlgebra
  haveI : IsScalarTower Γ(C.Xbar, C.U) (arithFF Ω C hc) (FFClosure (geomCurve Ω C)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e : C.Xbar.functionField ≃+* arithFF Ω C hc :=
    RingEquiv.ofBijective _ (ffEmb Ω C hc).rangeRestrictField_bijective
  have hcomp : e.symm.toRingHom.comp (secToArithFF Ω C hc) =
      algebraMap Γ(C.Xbar, C.U) C.Xbar.functionField := by
    refine RingHom.ext fun a ↦ e.injective ?_
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    exact Subtype.ext (ffEmb_germ Ω C hc a).symm
  have hs := galoisAction_surjective (F := arithFF Ω C hc) (Ω := FFClosure (geomCurve Ω C))
    Γ(C.Xbar, C.U) (fun a b hab ↦ secEmb_injective Ω C hU
      (congrArg (fun z : arithFF Ω C hc ↦ (z : FFClosure (geomCurve Ω C))) hab))
    fun x hx ↦ by
      have := mem_range_of_isIntegralElem_of_isIntegrallyClosed (RingHom.id _)
        (secToArithFF Ω C hc) e.symm.toRingHom e.symm.injective hcomp
        (t := x) (by rw [RingHom.comp_id]; exact hx)
      exact this
  have hs' := galoisAction_surjective_of_eq (arithFF Ω C hc) (arithGenPt Ω C hc) _
    (specMap_algebraMap_arithGenPt Ω C hc) hs
  exact (autContinuousMulEquivOfIso (arithFiberIso Ω C hc)).surjective.comp hs'

/-- **The cuspidal inertia groups of `Π_U` are exactly the `arithInertia W` of the places over
the cusps** (no conjugation needed: conjugation moves the place, `map_geomCuspInertia_comap`). -/
theorem mem_arithCusps_iff
    {I : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))} :
    I ∈ arithCusps Ω C hc ↔ ∃ W, IsCuspPlace Ω C hc W ∧ I = arithInertia Ω C hc W := by
  constructor
  · rintro ⟨_, ⟨W, hkW, hWU, rfl⟩, g, rfl⟩
    obtain ⟨τ, rfl⟩ := arithAction_surjective Ω C hc g
    have hW : IsCuspPlace Ω C hc W :=
      ⟨hkW, fun h ↦ hWU ((isCentredOn_geomOpen_iff Ω C hc W).2 ⟨hkW, h⟩)⟩
    have hW' := isCuspPlace_comap Ω C hc τ.symm hW
    refine ⟨_, hW', ?_⟩
    exact (map_geomCuspInertia_comap Ω C hc hkW τ hW'.1).symm.trans
      (map_geomCuspInertia Ω C hc hW'.1)
  · rintro ⟨W, hW, rfl⟩
    refine ⟨_, ⟨W, hW.1, fun h ↦ hW.2 ((isCentredOn_geomOpen_iff Ω C hc W).1 h).2, rfl⟩, 1, ?_⟩
    have e1 : (MulAut.conj
        (1 : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp
    rw [e1, Subgroup.map_id]
    exact (map_geomCuspInertia Ω C hc hW.1).symm

/-- The cuspidal inertia groups are closed under conjugation. -/
lemma map_conj_mem_arithCusps {I} (hI : I ∈ arithCusps Ω C hc) (t) :
    I.map (MulAut.conj t).toMonoidHom ∈ arithCusps Ω C hc := by
  obtain ⟨I₀, hI₀, g, rfl⟩ := hI
  refine ⟨I₀, hI₀, t * g, ?_⟩
  rw [Subgroup.map_map]
  exact congrArg (fun φ ↦ Subgroup.map φ _) (MonoidHom.ext fun x ↦ by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group)

/-- The arithmetic generic geometric point `Spec K(X̄_Ω)^alg ⟶ Spec L₀ ⟶ Spec Γ(U)`. -/
abbrev arithPt : Spec (.of (FFClosure (geomCurve Ω C))) ⟶ Spec Γ(C.Xbar, C.U) :=
  Spec.map (CommRingCat.ofHom (algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C)))) ≫
    arithGenPt Ω C hc

/-- **The inertia group of a place `W` in `Π_U`**, moved to the base point by an isomorphism of
fibre functors `β`. -/
def cuspAt (β : fiber (arithPt Ω C hc) ≅
      fiber (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  (galInertia (arithPt Ω C hc) (arithFF Ω C hc) (arithGenPt Ω C hc) rfl W).map
    (autContinuousMulEquivOfIso β).toMulEquiv.toMonoidHom

/-- The change of base point of `arithAction`, from `arithPt`. -/
def arithIso : fiber (arithPt Ω C hc) ≅
    fiber (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  eqToIso (congrArg fiber (specMap_algebraMap_arithGenPt Ω C hc)) ≪≫ arithFiberIso Ω C hc

lemma cuspAt_arithIso (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    cuspAt Ω C hc (arithIso Ω C hc) W = arithInertia Ω C hc W := by
  rw [cuspAt, arithIso, map_autIso_trans,
    map_galInertia_eqToIso _ _ _ (specMap_algebraMap_arithGenPt Ω C hc), galInertia,
    MonoidHom.map_closure, Set.image_image, arithInertia]
  rfl

/-- `cuspAt β W` for another `β` is a conjugate, by an element independent of `W`. -/
lemma exists_cuspAt_eq_conj (β : fiber (arithPt Ω C hc) ≅
      fiber (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    ∃ t, ∀ W, cuspAt Ω C hc β W =
      (arithInertia Ω C hc W).map (MulAut.conj t).toMonoidHom := by
  obtain ⟨t, ht⟩ := exists_map_autIso_eq_conj (arithIso Ω C hc) β
  exact ⟨t, fun W ↦ (ht _).trans (by rw [← cuspAt, cuspAt_arithIso])⟩

/-- `cuspAt β W` is a cuspidal inertia group of `Π_U` if `W` lies over a cusp. -/
theorem cuspAt_mem_arithCusps (β : fiber (arithPt Ω C hc) ≅
      fiber (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    {W : ValuationSubring (FFClosure (geomCurve Ω C))} (hW : IsCuspPlace Ω C hc W) :
    cuspAt Ω C hc β W ∈ arithCusps Ω C hc := by
  obtain ⟨t, ht⟩ := exists_cuspAt_eq_conj Ω C hc β
  rw [ht]
  exact map_conj_mem_arithCusps Ω C hc ((mem_arithCusps_iff Ω C hc).2 ⟨W, hW, rfl⟩) t

/-- **Every cuspidal inertia group of `Π_U` is `cuspAt β W`** for a place `W` over a cusp, for
any fixed `β`. -/
theorem exists_cuspAt_eq (β : fiber (arithPt Ω C hc) ≅
      fiber (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    {I} (hI : I ∈ arithCusps Ω C hc) :
    ∃ W, IsCuspPlace Ω C hc W ∧ cuspAt Ω C hc β W = I := by
  obtain ⟨t, ht⟩ := exists_cuspAt_eq_conj Ω C hc β
  obtain ⟨W, hW, hWI⟩ := (mem_arithCusps_iff Ω C hc).1 (map_conj_mem_arithCusps Ω C hc hI t⁻¹)
  refine ⟨W, hW, ?_⟩
  rw [ht, ← hWI, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id I]
  exact congrArg (fun φ ↦ Subgroup.map φ I) (MonoidHom.ext fun x ↦ by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group)

end Curve

/-! ### Finite étale maps of affine hyperbolic curves -/

lemma isTorsionFree_of_fields (F L : Type*) [Field F] [Field L] [Algebra F L] :
    Module.IsTorsionFree F L :=
  .of_smul_eq_zero fun r m h ↦ by
    rw [Algebra.smul_def] at h
    exact (mul_eq_zero.1 h).imp_left fun h' ↦
      (algebraMap F L).injective (h'.trans (map_zero _).symm)

section Cover

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {K' : Type u} [Field K'] [NumberField K'] [Algebra K' Ω] [Algebra.IsAlgebraic K' Ω]
  (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  (C' : HypCurve K') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
  (F : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- An isomorphism of fibre functors of `U` from the image of the base point of `Π_{U'}` to the
base point of `Π_U`. -/
def coverFib : fiber ((basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) ≫ F) ≅
    fiber (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  haveI := isIntegral_specSections C hc
  (nonempty_iso_of_fiberFunctor _ _).some

/-- **`Π_{U'} → Π_U`** induced by `F : U' ⟶ U` (followed by a change of base point). -/
def coverPiHom : (arithmeticExt Ω C' hc').Pi →ₜ* (arithmeticExt Ω C hc).Pi :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (autContinuousMulEquivOfIso (coverFib Ω C hc C' hc' F))).comp (fundamentalGroupMap F rfl)

lemma coverPiHom_apply (γ : (arithmeticExt Ω C' hc').Pi) :
    coverPiHom Ω C hc C' hc' F γ =
      autContinuousMulEquivOfIso (coverFib Ω C hc C' hc' F) (fundamentalGroupMap F rfl γ) :=
  rfl

variable [IsFiniteEtale F]

/-- `Π_{U'} → Π_U` is injective. -/
theorem coverPiHom_injective : Function.Injective (coverPiHom Ω C hc C' hc' F) := by
  haveI := isIntegral_specSections C' hc'
  exact (autContinuousMulEquivOfIso _).injective.comp
    (fundamentalGroupMap_injective_of_isFiniteEtale' F
      (basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) rfl)

/-- `Π_{U'} → Π_U` has open image. -/
theorem isOpen_range_coverPiHom : IsOpen (Set.range (coverPiHom Ω C hc C' hc' F)) := by
  have h := isOpen_range_fundamentalGroupMap_of_isFiniteEtale F
    (basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) rfl
  have e : Set.range (coverPiHom Ω C hc C' hc' F) =
      autContinuousMulEquivOfIso (coverFib Ω C hc C' hc' F) ''
        Set.range (fundamentalGroupMap F rfl) := by
    rw [← Set.range_comp]
    rfl
  rw [e]
  exact (autContinuousMulEquivOfIso (coverFib Ω C hc C' hc' F)).toHomeomorph.isOpenMap _ h

/-! #### The function fields -/

/-- The ring map `Γ(U) → Γ(U')` of `F`. -/
abbrev coverRing : Γ(C.Xbar, C.U) →+* Γ(C'.Xbar, C'.U) := (Spec.preimage F).hom

lemma specMap_coverRing : Spec.map (CommRingCat.ofHom (coverRing C C' F)) = F := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- `Γ(U')` is finite over `Γ(U)`. -/
lemma coverRing_finite : (coverRing C C' F).Finite := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (coverRing C C' F))) := by
    rw [specMap_coverRing]
    infer_instance
  rwa [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom] at this

/-- `Γ(U) → Γ(U')` is injective (`Γ(U')` is flat over the domain `Γ(U)`). -/
lemma coverRing_injective : Function.Injective (coverRing C C' F) := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  haveI := IsCurveOver.isIntegral K' C'.Xbar
  haveI : Nonempty C'.U := C'.nonempty.to_subtype
  have hflat : (coverRing C C' F).Flat := by
    have : Flat (Spec.map (CommRingCat.ofHom (coverRing C C' F))) := by
      rw [specMap_coverRing]
      infer_instance
    rwa [Flat.SpecMap_iff, CommRingCat.hom_ofHom] at this
  letI := (coverRing C C' F).toAlgebra
  haveI : Module.Flat Γ(C.Xbar, C.U) Γ(C'.Xbar, C'.U) := hflat
  refine (injective_iff_map_eq_zero _).2 fun r hr ↦ by_contra fun hr0 ↦ ?_
  have hreg := Module.Flat.isSMulRegular_of_isRegular (M := Γ(C'.Xbar, C'.U))
    (IsRegular.of_ne_zero hr0)
  have h1 : r • (1 : Γ(C'.Xbar, C'.U)) = r • 0 := by
    rw [Algebra.smul_def, mul_one, smul_zero]
    exact hr
  exact one_ne_zero (hreg h1)

include hc' in
/-- **The map of function fields `ℓ : L₀ = K(X̄) → L₀' = K(X̄')`** induced by `F`. -/
def coverFF : arithFF Ω C hc →+* arithFF Ω C' hc' :=
  haveI := IsCurveOver.isIntegral K' C'.Xbar
  haveI : Nonempty C'.U := C'.nonempty.to_subtype
  haveI := isFractionRing_sections C hc
  (((ffEmb Ω C' hc').rangeRestrictField).comp
    (IsFractionRing.lift (A := Γ(C.Xbar, C.U)) (K := C.Xbar.functionField)
      (g := (C'.Xbar.germToFunctionField C'.U).hom.comp (coverRing C C' F))
      (show Function.Injective ((C'.Xbar.germToFunctionField C'.U).hom ∘ coverRing C C' F) from
        (C'.Xbar.germToFunctionField_injective C'.U).comp (coverRing_injective C C' F)))).comp
    (RingEquiv.ofBijective _ (ffEmb Ω C hc).rangeRestrictField_bijective).symm.toRingHom

lemma coverFF_secToArithFF (a : Γ(C.Xbar, C.U)) :
    coverFF Ω C hc C' hc' F (secToArithFF Ω C hc a) =
      secToArithFF Ω C' hc' (coverRing C C' F a) := by
  haveI := IsCurveOver.isIntegral K' C'.Xbar
  haveI : Nonempty C'.U := C'.nonempty.to_subtype
  haveI := isFractionRing_sections C hc
  let e : C.Xbar.functionField ≃+* arithFF Ω C hc :=
    RingEquiv.ofBijective _ (ffEmb Ω C hc).rangeRestrictField_bijective
  have h1 : e.symm (secToArithFF Ω C hc a) = C.Xbar.germToFunctionField C.U a := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact Subtype.ext (ffEmb_germ Ω C hc a).symm
  change (ffEmb Ω C' hc').rangeRestrictField (IsFractionRing.lift _ (e.symm _)) = _
  rw [h1]
  refine Subtype.ext ?_
  rw [RingHom.coe_rangeRestrictField]
  change ffEmb Ω C' hc' (IsFractionRing.lift _ (algebraMap Γ(C.Xbar, C.U) _ a)) = _
  rw [IsFractionRing.lift_algebraMap]
  exact ffEmb_germ Ω C' hc' _

/-- Elements of `L₀` are quotients of sections. -/
lemma exists_eq_div_secToArithFF (x : arithFF Ω C hc) :
    ∃ a b, x = secToArithFF Ω C hc a / secToArithFF Ω C hc b := by
  haveI := isFractionRing_sections C hc
  obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.1 x.2
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(C.Xbar, C.U)) z
  refine ⟨a, b, Subtype.ext ?_⟩
  rw [← hz, map_div₀, Subfield.coe_div]
  exact congrArg₂ (· / ·) (ffEmb_germ Ω C hc a) (ffEmb_germ Ω C hc b)

/-- **`L₀'` is finite over `L₀`** (`Γ(U')` is finite over `Γ(U)`). -/
theorem finiteDimensional_coverFF :
    letI := (coverFF Ω C hc C' hc' F).toAlgebra
    FiniteDimensional (arithFF Ω C hc) (arithFF Ω C' hc') := by
  letI := (coverFF Ω C hc C' hc' F).toAlgebra
  letI := (coverRing C C' F).toAlgebra
  have hfin : Module.Finite Γ(C.Xbar, C.U) Γ(C'.Xbar, C'.U) := coverRing_finite C C' F
  obtain ⟨s, hs⟩ := hfin.fg_top
  let ψ := secToArithFF Ω C' hc'
  let A := Algebra.adjoin (arithFF Ω C hc) ((ψ : Γ(C'.Xbar, C'.U) → arithFF Ω C' hc') '' s)
  have hint : ∀ b : Γ(C'.Xbar, C'.U), IsIntegral (arithFF Ω C hc) (ψ b) := fun b ↦ by
    have hb : IsIntegral Γ(C.Xbar, C.U) b := (coverRing_finite C C' F).to_isIntegral b
    exact hb.map_of_comp_eq (secToArithFF Ω C hc) ψ
      (RingHom.ext fun a ↦ coverFF_secToArithFF Ω C hc C' hc' F a)
  have hAfg : (Subalgebra.toSubmodule A).FG :=
    fg_adjoin_of_finite (s.finite_toSet.image _) (by rintro _ ⟨b, -, rfl⟩; exact hint b)
  have hψA : ∀ b, ψ b ∈ A := by
    intro b
    have hb : b ∈ Submodule.span Γ(C.Xbar, C.U) (s : Set Γ(C'.Xbar, C'.U)) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem A
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul]
      have e : ψ (algebraMap Γ(C.Xbar, C.U) Γ(C'.Xbar, C'.U) a) =
          algebraMap (arithFF Ω C hc) (arithFF Ω C' hc') (secToArithFF Ω C hc a) :=
        (coverFF_secToArithFF Ω C hc C' hc' F a).symm
      rw [e]
      exact mul_mem (A.algebraMap_mem _) hx
  have htop : A = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, rfl⟩ := exists_eq_div_secToArithFF Ω C' hc' x
    rw [div_eq_mul_inv]
    exact mul_mem (hψA a) ((hint b).inv_mem (hψA b))
  rw [htop, Algebra.top_toSubmodule] at hAfg
  exact ⟨hAfg⟩

/-- `L₀ → K(X̄'_Ω)^alg` through `ℓ`. -/
abbrev coverAlgFV : Algebra (arithFF Ω C hc) (FFClosure (geomCurve Ω C')) :=
  ((algebraMap (arithFF Ω C' hc') (FFClosure (geomCurve Ω C'))).comp
    (coverFF Ω C hc C' hc' F)).toAlgebra

/-- **`σ : K(X̄_Ω)^alg ≅ K(X̄'_Ω)^alg` over `L₀`**: both are algebraic closures of `L₀`. -/
def coverσ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C') :=
  letI := (coverFF Ω C hc C' hc' F).toAlgebra
  letI := coverAlgFV Ω C hc C' hc' F
  haveI : IsScalarTower (arithFF Ω C hc) (arithFF Ω C' hc') (FFClosure (geomCurve Ω C')) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := finiteDimensional_coverFF Ω C hc C' hc' F
  haveI := isTorsionFree_of_fields (arithFF Ω C hc) (FFClosure (geomCurve Ω C'))
  haveI := isTorsionFree_of_fields (arithFF Ω C hc) (FFClosure (geomCurve Ω C))
  haveI : Algebra.IsAlgebraic (arithFF Ω C hc) (FFClosure (geomCurve Ω C')) :=
    Algebra.IsAlgebraic.trans (arithFF Ω C hc) (arithFF Ω C' hc') _
  haveI : IsAlgClosure (arithFF Ω C hc) (FFClosure (geomCurve Ω C')) :=
    ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosure (arithFF Ω C hc) (FFClosure (geomCurve Ω C)) :=
    ⟨inferInstance, inferInstance⟩
  (IsAlgClosure.equiv (arithFF Ω C hc) (FFClosure (geomCurve Ω C))
    (FFClosure (geomCurve Ω C'))).toRingEquiv

lemma coverσ_algebraMap (c : arithFF Ω C hc) :
    coverσ Ω C hc C' hc' F (algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C)) c) =
      algebraMap (arithFF Ω C' hc') (FFClosure (geomCurve Ω C')) (coverFF Ω C hc C' hc' F c) :=
  letI := (coverFF Ω C hc C' hc' F).toAlgebra
  letI := coverAlgFV Ω C hc C' hc' F
  haveI : IsScalarTower (arithFF Ω C hc) (arithFF Ω C' hc') (FFClosure (geomCurve Ω C')) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := finiteDimensional_coverFF Ω C hc C' hc' F
  haveI := isTorsionFree_of_fields (arithFF Ω C hc) (FFClosure (geomCurve Ω C'))
  haveI := isTorsionFree_of_fields (arithFF Ω C hc) (FFClosure (geomCurve Ω C))
  haveI : Algebra.IsAlgebraic (arithFF Ω C hc) (FFClosure (geomCurve Ω C')) :=
    Algebra.IsAlgebraic.trans (arithFF Ω C hc) (arithFF Ω C' hc') _
  haveI : IsAlgClosure (arithFF Ω C hc) (FFClosure (geomCurve Ω C')) :=
    ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosure (arithFF Ω C hc) (FFClosure (geomCurve Ω C)) :=
    ⟨inferInstance, inferInstance⟩
  (IsAlgClosure.equiv (arithFF Ω C hc) (FFClosure (geomCurve Ω C))
    (FFClosure (geomCurve Ω C'))).commutes c

lemma coverσ_secEmb (a : Γ(C.Xbar, C.U)) :
    coverσ Ω C hc C' hc' F (secEmb Ω C (isAffineOpen_U C hc) a) =
      secEmb Ω C' (isAffineOpen_U C' hc') (coverRing C C' F a) := by
  have := coverσ_algebraMap Ω C hc C' hc' F (secToArithFF Ω C hc a)
  rw [coverFF_secToArithFF] at this
  exact this

/-- **Places over cusps correspond**: `W` lies over a cusp of `U'` iff `σ⁻¹(W)` lies over a cusp
of `U`. -/
theorem isCuspPlace_comap_coverσ (W : ValuationSubring (FFClosure (geomCurve Ω C'))) :
    IsCuspPlace Ω C' hc' W ↔
      IsCuspPlace Ω C hc (W.comap (coverσ Ω C hc C' hc' F : _ →+* _)) := by
  set σ := coverσ Ω C hc C' hc' F
  have hval : (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C')) c ∈ W) ↔
      ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈
        W.comap (σ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C')) := by
    constructor
    · intro h c
      rw [ValuationSubring.mem_comap]
      obtain ⟨c', hc'⟩ := exists_algebraMap_eq_apply Ω C'
        (σ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C')) c
      rw [← hc']
      exact h c'
    · intro h c
      obtain ⟨c', hc'⟩ := exists_algebraMap_eq_apply Ω C
        (σ.symm : FFClosure (geomCurve Ω C') →+* FFClosure (geomCurve Ω C)) c
      have := h c'
      rw [ValuationSubring.mem_comap, hc'] at this
      simpa using this
  have hsec : (∀ b : Γ(C'.Xbar, C'.U), secEmb Ω C' (isAffineOpen_U C' hc') b ∈ W) ↔
      ∀ a : Γ(C.Xbar, C.U), secEmb Ω C (isAffineOpen_U C hc) a ∈
        W.comap (σ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C')) := by
    constructor
    · intro h a
      rw [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, coverσ_secEmb]
      exact h _
    · intro h b
      have hA : ∀ a, secEmb Ω C' (isAffineOpen_U C' hc') (coverRing C C' F a) ∈ W.toSubring :=
        fun a ↦ by
          have := h a
          rwa [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, coverσ_secEmb] at this
      letI := (coverRing C C' F).toAlgebra
      have hint : IsIntegral Γ(C.Xbar, C.U) b := (coverRing_finite C C' F).to_isIntegral b
      let g : Γ(C.Xbar, C.U) →+* W.toSubring :=
        ((secEmb Ω C' (isAffineOpen_U C' hc')).comp (coverRing C C' F)).codRestrict W.toSubring hA
      have hcomp : (algebraMap W.toSubring (FFClosure (geomCurve Ω C'))).comp g =
          (secEmb Ω C' (isAffineOpen_U C' hc')).comp
            (algebraMap Γ(C.Xbar, C.U) Γ(C'.Xbar, C'.U)) := rfl
      have hb := hint.map_of_comp_eq g (secEmb Ω C' (isAffineOpen_U C' hc')) hcomp
      haveI : IsIntegrallyClosedIn W.toSubring (FFClosure (geomCurve Ω C')) :=
        inferInstanceAs (IsIntegrallyClosedIn W (FFClosure (geomCurve Ω C')))
      obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hb
      change secEmb Ω C' (isAffineOpen_U C' hc') b ∈ W.toSubring
      rw [← hy]
      exact y.2
  exact and_congr hval (not_congr hsec)

/-- The point equation `x_{U'} ≫ F = Spec σ ≫ x_U` of the arithmetic generic points. -/
lemma arithGenPt_comp_cover :
    letI := (coverFF Ω C hc C' hc' F).toAlgebra
    arithGenPt Ω C' hc' ≫ F = Spec.map (CommRingCat.ofHom
      (algebraMap (arithFF Ω C hc) (arithFF Ω C' hc'))) ≫ arithGenPt Ω C hc := by
  letI := (coverFF Ω C hc C' hc' F).toAlgebra
  conv_lhs => rw [← specMap_coverRing C C' F]
  rw [arithGenPt, arithGenPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun a ↦ (coverFF_secToArithFF Ω C hc C' hc' F a).symm

lemma arithPt_comp_cover :
    arithPt Ω C' hc' ≫ F = specIso (coverσ Ω C hc C' hc' F) ≫ arithPt Ω C hc := by
  letI := (coverFF Ω C hc C' hc' F).toAlgebra
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap (arithFF Ω C' hc')
        (FFClosure (geomCurve Ω C')))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (arithFF Ω C hc) (arithFF Ω C' hc'))) =
      specIso (coverσ Ω C hc C' hc' F) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C)))) := by
    rw [specIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ (coverσ_algebraMap Ω C hc C' hc' F c).symm
  rw [arithPt, arithPt, Category.assoc, arithGenPt_comp_cover Ω C hc C' hc' F, ← Category.assoc,
    e1, Category.assoc]

/-- `coverPiHom` on `cuspAt`, through `π₁ᵉᵗ(F)` at the arithmetic generic point. -/
lemma map_cuspAt_coverPiHom (βV : fiber (arithPt Ω C' hc') ≅
      fiber (basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)))
    (W : ValuationSubring (FFClosure (geomCurve Ω C'))) :
    (cuspAt Ω C' hc' βV W).map (coverPiHom Ω C hc C' hc' F).toMonoidHom =
      ((galInertia (arithPt Ω C' hc') (arithFF Ω C' hc') (arithGenPt Ω C' hc') rfl W).map
        (fundamentalGroupMap F rfl).toMonoidHom).map
          (autContinuousMulEquivOfIso (fiberIsoMap F rfl rfl βV ≪≫
            coverFib Ω C hc C' hc' F)).toMulEquiv.toMonoidHom := by
  rw [cuspAt, Subgroup.map_map, Subgroup.map_map]
  refine congrArg (fun φ ↦ Subgroup.map φ _) (MonoidHom.ext fun τ ↦ ?_)
  change autContinuousMulEquivOfIso (coverFib Ω C hc C' hc' F)
    (fundamentalGroupMap F rfl (autContinuousMulEquivOfIso βV τ)) =
      autContinuousMulEquivOfIso (fiberIsoMap F rfl rfl βV ≪≫ coverFib Ω C hc C' hc' F)
        (fundamentalGroupMap F rfl τ)
  rw [fundamentalGroupMap_autContinuousMulEquivOfIso F rfl rfl βV τ]
  exact (Iso.trans_conjAut (fiberIsoMap F rfl rfl βV) (coverFib Ω C hc C' hc' F) _).symm

/-- **The main comparison**: `coverPiHom` maps the inertia group of `W` in `Π_{U'}` into the
inertia group of `σ⁻¹(W)` in `Π_U`, with finite index (for a suitable change of base point `β`
of `U`, independent of `W`). -/
theorem exists_map_cuspAt_coverHom_le (βV : fiber (arithPt Ω C' hc') ≅
      fiber (basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U))) :
    ∃ β : fiber (arithPt Ω C hc) ≅
        fiber (basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
      ∀ W : ValuationSubring (FFClosure (geomCurve Ω C')),
        (cuspAt Ω C' hc' βV W).map (coverPiHom Ω C hc C' hc' F).toMonoidHom ≤
            cuspAt Ω C hc β (W.comap (coverσ Ω C hc C' hc' F : _ →+* _)) ∧
          ((cuspAt Ω C' hc' βV W).map (coverPiHom Ω C hc C' hc' F).toMonoidHom).relIndex
            (cuspAt Ω C hc β (W.comap (coverσ Ω C hc C' hc' F : _ →+* _))) ≠ 0 := by
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
  let δ := fiberIsoMap F rfl rfl βV ≪≫ coverFib Ω C hc C' hc' F
  let γ := eqToIso (congrArg fiber (arithPt_comp_cover Ω C hc C' hc' F)) ≪≫
    fieldChangeIso (coverσ Ω C hc C' hc' F) (arithPt Ω C hc)
  refine ⟨γ.symm ≪≫ δ, fun W ↦ ?_⟩
  have hj := arithGenPt_comp_cover Ω C hc C' hc' F
  have h1 := map_galInertia_le F (arithGenPt Ω C' hc') (arithGenPt Ω C hc) hj W
  have h2 := relIndex_map_galInertia_ne_zero F (arithGenPt Ω C' hc') (arithGenPt Ω C hc) hj W
  have k2 : cuspAt Ω C hc (γ.symm ≪≫ δ) (W.comap (coverσ Ω C hc C' hc' F : _ →+* _)) =
      (galInertia _ (arithFF Ω C hc) (arithGenPt Ω C hc)
        (specAlgebraMap_comp_generic F (arithGenPt Ω C' hc') (arithGenPt Ω C hc) hj) W).map
          (autContinuousMulEquivOfIso δ).toMulEquiv.toMonoidHom := by
    have hm : (galInertia _ (arithFF Ω C hc) (arithGenPt Ω C hc)
        (specAlgebraMap_comp_generic F (arithGenPt Ω C' hc') (arithGenPt Ω C hc) hj) W).map
          (autContinuousMulEquivOfIso γ).toMulEquiv.toMonoidHom =
        galInertia (arithPt Ω C hc) (arithFF Ω C hc) (arithGenPt Ω C hc) rfl
          (W.comap (coverσ Ω C hc C' hc' F : _ →+* _)) :=
      by
        have h3 := map_galInertia_eqToIso (arithFF Ω C hc) (arithGenPt Ω C hc)
          (specAlgebraMap_comp_generic F (arithGenPt Ω C' hc') (arithGenPt Ω C hc) hj)
          (arithPt_comp_cover Ω C hc C' hc' F) W
        have h4 := map_galInertia_fieldChange (coverσ Ω C hc C' hc' F) (arithPt Ω C hc)
          (arithFF Ω C hc) (coverσ_algebraMap Ω C hc C' hc' F) (arithGenPt Ω C hc) rfl W
        rw [map_autIso_trans, h3]
        exact h4
    rw [cuspAt, ← hm, ← map_autIso_trans]
    exact congrArg (fun i ↦ Subgroup.map (autContinuousMulEquivOfIso i).toMulEquiv.toMonoidHom
      (galInertia _ (arithFF Ω C hc) (arithGenPt Ω C hc) _ W)) (Iso.self_symm_id_assoc γ δ)
  rw [map_cuspAt_coverPiHom, k2]
  refine ⟨Subgroup.map_mono h1, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ (autContinuousMulEquivOfIso δ).injective]
  exact h2

/-- **(b) Every cuspidal inertia group of `Π_{U'}` maps into a cuspidal inertia group of `Π_U`,
with finite index.** -/
theorem exists_arithCusps_map_coverPiHom {J} (hJ : J ∈ arithCusps Ω C' hc') :
    ∃ I ∈ arithCusps Ω C hc, J.map (coverPiHom Ω C hc C' hc' F).toMonoidHom ≤ I ∧
      (J.map (coverPiHom Ω C hc C' hc' F).toMonoidHom).relIndex I ≠ 0 := by
  obtain ⟨β, hβ⟩ := exists_map_cuspAt_coverHom_le Ω C hc C' hc' F (arithIso Ω C' hc')
  obtain ⟨W, hW, rfl⟩ := exists_cuspAt_eq Ω C' hc' (arithIso Ω C' hc') hJ
  exact ⟨_, cuspAt_mem_arithCusps Ω C hc β ((isCuspPlace_comap_coverσ Ω C hc C' hc' F W).1 hW),
    hβ W⟩

/-- **(a) Every cuspidal inertia group of `Π_U` contains, with finite index, the image of a
cuspidal inertia group of `Π_{U'}`.** -/
theorem exists_arithCusps_coverHom_le {I} (hI : I ∈ arithCusps Ω C hc) :
    ∃ J ∈ arithCusps Ω C' hc', J.map (coverPiHom Ω C hc C' hc' F).toMonoidHom ≤ I ∧
      (J.map (coverPiHom Ω C hc C' hc' F).toMonoidHom).relIndex I ≠ 0 := by
  obtain ⟨β, hβ⟩ := exists_map_cuspAt_coverHom_le Ω C hc C' hc' F (arithIso Ω C' hc')
  obtain ⟨W', hW', rfl⟩ := exists_cuspAt_eq Ω C hc β hI
  set σ := coverσ Ω C hc C' hc' F
  have hWW : (W'.comap (σ.symm : FFClosure (geomCurve Ω C') →+* FFClosure (geomCurve Ω C))).comap
      (σ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C')) = W' := by
    ext x
    simp [ValuationSubring.mem_comap]
  have hW : IsCuspPlace Ω C' hc'
      (W'.comap (σ.symm : FFClosure (geomCurve Ω C') →+* FFClosure (geomCurve Ω C))) :=
    (isCuspPlace_comap_coverσ Ω C hc C' hc' F _).2 (by rw [hWW]; exact hW')
  refine ⟨_, cuspAt_mem_arithCusps Ω C' hc' (arithIso Ω C' hc') hW, ?_⟩
  have := hβ (W'.comap (σ.symm : FFClosure (geomCurve Ω C') →+* FFClosure (geomCurve Ω C)))
  rwa [hWW] at this

/-! #### Covers lying over an extension of number fields -/

section Tower

variable [Algebra K K'] [IsScalarTower K K' Ω]

variable (hF : F ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K')))

include hF in
lemma coverPiHom_base_spec :
    ((basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)) ≫ F) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [Category.assoc, hF, ← Category.assoc, basePoint_spec₂, specMap_algebraMap_tower]

/-- The element of `G_K` by which the change of base point conjugates (`pr_coverPiHom`). -/
def coverG : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  fiberIsoMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
    (coverPiHom_base_spec Ω C C' hc' F hF) (basePoint_spec₂ Ω C hc) (coverFib Ω C hc C' hc' F)

/-- **`ι : G_{K'} → G_K`** for `coverPiHom`: `galoisMap` followed by conjugation by `coverG`. -/
def coverι : (arithmeticExt Ω C' hc').G →ₜ* (arithmeticExt Ω C hc).G :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (autContinuousMulEquivOfIso (coverG Ω C hc C' hc' F hF))).comp (galoisMap K K' Ω)

/-- **Compatibility with the projections**: `pr ∘ coverPiHom = coverι ∘ pr'`. -/
theorem pr_coverPiHom (γ : (arithmeticExt Ω C' hc').Pi) :
    (arithmeticExt Ω C hc).pr (coverPiHom Ω C hc C' hc' F γ) =
      coverι Ω C hc C' hc' F hF ((arithmeticExt Ω C' hc').pr γ) := by
  let sK := Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)))
  let sK' := Spec.map (CommRingCat.ofHom (algebraMap K' Γ(C'.Xbar, C'.U)))
  let x' := basePoint Ω C' hc' ≫ baseChangeSpec K' Ω Γ(C'.Xbar, C'.U)
  have h1 : (x' ≫ F) ≫ sK = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
    coverPiHom_base_spec Ω C C' hc' F hF
  have hB := fundamentalGroupMap_autContinuousMulEquivOfIso sK h1 (basePoint_spec₂ Ω C hc)
    (coverFib Ω C hc C' hc' F) (fundamentalGroupMap F rfl γ)
  have hC : fundamentalGroupMap sK h1 (fundamentalGroupMap F rfl γ) =
      galoisMap K K' Ω ((arithmeticExt Ω C' hc').pr γ) := by
    have h3 : x' ≫ F ≫ sK = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
      (Category.assoc _ _ _).symm.trans h1
    have h4 : x' ≫ sK' ≫ Spec.map (CommRingCat.ofHom (algebraMap K K')) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := hF ▸ h3
    have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp F sK rfl h1 h3) γ
    have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp _ _ (basePoint_spec₂ Ω C' hc')
      (specMap_algebraMap_tower K K' Ω) h4) γ
    rw [fundamentalGroupMap_congr hF h3 h4] at c1
    exact c1.symm.trans c2
  change fundamentalGroupMap sK (basePoint_spec₂ Ω C hc) (autContinuousMulEquivOfIso
    (coverFib Ω C hc C' hc' F) (fundamentalGroupMap F rfl γ)) = _
  rw [hB, hC]
  rfl

/-- `coverι` is injective. -/
theorem coverι_injective : Function.Injective (coverι Ω C hc C' hc' F hF) :=
  (autContinuousMulEquivOfIso _).injective.comp (galoisMap_injective K K' Ω)

/-- `coverι` has open image. -/
theorem isOpen_range_coverι : IsOpen (Set.range (coverι Ω C hc C' hc' F hF)) := by
  haveI := isFiniteEtale_specMap_numberField (K := K) (K' := K')
  have h := isOpen_range_fundamentalGroupMap_of_isFiniteEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K K'))) (Spec.map (CommRingCat.ofHom
      (algebraMap K' Ω))) (specMap_algebraMap_tower K K' Ω)
  have e : Set.range (coverι Ω C hc C' hc' F hF) =
      autContinuousMulEquivOfIso (coverG Ω C hc C' hc' F hF) ''
        Set.range (galoisMap K K' Ω) := by
    rw [← Set.range_comp]
    rfl
  rw [e]
  exact (autContinuousMulEquivOfIso (coverG Ω C hc C' hc' F hF)).toHomeomorph.isOpenMap _ h

end Tower

end Cover

end CurvesJacobian.Cusp
