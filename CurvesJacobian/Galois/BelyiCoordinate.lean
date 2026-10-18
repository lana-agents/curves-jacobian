/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.BelyiInfty
import Belyi.Converse.BranchedCurve

/-!
# The coordinate function of a morphism to `ℙ¹`

Let `X` be a curve over `k` and `f : X ⟶ ℙ¹_k` a morphism over `k` with `f(η) ≠ ∞` for the
generic point `η` of `X`. Then `Spec K(X) ⟶ X ⟶ ℙ¹` factors through the affine chart
`Belyi.lineι k : 𝔸¹ = Spec k[T] ⟶ ℙ¹`, by `Spec` of a ring map `k[T] → K(X)`
(`CurvesJacobian.coordHom`); its value at `T` is the rational function `x = f^*(T)`
(`CurvesJacobian.coordFun`).

* `CurvesJacobian.coordHom_eq_aeval`: `coordHom = aeval x`.
* `CurvesJacobian.eq_of_fromSpecStalk_comp_eq`: two `k`-morphisms `X ⟶ ℙ¹` which agree at the
  generic point are equal; hence `CurvesJacobian.eq_toP1_coordFun`: **`f = toP1 x`**.
* `CurvesJacobian.transcendental_coordFun`: `x` is transcendental if `f` is dominant (e.g.
  finite).
* `CurvesJacobian.coordFun_mem_stalk_iff`: `x ∈ 𝒪_{X,p}` iff `f(p) ≠ ∞`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi MvPolynomial HomogeneousLocalization

universe u

namespace CurvesJacobian

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped Belyi.P1

section Unique

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsIntegral X]

/-- **Morphisms to `ℙ¹` are determined by the generic point.** Two `k`-morphisms from an integral
`k`-scheme to `ℙ¹_k` which agree on `Spec K(X)` are equal. -/
theorem eq_of_fromSpecStalk_comp_eq {f g : X ⟶ P1 k} [f.IsOver (Spec (CommRingCat.of k))]
    [g.IsOver (Spec (CommRingCat.of k))]
    (h : X.fromSpecStalk (genericPoint X) ≫ f = X.fromSpecStalk (genericPoint X) ≫ g) :
    f = g := by
  have h1 : f.toRationalMap = g.toRationalMap :=
    Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ (by
      rw [fromFunctionField_toRationalMap, fromFunctionField_toRationalMap, h])
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
    (S := Spec (CommRingCat.of k)) (f := f.toPartialMap) (g := g)).1
      (Scheme.PartialMap.toRationalMap_eq_iff.1 h1)
  simp only [Scheme.Hom.toPartialMap_hom] at h2
  rw [← cancel_epi X.topIso.hom, h2]
  rfl

end Unique

/-- A dominant morphism of integral schemes maps the generic point to the generic point. -/
lemma base_genericPoint_of_isDominant {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : X ⟶ Y) [IsDominant g] : g.base (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  have h := (genericPoint_spec X).image g.continuous
  rwa [Set.image_univ, g.denseRange.closure_range] at h

section Coordinate

/-- The range of `𝔸¹ ⟶ ℙ¹` is `ℙ¹ ∖ {∞}`. -/
lemma mem_range_lineι_iff {k : Type u} [Field k] (y : P1 k) :
    y ∈ Set.range (lineι k).base ↔ y ≠ P1.infty k := by
  rw [← mem_range_awayι_one_iff]
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom
      (P1.awayChartEquivOne k).toRingEquiv.toRingHom)).base := by
    haveI : IsIso (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom) :=
      (P1.awayChartEquivOne k).toRingEquiv.toCommRingCatIso.isIso_hom
    exact (Scheme.homeoOfIso (asIso (Spec.map (CommRingCat.ofHom
      (P1.awayChartEquivOne k).toRingEquiv.toRingHom)))).surjective
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hsurj z
    exact ⟨w, rfl⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ P1 k}

/-- If `f(η) ≠ ∞`, the generic point of `X` maps into the affine chart. -/
lemma range_fromSpecStalk_comp_subset (hη : f.base (genericPoint X) ≠ P1.infty k) :
    Set.range (X.fromSpecStalk (genericPoint X) ≫ f).base ⊆ Set.range (lineι k).base := by
  rintro _ ⟨z, rfl⟩
  rw [mem_range_lineι_iff]
  have hz : z = IsLocalRing.closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  rw [hz, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  exact hη

variable (f) in
/-- **The coordinate ring map** `k[T] → K(X)` of `f` (for `f(η) ≠ ∞`): `Spec K(X) ⟶ X ⟶ ℙ¹`
is `Spec` of it followed by `𝔸¹ ⟶ ℙ¹`. -/
def coordHom (hη : f.base (genericPoint X) ≠ P1.infty k) :
    CommRingCat.of (Polynomial k) ⟶ X.functionField :=
  Spec.preimage (IsOpenImmersion.lift (lineι k) _ (range_fromSpecStalk_comp_subset hη))

lemma spec_map_coordHom (hη : f.base (genericPoint X) ≠ P1.infty k) :
    Spec.map (coordHom f hη) =
      IsOpenImmersion.lift (lineι k) _ (range_fromSpecStalk_comp_subset hη) :=
  Spec.map_preimage _

@[reassoc]
lemma spec_map_coordHom_comp_lineι (hη : f.base (genericPoint X) ≠ P1.infty k) :
    Spec.map (coordHom f hη) ≫ lineι k = X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [spec_map_coordHom, IsOpenImmersion.lift_fac]

variable (f) in
/-- **The coordinate function** `x = f^*(T) ∈ K(X)` of `f`. -/
def coordFun (hη : f.base (genericPoint X) ≠ P1.infty k) : X.functionField :=
  (coordHom f hη).hom Polynomial.X

variable [X.Over (Spec (CommRingCat.of k))]

/-- `k[T] → K(X)` is a `k`-algebra map if `f` is a `k`-morphism. -/
lemma coordHom_C (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (c : k) :
    (coordHom f hη).hom (Polynomial.C c) = algebraMap k X.functionField c := by
  have h : CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ coordHom f hη =
      CommRingCat.ofHom (algebraMap k X.functionField) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← lineι_structMap, spec_map_coordHom_comp_lineι_assoc, hfk,
      specMap_algebraMap_functionField]
  exact congrArg (fun φ ↦ φ.hom c) h

/-- The coordinate ring map as a `k`-algebra map. -/
def coordAlgHom (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    Polynomial k →ₐ[k] X.functionField :=
  { (coordHom f hη).hom with commutes' := coordHom_C hη hfk }

/-- **`k[T] → K(X)` is evaluation at `x`.** -/
lemma coordHom_eq_aeval (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (p : Polynomial k) :
    (coordHom f hη).hom p = Polynomial.aeval (coordFun f hη) p := by
  have h : coordAlgHom hη hfk = Polynomial.aeval (coordFun f hη) :=
    Polynomial.algHom_ext (by rw [Polynomial.aeval_X]; rfl)
  exact DFunLike.congr_fun h p

/-- `Spec K(X) ⟶ 𝔸¹ ⟶ ℙ¹` is the `K(X)`-point of `ℙ¹` with coordinate `x`. -/
lemma spec_map_coordHom_comp_lineι_eq_point (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    Spec.map (coordHom f hη) ≫ lineι k = P1.point k (coordFun f hη) := by
  have hX : (P1.awayChartEquivOne k).symm Polynomial.X = P1.affineCoord k :=
    (AlgEquiv.symm_apply_eq _).mpr (P1.awayChartEquivOne_affineCoord k).symm
  have hA : (P1.awayEvalₐ k (coordFun f hη)).comp
      ((P1.awayChartEquivOne k).symm : Polynomial k →ₐ[k] _) =
        Polynomial.aeval (coordFun f hη) :=
    Polynomial.algHom_ext (by
      rw [AlgHom.comp_apply, Polynomial.aeval_X, AlgEquiv.coe_toAlgHom, hX]
      exact P1.awayEval_affineCoord k _)
  have h : CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom ≫
      coordHom f hη = CommRingCat.ofHom (P1.awayEval k (coordFun f hη)) := by
    ext a
    obtain ⟨p, rfl⟩ := (P1.awayChartEquivOne k).symm.surjective a
    change (coordHom f hη).hom (P1.awayChartEquivOne k ((P1.awayChartEquivOne k).symm p)) =
      P1.awayEvalₐ k (coordFun f hη) ((P1.awayChartEquivOne k).symm p)
    rw [AlgEquiv.apply_symm_apply, coordHom_eq_aeval hη hfk]
    exact (DFunLike.congr_fun hA p).symm
  rw [lineι, ← Category.assoc, ← Spec.map_comp, h]
  rfl

/-- **`x` is transcendental** if `f` is dominant: `Spec K(X)` maps to the generic point of `𝔸¹`,
so `k[T] → K(X)` is injective. -/
theorem transcendental_coordFun [IsDominant f] (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    Transcendental k (coordFun f hη) := by
  haveI : IsIntegral (P1 k) := inferInstance
  have hgen := base_genericPoint_of_isDominant f
  have hl := genericPoint_eq_of_isOpenImmersion (lineι k)
  have hpt : (Spec.map (coordHom f hη)).base (IsLocalRing.closedPoint X.functionField) =
      genericPoint (Spec (CommRingCat.of (Polynomial k))) := by
    apply (lineι k).isOpenEmbedding.injective
    rw [hl, ← hgen, ← Scheme.Hom.comp_apply, spec_map_coordHom_comp_lineι, Scheme.Hom.comp_apply,
      Scheme.fromSpecStalk_closedPoint]
  rw [genericPoint_eq_bot_of_affine] at hpt
  have hker : RingHom.ker (coordHom f hη).hom = ⊥ := by
    have h := congrArg PrimeSpectrum.asIdeal hpt
    change Ideal.comap (coordHom f hη).hom (IsLocalRing.maximalIdeal X.functionField) = ⊥ at h
    rwa [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot] at h
  rw [transcendental_iff_injective]
  intro p q hpq
  apply (RingHom.injective_iff_ker_eq_bot _).2 hker
  rw [coordHom_eq_aeval hη hfk, coordHom_eq_aeval hη hfk]
  exact hpq

end Coordinate

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X] {f : X ⟶ P1 k}

omit [IsAlgClosed k] in
/-- **`f` is the morphism attached to its coordinate function**: `f = toP1 x`. -/
theorem eq_toP1_coordFun (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    f = toP1 k X (coordFun f hη) := by
  haveI : f.IsOver (Spec (CommRingCat.of k)) :=
    (Scheme.Hom.isOver_iff (Spec (CommRingCat.of k))).mpr hfk
  apply eq_of_fromSpecStalk_comp_eq
  rw [fromSpecStalk_comp_toP1, ← spec_map_coordHom_comp_lineι hη,
    spec_map_coordHom_comp_lineι_eq_point hη hfk]
  rfl

omit [IsAlgClosed k] in
/-- **`x` is regular at `p` iff `f(p) ≠ ∞`**, for `f` finite. -/
theorem coordFun_mem_stalkVS_iff [IsFinite f] (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (p : X) :
    coordFun f hη ∈ stalkVS k p ↔ f.base p ≠ P1.infty k := by
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  have hf : f.base p = (toP1 k X (coordFun f hη)).base p :=
    congrArg (fun g : X ⟶ P1 k ↦ g.base p) (eq_toP1_coordFun hη hfk)
  rw [hf, ne_eq, toP1_eq_infty_iff, not_not, mem_chartOne_iff k hx]

end Curve

end

end CurvesJacobian
