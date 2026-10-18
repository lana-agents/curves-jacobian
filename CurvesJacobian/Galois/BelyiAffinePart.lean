/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.BelyiCoordinate
import CurvesJacobian.Galois.MaxSpecBaseChange
import WeilCurves.Hurwitz.Belyi

/-!
# The ring of the affine part of a finite morphism to `ℙ¹`

Let `X` be a curve over an algebraically closed field `k` of characteristic zero and
`f : X ⟶ ℙ¹_k` a finite `k`-morphism, `x = f^*(T) ∈ K(X)` its coordinate function
(`CurvesJacobian.coordFun`). The affine part `X ×_{ℙ¹} 𝔸¹` of `f` has ring of functions
`B = Belyi.lineCoverRing f`, with coordinate `t` the image of `T`.

* `CurvesJacobian.lineCoverToFunctionField`: the ring map `ρ : B → K(X)` (restriction to the
  generic point), with `ρ(t) = x`; it is injective (`B` is a domain integral over `k[t]` and
  `k[t] → K(X)` is injective).
* `CurvesJacobian.mem_range_lineCoverToFunctionField_iff`: its range is the integral closure of
  `k[x]` in `K(X)` (`CurvesJacobian.mem_range_germToFunctionField_iff`).
* `CurvesJacobian.lineCoverChartEquiv`: hence **`B ≅ A_x`**, weil-curves' chart ring of `x`.
* `CurvesJacobian.card_maximalSpectrum_lineCover_eq`: for `a ∈ k`, the maximal ideals of `B`
  containing `t - a` are as many as the places `Q` of `K(X)` with `ord_Q (x - a) > 0`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField
open scoped IntermediateField

universe u

namespace CurvesJacobian

noncomputable section

/-- On `Spec K` the restriction of `Spec K ⟶ X` to `V ∋ x` is the germ at `x`. -/
lemma fromSpecStalk_appLE {X : Scheme.{u}} {x : X} {V : X.Opens} (hx : x ∈ V)
    (e : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ V) :
    (X.fromSpecStalk x).appLE V ⊤ e = X.presheaf.germ V x hx ≫ (Scheme.ΓSpecIso _).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  rw [show (homOfLE le_top).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ P1 k}

variable (f) in
/-- The generic point of `X`, as a point of the affine part `X ×_{ℙ¹} 𝔸¹`. -/
def lineCoverGeneric (hη : f.base (genericPoint X) ≠ P1.infty k) :
    Spec X.functionField ⟶ lineCover f :=
  pullback.lift (X.fromSpecStalk (genericPoint X)) (Spec.map (coordHom f hη))
    (spec_map_coordHom_comp_lineι hη).symm

variable (f) in
/-- **The restriction `ρ : B → K(X)`** of functions on the affine part to the generic point. -/
def lineCoverToFunctionField (hη : f.base (genericPoint X) ≠ P1.infty k) :
    lineCoverRing f →+* X.functionField :=
  (Scheme.ΓSpecIso X.functionField).hom.hom.comp (lineCoverGeneric f hη).appTop.hom

/-- `ρ ∘ (k[t] → B) = (k[t] → K(X))`. -/
lemma lineCoverToFunctionField_algebraMap (hη : f.base (genericPoint X) ≠ P1.infty k)
    (p : Polynomial k) :
    lineCoverToFunctionField f hη (algebraMap (Polynomial k) (lineCoverRing f) p) =
      (coordHom f hη).hom p := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
      (pullback.snd f (lineι k)).appTop ≫ (lineCoverGeneric f hη).appTop ≫
        (Scheme.ΓSpecIso X.functionField).hom = coordHom f hη := by
    rw [← Scheme.Hom.comp_appTop_assoc, lineCoverGeneric, pullback.lift_snd,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun φ ↦ φ.hom p) h

/-- `ρ(t) = x`. -/
lemma lineCoverToFunctionField_t (hη : f.base (genericPoint X) ≠ P1.infty k) :
    lineCoverToFunctionField f hη (algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X) =
      coordFun f hη :=
  lineCoverToFunctionField_algebraMap hη _

/-- On sections over `V = f⁻¹(𝔸¹)`, `ρ` is the germ at the generic point. -/
lemma lineCoverToFunctionField_appLE (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hgen : genericPoint X ∈ f ⁻¹ᵁ (lineι k).opensRange)
    (e : ⊤ ≤ pullback.fst f (lineι k) ⁻¹ᵁ (f ⁻¹ᵁ (lineι k).opensRange))
    (s : Γ(X, f ⁻¹ᵁ (lineι k).opensRange)) :
    lineCoverToFunctionField f hη ((pullback.fst f (lineι k)).appLE _ ⊤ e s) =
      X.presheaf.germ _ (genericPoint X) hgen s := by
  have hle : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ (f ⁻¹ᵁ (lineι k).opensRange) := by
    intro z _
    rw [Subsingleton.elim (α := PrimeSpectrum X.functionField) z
      (IsLocalRing.closedPoint X.functionField)]
    change (X.fromSpecStalk (genericPoint X)).base (IsLocalRing.closedPoint X.functionField) ∈
      f ⁻¹ᵁ (lineι k).opensRange
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hgen
  have h : (pullback.fst f (lineι k)).appLE _ ⊤ e ≫ (lineCoverGeneric f hη).appTop =
      (X.fromSpecStalk (genericPoint X)).appLE (f ⁻¹ᵁ (lineι k).opensRange) ⊤ hle := by
    have key : ∀ (g : Spec X.functionField ⟶ X) (_ : g = X.fromSpecStalk (genericPoint X)) e',
        g.appLE (f ⁻¹ᵁ (lineι k).opensRange) ⊤ e' =
          (X.fromSpecStalk (genericPoint X)).appLE (f ⁻¹ᵁ (lineι k).opensRange) ⊤ hle := by
      rintro g rfl e'
      rfl
    change _ ≫ (lineCoverGeneric f hη).app ⊤ = _
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact key _ (pullback.lift_fst _ _ _) _
  change (Scheme.ΓSpecIso X.functionField).hom.hom
    (((pullback.fst f (lineι k)).appLE _ ⊤ e ≫ (lineCoverGeneric f hη).appTop).hom s) = _
  rw [h, fromSpecStalk_appLE hgen]
  change ((Scheme.ΓSpecIso X.functionField).inv ≫ (Scheme.ΓSpecIso X.functionField).hom).hom
    (X.presheaf.germ _ _ hgen s) = _
  rw [Iso.inv_hom_id]
  rfl

section Curve

variable [X.Over (Spec (CommRingCat.of k))]

omit [X.Over (Spec (CommRingCat.of k))] in
lemma genericPoint_mem_preimage_lineι (hη : f.base (genericPoint X) ≠ P1.infty k) :
    genericPoint X ∈ f ⁻¹ᵁ (lineι k).opensRange :=
  (mem_range_lineι_iff _).2 hη

omit [IsIntegral X] [X.Over (Spec (CommRingCat.of k))] in
lemma top_le_preimage_fst_lineι :
    ⊤ ≤ pullback.fst f (lineι k) ⁻¹ᵁ (f ⁻¹ᵁ (lineι k).opensRange) := by
  intro z _
  change f.base ((pullback.fst f (lineι k)).base z) ∈ (lineι k).opensRange
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

omit [X.Over (Spec (CommRingCat.of k))] in
/-- **The affine part of `f` is integral** if the generic point does not go to `∞`: its ring `B`
is a domain. -/
theorem isDomain_lineCoverRing_of (hη : f.base (genericPoint X) ≠ P1.infty k) :
    IsDomain (lineCoverRing f) := by
  haveI : Nonempty (lineCover f) :=
    ⟨(lineCoverGeneric f hη).base (IsLocalRing.closedPoint X.functionField)⟩
  haveI := isIntegral_of_isOpenImmersion (pullback.fst f (lineι k))
  infer_instance

omit [IsIntegral X] [X.Over (Spec (CommRingCat.of k))] in
variable (f) in
/-- **The coordinate `t` of `𝔸¹` on the affine part `B` of a finite `f : X ⟶ ℙ¹`**, as a finite
coordinate (`k[t] → B` is finite). -/
def lineCoverCoord [IsFinite f] : Converse.FiniteCoord k (lineCoverRing f) where
  t := algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X
  finite := by
    haveI := lineCoverRing_finite (f := f)
    have e : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦
        algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X) =
        (IsScalarTower.toAlgHom k (Polynomial k) (lineCoverRing f)).comp
          (finOnePolyEquiv k : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k) :=
      MvPolynomial.algHom_ext fun i ↦ by simp [finOnePolyEquiv_eq]
    rw [AlgHom.Finite, e]
    exact RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance)
      (RingHom.Finite.of_surjective _ (finOnePolyEquiv k).surjective)

variable [CharZero k] [IsCurveOver k X] [IsFinite f]

/-- **`ρ : B → K(X)` is injective.** -/
theorem lineCoverToFunctionField_injective (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    Function.Injective (lineCoverToFunctionField f hη) := by
  haveI := isDomain_lineCoverRing_of hη
  haveI := lineCoverRing_finite (f := f)
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  haveI : Algebra.IsIntegral (Polynomial k) (lineCoverRing f) := Algebra.IsIntegral.of_finite _ _
  refine (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := Polynomial k) ?_)
  ext p
  simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot,
    lineCoverToFunctionField_algebraMap, coordHom_eq_aeval hη hfk]
  exact ⟨fun h ↦ (transcendental_iff_injective.1 hx) (by rw [h, map_zero]),
    fun h ↦ by rw [h, map_zero]⟩

/-- **The range of `ρ` is the integral closure of `k[x]` in `K(X)`.** -/
theorem mem_range_lineCoverToFunctionField_iff (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (z : X.functionField) :
    z ∈ Set.range (lineCoverToFunctionField f hη) ↔
      IsIntegral (Algebra.adjoin k {coordFun f hη}) z := by
  have hse : ∀ a, (coordHom f hη) a ∈ Algebra.adjoin k {coordFun f hη} := fun a ↦ by
    change (coordHom f hη).hom a ∈ _
    rw [coordHom_eq_aeval hη hfk]
    exact Polynomial.aeval_mem_adjoin_singleton k _
  constructor
  · rintro ⟨b, rfl⟩
    haveI := lineCoverRing_finite (f := f)
    haveI : Algebra.IsIntegral (Polynomial k) (lineCoverRing f) := Algebra.IsIntegral.of_finite _ _
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := Polynomial k) b
    let g : Polynomial k →+* Algebra.adjoin k {coordFun f hη} :=
      (coordHom f hη).hom.codRestrict (Algebra.adjoin k {coordFun f hη}).toSubring hse
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (Algebra.adjoin k {coordFun f hη}) X.functionField).comp g =
        (lineCoverToFunctionField f hη).comp (algebraMap (Polynomial k) (lineCoverRing f)) :=
      RingHom.ext fun p ↦ (lineCoverToFunctionField_algebraMap hη p).symm
    rw [hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  · intro hz
    have hgen := genericPoint_mem_preimage_lineι hη
    haveI : Nonempty (f ⁻¹ᵁ (lineι k).opensRange) := ⟨⟨_, hgen⟩⟩
    obtain ⟨s, hs⟩ := (mem_range_germToFunctionField_iff k (valuationRing_stalk_of_isCurveOver k X)
      f (lineι k) (coordHom f hη) (spec_map_coordHom_comp_lineι hη).symm (coordFun f hη) hse
      ⟨Polynomial.X, rfl⟩ z).2 hz
    exact ⟨_, (lineCoverToFunctionField_appLE hη hgen top_le_preimage_fst_lineι s).trans hs⟩

/-- **`B ≅ A_x`**: the ring of the affine part of `f` is weil-curves' chart ring of `x`. -/
def lineCoverChartEquiv (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    lineCoverRing f ≃+* chartRing k (coordFun f hη) :=
  RingEquiv.ofBijective ((lineCoverToFunctionField f hη).codRestrict
      (chartRing k (coordFun f hη)) fun b ↦ (mem_integralClosure_iff _ _).2
        ((mem_range_lineCoverToFunctionField_iff hη hfk _).1 ⟨b, rfl⟩))
    ⟨fun _ _ h ↦ lineCoverToFunctionField_injective hη hfk (congrArg Subtype.val h),
      fun z ↦ by
        obtain ⟨b, hb⟩ := (mem_range_lineCoverToFunctionField_iff hη hfk _).2
          ((mem_integralClosure_iff _ _).1 z.2)
        exact ⟨b, Subtype.ext hb⟩⟩

lemma lineCoverChartEquiv_apply (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (b : lineCoverRing f) :
    (lineCoverChartEquiv hη hfk b : X.functionField) = lineCoverToFunctionField f hη b :=
  rfl

end Curve

/-- Maximal ideals containing a nonzero element of a Dedekind domain are height-one primes. -/
def maximalSpectrumMemEquivHeightOne {R : Type*} [CommRing R] [IsDedekindDomain R] {r : R}
    (hr : r ≠ 0) :
    {M : MaximalSpectrum R // r ∈ M.asIdeal} ≃
      {v : IsDedekindDomain.HeightOneSpectrum R // r ∈ v.asIdeal} where
  toFun M := ⟨⟨M.1.asIdeal, M.1.isMaximal.isPrime, fun h ↦ hr (by
    have := M.2
    rwa [h, Ideal.mem_bot] at this)⟩, M.2⟩
  invFun v := ⟨⟨v.1.asIdeal, v.1.isMaximal⟩, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Places

variable {k K : Type*} [Field k] [PerfectField k] [Field K] [Algebra k K] [IsFunctionField k K]
  (x : K) [Fact (Transcendental k x)]

/-- `x - a` as an element of the chart ring `A_x`. -/
def chartSub (a : k) : chartRing k x :=
  ⟨x - algebraMap k K a, sub_mem (self_mem_chartRing k x) (algebraMap_mem_chartRing x a)⟩

omit [Fact (Transcendental k x)] in
lemma mem_of_ord_sub_pos {Q : Place k K} {a : k} (h : 0 < Q.ord (x - algebraMap k K a)) :
    x ∈ Q.1 := by
  have hmem : x - algebraMap k K a ∈ Q.1 :=
    (ValuationSubring.valuation_le_one_iff _ _).1
      (le_of_lt ((ValuationSubring.mem_nonunits_iff _).1 ((Place.ord_pos_iff Q).1 h).2))
  simpa using add_mem hmem (Q.algebraMap_mem a)

/-- **Height-one primes of `A_x` containing `x - a` are the zeros of `x - a`.** -/
def heightOneMemEquivPlace (a : k) :
    {v : IsDedekindDomain.HeightOneSpectrum (chartRing k x) // chartSub x a ∈ v.asIdeal} ≃
      {Q : Place k K // 0 < Q.ord (x - algebraMap k K a)} where
  toFun v := ⟨Place.ofChart x v.1, by
    have hne : x - algebraMap k K a ≠ 0 := sub_ne_zero.2 fun h ↦
      (Fact.out : Transcendental k x) (h ▸ isAlgebraic_algebraMap a)
    rw [Place.ord_pos_iff]
    refine ⟨hne, ?_⟩
    have h := v.2
    rw [← Place.toChart_ofChart x v.1, Place.mem_toChart_iff] at h
    exact h⟩
  invFun Q := ⟨Place.toChart x Q.1 (mem_of_ord_sub_pos x Q.2),
    (Place.mem_toChart_iff x Q.1 _).2 ((Place.ord_pos_iff Q.1).1 Q.2).2⟩
  left_inv v := Subtype.ext (Place.toChart_ofChart x v.1)
  right_inv Q := Subtype.ext (Place.ofChart_toChart x Q.1 (mem_of_ord_sub_pos x Q.2))

end Places

section Unramified

open Belyi.Converse

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

/-- **Where `t` is étale, `t - a` is a uniformizer**: if `k[t] → B[P(t)⁻¹]` is étale, `P(a) ≠ 0`
and `M` is a maximal ideal of `B` containing `t - a ≠ 0`, then `t - a ∉ M²`. Otherwise the
two `k[t]`-algebra maps `B[P(t)⁻¹] → B/M²` (the quotient map, and the residue map
`B → B/M = k ⊆ B/M²`) agree modulo the square-zero ideal `M/M²`, so they are equal (formal
unramifiedness), whence `M ⊆ M²` and `M = 0` by Krull's intersection theorem. -/
theorem sub_notMem_sq_of_etale (t : B) (P : MvPolynomial (Fin 1) k)
    (het : ((algebraMap B (Localization.Away
      (MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ t) P))).comp
        (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).toRingHom).Etale)
    {a : k} (ha : MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ a) P ≠ 0)
    (M : Ideal B) [hM : M.IsMaximal] (hmem : t - algebraMap k B a ∈ M)
    (hne : t - algebraMap k B a ≠ 0) : t - algebraMap k B a ∉ M ^ 2 := by
  intro hsq
  set h : B := MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ t) P with hh
  let R₀ := MvPolynomial (Fin 1) k
  let ev : R₀ →ₐ[k] B := MvPolynomial.aeval fun _ : Fin 1 ↦ t
  let A := Localization.Away h
  letI : Algebra R₀ A := ((algebraMap B A).comp ev.toRingHom).toAlgebra
  haveI : Algebra.Etale R₀ A := RingHom.etale_algebraMap.1 het
  let C := B ⧸ M ^ 2
  letI : Algebra R₀ C := ((Ideal.Quotient.mk (M ^ 2)).comp ev.toRingHom).toAlgebra
  let I : Ideal C := M.map (Ideal.Quotient.mk (M ^ 2))
  have hI : I ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  let res : B →ₐ[k] k := pointOfMaximal ⟨M, hM⟩
  have hres_mem : ∀ b, b - algebraMap k B (res b) ∈ M := fun b ↦ by
    change _ ∈ (⟨M, hM⟩ : MaximalSpectrum B).asIdeal
    rw [← ker_pointOfMaximal (K := k) ⟨M, hM⟩, RingHom.mem_ker, map_sub, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hres_ker : ∀ b, b ∈ M → res b = 0 := fun b hb ↦ by
    rw [← RingHom.mem_ker, ker_pointOfMaximal (K := k) ⟨M, hM⟩]
    exact hb
  have hres_t : res t = a := by
    have h0 := hres_ker _ hmem
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h0
    exact h0
  let qB : B →+* C := Ideal.Quotient.mk (M ^ 2)
  let rB : B →+* C := (algebraMap k C).comp res.toRingHom
  have hdiff : ∀ b, qB b - rB b ∈ I := fun b ↦ by
    change Ideal.Quotient.mk (M ^ 2) b - algebraMap k C (res b) ∈ I
    rw [← Ideal.Quotient.mk_algebraMap, ← map_sub]
    exact Ideal.mem_map_of_mem _ (hres_mem b)
  have hres_h : res h = MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ a) P := by
    rw [hh, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp [hres_t]
  have hrB : IsUnit (rB h) := by
    change IsUnit (algebraMap k C (res h))
    rw [hres_h]
    exact (Ne.isUnit ha).map _
  have hqB : IsUnit (qB h) := by
    have hnil : IsNilpotent (qB h - rB h) := ⟨2, by
      have := Ideal.pow_mem_pow (hdiff h) 2
      rwa [hI, Ideal.mem_bot] at this⟩
    have := hnil.isUnit_add_left_of_commute hrB (Commute.all _ _)
    rwa [add_sub_cancel] at this
  let qA : A →+* C := IsLocalization.Away.lift h hqB
  let rA : A →+* C := IsLocalization.Away.lift h hrB
  have hqr : ∀ p : R₀, rB (ev p) = qB (ev p) := by
    intro p
    have e : rB.comp ev.toRingHom = qB.comp ev.toRingHom := by
      refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun i ↦ ?_
      · change algebraMap k C (res (ev (MvPolynomial.C c))) =
          Ideal.Quotient.mk (M ^ 2) (ev (MvPolynomial.C c))
        rw [MvPolynomial.aeval_C, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
          Ideal.Quotient.mk_algebraMap]
      · change algebraMap k C (res (ev (MvPolynomial.X i))) =
          Ideal.Quotient.mk (M ^ 2) (ev (MvPolynomial.X i))
        rw [MvPolynomial.aeval_X, hres_t, ← Ideal.Quotient.mk_algebraMap]
        exact (Ideal.Quotient.eq.2 hsq).symm
    exact congrArg (fun φ : R₀ →+* C ↦ φ p) e
  let qA' : A →ₐ[R₀] C :=
    { qA with commutes' := fun p ↦ IsLocalization.Away.lift_eq h hqB (ev p) }
  let rA' : A →ₐ[R₀] C :=
    { rA with commutes' := fun p ↦ (IsLocalization.Away.lift_eq h hrB (ev p)).trans (hqr p) }
  have hcomp : (Ideal.Quotient.mkₐ R₀ I).comp qA' = (Ideal.Quotient.mkₐ R₀ I).comp rA' := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    ext b
    change Ideal.Quotient.mk I (qA (algebraMap B A b)) = Ideal.Quotient.mk I (rA (algebraMap B A b))
    rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.eq.2 (hdiff b)
  have heq : qA' = rA' := Algebra.FormallyUnramified.comp_injective I hI hcomp
  have hle : M ≤ M ^ 2 := fun b hb ↦ by
    have h1 := congrArg (fun φ : A →ₐ[R₀] C ↦ φ (algebraMap B A b)) heq
    change qA (algebraMap B A b) = rA (algebraMap B A b) at h1
    rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at h1
    change Ideal.Quotient.mk (M ^ 2) b = algebraMap k C (res b) at h1
    rw [hres_ker b hb, map_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  have hpow : ∀ n : ℕ, M ≤ M ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc M ≤ M ^ 2 := hle
        _ = M * M := sq M
        _ ≤ M * M ^ (n + 1) := Ideal.mul_mono_right ih
        _ = M ^ (n + 1 + 1) := (pow_succ' M (n + 1)).symm
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hbot := Ideal.iInf_pow_eq_bot_of_isDomain (I := M) hM.ne_top
  apply hne
  have hin : t - algebraMap k B a ∈ ⨅ i, M ^ i := by
    rw [Submodule.mem_iInf]
    intro i
    cases i with
    | zero => simp
    | succ n => exact hpow n hmem
  rwa [hbot, Ideal.mem_bot] at hin

/-- **Over `a ≠ 0, 1` the coordinate `t - a` is a uniformizer** (`sub_notMem_sq_of_etale` for
`P = X (X - 1)`). -/
theorem branchedData_sub_notMem_sq (D : BranchedData k B) {a : k} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (M : Ideal B) [M.IsMaximal] (hmem : D.t - algebraMap k B a ∈ M)
    (hne : D.t - algebraMap k B a ≠ 0) : D.t - algebraMap k B a ∉ M ^ 2 :=
  sub_notMem_sq_of_etale D.t (branchPolyZeroOne k) D.etale
    (by simpa [branchPolyZeroOne] using mul_ne_zero ha0 (sub_ne_zero.2 ha1)) M hmem hne

end Unramified

section Count

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] {f : X ⟶ P1 k} [IsFinite f]

omit [IsAlgClosed k] [CharZero k] [IsCurveOver k X] [IsFinite f] in
lemma lineCoverToFunctionField_algebraMap_base (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (a : k) :
    lineCoverToFunctionField f hη (algebraMap k (lineCoverRing f) a) =
      algebraMap k X.functionField a := by
  rw [IsScalarTower.algebraMap_apply k (Polynomial k) (lineCoverRing f),
    lineCoverToFunctionField_algebraMap, Polynomial.algebraMap_eq, coordHom_C hη hfk]

omit [IsAlgClosed k] in
lemma lineCoverChartEquiv_sub (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (a : k) :
    haveI : Fact (Transcendental k (coordFun f hη)) :=
      haveI := isDominant_of_isFinite f
      ⟨transcendental_coordFun hη hfk⟩
    lineCoverChartEquiv hη hfk ((lineCoverCoord f).t - algebraMap k (lineCoverRing f) a) =
      chartSub (coordFun f hη) a := by
  apply Subtype.ext
  rw [lineCoverChartEquiv_apply, map_sub, lineCoverToFunctionField_algebraMap_base hη hfk]
  congr 1
  exact lineCoverToFunctionField_t hη

omit [IsAlgClosed k] in
/-- **Fibre counts on `B` are zero counts of `x - a`**: the maximal ideals of
`B = Γ(X ×_{ℙ¹} 𝔸¹)` containing `t - a` correspond to the places `Q` of `K(X)` with
`ord_Q (x - a) > 0`. -/
theorem card_maximalSpectrum_lineCover_eq (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (a : k) :
    Nat.card {M : MaximalSpectrum (lineCoverRing f) //
        (lineCoverCoord f).t - algebraMap k (lineCoverRing f) a ∈ M.asIdeal} =
      Nat.card {Q : Place k X.functionField //
        0 < Q.ord (coordFun f hη - algebraMap k X.functionField a)} := by
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  haveI : Fact (Transcendental k (coordFun f hη)) := ⟨hx⟩
  have hne : chartSub (coordFun f hη) a ≠ 0 := fun h ↦ by
    have h' := congrArg Subtype.val h
    exact (transcendental_sub_algebraMap hx a) (by
      change coordFun f hη - algebraMap k X.functionField a = 0 at h'
      rw [h']
      exact isAlgebraic_zero)
  refine Nat.card_congr ((ComplexAnalytic.maximalSpectrumMemEquiv
    (lineCoverChartEquiv hη hfk) _).trans ?_)
  refine (Equiv.subtypeEquivRight fun M ↦ ?_).trans
    ((maximalSpectrumMemEquivHeightOne hne).trans (heightOneMemEquivPlace _ a))
  rw [lineCoverChartEquiv_sub hη hfk a]

omit [IsAlgClosed k] in
/-- **A criterion for `x` to be unramified over `a`**: if `B ≅ R'` and `t - a ∈ B` corresponds to
`r' ∈ R'` with `r' ∉ M²` for every maximal ideal `M ∋ r'` of `R'` (when `r' ≠ 0`), then
`ord_Q (x - a) ≤ 1` for every place `Q` of `K(X)` (through `B ≅ A_x`). -/
theorem ord_coordFun_sub_le_one_of_ringEquiv (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    {R' : Type*} [CommRing R'] (ψ : R' ≃+* lineCoverRing f) (a : k) (r' : R')
    (hr' : ψ r' = (lineCoverCoord f).t - algebraMap k (lineCoverRing f) a)
    (h : ∀ M : Ideal R', M.IsMaximal → r' ∈ M → r' ≠ 0 → r' ∉ M ^ 2)
    (Q : Place k X.functionField) :
    Q.ord (coordFun f hη - algebraMap k X.functionField a) ≤ 1 := by
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  haveI : Fact (Transcendental k (coordFun f hη)) := ⟨hx⟩
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hpos : 0 < Q.ord (coordFun f hη - algebraMap k X.functionField a) := by omega
  set x := coordFun f hη
  have hxQ := mem_of_ord_sub_pos x hpos
  set v := Place.toChart x Q hxQ
  have hQ : Place.ofChart x v = Q := Place.ofChart_toChart x Q hxQ
  set r := chartSub x a
  have hr0 : r ≠ 0 := fun h ↦ by
    have h' := congrArg Subtype.val h
    exact (transcendental_sub_algebraMap hx a) (by
      change x - algebraMap k X.functionField a = 0 at h'
      rw [h']
      exact isAlgebraic_zero)
  have hord := Place.ord_ofChart_algebraMap x v hr0
  rw [hQ] at hord
  change Q.ord (x - algebraMap k X.functionField a) = _ at hord
  have hmul : 2 ≤ multiplicity v.asIdeal (Ideal.span {r}) := by omega
  have hdvd := pow_dvd_of_le_multiplicity hmul
  rw [Ideal.dvd_iff_le] at hdvd
  have hrv2 : r ∈ v.asIdeal ^ 2 := hdvd (Ideal.mem_span_singleton_self r)
  have hrv : r ∈ v.asIdeal := Ideal.pow_le_self two_ne_zero hrv2
  set φ := ψ.trans (lineCoverChartEquiv hη hfk)
  have hφ : φ.symm r = r' := by
    rw [RingEquiv.symm_apply_eq, RingEquiv.trans_apply, hr', lineCoverChartEquiv_sub hη hfk a]
  let M := v.asIdeal.map φ.symm
  haveI : M.IsMaximal := Ideal.map_isMaximal_of_equiv φ.symm (p := v.asIdeal)
  have hM : r' ∈ M := by
    rw [← hφ]
    exact Ideal.mem_map_of_mem _ hrv
  have hM2 : r' ∈ M ^ 2 := by
    rw [← hφ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hrv2
  have hne : r' ≠ 0 := by
    rw [← hφ]
    exact (map_ne_zero_iff _ φ.symm.injective).2 hr0
  exact h M inferInstance hM hne hM2

/-- **The coordinate is unramified where it is étale**: if `k[t] → B[P(t)⁻¹]` is étale and
`P(a) ≠ 0`, then `ord_Q (x - a) ≤ 1` for every place `Q` of `K(X)`
(`CurvesJacobian.sub_notMem_sq_of_etale` through `B ≅ A_x`). -/
theorem ord_coordFun_sub_le_one_of_etale (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (P : MvPolynomial (Fin 1) k)
    (het : ((algebraMap (lineCoverRing f) (Localization.Away
      (MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ (lineCoverCoord f).t) P))).comp
        (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ (lineCoverCoord f).t).toRingHom).Etale)
    (Q : Place k X.functionField) (a : k)
    (ha : MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ a) P ≠ 0) :
    Q.ord (coordFun f hη - algebraMap k X.functionField a) ≤ 1 := by
  haveI := isDomain_lineCoverRing_of hη
  exact ord_coordFun_sub_le_one_of_ringEquiv hη hfk (RingEquiv.refl _) a _ rfl
    (fun M _ hM hne ↦ sub_notMem_sq_of_etale _ P het ha M hM hne) Q

/-- **The Belyi coordinate is unramified over `a ≠ 0, 1`**: `ord_Q (x - a) ≤ 1` for every place
`Q` of `K(X)` (`CurvesJacobian.branchedData_sub_notMem_sq` through `B ≅ A_x`). -/
theorem ord_coordFun_sub_le_one (hf : IsBelyiMap k f) (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k))
    (Q : Place k X.functionField) (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Q.ord (coordFun f hη - algebraMap k X.functionField a) ≤ 1 :=
  ord_coordFun_sub_le_one_of_etale hη hfk (Converse.branchPolyZeroOne k) hf.branchedData.etale Q a
    (by simpa [Converse.branchPolyZeroOne] using mul_ne_zero ha0 (sub_ne_zero.2 ha1))

omit [IsAlgClosed k] in
/-- **Poles of `x` are the points over `∞`.** -/
theorem card_ord_coordFun_neg (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (D : Set X)
    (hD : ∀ p : X, f.base p = P1.infty k ↔ p ∈ D) (hDgen : ∀ p ∈ D, p ≠ genericPoint X) :
    Nat.card {Q : Place k X.functionField // Q.ord (coordFun f hη) < 0} = Nat.card D := by
  refine Nat.card_congr ((Equiv.subtypeEquiv (curvePlaceEquiv k X).symm fun Q ↦ ?_).trans
    (Equiv.subtypeSubtypeEquivSubtype fun {p} hp ↦ hDgen p hp))
  have hQ : Q.1 = stalkVS k ((curvePlaceEquiv k X).symm Q).1 := by
    conv_lhs => rw [← (curvePlaceEquiv k X).apply_symm_apply Q]
    rfl
  rw [Place.ord_neg_iff, hQ, coordFun_mem_stalkVS_iff hη hfk, not_not, hD]

/-- **Zeros of `x - a` over an unramified value count the degree.** -/
theorem card_ord_sub_pos_eq_finrank {K : Type*} [Field K] [Algebra k K] [IsFunctionField k K]
    {x : K} (hx : Transcendental k x) (a : k)
    (hunr : ∀ Q : Place k K, Q.ord (x - algebraMap k K a) ≤ 1) :
    Nat.card {Q : Place k K // 0 < Q.ord (x - algebraMap k K a)} =
      Module.finrank k⟮x⟯ K := by
  classical
  have hxa := transcendental_sub_algebraMap hx a
  have h := Place.sum_ord_mul_deg_zeros (x - algebraMap k K a) hxa
  rw [adjoin_sub_algebraMap_eq] at h
  set T := (Place.finite_setOf_ord_pos (k := k) (x - algebraMap k K a)).toFinset
  have h1 : ∀ Q ∈ T, Q.ord (x - algebraMap k K a) * (Q.deg : ℤ) = 1 := fun Q hQ ↦ by
    have hpos : 0 < Q.ord (x - algebraMap k K a) := by simpa [T] using hQ
    rw [Place.deg_eq_one, Nat.cast_one, mul_one]
    exact le_antisymm (hunr Q) hpos
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hT : Nat.card {Q : Place k K // 0 < Q.ord (x - algebraMap k K a)} = T.card := by
    rw [← Set.ncard_eq_toFinset_card _ (Place.finite_setOf_ord_pos _)]
    exact Nat.card_coe_set_eq _
  rw [hT]
  exact_mod_cast h

end Count

end

end CurvesJacobian
