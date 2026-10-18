/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverCusps
import CurvesJacobian.Cusp.FillElemOp

/-!
# Decomposition groups of closed points and cuspidal decomposition groups ([AbsTopII] Cor 3.7 (c))

[AbsTopII] Corollary 3.7 (c) (`Topics in Absolute Anabelian Geometry II.txt` l.4767–4769): "The
decomposition groups of the closed points of `X` lying in the complement of `U_X` may be obtained
as the images via `Π_{U_X} ↠ Π` of the cuspidal decomposition groups of `Π_{U_X}` [cf. [Mzk15],
Lemma 4.5, (v)]." The cuspidal decomposition groups are recovered from the cuspidal inertia
groups as their commensurators ([AbsTopI] Lemma 4.5 (vi), `Topics in Absolute Anabelian Geometry
I.txt` l.2840: "Let `I ⊆ Π` be a decomposition group of a cusp. Then `I = C_Π(I ∩ Δ)`").

For a hyperbolic curve `C = (X̄, U)` over a number field `K` with a cusp (`Π_U` of
`CurvesJacobian.Cusp.arithmeticExt`, `F = K(X̄_Ω)^alg ⊇ L₀ = K(X̄)`):

* `CurvesJacobian.Cusp.decompGal P W`: the decomposition group `{σ | σ(W) = W}` of a valuation
  subring `W ⊆ Ω` in `Gal(Ω / P)`;
* `CurvesJacobian.Cusp.arithDecomp C W`: its image in `Π_U` under the arithmetic Galois action
  `Gal(F / L₀) → Π_U` (`arithAction`) — **the decomposition group of the place `W`**. If `W` is
  centred on `U` (on a closed point `x ∈ U`), this is a decomposition group of `x`; if `W` lies over
  a cusp (`IsCuspPlace`), it is a cuspidal decomposition group;
* **`commensurator_arithInertia`** ([AbsTopI] Lemma 4.5 (vi)): for `W` over a cusp, the
  commensurator in `Π_U` of the cuspidal inertia group `arithInertia W` is `arithDecomp W`. So the
  cuspidal decomposition groups are determined by the cuspidal inertia groups
  (`CuspidalExt.cusps`) alone;
* **`exists_map_fillMap_arithDecomp`**: for `U ⊆ U'` (both with a cusp, `(X̄, U')` hyperbolic),
  `Π_U ↠ Π_{U'}` (`fillMap`) maps `arithDecomp_U W` onto `arithDecomp_{U'} W`, up to one change of
  base point independent of `W`;
* **`exists_map_fillMap_commensurator`** ([AbsTopII] Cor 3.7 (c)): hence the image under
  `Π_U ↠ Π_{U'}` of the cuspidal decomposition group `Comm_{Π_U}(I_W)` is the decomposition group
  `arithDecomp_{U'} W` of the closed point of `U' ∖ U` under `W` (when `W` is centred on `U'`).

## Proof of `commensurator_arithInertia`

`Π_U = arithAction(Gal(F / L₀))` (`arithAction_surjective`) and conjugation by `arithAction τ`
moves `arithInertia W` to `arithInertia (τ W)`; so `D_W` normalises `I_W`. Conversely if
`arithAction τ` commensurates `I_W`, then the geometric cuspidal inertia groups of `W` and `τ⁻¹ W`
in `π₁ᵉᵗ(U_Ω)` are commensurable (`geomToPi` is injective), and the geometric terminality argument
(`exists_mem_ker_comap_eq`, which needs `U_Ω` hyperbolic: at least three cusps, or genus `≥ 1`
via `exists_cuspSep`) gives `n ∈ Gal(F / K(X̄_Ω))` acting trivially on `π₁ᵉᵗ(U_Ω)` with
`n(W) = τ⁻¹ W`; then `τ ∘ n ∈ D_W` has the same image as `τ`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve
open scoped TensorProduct

universe u

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-! ### Decomposition groups of valuation subrings -/

section DecompGal

variable {Ω : Type u} [Field Ω] (P : Type u) [Field P] [Algebra P Ω]

/-- **The decomposition group** `D_W = {σ | σ(W) = W}` of a valuation subring `W ⊆ Ω` in
`Gal(Ω / P)`. -/
def decompGal (W : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[P] Ω) where
  carrier := {σ | ∀ x, σ x ∈ W ↔ x ∈ W}
  one_mem' := fun _ ↦ Iff.rfl
  mul_mem' := fun {σ τ} hσ hτ x ↦ (hσ (τ x)).trans (hτ x)
  inv_mem' := fun {σ} hσ x ↦ by
    have := hσ (σ⁻¹ x)
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at this
    rw [AlgEquiv.aut_inv]
    exact this.symm

variable {P}

lemma mem_decompGal {W : ValuationSubring Ω} {σ : Ω ≃ₐ[P] Ω} :
    σ ∈ decompGal P W ↔ ∀ x, σ x ∈ W ↔ x ∈ W := Iff.rfl

/-- `σ ∈ D_W` iff `σ⁻¹(W) = W`. -/
lemma mem_decompGal_iff_comap {W : ValuationSubring Ω} {σ : Ω ≃ₐ[P] Ω} :
    σ ∈ decompGal P W ↔ W.comap (σ : Ω →+* Ω) = W := by
  rw [mem_decompGal, SetLike.ext_iff]
  exact Iff.rfl

/-- `σ ∈ D_W` iff `σ(W) = W` in the form `W.comap σ⁻¹ = W`. -/
lemma comap_symm_eq_of_mem_decompGal {W : ValuationSubring Ω} {σ : Ω ≃ₐ[P] Ω}
    (hσ : σ ∈ decompGal P W) : W.comap (σ.symm : Ω →+* Ω) = W := by
  have := mem_decompGal_iff_comap.1 (inv_mem hσ)
  rwa [AlgEquiv.aut_inv] at this

end DecompGal

/-! ### Galois actions along an equality of geometric points -/

section EqToIso

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (F : Type u) [Field F]
  [Algebra F Ω] [IsGalois F Ω] (j : Spec (.of F) ⟶ X)

lemma galoisAction_eqToIso_symm {η η' : Spec (.of Ω) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η) (e : η' = η) (g : Ω ≃ₐ[F] Ω) :
    galoisAction F j (h.trans e.symm) g =
      autContinuousMulEquivOfIso (eqToIso (congrArg fiber e)).symm (galoisAction F j h g) := by
  subst e
  change _ = Iso.conjAut _ _
  simp [Iso.conjAut_apply]

end EqToIso

/-! ### Arithmetic decomposition groups and the commensurator of cuspidal inertia -/

section Arith

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **The decomposition group of the place `W` in `Π_U`**: the image of `D_W ⊆ Gal(F / L₀)` under
the arithmetic Galois action `Gal(K(X̄_Ω)^alg / K(X̄)) → Π_U`. -/
def arithDecomp (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  (decompGal (arithFF Ω C hc) W).map (arithAction Ω C hc)

/-- **Conjugating by the arithmetic Galois action moves the place.** -/
lemma arithInertia_comap (W : ValuationSubring (FFClosure (geomCurve Ω C)))
    (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    arithInertia Ω C hc (W.comap (τ.symm : FFClosure (geomCurve Ω C) →+*
        FFClosure (geomCurve Ω C))) =
      (arithInertia Ω C hc W).map (MulAut.conj (arithAction Ω C hc τ)).toMonoidHom := by
  rw [arithInertia, arithInertia, MonoidHom.map_closure, Set.image_image]
  congr 1
  ext γ
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    refine ⟨τ⁻¹ * ρ * τ, (GaloisPi1.mem_inertia_comap_iff τ ρ).1 hρ, ?_⟩
    simp [map_mul, mul_assoc]
  · rintro ⟨ρ, hρ, rfl⟩
    refine ⟨τ * ρ * τ⁻¹, (GaloisPi1.mem_inertia_comap_iff τ _).2 (by simpa [mul_assoc] using hρ),
      ?_⟩
    simp [map_mul]

/-- The geometric form of `arithInertia` for places over a cusp. -/
lemma arithInertia_eq_map_geom {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W) :
    arithInertia Ω C hc W = (geomCuspInertia Ω C W).map (geomToPi Ω C hc) :=
  (map_geomCuspInertia Ω C hc hW).symm

/-- **The decomposition group of a cusp normalises its inertia group.** -/
lemma arithDecomp_le_commensurator (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    arithDecomp Ω C hc W ≤
      Subgroup.Commensurable.commensurator (arithInertia Ω C hc W) := by
  rintro _ ⟨σ, hσ, rfl⟩
  rw [Subgroup.Commensurable.commensurator_mem_iff, conjAct_smul_eq_map,
    ← arithInertia_comap, comap_symm_eq_of_mem_decompGal hσ]

/-- **The commensurator of a cuspidal inertia group of `Π_U` is the cuspidal decomposition group**
([AbsTopI] Lemma 4.5 (vi), `Topics in Absolute Anabelian Geometry I.txt` l.2840:
`I = C_Π(I ∩ Δ)` for a decomposition group `I` of a cusp). -/
theorem commensurator_arithInertia {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) :
    Subgroup.Commensurable.commensurator (arithInertia Ω C hc W) = arithDecomp Ω C hc W := by
  refine le_antisymm (fun γ hγ ↦ ?_) (arithDecomp_le_commensurator Ω C hc W)
  obtain ⟨τ, rfl⟩ := arithAction_surjective Ω C hc γ
  rw [Subgroup.Commensurable.commensurator_mem_iff, conjAct_smul_eq_map,
    ← arithInertia_comap] at hγ
  set W' := W.comap (τ.symm : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C)) with hW'def
  have hW' : IsCuspPlace Ω C hc W' := isCuspPlace_comap Ω C hc τ.symm hW
  rw [arithInertia_eq_map_geom Ω C hc hW.1, arithInertia_eq_map_geom Ω C hc hW'.1] at hγ
  have hinj := geomToPi_injective Ω C hc
  have hcomm : (geomCuspInertia Ω C W).relIndex (geomCuspInertia Ω C W') ≠ 0 := by
    have := hγ.2
    rwa [Subgroup.relIndex_map_map_of_injective _ _ hinj] at this
  have hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W :=
    fun h ↦ hW.2 ((isCentredOn_geomOpen_iff Ω C hc W).1 h).2
  have hW'U : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W' :=
    fun h ↦ hW'.2 ((isCentredOn_geomOpen_iff Ω C hc W').1 h).2
  have hfin := compl_finite_baseChangeOpen K Ω C.nonempty
  have hhyp : 2 < 2 * (curveGenus Ω (geomCurve Ω C)).toNat +
      Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)) :=
    isHyperbolic_baseChange Ω C
  have hU3 : 2 < Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)) ∨
      ∃ O₀ : Subgroup (geomData Ω C).H, O₀.Normal ∧ IsOpen (O₀ : Set (geomData Ω C).H) ∧
        ((geomData Ω C).chartHom (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C))
          (genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
            (geomOpen Ω C))).ker ≤ O₀ ∧ CuspSep (geomData Ω C) O₀ W := by
    by_cases h3 : 2 < Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C))
    · exact Or.inl h3
    · exact Or.inr (exists_cuspSep (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
        (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (by omega) hfin hW.1 hWU)
  obtain ⟨n, hn, hnW⟩ := exists_mem_ker_comap_eq (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) hfin hU3 hW.1 hW'.1 hWU hW'U hcomm
  -- `σ₀ = τ⁻¹ ∘ n` fixes `W`
  have hσ₀ : τ⁻¹ * toArithAut Ω C hc n ∈ decompGal (arithFF Ω C hc) W := by
    intro x
    have := SetLike.ext_iff.1 hnW x
    rw [hW'def, ValuationSubring.mem_comap, ValuationSubring.mem_comap] at this
    rw [← this, AlgEquiv.aut_inv]
    rfl
  have hn1 : arithAction Ω C hc (toArithAut Ω C hc n) = 1 := by
    rw [← geomToPi_chartHom]
    erw [(MonoidHom.mem_ker).1 hn]
    exact map_one _
  refine ⟨(τ⁻¹ * toArithAut Ω C hc n)⁻¹, inv_mem hσ₀, ?_⟩
  rw [map_inv, map_mul, hn1, mul_one, map_inv, inv_inv]

end Arith

/-! ### Decomposition groups along `Π_U ↠ Π_{U'}` -/

section Fill

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens} (h : C.U ≤ U')
  (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
  (hyp : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U')

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The function field embeddings of `(X̄, U)` and `(X̄, U')` agree. -/
lemma ffEmb_fillCurve_apply (y : C.Xbar.functionField) :
    ffEmb Ω (fillCurve C h hyp) hc' y = ffEmb Ω C hc y := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  haveI : Nonempty U' := (C.nonempty.mono h).to_subtype
  haveI := nonempty_fillOpen Ω C h
  haveI : IsFractionRing Γ(C.Xbar, U') C.Xbar.functionField :=
    functionField_isFractionRing_of_isAffineOpen C.Xbar U' (isAffineOpen_of_le C h hc')
  have key : ∀ a : Γ(C.Xbar, U'), ffEmb Ω (fillCurve C h hyp) hc'
      (algebraMap Γ(C.Xbar, U') C.Xbar.functionField a) =
        ffEmb Ω C hc (algebraMap Γ(C.Xbar, U') C.Xbar.functionField a) := fun a ↦ by
    have e1 : ffEmb Ω (fillCurve C h hyp) hc' (C.Xbar.germToFunctionField U' a) =
        secEmb Ω C (isAffineOpen_of_le C h hc') a := ffEmb_germ Ω (fillCurve C h hyp) hc' a
    have e2 : ffEmb Ω C hc (C.Xbar.germToFunctionField U' a) =
        secEmb Ω C (isAffineOpen_of_le C h hc') a := by
      rw [← germ_resAlg C h a, ffEmb_germ, secEmb_resAlg Ω C hc h hc']
    exact e1.trans e2.symm
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(C.Xbar, U')) y
  rw [map_div₀, map_div₀, key a, key b]

lemma mem_arithFF_fillCurve (y : FFClosure (geomCurve Ω C)) :
    y ∈ arithFF Ω (fillCurve C h hyp) hc' ↔ y ∈ arithFF Ω C hc := by
  simp only [arithFF, RingHom.mem_fieldRange]
  exact ⟨fun ⟨z, hz⟩ ↦ ⟨z, (ffEmb_fillCurve_apply Ω C hc h hc' hyp z).symm.trans hz⟩,
    fun ⟨z, hz⟩ ↦ ⟨z, (ffEmb_fillCurve_apply Ω C hc h hc' hyp z).trans hz⟩⟩

/-- An automorphism over `L₀ = K(X̄)` (for `U`) as an automorphism over `L₀` (for `U'`). -/
def castFill (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    FFClosure (geomCurve Ω (fillCurve C h hyp)) ≃ₐ[arithFF Ω (fillCurve C h hyp) hc']
      FFClosure (geomCurve Ω (fillCurve C h hyp)) :=
  AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x ↦
    τ.commutes ⟨x.1, (mem_arithFF_fillCurve Ω C hc h hc' hyp x.1).1 x.2⟩

lemma castFill_surjective : Function.Surjective (castFill Ω C hc h hc' hyp) := fun τ' ↦
  ⟨AlgEquiv.ofRingEquiv (f := τ'.toRingEquiv) fun x ↦
    τ'.commutes ⟨x.1, (mem_arithFF_fillCurve Ω C hc h hc' hyp x.1).2 x.2⟩,
    AlgEquiv.ext fun _ ↦ rfl⟩

/-- The generic geometric point of `Spec Γ(U')` obtained through `Spec Γ(U)`. -/
abbrev fillGen : Spec (.of (FFClosure (geomCurve Ω C))) ⟶ Spec (.of Γ(C.Xbar, U')) :=
  ((specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫ genOpen Ω C C.U) ≫
    geomToSpec Ω C hc) ≫ Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)

lemma fillGen_spec : Spec.map (CommRingCat.ofHom (algebraMap (arithFF Ω C hc)
      (FFClosure (geomCurve Ω C)))) ≫ (arithGenPt Ω C hc ≫
        Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) = fillGen Ω C hc h := by
  rw [← Category.assoc, specMap_algebraMap_arithGenPt]

/-- The two generic geometric points of `Spec Γ(U')` (through `U` and directly) agree. -/
lemma fillGen_eq :
    (specPoint (geomData Ω (fillCurve C h hyp)).L (FFClosure (geomCurve Ω (fillCurve C h hyp))) ≫
        genOpen Ω (fillCurve C h hyp) (fillCurve C h hyp).U) ≫
          geomToSpec Ω (fillCurve C h hyp) hc' = fillGen Ω C hc h := by
  haveI := nonempty_fillOpen Ω C h
  rw [← specMap_algebraMap_arithGenPt Ω (fillCurve C h hyp) hc', ← fillGen_spec Ω C hc h]
  simp only [arithGenPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  change secEmb Ω (fillCurve C h hyp) (isAffineOpen_U (fillCurve C h hyp) hc') a =
    secEmb Ω C (isAffineOpen_U C hc) (resAlg K h a)
  rw [secEmb_resAlg Ω C hc h hc']
  rfl

/-- `fillMap ∘ arithAction` is a Galois action at `fillGen`, moved to the base point. -/
lemma fillMap_arithAction
    (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    fillMap Ω C hc h (arithAction Ω C hc τ) =
      autContinuousMulEquivOfIso (fiberIsoMap (Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom))
        rfl (fillPoint_spec Ω C hc h) (arithFiberIso Ω C hc))
        (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc ≫
          Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (fillGen_spec Ω C hc h) τ) := by
  change fundamentalGroupMap _ (fillPoint_spec Ω C hc h)
    (autContinuousMulEquivOfIso (arithFiberIso Ω C hc) (galoisAction (arithFF Ω C hc)
      (arithGenPt Ω C hc) (specMap_algebraMap_arithGenPt Ω C hc) τ)) = _
  rw [fundamentalGroupMap_autContinuousMulEquivOfIso _ rfl (fillPoint_spec Ω C hc h),
    fundamentalGroupMap_galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc) _
      (specMap_algebraMap_arithGenPt Ω C hc) rfl (fillGen_spec Ω C hc h)]

/-- The change of base point from `fillGen` to the base point of `(X̄, U')`. -/
def fillGenIso : fiber (fillGen Ω C hc h) ≅ fiber (basePoint Ω (fillCurve C h hyp) hc' ≫
    baseChangeSpec K Ω Γ(C.Xbar, U')) :=
  (eqToIso (congrArg fiber (fillGen_eq Ω C hc h hc' hyp))).symm ≪≫
    arithFiberIso Ω (fillCurve C h hyp) hc'

/-- The arithmetic Galois action of `(X̄, U')`, as a Galois action at `fillGen`. -/
lemma arithAction_fillCurve
    (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    arithAction Ω (fillCurve C h hyp) hc' (castFill Ω C hc h hc' hyp τ) =
      autContinuousMulEquivOfIso (fillGenIso Ω C hc h hc' hyp)
        (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc ≫
          Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (fillGen_spec Ω C hc h) τ) := by
  have e := fillGen_eq Ω C hc h hc' hyp
  have key : galoisAction (arithFF Ω (fillCurve C h hyp) hc') (arithGenPt Ω (fillCurve C h hyp) hc')
      (specMap_algebraMap_arithGenPt Ω (fillCurve C h hyp) hc') (castFill Ω C hc h hc' hyp τ) =
      autContinuousMulEquivOfIso (eqToIso (congrArg fiber e)).symm
        (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc ≫
          Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (fillGen_spec Ω C hc h) τ) := by
    have h' := (specMap_algebraMap_arithGenPt Ω (fillCurve C h hyp) hc').trans e
    letI : Algebra (arithFF Ω (fillCurve C h hyp) hc') (FFClosure (geomCurve Ω C)) :=
      inferInstanceAs (Algebra (arithFF Ω (fillCurve C h hyp) hc')
        (FFClosure (geomCurve Ω (fillCurve C h hyp))))
    haveI : IsGalois (arithFF Ω (fillCurve C h hyp) hc') (FFClosure (geomCurve Ω C)) :=
      inferInstanceAs (IsGalois (arithFF Ω (fillCurve C h hyp) hc')
        (FFClosure (geomCurve Ω (fillCurve C h hyp))))
    have k1 := galoisAction_eq_of_apply_eq (arithFF Ω C hc) (arithGenPt Ω C hc ≫
      Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (arithGenPt Ω (fillCurve C h hyp) hc')
      (fillGen_spec Ω C hc h) h' τ (castFill Ω C hc h hc' hyp τ) fun _ ↦ rfl
    rw [k1]
    exact galoisAction_eqToIso_symm (arithFF Ω (fillCurve C h hyp) hc')
      (arithGenPt Ω (fillCurve C h hyp) hc') h' e (castFill Ω C hc h hc' hyp τ)
  change autContinuousMulEquivOfIso (arithFiberIso Ω (fillCurve C h hyp) hc')
    (galoisAction (arithFF Ω (fillCurve C h hyp) hc') (arithGenPt Ω (fillCurve C h hyp) hc')
      (specMap_algebraMap_arithGenPt Ω (fillCurve C h hyp) hc') (castFill Ω C hc h hc' hyp τ)) = _
  rw [key, fillGenIso]
  exact (Iso.trans_conjAut _ _ _).symm

/-- `fillMap (D_W(U))`, as the image of `D_W` under the Galois action at `fillGen`. -/
lemma map_fillMap_arithDecomp (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    (arithDecomp Ω C hc W).map (fillMap Ω C hc h).toMonoidHom =
      ((decompGal (arithFF Ω C hc) W).map (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc ≫
          Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (fillGen_spec Ω C hc h))).map
        (autContinuousMulEquivOfIso (fiberIsoMap (Spec.map (CommRingCat.ofHom
          (resAlg K h).toRingHom)) rfl (fillPoint_spec Ω C hc h)
            (arithFiberIso Ω C hc))).toMulEquiv.toMonoidHom := by
  rw [arithDecomp, Subgroup.map_map, Subgroup.map_map]
  exact congrArg (fun φ ↦ Subgroup.map φ _) (MonoidHom.ext fun τ ↦ fillMap_arithAction Ω C hc h τ)

/-- `D_W(U')`, moved to `fillPoint`, as the image of `D_W` under the Galois action at
`fillGen`. -/
lemma map_arithDecomp_fillCurve (α₀ : fiber (basePoint Ω (fillCurve C h hyp) hc') ≅
      fiber (fillPoint Ω C hc h)) (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    (arithDecomp Ω (fillCurve C h hyp) hc' W).map (autContinuousMulEquivOfIso
      (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)).toMulEquiv.toMonoidHom =
      ((decompGal (arithFF Ω C hc) W).map (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc ≫
          Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (fillGen_spec Ω C hc h))).map
        (autContinuousMulEquivOfIso (fillGenIso Ω C hc h hc' hyp ≪≫
          fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)).toMulEquiv.toMonoidHom := by
  have key : ∀ τ, autContinuousMulEquivOfIso
      (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)
        (arithAction Ω (fillCurve C h hyp) hc' (castFill Ω C hc h hc' hyp τ)) =
      autContinuousMulEquivOfIso (fillGenIso Ω C hc h hc' hyp ≪≫
          fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)
        (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc ≫
          Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) (fillGen_spec Ω C hc h) τ) :=
    fun τ ↦ by
      rw [arithAction_fillCurve]
      exact (Iso.trans_conjAut _ _ _).symm
  ext y
  simp only [arithDecomp, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨τ', hτ', rfl⟩, rfl⟩
    obtain ⟨τ, rfl⟩ := castFill_surjective Ω C hc h hc' hyp τ'
    exact ⟨_, ⟨τ, fun x ↦ hτ' x, rfl⟩, (key τ).symm⟩
  · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    exact ⟨_, ⟨castFill Ω C hc h hc' hyp τ, fun x ↦ hτ x, rfl⟩, key τ⟩

/-- **Decomposition groups along `Π_U ↠ Π_{U'}`**: for any change of base point `α₀` from the base
point of `(X̄, U')` to `fillPoint`, there is `t ∈ Π_{U'}` such that for every place `W`,
`fillMap (D_W(U)) = t · α₀(D_W(U')) · t⁻¹`. -/
theorem exists_map_fillMap_arithDecomp
    (α₀ : fiber (basePoint Ω (fillCurve C h hyp) hc') ≅ fiber (fillPoint Ω C hc h)) :
    ∃ t, ∀ W : ValuationSubring (FFClosure (geomCurve Ω C)),
      (arithDecomp Ω C hc W).map (fillMap Ω C hc h).toMonoidHom =
        ((arithDecomp Ω (fillCurve C h hyp) hc' W).map (autContinuousMulEquivOfIso
          (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)).toMulEquiv.toMonoidHom).map
            (MulAut.conj t).toMonoidHom := by
  obtain ⟨t, ht⟩ := exists_map_autIso_eq_conj (fillGenIso Ω C hc h hc' hyp ≪≫
    fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)
    (fiberIsoMap (Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) rfl
      (fillPoint_spec Ω C hc h) (arithFiberIso Ω C hc))
  exact ⟨t, fun W ↦ by
    rw [map_fillMap_arithDecomp, map_arithDecomp_fillCurve Ω C hc h hc' hyp α₀]
    exact ht _⟩

include hyp in
/-- **[AbsTopII] Corollary 3.7 (c)** (`Topics in Absolute Anabelian Geometry II.txt`
l.4767–4769): the decomposition groups of the closed points of `U' ∖ U` are the images under
`Π_U ↠ Π_{U'}` of the cuspidal decomposition groups `Comm_{Π_U}(I)` of `Π_U` (`I` a cuspidal
inertia group, i.e. an element of `(arithmeticExt Ω C hc).cusps`; [AbsTopI] Lemma 4.5 (vi)).
Precisely: up to one change of base point `t` (independent of the cusp), for every place `W` of
`K(X̄_Ω)^alg` over a cusp of `U`, `fillMap (Comm_{Π_U}(I_W))` is the decomposition group
`D_W(U')` of `W` in `Π_{U'}`; if `W` is centred on `U'` (i.e. lies over a closed point
`x ∈ U' ∖ U`), this is a decomposition group of the closed point `x`. -/
theorem exists_map_fillMap_commensurator
    (α₀ : fiber (basePoint Ω (fillCurve C h hyp) hc') ≅ fiber (fillPoint Ω C hc h)) :
    ∃ t, ∀ W : ValuationSubring (FFClosure (geomCurve Ω C)), IsCuspPlace Ω C hc W →
      (Subgroup.Commensurable.commensurator (arithInertia Ω C hc W)).map
          (fillMap Ω C hc h).toMonoidHom =
        ((arithDecomp Ω (fillCurve C h hyp) hc' W).map (autContinuousMulEquivOfIso
          (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)).toMulEquiv.toMonoidHom).map
            (MulAut.conj t).toMonoidHom := by
  obtain ⟨t, ht⟩ := exists_map_fillMap_arithDecomp Ω C hc h hc' hyp α₀
  exact ⟨t, fun W hW ↦ by rw [commensurator_arithInertia Ω C hc hW, ht W]⟩

include hyp in
/-- **[AbsTopII] Corollary 3.7 (c)**, group-theoretic form: every cuspidal inertia group `I` of
`Π_U` (`I ∈ CuspidalExt.cusps`) is `I_W` for a place `W` over a cusp, and the image of its
commensurator (the cuspidal decomposition group) under `Π_U ↠ Π_{U'}` is the decomposition group of
`W` in `Π_{U'}`, up to one change of base point independent of `I`. -/
theorem exists_map_fillMap_commensurator_cusps
    (α₀ : fiber (basePoint Ω (fillCurve C h hyp) hc') ≅ fiber (fillPoint Ω C hc h)) :
    ∃ t, ∀ I ∈ (arithmeticExt Ω C hc).cusps, ∃ W, IsCuspPlace Ω C hc W ∧
      I = arithInertia Ω C hc W ∧
      (Subgroup.Commensurable.commensurator I).map (fillMap Ω C hc h).toMonoidHom =
        ((arithDecomp Ω (fillCurve C h hyp) hc' W).map (autContinuousMulEquivOfIso
          (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U')) rfl rfl α₀)).toMulEquiv.toMonoidHom).map
            (MulAut.conj t).toMonoidHom := by
  obtain ⟨t, ht⟩ := exists_map_fillMap_commensurator Ω C hc h hc' hyp α₀
  refine ⟨t, fun I hI ↦ ?_⟩
  obtain ⟨W, hW, rfl⟩ := (mem_arithCusps_iff Ω C hc).1 hI
  exact ⟨W, hW, rfl, ht W hW⟩

end Fill

end CurvesJacobian.Cusp
