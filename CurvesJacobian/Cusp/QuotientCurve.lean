/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverInstance
import CurvesJacobian.Cusp.GaloisQuotient
import CurvesJacobian.Cusp.InvariantLine
import CurvesJacobian.Cusp.P1Curve
import CurvesJacobian.Cusp.FillSeq
import Belyi.Converse.PuncturedLine

/-!
# The quotient of an affine curve by a finite group, as a hyperbolic curve (MR8 option (Q))

Let `K` be a number field, `R` a `K`-domain, `t ∈ R` transcendental over `K` with
`K[X] → R`, `X ↦ t`, finite (`CurvesJacobian.Cusp.lineHom`), `ρ : G →* Aut_K(R)` an injective
action of a finite group fixing `t`, and `h ≠ 0` in `K[X]` with `K[X]_h → R_h` étale
(`CurvesJacobian.Cusp.exists_etale_away`). Put `h' = X (X - 1) h`
(`CurvesJacobian.Cusp.quotLinePoly`).

* `CurvesJacobian.Cusp.lineCurve`: the hyperbolic curve `(ℙ¹_K, D(h'))`, `D(h') ⊆ 𝔸¹ ⊆ ℙ¹`
  (the image of the open immersion
  `CurvesJacobian.Cusp.quotLineι : Spec K[X]_{h'} ⟶ ℙ¹`); it lies in
  `ℙ¹ ∖ {0, 1, ∞}` (`quotLineι_opensRange_le`), so it has at least three cusps and is hyperbolic;
  `lineCurve_cusp`: `∞` is a cusp. `CurvesJacobian.Cusp.lineCurveIso`:
  `Spec K[X]_{h'} ≅ Spec Γ(ℙ¹, D(h'))`, compatible with the structure maps to `Spec K`
  (`lineCurveIso_hom_structure`).
* `CurvesJacobian.Cusp.etale_finite_awayMap_of_dvd`: `K[X]_{h₁} → R_{h₁}` is étale and finite for
  every multiple `h₁` of `h` (the basic open `D(h₁) ⊆ Spec R` lies in the étale locus).
* `CurvesJacobian.Cusp.quotLineCover`: the finite étale (`isFiniteEtale_lineCover`) cover
  `Spec R_{h'} ⟶ Spec Γ(ℙ¹, D(h'))`, `Spec R_{h'}` connected (`connectedSpace_coverRing`), and
  `CurvesJacobian.Cusp.coverAut : G →* Aut (coverObj (quotLineCover …))`, `g ↦ Spec (ρ g⁻¹)`,
  injective (`coverAut_injective`).
* The quotient `W = (qObj ρ').left` (`CurvesJacobian.Cusp.lineQuot`) is connected
  (`connectedSpace_lineQuot`) and finite étale over `Spec Γ(ℙ¹, D(h'))`, the quotient map
  `Spec R_{h'} ⟶ W` is finite étale (`isFiniteEtale_lineQuotMap`), and
  `CurvesJacobian.Cusp.lineQuotCurve`: the hyperbolic curve `Z₀ = coverCurve (W ⟶ U)` over the
  constant field of `W` (with a cusp, `lineQuotCurve_cusp`, and `Spec Γ(Z₀) ≅ W`,
  `lineQuotCurveIso`).
* In `π₁ᵉᵗ` of `Spec Γ(ℙ¹, D(h'))`: `π₁ᵉᵗ(Spec R_{h'}) ≤ π₁ᵉᵗ(W)`
  (`coverSubgroup_le_lineQuot`), normal (`normal_coverSubgroup_lineQuot`), with quotient `≃* G`
  (`lineQuotEquiv`) (`CurvesJacobian.Cusp.coverSubgroupQuotEquiv`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Polynomial

open scoped Belyi.P1

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-- A localisation of a domain away from a nonzero element is a domain. -/
lemma isDomain_away_of_ne_zero {A : Type*} [CommRing A] [IsDomain A] {a : A} (ha : a ≠ 0) :
    IsDomain (Localization.Away a) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)

/-- `Spec` of a localisation of a domain away from a nonzero element is connected. -/
lemma connectedSpace_spec_away {A : Type u} [CommRing A] [IsDomain A] {a : A} (ha : a ≠ 0) :
    ConnectedSpace (Spec (.of (Localization.Away a))) :=
  haveI := isDomain_away_of_ne_zero ha
  @IrreducibleSpace.connectedSpace _ _ (PrimeSpectrum.irreducibleSpace (R := Localization.Away a))

/-! ### The punctured line `D(h') ⊆ 𝔸¹ ⊆ ℙ¹` -/

section Line

variable (K : Type u) [Field K]

/-- `h' = X (X - 1) q`: the open `D(h') ⊆ 𝔸¹` misses `0`, `1` (and `∞`). -/
noncomputable abbrev quotLinePoly (q : K[X]) : K[X] := puncturedPoly K * q

lemma quotLinePoly_ne_zero {q : K[X]} (hq : q ≠ 0) : quotLinePoly K q ≠ 0 :=
  mul_ne_zero (mul_ne_zero X_ne_zero (by simpa using X_sub_C_ne_zero (1 : K))) hq

/-- The ring map from the chart ring of `D₊(X₁)` (`≅ K[X]`) to `K[X]_p`. -/
noncomputable def lineChartMap (p : K[X]) :
    HomogeneousLocalization.Away (P1Grading K) (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) →+*
      Localization.Away p :=
  (algebraMap K[X] (Localization.Away p)).comp (P1.awayChartEquivOne K).toRingEquiv.toRingHom

lemma isLocalization_lineChartMap (p : K[X]) :
    letI := (lineChartMap K p).toAlgebra
    IsLocalization.Away ((P1.awayChartEquivOne K).toRingEquiv.symm p) (Localization.Away p) := by
  have h := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers p)
    (Localization.Away p) (P1.awayChartEquivOne K).toRingEquiv.symm
  rw [Submonoid.map_powers] at h
  exact h

/-- The open immersion `Spec K[X]_p ⟶ ℙ¹_K` onto `D(p) ⊆ D₊(X₁) = 𝔸¹`. -/
noncomputable def quotLineι (p : K[X]) : Spec (.of (Localization.Away p)) ⟶ P1 K :=
  Spec.map (CommRingCat.ofHom (lineChartMap K p)) ≫
    Proj.awayι (P1Grading K) (MvPolynomial.X 1) (P1.X_mem_P1Grading K 1) one_pos

instance (p : K[X]) : IsOpenImmersion (quotLineι K p) := by
  letI := (lineChartMap K p).toAlgebra
  haveI := isLocalization_lineChartMap K p
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (lineChartMap K p))) :=
    IsOpenImmersion.of_isLocalization ((P1.awayChartEquivOne K).toRingEquiv.symm p)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (lineChartMap K p)) ≫
    Proj.awayι (P1Grading K) (MvPolynomial.X 1) (P1.X_mem_P1Grading K 1) one_pos)
  infer_instance

/-- `Spec K[X]_p ⟶ ℙ¹ ⟶ Spec K` is `Spec` of the `K`-algebra structure of `K[X]_p`. -/
@[reassoc]
lemma quotLineι_structMap (p : K[X]) :
    quotLineι K p ≫ (P1 K ↘ Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away p))) := by
  change Spec.map (CommRingCat.ofHom (lineChartMap K p)) ≫
      (Proj.awayι (P1Grading K) (MvPolynomial.X 1) (P1.X_mem_P1Grading K 1) one_pos ≫
        P1.structMap K) = _
  rw [P1.awayι_comp_structMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  change algebraMap K[X] (Localization.Away p)
    (P1.awayChartEquivOne K (P1.chartAlgHom K 1 c)) = _
  rw [show P1.chartAlgHom K 1 c = algebraMap K _ c from rfl, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

lemma lineChartMap_quotLinePoly (q : K[X]) :
    lineChartMap K (quotLinePoly K q) =
      (IsLocalization.Away.awayToAwayRight (S := puncturedRing K) (puncturedPoly K) q
        (P := Localization.Away (quotLinePoly K q))).comp (puncturedChartMap K) :=
  RingHom.ext fun _ ↦ (IsLocalization.Away.awayToAwayRight_eq (S := puncturedRing K)
    (puncturedPoly K) q _).symm

/-- `Spec K[X]_{h'} ⟶ ℙ¹` factors through the thrice-punctured line `Spec K[X]_{X(X-1)}`. -/
lemma quotLineι_quotLinePoly (q : K[X]) :
    quotLineι K (quotLinePoly K q) = Spec.map (CommRingCat.ofHom
      (IsLocalization.Away.awayToAwayRight (S := puncturedRing K) (puncturedPoly K) q
        (P := Localization.Away (quotLinePoly K q)))) ≫ puncturedι K := by
  rw [quotLineι, lineChartMap_quotLinePoly, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

/-- **`D(h') ⊆ ℙ¹ ∖ {0, 1, ∞}`.** -/
lemma quotLineι_opensRange_le (q : K[X]) :
    (quotLineι K (quotLinePoly K q)).opensRange ≤ puncturedLine K := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  rw [← opensRange_puncturedι]
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.awayToAwayRight (S := puncturedRing K) (puncturedPoly K) q
      (P := Localization.Away (quotLinePoly K q)))) y, ?_⟩
  rw [quotLineι_quotLinePoly]
  rfl

lemma quotLineι_opensRange_nonempty {q : K[X]} (hq : q ≠ 0) :
    ((quotLineι K (quotLinePoly K q)).opensRange : Set (P1 K)).Nonempty := by
  haveI := isDomain_away_of_ne_zero (quotLinePoly_ne_zero K hq)
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum (Localization.Away (quotLinePoly K q))) := inferInstance
  exact ⟨_, y, rfl⟩

variable [CharZero K]

/-- **The punctured line `(ℙ¹_K, D(h'))`**, `h' = X (X - 1) q`, as a hyperbolic curve: it is
contained in `ℙ¹ ∖ {0, 1, ∞}`, hence has cusp degree `≥ 3`. -/
noncomputable def lineCurve (q : K[X]) (hq : q ≠ 0) : HypCurve K where
  Xbar := P1 K
  U := (quotLineι K (quotLinePoly K q)).opensRange
  nonempty := quotLineι_opensRange_nonempty K hq
  cusps_finite := finite_compl_of_isCurveOver (k := K) (P1 K) _ (quotLineι_opensRange_nonempty K hq)
  hyperbolic := lt_of_lt_of_le
    (by have := three_le_cuspDegree_puncturedLine K; omega)
    (Nat.add_le_add_left (cuspDegree_anti (quotLineι_opensRange_le K q)
      (finite_compl_of_isCurveOver (k := K) (P1 K) _ (quotLineι_opensRange_nonempty K hq))) _)

lemma lineCurve_Xbar (q : K[X]) (hq : q ≠ 0) : (lineCurve K q hq).Xbar = P1 K := rfl

lemma lineCurve_U (q : K[X]) (hq : q ≠ 0) :
    (lineCurve K q hq).U = (quotLineι K (quotLinePoly K q)).opensRange := rfl

/-- **`∞` is a cusp of the punctured line.** -/
theorem lineCurve_cusp (q : K[X]) (hq : q ≠ 0) :
    ((lineCurve K q hq).U : Set (lineCurve K q hq).Xbar)ᶜ.Nonempty :=
  ⟨P1.infty K, fun hx ↦ quotLineι_opensRange_le K q hx (infty_mem_markedPoints K)⟩

lemma isAffineOpen_lineCurve (q : K[X]) (hq : q ≠ 0) : IsAffineOpen (lineCurve K q hq).U :=
  isAffineOpen_opensRange (quotLineι K (quotLinePoly K q))

/-- **`Spec K[X]_{h'} ≅ Spec Γ(ℙ¹, D(h'))`.** -/
noncomputable def lineCurveIso (q : K[X]) (hq : q ≠ 0) :
    Spec (.of (Localization.Away (quotLinePoly K q))) ≅
      Spec Γ((lineCurve K q hq).Xbar, (lineCurve K q hq).U) :=
  (quotLineι K (quotLinePoly K q)).isoOpensRange ≪≫ (isAffineOpen_lineCurve K q hq).isoSpec

/-- `lineCurveIso` is compatible with the structure morphisms to `Spec K`. -/
theorem lineCurveIso_hom_structure (q : K[X]) (hq : q ≠ 0) :
    (lineCurveIso K q hq).hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K Γ((lineCurve K q hq).Xbar, (lineCurve K q hq).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away (quotLinePoly K q)))) := by
  rw [← isoSpec_inv_ι_structure K (isAffineOpen_lineCurve K q hq)]
  simp only [lineCurveIso, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact (Scheme.Hom.isoOpensRange_hom_ι_assoc (quotLineι K (quotLinePoly K q)) _).trans
    (quotLineι_structMap K _)

instance connectedSpace_lineCurve (q : K[X]) (hq : q ≠ 0) :
    ConnectedSpace (Spec Γ((lineCurve K q hq).Xbar, (lineCurve K q hq).U)) :=
  haveI := connectedSpace_spec_away (quotLinePoly_ne_zero K hq)
  ObjectProperty.prop_of_iso (fun X : Scheme.{u} ↦ ConnectedSpace X) (lineCurveIso K q hq)
    inferInstance

end Line

/-! ### The cover `Spec R_{h'} ⟶ Spec Γ(ℙ¹, D(h'))` -/

section Cover

variable {K R : Type u} [Field K] [CommRing R] [IsDomain R] [Algebra K R]

attribute [local instance] lineAwayAlgebra

omit [IsDomain R] in
/-- **Étaleness persists on smaller basic opens.** If `K[X]_h → R_h` is étale and `K[X] → R` is
finite, then `K[X]_{h₁} → R_{h₁}` is finite étale for every multiple `h₁` of `h`. -/
theorem etale_finite_awayMap_of_dvd {t : R} (hfin : (lineHom K t).Finite) {h h₁ : K[X]}
    (hdvd : h ∣ h₁) (he : (Localization.awayMap (lineHom K t) h).Etale) :
    (Localization.awayMap (lineHom K t) h₁).Etale ∧
      (Localization.awayMap (lineHom K t) h₁).Finite := by
  letI := lineAlgebra K t
  haveI : Module.Finite K[X] R := hfin
  haveI : Algebra.FinitePresentation K[X] R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have tower : ∀ p : K[X],
      IsScalarTower K[X] (Localization.Away p) (Localization.Away (lineHom K t p)) := fun p ↦
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = Localization.awayMap (lineHom K t) p (algebraMap K[X] (Localization.Away p) a)
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
        IsScalarTower.algebraMap_apply K[X] R]
      rfl
  haveI := tower h
  haveI : Algebra.Etale (Localization.Away h) (Localization.Away (lineHom K t h)) := he
  haveI : Algebra.Etale K[X] (Localization.Away h) := Algebra.Etale.of_isLocalizationAway h
  haveI : Algebra.Etale K[X] (Localization.Away (lineHom K t h)) :=
    Algebra.Etale.comp K[X] (Localization.Away h) _
  have hsub0 : (PrimeSpectrum.basicOpen (lineHom K t h₁) : Set (PrimeSpectrum R)) ⊆
      PrimeSpectrum.basicOpen (lineHom K t h) := by
    obtain ⟨c, rfl⟩ := hdvd
    intro x hx
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hx ⊢
    intro hxh
    exact hx (by rw [map_mul]; exact x.asIdeal.mul_mem_right _ hxh)
  have hsub : (PrimeSpectrum.basicOpen (lineHom K t h₁) : Set (PrimeSpectrum R)) ⊆
      Algebra.etaleLocus K[X] R :=
    hsub0.trans (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr inferInstance)
  haveI : Algebra.Etale K[X] (Localization.Away (lineHom K t h₁)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hsub
  haveI : Algebra.Etale K[X] (Localization.Away h₁) := Algebra.Etale.of_isLocalizationAway h₁
  haveI := tower h₁
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R (Submonoid.powers h₁))
      (Localization.Away (lineHom K t h₁)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact Localization.isLocalization
  exact ⟨Algebra.Etale.of_restrictScalars K[X] (Localization.Away h₁) _,
    Module.Finite.of_isLocalization K[X] R (Submonoid.powers h₁)⟩

omit [IsDomain R] in
lemma lineHom_ne_zero {t : R} (htr : Transcendental K t) {p : K[X]} (hp : p ≠ 0) :
    lineHom K t p ≠ 0 :=
  fun h0 ↦ hp ((transcendental_iff_injective.mp htr) (h0.trans (map_zero _).symm))

variable [CharZero K]

variable (K) in
/-- `R_{h'} = R[1/h'(t)]` for `h' = X (X - 1) h`. -/
abbrev quotCoverRing (t : R) (h : K[X]) : Type u :=
  Localization.Away (lineHom K t (quotLinePoly K h))

variable (K) (t : R) (h : K[X]) (hh : h ≠ 0)

omit [CharZero K] in
include hh in
lemma connectedSpace_coverRing (htr : Transcendental K t) :
    ConnectedSpace (Spec (.of (quotCoverRing K t h))) :=
  connectedSpace_spec_away (lineHom_ne_zero htr (quotLinePoly_ne_zero K hh))

/-- The ring map `Γ(ℙ¹, D(h')) ≅ K[X]_{h'} → R_{h'}`. -/
noncomputable def quotLineCoverHom :
    Γ((lineCurve K h hh).Xbar, (lineCurve K h hh).U) ⟶ CommRingCat.of (quotCoverRing K t h) :=
  Spec.preimage (lineCurveIso K h hh).hom ≫
    CommRingCat.ofHom (Localization.awayMap (lineHom K t) (quotLinePoly K h))

/-- **The cover `Spec R_{h'} ⟶ Spec Γ(ℙ¹, D(h'))`.** -/
noncomputable def quotLineCover :
    Spec (.of (quotCoverRing K t h)) ⟶ Spec Γ((lineCurve K h hh).Xbar, (lineCurve K h hh).U) :=
  Spec.map (quotLineCoverHom K t h hh)

omit [IsDomain R] in
lemma quotLineCover_eq : quotLineCover K t h hh =
    Spec.map (CommRingCat.ofHom (Localization.awayMap (lineHom K t) (quotLinePoly K h))) ≫
      (lineCurveIso K h hh).hom := by
  rw [quotLineCover, quotLineCoverHom, Spec.map_comp, Spec.map_preimage]

omit [IsDomain R] in
/-- **The cover is finite étale.** -/
theorem isFiniteEtale_lineCover (hfin : (lineHom K t).Finite)
    (he : (Localization.awayMap (lineHom K t) h).Etale) :
    IsFiniteEtale (quotLineCover K t h hh) := by
  obtain ⟨he', hf'⟩ := etale_finite_awayMap_of_dvd hfin (dvd_mul_left h (puncturedPoly K)) he
  haveI : IsFiniteEtale (Spec.map (CommRingCat.ofHom
      (Localization.awayMap (lineHom K t) (quotLinePoly K h)))) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.FiniteEtale.iff_finite_and_etale]
    exact ⟨he', hf'⟩
  haveI : IsFiniteEtale (lineCurveIso K h hh).hom := ⟨⟩
  rw [quotLineCover_eq]
  infer_instance

variable (hfin : (lineHom K t).Finite) (he : (Localization.awayMap (lineHom K t) h).Etale)

/-- The `Spec` of an automorphism of `R_{h'}` over `K[X]_{h'}`, as an automorphism of the cover in
`FiniteEtale (Spec Γ(ℙ¹, D(h')))`. -/
noncomputable def coverSpecAut
    (σ : quotCoverRing K t h ≃ₐ[Localization.Away (quotLinePoly K h)] quotCoverRing K t h) :
    haveI := isFiniteEtale_lineCover K t h hh hfin he
    Aut (coverObj (quotLineCover K t h hh)) :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  MorphismProperty.Over.isoMk
    { hom := Spec.map (CommRingCat.ofHom (σ : quotCoverRing K t h →+* quotCoverRing K t h))
      inv := Spec.map (CommRingCat.ofHom (σ.symm : quotCoverRing K t h →+* quotCoverRing K t h))
      hom_inv_id := by
        change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of (quotCoverRing K t h)))
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext x
        simp
      inv_hom_id := by
        change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of (quotCoverRing K t h)))
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext x
        simp }
    (by
      change Spec.map _ ≫ Spec.map (quotLineCoverHom K t h hh) =
        Spec.map (quotLineCoverHom K t h hh)
      rw [← Spec.map_comp]
      congr 1
      simp only [quotLineCoverHom, Category.assoc]
      congr 1
      ext x
      exact σ.commutes x)

omit [IsDomain R] in
lemma coverSpecAut_hom_left
    (σ : quotCoverRing K t h ≃ₐ[Localization.Away (quotLinePoly K h)] quotCoverRing K t h) :
    (coverSpecAut K t h hh hfin he σ).hom.left =
      Spec.map (CommRingCat.ofHom (σ : quotCoverRing K t h →+* quotCoverRing K t h)) :=
  rfl

variable {G : Type*} [Group G] (ρ : G →* (R ≃ₐ[K] R)) (hinv : ∀ g, ρ g t = t)

/-- **The action of `G` on the cover**: `g ↦ Spec (ρ g⁻¹)` (`Spec` is contravariant), from the
extension `CurvesJacobian.Cusp.awayAut` of `ρ` to `R_{h'}`. -/
noncomputable def coverAut :
    haveI := isFiniteEtale_lineCover K t h hh hfin he
    G →* Aut (coverObj (quotLineCover K t h hh)) :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  { toFun := fun g ↦ coverSpecAut K t h hh hfin he (awayAut ρ hinv (quotLinePoly K h) g⁻¹)
    map_one' := Iso.ext <| MorphismProperty.Over.Hom.ext <| by
      change Spec.map _ = 𝟙 _
      rw [← Spec.map_id]
      congr 1
      ext x
      simp
    map_mul' := fun g g' ↦ Iso.ext <| MorphismProperty.Over.Hom.ext <| by
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp [mul_inv_rev, map_mul, AlgEquiv.mul_apply] }

omit [IsDomain R] in
lemma coverAut_hom_left (g : G) :
    (coverAut K t h hh hfin he ρ hinv g).hom.left = Spec.map (CommRingCat.ofHom
      (awayAut ρ hinv (quotLinePoly K h) g⁻¹ : quotCoverRing K t h →+* quotCoverRing K t h)) :=
  rfl

/-- **The action on the cover is faithful** if `ρ` is. -/
theorem coverAut_injective (htr : Transcendental K t) (hρ : Function.Injective ρ) :
    Function.Injective (coverAut K t h hh hfin he ρ hinv) := by
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  have h1 : Spec.map (CommRingCat.ofHom
      (awayAut ρ hinv (quotLinePoly K h) g⁻¹ :
        quotCoverRing K t h →+* quotCoverRing K t h)) = 𝟙 _ :=
    congrArg (fun e : Aut (coverObj (quotLineCover K t h hh)) ↦ e.hom.left) hg
  have h2 := Spec.map_injective (h1.trans (Spec.map_id _).symm)
  have hinj : Function.Injective (algebraMap R (quotCoverRing K t h)) :=
    IsLocalization.injective (M := Submonoid.powers (lineHom K t (quotLinePoly K h))) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (lineHom_ne_zero htr (quotLinePoly_ne_zero K hh)))
  have h3 : ρ g⁻¹ = 1 := AlgEquiv.ext fun r ↦ hinj (by
    have := congrArg (fun φ : CommRingCat.of (quotCoverRing K t h) ⟶ CommRingCat.of
      (quotCoverRing K t h) ↦ φ.hom (algebraMap R _ r)) h2
    change awayAut ρ hinv (quotLinePoly K h) g⁻¹ (algebraMap R _ r) = algebraMap R _ r at this
    rw [awayAut_algebraMap] at this
    exact this)
  exact inv_eq_one.mp (hρ (h3.trans (map_one ρ).symm))

/-! ### The quotient `W = Spec R_{h'} / G` and the quotient curve -/

variable [Finite G]

/-- **The quotient `W = Spec R_{h'} / G`**, a finite étale scheme over `Spec Γ(ℙ¹, D(h'))`. -/
noncomputable abbrev lineQuotObj :
    FiniteEtale (Spec Γ((lineCurve K h hh).Xbar, (lineCurve K h hh).U)) :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  qObj (coverAut K t h hh hfin he ρ hinv)

/-- The scheme `W`. -/
noncomputable abbrev lineQuot : Scheme.{u} := (lineQuotObj K t h hh hfin he ρ hinv).left

/-- The structure map `W ⟶ Spec Γ(ℙ¹, D(h'))` (finite étale). -/
noncomputable abbrev lineQuotHom :
    lineQuot K t h hh hfin he ρ hinv ⟶ Spec Γ((lineCurve K h hh).Xbar, (lineCurve K h hh).U) :=
  (lineQuotObj K t h hh hfin he ρ hinv).hom

instance isFiniteEtale_lineQuotHom : IsFiniteEtale (lineQuotHom K t h hh hfin he ρ hinv) :=
  (lineQuotObj K t h hh hfin he ρ hinv).2

/-- The quotient map `q : Spec R_{h'} ⟶ W`. -/
noncomputable def lineQuotMap :
    Spec (.of (quotCoverRing K t h)) ⟶ lineQuot K t h hh hfin he ρ hinv :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  (qMap (coverAut K t h hh hfin he ρ hinv)).hom.left

/-- The quotient map is finite étale. -/
instance isFiniteEtale_lineQuotMap : IsFiniteEtale (lineQuotMap K t h hh hfin he ρ hinv) :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  isFiniteEtale_qMap (coverAut K t h hh hfin he ρ hinv)

omit [IsDomain R] in
/-- `q` lies over `Spec Γ(ℙ¹, D(h'))`. -/
lemma lineQuotMap_comp :
    lineQuotMap K t h hh hfin he ρ hinv ≫ lineQuotHom K t h hh hfin he ρ hinv =
      quotLineCover K t h hh :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  qMap_comp_hom (coverAut K t h hh hfin he ρ hinv)

/-- **The quotient `W` is connected.** -/
theorem connectedSpace_lineQuot (htr : Transcendental K t) :
    ConnectedSpace (lineQuot K t h hh hfin he ρ hinv) :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  haveI := connectedSpace_coverRing K t h hh htr
  connectedSpace_qObj (coverAut K t h hh hfin he ρ hinv)

variable [NumberField K] (htr : Transcendental K t)

/-- **The quotient curve `Z₀`**: `W` as a hyperbolic curve over its constant field
(`CurvesJacobian.Cusp.coverCurve` of the connected finite étale `W ⟶ Spec Γ(ℙ¹, D(h'))`). -/
noncomputable def lineQuotCurve :
    haveI := connectedSpace_lineQuot K t h hh hfin he ρ hinv htr
    HypCurve (coverField (lineCurve K h hh) (lineCurve_cusp K h hh)
      (lineQuotHom K t h hh hfin he ρ hinv)) :=
  haveI := connectedSpace_lineQuot K t h hh hfin he ρ hinv htr
  coverCurve (lineCurve K h hh) (lineCurve_cusp K h hh) (lineQuotHom K t h hh hfin he ρ hinv)

omit [NumberField K] in
/-- The quotient curve has a cusp. -/
theorem lineQuotCurve_cusp :
    ((lineQuotCurve K t h hh hfin he ρ hinv htr).U :
      Set (lineQuotCurve K t h hh hfin he ρ hinv htr).Xbar)ᶜ.Nonempty :=
  haveI := connectedSpace_lineQuot K t h hh hfin he ρ hinv htr
  coverCurve_cusp (lineCurve K h hh) (lineCurve_cusp K h hh) (lineQuotHom K t h hh hfin he ρ hinv)

/-- **`Spec Γ(Z₀) ≅ W`** (`CurvesJacobian.Cusp.coverIso`). -/
noncomputable def lineQuotCurveIso :
    Spec Γ((lineQuotCurve K t h hh hfin he ρ hinv htr).Xbar,
      (lineQuotCurve K t h hh hfin he ρ hinv htr).U) ≅ lineQuot K t h hh hfin he ρ hinv :=
  haveI := connectedSpace_lineQuot K t h hh hfin he ρ hinv htr
  coverIso (lineCurve K h hh) (lineCurve_cusp K h hh) (lineQuotHom K t h hh hfin he ρ hinv)

/-! ### Fundamental groups: `π₁ᵉᵗ(Spec R_{h'}) ⊴ π₁ᵉᵗ(W)` with quotient `G` -/

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η : Spec (.of Ω) ⟶ Spec (.of (quotCoverRing K t h)))
  {η' : Spec (.of Ω) ⟶ Spec Γ((lineCurve K h hh).Xbar, (lineCurve K h hh).U)}

omit [NumberField K] [IsDomain R] in
/-- **`π₁ᵉᵗ(Spec R_{h'}) ≤ π₁ᵉᵗ(W)`** inside `π₁ᵉᵗ(Spec Γ(ℙ¹, D(h')))`. -/
theorem coverSubgroup_le_lineQuot (hη : η ≫ quotLineCover K t h hh = η') :
    haveI := isFiniteEtale_lineCover K t h hh hfin he
    (coverSubgroup (quotLineCover K t h hh) η hη : Subgroup π₁ᵉᵗ(η')) ≤
      quotCoverSubgroup η hη (coverAut K t h hh hfin he ρ hinv) :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  coverSubgroup_le_quot hη

omit [NumberField K] in
include htr in
/-- **`π₁ᵉᵗ(Spec R_{h'})` is normal in `π₁ᵉᵗ(W)`** (for `ρ` injective). -/
theorem normal_coverSubgroup_lineQuot (hρ : Function.Injective ρ)
    (hη : η ≫ quotLineCover K t h hh = η') :
    haveI := isFiniteEtale_lineCover K t h hh hfin he
    ((coverSubgroup (quotLineCover K t h hh) η hη : Subgroup π₁ᵉᵗ(η')).subgroupOf
      (quotCoverSubgroup η hη (coverAut K t h hh hfin he ρ hinv))).Normal :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  haveI := connectedSpace_coverRing K t h hh htr
  normal_coverSubgroup_quot hη (coverAut_injective K t h hh hfin he ρ hinv htr hρ)

omit [NumberField K] in
/-- **`π₁ᵉᵗ(W) ⧸ π₁ᵉᵗ(Spec R_{h'}) ≃* G`** (`CurvesJacobian.Cusp.coverSubgroupQuotEquiv`). -/
noncomputable def lineQuotEquiv (hρ : Function.Injective ρ) (hη : η ≫ quotLineCover K t h hh = η') :
    haveI := isFiniteEtale_lineCover K t h hh hfin he
    haveI := normal_coverSubgroup_lineQuot K t h hh hfin he ρ hinv htr η hρ hη
    quotCoverSubgroup η hη (coverAut K t h hh hfin he ρ hinv) ⧸
      (coverSubgroup (quotLineCover K t h hh) η hη : Subgroup π₁ᵉᵗ(η')).subgroupOf
        (quotCoverSubgroup η hη (coverAut K t h hh hfin he ρ hinv)) ≃* G :=
  haveI := isFiniteEtale_lineCover K t h hh hfin he
  haveI := normal_coverSubgroup_lineQuot K t h hh hfin he ρ hinv htr η hρ hη
  haveI := connectedSpace_coverRing K t h hh htr
  coverSubgroupQuotEquiv hη (coverAut_injective K t h hh hfin he ρ hinv htr hρ)

end Cover

end CurvesJacobian.Cusp
