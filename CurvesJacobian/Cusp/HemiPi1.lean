/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.OrbiQuotientPi1
import CurvesJacobian.Cusp.CurveGaloisData
import CurvesJacobian.Cusp.EllipticPunctured
import CurvesJacobian.Galois.EtalePi1
import EllipticCurves.FunctionField.NegYGalois
import EllipticCurves.FunctionField.TranslationEndomorphism

/-!
# `π₁` of the hemi-elliptic orbicurve `(E ∖ {O}) / ±1` (MR8, bridge for [AbsTopII] Cor. 3.3)

Let `E` be an elliptic curve over a field `K` of characteristic `0`, `Ē = curveE E` its smooth
projective model, `X = E ∖ {O} = q⁻¹ 𝔸¹` (`XE E`), `Ω = K(Ē)^alg` and `t = x ∈ K(Ē) ⊆ Ω` the
Weierstrass `x`-coordinate. We apply the generic orbifold extension of
`CurvesJacobian.Cusp.OrbiQuotientPi1` to the quotient of `X` by the hyperelliptic involution
`[−1] : y ↦ −y − a₁x − a₃`:

* `CurvesJacobian.Cusp.funFieldEquivE : K(Ē) ≃ K(E)` (fraction fields of `Γ(X) ≅ K[E]`), mapping
  `x` to `genX` (`funFieldEquivE_xN`); hence `x` is transcendental (`transcendental_xN`);
* `CurvesJacobian.Cusp.hemiCurveData E = curveGaloisData K _` (`H = H_L = Gal(Ω / K(Ē))`) and
  `[L : K(x)] = 2` (`finrank_hemiCurveData_L`, from `[K(E) : K(x)] = 2` of `elliptic-curves`);
  so `H_L` is normal (`hemiHL_normal`) and
  `CurvesJacobian.Cusp.hemiData E = galoisDataTop _ _` (`H = Gal(Ω / K(x))`, `A = H ⧸ H_L`);
* `index_range_orbiIncl_hemi : [Π_C : Π_X] = 2`, `card_hemiA : |A| = 2`,
  `hemiAEquiv : A ≃* ℤ/2`;
* `CurvesJacobian.Cusp.mem_range_germ_XE_iff`: `Γ(X) ⊆ K(Ē)` is the integral closure of `K[x]`;
  hence `sectionsXEHemiAlgEquiv : Γ(X) ≃ₐ[K] R` and `hemiREquiv : K[E] ≃ₐ[K] R`, compatible with
  the embeddings into `Ω` (`algebraMap_sectionsXEHemiAlgEquiv`, `algebraMap_hemiREquiv`);
* `hemi_smul_hemiREquiv`: the nontrivial element of `A` acts on `R ≅ K[E]` as `[−1]`
  (`negYCoordEquiv`);
* `hemi_orbiIncl`, `hemi_orbiEmb`: `Π_X = π₁(E ∖ {O}) ↪ Π_C` is an open embedding with normal
  image of index `2`, compatible with the projections to `Gal(K̄ / K)`.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve Topology
open WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section Generic

/-- Two roots of the same monic quadratic `Y² + c₁ Y − c₀` are equal or conjugate. -/
lemma eq_or_eq_neg_sub_of_quadratic₂ {F : Type*} [CommRing F] [IsDomain F] {y z c₁ c₀ : F}
    (hy : y ^ 2 + c₁ * y - c₀ = 0) (hz : z ^ 2 + c₁ * z - c₀ = 0) : z = y ∨ z = -y - c₁ := by
  have h : (z - y) * (z - (-y - c₁)) = 0 := by linear_combination hz - hy
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]

/-- The image of `π₁ᵉᵗ(Spec R) ↪ etalePi1 R A Ω` is the image of `ι` under `equivPi1⁻¹`. -/
theorem range_orbiEmb₂ : (orbiEmb D).toMonoidHom.range =
    (orbiIncl D).toMonoidHom.range.map (D.equivPi1.symm.toMulEquiv : _ →* _) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨(galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D) y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).symm z, ?_⟩
    change D.equivPi1.symm (orbiIncl D (((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D))
      (((galoisDataHL D).equivPi1Spec (galoisDataHL_H_le D)).symm z))) = _
    rw [ContinuousMulEquiv.apply_symm_apply]
    rfl

/-- The image of `orbiEmb` is normal. -/
theorem range_orbiEmb_normal₂ : (orbiEmb D).toMonoidHom.range.Normal := by
  rw [range_orbiEmb₂]
  exact Subgroup.Normal.map (range_orbiIncl_normal D) _ D.equivPi1.symm.toMulEquiv.surjective

/-- The index of the image of `orbiEmb` is that of `ι`, i.e. `[H : H_L]`. -/
theorem index_range_orbiEmb₂ :
    (orbiEmb D).toMonoidHom.range.index = (orbiIncl D).toMonoidHom.range.index := by
  rw [range_orbiEmb₂]
  exact Subgroup.index_map_equiv _ _

end Generic

section Hemi

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- `Ē` is integral, as a named instance. The unfolded instance (integrality of the
normalisation of `ℙ¹` in `E ∖ E[2]`) is a large term, and it is repeated in every occurrence of
`Ω = K(Ē)^alg` in the types of the hemi files; naming it keeps these types small (olean
serialization of the hemi files was slow). -/
instance (priority := high) isIntegral_curveE : IsIntegral (curveE E) := inferInstance

/-! ### `K(Ē) ≃ K(E)` and the transcendence of `x` -/

/-- **`K(Ē) ≃ K(E)`**: the fraction fields of `Γ(E ∖ {O}) ≃ K[E]`. -/
def funFieldEquivE : (curveE E).functionField ≃+* E.toAffine.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (sectionsXEAlgEquiv E).toRingEquiv

lemma funFieldEquivE_germ (s : Γ(curveE E, XE E)) :
    funFieldEquivE E (algebraMap Γ(curveE E, XE E) (curveE E).functionField s) =
      algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField (sectionsXEAlgEquiv E s) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ s

lemma coordToXE_of (q : K[X]) :
    coordToXE E (AdjoinRoot.of E.toAffine.polynomial q) = polyToXE E q :=
  AdjoinRoot.lift_of _

lemma sectionsXEAlgEquiv_xX :
    sectionsXEAlgEquiv E (xX E) = AdjoinRoot.of E.toAffine.polynomial X := by
  apply (sectionsXEAlgEquiv E).symm.injective
  rw [AlgEquiv.symm_apply_apply, sectionsXEAlgEquiv_symm_apply, coordToXE_of]
  rfl

lemma funFieldEquivE_xN : funFieldEquivE E (xN E) = genX E.toAffine := by
  rw [← germ_xX, funFieldEquivE_germ, sectionsXEAlgEquiv_xX]
  rfl

lemma funFieldEquivE_algebraMap (c : K) :
    funFieldEquivE E (algebraMap K (curveE E).functionField c) =
      algebraMap K E.toAffine.FunctionField c := by
  rw [← germ_algebraMap_XE, funFieldEquivE_germ, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

/-- `K(Ē) ≃ₐ[K] K(E)`. -/
def funFieldAlgEquivE : (curveE E).functionField ≃ₐ[K] E.toAffine.FunctionField :=
  AlgEquiv.ofRingEquiv (f := funFieldEquivE E) (funFieldEquivE_algebraMap E)

/-- **`x` is transcendental over `K`.** -/
theorem transcendental_xN : Transcendental K (xN E) := fun h =>
  transcendental_genX (W := E.toAffine) (by
    rw [← funFieldEquivE_xN]
    exact (isAlgebraic_algHom_iff (funFieldAlgEquivE E).toAlgHom
      (funFieldAlgEquivE E).injective).2 h)

/-! ### The Galois data -/

/-- The Galois data of `Ē` with coordinate `t = x`: `H = H_L = Gal(Ω / K(Ē))`. -/
abbrev hemiCurveData : GaloisData K (coordT (xN E)) := curveGaloisData K (transcendental_xN E)

instance isGalois_K₀_hemi : IsGalois (K₀ K (coordT (xN E))) (FFClosure (curveE E)) :=
  isGalois_K₀_algebraicClosure (k := K) (xN E) (transcendental_xN E)

/-- The embedding `K(E) ≃ K(Ē) → Ω`. -/
def embE : E.toAffine.FunctionField →ₐ[K] FFClosure (curveE E) :=
  (IsScalarTower.toAlgHom K (curveE E).functionField (FFClosure (curveE E))).comp
    (funFieldAlgEquivE E).symm.toAlgHom

lemma embE_genX : embE E (genX E.toAffine) = coordT (xN E) := by
  rw [← funFieldEquivE_xN]
  change algebraMap _ _ ((funFieldEquivE E).symm (funFieldEquivE E (xN E))) = _
  rw [RingEquiv.symm_apply_apply]

/-- **`[L : K(x)] = 2`**, from `[K(E) : K(x)] = 2`. -/
theorem finrank_hemiCurveData_L :
    Module.finrank (K₀ K (coordT (xN E))) (hemiCurveData E).L = 2 := by
  have hmap : (IntermediateField.adjoin K {genX E.toAffine}).map (embE E) =
      K₀ K (coordT (xN E)) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, embE_genX]
  let i : ratFuncRange E.toAffine ≃+* K₀ K (coordT (xN E)) :=
    ((IntermediateField.equivOfEq (ratFuncRange_eq_adjoin (W := E.toAffine))).trans
      ((IntermediateField.equivMap _ (embE E)).trans
        (IntermediateField.equivOfEq hmap))).toRingEquiv
  let j : E.toAffine.FunctionField ≃+* (hemiCurveData E).L :=
    (funFieldEquivE E).symm.trans (curveEquivL K (transcendental_xN E))
  rw [← finrank_ratFuncRange (W := E.toAffine)]
  exact (Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext fun _ => Subtype.ext rfl)).symm

/-- `H_L = Gal(Ω / K(Ē))` is normal in `Gal(Ω / K(x))`: `K(Ē) / K(x)` is quadratic, hence
Galois. -/
theorem hemiHL_normal : (hemiCurveData E).HL.Normal := by
  haveI : Algebra.IsQuadraticExtension (K₀ K (coordT (xN E))) (hemiCurveData E).L :=
    { toFree := Module.Free.of_divisionRing _ _, finrank_eq_two' := finrank_hemiCurveData_L E }
  rw [← (hemiCurveData E).fixingSubgroup_L]
  exact (InfiniteGalois.normal_iff_isGalois _).2 inferInstance

/-- **The Galois data of the hemi-elliptic orbicurve `[(E ∖ {O}) / ±1]`**: `H = Gal(Ω / K(x))`,
`H_L = Gal(Ω / K(Ē))`. -/
abbrev hemiData : GaloisData K (coordT (xN E)) :=
  galoisDataTop (hemiCurveData E) (hemiHL_normal E)

theorem finrank_hemiData_L : Module.finrank (K₀ K (coordT (xN E))) (hemiData E).L = 2 :=
  finrank_hemiCurveData_L E

/-- **`[Π_C : Π_X] = 2`.** -/
theorem index_range_orbiIncl_hemi : (orbiIncl (hemiData E)).toMonoidHom.range.index = 2 := by
  rw [index_range_orbiIncl_of_H_eq_top _ rfl]
  exact finrank_hemiData_L E

/-- **`|A| = 2`.** -/
theorem card_hemiA : Nat.card (hemiData E).A = 2 :=
  (Nat.card_congr (orbiQuotEquiv (hemiData E)).toEquiv).symm.trans (index_range_orbiIncl_hemi E)

/-- **`A ≃ ℤ / 2`.** -/
def hemiAEquiv : (hemiData E).A ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (card_hemiA E)
    ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2))

/-! ### `R ≅ Γ(E ∖ {O}) ≅ K[E]` -/

lemma germ_polyToXE (p : K[X]) :
    algebraMap Γ(curveE E, XE E) (curveE E).functionField (polyToXE E p) = aeval (xN E) p := by
  have h : (algebraMap Γ(curveE E, XE E) (curveE E).functionField).comp (polyToXE E) =
      (aeval (xN E)).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have h1 : algebraMap K E.toAffine.CoordinateRing a =
          AdjoinRoot.of E.toAffine.polynomial (C a) := by
        rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
      rw [RingHom.comp_apply, ← coordToXE_of, ← h1, coordToXE_algebraMap, germ_algebraMap_XE]
      exact (aeval_C _ _).symm
    · rw [RingHom.comp_apply]
      change algebraMap Γ(curveE E, XE E) (curveE E).functionField (xX E) = _
      rw [germ_xX]
      exact (aeval_X _).symm
  exact RingHom.congr_fun h p

/-- **`Γ(E ∖ {O}) ⊆ K(Ē)` is the integral closure of `K[x]`.** -/
theorem mem_range_germ_XE_iff (z : (curveE E).functionField) :
    z ∈ Set.range (algebraMap Γ(curveE E, XE E) (curveE E).functionField) ↔
      IsIntegral (Algebra.adjoin K {xN E}) z := by
  constructor
  · rintro ⟨s, rfl⟩
    letI := (qXE E).hom.toAlgebra
    obtain ⟨p, hpm, hp⟩ := isIntegral_qXE E s
    let φ : Γ(P1 K, A1 K) →+* Algebra.adjoin K {xN E} :=
      ((aeval (xN E)).toRingHom.codRestrict (Algebra.adjoin K {xN E}).toSubring
        (fun _ => aeval_mem_adjoin_singleton K (xN E))).comp (sectionsA1Iso K).hom.hom
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [eval₂_map]
    have hc : (algebraMap (Algebra.adjoin K {xN E}) (curveE E).functionField).comp φ =
        (algebraMap Γ(curveE E, XE E) (curveE E).functionField).comp
          (algebraMap Γ(P1 K, A1 K) Γ(curveE E, XE E)) := by
      refine RingHom.ext fun a => ?_
      have ha : algebraMap Γ(P1 K, A1 K) Γ(curveE E, XE E) a =
          polyToXE E ((sectionsA1Iso K).hom a) := by
        change qXE E a = qXE E ((sectionsA1Iso K).inv ((sectionsA1Iso K).hom a))
        rw [Iso.hom_inv_id_apply]
      rw [RingHom.comp_apply, RingHom.comp_apply, ha, germ_polyToXE]
      rfl
    rw [hc, ← hom_eval₂, hp, map_zero]
  · intro hz
    have hle : (Algebra.adjoin K {xN E}).toSubring ≤
        (algebraMap Γ(curveE E, XE E) (curveE E).functionField).range := by
      intro w hw
      change w ∈ Algebra.adjoin K {xN E} at hw
      induction hw using Algebra.adjoin_induction with
      | mem w hw =>
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ⟨xX E, germ_xX E⟩
      | algebraMap c => exact ⟨algebraMap K _ c, germ_algebraMap_XE E c⟩
      | add w v _ _ hw hv => exact add_mem hw hv
      | mul w v _ _ hw hv => exact mul_mem hw hv
    let e := RingEquiv.ofBijective
      (algebraMap Γ(curveE E, XE E) (curveE E).functionField).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective Γ(curveE E, XE E) (curveE E).functionField
        (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
    let g : Algebra.adjoin K {xN E} →+* Γ(curveE E, XE E) :=
      (e.symm : _ →+* _).comp (Subring.inclusion hle)
    obtain ⟨p, hpm, hp⟩ := hz
    have hint : IsIntegral Γ(curveE E, XE E) z := by
      refine ⟨p.map g, hpm.map g, ?_⟩
      rw [eval₂_map]
      have hc : (algebraMap Γ(curveE E, XE E) (curveE E).functionField).comp g =
          algebraMap (Algebra.adjoin K {xN E}) (curveE E).functionField := by
        refine RingHom.ext fun w => ?_
        have h1 : e (e.symm (Subring.inclusion hle w)) = Subring.inclusion hle w :=
          e.apply_symm_apply _
        exact congrArg Subtype.val h1
      rw [hc]
      exact hp
    exact IsIntegrallyClosed.isIntegral_iff.1 hint

/-- `K(Ē) ≃ L` for the Galois data `hemiData E`. -/
def hemiEquivL : (curveE E).functionField ≃+* (hemiData E).L :=
  curveEquivL K (transcendental_xN E)

lemma hemiEquivL_apply (z : (curveE E).functionField) :
    ((hemiEquivL E z : (hemiData E).L) : FFClosure (curveE E)) =
      algebraMap (curveE E).functionField (FFClosure (curveE E)) z := rfl

lemma hemiEquivL_algebraMap (c : K) :
    ((hemiEquivL E (algebraMap K (curveE E).functionField c) : (hemiData E).L) :
      FFClosure (curveE E)) = algebraMap K (FFClosure (curveE E)) c :=
  curveEquivL_algebraMap K (transcendental_xN E) c

lemma hemiEquivL_xN :
    ((hemiEquivL E (xN E) : (hemiData E).L) : FFClosure (curveE E)) = coordT (xN E) := rfl

/-- **`Γ(E ∖ {O}) ≅ R`** (the integral closure of `K[x]` in `L`), as rings. -/
def sectionsXERingEquiv : Γ(curveE E, XE E) ≃+* (hemiData E).R :=
  ringEquivOfRangeEq ((hemiEquivL E).toRingHom.comp
      (algebraMap Γ(curveE E, XE E) (curveE E).functionField))
    (algebraMap (hemiData E).R (hemiData E).L)
    ((hemiEquivL E).injective.comp
      (IsFractionRing.injective Γ(curveE E, XE E) (curveE E).functionField))
    (hemiData E).algebraMap_L_injective
    fun y => by
      rw [mem_range_algebraMap_L_iff]
      constructor
      · rintro ⟨a, rfl⟩
        exact (isIntegral_iff_one (hemiData E) (curveE E) (hemiEquivL E) (hemiEquivL_algebraMap E)
          (hemiEquivL_xN E) _).1 ((mem_range_germ_XE_iff E _).1 ⟨a, rfl⟩)
      · intro h
        have h' : IsIntegral (A₀ K (coordT (xN E)))
            ((hemiEquivL E ((hemiEquivL E).symm y) : (hemiData E).L) : FFClosure (curveE E)) := by
          rwa [RingEquiv.apply_symm_apply]
        obtain ⟨a, ha⟩ := (mem_range_germ_XE_iff E _).2
          ((isIntegral_iff_one (hemiData E) (curveE E) (hemiEquivL E) (hemiEquivL_algebraMap E)
            (hemiEquivL_xN E) _).2 h')
        refine ⟨a, ?_⟩
        change hemiEquivL E (algebraMap Γ(curveE E, XE E) (curveE E).functionField a) = y
        rw [ha, RingEquiv.apply_symm_apply]

lemma algebraMap_sectionsXERingEquiv (s : Γ(curveE E, XE E)) :
    algebraMap (hemiData E).R (FFClosure (curveE E)) (sectionsXERingEquiv E s) =
      algebraMap (curveE E).functionField (FFClosure (curveE E))
        (algebraMap Γ(curveE E, XE E) (curveE E).functionField s) := by
  unfold sectionsXERingEquiv
  exact congrArg (fun y : (hemiData E).L => (y : FFClosure (curveE E)))
    (ringEquivOfRangeEq_apply _ (algebraMap (hemiData E).R (hemiData E).L) _ _ _ s)

/-- **`Γ(E ∖ {O}) ≃ₐ[K] R`**, compatible with the embeddings into `Ω`
(`algebraMap_sectionsXEHemiAlgEquiv`). -/
def sectionsXEHemiAlgEquiv : Γ(curveE E, XE E) ≃ₐ[K] (hemiData E).R :=
  AlgEquiv.ofRingEquiv (f := sectionsXERingEquiv E) fun c => CoordRing.ext (by
    rw [algebraMap_sectionsXERingEquiv, germ_algebraMap_XE,
      ← IsScalarTower.algebraMap_apply K (curveE E).functionField (FFClosure (curveE E)),
      ← IsScalarTower.algebraMap_apply K (hemiData E).R (FFClosure (curveE E))])

lemma algebraMap_sectionsXEHemiAlgEquiv (s : Γ(curveE E, XE E)) :
    algebraMap (hemiData E).R (FFClosure (curveE E)) (sectionsXEHemiAlgEquiv E s) =
      algebraMap (curveE E).functionField (FFClosure (curveE E))
        (algebraMap Γ(curveE E, XE E) (curveE E).functionField s) :=
  algebraMap_sectionsXERingEquiv E s

/-- **`K[E] ≃ₐ[K] R`**: the coordinate ring of the Weierstrass model `E ∖ {O}` is the ring `R`
of the Galois data `hemiData E`. -/
def hemiREquiv : E.toAffine.CoordinateRing ≃ₐ[K] (hemiData E).R :=
  (sectionsXEAlgEquiv E).symm.trans (sectionsXEHemiAlgEquiv E)

lemma algebraMap_hemiREquiv (a : E.toAffine.CoordinateRing) :
    algebraMap (hemiData E).R (FFClosure (curveE E)) (hemiREquiv E a) =
      algebraMap (curveE E).functionField (FFClosure (curveE E))
        (algebraMap Γ(curveE E, XE E) (curveE E).functionField (coordToXE E a)) :=
  algebraMap_sectionsXERingEquiv E _

/-- The embedding `ρ : K[E] ≅ R ⊆ Ω`. -/
def hemiRho : E.toAffine.CoordinateRing →+* FFClosure (curveE E) :=
  (algebraMap (hemiData E).R (FFClosure (curveE E))).comp (hemiREquiv E).toRingEquiv.toRingHom

lemma hemiRho_apply (a : E.toAffine.CoordinateRing) :
    hemiRho E a = algebraMap (hemiData E).R (FFClosure (curveE E)) (hemiREquiv E a) := rfl

/-- `ρ` is `x ↦ t` on `K[x]`. -/
lemma hemiRho_of (q : K[X]) :
    hemiRho E (AdjoinRoot.of E.toAffine.polynomial q) = aeval (coordT (xN E)) q := by
  rw [hemiRho_apply, algebraMap_hemiREquiv, coordToXE_of, germ_polyToXE]
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom K (curveE E).functionField
    (FFClosure (curveE E))) (xN E) q).symm

lemma hemiRho_of_X : hemiRho E (AdjoinRoot.of E.toAffine.polynomial X) = coordT (xN E) := by
  rw [hemiRho_of, aeval_X]

/-- Elements of `Gal(Ω / K(x))` fix `ρ(K[x])`. -/
lemma fix_hemiRho_of (σ : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E))
    (q : K[X]) : σ (hemiRho E (AdjoinRoot.of E.toAffine.polynomial q)) =
      hemiRho E (AdjoinRoot.of E.toAffine.polynomial q) := by
  rw [hemiRho_of]
  have hmem : aeval (coordT (xN E)) q ∈ K₀ K (coordT (xN E)) :=
    IntermediateField.algebra_adjoin_le_adjoin K _ (aeval_mem_adjoin_singleton K _)
  exact σ.commutes ⟨_, hmem⟩

/-- The Weierstrass equation for `ρ(y)`. -/
lemma hemiRho_root_eq :
    hemiRho E (AdjoinRoot.root E.toAffine.polynomial) ^ 2 +
      hemiRho E (AdjoinRoot.of E.toAffine.polynomial (C E.a₁ * X + C E.a₃)) *
        hemiRho E (AdjoinRoot.root E.toAffine.polynomial) -
      hemiRho E (AdjoinRoot.of E.toAffine.polynomial
        (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = 0 := by
  have h0 : AdjoinRoot.mk E.toAffine.polynomial (Y ^ 2 + C (C E.a₁ * X + C E.a₃) * Y -
      C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.mk_C] at h0
  have h1 := congrArg (hemiRho E) h0
  rwa [map_sub, map_add, map_mul, map_pow, map_zero] at h1

/-- `ρ([−1] y) = −ρ(y) − a₁ t − a₃`. -/
lemma hemiRho_negY_root :
    hemiRho E (negYCoordEquiv E.toAffine (AdjoinRoot.root E.toAffine.polynomial)) =
      -hemiRho E (AdjoinRoot.root E.toAffine.polynomial) -
        hemiRho E (AdjoinRoot.of E.toAffine.polynomial (C E.a₁ * X + C E.a₃)) := by
  rw [negYCoordEquiv_apply, negYCoordHom_root, WeierstrassCurve.Affine.negPolynomial]
  change hemiRho E (AdjoinRoot.mk E.toAffine.polynomial
    (-(Y : K[X][Y]) - C (C E.a₁ * X + C E.a₃))) = _
  rw [map_sub, map_neg, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_sub, map_neg]

/-- An element of `Gal(Ω / K(x))` fixing `ρ(K[E])` lies in `H_L`, i.e. is trivial in `A`. -/
lemma mk_eq_one_of_fix_hemiRho (h : (hemiData E).H)
    (hfix : ∀ a, (h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E))
      (hemiRho E a) = hemiRho E a) : (h : (hemiData E).A) = 1 := by
  have hσ : (h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E)) ∈
      (hemiData E).L.fixingSubgroup := by
    refine CoordRing.mem_fixingSubgroup_of_forall _ fun x => ?_
    have hx := hfix ((hemiREquiv E).symm x)
    rwa [hemiRho_apply, AlgEquiv.apply_symm_apply] at hx
  rw [(hemiData E).fixingSubgroup_L] at hσ
  exact (QuotientGroup.eq_one_iff h).2 (Subgroup.mem_subgroupOf.2 hσ)

/-- **The nontrivial element of `A ≅ ℤ/2` acts on `R ≅ K[E]` as `[−1]`** (`x ↦ x`,
`y ↦ −y − a₁x − a₃`). -/
theorem hemi_smul_hemiREquiv (h : (hemiData E).H) (hh : (h : (hemiData E).A) ≠ 1)
    (a : E.toAffine.CoordinateRing) :
    (h : (hemiData E).A) • hemiREquiv E a = hemiREquiv E (negYCoordEquiv E.toAffine a) := by
  have hy := hemiRho_root_eq E
  have hz : ((h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E))
      (hemiRho E (AdjoinRoot.root E.toAffine.polynomial))) ^ 2 +
      hemiRho E (AdjoinRoot.of E.toAffine.polynomial (C E.a₁ * X + C E.a₃)) *
        (h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E))
          (hemiRho E (AdjoinRoot.root E.toAffine.polynomial)) -
      hemiRho E (AdjoinRoot.of E.toAffine.polynomial
        (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = 0 := by
    have h1 := congrArg (h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))] FFClosure (curveE E))
      hy
    rwa [map_sub, map_add, map_mul, map_pow, map_zero, fix_hemiRho_of, fix_hemiRho_of] at h1
  have hAlg : ((h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))]
      FFClosure (curveE E)).toRingEquiv.toRingHom.comp (hemiRho E)).comp
        (AdjoinRoot.of E.toAffine.polynomial) =
      (hemiRho E).comp (AdjoinRoot.of E.toAffine.polynomial) :=
    RingHom.ext fun q => fix_hemiRho_of E _ q
  have key := eq_or_eq_neg_sub_of_quadratic₂ (F := FFClosure (curveE E)) hy hz
  rcases key with h1 | h1
  · refine absurd (mk_eq_one_of_fix_hemiRho E h fun b => ?_) hh
    have he : (h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))]
        FFClosure (curveE E)).toRingEquiv.toRingHom.comp (hemiRho E) = hemiRho E :=
      AdjoinRoot.ringHom_ext hAlg h1
    exact RingHom.congr_fun he b
  · refine CoordRing.ext ?_
    rw [GaloisData.algebraMap_smul]
    have he : (h : FFClosure (curveE E) ≃ₐ[K₀ K (coordT (xN E))]
        FFClosure (curveE E)).toRingEquiv.toRingHom.comp (hemiRho E) =
        (hemiRho E).comp (negYCoordEquiv E.toAffine).toRingEquiv.toRingHom := by
      refine AdjoinRoot.ringHom_ext ?_ ?_
      · rw [hAlg]
        refine RingHom.ext fun q => ?_
        change hemiRho E _ = hemiRho E (negYCoordEquiv E.toAffine
          (algebraMap K[X] E.toAffine.CoordinateRing q))
        rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq]
      · change _ = hemiRho E (negYCoordEquiv E.toAffine (AdjoinRoot.root E.toAffine.polynomial))
        rw [hemiRho_negY_root]
        exact h1
    exact RingHom.congr_fun he a

/-! ### The orbifold extension `1 → Π_{E ∖ O} → Π_C → ℤ/2 → 1` -/

/-- **`Π_X = π₁(E ∖ {O}) ↪ Π_C`** (Galois-theoretic form): an open embedding with open normal
image of index `2`, compatible with the projections to `Gal(K̄ / K)`, with
`Δ_C ∩ Π_X = Δ_X`. -/
theorem hemi_orbiIncl :
    IsOpenEmbedding (orbiIncl (hemiData E)) ∧
      (orbiIncl (hemiData E)).toMonoidHom.range.Normal ∧
      (orbiIncl (hemiData E)).toMonoidHom.range.index = 2 ∧
      (piConstC (hemiData E)).comp (orbiIncl (hemiData E)).toMonoidHom =
        piConstX (hemiData E) ∧
      (piConstC (hemiData E)).ker ⊓ (orbiIncl (hemiData E)).toMonoidHom.range =
        (piConstX (hemiData E)).ker.map (orbiIncl (hemiData E)).toMonoidHom :=
  ⟨isOpenEmbedding_orbiIncl _, range_orbiIncl_normal _, index_range_orbiIncl_hemi E,
    piConst_comp_orbiIncl _, ker_piConst_inf_range_orbiIncl _⟩

/-- **`π₁ᵉᵗ(Spec R) ↪ etalePi1 R A Ω`** for `R ≅ K[E] = Γ(E ∖ {O})` (`hemiREquiv`) and
`A ≅ ℤ/2` acting by `[−1]` (`hemi_smul_hemiREquiv`): an open embedding with normal image of
index `2`. -/
theorem hemi_orbiEmb :
    IsOpenEmbedding (orbiEmb (hemiData E)) ∧ (orbiEmb (hemiData E)).toMonoidHom.range.Normal ∧
      (orbiEmb (hemiData E)).toMonoidHom.range.index = 2 :=
  ⟨isOpenEmbedding_orbiEmb _, range_orbiEmb_normal₂ _,
    (index_range_orbiEmb₂ _).trans (index_range_orbiIncl_hemi E)⟩

end Hemi

end CurvesJacobian.Cusp
