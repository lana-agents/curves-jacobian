/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SectionBridgeSpec
import CurvesJacobian.LocAn.ThmC
import CurvesJacobian.Galois.EtalePi1Open

/-!
# The place of a rational point of a curve in the Galois model

Setting of `Galois/EtalePi1Open.lean`: `D : GaloisData k t`, a curve `X` over `k` (characteristic
`0`) and `eL : K(X) ≃ L` with `eL(k) = k` (`hk`). Let `x : Spec k ⟶ X` be a `k`-rational point
(`x ≫ (X ↘ Spec k) = 𝟙`), `p` its image and `φ = stalkClosedPointTo x : 𝒪_{X,p} → k`.

* `CurvesJacobian.LocAn.SectionBridge.ratPlace`: a place `A ⊆ Ω` dominating `𝒪_{X,p} ⊆ K(X) ≅ L`
  (Mathlib's `IsLocalRing.exists_factor_valuationRing`), with `comapK A = 𝒪_{X,p}`;
* `placeMor : Spec A ⟶ X` (`Spec A ⟶ Spec 𝒪_{X,p} ⟶ X`), with
  `vGen_placeMor : (Spec Ω ⟶ Spec A ⟶ X) = geometricGenericPoint` and
  **`closed_placeMor`**: `(Spec κ(A) ⟶ Spec A ⟶ X) = (Spec κ(A) ⟶ Spec k ⟶ X)`, from
  `residue_stalkToPlace` (`𝒪_{X,p} → A → κ(A)` is `𝒪_{X,p} →φ k → κ(A)`: both kill the maximal
  ideal and agree on the constants, and `φ` is a retraction of `k → 𝒪_{X,p}`);
* `ratPointOf`: the point as a `RatPoint D` (for `H_L = H`): `κ(A)` is algebraic over `k`
  (`isIntegral_residueField_of_rational`, a general statement: residue fields of algebraic
  extensions of a place with rational residues) and residues of functions are rational.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi IsLocalRing Pi1.Orbifold

universe u

noncomputable section

namespace CurvesJacobian.LocAn.SectionBridge

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve

/-! ### Residue fields of places with rational residues -/

/-- **Residue fields under algebraic extensions**: let `A` be a place of `Ω`, algebraic over a
subfield `E`, and suppose the residue of every element of `E ∩ A` lies in the image of `k`. Then
`κ(A)` is algebraic over `k`. -/
theorem isIntegral_residueField_of_rational {Ω E k : Type u} [Field Ω] [Field E] [Field k]
    [Algebra E Ω] [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) [Algebra k (ResidueField A)]
    (hrat : ∀ (a : E) (ha : algebraMap E Ω a ∈ A),
      ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c) :
    Algebra.IsIntegral k (ResidueField A) := by
  classical
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp0, hpb⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) (b : Ω)
  obtain ⟨i₀, hi₀, hmax⟩ := p.support.exists_max_image
    (fun i ↦ A.valuation (algebraMap E Ω (p.coeff i))) (Polynomial.nonempty_support_iff.2 hp0)
  set c₀ : E := p.coeff i₀ with hc₀def
  have hc₀ : c₀ ≠ 0 := Polynomial.mem_support_iff.1 hi₀
  have hv₀ : A.valuation (algebraMap E Ω c₀) ≠ 0 := by
    rw [Ne, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap E Ω).injective]
    exact hc₀
  have hd : ∀ i, algebraMap E Ω (p.coeff i / c₀) ∈ A := by
    intro i
    rw [← A.valuation_le_one_iff, map_div₀, map_div₀]
    by_cases hi : i ∈ p.support
    · exact (div_le_one₀ (zero_lt_iff.2 hv₀)).2 (hmax i hi)
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero, map_zero, zero_div]
      exact zero_le
  choose c hc using fun i ↦ hrat (p.coeff i / c₀) (hd i)
  let r : Polynomial k := ∑ i ∈ p.support, Polynomial.monomial i (c i)
  have hr0 : r ≠ 0 := by
    intro h
    have h1 : r.coeff i₀ = c i₀ := by
      simp only [r, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ if_neg hj) (fun h ↦ absurd hi₀ h), if_pos rfl]
    rw [h, Polynomial.coeff_zero] at h1
    have h2 := hc i₀
    rw [← h1, map_zero] at h2
    have h3 : (⟨algebraMap E Ω (p.coeff i₀ / c₀), hd i₀⟩ : A) = 1 := by
      apply Subtype.ext
      change algebraMap E Ω (p.coeff i₀ / c₀) = 1
      rw [← hc₀def, div_self hc₀, map_one]
    rw [h3, map_one] at h2
    exact one_ne_zero h2
  refine (show IsAlgebraic k (residue A b) from ⟨r, hr0, ?_⟩).isIntegral
  have hsum : (∑ i ∈ p.support, (⟨algebraMap E Ω (p.coeff i / c₀), hd i⟩ : A) * b ^ i) = 0 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    change ∑ i ∈ p.support, algebraMap E Ω (p.coeff i / c₀) * (b : Ω) ^ i = 0
    have : (Polynomial.aeval (b : Ω) p) =
        ∑ i ∈ p.support, algebraMap E Ω (p.coeff i) * (b : Ω) ^ i := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    have h2 : ∑ i ∈ p.support, algebraMap E Ω (p.coeff i / c₀) * (b : Ω) ^ i =
        (Polynomial.aeval (b : Ω) p) * (algebraMap E Ω c₀)⁻¹ := by
      rw [this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_div₀]
      ring
    rw [h2, hpb, zero_mul]
  have := congrArg (residue A) hsum
  rw [map_zero, map_sum] at this
  rw [← this, map_sum]
  simp only [Polynomial.aeval_monomial, map_mul, map_pow, hc]

/-! ### The place of a rational point -/

section Place

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  [CharZero k] [IsCurveOver k X]
  (x : Spec (.of k) ⟶ X) (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _)

/-- The point of `X` of a rational point `x : Spec k ⟶ X`. -/
abbrev ratPt : X := x (closedPoint k)

/-- The constants `k → 𝒪_{X,p}`. -/
def stalkConst (p : X) : k →+* X.presheaf.stalk p :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ X.presheaf.germ ⊤ p trivial).hom

omit [IsIntegral X] [CharZero k] [IsCurveOver k X] in
include hx in
/-- `φ : 𝒪_{X,p} → k` is a retraction of the constants. -/
lemma stalkClosedPointTo_stalkConst (c : k) :
    (Scheme.stalkClosedPointTo x).hom (stalkConst (ratPt x) c) = c := by
  have h := Scheme.germ_stalkClosedPointTo x ⊤ trivial
  have e1 : (X ↘ Spec (.of k)).appTop ≫ x.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hx]
    rfl
  change (X.presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo x).hom
    ((X ↘ Spec (.of k)).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) = c
  rw [h]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply]
  have e2 : x.appTop.hom ((X ↘ Spec (.of k)).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) =
      (Scheme.ΓSpecIso (.of k)).inv.hom c := by
    rw [← CommRingCat.comp_apply, e1]
    rfl
  change (Scheme.ΓSpecIso (.of k)).hom.hom (((Spec (.of k)).presheaf.map _).hom
    (x.appTop.hom ((X ↘ Spec (.of k)).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)))) = c
  rw [e2]
  have e3 : ∀ (h : (⊤ : (Spec (CommRingCat.of k)).Opens) = x ⁻¹ᵁ ⊤) (y),
      ((Spec (CommRingCat.of k)).presheaf.map (eqToHom h).op).hom y = y := fun h y ↦ by
    have : (Spec (CommRingCat.of k)).presheaf.map (eqToHom h).op = 𝟙 _ :=
      (Spec (CommRingCat.of k)).presheaf.map_id _
    exact congrArg (fun f ↦ f.hom y) this
  erw [e3]
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id_apply c

/-- The local ring `𝒪_{X,p} ⊆ K(X)` mapped to `Ω` through `eL`. -/
def stalkVSToΩ (p : X) : stalkVS k p →+* Ω := (embK D X eL hk).toRingHom.comp (stalkVS k p).subtype

lemma exists_ratPlace (p : X) : ∃ (A : ValuationSubring Ω) (h : ∀ a, stalkVSToΩ D eL hk p a ∈ A),
    IsLocalHom ((stalkVSToΩ D eL hk p).codRestrict A.toSubring h) :=
  IsLocalRing.exists_factor_valuationRing _

/-- **The place of a point**: a valuation subring `A ⊆ Ω` dominating `𝒪_{X,p}`. -/
def ratPlace (p : X) : ValuationSubring Ω := (exists_ratPlace D eL hk p).choose

lemma stalkVSToΩ_mem (p : X) (a : stalkVS k p) : stalkVSToΩ D eL hk p a ∈ ratPlace D eL hk p :=
  (exists_ratPlace D eL hk p).choose_spec.choose a

/-- `𝒪_{X,p} → A`. -/
def vsToPlace (p : X) : stalkVS k p →+* ratPlace D eL hk p :=
  (stalkVSToΩ D eL hk p).codRestrict _ (stalkVSToΩ_mem D eL hk p)

instance (p : X) : IsLocalHom (vsToPlace D eL hk p) :=
  (exists_ratPlace D eL hk p).choose_spec.choose_spec

lemma coe_vsToPlace (p : X) (a : stalkVS k p) :
    ((vsToPlace D eL hk p a : ratPlace D eL hk p) : Ω) = embK D X eL hk a := rfl

include hk in
lemma algebraMap_mem_ratPlace (p : X) (c : k) : algebraMap k Ω c ∈ ratPlace D eL hk p := by
  rw [← (embK D X eL hk).commutes c]
  exact stalkVSToΩ_mem D eL hk p ⟨_, algebraMap_mem_stalkValuationSubring k _ p c⟩

/-- **Domination**: `A ∩ K(X) = 𝒪_{X,p}`. -/
lemma comapK_ratPlace (p : X) : comapK D X eL hk (ratPlace D eL hk p) = stalkVS k p := by
  set O := stalkVS k p
  set f := stalkVSToΩ D eL hk p
  apply le_antisymm
  · intro z hz
    by_contra hzO
    have hz0 : z ≠ 0 := fun h ↦ hzO (h ▸ zero_mem O)
    have hzi : z⁻¹ ∈ O := (O.mem_or_inv_mem z).resolve_left hzO
    have hu : IsUnit (vsToPlace D eL hk p ⟨z⁻¹, hzi⟩) := by
      refine IsUnit.of_mul_eq_one ⟨_, hz⟩ (Subtype.ext ?_)
      change (embK D X eL hk) z⁻¹ * (embK D X eL hk) z = 1
      rw [map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hz0)]
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ((IsLocalHom.map_nonunit _) hu)
    have hb' : z⁻¹ * (b : X.functionField) = 1 := congrArg Subtype.val hb
    rw [inv_mul_eq_one₀ hz0] at hb'
    exact hzO (hb' ▸ b.2)
  · intro z hz
    exact stalkVSToΩ_mem D eL hk p ⟨z, hz⟩

/-- `𝒪_{X,p} ≅ O_p ⊆ K(X)`. -/
abbrev stalkToVS (p : X) : X.presheaf.stalk p ⟶ CommRingCat.of (stalkVS k p) :=
  stalkToValuationSubring (valuationRing_stalk_of_isCurveOver k X) p rfl

/-- **The morphism `Spec A ⟶ Spec 𝒪_{X,p} ⟶ X`.** -/
def placeMor (p : X) : Spec (.of (ratPlace D eL hk p)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (vsToPlace D eL hk p)) ≫ Spec.map (stalkToVS (k := k) p) ≫
    X.fromSpecStalk p

/-- The generic geometric point of `Spec A ⟶ X` is the geometric generic point of `X`. -/
lemma vGen_placeMor (p : X) :
    FiniteEtale.vGen (ratPlace D eL hk p) ≫ placeMor D eL hk p = geometricGenericPoint D X eL := by
  have h1 : FiniteEtale.vGen (ratPlace D eL hk p) ≫
      Spec.map (CommRingCat.ofHom (vsToPlace D eL hk p)) =
      Spec.map (CommRingCat.ofHom ((algebraMap D.L Ω).comp eL.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (stalkVS k p) X.functionField)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [placeMor, ← Category.assoc, h1, Category.assoc,
    SpecMap_stalkToValuationSubring_fromSpecStalk, geometricGenericPoint]

/-- The algebra structure `resAlg` on `κ(A)` for the place of a rational point. -/
abbrev placeAlg (p : X) : Algebra k (ResidueField (ratPlace D eL hk p)) :=
  CurvesJacobian.Kummer.resAlg (ratPlace D eL hk p) (algebraMap_mem_ratPlace D eL hk p)

/-- `𝒪_{X,p} → A`. -/
def stalkToPlace (p : X) : X.presheaf.stalk p →+* ratPlace D eL hk p :=
  (vsToPlace D eL hk p).comp (stalkToVS (k := k) p).hom

instance (p : X) : IsLocalHom (stalkToPlace D eL hk p) := by
  unfold stalkToPlace
  infer_instance

lemma coe_stalkToPlace (p : X) (s : X.presheaf.stalk p) :
    ((stalkToPlace D eL hk p s : ratPlace D eL hk p) : Ω) =
      embK D X eL hk (algebraMap (X.presheaf.stalk p) X.functionField s) := rfl

include hx in
/-- **Residues at a rational point**: `𝒪_{X,p} → A → κ(A)` is `𝒪_{X,p} →φ k → κ(A)`. -/
lemma residue_stalkToPlace (s : X.presheaf.stalk (ratPt x)) :
    letI := placeAlg D eL hk (ratPt x)
    residue _ (stalkToPlace D eL hk (ratPt x) s) =
      algebraMap k _ ((Scheme.stalkClosedPointTo x).hom s) := by
  letI := placeAlg D eL hk (ratPt x)
  let p := ratPt x
  let φ := (Scheme.stalkClosedPointTo x).hom
  let ρ := stalkToPlace D eL hk p
  have hconst : ∀ c : k, residue _ (ρ (stalkConst p c)) = algebraMap k _ c := by
    intro c
    have h1 : ((ρ (stalkConst p c) : ratPlace D eL hk p) : Ω) = algebraMap k Ω c := by
      rw [coe_stalkToPlace]
      change embK D X eL hk (algebraMap (X.presheaf.stalk p) X.functionField
        ((X.presheaf.germ ⊤ p trivial).hom ((X ↘ Spec (CommRingCat.of k)).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)))) = _
      rw [algebraMap_stalk_functionField_germ]
      exact (embK D X eL hk).commutes c
    rw [show ρ (stalkConst p c) = ⟨algebraMap k Ω c, algebraMap_mem_ratPlace D eL hk p c⟩ from
      Subtype.ext h1]
    rfl
  have hm : ∀ s', φ s' = 0 → residue _ (ρ s') = 0 := by
    intro s' hs'
    rw [residue_eq_zero_iff]
    refine map_nonunit ρ s' fun hu ↦ ?_
    have := hu.map φ
    rw [hs'] at this
    exact not_isUnit_zero this
  have h0 : φ (s - stalkConst p (φ s)) = 0 := by
    rw [map_sub, stalkClosedPointTo_stalkConst x hx, sub_self]
  calc residue _ (ρ s) = residue _ (ρ (s - stalkConst p (φ s))) +
        residue _ (ρ (stalkConst p (φ s))) := by rw [← map_add, ← map_add, sub_add_cancel]
    _ = _ := by rw [hm _ h0, zero_add, hconst]

include hx in
/-- **The closed point of `Spec A ⟶ X` is the rational point**:
`Spec κ(A) ⟶ Spec A ⟶ X` equals `Spec κ(A) ⟶ Spec k ⟶ X`. -/
lemma closed_placeMor :
    letI := placeAlg D eL hk (ratPt x)
    Spec.map (CommRingCat.ofHom (residue (ratPlace D eL hk (ratPt x)))) ≫
        placeMor D eL hk (ratPt x) =
      Spec.map (CommRingCat.ofHom (algebraMap k (ResidueField (ratPlace D eL hk (ratPt x))))) ≫
        x := by
  letI := placeAlg D eL hk (ratPt x)
  have hring : stalkToVS (k := k) (ratPt x) ≫ CommRingCat.ofHom (vsToPlace D eL hk (ratPt x)) ≫
      CommRingCat.ofHom (residue (ratPlace D eL hk (ratPt x))) =
      Scheme.stalkClosedPointTo x ≫
        CommRingCat.ofHom (algebraMap k (ResidueField (ratPlace D eL hk (ratPt x)))) := by
    ext s
    exact residue_stalkToPlace D eL hk x hx s
  calc _ = Spec.map (stalkToVS (k := k) (ratPt x) ≫
          CommRingCat.ofHom (vsToPlace D eL hk (ratPt x)) ≫
          CommRingCat.ofHom (residue (ratPlace D eL hk (ratPt x)))) ≫
        X.fromSpecStalk (ratPt x) := by
        simp only [placeMor, Spec.map_comp, Category.assoc]
    _ = _ := by
        rw [hring, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

include hx in
/-- Residues of functions at a rational point are rational. -/
lemma ratPlace_hrat (hHL : D.HL = D.H) :
    letI := placeAlg D eL hk (ratPt x)
    ∀ (a : F D) (ha : (a : Ω) ∈ ratPlace D eL hk (ratPt x)),
      ∃ c : k, residue _ ⟨_, ha⟩ = algebraMap k (ResidueField (ratPlace D eL hk (ratPt x))) c := by
  letI := placeAlg D eL hk (ratPt x)
  intro a ha
  have haL : (a : Ω) ∈ D.L := by
    have := a.2
    unfold GaloisData.L
    rwa [hHL]
  set f : X.functionField := eL.symm ⟨a, haL⟩
  have hf : ((eL f : D.L) : Ω) = a := by simp [f]
  have hfO : f ∈ stalkVS k (ratPt x) := by
    rw [← comapK_ratPlace D eL hk (ratPt x), ValuationSubring.mem_comap]
    change ((eL f : D.L) : Ω) ∈ ratPlace D eL hk (ratPt x)
    rw [hf]
    exact ha
  obtain ⟨s, hs⟩ := hfO
  refine ⟨(Scheme.stalkClosedPointTo x).hom s, ?_⟩
  rw [← residue_stalkToPlace D eL hk x hx s]
  congr 1
  apply Subtype.ext
  rw [coe_stalkToPlace]
  rw [embK_apply]
  change (a : Ω) = ((eL (algebraMap _ _ s) : D.L) : Ω)
  rw [show algebraMap _ X.functionField s = f from hs, hf]

variable [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- **A `k`-rational point of `X` as a rational point of the Galois model** (`H_L = H`): the
place `A = ratPlace` dominating `𝒪_{X,p}`. -/
def ratPointOf (hHL : D.HL = D.H) : RatPoint D where
  A := ratPlace D eL hk (ratPt x)
  hk := algebraMap_mem_ratPlace D eL hk _
  isIntegral := by
    letI := placeAlg D eL hk (ratPt x)
    haveI : Algebra.IsAlgebraic (F D) Ω :=
      Algebra.IsAlgebraic.tower_top (K := K₀ k t) (L := F D) (A := Ω)
    exact isIntegral_residueField_of_rational (E := F D) _ (ratPlace_hrat D eL hk x hx hHL)
  hrat := ratPlace_hrat D eL hk x hx hHL

omit [IsAlgClosed Ω] in
lemma ratPointOf_A (hHL : D.HL = D.H) :
    (ratPointOf D eL hk x hx hHL).A = ratPlace D eL hk (ratPt x) := rfl

end Place

end CurvesJacobian.LocAn.SectionBridge
