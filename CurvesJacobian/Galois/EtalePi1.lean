/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.CurveCharts
import CurvesJacobian.Galois.PiCharacters
import Pi1.Orbifold.EtaleTwoCharts

/-!
# `π₁ᵉᵗ` of a proper curve is `Π_X`

Let `k` be algebraically closed of characteristic `0`, `D : GaloisData k t` Galois data with
`H = H_L` (`hH : D.H ≤ D.HL`), and `X` a curve over `k` (`Belyi.IsCurveOver`) together with a
`k`-isomorphism `eL : K(X) ≃ L = Ω^{H_L}` sending a rational function `τ` to `t`. Then

`CurvesJacobian.etalePi1EquivPiX : π₁ᵉᵗ(X, ξ) ≃ₜ* Π_X = H ⧸ ⟨⟨SAll D⟩⟩`

at the geometric generic point `ξ : Spec Ω ⟶ Spec L ≅ Spec K(X) ⟶ X`
(`CurvesJacobian.geometricGenericPoint`). This is SGA 1 V.8.2 for proper curves; the
characters of `Π_X` were related to `Pic⁰[n]` in `CurvesJacobian.picTorsionEquivPiChars`.

The proof applies pi1's two-chart étale van Kampen theorem in Galois form
(`Pi1.Orbifold.GaloisData.ker_chartHomX`) to the charts `U = π⁻¹ D₊(X₁)` and
`U' = π⁻¹ D₊(X₀)` of `π = toP1 τ : X ⟶ ℙ¹` (`CurvesJacobian.chartOne`, `chartZero`): their
rings of functions are the integral closures of `k[τ]` and `k[τ⁻¹]` in `K(X)`
(`mem_range_germ_chartOne_iff`), which `eL` identifies with the rings `D.R` and
`(D.transfer _ _).R` of pi1 (for `t' = t⁻¹`). The inertia elements over `k[t]` and `k[t⁻¹]`
together are all inertia elements (`GaloisData.S_union_Sat_inv`), i.e. `SAll D`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

namespace CurvesJacobian

section Algebra

/-- Integrality over `k[s]` is preserved and reflected by an injective `k`-algebra map. -/
lemma isIntegral_adjoin_map_iff {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K]
    [Algebra k Ω] (f : K →ₐ[k] Ω) (s z : K) :
    IsIntegral (Algebra.adjoin k {s}) z ↔ IsIntegral (Algebra.adjoin k {f s}) (f z) := by
  have hf : Function.Injective f := f.toRingHom.injective
  have hmap : (Algebra.adjoin k {s}).map f = Algebra.adjoin k {f s} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let ψ : Algebra.adjoin k {s} ≃ₐ[k] Algebra.adjoin k {f s} :=
    (Subalgebra.equivMapOfInjective _ f hf).trans (Subalgebra.equivOfEq _ _ hmap)
  have hψ : ∀ b, ((ψ b : Algebra.adjoin k {f s}) : Ω) = f b := fun _ => rfl
  constructor
  · rintro ⟨p, hpm, hp⟩
    refine ⟨p.map ψ.toRingEquiv.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap (Algebra.adjoin k {f s}) Ω).comp ψ.toRingEquiv.toRingHom =
        f.toRingHom.comp (algebraMap (Algebra.adjoin k {s}) K) :=
      RingHom.ext fun b => hψ b
    rw [hc]
    change Polynomial.eval₂ ((f : K →+* Ω).comp _) ((f : K →+* Ω) z) p = 0
    rw [← Polynomial.hom_eval₂, hp, map_zero]
  · rintro ⟨p, hpm, hp⟩
    refine ⟨p.map ψ.symm.toRingEquiv.toRingHom, hpm.map _, hf ?_⟩
    rw [map_zero]
    change f (Polynomial.eval₂ (algebraMap (Algebra.adjoin k {s}) K) z
      (p.map ψ.symm.toRingEquiv.toRingHom)) = 0
    rw [Polynomial.eval₂_map]
    change f.toRingHom (Polynomial.eval₂ _ z p) = 0
    rw [Polynomial.hom_eval₂]
    have hc : f.toRingHom.comp ((algebraMap (Algebra.adjoin k {s}) K).comp
        ψ.symm.toRingEquiv.toRingHom) = algebraMap (Algebra.adjoin k {f s}) Ω := by
      refine RingHom.ext fun b => ?_
      change f (ψ.symm b : K) = (b : Ω)
      rw [← hψ, AlgEquiv.apply_symm_apply]
    rw [hc]
    exact hp

/-- A ring isomorphism between two subrings of `L` given as ranges of injective maps. -/
def ringEquivOfRangeEq {A B L : Type u} [CommRing A] [CommRing B] [CommRing L] (f : A →+* L)
    (g : B →+* L) (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ y, y ∈ Set.range f ↔ y ∈ Set.range g) : A ≃+* B :=
  (RingEquiv.ofBijective f.rangeRestrict ⟨fun _ _ e => hf (congrArg Subtype.val e),
    f.rangeRestrict_surjective⟩).trans
  ((RingEquiv.subringCongr (SetLike.ext h)).trans
    (RingEquiv.ofBijective g.rangeRestrict ⟨fun _ _ e => hg (congrArg Subtype.val e),
      g.rangeRestrict_surjective⟩).symm)

lemma ringEquivOfRangeEq_apply {A B L : Type u} [CommRing A] [CommRing B] [CommRing L]
    (f : A →+* L) (g : B →+* L) (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ y, y ∈ Set.range f ↔ y ∈ Set.range g) (a : A) :
    g (ringEquivOfRangeEq f g hf hg h a) = f a := by
  set b := ringEquivOfRangeEq f g hf hg h a
  have : g.rangeRestrict b = ⟨f a, (h (f a)).mp ⟨a, rfl⟩⟩ := by
    simp only [b, ringEquivOfRangeEq, RingEquiv.trans_apply]
    exact (RingEquiv.ofBijective g.rangeRestrict _).apply_symm_apply _
  exact congrArg Subtype.val this

end Algebra

section Charts

variable {X : Scheme.{u}} [IsIntegral X]

/-- The generic point `Spec K(X) ⟶ X` factors through every nonempty open. -/
lemma range_fromSpecStalk_genericPoint_subset (V : X.Opens) [Nonempty V] :
    Set.range (X.fromSpecStalk (genericPoint X)).base ⊆ Set.range V.ι.base := by
  rw [Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
  intro y hy
  exact hy.mem_open V.2 (genericPoint_mem_of_nonempty V)

/-- The generic point `Spec K(X) ⟶ V` of a nonempty open `V`. -/
def genericToOpen (V : X.Opens) [Nonempty V] : Spec X.functionField ⟶ V :=
  IsOpenImmersion.lift V.ι _ (range_fromSpecStalk_genericPoint_subset V)

@[reassoc (attr := simp)]
lemma genericToOpen_ι (V : X.Opens) [Nonempty V] :
    genericToOpen V ≫ V.ι = X.fromSpecStalk (genericPoint X) :=
  IsOpenImmersion.lift_fac _ _ _

lemma genericToOpen_homOfLE_isoSpec_hom {W V : X.Opens} [Nonempty V] [Nonempty W]
    (hVW : V ≤ W) (hW : IsAffineOpen W) :
    genericToOpen V ≫ X.homOfLE hVW ≫ hW.isoSpec.hom = Spec.map (X.germToFunctionField W) := by
  have hg : genericPoint X ∈ W := genericPoint_mem_of_nonempty W
  rw [← cancel_mono (hW.isoSpec.inv ≫ W.ι), Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, Scheme.homOfLE_ι, genericToOpen_ι, IsAffineOpen.isoSpec_inv_ι,
    ← hW.fromSpecStalk_eq_fromSpecStalk hg]
  rfl

/-- The chart `W ≅ Spec Γ(X, W) ≅ Spec R` attached to a ring isomorphism `ψ : Γ(X, W) ≅ R`. -/
def chartIso {W : X.Opens} (hW : IsAffineOpen W) {R : CommRingCat.{u}} (ψ : Γ(X, W) ≅ R) :
    (W : Scheme.{u}) ≅ Spec R :=
  hW.isoSpec ≪≫ Scheme.Spec.mapIso ψ.symm.op

/-- Compatibility of `chartIso` with the generic points. -/
lemma genericToOpen_homOfLE_chartIso {W V : X.Opens} [Nonempty V] [Nonempty W] (hVW : V ≤ W)
    (hW : IsAffineOpen W) {R L : CommRingCat.{u}} (ψ : Γ(X, W) ≅ R) (a : R ⟶ L)
    (eL : X.functionField ⟶ L) (h : ψ.hom ≫ a = X.germToFunctionField W ≫ eL) :
    Spec.map eL ≫ genericToOpen V ≫ X.homOfLE hVW ≫ (chartIso hW ψ).hom = Spec.map a := by
  have hg : genericPoint X ∈ W := genericPoint_mem_of_nonempty W
  have key : genericToOpen V ≫ X.homOfLE hVW ≫ hW.isoSpec.hom =
      Spec.map (X.germToFunctionField W) := by
    rw [← cancel_mono (hW.isoSpec.inv ≫ W.ι), Category.assoc, Category.assoc,
      Iso.hom_inv_id_assoc, Scheme.homOfLE_ι, genericToOpen_ι, IsAffineOpen.isoSpec_inv_ι,
      ← hW.fromSpecStalk_eq_fromSpecStalk hg]
    rfl
  have ha : a = ψ.inv ≫ X.germToFunctionField W ≫ eL := by
    rw [← h, Iso.inv_hom_id_assoc]
  simp only [chartIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [ha, Spec.map_comp, Spec.map_comp, ← key]
  simp only [Category.assoc]


/-- **`π₁ᵉᵗ(Spec K(X)) ↠ π₁ᵉᵗ(V)`** for a nonempty affine open `V` of an integral scheme with
integrally closed stalks (through any field isomorphic to `K(X)`). -/
lemma fundamentalGroupMap_genericToOpen_surjective {V : X.Opens} [Nonempty V]
    (hV : IsAffineOpen V) (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) {L : Type u}
    [Field L] (e : X.functionField ≃+* L) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x₀ : Spec (.of Ω) ⟶ Spec (.of L)) :
    Function.Surjective (fundamentalGroupMap
      (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ genericToOpen V) (rfl : x₀ ≫ _ = _)) := by
  set φ : Γ(X, V) ⟶ CommRingCat.of L :=
    X.germToFunctionField V ≫ CommRingCat.ofHom e.toRingHom with hφ
  have hiso : genericToOpen V ≫ hV.isoSpec.hom = Spec.map (X.germToFunctionField V) := by
    have := genericToOpen_homOfLE_isoSpec_hom (le_refl V) hV
    rwa [Scheme.homOfLE_rfl, Category.id_comp] at this
  have hjeq : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ genericToOpen V =
      Spec.map φ ≫ hV.isoSpec.inv := by
    rw [← cancel_mono hV.isoSpec.hom, Category.assoc, Category.assoc, hiso, Iso.inv_hom_id,
      Category.comp_id, hφ, Spec.map_comp]
    rfl
  have hinj : Function.Injective φ :=
    e.injective.comp (X.germToFunctionField_injective V)
  haveI := isIntegrallyClosed_of_isAffineOpen hV (fun x _ => hX x)
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV
  have hint : ∀ s : L, (letI := φ.hom.toAlgebra; _root_.IsIntegral Γ(X, V) s) →
      s ∈ Set.range φ := by
    intro s hs
    obtain ⟨p, hpm, hp⟩ := hs
    have hz : _root_.IsIntegral Γ(X, V) (e.symm s) := by
      refine ⟨p, hpm, e.injective ?_⟩
      rw [map_zero, ← hp]
      change e.toRingHom (Polynomial.eval₂ (X.germToFunctionField V).hom (e.symm s) p) = _
      rw [Polynomial.hom_eval₂]
      change Polynomial.eval₂ (e.toRingHom.comp (X.germToFunctionField V).hom)
        (e (e.symm s)) p = _
      rw [RingEquiv.apply_symm_apply]
      rfl
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hz
    refine ⟨a, ?_⟩
    change e (X.germToFunctionField V a) = s
    change e (algebraMap Γ(X, V) X.functionField a) = s
    rw [ha, RingEquiv.apply_symm_apply]
  haveI : IsIso (Spec.map φ).fromNormalization := isIso_fromNormalization_specMap φ hinj hint
  haveI : ConnectedSpace V := connectedSpace_opens_of_isIntegral V
  haveI : IsAffine V := hV
  haveI : ConnectedSpace (Spec Γ(X, V)) :=
    (hV.isoSpec.hom.homeomorph.surjective).connectedSpace hV.isoSpec.hom.homeomorph.continuous
  have h1 := fundamentalGroupMap_surjective_of_isIso_fromNormalization (Spec.map φ)
    (rfl : x₀ ≫ Spec.map φ = _)
  have h2 : x₀ ≫ Spec.map φ ≫ hV.isoSpec.inv =
      x₀ ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫ genericToOpen V := by
    rw [← hjeq]
  rw [fundamentalGroupMap_congr hjeq _ h2]
  have h3 : (x₀ ≫ Spec.map φ) ≫ hV.isoSpec.inv =
      x₀ ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫ genericToOpen V := by
    rw [Category.assoc]; exact h2
  have hc := fundamentalGroupMap_comp (Spec.map φ) hV.isoSpec.inv
    (rfl : x₀ ≫ Spec.map φ = _) h3 h2
  intro y
  obtain ⟨z, hz⟩ := (fundamentalGroupMap_bijective_of_isIso hV.isoSpec.inv h3).2 y
  obtain ⟨w, rfl⟩ := h1 z
  exact ⟨w, by rw [hc]; exact hz⟩

end Charts

section Main

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)

/-- Membership in the coordinate ring `R ⊆ L`: integrality over `k[t]`. -/
lemma mem_range_algebraMap_L_iff (E : GaloisData k t) (y : E.L) :
    y ∈ Set.range (algebraMap E.R E.L) ↔ IsIntegral (A₀ k t) (y : Ω) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact CoordRing.isIntegral_algebraMap r
  · intro h
    exact ⟨CoordRing.mk (y : Ω) y.2 h, Subtype.ext rfl⟩

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)

/-- `K(X) ≅ L ⊆ Ω` as a `k`-algebra map. -/
def embK : X.functionField →ₐ[k] Ω :=
  { (algebraMap D.L Ω).comp eL.toRingHom with commutes' := hk }

lemma embK_apply (z : X.functionField) : embK D X eL hk z = ((eL z : D.L) : Ω) := rfl

include hk in
lemma transcendental_of_embK {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t) :
    Transcendental k τ := fun h => D.transcendental (by
  rw [← hτ, ← embK_apply D X eL hk]
  exact (isAlgebraic_algHom_iff (embK D X eL hk) (embK D X eL hk).toRingHom.injective).mpr h)

section Pi1

open Pi1.Orbifold.GaloisData in
/-- `k(t⁻¹) = k(t)`. -/
lemma K₀_eq_K₀_inv : K₀ k t = K₀ k t⁻¹ := IntermediateField.ext mem_K₀_inv_iff

/-- `Ω` is Galois over `k(t⁻¹) = k(t)`. -/
lemma isGalois_K₀_inv [IsGalois (K₀ k t) Ω] : IsGalois (K₀ k t⁻¹) Ω :=
  K₀_eq_K₀_inv (k := k) (t := t) ▸ inferInstance

attribute [local instance] isGalois_K₀_inv

lemma transcendental_inv_of (E : GaloisData k t) : Transcendental k t⁻¹ := fun h =>
  E.transcendental (IsAlgebraic.inv_iff.mp h)

variable [IsGalois (K₀ k t) Ω]

/-- The Galois data `D` seen from `t⁻¹` (pi1's `GaloisData.transfer`). -/
abbrev invData : GaloisData k t⁻¹ :=
  D.transfer Pi1.Orbifold.GaloisData.mem_K₀_inv_iff (transcendental_inv_of D)

/-- `L` seen as the function field of `invData D`. -/
def invL : D.L ≃+* (invData D).L where
  toFun x := ⟨x.1, (D.mem_transfer_L _ _ _).2 x.2⟩
  invFun x := ⟨x.1, (D.mem_transfer_L _ _ _).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl


variable {τ : X.functionField}
  (hτ : ((eL τ : D.L) : Ω) = t)

omit [IsGalois (K₀ k t) Ω] in
include hk hτ in
lemma isIntegral_iff_one (z : X.functionField) :
    IsIntegral (Algebra.adjoin k {τ}) z ↔ IsIntegral (A₀ k t) ((eL z : D.L) : Ω) := by
  rw [isIntegral_adjoin_map_iff (embK D X eL hk) τ z, embK_apply, hτ]
  rfl

omit [IsGalois (K₀ k t) Ω] in
include hk hτ in
lemma isIntegral_iff_zero (z : X.functionField) :
    IsIntegral (Algebra.adjoin k {τ⁻¹}) z ↔ IsIntegral (A₀ k t⁻¹) ((eL z : D.L) : Ω) := by
  rw [isIntegral_adjoin_map_iff (embK D X eL hk) τ⁻¹ z, map_inv₀, embK_apply, hτ]
  rfl

omit [IsGalois (K₀ k t) Ω] in
include hk hτ in
lemma ne_zero_of_embK : τ ≠ 0 := by
  rintro rfl
  exact transcendental_of_embK D X eL hk hτ isAlgebraic_zero

variable [IsAlgClosed k] [CharZero k] [IsCurveOver k X]

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed k] in
lemma nonempty_chartZero_of_ne_zero (hτ0 : τ ≠ 0) : Nonempty (chartZero k X τ) :=
  ⟨⟨_, genericPoint_mem_chartZero hτ0⟩⟩

/-- `Γ(π⁻¹ D₊(X₁)) ≅ R` (the integral closure of `k[t]` in `L`). -/
def chartOneEquiv : Γ(X, chartOne k X τ) ≃+* D.R :=
  ringEquivOfRangeEq (eL.toRingHom.comp (X.germToFunctionField (chartOne k X τ)).hom)
    (algebraMap D.R D.L)
    (eL.injective.comp (X.germToFunctionField_injective _)) D.algebraMap_L_injective
    fun y => by
      rw [mem_range_algebraMap_L_iff]
      constructor
      · rintro ⟨a, rfl⟩
        exact (isIntegral_iff_one D X eL hk hτ _).mp
          ((mem_range_germ_chartOne_iff (transcendental_of_embK D X eL hk hτ) _).mp ⟨a, rfl⟩)
      · intro h
        have h' : IsIntegral (A₀ k t) ((eL (eL.symm y) : D.L) : Ω) := by
          rwa [RingEquiv.apply_symm_apply]
        obtain ⟨a, ha⟩ := (mem_range_germ_chartOne_iff (transcendental_of_embK D X eL hk hτ) _).mpr
          ((isIntegral_iff_one D X eL hk hτ _).mpr h')
        exact ⟨a, by simp [ha]⟩

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed k] in
lemma algebraMap_chartOneEquiv (a : Γ(X, chartOne k X τ)) :
    algebraMap D.R D.L (chartOneEquiv D X eL hk hτ a) =
      eL (X.germToFunctionField (chartOne k X τ) a) :=
  ringEquivOfRangeEq_apply _ _ _ _ _ a

/-- `Γ(π⁻¹ D₊(X₀)) ≅ R'` (the integral closure of `k[t⁻¹]` in `L`). -/
def chartZeroEquiv :
    haveI := nonempty_chartZero_of_ne_zero (k := k) X (ne_zero_of_embK D X eL hk hτ)
    Γ(X, chartZero k X τ) ≃+* (invData D).R :=
  haveI := nonempty_chartZero_of_ne_zero (k := k) X (ne_zero_of_embK D X eL hk hτ)
  ringEquivOfRangeEq
    ((eL.trans (invL D)).toRingHom.comp (X.germToFunctionField (chartZero k X τ)).hom)
    (algebraMap (invData D).R (invData D).L)
    ((eL.trans (invL D)).injective.comp (X.germToFunctionField_injective _))
    (invData D).algebraMap_L_injective
    fun y => by
      rw [mem_range_algebraMap_L_iff]
      constructor
      · rintro ⟨a, rfl⟩
        exact (isIntegral_iff_zero D X eL hk hτ _).mp
          ((mem_range_germ_chartZero_iff (transcendental_of_embK D X eL hk hτ) _).mp ⟨a, rfl⟩)
      · intro h
        have e : eL ((eL.trans (invL D)).symm y) = (invL D).symm y := by
          rw [RingEquiv.symm_trans_apply, RingEquiv.apply_symm_apply]
        have h' : IsIntegral (A₀ k t⁻¹) ((eL ((eL.trans (invL D)).symm y) : D.L) : Ω) := by
          rw [e]
          exact h
        obtain ⟨a, ha⟩ := (mem_range_germ_chartZero_iff (transcendental_of_embK D X eL hk hτ)
          _).mpr ((isIntegral_iff_zero D X eL hk hτ _).mpr h')
        refine ⟨a, ?_⟩
        change (eL.trans (invL D)) _ = y
        rw [ha, RingEquiv.apply_symm_apply]

omit [IsAlgClosed k] in
lemma algebraMap_chartZeroEquiv :
    haveI := nonempty_chartZero_of_ne_zero (k := k) X (ne_zero_of_embK D X eL hk hτ)
    ∀ a : Γ(X, chartZero k X τ),
      algebraMap (invData D).R (invData D).L (chartZeroEquiv D X eL hk hτ a) =
        (eL.trans (invL D)) (X.germToFunctionField (chartZero k X τ) a) :=
  haveI := nonempty_chartZero_of_ne_zero (k := k) X (ne_zero_of_embK D X eL hk hτ)
  fun a => ringEquivOfRangeEq_apply _ _ _ _ _ a

/-- The geometric generic point `Spec Ω ⟶ Spec L ≅ Spec K(X) ⟶ X`. -/
def geometricGenericPoint : Spec (.of Ω) ⟶ X :=
  Spec.map (CommRingCat.ofHom ((algebraMap D.L Ω).comp eL.toRingHom)) ≫
    X.fromSpecStalk (genericPoint X)

/-- `π₁ᵉᵗ` at equal geometric points. -/
def fundamentalGroupCongr {Y : Scheme.{u}} {x₁ x₂ : Spec (.of Ω) ⟶ Y} (h : x₁ = x₂) :
    π₁ᵉᵗ(x₁) ≃ₜ* π₁ᵉᵗ(x₂) := by
  subst h
  exact ContinuousMulEquiv.refl _

variable [IsSepClosed Ω] (hH : D.H ≤ D.HL)

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed k] [CharZero k] [IsSepClosed Ω] in
include hH in
/-- The inertia elements over `k[t]` and over `k[t⁻¹]` are all inertia elements (`H = H_L`). -/
lemma S_union_Sat_inv_eq_SAll : D.S ∪ D.Sat t⁻¹ = SAll D := by
  rw [Pi1.Orbifold.GaloisData.S_union_Sat_inv]
  ext σ
  exact ⟨fun ⟨h1, h2⟩ => ⟨D.le h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hH h1, h2⟩⟩

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed k] [IsSepClosed Ω] in
include hk hτ in
lemma nonempty_chartOne_inf_chartZero :
    Nonempty ((chartOne k X τ ⊓ chartZero k X τ : X.Opens) : Scheme.{u}) :=
  ⟨⟨genericPoint X, genericPoint_mem_chartOne τ,
    genericPoint_mem_chartZero (ne_zero_of_embK D X eL hk hτ)⟩⟩

include hk hτ in
/-- The generic point `Spec L ≅ Spec K(X) ⟶ π⁻¹ D₊(X₁) ∩ π⁻¹ D₊(X₀)`. -/
def curveJ : Spec (.of D.L) ⟶ ((chartOne k X τ ⊓ chartZero k X τ : X.Opens) : Scheme.{u}) :=
  haveI := nonempty_chartOne_inf_chartZero D X eL hk hτ
  Spec.map (CommRingCat.ofHom eL.toRingHom) ≫ genericToOpen _

omit [IsAlgClosed k] in
/-- **Étale van Kampen for the two charts of a curve**: the kernel of the intrinsic Galois action
`H → π₁ᵉᵗ(X)` through the generic point is the closed normal subgroup generated by all inertia
elements (`H = H_L`). -/
theorem ker_curveChartHomX :
    (D.chartHomX hH (chartOne k X τ) (chartZero k X τ) (curveJ D X eL hk hτ)).ker =
      GaloisPi1.kernel D.H (SAll D) := by
  have hτT := transcendental_of_embK D X eL hk hτ
  have hτ0 := ne_zero_of_embK D X eL hk hτ
  haveI := nonempty_chartZero_of_ne_zero (k := k) X hτ0
  haveI := IsCurveOver.isLocallyNoetherian k X
  have hXc := IsCurveOver.isIntegrallyClosed_stalk k X
  have hU := isAffineOpen_chartOne (k := k) (X := X) hτT
  have hU' := isAffineOpen_chartZero (k := k) (X := X) hτT
  haveI hUU := nonempty_chartOne_inf_chartZero D X eL hk hτ
  haveI := connectedSpace_opens_of_isIntegral (chartOne k X τ)
  haveI := connectedSpace_opens_of_isIntegral (chartZero k X τ)
  haveI := connectedSpace_opens_of_isIntegral (chartOne k X τ ⊓ chartZero k X τ)
  haveI : IsIso (chartOne k X τ).ι.fromNormalization :=
    isIso_fromNormalization_of_isIntegrallyClosed _ (denseRange_of_isOpenImmersion _) hXc
  haveI : IsIso (incl₂ (chartOne k X τ) (chartZero k X τ)).fromNormalization :=
    haveI : AlgebraicGeometry.IsIntegral (chartZero k X τ : Scheme.{u}) :=
      isIntegral_of_isOpenImmersion (chartZero k X τ).ι
    isIso_fromNormalization_of_isIntegrallyClosed_opens _ _
      (denseRange_of_isOpenImmersion _) hXc
  let eU := chartIso hU (chartOneEquiv D X eL hk hτ).toCommRingCatIso
  let eU' := chartIso hU' (chartZeroEquiv D X eL hk hτ).toCommRingCatIso
  let j' : Spec (.of (invData D).L) ⟶
      ((chartOne k X τ ⊓ chartZero k X τ : X.Opens) : Scheme.{u}) :=
    Spec.map (CommRingCat.ofHom (eL.trans (invL D)).toRingHom) ≫ genericToOpen _
  have hj : curveJ D X eL hk hτ ≫ incl₁ _ _ ≫ eU.hom = D.genericPoint := by
    simp only [curveJ, Category.assoc]
    exact genericToOpen_homOfLE_chartIso inf_le_left hU _ _ _
      (CommRingCat.hom_ext (RingHom.ext fun a => algebraMap_chartOneEquiv D X eL hk hτ a))
  have hj' : j' ≫ incl₂ _ _ ≫ eU'.hom = (invData D).genericPoint := by
    simp only [j', Category.assoc]
    exact genericToOpen_homOfLE_chartIso inf_le_right hU' _ _ _
      (CommRingCat.hom_ext (RingHom.ext fun a => algebraMap_chartZeroEquiv D X eL hk hτ a))
  have hξ : specPoint (invData D).L Ω ≫ j' = specPoint D.L Ω ≫ curveJ D X eL hk hτ := by
    simp only [curveJ, j', ← Category.assoc, ← Spec.map_comp]
    rfl
  have hsurj := fundamentalGroupMap_genericToOpen_surjective
    (IsCurveOver.isAffineOpen_inf k X hU hU') hXc eL (specPoint D.L Ω)
  have hker := D.ker_chartHomX hH (chartOne k X τ) (chartZero k X τ)
    Pi1.Orbifold.GaloisData.mem_K₀_inv_iff (transcendental_inv_of D) (chartOne_sup_chartZero τ)
    eU eU' (curveJ D X eL hk hτ) j' hj hj' hξ hsurj
  rwa [S_union_Sat_inv_eq_SAll D hH] at hker

omit [IsAlgClosed k] in
theorem curveChartHomX_surjective :
    Function.Surjective
      (D.chartHomX hH (chartOne k X τ) (chartZero k X τ) (curveJ D X eL hk hτ)) := by
  have hτT := transcendental_of_embK D X eL hk hτ
  haveI := IsCurveOver.isLocallyNoetherian k X
  have hXc := IsCurveOver.isIntegrallyClosed_stalk k X
  have hU := isAffineOpen_chartOne (k := k) (X := X) hτT
  haveI := nonempty_chartOne_inf_chartZero D X eL hk hτ
  haveI := connectedSpace_opens_of_isIntegral (chartOne k X τ)
  haveI := connectedSpace_opens_of_isIntegral (chartOne k X τ ⊓ chartZero k X τ)
  haveI : IsIso (chartOne k X τ).ι.fromNormalization :=
    isIso_fromNormalization_of_isIntegrallyClosed _ (denseRange_of_isOpenImmersion _) hXc
  let eU := chartIso hU (chartOneEquiv D X eL hk hτ).toCommRingCatIso
  have hj : curveJ D X eL hk hτ ≫ incl₁ _ _ ≫ eU.hom = D.genericPoint := by
    simp only [curveJ, Category.assoc]
    exact genericToOpen_homOfLE_chartIso inf_le_left hU _ _ _
      (CommRingCat.hom_ext (RingHom.ext fun a => algebraMap_chartOneEquiv D X eL hk hτ a))
  exact D.chartHomX_surjective hH _ _ eU _ hj

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed k] [IsSepClosed Ω] in
lemma curveJ_basePoint :
    ((specPoint D.L Ω ≫ curveJ D X eL hk hτ) ≫ incl₁ _ _) ≫ (chartOne k X τ).ι =
      geometricGenericPoint D X eL := by
  simp only [curveJ, geometricGenericPoint, Category.assoc, Scheme.homOfLE_ι, genericToOpen_ι]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- **`π₁ᵉᵗ` of a proper curve is `Π_X`** (SGA 1 V.8.2): for a curve `X` over `k` with
`K(X) ≅ L` (`τ ↦ t`), the étale fundamental group of `X` at the geometric generic point is
`H ⧸ ⟨⟨SAll D⟩⟩`. See the module docstring. -/
def etalePi1EquivPiX :
    π₁ᵉᵗ(geometricGenericPoint D X eL) ≃ₜ* GaloisPi1.pi1 D.H (SAll D) D.isClosed_H :=
  (fundamentalGroupCongr (curveJ_basePoint D X eL hk hτ)).symm.trans
    (GaloisPi1.equivOfSurjective D.H D.isClosed_H (SAll D)
      (D.chartHomX hH (chartOne k X τ) (chartZero k X τ) (curveJ D X eL hk hτ))
      (D.continuous_chartHomX hH _ _ _) (curveChartHomX_surjective D X eL hk hτ hH)
      (ker_curveChartHomX D X eL hk hτ hH))

/-- **`π₁ᵉᵗ(X) ≃ₜ* Π_X`**: `etalePi1EquivPiX` with target `CurvesJacobian.PiX D`. -/
def etalePi1EquivPiX' : π₁ᵉᵗ(geometricGenericPoint D X eL) ≃ₜ* PiX D :=
  etalePi1EquivPiX D X eL hk hτ hH

end Pi1

end Main

end CurvesJacobian

end
