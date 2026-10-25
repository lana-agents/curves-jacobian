/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SectionBridgePlace

/-!
# The section of a rational point: `π₁ᵉᵗ` versus the Galois model

Setting of `LocAn/SectionBridgePlace.lean` (`H_L = H`, `Ω` algebraically closed, Galois over
`k(t)`), and `x : Spec k ⟶ X` a `k`-rational point with place `A` (`ratPointOf`).

* `CurvesJacobian.LocAn.SectionBridge.specPath`: the specialisation path
  `fiber η̄ ≅ fiber (Spec κ(A) ⟶ Spec k ⟶ X)` from the geometric generic point `η̄` (through
  `Spec A ⟶ X`, `FiniteEtale.spIso`);
* `specPath_conjAut`: it conjugates the action of `τ ∈ D_A` at `η̄` into the action of its image
  `τ̄ ∈ Gal(κ(A)/k)` through `x` (equivariance of specialisation);
* `kbarPath`: the same path followed by `κ(A) ≅ k̄` (`kbarEquiv`), ending at
  `Spec k̄ ⟶ Spec k ⟶ X`;
* `schSection x : G_k → π₁ᵉᵗ(X, η̄)`: the scheme-theoretic section `π₁ᵉᵗ(x)` (Galois action
  through `x`) transported to `η̄` along `kbarPath`;
* **`etalePi1EquivPiX'_schSection`**: under `π₁ᵉᵗ(X, η̄) ≃ Π_X` (`etalePi1EquivPiX'`), the section
  `schSection x` is the Galois-model section `xSectionGk` of the rational point `ratPointOf x`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi IsLocalRing Pi1.Orbifold
open AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace CurvesJacobian.LocAn.SectionBridge

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve

lemma conjAut_symm_conjAut {C : Type*} [Category C] {P Q : C} (α : P ≅ Q) (f : Aut P) :
    α.symm.conjAut (α.conjAut f) = f := by
  rw [← Iso.trans_conjAut, Iso.self_symm_id, Iso.conjAut_apply]
  simp

lemma conjAut_conjAut_symm {C : Type*} [Category C] {P Q : C} (α : P ≅ Q) (f : Aut Q) :
    α.conjAut (α.symm.conjAut f) = f := by
  simpa using conjAut_symm_conjAut α.symm f

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

instance isAlgClosed_residueField (x : RatPoint D) : IsAlgClosed (ResidueField x.A) :=
  IsAlgClosed.of_ringEquiv _ _ (kbarEquiv x.A x.hk x.hkres).toRingEquiv

instance isGalois_residueField (x : RatPoint D) : IsGalois k (ResidueField x.A) :=
  IsGalois.of_algEquiv (kbarEquiv x.A x.hk x.hkres)

end Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  [CharZero k] [IsCurveOver k X] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (x : Spec (.of k) ⟶ X) (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) (hHL : D.HL = D.H)

/-- The rational point of the Galois model attached to `x`. -/
abbrev xh : RatPoint D := ratPointOf D eL hk x hx hHL

omit [X.Over (Spec (CommRingCat.of k))] [CharZero k] [IsCurveOver k X] [IsGalois (K₀ k t) Ω]
  [IsAlgClosed Ω] in
lemma genericLX_point :
    Spec.map (CommRingCat.ofHom (algebraMap D.L Ω)) ≫ genericLX D X eL =
      geometricGenericPoint D X eL := by
  rw [genericLX, geometricGenericPoint, ← Category.assoc, ← Spec.map_comp]
  rfl

omit [IsAlgClosed Ω] in
/-- `vGen_placeMor` for the place of `x`. -/
lemma vGen_placeMor' :
    vGen (xh D eL hk x hx hHL).A ≫ placeMor D eL hk (ratPt x) = geometricGenericPoint D X eL :=
  vGen_placeMor D eL hk (ratPt x)

omit [IsAlgClosed Ω] in
/-- `closed_placeMor` for the place of `x`. -/
lemma closed_placeMor' :
    Spec.map (CommRingCat.ofHom (residue (xh D eL hk x hx hHL).A)) ≫ placeMor D eL hk (ratPt x) =
      Spec.map (CommRingCat.ofHom (algebraMap k (ResidueField (xh D eL hk x hx hHL).A))) ≫ x :=
  closed_placeMor D eL hk x hx

/-- **The specialisation path** `fiber η̄ ≅ fiber (Spec κ(A) ⟶ Spec k ⟶ X)`. -/
def specPath : fiber (geometricGenericPoint D X eL) ≅
    fiber (Spec.map (CommRingCat.ofHom (algebraMap k (ResidueField (xh D eL hk x hx hHL).A))) ≫
      x) :=
  eqToIso (congrArg fiber (vGen_placeMor' D eL hk x hx hHL).symm) ≪≫
    spIso (xh D eL hk x hx hHL).A (placeMor D eL hk (ratPt x))
      (Spec.map (CommRingCat.ofHom (residue (xh D eL hk x hx hHL).A))) ≪≫
    eqToIso (congrArg fiber (closed_placeMor' D eL hk x hx hHL))

/-- The automorphism of `A` given by an element of the decomposition group. -/
abbrev decompRingHom {A : ValuationSubring Ω} (τ : A.decompositionSubgroup (F D)) : A →+* A :=
  MulSemiringAction.toRingHom _ A τ

/-- **Specialisation is equivariant**: `specPath` conjugates the action of `τ ∈ D_A` at the
geometric generic point into the action of its image in `Gal(κ(A)/k)` through `x`. -/
theorem specPath_conjAut (τ : (xh D eL hk x hx hHL).A.decompositionSubgroup (F D)) :
    (specPath D eL hk x hx hHL).conjAut (galoisAction D.L (genericLX D X eL) (genericLX_point D eL)
      (D.toGalL (Subgroup.inclusion hHL.ge (ofGalF D τ.1)))) =
    galoisAction k x rfl (Decomposition.decompositionMap (F D) _ (xh D eL hk x hx hHL).hk
      (xh D eL hk x hx hHL).hkres τ) := by
  have hLF : ∀ z : Ω, z ∈ D.L → τ.1 z = z := fun z hz ↦ by
    have hz' : z ∈ F D := by
      have := hz
      unfold GaloisData.L at this
      rwa [hHL] at this
    exact τ.1.commutes ⟨z, hz'⟩
  have hφ : Spec.map (CommRingCat.ofHom (decompRingHom D τ)) ≫ placeMor D eL hk (ratPt x) =
      placeMor D eL hk (ratPt x) := by
    have e : CommRingCat.ofHom (vsToPlace D eL hk (ratPt x)) ≫
        CommRingCat.ofHom (decompRingHom D τ) =
          CommRingCat.ofHom (vsToPlace D eL hk (ratPt x)) := by
      ext o
      exact hLF _ (eL o.1).2
    have e' : Spec.map (CommRingCat.ofHom (decompRingHom D τ)) ≫
        Spec.map (CommRingCat.ofHom (vsToPlace D eL hk (ratPt x))) =
        Spec.map (CommRingCat.ofHom (vsToPlace D eL hk (ratPt x))) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map e
    rw [placeMor]
    exact (Category.assoc _ _ _).symm.trans (e' =≫ _)
  have h₁ : Spec.map (CommRingCat.ofHom ((D.toGalL (Subgroup.inclusion hHL.ge (ofGalF D τ.1)) :
      Ω ≃ₐ[D.L] Ω) : Ω →+* Ω)) ≫ vGen (xh D eL hk x hx hHL).A =
        vGen (xh D eL hk x hx hHL).A ≫ Spec.map (CommRingCat.ofHom (decompRingHom D τ)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    change (D.toGalL _) (a : Ω) = τ.1 (a : Ω)
    rw [GaloisData.toGalL_apply]
    exact ofGalF_apply D τ.1 a
  have h₂ : Spec.map (CommRingCat.ofHom ((Decomposition.decompositionMap (F D) _
      (xh D eL hk x hx hHL).hk (xh D eL hk x hx hHL).hkres τ :
        ResidueField (xh D eL hk x hx hHL).A ≃ₐ[k] ResidueField (xh D eL hk x hx hHL).A) :
        ResidueField (xh D eL hk x hx hHL).A →+* ResidueField (xh D eL hk x hx hHL).A)) ≫
          Spec.map (CommRingCat.ofHom (residue (xh D eL hk x hx hHL).A)) =
      Spec.map (CommRingCat.ofHom (residue (xh D eL hk x hx hHL).A)) ≫
        Spec.map (CommRingCat.ofHom (decompRingHom D τ)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  rw [specPath, Iso.trans_conjAut, Iso.trans_conjAut,
    eqToIso_conjAut_galoisAction D.L (genericLX D X eL) (vGen_placeMor' D eL hk x hx hHL).symm
      (genericLX_point D eL),
    spIso_conjAut_galoisAction (xh D eL hk x hx hHL).A (placeMor D eL hk (ratPt x))
      (Spec.map (CommRingCat.ofHom (residue (xh D eL hk x hx hHL).A))) D.L k (genericLX D X eL) x
      ((genericLX_point D eL).trans (vGen_placeMor' D eL hk x hx hHL).symm)
      (closed_placeMor' D eL hk x hx hHL).symm _ _ _ hφ h₁ h₂,
    eqToIso_conjAut_galoisAction k x (closed_placeMor' D eL hk x hx hHL)]

/-- `κ(A) ≅ k̄` for the place of `x`. -/
abbrev resEquiv : kbar k Ω ≃ₐ[k] ResidueField (xh D eL hk x hx hHL).A :=
  kbarEquiv (xh D eL hk x hx hHL).A (xh D eL hk x hx hHL).hk (xh D eL hk x hx hHL).hkres

lemma kbar_point :
    specHom ((resEquiv D eL hk x hx hHL).symm : ResidueField (xh D eL hk x hx hHL).A →+* kbar k Ω) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k (ResidueField (xh D eL hk x hx hHL).A))) ≫ x) =
      Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))) ≫ x := by
  rw [specHom, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext fun c ↦ (resEquiv D eL hk x hx hHL).symm.commutes c)

/-- **The path from the geometric generic point to `Spec k̄ ⟶ Spec k ⟶ X`**: `specPath`
followed by `κ(A) ≅ k̄`. -/
def kbarPath : fiber (geometricGenericPoint D X eL) ≅
    fiber (Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))) ≫ x) :=
  specPath D eL hk x hx hHL ≪≫
    fieldExtIso ((resEquiv D eL hk x hx hHL).symm :
      ResidueField (xh D eL hk x hx hHL).A →+* kbar k Ω) _ ≪≫
    eqToIso (congrArg fiber (kbar_point D eL hk x hx hHL))

theorem kbarPath_conjAut (τ : (xh D eL hk x hx hHL).A.decompositionSubgroup (F D)) :
    (kbarPath D eL hk x hx hHL).conjAut (galoisAction D.L (genericLX D X eL) (genericLX_point D eL)
      (D.toGalL (Subgroup.inclusion hHL.ge (ofGalF D τ.1)))) =
    galoisAction k x rfl (AlgEquiv.autCongr (resEquiv D eL hk x hx hHL).symm
      (Decomposition.decompositionMap (F D) _ (xh D eL hk x hx hHL).hk
        (xh D eL hk x hx hHL).hkres τ)) := by
  rw [kbarPath, Iso.trans_conjAut, Iso.trans_conjAut, specPath_conjAut]
  have := galoisAction_fieldExt ((resEquiv D eL hk x hx hHL).symm :
      ResidueField (xh D eL hk x hx hHL).A →+* kbar k Ω)
    (Spec.map (CommRingCat.ofHom (algebraMap k (ResidueField (xh D eL hk x hx hHL).A))) ≫ x)
    k k x x rfl (kbar_point D eL hk x hx hHL).symm
    (Decomposition.decompositionMap (F D) _ (xh D eL hk x hx hHL).hk
        (xh D eL hk x hx hHL).hkres τ)
    (AlgEquiv.autCongr (resEquiv D eL hk x hx hHL).symm
      (Decomposition.decompositionMap (F D) _ (xh D eL hk x hx hHL).hk
        (xh D eL hk x hx hHL).hkres τ)) (fun z ↦ by
        simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_symm,
          AlgEquiv.apply_symm_apply, RingHom.coe_coe])
  change (eqToIso _).conjAut (fieldExtEquiv _ _ _) = _
  rw [this, eqToIso_conjAut_galoisAction k x (kbar_point D eL hk x hx hHL)]

/-- **The section of a rational point**, scheme-theoretically: `π₁ᵉᵗ(x) : G_k = π₁ᵉᵗ(Spec k) →
π₁ᵉᵗ(X, Spec k̄ ⟶ Spec k ⟶ X)`, transported to the geometric generic point along `kbarPath`. -/
def schSection : Gk k Ω →* π₁ᵉᵗ(geometricGenericPoint D X eL) :=
  (kbarPath D eL hk x hx hHL).symm.conjAut.toMonoidHom.comp (galoisAction k x rfl)

omit [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- `π₁ᵉᵗ(X) ≃ Π_X` on the Galois action through the generic point. -/
lemma etalePi1EquivPiX'_galoisAction [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] {τ : X.functionField}
    (hτ : ((eL τ : D.L) : Ω) = t) (σ : D.H) :
    etalePi1EquivPiX' D X eL hk hτ hHL.ge (galoisAction D.L (genericLX D X eL)
      (genericLX_point D eL) (D.toGalL (Subgroup.inclusion hHL.ge σ))) = (σ : PiX D) := by
  apply (etalePi1EquivPiX' D X eL hk hτ hHL.ge).symm.injective
  rw [ContinuousMulEquiv.symm_apply_apply]
  change _ = (fundamentalGroupCongr (curveJ_basePoint D X eL hk hτ))
    (D.chartHomX hHL.ge (chartOne k X τ) (chartZero k X τ) (curveJ D X eL hk hτ) σ)
  rw [fundamentalGroupCongr_eq _ (by rw [Category.comp_id, curveJ_basePoint]),
    fundamentalGroupMap_id_curveChartHomX_galoisAction D X eL hk hHL.ge hτ _ (genericLX_point D eL)]

/-- **The bridge**: under `π₁ᵉᵗ(X, η̄) ≃ Π_X`, the scheme-theoretic section of the rational point
`x` is the Galois-model section `xSectionGk` of `ratPointOf x`. -/
theorem etalePi1EquivPiX'_schSection {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
    (g : Gk k Ω) :
    etalePi1EquivPiX' D X eL hk hτ hHL.ge (schSection D eL hk x hx hHL g) =
      xSectionGk (xh D eL hk x hx hHL) g := by
  obtain ⟨σ, hσ⟩ := (xh D eL hk x hx hHL).decompositionMap_surjective
    (AlgEquiv.autCongr (resEquiv D eL hk x hx hHL) g)
  have hg : g = AlgEquiv.autCongr (resEquiv D eL hk x hx hHL).symm
      (Decomposition.decompositionMap (F D) _ (xh D eL hk x hx hHL).hk
        (xh D eL hk x hx hHL).hkres σ) := by
    rw [hσ, ← AlgEquiv.autCongr_symm, MulEquiv.symm_apply_apply]
  have h1 : schSection D eL hk x hx hHL g = galoisAction D.L (genericLX D X eL)
      (genericLX_point D eL) (D.toGalL (Subgroup.inclusion hHL.ge (ofGalF D σ.1))) := by
    change (kbarPath D eL hk x hx hHL).symm.conjAut (galoisAction k x rfl g) = _
    rw [hg, ← kbarPath_conjAut, conjAut_symm_conjAut]
  rw [h1, etalePi1EquivPiX'_galoisAction D eL hk hHL hτ, xSectionGk, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ← hσ, xSection_decompositionMap, decompToPiX_apply]

end CurvesJacobian.LocAn.SectionBridge
