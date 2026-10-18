/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.FundamentalGroup.GenericPoint
import Pi1.FundamentalGroup.FiberFunctorIso
import Pi1.Orbicurve.GaloisPi1

/-!
# Changing the field of a geometric point, and Galois inertia groups in `π₁ᵉᵗ`

For a geometric point `η : Spec Ω ⟶ X` and an isomorphism of fields `σ : Ω ≃+* Ω'`, the geometric
points `η` and `η' = Spec σ ≫ η` have isomorphic fibre functors
(`AlgebraicGeometry.FiniteEtale.fieldChangeIso`: a point `x : Spec Ω' ⟶ A` over `η'` goes to
`Spec σ⁻¹ ≫ x`). Under the induced isomorphism `π₁ᵉᵗ(η') ≃ₜ* π₁ᵉᵗ(η)`, the Galois action
through a field-valued point `j : Spec F ⟶ X` is transported by conjugation with `σ`
(`galoisAction_fieldChange`).

This is used to compare the cuspidal inertia groups of curves whose Galois models live in
different algebraically closed fields (the curves of a Belyi chain, [AbsTopII] Example 3.6):
`AlgebraicGeometry.FiniteEtale.galInertia F j h W` is the image in `π₁ᵉᵗ(η)` of the inertia group
`GaloisPi1.inertia W ⊆ Gal(Ω / F)` of a valuation subring `W ⊆ Ω` (for the generic point `j` of a
curve and `W` a place over a cusp: the cuspidal inertia group), and
`galInertia_fieldChange`: it is carried to `galInertia F j h (W.comap σ)`.
-/

open CategoryTheory Limits PreGaloisCategory

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
  (σ : Ω ≃+* Ω') (η : Spec (.of Ω) ⟶ X)

/-- `Spec σ : Spec Ω' ⟶ Spec Ω`. -/
abbrev specIso : Spec (.of Ω') ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω'))

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specIso_symm_comp : specIso σ.symm ≫ specIso σ = 𝟙 _ := by
  rw [specIso, specIso, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of Ω)
  ext x
  simp

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specIso_comp_symm : specIso σ ≫ specIso σ.symm = 𝟙 _ := by
  simpa using specIso_symm_comp σ.symm

/-- Points over `Spec σ ≫ η` correspond to points over `η` (precomposition with `Spec σ⁻¹`). -/
def overHomEquiv (A : FiniteEtale X) :
    (Over.mk (specIso σ ≫ η) ⟶ A.toComma) ≃ (Over.mk η ⟶ A.toComma) where
  toFun x := Over.homMk (specIso σ.symm ≫ x.left) (by
    have h1 : x.left ≫ A.toComma.hom = specIso σ ≫ η := Over.w x
    change (specIso σ.symm ≫ x.left) ≫ A.toComma.hom = η
    exact (Category.assoc _ _ _).trans ((congrArg (specIso σ.symm ≫ ·) h1).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ η) (specIso_symm_comp σ))).trans
        (Category.id_comp η))))
  invFun y := Over.homMk (specIso σ ≫ y.left) (by
    have h1 : y.left ≫ A.toComma.hom = η := Over.w y
    change (specIso σ ≫ y.left) ≫ A.toComma.hom = specIso σ ≫ η
    exact (Category.assoc _ _ _).trans (congrArg (specIso σ ≫ ·) h1))
  left_inv x := by
    ext : 1
    change specIso σ ≫ specIso σ.symm ≫ x.left = x.left
    rw [← Category.assoc, specIso_comp_symm, Category.id_comp]
  right_inv y := by
    ext : 1
    change specIso σ.symm ≫ specIso σ ≫ y.left = y.left
    rw [← Category.assoc, specIso_symm_comp, Category.id_comp]

/-- **Changing the field of a geometric point**: `fiber (Spec σ ≫ η) ≅ fiber η`. -/
def fieldChangeIso : fiber (specIso σ ≫ η) ≅ fiber η :=
  NatIso.ofComponents (fun A ↦ FintypeCat.equivEquivIso
    (((fiberObjEquivHom _ A).trans (overHomEquiv σ η A)).trans (fiberObjEquivHom η A).symm))
    fun {A B} f ↦ by
      ext x
      change (fiberObjEquivHom η B).symm (overHomEquiv σ η B
          (fiberObjEquivHom _ B ((fiber _).map f x))) =
        (fiber η).map f ((fiberObjEquivHom η A).symm
          (overHomEquiv σ η A (fiberObjEquivHom _ A x)))
      rw [fiberObjEquivHom_symm_naturality, ← fiberObjEquivHom_naturality]
      congr 1

lemma fieldChangeIso_hom_app (A : FiniteEtale X) (x : (fiber (specIso σ ≫ η)).obj A) :
    fiberObjEquivHom η A ((fieldChangeIso σ η).hom.app A x) =
      overHomEquiv σ η A (fiberObjEquivHom _ A x) :=
  Equiv.apply_symm_apply _ _

lemma fieldChangeIso_inv_app (A : FiniteEtale X) (x : (fiber η).obj A) :
    fiberObjEquivHom _ A ((fieldChangeIso σ η).inv.app A x) =
      (overHomEquiv σ η A).symm (fiberObjEquivHom η A x) := by
  have h := fieldChangeIso_hom_app σ η A ((fieldChangeIso σ η).inv.app A x)
  rw [show (fieldChangeIso σ η).hom.app A ((fieldChangeIso σ η).inv.app A x) = x from
    FintypeCat.inv_hom_id_apply ((fieldChangeIso σ η).app A) x] at h
  rw [h, Equiv.symm_apply_apply]

lemma valuation_lt_one_iff_inv {K : Type*} [Field K] (A : ValuationSubring K) (x : K) :
    A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]
  simp [hx]

section Galois

variable (F : Type u) [Field F] [Algebra F Ω] [Algebra F Ω'] [IsGalois F Ω] [IsGalois F Ω']
  (hσ : ∀ c : F, σ (algebraMap F Ω c) = algebraMap F Ω' c)

/-- Conjugation by `σ : Ω ≃+* Ω'` (over `F`): `Gal(Ω' / F) ≃* Gal(Ω / F)`, `g ↦ σ⁻¹ g σ`. -/
def galConj : (Ω' ≃ₐ[F] Ω') ≃* (Ω ≃ₐ[F] Ω) where
  toFun g :=
    { ((σ.trans g.toRingEquiv).trans σ.symm) with
      commutes' := fun c ↦ by
        change σ.symm (g (σ (algebraMap F Ω c))) = _
        rw [hσ, g.commutes, ← hσ, RingEquiv.symm_apply_apply] }
  invFun g :=
    { ((σ.symm.trans g.toRingEquiv).trans σ) with
      commutes' := fun c ↦ by
        change σ (g (σ.symm (algebraMap F Ω' c))) = _
        rw [← hσ, RingEquiv.symm_apply_apply, g.commutes, hσ] }
  left_inv g := by
    ext x
    change σ (σ.symm (g (σ (σ.symm x)))) = g x
    simp
  right_inv g := by
    ext x
    change σ.symm (σ (g (σ.symm (σ x)))) = g x
    simp
  map_mul' g g' := by
    ext x
    change σ.symm (g (g' (σ x))) = σ.symm (g (σ (σ.symm (g' (σ x)))))
    simp

omit [IsSepClosed Ω] [IsSepClosed Ω'] [IsGalois F Ω] [IsGalois F Ω'] in
lemma galConj_apply (g : Ω' ≃ₐ[F] Ω') (x : Ω) : galConj σ F hσ g x = σ.symm (g (σ x)) := rfl

omit [IsSepClosed Ω] [IsSepClosed Ω'] [IsGalois F Ω] [IsGalois F Ω'] in
lemma specIso_galConj (g : Ω' ≃ₐ[F] Ω') :
    Spec.map (CommRingCat.ofHom ((galConj σ F hσ g : Ω ≃ₐ[F] Ω) : Ω →+* Ω)) =
      specIso σ.symm ≫ Spec.map (CommRingCat.ofHom (g : Ω' →+* Ω')) ≫ specIso σ := by
  rw [specIso, specIso, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2

omit [IsSepClosed Ω] [IsSepClosed Ω'] [IsGalois F Ω] [IsGalois F Ω'] in
include hσ in
lemma specAlgebraMap_fieldChange :
    Spec.map (CommRingCat.ofHom (algebraMap F Ω')) =
      specIso σ ≫ Spec.map (CommRingCat.ofHom (algebraMap F Ω)) := by
  rw [specIso, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  exact (hσ c).symm

variable (j : Spec (.of F) ⟶ X) (h : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η)

omit [IsSepClosed Ω] [IsSepClosed Ω'] [IsGalois F Ω] [IsGalois F Ω'] in
include hσ h in
lemma specAlgebraMap_comp_fieldChange :
    Spec.map (CommRingCat.ofHom (algebraMap F Ω')) ≫ j = specIso σ ≫ η := by
  rw [specAlgebraMap_fieldChange σ F hσ, Category.assoc, h]

/-- **The Galois action under a change of field**: conjugation by `fieldChangeIso` carries the
action of `g ∈ Gal(Ω' / F)` to the action of `σ⁻¹ g σ ∈ Gal(Ω / F)`. -/
theorem galoisAction_fieldChange (g : Ω' ≃ₐ[F] Ω') :
    autContinuousMulEquivOfIso (fieldChangeIso σ η)
        (galoisAction F j (specAlgebraMap_comp_fieldChange σ η F hσ j h) g) =
      galoisAction F j h (galConj σ F hσ g) := by
  refine ext_of_hom_app_left fun A x ↦ ?_
  rw [galoisAction_hom_app_left]
  change (fiberObjEquivHom η A ((fieldChangeIso σ η).hom.app A
    ((galoisAction F j _ g).hom.app A ((fieldChangeIso σ η).inv.app A x)))).left = _
  rw [fieldChangeIso_hom_app]
  change specIso σ.symm ≫ (fiberObjEquivHom _ A ((galoisAction F j _ g).hom.app A
    ((fieldChangeIso σ η).inv.app A x))).left = _
  rw [galoisAction_hom_app_left, fieldChangeIso_inv_app, specIso_galConj]
  change specIso σ.symm ≫ Spec.map (CommRingCat.ofHom (g : Ω' →+* Ω')) ≫ specIso σ ≫
    (fiberObjEquivHom η A x).left = _
  simp only [Category.assoc]

/-- **The inertia subgroup of `π₁ᵉᵗ(η)` at a valuation subring `W ⊆ Ω`** through the field-valued
point `j : Spec F ⟶ X`: the subgroup generated by the image of the inertia group
`GaloisPi1.inertia W ⊆ Gal(Ω / F)` under the Galois action. -/
def galInertia (W : ValuationSubring Ω) : Subgroup π₁ᵉᵗ(η) :=
  Subgroup.closure (galoisAction F j h '' GaloisPi1.inertia W)

omit [IsSepClosed Ω] [IsSepClosed Ω'] [IsGalois F Ω] [IsGalois F Ω'] in
lemma mem_inertia_comap_iff (W : ValuationSubring Ω') (g : Ω' ≃ₐ[F] Ω') :
    galConj σ F hσ g ∈ GaloisPi1.inertia (W.comap (σ : Ω →+* Ω')) ↔
      g ∈ GaloisPi1.inertia W := by
  simp only [GaloisPi1.inertia, Set.mem_setOf_eq]
  have key : ∀ x : Ω, (W.comap (σ : Ω →+* Ω')).valuation x < 1 ↔ W.valuation (σ x) < 1 := by
    intro x
    rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap]
    simp
  constructor
  · intro hg a ha
    have := hg (σ.symm a) (by simpa [ValuationSubring.mem_comap] using ha)
    rw [key, galConj_apply, RingEquiv.apply_symm_apply, map_sub, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply] at this
    exact this
  · intro hg a ha
    rw [key, galConj_apply, map_sub, RingEquiv.apply_symm_apply]
    exact hg (σ a) ha

/-- **Inertia groups under a change of field**: `fieldChangeIso` carries the inertia subgroup at
`W ⊆ Ω'` to the inertia subgroup at `σ⁻¹(W) ⊆ Ω`. -/
theorem map_galInertia_fieldChange (W : ValuationSubring Ω') :
    (galInertia (specIso σ ≫ η) F j (specAlgebraMap_comp_fieldChange σ η F hσ j h) W).map
        (autContinuousMulEquivOfIso (fieldChangeIso σ η)).toMulEquiv.toMonoidHom =
      galInertia η F j h (W.comap (σ : Ω →+* Ω')) := by
  rw [galInertia, galInertia, MonoidHom.map_closure]
  congr 1
  ext γ
  simp only [Set.mem_image, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨galConj σ F hσ g, (mem_inertia_comap_iff σ F hσ W g).2 hg,
      (galoisAction_fieldChange σ η F hσ j h g).symm⟩
  · rintro ⟨g₀, hg₀, rfl⟩
    obtain ⟨g, rfl⟩ := (galConj σ F hσ).surjective g₀
    exact ⟨_, ⟨g, (mem_inertia_comap_iff σ F hσ W g).1 hg₀, rfl⟩,
      galoisAction_fieldChange σ η F hσ j h g⟩

end Galois

end AlgebraicGeometry.FiniteEtale
