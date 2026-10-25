/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SectionBridgeThmC

/-!
# Sections of rational points under endomorphisms over `k`

Setting of `LocAn/SectionBridge.lean`: `X` a curve over `k` with geometric generic point `η̄`,
`x : Spec k ⟶ X` a rational point and `kbarPath x : fiber η̄ ≅ fiber (Spec k̄ ⟶ Spec k ⟶ X)` the
specialisation path defining the section `schSection x : G_k → π₁ᵉᵗ(X, η̄)`.

* General facts on base point changes `AlgebraicGeometry.FiniteEtale.fiberIsoMap` (composition,
  inverses, `eqToIso`, composition of the morphisms, and `fundamentalGroupMap` as a base point
  change).
* **`CurvesJacobian.LocAn.SectionBridge.fiberIsoMap_kbarPath`** (L2): the image of `kbarPath x`
  in `Spec k` is the fixed path `fiber (η̄ ≫ str) = fiber (Spec Ω ⟶ Spec k̄ ⟶ Spec k) ≅
  fiber (Spec k̄ ⟶ Spec k)` (inverse of `fieldExtIso`), independently of `x`: the section of
  `π^* E` extending a point over `η̄` maps `Spec A` into the finite `k`-scheme `E`, hence factors
  through the integral closure of `k` in `A`, on which the residue map is the inclusion `k̄ ⊆ Ω`.
* **`exists_conj_schSection_comp`** (L1): if `φ : X ⟶ X` over `k` acts on `π₁ᵉᵗ(X, η̄)` as the
  identity up to a path `γ : fiber (η̄ ≫ φ) ≅ fiber η̄` lying over the base, then for every rational
  point `x`, the section of `x ≫ φ` is the conjugate of the section of `x` by an element `c` of
  `Δ_X = ker(π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k))`.
* **`comp_eq_of_conj_padic`**, **`comp_eq_of_conj_numberField`**: by [LocAn] Thm C, such a `φ`
  fixes every rational point of a proper curve of geometric genus `≠ 0` over a finite extension
  of `ℚ_p` or a number field.
-/

open CategoryTheory Functor

universe u u₁ u₂ u₃ u₄ u₅ u₆ w

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]
  {E : Type u₅} [Category.{u₆} E]
  {F F' : C ⥤ FintypeCat.{w}} {G G' : D ⥤ FintypeCat.{w}} {K K' : E ⥤ FintypeCat.{w}}

set_option backward.isDefEq.respectTransparency false in
/-- `transportIso` is unchanged when the functor `H` is replaced by an isomorphic one. -/
lemma transportIso_isoWhiskerRight' {H H' : D ⥤ C} (c : H' ≅ H) (e : H ⋙ F ≅ G)
    (e' : H ⋙ F' ≅ G') (α : F ≅ F') :
    transportIso (Functor.isoWhiskerRight c F ≪≫ e) (Functor.isoWhiskerRight c F' ≪≫ e') α =
      transportIso e e' α := by
  refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
  simp only [transportIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [α.hom.naturality_assoc, ← F'.map_comp_assoc, Iso.inv_hom_id_app, F'.map_id,
    Category.id_comp]

/-- Transporting twice is transporting along the composite functor. -/
lemma transportIso_transportIso' (H₁ : D ⥤ C) (H₂ : E ⥤ D) (e : H₁ ⋙ F ≅ G)
    (e' : H₁ ⋙ F' ≅ G') (d : H₂ ⋙ G ≅ K) (d' : H₂ ⋙ G' ≅ K') (α : F ≅ F') :
    transportIso d d' (transportIso e e' α) =
      transportIso (Functor.associator H₂ H₁ F ≪≫ Functor.isoWhiskerLeft H₂ e ≪≫ d)
        (Functor.associator H₂ H₁ F' ≪≫ Functor.isoWhiskerLeft H₂ e' ≪≫ d') α := by
  ext X
  simp [transportIso]

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

open PreGaloisCategory

variable {X Y W : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `pullbackFiberIso` of a composite, componentwise. -/
lemma pullbackFiberIso_comp_hom_app' (f : Y ⟶ X) (g : X ⟶ W) {q : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : q ≫ f = η) (h₂ : η ≫ g = ζ)
    (h : q ≫ f ≫ g = ζ) (A : FiniteEtale W) :
    (fiber q).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
      (pullbackFiberIso f h₁).hom.app ((pullback g).obj A) ≫ (pullbackFiberIso g h₂).hom.app A =
    (pullbackFiberIso (f ≫ g) h).hom.app A := by
  have key : (pullback q).map ((MorphismProperty.Over.pullbackComp f g).hom.app A) ≫
        (MorphismProperty.Over.pullbackComp q f η h₁.symm).inv.app ((pullback g).obj A) ≫
        (MorphismProperty.Over.pullbackComp η g ζ h₂.symm).inv.app A =
      (MorphismProperty.Over.pullbackComp q (f ≫ g) ζ h.symm).inv.app A := by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext <;> simp [FiniteEtale]
  rw [pullbackFiberIso_hom_app (f ≫ g), ← key, pullbackFiberIso_hom_app f,
    pullbackFiberIso_hom_app g]
  simp only [fiber, Functor.comp_map, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- `pullbackFiberIso` of a composite. -/
lemma pullbackFiberIso_comp' (f : Y ⟶ X) (g : X ⟶ W) {q : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : q ≫ f = η) (h₂ : η ≫ g = ζ)
    (h : q ≫ f ≫ g = ζ) :
    pullbackFiberIso (f ≫ g) h =
      Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp f g) (fiber q) ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f h₁) ≪≫
        pullbackFiberIso g h₂ := by
  refine Iso.ext (NatTrans.ext (funext fun A ↦ ?_))
  rw [← pullbackFiberIso_comp_hom_app' f g h₁ h₂ h A]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  rfl

/-- Base point changes compose (geometric points with different fields). -/
lemma fiberIsoMap_trans' (f : Y ⟶ X) {q : Spec (.of Ω) ⟶ Y} {q' : Spec (.of Ω') ⟶ Y}
    {q'' : Spec (.of Ω'') ⟶ Y} {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X}
    {η'' : Spec (.of Ω'') ⟶ X} (h : q ≫ f = η) (h' : q' ≫ f = η') (h'' : q'' ≫ f = η'')
    (α : fiber q ≅ fiber q') (β : fiber q' ≅ fiber q'') :
    fiberIsoMap f h h'' (α ≪≫ β) = fiberIsoMap f h h' α ≪≫ fiberIsoMap f h' h'' β := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- Base point changes commute with inverses (geometric points with different fields). -/
lemma fiberIsoMap_symm' (f : Y ⟶ X) {q : Spec (.of Ω) ⟶ Y} {q' : Spec (.of Ω') ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X} (h : q ≫ f = η) (h' : q' ≫ f = η')
    (α : fiber q ≅ fiber q') :
    fiberIsoMap f h' h α.symm = (fiberIsoMap f h h' α).symm := by
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- `fiberIsoMap` of the identification of the fibres at equal geometric points. -/
lemma fiberIsoMap_eqToIso (f : Y ⟶ X) {q q' : Spec (.of Ω) ⟶ Y} (hq : q = q')
    {η η' : Spec (.of Ω) ⟶ X} (h : q ≫ f = η) (h' : q' ≫ f = η') (hη : η = η') :
    fiberIsoMap f h h' (eqToIso (congrArg fiber hq)) = eqToIso (congrArg fiber hη) := by
  subst hq h h'
  ext : 2
  simp [fiberIsoMap, transportIso]

/-- `fiberIsoMap` only depends on the morphism (geometric points with different fields). -/
lemma fiberIsoMap_congr' {f f' : Y ⟶ X} (hf : f = f') {q : Spec (.of Ω) ⟶ Y}
    {q' : Spec (.of Ω') ⟶ Y} {η : Spec (.of Ω) ⟶ X} {η' : Spec (.of Ω') ⟶ X} (h : q ≫ f = η)
    (h' : q' ≫ f = η') (k : q ≫ f' = η) (k' : q' ≫ f' = η') (α : fiber q ≅ fiber q') :
    fiberIsoMap f h h' α = fiberIsoMap f' k k' α := by
  subst hf
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Base point changes along a composite** (geometric points with different fields):
`g_*(f_* α) = (f ≫ g)_* α`. -/
lemma fiberIsoMap_fiberIsoMap' (f : Y ⟶ X) (g : X ⟶ W)
    {q : Spec (.of Ω) ⟶ Y} {q' : Spec (.of Ω') ⟶ Y} {η : Spec (.of Ω) ⟶ X}
    {η' : Spec (.of Ω') ⟶ X} {ζ : Spec (.of Ω) ⟶ W} {ζ' : Spec (.of Ω') ⟶ W}
    (h₁ : q ≫ f = η) (h₁' : q' ≫ f = η') (h₂ : η ≫ g = ζ) (h₂' : η' ≫ g = ζ')
    (h : q ≫ f ≫ g = ζ) (h' : q' ≫ f ≫ g = ζ') (α : fiber q ≅ fiber q') :
    fiberIsoMap g h₂ h₂' (fiberIsoMap f h₁ h₁' α) = fiberIsoMap (f ≫ g) h h' α := by
  simp only [fiberIsoMap]
  rw [pullbackFiberIso_comp' f g h₁ h₂ h, pullbackFiberIso_comp' f g h₁' h₂' h',
    transportIso_isoWhiskerRight', transportIso_transportIso']

/-- **`fundamentalGroupMap` is a base point change**: `f_* σ = fiberIsoMap f σ`. -/
lemma fundamentalGroupMap_eq_fiberIsoMap [IsSepClosed Ω] (f : Y ⟶ X) {q : Spec (.of Ω) ⟶ Y}
    {η : Spec (.of Ω) ⟶ X} (h : q ≫ f = η) (σ : π₁ᵉᵗ(q)) :
    (fundamentalGroupMap f h σ : fiber η ≅ fiber η) = fiberIsoMap f h h σ := by
  refine Iso.ext (NatTrans.ext (funext fun A ↦ FintypeCat.hom_ext _ _ fun z ↦ ?_))
  rw [fundamentalGroupMap_apply, fiberAutMap_hom_app_apply]
  rfl

/-- The identification `fiber η₁ = fiber η₂` does not change points. -/
lemma eqToIso_fiber_left [IsSepClosed Ω] {η₁ η₂ : Spec (.of Ω) ⟶ X} (h : η₁ = η₂)
    (B : FiniteEtale X) (y : (fiber η₁).obj B) :
    (fiberObjEquivHom η₂ B ((eqToIso (congrArg fiber h)).hom.app B y)).left =
      (fiberObjEquivHom η₁ B y).left := by
  subst h
  rfl

end AlgebraicGeometry.FiniteEtale

open TopologicalSpace AlgebraicGeometry Belyi IsLocalRing Pi1.Orbifold
open AlgebraicGeometry.FiniteEtale WeilCurves.FunctionField CategoryTheory.PreGaloisCategory

noncomputable section

namespace CurvesJacobian.LocAn.SectionBridge

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve CurvesJacobian.Cusp

/-! ### Morphisms into finite `k`-schemes -/

theorem exists_factor_integralClosure {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    {E : Scheme.{u}} (q : E ⟶ Spec (.of k)) [IsFinite q] (m : Spec (.of R) ⟶ E)
    (hm : m ≫ q = Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    ∃ m₀ : Spec (.of (integralClosure k R)) ⟶ E,
      Spec.map (CommRingCat.ofHom (algebraMap (integralClosure k R) R)) ≫ m₀ = m := by
  haveI : IsAffine E := isAffine_of_isAffineHom q
  set φ := Spec.preimage (m ≫ E.isoSpec.hom) with hφ
  have hφm : Spec.map φ = m ≫ E.isoSpec.hom := Spec.map_preimage _
  set ψ : CommRingCat.of k ⟶ Γ(E, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop with hψ
  have hψφ : ψ ≫ φ = CommRingCat.ofHom (algebraMap k R) := by
    apply Spec.map_injective
    have h1 := Scheme.isoSpec_inv_naturality q
    have h2 : Spec.map (q.appTop ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫ (Spec (.of k)).isoSpec.hom := by
      rw [Spec.map_comp, hφm, Category.assoc, ← hm, Category.assoc]
      congr 1
      rw [← cancel_mono (Spec (.of k)).isoSpec.inv, Category.assoc, Category.assoc,
        Iso.hom_inv_id, Category.comp_id, h1, Iso.hom_inv_id_assoc]
    rw [hψ, Category.assoc, Spec.map_comp, h2, Scheme.isoSpec_Spec_hom, Category.assoc,
      ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  letI : Algebra k Γ(E, ⊤) := ψ.hom.toAlgebra
  haveI : Module.Finite k Γ(E, ⊤) := by
    have hq : q.appTop.hom.Finite := q.finite_appTop
    have hi : (Scheme.ΓSpecIso (.of k)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
    exact hq.comp hi
  let φA : Γ(E, ⊤) →ₐ[k] R :=
    { φ.hom with
      commutes' := fun c ↦ congrArg (fun f ↦ f.hom c) hψφ }
  have hint : ∀ a, φ.hom a ∈ integralClosure k R := fun a ↦
    (Algebra.IsIntegral.isIntegral (R := k) a).map φA
  let φ₀ : Γ(E, ⊤) →+* integralClosure k R := φ.hom.codRestrict _ hint
  refine ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ E.isoSpec.inv, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom φ₀ ≫ CommRingCat.ofHom (algebraMap (integralClosure k R) R) = φ := by
    ext a; rfl
  rw [this, hφm, Category.assoc, Iso.hom_inv_id, Category.comp_id]


section Generic

variable {k Ω K Ω₂ : Type u} [Field k] [Field Ω] [IsSepClosed Ω] [Field K] [IsSepClosed K]
  [Field Ω₂] [IsSepClosed Ω₂]

/-- `fieldExtIso` on points: precomposition with `Spec ι`. -/
lemma fieldExtIso_hom_left {Y : Scheme.{u}} [ConnectedSpace Y] (ι : Ω₂ →+* K)
    (η : Spec (.of Ω₂) ⟶ Y) (B : FiniteEtale Y) (z : (fiber η).obj B) :
    (fiberObjEquivHom _ B ((fieldExtIso ι η).hom.app B z)).left =
      specHom ι ≫ (fiberObjEquivHom η B z).left :=
  fieldExtHom_app ι η B z

omit [IsSepClosed Ω] [IsSepClosed K] [IsSepClosed Ω₂] in
/-- **Morphisms from `Spec A` to a finite `k`-scheme see `Spec Ω ⟶ Spec A` and
`Spec Ω ⟶ Spec K ⟶ Spec Ω₂ ⟶ Spec A` identically**, if the ring maps agree on the elements of
`A` integral over `k`. -/
lemma specHom_comp_eq_of_integral (A : ValuationSubring Ω) (c : k →+* A) (r : A →+* Ω₂)
    (ρ : Ω₂ →+* K) (ι : K →+* Ω) (H : ∀ a : A, c.IsIntegralElem a → ι (ρ (r a)) = a)
    {Z : Scheme.{u}} (q : Z ⟶ Spec (.of k)) [hq : IsFinite q] (m : Spec (.of A) ⟶ Z)
    (hm : m ≫ q = Spec.map (CommRingCat.ofHom c)) :
    Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom ρ) ≫
        Spec.map (CommRingCat.ofHom r) ≫ m =
      Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ m := by
  letI : Algebra k A := c.toAlgebra
  obtain ⟨m₀, rfl⟩ := exists_factor_integralClosure q m hm
  simp only [← Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact H a.1 a.2

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- **The image of a specialisation path in `Spec k`** (generic form of L2): let `π : Spec A ⟶ X`
lie over `Spec c : Spec A ⟶ Spec k`, and consider the path
`fiber η ≅ fiber (Spec Ω ⟶ Spec A ⟶ X) ≅ fiber (Spec Ω₂ ⟶ Spec A ⟶ X) ≅ fiber (Spec K ⟶ …)`
(specialisation along `r : A → Ω₂`, then extension of the field along `ρ : Ω₂ → K`). If
`ι ∘ ρ ∘ r` is the inclusion `A ⊆ Ω` on the elements integral over `k`, then its image in
`Spec k`, followed by extending the field along `ι : K → Ω`, is the identification of fibres at
the equal points `η ≫ str = Spec Ω ⟶ Spec K ⟶ Spec k`. -/
theorem fiberIsoMap_specialisation_trans (str : X ⟶ Spec (.of k)) (A : ValuationSubring Ω)
    (c : k →+* A) (π : Spec (.of A) ⟶ X) (hπ : π ≫ str = Spec.map (CommRingCat.ofHom c))
    (r : A →+* Ω₂) (ρ : Ω₂ →+* K) (ι : K →+* Ω)
    (H : ∀ a : A, c.IsIntegralElem a → ι (ρ (r a)) = a)
    {η : Spec (.of Ω) ⟶ X} {p₂ : Spec (.of Ω₂) ⟶ X} {p₃ : Spec (.of K) ⟶ X}
    {j : Spec (.of K) ⟶ Spec (.of k)} (h₁ : η = vGen A ≫ π)
    (h₂ : Spec.map (CommRingCat.ofHom r) ≫ π = p₂) (h₃ : specHom ρ ≫ p₂ = p₃)
    (h₄ : p₃ ≫ str = j) (h₅ : η ≫ str = specHom ι ≫ j) :
    fiberIsoMap str rfl h₄ ((eqToIso (congrArg fiber h₁) ≪≫
        spIso A π (Spec.map (CommRingCat.ofHom r)) ≪≫ eqToIso (congrArg fiber h₂)) ≪≫
        fieldExtIso ρ p₂ ≪≫ eqToIso (congrArg fiber h₃)) ≪≫ fieldExtIso ι j =
      eqToIso (congrArg fiber h₅) := by
  subst h₁ h₂ h₃ h₄
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  refine Iso.ext (NatTrans.ext (funext fun E ↦ FintypeCat.hom_ext _ _ fun w ↦ ?_))
  refine (fiberObjEquivHom _ E).injective (Over.OverMorphism.ext ?_)
  rw [eqToIso_fiber_left h₅, Iso.trans_hom, NatTrans.comp_app, CategoryTheory.comp_apply,
    fieldExtIso_hom_left]
  set y := (pullbackFiberIso str (rfl : (vGen A ≫ π) ≫ str = _)).inv.app E w with hy
  have hyw : (fiberObjEquivHom _ E w).left =
      (fiberObjEquivHom _ _ y).left ≫ Limits.pullback.fst E.hom str := by
    have := pullbackFiberIso_hom_app_left str (rfl : (vGen A ≫ π) ≫ str = _) E y
    rwa [show (pullbackFiberIso str rfl).hom.app E y = w from
      FintypeCat.inv_hom_id_apply ((pullbackFiberIso str rfl).app E) w] at this
  have hM : (fiberIsoMap str rfl rfl (spIso A π (Spec.map (CommRingCat.ofHom r)) ≪≫
      fieldExtIso ρ (Spec.map (CommRingCat.ofHom r) ≫ π))).hom.app E w =
        (pullbackFiberIso str rfl).hom.app E
          ((spIso A π (Spec.map (CommRingCat.ofHom r)) ≪≫
            fieldExtIso ρ (Spec.map (CommRingCat.ofHom r) ≫ π)).hom.app _ y) := rfl
  rw [hM, pullbackFiberIso_hom_app_left, Iso.trans_hom, NatTrans.comp_app,
    CategoryTheory.comp_apply, fieldExtIso_hom_left]
  obtain ⟨s, hs⟩ := (secPt_bijective A π ((FiniteEtale.pullback str).obj E)).2 y
  rw [← hs, spIso_hom_secPt, secPt_left]
  rw [← hs, secPt_left] at hyw
  rw [hyw]
  have hm : (s.1 ≫ Limits.pullback.fst E.hom str) ≫ E.hom =
      Spec.map (CommRingCat.ofHom c) := by
    have hc : Limits.pullback.fst E.hom str ≫ E.hom = Limits.pullback.snd E.hom str ≫ str :=
      Limits.pullback.condition
    have h2 : s.1 ≫ Limits.pullback.snd E.hom str = π := s.2
    exact (Category.assoc _ _ _).trans ((congrArg (s.1 ≫ ·) hc).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ str) h2).trans hπ)))
  have K := specHom_comp_eq_of_integral A c r ρ ι H E.hom (hq := E.prop.toIsFinite) _ hm
  have e₁ : specHom ι ≫ (specHom ρ ≫ Spec.map (CommRingCat.ofHom r) ≫ s.1) ≫
      Limits.pullback.fst E.hom str = specHom ι ≫ specHom ρ ≫ Spec.map (CommRingCat.ofHom r) ≫
        s.1 ≫ Limits.pullback.fst E.hom str := by
    simp only [Category.assoc]
  exact e₁.trans (K.trans (Category.assoc _ _ _).symm)

end Generic

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  [CharZero k] [IsCurveOver k X] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (x : Spec (.of k) ⟶ X) (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) (hHL : D.HL = D.H)

omit [CharZero k] [IsCurveOver k X] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
include hk in
/-- The geometric generic point lies over `Spec Ω ⟶ Spec k`. -/
lemma geometricGenericPoint_toSpec :
    geometricGenericPoint D X eL ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [← genericLX_point D eL, Category.assoc, genericLX_toSpec D eL hk, ← Spec.map_comp]
  rfl

omit [CharZero k] [IsCurveOver k X] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
include hk in
/-- The geometric generic point lies over `Spec Ω ⟶ Spec k̄ ⟶ Spec k`. -/
lemma geometricGenericPoint_toSpec' :
    geometricGenericPoint D X eL ≫ (X ↘ Spec (.of k)) =
      specHom (algebraMap (kbar k Ω) Ω) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))) := by
  rw [geometricGenericPoint_toSpec D eL hk]
  exact (specMap_algebraMap_comp (F := kbar k Ω) (Ω := Ω) k).symm

omit [IsIntegral X] [CharZero k] [IsCurveOver k X] [IsAlgClosed Ω] in
include hx in
/-- `Spec k̄ ⟶ Spec k ⟶ X` lies over `Spec k̄ ⟶ Spec k`. -/
lemma kbar_toSpec :
    (Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))) ≫ x) ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))) := by
  rw [Category.assoc, hx, Category.comp_id]

/-- The constants `k → A` of the place of `x`. -/
def placeConst : k →+* (xh D eL hk x hx hHL).A :=
  (algebraMap k Ω).codRestrict (xh D eL hk x hx hHL).A (xh D eL hk x hx hHL).hk

omit [IsAlgClosed Ω] in
/-- `Spec A ⟶ X ⟶ Spec k` is `Spec` of the constants. -/
lemma placeMor_toSpec :
    placeMor D eL hk (ratPt x) ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (placeConst D eL hk x hx hHL)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ, placeMor D eL hk (ratPt x) ≫ (X ↘ Spec (.of k)) = Spec.map φ :=
    ⟨Spec.preimage _, (Spec.map_preimage _).symm⟩
  rw [hφ]
  have h1 : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap (xh D eL hk x hx hHL).A Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [Spec.map_comp, ← hφ, ← Category.assoc]
    exact (congrArg (· ≫ (X ↘ Spec (.of k))) (vGen_placeMor' D eL hk x hx hHL)).trans
      (geometricGenericPoint_toSpec D eL hk)
  have h2 := Spec.map_injective h1
  congr 1
  ext c
  exact congrArg (fun f ↦ f.hom c) h2

/-- On elements of `A` integral over `k`, `ι ∘ res⁻¹ ∘ residue` is the inclusion `A ⊆ Ω`. -/
lemma algebraMap_resEquiv_symm_residue (a : (xh D eL hk x hx hHL).A)
    (ha : IsIntegral k (a : Ω)) :
    algebraMap (kbar k Ω) Ω ((resEquiv D eL hk x hx hHL).symm
      (residue (xh D eL hk x hx hHL).A a)) = a := by
  have hb : (a : Ω) ∈ kbar k Ω := mem_algebraicClosure_iff.mpr ha.isAlgebraic
  have : (resEquiv D eL hk x hx hHL).symm (residue (xh D eL hk x hx hHL).A a) = ⟨a, hb⟩ := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

/-- **L2: the specialisation paths lie over a fixed path of `Spec k`**: the image of `kbarPath x`
under `X ⟶ Spec k`, followed by `fiber (Spec k̄ ⟶ Spec k) ≅ fiber (Spec Ω ⟶ Spec k̄ ⟶ Spec k)`
(`fieldExtIso`), is the identification `η̄ ≫ str = Spec Ω ⟶ Spec k̄ ⟶ Spec k`; in particular it
does not depend on `x`. -/
theorem fiberIsoMap_kbarPath_trans :
    fiberIsoMap (X ↘ Spec (.of k)) rfl (kbar_toSpec x hx) (kbarPath D eL hk x hx hHL) ≪≫
        fieldExtIso (algebraMap (kbar k Ω) Ω)
          (Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω)))) =
      eqToIso (congrArg fiber (geometricGenericPoint_toSpec' D eL hk)) :=
  fiberIsoMap_specialisation_trans (X ↘ Spec (.of k)) _ (placeConst D eL hk x hx hHL) _
    (placeMor_toSpec D eL hk x hx hHL) _ _ _
    (fun a ha ↦ algebraMap_resEquiv_symm_residue D eL hk x hx hHL a (by
      obtain ⟨p, hp, he⟩ := ha
      refine ⟨p, hp, ?_⟩
      have := congrArg (algebraMap (xh D eL hk x hx hHL).A Ω) he
      rwa [Polynomial.hom_eval₂, map_zero] at this))
    (vGen_placeMor' D eL hk x hx hHL).symm (closed_placeMor' D eL hk x hx hHL)
    (kbar_point D eL hk x hx hHL) (kbar_toSpec x hx) (geometricGenericPoint_toSpec' D eL hk)

/-- **L2**, in the form `fiberIsoMap (kbarPath x) = (identification) ≪≫ fieldExtIso⁻¹`. -/
theorem fiberIsoMap_kbarPath :
    fiberIsoMap (X ↘ Spec (.of k)) rfl (kbar_toSpec x hx) (kbarPath D eL hk x hx hHL) =
      eqToIso (congrArg fiber (geometricGenericPoint_toSpec' D eL hk)) ≪≫
        (fieldExtIso (algebraMap (kbar k Ω) Ω)
          (Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))))).symm := by
  rw [← fiberIsoMap_kbarPath_trans D eL hk x hx hHL, Iso.trans_assoc, Iso.self_symm_id,
    Iso.trans_refl]

end Galois


section Endo

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  [CharZero k] [IsCurveOver k X] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] (hHL : D.HL = D.H)
  {φ : X ⟶ X} (hφ : φ ≫ (X ↘ Spec (.of k)) = X ↘ Spec (.of k))

omit [IsIntegral X] [CharZero k] [IsCurveOver k X] in
include hφ in
/-- A point composed with a `k`-morphism `φ` lies over the same point of `Spec k`. -/
lemma comp_toSpec {Ω' : Type u} [Field Ω'] (p : Spec (.of Ω') ⟶ X) :
    (p ≫ φ) ≫ (X ↘ Spec (.of k)) = p ≫ (X ↘ Spec (.of k)) := by
  rw [Category.assoc, hφ]

omit [IsIntegral X] [CharZero k] [IsCurveOver k X] in
include hφ in
/-- The image of a rational point under a `k`-morphism is a rational point. -/
lemma comp_rat {x : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) :
    (x ≫ φ) ≫ (X ↘ Spec (.of k)) = 𝟙 _ := by
  rw [Category.assoc, hφ, hx]

/-- **L1: sections of rational points under a `k`-endomorphism acting trivially on `π₁ᵉᵗ`**.
Let `φ : X ⟶ X` be a `k`-morphism and `γ : fiber (η̄ ≫ φ) ≅ fiber η̄` a path such that
`φ_* : π₁ᵉᵗ(X, η̄) → π₁ᵉᵗ(X, η̄ ≫ φ)` followed by conjugation with `γ` is the identity (`hγ`), and
`γ` lies over the base: its image in `Spec k` is the identity path (`hγb`). Then for every rational
point `x`, the section of `x ≫ φ` is conjugate to the section of `x` by an element `c` of
`Δ_X = ker(π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k))`, namely `c = γ⁻¹ · φ_*(kbarPath x) · kbarPath (x ≫ φ)⁻¹`. -/
theorem exists_conj_schSection_comp
    (γ : fiber (geometricGenericPoint D X eL ≫ φ) ≅ fiber (geometricGenericPoint D X eL))
    (hγ : ∀ σ : π₁ᵉᵗ(geometricGenericPoint D X eL),
      σ = γ.conjAut (fundamentalGroupMap φ rfl σ))
    (hγb : fiberIsoMap (X ↘ Spec (.of k)) (comp_toSpec hφ _) rfl γ = Iso.refl _)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) :
    ∃ c : π₁ᵉᵗ(geometricGenericPoint D X eL),
      fundamentalGroupMap (X ↘ Spec (.of k)) rfl c = 1 ∧
      ∀ g, schSection D eL hk (x ≫ φ) (comp_rat hφ hx) hHL g =
        c * schSection D eL hk x hx hHL g * c⁻¹ := by
  have h₂ : (Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))) ≫ x) ≫ φ =
      Spec.map (CommRingCat.ofHom (algebraMap k (kbar k Ω))) ≫ x ≫ φ := Category.assoc _ _ _
  let c : π₁ᵉᵗ(geometricGenericPoint D X eL) :=
    γ.symm ≪≫ fiberIsoMap φ rfl h₂ (kbarPath D eL hk x hx hHL) ≪≫
      (kbarPath D eL hk (x ≫ φ) (comp_rat hφ hx) hHL).symm
  refine ⟨c, ?_, fun g ↦ ?_⟩
  · have hM : fiberIsoMap (X ↘ Spec (.of k)) (comp_toSpec hφ _)
        (kbar_toSpec (x ≫ φ) (comp_rat hφ hx)) (fiberIsoMap φ rfl h₂ (kbarPath D eL hk x hx hHL)) =
        fiberIsoMap (X ↘ Spec (.of k)) rfl (kbar_toSpec (x ≫ φ) (comp_rat hφ hx))
          (kbarPath D eL hk (x ≫ φ) (comp_rat hφ hx) hHL) := by
      rw [fiberIsoMap_fiberIsoMap' φ (X ↘ Spec (.of k)) rfl h₂ (comp_toSpec hφ _)
          (kbar_toSpec (x ≫ φ) (comp_rat hφ hx)) (by rw [hφ])
          (by rw [hφ]; exact kbar_toSpec x hx),
        fiberIsoMap_congr' hφ _ _ rfl (kbar_toSpec x hx), fiberIsoMap_kbarPath D eL hk x hx hHL,
        fiberIsoMap_kbarPath D eL hk (x ≫ φ) (comp_rat hφ hx) hHL]
    have h1 : (fundamentalGroupMap (X ↘ Spec (.of k)) rfl c :
        fiber (geometricGenericPoint D X eL ≫ (X ↘ Spec (.of k))) ≅ _) = Iso.refl _ := by
      rw [fundamentalGroupMap_eq_fiberIsoMap]
      change fiberIsoMap (X ↘ Spec (.of k)) rfl rfl (γ.symm ≪≫
        fiberIsoMap φ rfl h₂ (kbarPath D eL hk x hx hHL) ≪≫
          (kbarPath D eL hk (x ≫ φ) (comp_rat hφ hx) hHL).symm) = _
      rw [fiberIsoMap_trans' _ rfl (comp_toSpec hφ _) rfl, fiberIsoMap_trans' _ (comp_toSpec hφ _)
          (kbar_toSpec (x ≫ φ) (comp_rat hφ hx)) rfl, fiberIsoMap_symm', fiberIsoMap_symm', hγb,
        hM, Iso.refl_symm, Iso.refl_trans, Iso.self_symm_id]
    exact h1
  · have hs : fundamentalGroupMap φ rfl (schSection D eL hk x hx hHL g) =
        γ.symm.conjAut (schSection D eL hk x hx hHL g) := by
      conv_rhs => rw [hγ (schSection D eL hk x hx hHL g)]
      rw [conjAut_symm_conjAut]
    have e1 : galoisAction k (x ≫ φ) rfl g = fundamentalGroupMap φ h₂ (galoisAction k x rfl g) :=
      (fundamentalGroupMap_galoisAction (F := k) (j := x) (f := φ) (h₁ := rfl) (h₂ := h₂)
        (h := rfl) (g := g)).symm
    have e2 : galoisAction k x rfl g =
        autContinuousMulEquivOfIso (kbarPath D eL hk x hx hHL) (schSection D eL hk x hx hHL g) :=
      (conjAut_conjAut_symm (kbarPath D eL hk x hx hHL) (galoisAction k x rfl g)).symm
    have key : schSection D eL hk (x ≫ φ) (comp_rat hφ hx) hHL g =
        Iso.conjAut c (schSection D eL hk x hx hHL g) := by
      change (kbarPath D eL hk (x ≫ φ) (comp_rat hφ hx) hHL).symm.conjAut
        (galoisAction k (x ≫ φ) rfl g) = _
      rw [e1, e2, fundamentalGroupMap_autContinuousMulEquivOfIso φ rfl h₂, hs]
      change (kbarPath D eL hk (x ≫ φ) (comp_rat hφ hx) hHL).symm.conjAut
          ((fiberIsoMap φ rfl h₂ (kbarPath D eL hk x hx hHL)).conjAut
            (γ.symm.conjAut (schSection D eL hk x hx hHL g))) =
        (γ.symm ≪≫ fiberIsoMap φ rfl h₂ (kbarPath D eL hk x hx hHL) ≪≫
          (kbarPath D eL hk (x ≫ φ) (comp_rat hφ hx) hHL).symm).conjAut
            (schSection D eL hk x hx hHL g)
      rw [Iso.trans_conjAut, Iso.trans_conjAut]
    rw [key, Iso.conjAut_apply, Aut.Aut_mul_def, Aut.Aut_mul_def, Aut.Aut_inv_def]

end Endo

section Curve

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- **A `k`-endomorphism acting trivially on `π₁ᵉᵗ` fixes the rational points, over a finite
extension `k` of `ℚ_p`**: for a proper curve `X` of geometric genus `≠ 0` and `φ : X ⟶ X` over `k`
with a path `γ : fiber (η̄ ≫ φ) ≅ fiber η̄` over the base such that `γ ∘ φ_*` is the identity of
`π₁ᵉᵗ(X, η̄)`, `x ≫ φ = x` for every rational point `x`. -/
theorem comp_eq_of_conj_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k]
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {φ : X ⟶ X} (hφ : φ ≫ (X ↘ Spec (.of k)) = X ↘ Spec (.of k))
    (γ : fiber (geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ) ≫ φ) ≅
      fiber (geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (hγ : ∀ σ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)),
      σ = γ.conjAut (fundamentalGroupMap φ rfl σ))
    (hγb : fiberIsoMap (X ↘ Spec (.of k)) (comp_toSpec hφ _) rfl γ = Iso.refl _)
    {x : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) : x ≫ φ = x := by
  obtain ⟨c, hc1, hc2⟩ := exists_conj_schSection_comp (curveGaloisData k hτ) (curveEquivL k hτ)
    (curveEquivL_algebraMap k hτ) rfl hφ γ hγ hγb x hx
  exact (eq_of_schSection_conj_padic k hτ p hg hx (comp_rat hφ hx) c hc1 hc2).symm

/-- **A `k`-endomorphism acting trivially on `π₁ᵉᵗ` fixes the rational points, over a number
field `k`** (see `comp_eq_of_conj_padic`). -/
theorem comp_eq_of_conj_numberField [NumberField k]
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {φ : X ⟶ X} (hφ : φ ≫ (X ↘ Spec (.of k)) = X ↘ Spec (.of k))
    (γ : fiber (geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ) ≫ φ) ≅
      fiber (geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)))
    (hγ : ∀ σ : π₁ᵉᵗ(geometricGenericPoint (curveGaloisData k hτ) X (curveEquivL k hτ)),
      σ = γ.conjAut (fundamentalGroupMap φ rfl σ))
    (hγb : fiberIsoMap (X ↘ Spec (.of k)) (comp_toSpec hφ _) rfl γ = Iso.refl _)
    {x : Spec (.of k) ⟶ X} (hx : x ≫ (X ↘ Spec (.of k)) = 𝟙 _) : x ≫ φ = x := by
  obtain ⟨c, hc1, hc2⟩ := exists_conj_schSection_comp (curveGaloisData k hτ) (curveEquivL k hτ)
    (curveEquivL_algebraMap k hτ) rfl hφ γ hγ hγb x hx
  exact (eq_of_schSection_conj_numberField k hτ hg hx (comp_rat hφ hx) c hc1 hc2).symm

end Curve

end CurvesJacobian.LocAn.SectionBridge
