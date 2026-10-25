/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FieldExtIso
import Pi1.FundamentalGroup.HomotopyExact
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Specialisation of geometric points along a valuation ring

Let `A` be a valuation subring of a separably closed field `Ω` and `T = Spec A`. The étale
fundamental group of `T` at the generic geometric point `Spec Ω ⟶ T` is trivial
(`AlgebraicGeometry.FiniteEtale.subsingleton_pi1_vGen`: `A` is integrally closed in `Ω`, so
pi1's `galoisAction_surjective` applies to `Gal(Ω/Ω) = 1`). Hence every finite étale `T`-scheme
is split over its generic geometric point: for a morphism `π : T ⟶ X` and `B` finite étale over
`X`, the sections `s : T ⟶ B` over `π` are in bijection with the points of `B` over the geometric
point `Spec Ω ⟶ T ⟶ X` (`secPt_bijective`; abstractly, `bijective_map_terminal_of_subsingleton`
for a Galois category with trivial fundamental group).

This gives the **specialisation isomorphism of fibre functors**
`AlgebraicGeometry.FiniteEtale.spIso A π z : fiber (Spec Ω ⟶ T ⟶ X) ≅ fiber (z ≫ π)` for any
other geometric point `z` of `T` (e.g. the closed point `Spec κ(A) ⟶ T`): a point `Spec Ω ⟶ B`
extends uniquely to a section `T ⟶ B` over `π`, which is then restricted to `z`
(`spIso_hom_secPt`). It is **equivariant** for automorphisms `φ` of `T` over `X` covered by field
automorphisms of the two geometric points (`spIso_left_equivariant`); in particular it conjugates
the Galois action through a field-valued point at the generic point into the Galois action at
`z` (`spIso_conjAut_galoisAction`).
-/

open CategoryTheory Limits PreGaloisCategory

universe u

noncomputable section

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category.{u} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{u})
  [FiberFunctor F]

/-- **Trivial fundamental group ⇒ every point of a fibre comes from a unique section**: if
`Aut F` is trivial, then for a terminal object `T` and `t ∈ F(T)`, `Hom(T, X) → F(X)`,
`s ↦ F(s)(t)` is bijective. -/
theorem bijective_map_terminal_of_subsingleton [Subsingleton (Aut F)] {T : C}
    (hT : IsTerminal T) (t : F.obj T) (X : C) :
    Function.Bijective (fun s : T ⟶ X ↦ F.map s t) := by
  have hFT : IsTerminal (F.obj T) := hT.isTerminalObj F
  have hsub : ∀ a : F.obj T, a = t := fun a ↦ by
    have := hFT.hom_ext (𝟙 (F.obj T)) (FintypeCat.homMk fun _ ↦ t)
    exact congrArg (fun f : F.obj T ⟶ F.obj T ↦ f a) this
  refine ⟨fun s s' hss ↦ F.map_injective ?_, fun y ↦ ?_⟩
  · ext a
    rw [hsub a]
    exact hss
  · let f : (functorToAction F).obj T ⟶ (functorToAction F).obj X :=
      { hom := FintypeCat.homMk fun _ ↦ y
        comm := fun g ↦ by
          rw [Subsingleton.elim g 1, Action.ρ_one, Action.ρ_one]
          rfl }
    obtain ⟨s, hs⟩ := (functorToAction F).map_surjective f
    refine ⟨s, ?_⟩
    change ((functorToAction F).map s).hom t = y
    rw [hs]
    rfl

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

section Valuation

variable {Ω : Type u} [Field Ω] (A : ValuationSubring Ω)

/-- The generic geometric point `Spec Ω ⟶ Spec A` of a valuation subring `A ⊆ Ω`. -/
abbrev vGen : Spec (.of Ω) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω))

instance connectedSpace_specV : ConnectedSpace (Spec (.of A)) := inferInstance

/-- `Gal(Ω/Ω)` is trivial. -/
lemma subsingleton_algEquiv_self : Subsingleton (Ω ≃ₐ[Ω] Ω) :=
  ⟨fun σ τ ↦ AlgEquiv.ext fun a ↦ by
    rw [← mul_one a, ← smul_eq_mul, map_smul, map_smul, map_one, map_one]⟩

variable [IsSepClosed Ω]

/-- **`π₁ᵉᵗ` of a valuation ring at its generic geometric point is trivial** (`A` is integrally
closed in `Ω = Frac A`, so `Gal(Ω/Ω) → π₁ᵉᵗ(Spec A)` is surjective). -/
theorem subsingleton_pi1_vGen : Subsingleton π₁ᵉᵗ(vGen A) := by
  haveI := subsingleton_algEquiv_self (Ω := Ω)
  have hs := galoisAction_surjective Ω A (Ω := Ω) Subtype.val_injective fun x hx ↦ by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨y, hy⟩
  exact ⟨fun a b ↦ by
    obtain ⟨g, rfl⟩ := hs a
    obtain ⟨h, rfl⟩ := hs b
    rw [Subsingleton.elim g h]⟩

variable {X : Scheme.{u}} (π : Spec (.of A) ⟶ X)

/-- The sections of `B` over `π : Spec A ⟶ X`. -/
abbrev SecOver (B : FiniteEtale X) : Type u := {s : Spec (.of A) ⟶ B.left // s ≫ B.hom = π}

/-- The point of `B` over `z ≫ π` obtained by restricting a section over `π` to `z`. -/
def secPt {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (z : Spec (.of Ω') ⟶ Spec (.of A))
    (B : FiniteEtale X) (s : SecOver A π B) : (fiber (z ≫ π)).obj B :=
  (fiberObjEquivHom (z ≫ π) B).symm
    (Over.homMk (z ≫ s.1) ((Category.assoc _ _ _).trans (congrArg (z ≫ ·) s.2)))

omit [IsSepClosed Ω] in
lemma secPt_left {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (z : Spec (.of Ω') ⟶ Spec (.of A))
    (B : FiniteEtale X) (s : SecOver A π B) :
    (fiberObjEquivHom (z ≫ π) B (secPt A π z B s)).left = z ≫ s.1 := by
  rw [secPt, Equiv.apply_symm_apply]
  rfl

omit [IsSepClosed Ω] in
lemma secPt_ext {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {z : Spec (.of Ω') ⟶ Spec (.of A)}
    {B : FiniteEtale X} {y y' : (fiber (z ≫ π)).obj B}
    (h : (fiberObjEquivHom (z ≫ π) B y).left = (fiberObjEquivHom (z ≫ π) B y').left) : y = y' :=
  (fiberObjEquivHom (z ≫ π) B).injective (Over.OverMorphism.ext h)

/-- The section of `π^* B` over `Spec A` corresponding to a section of `B` over `π`. -/
def secToSelf (B : FiniteEtale X) (s : SecOver A π B) : self (Spec (.of A)) ⟶ (pullback π).obj B :=
  MorphismProperty.Over.homMk (pullback.lift s.1 (𝟙 _) (s.2.trans (Category.id_comp π).symm))
    (by change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _; rw [pullback.lift_snd]) trivial

omit [IsSepClosed Ω] in
lemma secToSelf_left_fst (B : FiniteEtale X) (s : SecOver A π B) :
    (secToSelf A π B s).left ≫ pullback.fst B.hom π = s.1 := by
  change pullback.lift _ _ _ ≫ _ = _
  rw [pullback.lift_fst]

/-- The left component of a point of `self T` over a geometric point `z` is `z`. -/
lemma self_left {T : Scheme.{u}} {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (z : Spec (.of Ω') ⟶ T)
    (t : (fiber z).obj (self T)) : (fiberObjEquivHom z (self T) t).left = z := by
  have := Over.w (fiberObjEquivHom z (self T) t)
  change _ ≫ 𝟙 T = z at this
  rwa [Category.comp_id] at this

/-- **Points over the generic geometric point extend uniquely to sections**: for `B` finite étale
over `X` and `π : Spec A ⟶ X`, restriction of sections over `π` to `Spec Ω ⟶ Spec A` is a
bijection onto the fibre of `B` over `Spec Ω ⟶ Spec A ⟶ X`. -/
theorem secPt_bijective (B : FiniteEtale X) : Function.Bijective (secPt A π (vGen A) B) := by
  haveI := subsingleton_pi1_vGen A
  let t : (fiber (vGen A)).obj (self (Spec (.of A))) :=
    (fiberObjEquivHom (vGen A) (self (Spec (.of A)))).symm
      (Over.homMk (vGen A) (Category.comp_id _))
  have hb := bijective_map_terminal_of_subsingleton (fiber (vGen A))
    (isTerminalSelf (Spec (.of A))) t ((pullback π).obj B)
  have hpt : ∀ m : self (Spec (.of A)) ⟶ (pullback π).obj B,
      (fiberObjEquivHom (vGen A) _ ((fiber (vGen A)).map m t)).left = vGen A ≫ m.left := by
    intro m
    rw [← fiberObjEquivHom_naturality]
    change (fiberObjEquivHom (vGen A) (self (Spec (.of A))) t).left ≫ m.left = _
    exact congrArg (· ≫ m.left) (self_left _ t)
  refine ⟨fun s s' hss ↦ ?_, fun y ↦ ?_⟩
  · have h1 : vGen A ≫ s.1 = vGen A ≫ s'.1 := by
      rw [← secPt_left A π (vGen A) B s, ← secPt_left A π (vGen A) B s', hss]
    have h2 : (fiber (vGen A)).map (secToSelf A π B s) t =
        (fiber (vGen A)).map (secToSelf A π B s') t := by
      refine (fiberObjEquivHom (vGen A) _).injective (Over.OverMorphism.ext ?_)
      rw [hpt, hpt]
      apply pullback.hom_ext
      · exact (Category.assoc _ _ _).trans ((congrArg (vGen A ≫ ·)
          (secToSelf_left_fst A π B s)).trans (h1.trans ((congrArg (vGen A ≫ ·)
            (secToSelf_left_fst A π B s')).symm.trans (Category.assoc _ _ _).symm)))
      · change vGen A ≫ pullback.lift _ _ _ ≫ pullback.snd _ _ =
          vGen A ≫ pullback.lift _ _ _ ≫ pullback.snd _ _
        rw [pullback.lift_snd, pullback.lift_snd]
    have h3 := hb.1 h2
    apply Subtype.ext
    rw [← secToSelf_left_fst A π B s, ← secToSelf_left_fst A π B s', h3]
  · let yT := (pullbackFiberIso π (rfl : vGen A ≫ π = _)).inv.app B y
    obtain ⟨m, hm⟩ := hb.2 yT
    have hmw : (m.left ≫ pullback.fst B.hom π) ≫ B.hom = π := by
      have hw := MorphismProperty.Over.w m
      change m.left ≫ pullback.snd B.hom π = 𝟙 _ at hw
      have hc : pullback.fst B.hom π ≫ B.hom = pullback.snd B.hom π ≫ π := pullback.condition
      exact (Category.assoc _ _ _).trans ((congrArg (m.left ≫ ·) hc).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hw).trans (Category.id_comp π))))
    refine ⟨⟨m.left ≫ pullback.fst B.hom π, hmw⟩, secPt_ext A π ?_⟩
    rw [secPt_left]
    have hy : y = (pullbackFiberIso π (rfl : vGen A ≫ π = _)).hom.app B yT :=
      (FintypeCat.inv_hom_id_apply ((pullbackFiberIso π (rfl : vGen A ≫ π = _)).app B) y).symm
    rw [hy, pullbackFiberIso_hom_app_left]
    change _ = (fiberObjEquivHom (vGen A) _ yT).left ≫ _
    rw [show yT = (fiber (vGen A)).map m t from hm.symm, hpt]
    exact (Category.assoc _ _ _).symm

/-- The inverse of `secPt_bijective`: the section extending a point over the generic point. -/
def extSec (B : FiniteEtale X) : (fiber (vGen A ≫ π)).obj B ≃ SecOver A π B :=
  (Equiv.ofBijective _ (secPt_bijective A π B)).symm

lemma secPt_extSec (B : FiniteEtale X) (y : (fiber (vGen A ≫ π)).obj B) :
    secPt A π (vGen A) B (extSec A π B y) = y :=
  (Equiv.ofBijective _ (secPt_bijective A π B)).apply_symm_apply y

lemma extSec_secPt (B : FiniteEtale X) (s : SecOver A π B) :
    extSec A π B (secPt A π (vGen A) B s) = s :=
  (Equiv.ofBijective _ (secPt_bijective A π B)).symm_apply_apply s

omit [IsSepClosed Ω] in
lemma secPt_map {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (z : Spec (.of Ω') ⟶ Spec (.of A))
    {B B' : FiniteEtale X} (f : B ⟶ B') (s : SecOver A π B) :
    (fiber (z ≫ π)).map f (secPt A π z B s) =
      secPt A π z B' ⟨s.1 ≫ f.left,
        (Category.assoc _ _ _).trans
          ((congrArg (s.1 ≫ ·) (MorphismProperty.Over.w f)).trans s.2)⟩ := by
  refine secPt_ext A π ?_
  rw [← fiberObjEquivHom_naturality]
  change (fiberObjEquivHom (z ≫ π) B (secPt A π z B s)).left ≫ f.left = _
  erw [secPt_left, secPt_left]
  exact Category.assoc _ _ _

variable {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (z : Spec (.of Ω') ⟶ Spec (.of A))

/-- **Specialisation**, as a morphism of fibre functors `fiber (Spec Ω ⟶ T ⟶ X) ⟶ fiber (z ≫ π)`:
extend a point to a section over `π` and restrict it to `z`. -/
def spHom : fiber (vGen A ≫ π) ⟶ fiber (z ≫ π) where
  app B := FintypeCat.homMk fun y ↦ secPt A π z B (extSec A π B y)
  naturality {B B'} f := by
    ext y
    change secPt A π z B' (extSec A π B' ((fiber (vGen A ≫ π)).map f y)) =
      (fiber (z ≫ π)).map f (secPt A π z B (extSec A π B y))
    conv_lhs => rw [← secPt_extSec A π B y, secPt_map, extSec_secPt]
    rw [secPt_map]

lemma spHom_app_secPt (B : FiniteEtale X) (s : SecOver A π B) :
    (spHom A π z).app B (secPt A π (vGen A) B s) = secPt A π z B s := by
  change secPt A π z B (extSec A π B (secPt A π (vGen A) B s)) = _
  rw [extSec_secPt]

variable [ConnectedSpace X]

instance : IsIso (spHom A π z) := isIso_of_fiberFunctor _ _ _

/-- **The specialisation isomorphism of fibre functors** `fiber (Spec Ω ⟶ Spec A ⟶ X) ≅
fiber (z ≫ π)`. -/
def spIso : fiber (vGen A ≫ π) ≅ fiber (z ≫ π) := asIso (spHom A π z)

lemma spIso_hom_secPt (B : FiniteEtale X) (s : SecOver A π B) :
    (spIso A π z).hom.app B (secPt A π (vGen A) B s) = secPt A π z B s :=
  spHom_app_secPt A π z B s

/-- **Equivariance of specialisation**: let `φ : Spec A ⟶ Spec A` be an automorphism over `X`
(`φ ≫ π = π`), covered by `σ₁ : Ω → Ω` at the generic point and by `σ₂ : Ω' → Ω'` at `z`. If the
point `y'` is `Spec σ₁ ≫ y`, then its specialisation is `Spec σ₂` composed with the
specialisation of `y`. -/
theorem spIso_left_equivariant (φ : Spec (.of A) ⟶ Spec (.of A)) (hφ : φ ≫ π = π)
    (σ₁ : Ω →+* Ω) (σ₂ : Ω' →+* Ω')
    (h₁ : Spec.map (CommRingCat.ofHom σ₁) ≫ vGen A = vGen A ≫ φ)
    (h₂ : Spec.map (CommRingCat.ofHom σ₂) ≫ z = z ≫ φ) (B : FiniteEtale X)
    (y y' : (fiber (vGen A ≫ π)).obj B)
    (hy : (fiberObjEquivHom _ B y').left =
      Spec.map (CommRingCat.ofHom σ₁) ≫ (fiberObjEquivHom _ B y).left) :
    (fiberObjEquivHom _ B ((spIso A π z).hom.app B y')).left =
      Spec.map (CommRingCat.ofHom σ₂) ≫
        (fiberObjEquivHom _ B ((spIso A π z).hom.app B y)).left := by
  obtain ⟨s, rfl⟩ := (secPt_bijective A π B).2 y
  let s' : SecOver A π B :=
    ⟨φ ≫ s.1, (Category.assoc _ _ _).trans ((congrArg (φ ≫ ·) s.2).trans hφ)⟩
  have hy' : y' = secPt A π (vGen A) B s' := by
    refine secPt_ext A π ?_
    rw [hy, secPt_left, secPt_left, ← Category.assoc, h₁, Category.assoc]
  rw [hy', spIso_hom_secPt, spIso_hom_secPt, secPt_left, secPt_left]
  change z ≫ φ ≫ s.1 = _
  rw [← Category.assoc, ← h₂, Category.assoc]

/-- **Specialisation conjugates Galois actions**: in the situation of `spIso_left_equivariant`,
with field-valued points `j₁ : Spec F₁ ⟶ X`, `j₂ : Spec F₂ ⟶ X` through which the generic point
and `z` factor, the specialisation isomorphism conjugates the action of `g₁ ∈ Gal(Ω/F₁)` into the
action of `g₂ ∈ Gal(Ω'/F₂)`. -/
theorem spIso_conjAut_galoisAction (F₁ F₂ : Type u) [Field F₁] [Field F₂] [Algebra F₁ Ω]
    [Algebra F₂ Ω'] [IsGalois F₁ Ω] [IsGalois F₂ Ω'] (j₁ : Spec (.of F₁) ⟶ X)
    (j₂ : Spec (.of F₂) ⟶ X) (hj₁ : Spec.map (CommRingCat.ofHom (algebraMap F₁ Ω)) ≫ j₁ =
      vGen A ≫ π)
    (hj₂ : Spec.map (CommRingCat.ofHom (algebraMap F₂ Ω')) ≫ j₂ = z ≫ π)
    (g₁ : Ω ≃ₐ[F₁] Ω) (g₂ : Ω' ≃ₐ[F₂] Ω') (φ : Spec (.of A) ⟶ Spec (.of A)) (hφ : φ ≫ π = π)
    (h₁ : Spec.map (CommRingCat.ofHom (g₁ : Ω →+* Ω)) ≫ vGen A = vGen A ≫ φ)
    (h₂ : Spec.map (CommRingCat.ofHom (g₂ : Ω' →+* Ω')) ≫ z = z ≫ φ) :
    (spIso A π z).conjAut (galoisAction F₁ j₁ hj₁ g₁) = galoisAction F₂ j₂ hj₂ g₂ := by
  refine ext_of_hom_app_left fun B w ↦ ?_
  rw [galoisAction_hom_app_left, Iso.conjAut_apply]
  set e := spIso A π z
  obtain ⟨y, rfl⟩ : ∃ y, e.hom.app B y = w :=
    ⟨e.inv.app B w, FintypeCat.inv_hom_id_apply (e.app B) w⟩
  change (fiberObjEquivHom _ B (e.hom.app B ((galoisAction F₁ j₁ hj₁ g₁).hom.app B
    (e.inv.app B (e.hom.app B y))))).left = _
  rw [show e.inv.app B (e.hom.app B y) = y from FintypeCat.hom_inv_id_apply (e.app B) y]
  exact spIso_left_equivariant A π z φ hφ _ _ h₁ h₂ B y _ (galoisAction_hom_app_left _ _ _ _ _ _)

end Valuation

/-- Transport of a Galois action along an equality of geometric points. -/
lemma eqToIso_conjAut_galoisAction {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (F : Type u) [Field F] [Algebra F Ω] [IsGalois F Ω] (j : Spec (.of F) ⟶ X)
    {η₁ η₂ : Spec (.of Ω) ⟶ X} (h : η₁ = η₂)
    (hj : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = η₁) (g : Ω ≃ₐ[F] Ω) :
    (eqToIso (congrArg fiber h)).conjAut (galoisAction F j hj g) =
      galoisAction F j (hj.trans h) g := by
  subst h
  simp [Iso.conjAut_apply]

end AlgebraicGeometry.FiniteEtale
