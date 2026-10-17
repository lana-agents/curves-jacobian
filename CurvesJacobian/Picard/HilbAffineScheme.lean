/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbSch
import CurvesJacobian.Picard.HilbAffineOpen
import CurvesJacobian.Picard.RelEffCartierBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Points of the Hilbert functor of an affine scheme with values in affine schemes

Let `X = Spec (R[x_i]/K) → S = Spec R` be a presented affine scheme over `Spec R` (`presMap K`)
and `F = hilbSch (presMap K) d`. For a ring `A`, an `A`-point `x` of `F` is a morphism
`Spec A → Spec R`, i.e. a ring map `φ : R → A`, together with a closed subscheme
`Z ⊆ X ×_S Spec A` finite locally free of degree `d` over `Spec A`. This file identifies such
points with ideals `J ⊆ A[x_i]` containing `K A[x_i]` with `A[x_i]/J` finite projective of
constant rank `d` (`IsHilbIdeal`), naturally in `A` (affine case of Stacks, Lemma 44.2.5,
Tag 0B99):

* `idealOf x`, with `map_le_idealOf`, `isHilbIdeal_idealOf` and `ext_of_idealOf`;
* `mk φ J`, with `mk_fst` and `idealOf_mk`;
* naturality: `idealOf_map` (pullback of `Z` corresponds to extension of ideals).

The key point is that `X ×_S Spec A ≅ Spec (A[x_i]/K A[x_i])`, since `Γ(X ×_S Spec A)` is a
pushout of rings (`isPushout_presMap`, `theta`, `ker_theta`).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite MvPolynomial

universe u

noncomputable section

namespace CurvesJacobian.HilbAffine

section Algebra

/-- A finite algebra is flat and of finite presentation iff it is a projective module. -/
lemma finite_flat_finitePresentation_iff {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] :
    (Module.Finite A B ∧ Module.Flat A B ∧ Algebra.FinitePresentation A B) ↔
      (Module.Finite A B ∧ Module.Projective A B) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    haveI := Module.FinitePresentation.of_finite_of_finitePresentation A B
    exact ⟨h1, Module.Flat.projective_of_finitePresentation⟩
  · rintro ⟨h1, h2⟩
    haveI := Module.finitePresentation_of_projective A B
    exact ⟨h1, inferInstance,
      (Module.FinitePresentation.iff_finitePresentation_of_finite A B).mp ‹_›⟩

/-- A morphism `f : Z ⟶ Spec A` from an affine scheme such that `A → Γ(Z)` factors as
`A → B ≅ Γ(Z)` is `Spec B → Spec A` up to isomorphism. -/
lemma eq_isoSpec_comp_SpecMap {Z : Scheme.{u}} [IsAffine Z] {A B : CommRingCat.{u}}
    (f : Z ⟶ Spec A) (α : A ⟶ B) (β : B ≅ Γ(Z, ⊤))
    (h : α ≫ β.hom = (Scheme.ΓSpecIso A).inv ≫ f.appTop) :
    f = (Z.isoSpec.hom ≫ Spec.map β.hom) ≫ Spec.map α := by
  rw [Category.assoc, ← Spec.map_comp, h, Spec.map_comp, ← Category.assoc,
    Scheme.isoSpec_hom_naturality, Category.assoc, ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id,
    Category.comp_id]

/-- For `f ≅ Spec B → Spec A`: finite, flat, of finite presentation with rank `d` iff `B` is a
finite projective `A`-module of constant rank `d`. -/
lemma props_iff_of_eq {Z : Scheme.{u}} {A : CommRingCat.{u}} {B : Type u} [CommRing B]
    [Algebra A B] (f : Z ⟶ Spec A) (e : Z ⟶ Spec (CommRingCat.of B)) [IsIso e]
    (hf : f = e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ) :
    (IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ ∀ t, f.finrank t = d) ↔
      (Module.Finite A B ∧ Module.Projective A B ∧
        ∀ p, Module.rankAtStalk (R := A) B p = d) := by
  subst hf
  have e1 : IsFinite (e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      Module.Finite A B := by
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite), IsFinite.SpecMap_iff,
      CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  have e2 : Flat (e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔ Module.Flat A B := by
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @Flat), Flat.SpecMap_iff,
      CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  have e3 : LocallyOfFinitePresentation (e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      Algebra.FinitePresentation A B := by
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation),
      LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finitePresentation_algebraMap]
  have e4 : ∀ [Module.Finite A B] [Module.Flat A B] (t : PrimeSpectrum A),
      (e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).finrank t =
        Module.rankAtStalk (R := A) B t := by
    intro _ _ t
    haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
      infer_instance
    haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
      infer_instance
    rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    haveI := e1.mp h1
    haveI := e2.mp h2
    obtain ⟨h1, h2⟩ := (finite_flat_finitePresentation_iff (A := A) (B := B)).mp
      ⟨e1.mp ‹_›, e2.mp ‹_›, e3.mp h3⟩
    exact ⟨h1, h2, fun p ↦ (e4 p).symm.trans (h4 p)⟩
  · rintro ⟨h1, h2, h4⟩
    obtain ⟨h1, h2, h3⟩ := (finite_flat_finitePresentation_iff (A := A) (B := B)).mpr ⟨h1, h2⟩
    haveI := h1
    haveI := h2
    exact ⟨e1.mpr h1, e2.mpr h2, e3.mpr h3, fun t ↦ (e4 t).trans (h4 t)⟩

end Algebra

variable {R : CommRingCat.{u}} {I : Type u}

variable (K : Ideal (MvPolynomial I R)) in
/-- The presented affine scheme `Spec (R[x_i]/K) → Spec R`. -/
abbrev presMap : Spec (CommRingCat.of (MvPolynomial I R ⧸ K)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K).comp MvPolynomial.C))

section Pushout

variable (K : Ideal (MvPolynomial I R)) {A : CommRingCat.{u}} (g : Spec A ⟶ Spec R)

/-- `A → Γ(X ×_S Spec A)`. -/
def constMap : A ⟶ Γ(pullback (presMap K) g, ⊤) :=
  (Scheme.ΓSpecIso A).inv ≫ (pullback.snd (presMap K) g).appTop

/-- `R[x]/K → Γ(X ×_S Spec A)`. -/
def coordMap : CommRingCat.of (MvPolynomial I R ⧸ K) ⟶ Γ(pullback (presMap K) g, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (pullback.fst (presMap K) g).appTop

lemma isPushout_presMap : IsPushout (CommRingCat.ofHom ((Ideal.Quotient.mk K).comp C))
    (Spec.preimage g) (coordMap K g) (constMap K g) := by
  refine (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback (presMap K) g)).of_iso
    (Scheme.ΓSpecIso R) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso A) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact Scheme.ΓSpecIso_naturality _
  · obtain ⟨φ, rfl⟩ := Spec.map_surjective g
    rw [Spec.preimage_map]
    exact Scheme.ΓSpecIso_naturality _
  · simp [coordMap]
  · simp [constMap]

/-- `A[x] → Γ(X ×_S Spec A)`; it is surjective with kernel `K A[x]` (`ker_theta`). -/
def theta : MvPolynomial I A →+* Γ(pullback (presMap K) g, ⊤) :=
  eval₂Hom (constMap K g).hom fun i ↦ (coordMap K g).hom (Ideal.Quotient.mk K (X i))

lemma theta_C (a : A) : theta K g (C a) = constMap K g a := eval₂Hom_C _ _ _

lemma theta_X (i : I) : theta K g (X i) = coordMap K g (Ideal.Quotient.mk K (X i)) :=
  eval₂Hom_X' _ _ _

lemma theta_comp_map : (theta K g).comp (MvPolynomial.map (Spec.preimage g).hom) =
    (coordMap K g).hom.comp (Ideal.Quotient.mk K) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_
  · have := congrArg (fun f ↦ f.hom r) (isPushout_presMap K g).w
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [RingHom.comp_apply, map_C, theta_C, RingHom.comp_apply, this]
  · rw [RingHom.comp_apply, map_X, theta_X, RingHom.comp_apply]

/-- The extended ideal `K A[x]`. -/
abbrev Kext : Ideal (MvPolynomial I A) := K.map (MvPolynomial.map (Spec.preimage g).hom)

lemma theta_map (p : MvPolynomial I R) :
    theta K g (MvPolynomial.map (Spec.preimage g).hom p) = coordMap K g (Ideal.Quotient.mk K p) :=
  RingHom.congr_fun (theta_comp_map K g) p

lemma Kext_le_ker : Kext K g ≤ RingHom.ker (theta K g) := by
  rw [Ideal.map_le_iff_le_comap]
  intro p hp
  rw [Ideal.mem_comap, RingHom.mem_ker, theta_map, Ideal.Quotient.eq_zero_iff_mem.mpr hp,
    map_zero]

/-- `A[x]/K A[x] → Γ(X ×_S Spec A)`. -/
def thetaBar : MvPolynomial I A ⧸ Kext K g →+* Γ(pullback (presMap K) g, ⊤) :=
  Ideal.Quotient.lift _ (theta K g) fun _ ha ↦ Kext_le_ker K g ha

lemma thetaBar_mk (p : MvPolynomial I A) :
    thetaBar K g (Ideal.Quotient.mk _ p) = theta K g p := rfl

/-- The inverse of `thetaBar`, from the universal property of the pushout. -/
def thetaInv : Γ(pullback (presMap K) g, ⊤) ⟶ CommRingCat.of (MvPolynomial I A ⧸ Kext K g) :=
  (isPushout_presMap K g).desc
    (CommRingCat.ofHom (Ideal.quotientMap _ (MvPolynomial.map (Spec.preimage g).hom)
      Ideal.le_comap_map))
    (CommRingCat.ofHom ((Ideal.Quotient.mk _).comp C)) (by
      ext r
      simp [Ideal.quotientMap_mk])

lemma coordMap_thetaInv : coordMap K g ≫ thetaInv K g =
    CommRingCat.ofHom (Ideal.quotientMap (Kext K g) (MvPolynomial.map (Spec.preimage g).hom)
      Ideal.le_comap_map) :=
  IsPushout.inl_desc _ _ _ _

lemma constMap_thetaInv : constMap K g ≫ thetaInv K g =
    CommRingCat.ofHom ((Ideal.Quotient.mk (Kext K g)).comp C) :=
  IsPushout.inr_desc _ _ _ _

lemma thetaInv_coordMap (q : MvPolynomial I R) :
    thetaInv K g (coordMap K g (Ideal.Quotient.mk K q)) =
      Ideal.Quotient.mk _ (MvPolynomial.map (Spec.preimage g).hom q) :=
  congrArg (fun f ↦ CommRingCat.Hom.hom f (Ideal.Quotient.mk K q)) (coordMap_thetaInv K g)

lemma thetaInv_constMap (a : A) :
    thetaInv K g (constMap K g a) = Ideal.Quotient.mk _ (C a) :=
  congrArg (fun f ↦ CommRingCat.Hom.hom f a) (constMap_thetaInv K g)

lemma thetaInv_comp : thetaInv K g ≫ CommRingCat.ofHom (thetaBar K g) = 𝟙 _ := by
  refine (isPushout_presMap K g).hom_ext ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      CommRingCat.hom_id, RingHom.id_apply]
    rw [thetaInv_coordMap, thetaBar_mk, theta_map]
  · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      CommRingCat.hom_id, RingHom.id_apply]
    rw [thetaInv_constMap, thetaBar_mk, theta_C]

lemma thetaBar_thetaInv (y : Γ(pullback (presMap K) g, ⊤)) :
    thetaBar K g (thetaInv K g y) = y :=
  congrArg (fun f ↦ f.hom y) (thetaInv_comp K g)

lemma thetaInv_thetaBar (y : MvPolynomial I A ⧸ Kext K g) :
    thetaInv K g (thetaBar K g y) = y := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [thetaBar_mk]
  induction p using MvPolynomial.induction_on with
  | C a => rw [theta_C, thetaInv_constMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, theta_X, thetaInv_coordMap, map_X, map_mul]

lemma theta_surjective : Function.Surjective (theta K g) := by
  intro y
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (thetaInv K g y)
  refine ⟨p, ?_⟩
  rw [← thetaBar_mk, hp, thetaBar_thetaInv]

lemma ker_theta : RingHom.ker (theta K g) = Kext K g := by
  refine le_antisymm (fun p hp ↦ ?_) (Kext_le_ker K g)
  rw [RingHom.mem_ker, ← thetaBar_mk] at hp
  have := thetaInv_thetaBar K g (Ideal.Quotient.mk _ p)
  rw [hp, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm

lemma preimage_comp {A' : CommRingCat.{u}} (ψ : A ⟶ A') :
    Spec.preimage (Spec.map ψ ≫ g) = Spec.preimage g ≫ ψ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp, Spec.preimage_map, Spec.preimage_map]

lemma Kext_comp {A' : CommRingCat.{u}} (ψ : A ⟶ A') :
    Kext K (Spec.map ψ ≫ g) = (Kext K g).map (MvPolynomial.map ψ.hom) := by
  have : (MvPolynomial.map (σ := I) ψ.hom).comp (MvPolynomial.map (Spec.preimage g).hom) =
      MvPolynomial.map (ψ.hom.comp (Spec.preimage g).hom) :=
    RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p
  rw [Kext, Kext, Ideal.map_map, this, preimage_comp, CommRingCat.hom_comp]

/-- Naturality of `theta` in `A`. -/
lemma theta_naturality {A' : CommRingCat.{u}} (ψ : A ⟶ A')
    (b : pullback (presMap K) (Spec.map ψ ≫ g) ⟶ pullback (presMap K) g)
    (h₁ : b ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map ψ) :
    b.appTop.hom.comp (theta K g) = (theta K (Spec.map ψ ≫ g)).comp (MvPolynomial.map ψ.hom) := by
  have hc : constMap K g ≫ b.appTop = ψ ≫ constMap K (Spec.map ψ ≫ g) := by
    rw [constMap, constMap, Category.assoc, ← Scheme.Hom.comp_appTop, h₂,
      Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]
  have hx : coordMap K g ≫ b.appTop = coordMap K (Spec.map ψ ≫ g) := by
    rw [coordMap, coordMap, Category.assoc, ← Scheme.Hom.comp_appTop, h₁]
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
  · rw [RingHom.comp_apply, theta_C, RingHom.comp_apply, map_C, theta_C]
    exact congrArg (fun f ↦ CommRingCat.Hom.hom f a) hc
  · rw [RingHom.comp_apply, theta_X, RingHom.comp_apply, map_X, theta_X]
    exact congrArg (fun f ↦ CommRingCat.Hom.hom f (Ideal.Quotient.mk K (X i))) hx

/-- The ideal of `A[x]` of a closed subscheme of `X ×_S Spec A`. -/
def idealOfSheaf (D : (pullback (presMap K) g).IdealSheafData) : Ideal (MvPolynomial I A) :=
  (D.ideal ⟨⊤, isAffineOpen_top _⟩).comap (theta K g)

/-- The closed subscheme of `X ×_S Spec A` of an ideal of `A[x]`. -/
def sheafOfIdeal (J : Ideal (MvPolynomial I A)) : (pullback (presMap K) g).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (J.map (theta K g))

lemma Kext_le_idealOfSheaf (D : (pullback (presMap K) g).IdealSheafData) :
    Kext K g ≤ idealOfSheaf K g D := fun p hp ↦ by
  have := Kext_le_ker K g hp
  rw [RingHom.mem_ker] at this
  rw [idealOfSheaf, Ideal.mem_comap, this]
  exact zero_mem _

lemma idealOfSheaf_sheafOfIdeal {J : Ideal (MvPolynomial I A)} (hJ : Kext K g ≤ J) :
    idealOfSheaf K g (sheafOfIdeal K g J) = J := by
  have h : (sheafOfIdeal K g J).ideal ⟨⊤, isAffineOpen_top _⟩ = J.map (theta K g) :=
    (Scheme.IdealSheafData.equivOfIsAffine (X := pullback (presMap K) g)).apply_symm_apply _
  rw [idealOfSheaf, h, Ideal.comap_map_of_surjective' _ (theta_surjective K g), ker_theta,
    sup_eq_left.mpr hJ]

lemma idealOfSheaf_injective {D D' : (pullback (presMap K) g).IdealSheafData}
    (h : idealOfSheaf K g D = idealOfSheaf K g D') : D = D' := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  have := congrArg (Ideal.map (theta K g)) h
  simp only [idealOfSheaf, Ideal.map_comap_of_surjective _ (theta_surjective K g)] at this
  exact this

/-- `A[x]/J ≅ Γ(X ×_S Spec A)/I_D` for `J = idealOfSheaf D`. -/
def sheafQuotEquiv (D : (pullback (presMap K) g).IdealSheafData) :
    (MvPolynomial I A ⧸ idealOfSheaf K g D) ≃+*
      (Γ(pullback (presMap K) g, ⊤) ⧸ D.ideal ⟨⊤, isAffineOpen_top _⟩) :=
  (Ideal.quotEquivOfEq (by rw [idealOfSheaf, ← RingHom.comap_ker, Ideal.mk_ker])).trans
    (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk _).comp (theta K g))
      (Ideal.Quotient.mk_surjective.comp (theta_surjective K g)))

lemma sheafQuotEquiv_mk (D : (pullback (presMap K) g).IdealSheafData) (p : MvPolynomial I A) :
    sheafQuotEquiv K g D (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (theta K g p) := rfl

/-- Pulling back a closed subscheme along `X ×_S Spec A' → X ×_S Spec A` extends its ideal. -/
lemma idealOfSheaf_comap {A' : CommRingCat.{u}} (ψ : A ⟶ A')
    (D : (pullback (presMap K) g).IdealSheafData)
    (b : pullback (presMap K) (Spec.map ψ ≫ g) ⟶ pullback (presMap K) g)
    (h₁ : b ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map ψ) :
    idealOfSheaf K (Spec.map ψ ≫ g) (D.comap b) =
      (idealOfSheaf K g D).map (MvPolynomial.map ψ.hom) := by
  have hb : b.appLE ⊤ ⊤ le_top = b.appTop := Scheme.Hom.appLE_eq_app b
  rw [idealOfSheaf, Scheme.IdealSheafData.ideal_comap_of_le D b ⟨⊤, isAffineOpen_top _⟩
    ⟨⊤, isAffineOpen_top _⟩ le_top, hb, idealOfSheaf]
  obtain ⟨J, hJ⟩ : ∃ J : Ideal (MvPolynomial I A),
      J.map (theta K g) = D.ideal ⟨⊤, isAffineOpen_top _⟩ :=
    ⟨_, Ideal.map_comap_of_surjective _ (theta_surjective K g) _⟩
  rw [← hJ, Ideal.map_map, theta_naturality K g ψ b h₁ h₂, ← Ideal.map_map,
    Ideal.comap_map_of_surjective' _ (theta_surjective K _), ker_theta,
    Ideal.comap_map_of_surjective' _ (theta_surjective K _), ker_theta, Ideal.map_sup,
    Kext_comp]

variable (d : ℕ)

/-- The closed subscheme `Z ⊆ X ×_S Spec A` of `D` is finite locally free of degree `d` over
`Spec A` iff `idealOfSheaf D` is an `A`-point of `Hilb^d` of the affine space. -/
theorem props_iff (D : (pullback (presMap K) g).IdealSheafData) :
    (IsFinite (D.subschemeι ≫ pullback.snd (presMap K) g) ∧
      Flat (D.subschemeι ≫ pullback.snd (presMap K) g) ∧
      LocallyOfFinitePresentation (D.subschemeι ≫ pullback.snd (presMap K) g) ∧
      ∀ t, (D.subschemeι ≫ pullback.snd (presMap K) g).finrank t = d) ↔
      IsHilbIdeal d (idealOfSheaf K g D) := by
  haveI : IsAffine D.subscheme := isAffine_of_isAffineHom D.subschemeι
  let β : CommRingCat.of (MvPolynomial I A ⧸ idealOfSheaf K g D) ≅ Γ(D.subscheme, ⊤) :=
    (sheafQuotEquiv K g D).toCommRingCatIso ≪≫ (D.subschemeObjIso ⟨⊤, isAffineOpen_top _⟩).symm
  have hι : D.subschemeι.appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal ⟨⊤, isAffineOpen_top _⟩)) ≫
        (D.subschemeObjIso ⟨⊤, isAffineOpen_top _⟩).inv :=
    D.subschemeι_app ⟨⊤, isAffineOpen_top _⟩
  have key := eq_isoSpec_comp_SpecMap (D.subschemeι ≫ pullback.snd (presMap K) g)
    (CommRingCat.ofHom (algebraMap A (MvPolynomial I A ⧸ idealOfSheaf K g D))) β ?_
  · have H := props_iff_of_eq (A := A) (B := MvPolynomial I A ⧸ idealOfSheaf K g D)
      (D.subschemeι ≫ pullback.snd (presMap K) g) (D.subscheme.isoSpec.hom ≫ Spec.map β.hom)
      key d
    exact H
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  rw [Scheme.Hom.comp_appTop, hι]
  change (D.subschemeObjIso _).inv (sheafQuotEquiv K g D (Ideal.Quotient.mk _ (C a))) =
    (D.subschemeObjIso _).inv (Ideal.Quotient.mk _ (constMap K g a))
  rw [sheafQuotEquiv_mk, theta_C]

end Pushout

section Points

variable {K : Ideal (MvPolynomial I R)} {d : ℕ} {A : CommRingCat.{u}}

/-- The ideal `J ⊆ A[x]` of the closed subscheme `Z ⊆ X ×_S Spec A ≅ Spec (A[x]/K A[x])` of an
`A`-point `x` of `Hilb^d`. -/
def idealOf (x : (hilbSch (presMap K) d).obj (op (Spec A))) : Ideal (MvPolynomial I A) :=
  idealOfSheaf K x.1 x.2.ideal

lemma map_le_idealOf (x : (hilbSch (presMap K) d).obj (op (Spec A))) :
    K.map (MvPolynomial.map (Spec.preimage x.1).hom) ≤ idealOf x :=
  Kext_le_idealOfSheaf K x.1 x.2.ideal

lemma isHilbIdeal_idealOf (x : (hilbSch (presMap K) d).obj (op (Spec A))) :
    IsHilbIdeal d (idealOf x) :=
  (props_iff K x.1 d x.2.ideal).mp
    ⟨x.2.isFinite, x.2.flat, x.2.locallyOfFinitePresentation, x.2.finrank_eq⟩

lemma ext_of_idealOf {x y : (hilbSch (presMap K) d).obj (op (Spec A))} (h1 : x.1 = y.1)
    (h2 : idealOf x = idealOf y) : x = y := by
  obtain ⟨g, P⟩ := x
  obtain ⟨g', P'⟩ := y
  obtain rfl : g = g' := h1
  obtain rfl : P = P' := HilbPoint.ext (idealOfSheaf_injective K g h2)
  rfl

/-- The `A`-point of `Hilb^d` given by `φ : R ⟶ A` and an ideal `J ⊇ K A[x]` with `A[x]/J`
finite projective of rank `d`. -/
def mk (φ : R ⟶ A) (J : Ideal (MvPolynomial I A))
    (hK : K.map (MvPolynomial.map φ.hom) ≤ J) (hJ : IsHilbIdeal d J) :
    (hilbSch (presMap K) d).obj (op (Spec A)) :=
  have hK' : Kext K (Spec.map φ) ≤ J := by rwa [Kext, Spec.preimage_map]
  have h := (props_iff K (Spec.map φ) d (sheafOfIdeal K (Spec.map φ) J)).mpr
    (by rwa [idealOfSheaf_sheafOfIdeal K _ hK'])
  ⟨Spec.map φ,
    { ideal := sheafOfIdeal K (Spec.map φ) J
      isFinite := h.1
      flat := h.2.1
      locallyOfFinitePresentation := h.2.2.1
      finrank_eq := h.2.2.2 }⟩

lemma mk_fst (φ : R ⟶ A) (J : Ideal (MvPolynomial I A))
    (hK : K.map (MvPolynomial.map φ.hom) ≤ J) (hJ : IsHilbIdeal d J) :
    (mk φ J hK hJ).1 = Spec.map φ := rfl

lemma idealOf_mk (φ : R ⟶ A) (J : Ideal (MvPolynomial I A))
    (hK : K.map (MvPolynomial.map φ.hom) ≤ J) (hJ : IsHilbIdeal d J) :
    idealOf (mk φ J hK hJ) = J :=
  idealOfSheaf_sheafOfIdeal K (Spec.map φ) (by rwa [Kext, Spec.preimage_map])

/-- Naturality: the pullback of `Z ⊆ X ×_S Spec A` along `Spec A' → Spec A` has ideal the
extension of the ideal of `Z`. -/
lemma idealOf_map {A' : CommRingCat.{u}} (ψ : A ⟶ A')
    (x : (hilbSch (presMap K) d).obj (op (Spec A))) :
    idealOf ((hilbSch (presMap K) d).map (Spec.map ψ).op x) =
      (idealOf x).map (MvPolynomial.map ψ.hom) := by
  obtain ⟨g, P⟩ := x
  exact idealOfSheaf_comap K g ψ P.ideal _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end Points

end CurvesJacobian.HilbAffine
