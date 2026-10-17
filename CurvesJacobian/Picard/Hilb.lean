/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RelEffCartierFinite
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The Hilbert functor of points

For a morphism `f : X ⟶ S` and `d : ℕ`, `Hilb^d_{X/S}(T)` is the set of closed subschemes
`Z ⊆ X_T = X ×_S T` such that `Z → T` is finite locally free of degree `d` (Stacks, Section 44.2,
Tag 0B94). Here "finite locally free of degree `d`" is: finite, flat, locally of finite
presentation, with `Scheme.Hom.finrank` constantly `d`.

* `HilbPoint f d T` and the pullback `HilbPoint.pullback` along `T' ⟶ T` (the ideal sheaf is
  pulled back along `X_{T'} → X_T`), giving the functor `hilbFunctor f d : (Over S)ᵒᵖ ⥤ Type u`.
* For a curve `C` over a perfect field `k` (`Belyi.IsCurveOver`), `hilbEquivRelEffCartier`:
  `Hilb^d_{C/k}(T)` is the set of relative effective Cartier divisors of degree `d` on
  `C ×_k T / T` (the description in the introduction of Stacks, Section 44.3, Tag 0B9C, made
  precise by Lemma 44.3.1, Tag 0B9D; see `CurvesJacobian.relEffCartier_iff`).

Representability for affine `X` over affine `S` (Stacks, Lemma 44.2.5, Tag 0B99) is proved in
`CurvesJacobian.Picard.HilbAffineRep` (`HilbAffine.isRepresentable_hilbSch`), using the Zariski
sheaf property (`CurvesJacobian.Picard.HilbSheaf`); the gluing for general `X` (Proposition
44.2.6, Tag 0B9A) is not done yet.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

variable {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)

/-- A `T`-point of `Hilb^d_{X/S}` (Stacks, Section 44.2, Tag 0B94): a closed subscheme of
`X ×_S T` which is finite locally free of degree `d` over `T`. -/
structure HilbPoint (T : Over S) where
  /-- the ideal sheaf of the closed subscheme -/
  ideal : (pullback f T.hom).IdealSheafData
  isFinite : IsFinite (ideal.subschemeι ≫ pullback.snd f T.hom)
  flat : Flat (ideal.subschemeι ≫ pullback.snd f T.hom)
  locallyOfFinitePresentation :
    LocallyOfFinitePresentation (ideal.subschemeι ≫ pullback.snd f T.hom)
  finrank_eq : ∀ t : T.left, (ideal.subschemeι ≫ pullback.snd f T.hom).finrank t = d

namespace HilbPoint

variable {f d}

@[ext]
lemma ext {T : Over S} {P Q : HilbPoint f d T} (h : P.ideal = Q.ideal) : P = Q := by
  cases P; cases Q; cases h; rfl

variable (f) {T T' T'' : Over S}

/-- The map `X_{T'} → X_T` induced by `T' ⟶ T` over `S`. -/
abbrev baseChangeMap (h : T' ⟶ T) : pullback f T'.hom ⟶ pullback f T.hom :=
  pullback.lift (pullback.fst f T'.hom) (pullback.snd f T'.hom ≫ h.left)
    (by rw [Category.assoc, Over.w h, pullback.condition])

lemma isPullback_baseChangeMap (h : T' ⟶ T) :
    IsPullback (baseChangeMap f h) (pullback.snd f T'.hom) (pullback.snd f T.hom) h.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f T.hom) (v₁₃ := f) (h₂₂ := T.hom) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f T.hom)
  convert IsPullback.of_hasPullback f T'.hom using 1
  · exact pullback.lift_fst _ _ _
  · simp

lemma baseChangeMap_id : baseChangeMap f (𝟙 T) = 𝟙 _ := by
  ext <;> simp [baseChangeMap]

lemma baseChangeMap_comp (h : T'' ⟶ T') (h' : T' ⟶ T) :
    baseChangeMap f (h ≫ h') = baseChangeMap f h ≫ baseChangeMap f h' := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    refine (pullback.lift_fst _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (baseChangeMap f h ≫ ·) (pullback.lift_fst _ _ _)).symm
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc]
    refine (pullback.lift_snd _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (baseChangeMap f h ≫ ·) (pullback.lift_snd _ _ _)).symm
    rw [← Category.assoc]
    refine Eq.trans ?_ (congrArg (· ≫ h'.left) (pullback.lift_snd _ _ _)).symm
    rw [Over.comp_left, Category.assoc]

variable {f}

/-- The pullback of `Z ⊆ X_T` along `T' ⟶ T`: the closed subscheme `Z ×_T T' ⊆ X_{T'}`. -/
def pullback (P : HilbPoint f d T) (h : T' ⟶ T) : HilbPoint f d T' :=
  have sq : IsPullback (Limits.pullback.snd (baseChangeMap f h) P.ideal.subschemeι)
      (Limits.pullback.fst (baseChangeMap f h) P.ideal.subschemeι ≫ Limits.pullback.snd f T'.hom)
      (P.ideal.subschemeι ≫ Limits.pullback.snd f T.hom) h.left :=
    (IsPullback.of_hasPullback (baseChangeMap f h) P.ideal.subschemeι).flip.paste_vert
      (isPullback_baseChangeMap f h)
  have e : (P.ideal.comap (baseChangeMap f h)).subschemeι ≫ Limits.pullback.snd f T'.hom =
      (P.ideal.comapIso (baseChangeMap f h)).hom ≫
        (Limits.pullback.fst (baseChangeMap f h) P.ideal.subschemeι ≫
          Limits.pullback.snd f T'.hom) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc]
  haveI := P.isFinite
  haveI := P.flat
  haveI := P.locallyOfFinitePresentation
  haveI : IsFinite (Limits.pullback.fst (baseChangeMap f h) P.ideal.subschemeι ≫
      Limits.pullback.snd f T'.hom) := MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  haveI : Flat (Limits.pullback.fst (baseChangeMap f h) P.ideal.subschemeι ≫
      Limits.pullback.snd f T'.hom) := MorphismProperty.of_isPullback (P := @Flat) sq ‹_›
  haveI : LocallyOfFinitePresentation (Limits.pullback.fst (baseChangeMap f h)
      P.ideal.subschemeι ≫ Limits.pullback.snd f T'.hom) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq ‹_›
  { ideal := P.ideal.comap (baseChangeMap f h)
    isFinite := by rw [e]; infer_instance
    flat := by rw [e]; infer_instance
    locallyOfFinitePresentation := by rw [e]; infer_instance
    finrank_eq := fun t ↦ by
      rw [e, Scheme.Hom.finrank_comp_left_of_isIso,
        Scheme.Hom.finrank_of_isPullback _ _ _ _ sq, P.finrank_eq] }

lemma pullback_ideal (P : HilbPoint f d T) (h : T' ⟶ T) :
    (P.pullback h).ideal = P.ideal.comap (baseChangeMap f h) := rfl

lemma pullback_id (P : HilbPoint f d T) : P.pullback (𝟙 T) = P := by
  ext1
  rw [pullback_ideal, baseChangeMap_id, Scheme.IdealSheafData.comap_id]

lemma pullback_comp (P : HilbPoint f d T) (h : T'' ⟶ T') (h' : T' ⟶ T) :
    P.pullback (h ≫ h') = (P.pullback h').pullback h := by
  ext1
  rw [pullback_ideal, pullback_ideal, pullback_ideal, baseChangeMap_comp,
    Scheme.IdealSheafData.comap_comp]

end HilbPoint

/-- The Hilbert functor of points `Hilb^d_{X/S} : (Sch/S)ᵒᵖ ⥤ Type` (Stacks, Section 44.2,
Tag 0B94). -/
def hilbFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := HilbPoint f d T.unop
  map h := ↾fun P ↦ P.pullback h.unop
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun P ↦ ?_
    exact P.pullback_id
  map_comp h h' := by
    refine ConcreteCategory.hom_ext _ _ fun P ↦ ?_
    exact P.pullback_comp h'.unop h.unop

section Curve

open Belyi

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  [PerfectField k] [IsCurveOver k C]

local notation "Sk" => Spec (CommRingCat.of k)

/-- For a curve `C` over a perfect field `k`, the `T`-points of `Hilb^d_{C/k}` are the relative
effective Cartier divisors of degree `d` on `C ×_k T / T` (Stacks, Section 44.3 introduction
(Tag 0B9C) via Lemma 44.3.1, Tag 0B9D). -/
def hilbEquivRelEffCartier (T : Over Sk) :
    HilbPoint (C ↘ Sk) d T ≃
      {D : RelEffCartier (pullback.snd (C ↘ Sk) T.hom) // ∀ t, D.degree t = d} where
  toFun P :=
    haveI := P.isFinite
    haveI := P.flat
    haveI := P.locallyOfFinitePresentation
    ⟨RelEffCartier.ofFiniteFlat C T.hom P.ideal, P.finrank_eq⟩
  invFun D :=
    { ideal := D.1.ideal
      isFinite := D.1.isFinite C T.hom
      flat := D.1.flat
      locallyOfFinitePresentation := D.1.locallyOfFinitePresentation C T.hom
      finrank_eq := D.2 }
  left_inv P := by ext1; rfl
  right_inv D := by
    obtain ⟨⟨I, h₁, h₂⟩, hD⟩ := D
    rfl

end Curve

end CurvesJacobian
