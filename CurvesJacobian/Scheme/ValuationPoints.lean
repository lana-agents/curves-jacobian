/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Points of an integral scheme with valuation-ring stalks as valuation subrings

Let `X` be an integral scheme all of whose stalks are valuation rings (e.g. a normal
one-dimensional Noetherian integral scheme such as a smooth curve over a field), with function
field `K = K(X)`. Each point `x` gives the valuation subring `𝒪_{X,x} ⊆ K`
(`CurvesJacobian.stalkValuationSubring`). We prove:

* `CurvesJacobian.stalkValuationSubring_injective`: if `X` is separated, `x ↦ 𝒪_{X,x}` is
  injective (valuative criterion of separatedness, Stacks Tag 01KZ, in the form of Mathlib's
  `IsSeparated.valuativeCriterion`);
* `CurvesJacobian.exists_stalkValuationSubring_eq`: if `π : X ⟶ Y` is universally closed, every
  valuation subring `O ⊆ K` for which `Spec K → X → Y` extends to `Spec O → Y` is a stalk
  (valuative criterion of universal closedness, Stacks Tag 01KF, Mathlib's
  `UniversallyClosed.eq_valuativeCriterion`, together with the maximality of valuation rings
  for domination);
* `CurvesJacobian.pointEquivValuationSubring`: for `X` separated and `π` universally closed,
  `X ≃ {O : ValuationSubring K // O extends over π}`.

For a proper curve over a field `k` this identifies the points of `X` with the valuation
subrings of `K(X)` containing `k` (`Scheme/CurvePlaces.lean`).
-/

open CategoryTheory Limits IsLocalRing AlgebraicGeometry

namespace CurvesJacobian

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- The canonical morphism `Spec K(X) ⟶ X` from the generic point. -/
noncomputable abbrev genericSpec (X : Scheme.{u}) [IsIntegral X] :
    Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

lemma genericPoint_specializes (x : X) : genericPoint X ⤳ x :=
  (genericPoint_spec X).specializes trivial

lemma ofHom_algebraMap_stalk (x : X) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes (genericPoint_specializes x) :=
  rfl

@[reassoc]
lemma SpecMap_algebraMap_stalk_fromSpecStalk (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = genericSpec X := by
  rw [ofHom_algebraMap_stalk]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

lemma algebraMap_stalk_injective (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
  IsFractionRing.injective _ _

variable (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))

/-- The stalk `𝒪_{X,x}`, viewed as a valuation subring of the function field. -/
noncomputable def stalkValuationSubring (x : X) : ValuationSubring X.functionField where
  toSubring := (algebraMap (X.presheaf.stalk x) X.functionField).range
  mem_or_inv_mem' f := by
    haveI := hX x
    rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) f with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, ha⟩

lemma mem_stalkValuationSubring_iff (x : X) (f : X.functionField) :
    f ∈ stalkValuationSubring hX x ↔ ∃ s, algebraMap (X.presheaf.stalk x) X.functionField s = f :=
  Iff.rfl

/-- The ring isomorphism `𝒪_{X,x} → O` onto a valuation subring `O` equal to the stalk. -/
noncomputable def stalkToValuationSubring (x : X) {O : ValuationSubring X.functionField}
    (hO : stalkValuationSubring hX x = O) : X.presheaf.stalk x ⟶ CommRingCat.of O :=
  CommRingCat.ofHom <| (algebraMap (X.presheaf.stalk x) X.functionField).codRestrict O.toSubring
    fun s ↦ hO ▸ ⟨s, rfl⟩

lemma coe_stalkToValuationSubring (x : X) {O : ValuationSubring X.functionField}
    (hO : stalkValuationSubring hX x = O) (s : X.presheaf.stalk x) :
    ((stalkToValuationSubring hX x hO s : O) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField s :=
  rfl

instance isLocalHom_stalkToValuationSubring (x : X) {O : ValuationSubring X.functionField}
    (hO : stalkValuationSubring hX x = O) : IsLocalHom (stalkToValuationSubring hX x hO).hom := by
  refine ⟨fun s hs ↦ ?_⟩
  obtain ⟨u, hu⟩ := hs
  have hinv : ((u⁻¹ : Oˣ) : X.functionField) ∈ stalkValuationSubring hX x := by
    rw [hO]; exact (u⁻¹ : Oˣ).1.2
  obtain ⟨t, ht⟩ := hinv
  refine IsUnit.of_mul_eq_one t (algebraMap_stalk_injective x ?_)
  rw [map_mul, map_one, ht, ← coe_stalkToValuationSubring hX x hO, ← hu]
  exact congrArg Subtype.val u.mul_inv

@[reassoc]
lemma SpecMap_stalkToValuationSubring_fromSpecStalk (x : X)
    {O : ValuationSubring X.functionField} (hO : stalkValuationSubring hX x = O) :
    Spec.map (CommRingCat.ofHom (algebraMap O X.functionField)) ≫
      Spec.map (stalkToValuationSubring hX x hO) ≫ X.fromSpecStalk x = genericSpec X := by
  rw [← Spec.map_comp_assoc]
  have : stalkToValuationSubring hX x hO ≫ CommRingCat.ofHom (algebraMap O X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    ext s; rfl
  rw [this]
  exact SpecMap_algebraMap_stalk_fromSpecStalk x

lemma stalkToValuationSubring_closedPoint (x : X) {O : ValuationSubring X.functionField}
    (hO : stalkValuationSubring hX x = O) :
    (Spec.map (stalkToValuationSubring hX x hO) ≫ X.fromSpecStalk x) (closedPoint O) = x := by
  rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- **Injectivity**: on a separated integral scheme with valuation-ring stalks, distinct points
have distinct local rings in the function field. -/
theorem stalkValuationSubring_injective [X.IsSeparated] :
    Function.Injective (stalkValuationSubring hX) := by
  intro x y hxy
  set O := stalkValuationSubring hX x
  let S : ValuativeCommSq (terminal.from X) :=
    { R := O, K := X.functionField, i₁ := genericSpec X, i₂ := terminal.from _,
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have hU := IsSeparated.valuativeCriterion (terminal.from X) S
  let lx : S.commSq.LiftStruct :=
    { l := Spec.map (stalkToValuationSubring hX x rfl) ≫ X.fromSpecStalk x
      fac_left := SpecMap_stalkToValuationSubring_fromSpecStalk hX x rfl
      fac_right := terminal.hom_ext _ _ }
  let ly : S.commSq.LiftStruct :=
    { l := Spec.map (stalkToValuationSubring hX y hxy.symm) ≫ X.fromSpecStalk y
      fac_left := SpecMap_stalkToValuationSubring_fromSpecStalk hX y hxy.symm
      fac_right := terminal.hom_ext _ _ }
  have hl : lx.l = ly.l := congrArg CommSq.LiftStruct.l (Subsingleton.elim lx ly)
  have := congrArg (fun f : Spec (CommRingCat.of O) ⟶ X ↦ f (closedPoint O)) hl
  simp only [lx, ly] at this
  rwa [stalkToValuationSubring_closedPoint, stalkToValuationSubring_closedPoint] at this

/-- `O` **extends over** `π : X ⟶ Y`: the composite `Spec K(X) ⟶ X ⟶ Y` extends to
`Spec O ⟶ Y`. For `Y = Spec k` this means `k ⊆ O`. -/
def ExtendsOver {Y : Scheme.{u}} (π : X ⟶ Y) (O : ValuationSubring X.functionField) : Prop :=
  ∃ g : Spec (CommRingCat.of O) ⟶ Y,
    Spec.map (CommRingCat.ofHom (algebraMap O X.functionField)) ≫ g = genericSpec X ≫ π

lemma extendsOver_stalkValuationSubring {Y : Scheme.{u}} (π : X ⟶ Y) (x : X) :
    ExtendsOver π (stalkValuationSubring hX x) :=
  ⟨Spec.map (stalkToValuationSubring hX x rfl) ≫ X.fromSpecStalk x ≫ π, by
    rw [← SpecMap_stalkToValuationSubring_fromSpecStalk_assoc hX x rfl]⟩

/-- **Existence**: for `π` universally closed, every valuation subring extending over `π` is
the local ring of a point. -/
theorem exists_stalkValuationSubring_eq {Y : Scheme.{u}} (π : X ⟶ Y) [UniversallyClosed π]
    (O : ValuationSubring X.functionField) (hO : ExtendsOver π O) :
    ∃ x, stalkValuationSubring hX x = O := by
  obtain ⟨g, hg⟩ := hO
  have hE : ValuativeCriterion.Existence π := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) π := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  let S : ValuativeCommSq π :=
    { R := O, K := X.functionField, i₁ := genericSpec X, i₂ := g, commSq := ⟨hg.symm⟩ }
  obtain ⟨l, hl₁, -⟩ := (hE S).exists_lift
  refine ⟨l (closedPoint O), ?_⟩
  let β := Scheme.stalkClosedPointTo l
  have hβ : β ≫ CommRingCat.ofHom (algebraMap O X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk (l (closedPoint O))) X.functionField) := by
    rw [← Spec.map_inj, ← cancel_mono (X.fromSpecStalk _), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, SpecMap_algebraMap_stalk_fromSpecStalk]
    exact hl₁
  have hβ' : ∀ s, ((β s : O) : X.functionField) =
      algebraMap (X.presheaf.stalk (l (closedPoint O))) X.functionField s := fun s ↦
    congrArg (fun φ ↦ φ s) hβ
  ext f
  constructor
  · rintro ⟨s, rfl⟩
    rw [← hβ']
    exact (β s).2
  · intro hf
    by_contra hn
    have hinv := ((stalkValuationSubring hX (l (closedPoint O))).mem_or_inv_mem f).resolve_left hn
    obtain ⟨s, hs⟩ := hinv
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hn (zero_mem _)
    have hsu : ¬ IsUnit s := by
      intro hu
      apply hn
      obtain ⟨t, ht⟩ := hu.exists_right_inv
      refine ⟨t, ?_⟩
      have h1 := congrArg (algebraMap (X.presheaf.stalk (l (closedPoint O))) X.functionField) ht
      rw [map_mul, map_one, hs] at h1
      exact ((inv_mul_eq_one₀ hf0).1 h1).symm
    apply hsu
    haveI : IsLocalHom β.hom := Scheme.isLocalHom_stalkClosedPointTo l
    refine isUnit_of_map_unit β.hom s (IsUnit.of_mul_eq_one ⟨f, hf⟩ (Subtype.ext ?_))
    change ((β s : O) : X.functionField) * f = 1
    rw [hβ', hs, inv_mul_cancel₀ hf0]

/-- For `X` separated, `π` universally closed and all stalks valuation rings, the points of `X`
are in bijection with the valuation subrings of `K(X)` extending over `π`. -/
noncomputable def pointEquivValuationSubring [X.IsSeparated] {Y : Scheme.{u}} (π : X ⟶ Y)
    [UniversallyClosed π] : X ≃ {O : ValuationSubring X.functionField // ExtendsOver π O} :=
  Equiv.ofBijective (fun x ↦ ⟨stalkValuationSubring hX x, extendsOver_stalkValuationSubring hX π x⟩)
    ⟨fun _ _ h ↦ stalkValuationSubring_injective hX (congrArg Subtype.val h),
      fun O ↦ (exists_stalkValuationSubring_eq hX π O.1 O.2).imp fun _ h ↦ Subtype.ext h⟩

end CurvesJacobian
