/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Hilb

/-!
# The Hilbert functor on the category of all schemes

Mathlib's representability criterion (`AlgebraicGeometry.Scheme.LocalRepresentability`, Stacks
Tag 01JJ) is stated for functors on `Scheme`, not on `Over S`. We therefore also regard
`Hilb^d_{X/S}` (Stacks, Section 44.2, Tag 0B94) as the functor
`T ↦ Σ (g : T ⟶ S), Hilb^d_{X/S}(T, g)` on all schemes (`hilbSch`); a scheme representing it
comes with its structure morphism to `S` (the first component of the universal point).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

variable {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}

namespace HilbPoint

/-- Transport of a point of `Hilb` along an equality of structure morphisms. -/
def cast {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) (P : HilbPoint f d (Over.mk g₁)) :
    HilbPoint f d (Over.mk g₂) :=
  P.pullback (Over.homMk (𝟙 T) (by rw [h]; exact Category.id_comp g₂))

lemma cast_rfl {T : Scheme.{u}} {g : T ⟶ S} (P : HilbPoint f d (Over.mk g)) :
    P.cast rfl = P := by
  rw [cast, show (Over.homMk (𝟙 T) (Category.id_comp g) : Over.mk g ⟶ Over.mk g) = 𝟙 _ by
      ext; rfl,
    pullback_id]

lemma heq_cast {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) (P : HilbPoint f d (Over.mk g₁)) :
    HEq P (P.cast h) := by
  subst h
  rw [cast_rfl]

lemma heq_iff {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) {P₁ : HilbPoint f d (Over.mk g₁)}
    {P₂ : HilbPoint f d (Over.mk g₂)} : HEq P₁ P₂ ↔ P₁.cast h = P₂ := by
  subst h
  rw [cast_rfl, heq_iff_eq]

lemma pullback_pullback {T T' T'' : Over S} (P : HilbPoint f d T) (a : T' ⟶ T) (b : T'' ⟶ T')
    (c : T'' ⟶ T) (h : b ≫ a = c) : (P.pullback a).pullback b = P.pullback c := by
  rw [← pullback_comp, h]

end HilbPoint

variable (f d)

/-- The Hilbert functor `Hilb^d_{X/S}` as a functor on all schemes:
`T ↦ Σ (g : T ⟶ S), Hilb^d_{X/S}(T, g)` (Stacks, Section 44.2, Tag 0B94). -/
def hilbSch : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Σ g : T.unop ⟶ S, HilbPoint f d (Over.mk g)
  map {T T'} h := ↾fun x ↦ ⟨h.unop ≫ x.1,
    x.2.pullback (Over.homMk h.unop rfl : Over.mk (h.unop ≫ x.1) ⟶ Over.mk x.1)⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨g, P⟩ := x
    refine Sigma.ext (Category.id_comp g) ((HilbPoint.heq_iff (Category.id_comp g)).mpr ?_)
    change (P.pullback _).pullback _ = P
    rw [HilbPoint.pullback_pullback _ _ _ (𝟙 _) (by ext; exact Category.id_comp _),
      HilbPoint.pullback_id]
  map_comp h h' := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨g, P⟩ := x
    refine Sigma.ext (Category.assoc _ _ _) ((HilbPoint.heq_iff (Category.assoc _ _ _)).mpr ?_)
    change (P.pullback _).pullback _ = (P.pullback _).pullback _
    rw [HilbPoint.pullback_pullback _ _ _ (Over.homMk (h'.unop ≫ h.unop) rfl)
        (by ext; exact Category.id_comp _),
      HilbPoint.pullback_pullback _ _ _ (Over.homMk (h'.unop ≫ h.unop) rfl) (by ext; rfl)]

end CurvesJacobian
