/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicProper
import CurvesJacobian.Picard.PicDimension
import CurvesJacobian.Picard.HilbLft

/-!
# The Jacobian of a curve as an abelian variety

Let `k` be a separably closed perfect field and `C` a curve of genus `g` over `k` with a rational
point `σ`.

* `CurvesJacobian.geometricallyIrreducible_of_surjective`: the image of a geometrically
  irreducible `S`-scheme under a surjective `S`-morphism is geometrically irreducible.
* **`CurvesJacobian.geometricallyIrreducible_hilbCurveHom`**: `Hilb^d_{C/k}` is geometrically
  irreducible over `k`, by induction on `d`: `Hilb^0` is a point (`surjective_hilbZeroPt`), and
  `Hilb^d ×_k C` (geometrically irreducible since `C` is geometrically integral and everything is
  universally open over a field) surjects onto `Hilb^{d+1}` (`surjective_hilbAdd`).
* **`CurvesJacobian.geometricallyIrreducible_picDegScheme`**: `Pic^d_{C/k,σ}` is geometrically
  irreducible, as the image of `Hilb^e_{C/k}` (`e ≥ g`) under `D ↦ [𝒪(D)] − N·[𝒪(x)]`
  (`surjective_picAbelHom`). Hence `Pic⁰_{C/k,σ}` is geometrically connected.
* `CurvesJacobian.IsAbelianVariety`: a group scheme over `S` which is proper, smooth and
  geometrically connected (over a field this is the usual definition; commutativity is a theorem,
  but for the Jacobian it is also recorded as an instance).
* **`CurvesJacobian.Jacobian C σ hσ`**: the Jacobian `J = Pic⁰_{C/k,σ}` (built from a chosen
  finite morphism `C ⟶ ℙ¹_k`, `IsCurveOver.exists_finite_to_P1`), with instances `GrpObj`,
  `IsCommMonObj`, `IsProper`, `Smooth`, `SmoothOfRelativeDimension g`, `GeometricallyIrreducible`,
  `GeometricallyConnected` and `IsAbelianVariety`, and the representability
  `Hom_k(T, J) ≅ Pic⁰_{C/k,σ}(T)` (`jacobianRepresentableBy`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Belyi Cech

section Generic

variable {X Y S : Scheme.{u}}

/-- The base change `X ×_S T ⟶ Y ×_S T` of an `S`-morphism `f : X ⟶ Y`. -/
abbrev bcOver (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S) (w : f ≫ q = p) {T : Scheme.{u}}
    (y : T ⟶ S) : pullback p y ⟶ pullback q y :=
  pullback.map p y q y f (𝟙 T) (𝟙 S) (by rw [Category.comp_id, w])
    (by rw [Category.comp_id, Category.id_comp])

/-- The base change of an `S`-morphism `f` along `y : T ⟶ S` is surjective if `f` is. -/
lemma surjective_bcOver (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    (w : f ≫ q = p) {T : Scheme.{u}} (y : T ⟶ S) [Surjective f] :
    Surjective (bcOver f p q w y) := by
  have h : IsPullback (bcOver f p q w y) (pullback.fst p y) (pullback.fst q y) f := by
    refine IsPullback.of_right (h₁₂ := pullback.snd q y) (h₂₂ := q) (v₁₃ := y) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback q y).flip
    have e : bcOver f p q w y ≫ pullback.snd q y = pullback.snd p y :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    rw [e, w]
    exact (IsPullback.of_hasPullback p y).flip
  exact MorphismProperty.of_isPullback h.flip ‹_›

/-- Isomorphisms are geometrically irreducible. -/
instance geometricallyIrreducible_of_isIso (f : X ⟶ Y) [IsIso f] : GeometricallyIrreducible f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  exact (pullback.snd f y).homeomorph.irreducibleSpace_iff.mpr inferInstance

/-- **The image of a geometrically irreducible `S`-scheme under a surjective `S`-morphism is
geometrically irreducible.** -/
lemma geometricallyIrreducible_of_surjective (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    (w : f ≫ q = p) [Surjective f] [GeometricallyIrreducible p] : GeometricallyIrreducible q := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  have hX : IrreducibleSpace ↥(pullback p y) :=
    pullback_of_geometrically (GeometricallyIrreducible.geometrically_irreducibleSpace (f := p))
      K y
  have hs := surjective_bcOver f p q w y
  exact Function.Surjective.irreducibleSpace (Scheme.Hom.continuous _) hs.surj

end Generic

section Hilb

variable (k : Type u) [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C]

instance (d : ℕ) : LocallyOfFinitePresentation (hilbCurveHom k C d) :=
  locallyOfFinitePresentation_hilbCurveHom k C d

/-- **`Hilb^d_{C/k}` is geometrically irreducible over `k`.** -/
theorem geometricallyIrreducible_hilbCurveHom :
    ∀ d : ℕ, GeometricallyIrreducible (hilbCurveHom k C d)
  | 0 => by
    haveI := surjective_hilbZeroPt k C
    exact geometricallyIrreducible_of_surjective (hilbZeroPt k C) _ _ (hilbZeroPt_comp k C)
  | d + 1 => by
    haveI := geometricallyIrreducible_hilbCurveHom d
    haveI := surjective_hilbAdd k C d
    haveI : GeometricallyIrreducible
        (pullback.snd (hilbCurveHom k C d) (C ↘ Spec (CommRingCat.of k)) ≫
          (C ↘ Spec (CommRingCat.of k))) :=
      GeometricallyIrreducible.comp _ _
    exact geometricallyIrreducible_of_surjective (hilbAdd k C d) _ _ (hilbAdd_comp k C d)

instance (d : ℕ) : GeometricallyIrreducible (hilbCurveHom k C d) :=
  geometricallyIrreducible_hilbCurveHom k C d

end Hilb

section Pic

variable {k : Type u} [Field k] [PerfectField k] [IsSepClosed k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- **`Pic^d_{C/k,σ}` is geometrically irreducible over `k`**: it is the image of the
geometrically irreducible `Hilb^e_{C/k}`, `e ≥ g`, under `D ↦ [𝒪(D)] − N·[𝒪(x)]`. -/
theorem geometricallyIrreducible_picDegScheme (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]
    (d : ℤ) : GeometricallyIrreducible (picDegScheme C σ hσ π d).hom := by
  haveI : IsAlgClosed k := IsSepClosed.isAlgClosed_of_perfectField k
  obtain ⟨xC, hx, hxW⟩ := exists_point_chart_inf C π
  obtain ⟨e, N, he, hg⟩ : ∃ e N : ℕ, (e : ℤ) = d + N ∧ genusNat k C ≤ e := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · exact ⟨genusNat k C + m, genusNat k C, by push_cast; ring, by omega⟩
    · exact ⟨genusNat k C, genusNat k C + m, by push_cast; ring, le_rfl⟩
  haveI := surjective_picAbelHom C σ hσ π xC hx hxW e N d he hg
  exact geometricallyIrreducible_of_surjective (picAbelHom C σ hσ π xC hx hxW e N d he) _ _
    (picAbelHom_comp C σ hσ π xC hx hxW e N d he)

instance (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π] (d : ℤ) :
    GeometricallyIrreducible (picDegScheme C σ hσ π d).hom :=
  geometricallyIrreducible_picDegScheme C σ hσ π d

end Pic

/-- **Abelian varieties.** A group scheme `A` over `S` is an abelian variety if it is proper,
smooth and geometrically connected over `S` (for `S` the spectrum of a field this is the usual
definition, e.g. Milne, *Abelian varieties*, §1). -/
class IsAbelianVariety {S : Scheme.{u}} (A : Over S) [GrpObj A] : Prop where
  isProper : IsProper A.hom
  smooth : Smooth A.hom
  geometricallyConnected : GeometricallyConnected A.hom

section Jacobian

variable (k : Type u) [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C]

/-- A chosen finite morphism `C ⟶ ℙ¹_k` (`IsCurveOver.exists_finite_to_P1`). -/
def curveToP1 : C ⟶ ProjectiveLine.scheme k :=
  (IsCurveOver.exists_finite_to_P1 k C).choose

instance : IsFinite (curveToP1 k C) :=
  (IsCurveOver.exists_finite_to_P1 k C).choose_spec

variable [IsSepClosed k] {k} (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- **The Jacobian** `J = Pic⁰_{C/k,σ}` of a curve `C` with a rational point `σ` over a separably
closed perfect field `k`, as a scheme over `k`. -/
abbrev Jacobian : Over (Spec (CommRingCat.of k)) :=
  picZeroScheme C σ hσ (curveToP1 k C)

/-- The Jacobian represents the functor `Pic⁰_{C/k,σ}` on `(Sch/k)`. -/
def jacobianRepresentableBy :
    (picZero C σ hσ (curveToP1 k C) ⋙ forget AddCommGrpCat).RepresentableBy (Jacobian C σ hσ) :=
  picZeroRepresentableBy C σ hσ (curveToP1 k C)

/-- The Jacobian is a group scheme over `k`. -/
instance : GrpObj (Jacobian C σ hσ) := inferInstanceAs (GrpObj (picZeroScheme C σ hσ _))

/-- The Jacobian is commutative. -/
instance : IsCommMonObj (Jacobian C σ hσ) :=
  inferInstanceAs (IsCommMonObj (picZeroScheme C σ hσ _))

/-- The Jacobian is proper over `k`. -/
instance : IsProper (Jacobian C σ hσ).hom :=
  inferInstanceAs (IsProper (picDegScheme C σ hσ (curveToP1 k C) 0).hom)

/-- The Jacobian is smooth over `k`. -/
instance : Smooth (Jacobian C σ hσ).hom :=
  inferInstanceAs (Smooth (picDegScheme C σ hσ (curveToP1 k C) 0).hom)

/-- The Jacobian is smooth of relative dimension `g` over `k`. -/
instance : SmoothOfRelativeDimension (genusNat k C) (Jacobian C σ hσ).hom :=
  inferInstanceAs (SmoothOfRelativeDimension (genusNat k C)
    (picDegScheme C σ hσ (curveToP1 k C) 0).hom)

/-- The Jacobian is geometrically irreducible over `k`. -/
instance : GeometricallyIrreducible (Jacobian C σ hσ).hom :=
  inferInstanceAs (GeometricallyIrreducible (picDegScheme C σ hσ (curveToP1 k C) 0).hom)

/-- The Jacobian is geometrically connected over `k`. -/
instance : GeometricallyConnected (Jacobian C σ hσ).hom := inferInstance

/-- **The Jacobian is an abelian variety of dimension `g`.** -/
instance : IsAbelianVariety (Jacobian C σ hσ) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The Jacobian is connected. -/
instance : ConnectedSpace (Jacobian C σ hσ).left :=
  GeometricallyConnected.connectedSpace_of_subsingleton (Jacobian C σ hσ).hom

end Jacobian

end CurvesJacobian
