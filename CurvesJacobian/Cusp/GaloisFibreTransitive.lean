/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.FieldTheory.AlgebraicClosure
import CurvesJacobian.Cusp.CoverOpen

/-!
# Deck transformations act transitively on the fibres of a Galois cover

Let `X` be a connected scheme and `q : V ⟶ X` finite étale such that `coverObj q` is a Galois
object of the Galois category `FiniteEtale X`. Then the automorphism group of `coverObj q` acts
transitively on the (scheme-theoretic) fibres of `q`:

* `CurvesJacobian.Cusp.exists_aut_comp_eq_of_isGalois₂`: two geometric points `a b` of `V`
  over the same geometric point of `X` differ by an automorphism, `a ≫ σ.hom.left = b`;
* `CurvesJacobian.Cusp.exists_aut_apply_eq_of_isGalois`: for points `z z' : V` with
  `q z = q z'` there is `σ : Aut (coverObj q)` with `σ.hom.left z = z'`.

The second statement follows from the first: choose a point `p` of `V ×_X V` over `(z, z')`
(`Scheme.Pullback.exists_preimage_pullback`) and a geometric point
`Spec Ω ⟶ Spec κ(p) ⟶ V ×_X V` with `Ω` an algebraic closure of `κ(p)`; its two projections
are geometric points of `V` over the same geometric point of `X`, with images `z` and `z'`.
The first statement is the transitivity of `Aut A` on `F.obj A` for a Galois object `A`
(`CategoryTheory.PreGaloisCategory.isPretransitive_of_isGalois`), read through
`fiberObjEquivHom`.
-/

open CategoryTheory Limits PreGaloisCategory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

universe u

namespace CurvesJacobian.Cusp

variable {X V : Scheme.{u}} [ConnectedSpace X] (q : V ⟶ X) [IsFiniteEtale q]

/-- **Transitivity on geometric fibres.** Two geometric points of a Galois cover `q : V ⟶ X`
lying over the same geometric point of `X` differ by an automorphism of the cover. -/
theorem exists_aut_comp_eq_of_isGalois₂ [IsGalois (coverObj q)] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (a b : Spec (.of Ω) ⟶ V) (h : a ≫ q = b ≫ q) :
    ∃ σ : Aut (coverObj q), a ≫ σ.hom.left = b := by
  have ha : a ≫ (coverObj q).hom = a ≫ q := rfl
  have hb : b ≫ (coverObj q).hom = a ≫ q := h.symm
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut (coverObj q))
    ((fiberObjEquivHom (a ≫ q) (coverObj q)).symm (Over.homMk a ha))
    ((fiberObjEquivHom (a ≫ q) (coverObj q)).symm (Over.homMk b hb))
  refine ⟨σ, ?_⟩
  have h1 : (fiber (a ≫ q)).map σ.hom
      ((fiberObjEquivHom (a ≫ q) (coverObj q)).symm (Over.homMk a ha)) =
      (fiberObjEquivHom (a ≫ q) (coverObj q)).symm (Over.homMk b hb) := hσ
  rw [fiberObjEquivHom_symm_naturality] at h1
  have h2 := congrArg CommaMorphism.left
    ((fiberObjEquivHom (a ≫ q) (coverObj q)).symm.injective h1)
  simp only [Over.comp_left, Over.homMk_left] at h2
  exact h2

/-- The geometric point `Spec Ω ⟶ Spec κ(x) ⟶ Y` of a scheme `Y` at `x : Y`, where `Ω` is the
algebraic closure of the residue field `κ(x)`. -/
noncomputable def geomPtResidue₂ {Y : Scheme.{u}} (x : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField x))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField x)
    (AlgebraicClosure (Y.residueField x)))) ≫ Y.fromSpecResidueField x

lemma geomPtResidue₂_apply {Y : Scheme.{u}} (x : Y)
    (s : Spec (.of (AlgebraicClosure (Y.residueField x)))) : geomPtResidue₂ x s = x := by
  rw [geomPtResidue₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- **Deck transformations act transitively on fibres of Galois covers.** For a finite étale
`q : V ⟶ X` over a connected scheme `X` with `coverObj q` Galois and points `z z' : V` with
`q z = q z'`, some automorphism of the cover maps `z` to `z'`. -/
theorem exists_aut_apply_eq_of_isGalois [IsGalois (coverObj q)] (z z' : V) (h : q z = q z') :
    ∃ σ : Aut (coverObj q), σ.hom.left z = z' := by
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback z z' h
  obtain ⟨σ, hσ⟩ := exists_aut_comp_eq_of_isGalois₂ q
    (geomPtResidue₂ p ≫ pullback.fst q q) (geomPtResidue₂ p ≫ pullback.snd q q)
    (by simp only [Category.assoc, pullback.condition])
  refine ⟨σ, ?_⟩
  have h3 := congrArg (fun g ↦ g default) hσ
  simp only [Scheme.Hom.comp_apply, geomPtResidue₂_apply, hp1] at h3
  have h4 : (geomPtResidue₂ p ≫ pullback.snd q q) default = z' := by
    rw [Scheme.Hom.comp_apply, geomPtResidue₂_apply, hp2]
  exact h3.trans h4

end CurvesJacobian.Cusp
