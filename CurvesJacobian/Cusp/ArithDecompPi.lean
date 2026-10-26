/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithDecomp
import CurvesJacobian.Cusp.ConjInducedCusps

/-!
# [AbsTopII] Corollary 3.7 (c) along `fillPiHom`

`exists_map_fillMap_commensurator_cusps` (`ArithDecomp.lean`) describes the images of the cuspidal
decomposition groups under `fillMap : Π_U → Π_{U'}(fillPoint)`. This file moves the statement to
`fillPiHom : Π_U → Π_{U'}` at the base point of `fillCurve` (the map used by the elliptic and
hemi-elliptic chains), via the change of base point `fillTransport`:

* `commensurable_map_injective`, **`map_commensurator_of_injective`**: commensurators commute with
  injective homomorphisms, `f(Comm_H(I)) = Comm_G(f(I)) ∩ f(H)`;
* **`exists_map_fillPiHom_commensurator_cusps`**: up to one conjugation `t ∈ Π_{U'}`, for every
  cuspidal inertia group `I = I_W` of `Π_U`, `fillPiHom (Comm_{Π_U}(I)) = t · D_W(U') · t⁻¹`,
  `D_W(U')` the decomposition group of `W` in `Π_{U'}` ([AbsTopII] Cor. 3.7 (c),
  `Topics in Absolute Anabelian Geometry II.txt` l.4767–4769).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  PreGaloisCategory

open scoped Pointwise

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

section Generic

variable {H G : Type*} [Group H] [Group G]

lemma conjAct_smul_map_of_hom (f : H →* G) (h : H) (I : Subgroup H) :
    ConjAct.toConjAct (f h) • I.map f = (ConjAct.toConjAct h • I).map f := by
  rw [conjAct_smul_eq_map, conjAct_smul_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

lemma commensurable_map_injective (f : H →* G) (hf : Function.Injective f) {I J : Subgroup H} :
    Subgroup.Commensurable (I.map f) (J.map f) ↔ Subgroup.Commensurable I J := by
  rw [Subgroup.Commensurable, Subgroup.Commensurable,
    Subgroup.relIndex_map_map_of_injective _ _ hf, Subgroup.relIndex_map_map_of_injective _ _ hf]

/-- **Commensurators commute with injective homomorphisms**:
`f(Comm_H(I)) = Comm_G(f(I)) ∩ f(H)`. -/
theorem map_commensurator_of_injective (f : H →* G) (hf : Function.Injective f)
    (I : Subgroup H) :
    (Subgroup.Commensurable.commensurator I).map f =
      Subgroup.Commensurable.commensurator (I.map f) ⊓ f.range := by
  have key : ∀ h : H, Subgroup.Commensurable (ConjAct.toConjAct (f h) • I.map f) (I.map f) ↔
      Subgroup.Commensurable (ConjAct.toConjAct h • I) I := fun h ↦ by
    rw [conjAct_smul_map_of_hom, commensurable_map_injective f hf]
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(Subgroup.Commensurable.commensurator_mem_iff _ _).2
      ((key h).2 ((Subgroup.Commensurable.commensurator_mem_iff _ _).1 hh)), h, rfl⟩
  · rintro ⟨hg, h, rfl⟩
    exact ⟨h, (Subgroup.Commensurable.commensurator_mem_iff _ _).2
      ((key h).1 ((Subgroup.Commensurable.commensurator_mem_iff _ _).1 hg)), rfl⟩

/-- Conjugating the image of a subgroup under an isomorphism. -/
lemma map_conj_map_mulEquiv (e : H ≃* G) (t : G) (D : Subgroup H) :
    (D.map e.toMonoidHom).map (MulAut.conj t).toMonoidHom =
      ((D.map (MulAut.conj (e.symm t)).toMonoidHom).map e.toMonoidHom) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

end Generic

section Fill

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens} (h : C.U ≤ U')
  (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
  (hyp : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U')

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `fillTransport ∘ fillPiHom = fillMap`, on subgroups. -/
lemma map_fillPiHom_map_fillTransport (S : Subgroup
    π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    (S.map (fillPiHom Ω C hc h hc' hyp).toMonoidHom).map
        (fillTransport Ω C hc h hc' hyp).toMulEquiv.toMonoidHom =
      S.map (fillMap Ω C hc h).toMonoidHom := by
  rw [Subgroup.map_map]
  exact congrArg (fun f ↦ S.map f)
    (MonoidHom.ext fun σ ↦ fillTransport_fillPiHom Ω C hc h hc' hyp σ)

include hyp in
/-- **[AbsTopII] Corollary 3.7 (c) along `fillPiHom`** (`Topics in Absolute Anabelian Geometry
II.txt` l.4767–4769; `exists_map_fillMap_commensurator_cusps` at the base point of `fillCurve`):
up to one conjugation `t ∈ Π_{U'}` (independent of the cusp), every cuspidal inertia group `I` of
`Π_U` is `I_W` for a place `W` over a cusp of `U`, and the image under `fillPiHom : Π_U → Π_{U'}`
of its commensurator (the cuspidal decomposition group, [AbsTopI] Lemma 4.5 (vi)) is
`t · D_W(U') · t⁻¹`, `D_W(U')` the decomposition group of `W` in `Π_{U'}`. -/
theorem exists_map_fillPiHom_commensurator_cusps :
    ∃ t, ∀ I ∈ arithCusps Ω C hc, ∃ W, IsCuspPlace Ω C hc W ∧ I = arithInertia Ω C hc W ∧
      (Subgroup.Commensurable.commensurator I).map (fillPiHom Ω C hc h hc' hyp).toMonoidHom =
        (arithDecomp Ω (fillCurve C h hyp) hc' W).map (MulAut.conj t).toMonoidHom := by
  obtain ⟨t, ht⟩ := exists_map_fillMap_commensurator_cusps Ω C hc h hc' hyp
    (fillAlpha Ω C hc h hc' hyp)
  set T := fillTransport Ω C hc h hc' hyp with hT
  refine ⟨T.toMulEquiv.symm t, fun I hI ↦ ?_⟩
  obtain ⟨W, hW, hIW, hmap⟩ := ht I hI
  refine ⟨W, hW, hIW, ?_⟩
  have hmap' : (Subgroup.Commensurable.commensurator I).map (fillMap Ω C hc h).toMonoidHom =
      ((arithDecomp Ω (fillCurve C h hyp) hc' W).map
        T.toMulEquiv.toMonoidHom).map (MulAut.conj t).toMonoidHom := hmap
  apply Subgroup.map_injective (f := T.toMulEquiv.toMonoidHom) T.injective
  rw [map_fillPiHom_map_fillTransport, hmap', map_conj_map_mulEquiv]
  rfl

end Fill

end CurvesJacobian.Cusp
