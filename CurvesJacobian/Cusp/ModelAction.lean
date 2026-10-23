/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.GeomModel

/-!
# The semilinear action of `N_A(ι(Π_Y))` on a geometric model as a group homomorphism

For a geometric model `D` of a chain object `A` (`CurvesJacobian.Cusp.GeomModel`) and the
rel-isom-DGC over its field of definition `M`, the semilinear automorphisms `F_g` of
`Spec Γ(U_Y)` (`GeomModel.exists_semilinearAut`, unique by `GeomModel.eq_of_semilinearAut`)
assemble into a group homomorphism
`GeomModel.semilinearAction : N_A(ι(Π_Y)) →* Aut (Spec Γ(U_Y))` (`F_{gh} = F_g ∘ F_h`), trivial on
`ι(Π_Y)` (`GeomModel.semilinearAction_ι`). This is the action of the finite group
`N_A(ι(Π_Y)) / ι(Π_Y)` on the model ([AbsTopI] Thm 4.7 (i), proof).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp.GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A) (hDGC : RelIsomDGC.Exists D.M)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The restriction `α_g` of `τ_g` to `M` (`GeomModel.exists_resAut`). -/
def resAut (g : D.Nrm) : D.M ≃ₐ[K] D.M := (D.exists_resAut g).choose

lemma resAut_spec (g : D.Nrm) (x : D.M) :
    algebraMap D.M Ω (D.resAut g x) = D.tau g (algebraMap D.M Ω x) :=
  (D.exists_resAut g).choose_spec x

lemma tau_mul (g h : D.Nrm) : D.tau (g * h) = D.tau h * D.tau g := by
  apply (mulEquivAutFiber K Ω).injective
  rw [map_mul, mulEquivAutFiber_tau, mulEquivAutFiber_tau, mulEquivAutFiber_tau,
    Subgroup.coe_mul, map_mul]
  group

/-- `α_{gh} = α_h ∘ α_g`. -/
lemma resAut_mul (g h : D.Nrm) : D.resAut (g * h) = (D.resAut g).trans (D.resAut h) :=
  AlgEquiv.ext fun x ↦ (algebraMap D.M Ω).injective (by
    rw [resAut_spec, tau_mul, AlgEquiv.trans_apply, resAut_spec, resAut_spec]
    rfl)

include hDGC in
lemma exists_semilinearAut_resAut (g : D.Nrm) :
    ∃ F : Spec Γ(D.Y.Xbar, D.Y.U) ≅ Spec Γ(D.Y.Xbar, D.Y.U),
      F.hom ≫ sKU D.Y = sKU D.Y ≫ specRingEquiv (D.resAut g).toRingEquiv ∧
        IsConjInduced F.hom (D.conjPi g) := by
  obtain ⟨α, hα, F, hF, H⟩ := D.exists_semilinearAut hDGC g
  obtain rfl : α = D.resAut g := D.resAut_unique g hα (D.resAut_spec g)
  exact ⟨F, hF, H⟩

/-- **The semilinear automorphism `F_g`** of `Spec Γ(U_Y)` (a choice; unique). -/
def semilinearAutOf (g : D.Nrm) : Spec Γ(D.Y.Xbar, D.Y.U) ≅ Spec Γ(D.Y.Xbar, D.Y.U) :=
  (D.exists_semilinearAut_resAut hDGC g).choose

lemma semilinearAutOf_sKU (g : D.Nrm) :
    (D.semilinearAutOf hDGC g).hom ≫ sKU D.Y =
      sKU D.Y ≫ specRingEquiv (D.resAut g).toRingEquiv :=
  (D.exists_semilinearAut_resAut hDGC g).choose_spec.1

lemma isConjInduced_semilinearAutOf (g : D.Nrm) :
    IsConjInduced (D.semilinearAutOf hDGC g).hom (D.conjPi g) :=
  (D.exists_semilinearAut_resAut hDGC g).choose_spec.2

omit [NumberField K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma specRingEquiv_trans {L : Type u} [Field L] (α β : L ≃+* L) :
    specRingEquiv (α.trans β) = specRingEquiv β ≫ specRingEquiv α := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- **`F_{gh} = F_h ≫ F_g`.** -/
theorem semilinearAutOf_mul (g h : D.Nrm) :
    D.semilinearAutOf hDGC (g * h) = D.semilinearAutOf hDGC h ≪≫ D.semilinearAutOf hDGC g := by
  refine D.eq_of_semilinearAut (g * h) (D.resAut_spec (g * h))
    (D.semilinearAutOf_sKU hDGC (g * h)) ?_ (D.isConjInduced_semilinearAutOf hDGC (g * h)) ?_
  · rw [Iso.trans_hom, Category.assoc, semilinearAutOf_sKU, reassoc_of% semilinearAutOf_sKU,
      resAut_mul]
    exact congrArg (sKU D.Y ≫ ·) (specRingEquiv_trans _ _).symm
  · refine ((D.isConjInduced_semilinearAutOf hDGC h).comp
      (D.isConjInduced_semilinearAutOf hDGC g)).congr_fun fun σ ↦ ?_
    exact D.conjPi_mul g h σ

/-- **The semilinear action** `N_A(ι(Π_Y)) →* Aut (Spec Γ(U_Y))`, `g ↦ F_g`. -/
def semilinearAction : D.Nrm →* Aut (Spec Γ(D.Y.Xbar, D.Y.U)) :=
  MonoidHom.mk' (D.semilinearAutOf hDGC) fun g h ↦ by
    rw [semilinearAutOf_mul, Aut.Aut_mul_def]

lemma semilinearAction_apply (g : D.Nrm) :
    D.semilinearAction hDGC g = D.semilinearAutOf hDGC g := rfl

/-- **The action is trivial on `ι(Π_Y)`.** -/
theorem semilinearAction_ι (σ : D.Pi) : D.semilinearAction hDGC (D.ιN σ) = 1 :=
  (D.semilinearAut_ι σ (D.resAut_spec _) (D.semilinearAutOf_sKU hDGC _)
    (D.isConjInduced_semilinearAutOf hDGC _)).2

/-- `ι : Π_Y →* N_A(ι(Π_Y))`. -/
def ιNHom : D.Pi →* D.Nrm where
  toFun := D.ιN
  map_one' := Subtype.ext (map_one D.ι)
  map_mul' a b := Subtype.ext (map_mul D.ι a b)

/-- `ι(Π_Y)` lies in the kernel of the semilinear action. -/
theorem range_ιNHom_le_ker : D.ιNHom.range ≤ (D.semilinearAction hDGC).ker := by
  rintro _ ⟨σ, rfl⟩
  exact D.semilinearAction_ι hDGC σ

end CurvesJacobian.Cusp.GeomModel
