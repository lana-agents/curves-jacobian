/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LineBranch
import Pi1.FundamentalGroup.BaseChangeInjective

/-!
# Base change of branches at cusps

For a field extension `Ω / K` and a branch `b` at the cusp `j` of a finite étale
`Y ⟶ Spec R` (`CurvesJacobian.Cusp.CuspBranch`), the base change `Ω ⊗[K] b.A`, `s ↦ 1 ⊗ s`,
is a branch at `j` of the base change `Y_Ω ⟶ Spec (Ω ⊗[K] R)`
(`CurvesJacobian.Cusp.CuspBranch.baseChange`): étaleness over `K[X]` is stable under base change
(the square `K[X] → A`, `Ω[X] → Ω ⊗ A` is a pushout,
`CurvesJacobian.Cusp.etale_mvAeval_baseChange`), the point `ε` extends `Ω`-linearly, and the
morphism to `Y_Ω = Y ×_{Spec R} Spec (Ω ⊗ R)` is the pullback of the two obvious maps.
-/

open CategoryTheory AlgebraicGeometry Polynomial
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K]

section BaseChange

variable {A : Type u} [CommRing A] [Algebra K A] {Ω : Type u} [CommRing Ω] [Algebra K Ω]

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

/-- **Étaleness of `K[X₀] → A`, `X₀ ↦ s`, is stable under base change** to `Ω[X₀] → Ω ⊗ A`. -/
theorem etale_mvAeval_baseChange {s : A}
    (h : (MvPolynomial.aeval (R := K) fun _ : Fin 1 ↦ s).toRingHom.Etale) :
    (MvPolynomial.aeval (R := Ω) fun _ : Fin 1 ↦ (1 ⊗ₜ s : Ω ⊗[K] A)).toRingHom.Etale := by
  letI : Algebra (MvPolynomial (Fin 1) K) A :=
    (MvPolynomial.aeval (R := K) fun _ : Fin 1 ↦ s).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin 1) Ω) (Ω ⊗[K] A) :=
    (MvPolynomial.aeval (R := Ω) fun _ : Fin 1 ↦ (1 ⊗ₜ s : Ω ⊗[K] A)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin 1) K) (Ω ⊗[K] A) :=
    ((algebraMap A (Ω ⊗[K] A)).comp
      (MvPolynomial.aeval (R := K) fun _ : Fin 1 ↦ s).toRingHom).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin 1) K) A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap K A r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower (MvPolynomial (Fin 1) K) A (Ω ⊗[K] A) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (MvPolynomial (Fin 1) K) (MvPolynomial (Fin 1) Ω) (Ω ⊗[K] A) :=
    IsScalarTower.of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun r ↦ by
      change algebraMap A (Ω ⊗[K] A) (MvPolynomial.aeval _ (MvPolynomial.C r)) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap K Ω) (MvPolynomial.C r))
      rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.aeval_C]
      change (1 : Ω) ⊗ₜ algebraMap K A r = algebraMap K Ω r ⊗ₜ (1 : A)
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply'])
      (fun i ↦ by
        change algebraMap A (Ω ⊗[K] A) (MvPolynomial.aeval _ (MvPolynomial.X i)) =
          MvPolynomial.aeval _ (MvPolynomial.map (algebraMap K Ω) (MvPolynomial.X i))
        rw [MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.aeval_X]
        rfl))
  haveI : IsScalarTower K (MvPolynomial (Fin 1) Ω) (Ω ⊗[K] A) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap K (Ω ⊗[K] A) r =
        MvPolynomial.aeval _ (MvPolynomial.C (algebraMap K Ω r))
      rw [MvPolynomial.aeval_C]
      rfl
  haveI : IsScalarTower Ω (MvPolynomial (Fin 1) Ω) (Ω ⊗[K] A) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap Ω (Ω ⊗[K] A) r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower K A (Ω ⊗[K] A) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap Ω (Ω ⊗[K] A) (algebraMap K Ω r) = (1 : Ω) ⊗ₜ algebraMap K A r
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  haveI : Algebra.IsPushout K A Ω (Ω ⊗[K] A) := TensorProduct.isPushout'
  haveI : Algebra.IsPushout (MvPolynomial (Fin 1) K) A (MvPolynomial (Fin 1) Ω) (Ω ⊗[K] A) :=
    (Algebra.IsPushout.comp_iff K (MvPolynomial (Fin 1) K) Ω (S' := MvPolynomial (Fin 1) Ω)
      (T := A) (T' := Ω ⊗[K] A)).1 inferInstance
  exact RingHom.Etale.isStableUnderBaseChange (MvPolynomial (Fin 1) K) A
    (MvPolynomial (Fin 1) Ω) (Ω ⊗[K] A) h

end BaseChange

/-- `CuspRel` is preserved by ring maps. -/
lemma CuspRel.map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {j : Fin 3} {T s : A}
    (h : CuspRel j T s) : CuspRel j (f T) (f s) := by
  fin_cases j
  · exact congrArg f h
  · change f T = 1 + f s
    rw [show T = 1 + s from h, map_add, map_one]
  · change 2 * f T * f s = f s + 2
    have h' := congrArg f (show 2 * T * s = s + 2 from h)
    simpa only [map_mul, map_add, map_ofNat] using h'

section Branch

variable {R : Type u} [CommRing R] [Algebra K R] {T : R}
  {Y : AlgebraicGeometry.FiniteEtale (Spec (.of R))} {j : Fin 3}
  (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- `A[1/s] → (Ω ⊗ A)[1/(1 ⊗ s)]`. -/
def awayBaseChange (b : CuspBranch K T Y.hom j) :
    Localization.Away b.s →ₐ[K] Localization.Away ((1 : Ω) ⊗ₜ[K] b.s) :=
  IsLocalization.Away.liftAlgHom b.s
    (f := (IsScalarTower.toAlgHom K (Ω ⊗[K] b.A) (Localization.Away ((1 : Ω) ⊗ₜ[K] b.s))).comp
      Algebra.TensorProduct.includeRight)
    (by
      have hu : IsUnit (algebraMap (Ω ⊗[K] b.A) (Localization.Away ((1 : Ω) ⊗ₜ[K] b.s))
          ((1 : Ω) ⊗ₜ[K] b.s)) := IsLocalization.Away.algebraMap_isUnit _
      simpa using hu)

lemma awayBaseChange_algebraMap (b : CuspBranch K T Y.hom j) (a : b.A) :
    awayBaseChange Ω b (algebraMap b.A _ a) = algebraMap _ _ ((1 : Ω) ⊗ₜ[K] a) := by
  simp [awayBaseChange]

/-- The base change `Ω ⊗ R → (Ω ⊗ A)[1/(1 ⊗ s)]` of `θ`. -/
def thetaBaseChange (b : CuspBranch K T Y.hom j) :
    Ω ⊗[K] R →ₐ[Ω] Localization.Away ((1 : Ω) ⊗ₜ[K] b.s) :=
  Algebra.TensorProduct.lift (Algebra.ofId Ω _) ((awayBaseChange Ω b).comp b.θ)
    (fun _ _ ↦ Commute.all _ _)

lemma thetaBaseChange_tmul (b : CuspBranch K T Y.hom j) (r : R) :
    thetaBaseChange Ω b ((1 : Ω) ⊗ₜ r) = awayBaseChange Ω b (b.θ r) := by
  simp [thetaBaseChange, Algebra.TensorProduct.lift_tmul]

/-- **Base change of a branch** along a field extension `Ω / K`. -/
def CuspBranch.baseChange (b : CuspBranch K T Y.hom j) :
    CuspBranch Ω ((1 : Ω) ⊗ₜ[K] T)
      ((AlgebraicGeometry.FiniteEtale.pullback
        (AlgebraicGeometry.FiniteEtale.baseChangeSpec K Ω R)).obj Y).hom j where
  A := Ω ⊗[K] b.A
  s := (1 : Ω) ⊗ₜ[K] b.s
  etale := etale_mvAeval_baseChange b.etale
  pt := Algebra.TensorProduct.lift (Algebra.ofId Ω Ω) ((Algebra.ofId K Ω).comp b.pt)
    (fun _ _ ↦ Commute.all _ _)
  pt_s := by simp [Algebra.TensorProduct.lift_tmul, b.pt_s]
  θ := thetaBaseChange Ω b
  rel := by
    rw [thetaBaseChange_tmul, ← awayBaseChange_algebraMap]
    exact CuspRel.map (awayBaseChange Ω b).toRingHom b.rel
  m := Limits.pullback.lift
    (Spec.map (CommRingCat.ofHom (awayBaseChange Ω b).toRingHom) ≫ b.m)
    (Spec.map (CommRingCat.ofHom (thetaBaseChange Ω b).toRingHom)) (by
      refine (Category.assoc _ _ _).trans
        ((congrArg (fun g ↦ Spec.map (CommRingCat.ofHom (awayBaseChange Ω b).toRingHom) ≫ g)
          b.hm).trans ?_)
      exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map (CommRingCat.hom_ext
        (RingHom.ext fun r ↦ (thetaBaseChange_tmul Ω b r).symm))).trans (Spec.map_comp _ _)))
  hm := Limits.pullback.lift_snd _ _ _

end Branch

end CurvesJacobian.Cusp
