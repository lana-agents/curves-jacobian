/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverGenus
import CurvesJacobian.Cusp.CoverCuspDegree
import Belyi.Curve.BaseChange
import Belyi.Anabelian.BelyiInput
import Pi1.FundamentalGroup.Galois

/-!
# Base change of hyperbolic curves along a field extension

Let `M'/M` be an extension of fields. For a scheme `X` over `M` we write
`X_{M'} = Spec M' ×_{Spec M} X` (`CurvesJacobian.Cusp.bcX`, in the pullback order of belyi's
`Belyi.Anabelian.exists_belyi_open_le_finSub`) with projection `bcπ : X_{M'} ⟶ X`.

* `CurvesJacobian.Cusp.isCurveOver_bcX`, `CurvesJacobian.Cusp.surjective_bcπ`: the base change of
  a curve is a curve, and `bcπ` is surjective.
* `Belyi.Anabelian.HypCurve.bc`: for `M` of characteristic zero and `M'/M` algebraic, the base
  change of a hyperbolic curve is a hyperbolic curve (the genus and the cusp degree do not drop:
  `CurvesJacobian.Cusp.curveGenus_le_bc`, `CurvesJacobian.Cusp.cuspDegree_le_bc`).
* `CurvesJacobian.Cusp.isPullback_specΓ`: for a cartesian square `X' = Spec M' ×_{Spec M} X` and
  an affine open `U ⊆ X` with preimage `V ⊆ X'`, the square of rings
  `Γ(X', V) ← Γ(X, U)`, `M' ← M` is a pushout, i.e.
  `Spec Γ(X', V) = Spec M' ×_{Spec M} Spec Γ(X, U)`;
  hence `Spec Γ(X', V) ⟶ Spec Γ(X, U)` is finite étale for `M'/M` finite separable
  (`CurvesJacobian.Cusp.isFiniteEtale_specΓ`).
* `CurvesJacobian.Cusp.isFiniteEtale_specMap_appLE`: if `g ∣_ U` is finite étale for affine `U`
  with affine preimage `V`, then `Spec Γ(X, V) ⟶ Spec Γ(Y, U)` is finite étale.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### The base-change scheme -/

section BaseChange

variable (M : Type u) [Field M] (M' : Type u) [Field M'] [Algebra M M']

/-- The base change `X_{M'} = Spec M' ×_{Spec M} X` of a scheme `X` over `M`. -/
abbrev bcX (X : Scheme.{u}) [X.Over (Spec (.of M))] : Scheme.{u} :=
  pullback (specAlgebraMap M M') (X ↘ Spec (.of M))

/-- `X_{M'}` is a scheme over `M'` via the first projection. -/
instance (X : Scheme.{u}) [X.Over (Spec (.of M))] : (bcX M M' X).Over (Spec (.of M')) :=
  ⟨pullback.fst _ _⟩

/-- The projection `X_{M'} ⟶ X`. -/
abbrev bcπ (X : Scheme.{u}) [X.Over (Spec (.of M))] : bcX M M' X ⟶ X :=
  pullback.snd _ _

/-- The base-change square `X_{M'} ⟶ X` over `Spec M' ⟶ Spec M` is cartesian. -/
lemma isPullback_bcπ (X : Scheme.{u}) [X.Over (Spec (.of M))] :
    IsPullback (bcπ M M' X) (bcX M M' X ↘ Spec (.of M')) (X ↘ Spec (.of M))
      (specAlgebraMap M M') :=
  (IsPullback.of_hasPullback _ _).flip

/-- The base change of a curve over `M` is a curve over `M'`. -/
instance isCurveOver_bcX (X : Scheme.{u}) [X.Over (Spec (.of M))] [IsCurveOver M X] :
    IsCurveOver M' (bcX M M' X) :=
  IsCurveOver.of_iso (pullbackSymmetry (X ↘ Spec (.of M)) (specAlgebraMap M M'))
    (pullbackSymmetry_hom_comp_fst _ _)

/-- `X_{M'} ⟶ X` is surjective. -/
lemma surjective_bcπ (X : Scheme.{u}) [X.Over (Spec (.of M))] :
    Function.Surjective (bcπ M M' X) := by
  haveI : Surjective (specAlgebraMap M M') := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y⟩ : Nonempty (Spec (.of M')) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩
  haveI : Surjective (bcπ M M' X) :=
    MorphismProperty.pullback_snd (P := @Surjective) _ _ inferInstance
  exact (bcπ M M' X).surjective

/-- The preimage of a nonempty open under `X_{M'} ⟶ X` is nonempty. -/
lemma nonempty_preimage_bcπ (X : Scheme.{u}) [X.Over (Spec (.of M))] {U : X.Opens}
    (hU : (U : Set X).Nonempty) :
    ((bcπ M M' X ⁻¹ᵁ U : (bcX M M' X).Opens) : Set (bcX M M' X)).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, rfl⟩ := surjective_bcπ M M' X x
  exact ⟨y, hx⟩

/-- `X_{M'} ⟶ X` maps the generic point to the generic point. -/
lemma bcπ_genericPoint (X : Scheme.{u}) [X.Over (Spec (.of M))] [IsIntegral X]
    [IsIntegral (bcX M M' X)] :
    bcπ M M' X (genericPoint (bcX M M' X)) = genericPoint X := by
  obtain ⟨y, hy⟩ := surjective_bcπ M M' X (genericPoint X)
  have h1 := (genericPoint_specializes y).map (bcπ M M' X).continuous
  rw [hy] at h1
  exact (h1.antisymm (genericPoint_specializes _)).eq

/-- **The genus does not drop under base change**: `g(X / M) ≤ g(X_{M'} / M')`. -/
lemma curveGenus_le_bc [CharZero M] [Algebra.IsAlgebraic M M'] (X : Scheme.{u})
    [X.Over (Spec (.of M))] [IsCurveOver M X] :
    haveI := IsCurveOver.isIntegral M X
    haveI := IsCurveOver.isIntegral M' (bcX M M' X)
    Anabelian.curveGenus M X ≤ Anabelian.curveGenus M' (bcX M M' X) := by
  haveI := IsCurveOver.isIntegral M X
  haveI := IsCurveOver.isIntegral M' (bcX M M' X)
  exact curveGenus_le_of_genericPoint (bcπ M M' X) pullback.condition.symm
    (bcπ_genericPoint M M' X)

/-- **The cusp degree does not drop under base change**: `r(U) ≤ r(U_{M'})`. -/
lemma cuspDegree_le_bc [CharZero M] (X : Scheme.{u}) [X.Over (Spec (.of M))] [IsCurveOver M X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Anabelian.cuspDegree M X U ≤ Anabelian.cuspDegree M' (bcX M M' X) (bcπ M M' X ⁻¹ᵁ U) :=
  cuspDegree_le_cuspDegree_of_surjective (bcπ M M' X) pullback.condition
    (surjective_bcπ M M' X) U hU

end BaseChange

end CurvesJacobian.Cusp

/-! ### Base change of hyperbolic curves -/

namespace Belyi.Anabelian.HypCurve

open CurvesJacobian.Cusp

variable {M : Type u} [Field M] [CharZero M] (M' : Type u) [Field M'] [Algebra M M']
  [Algebra.IsAlgebraic M M']

/-- The **base change** of a hyperbolic curve `C = (X̄, U)` over `M` to an algebraic extension
`M'` of `M`: `(X̄_{M'}, U_{M'})`. -/
def bc (C : HypCurve M) : HypCurve M' where
  Xbar := bcX M M' C.Xbar
  U := bcπ M M' C.Xbar ⁻¹ᵁ C.U
  nonempty := nonempty_preimage_bcπ M M' C.Xbar C.nonempty
  cusps_finite := by
    haveI : CharZero M' := charZero_of_injective_algebraMap (algebraMap M M').injective
    exact finite_compl_of_isCurveOver (k := M') _ _ (nonempty_preimage_bcπ M M' C.Xbar C.nonempty)
  hyperbolic := by
    haveI := IsCurveOver.isIntegral M C.Xbar
    exact Nat.lt_of_lt_of_le C.hyperbolic (Nat.add_le_add
      (Nat.mul_le_mul_left 2 (curveGenus_le_bc M M' C.Xbar))
      (cuspDegree_le_bc M M' C.Xbar C.U C.nonempty))

/-- The base change of a hyperbolic curve with a cusp has a cusp. -/
lemma bc_cusp (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    ((C.bc M').U : Set (C.bc M').Xbar)ᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, rfl⟩ := surjective_bcπ M M' C.Xbar x
  exact ⟨y, hx⟩

end Belyi.Anabelian.HypCurve

namespace CurvesJacobian.Cusp

/-! ### Affine opens and `Spec Γ` -/

section Affine

/-- For an affine open `U` of a scheme over `R`, `Spec Γ(X, U) ⟶ X ⟶ Spec R` is `Spec` of the
structure map `R → Γ(X, U)`. -/
lemma fromSpec_comp_over (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
    {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ (X ↘ Spec (.of R)) = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (.of R)) (isAffineOpen_top _) hU
    (by simp), IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

/-- `Spec Γ(X, g⁻¹ U) ⟶ Spec Γ(Y, U)` is conjugate to `g ∣_ U` via `IsAffineOpen.isoSpec`. -/
lemma specMap_appLE_isoSpec_inv {X Y : Scheme.{u}} (g : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U)) :
    Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ (g ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.SpecMap_appLE_fromSpec, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]

/-- **Finite étale maps of affine opens.** If `g ∣_ U` is finite étale, `U` is affine and its
preimage `V` is affine, then `Spec Γ(X, V) ⟶ Spec Γ(Y, U)` is finite étale. -/
theorem isFiniteEtale_specMap_appLE {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (hV : V = g ⁻¹ᵁ U) (hU : IsAffineOpen U) (hV' : IsAffineOpen V) [IsFinite (g ∣_ U)]
    [Etale (g ∣_ U)] : IsFiniteEtale (Spec.map (g.appLE U V hV.le)) := by
  subst hV
  haveI : IsFiniteEtale (g ∣_ U) := ⟨⟩
  haveI : IsFiniteEtale hV'.isoSpec.inv := ⟨⟩
  haveI : IsFiniteEtale hU.isoSpec.hom := ⟨⟩
  have e := (Iso.comp_inv_eq _).mp (specMap_appLE_isoSpec_inv g hU hV')
  have : IsFiniteEtale ((hV'.isoSpec.inv ≫ g ∣_ U) ≫ hU.isoSpec.hom) := inferInstance
  rw [← e] at this
  exact this

variable {M : Type u} [Field M] {M' : Type u} [Field M'] [Algebra M M']

/-- `Spec M' ⟶ Spec M` is finite étale for a finite separable extension `M'/M`. -/
lemma isFiniteEtale_specAlgebraMap [FiniteDimensional M M'] [Algebra.IsSeparable M M'] :
    IsFiniteEtale (specAlgebraMap M M') := by
  haveI : Algebra.FormallyEtale M M' := Algebra.FormallyEtale.of_isSeparable M M'
  haveI : Algebra.FinitePresentation M M' :=
    (Algebra.FinitePresentation.of_finiteType (R := M) (A := M')).mp inferInstance
  haveI : Algebra.Etale M M' := ⟨inferInstance, inferInstance⟩
  change IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap M M')))
  rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
  exact ⟨⟩

variable {X X' : Scheme.{u}} [X.Over (Spec (.of M))] [X'.Over (Spec (.of M'))] (f : X' ⟶ X)
  (hsq : IsPullback f (X' ↘ Spec (.of M')) (X ↘ Spec (.of M)) (specAlgebraMap M M'))
include hsq

/-- In a base-change square along `Spec M' ⟶ Spec M`, the morphism `f : X' ⟶ X` is affine. -/
lemma isAffineHom_of_isPullback : IsAffineHom f :=
  MorphismProperty.of_isPullback hsq.flip inferInstance

/-- The preimage of an affine open along a base change `f : X' ⟶ X` is affine. -/
lemma isAffineOpen_of_isPullback {U : X.Opens} {V : X'.Opens} (hV : V = f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) : IsAffineOpen V := by
  haveI := isAffineHom_of_isPullback f hsq
  subst hV
  exact hU.preimage f

/-- **Affine opens along a base-change square.** For `X' = Spec M' ×_{Spec M} X`, an affine open
`U ⊆ X` and `V = f⁻¹ U`, the square `Spec Γ(X', V) ⟶ Spec Γ(X, U)` over `Spec M' ⟶ Spec M` is
cartesian. -/
theorem isPullback_specΓ {U : X.Opens} {V : X'.Opens} (hV : V = f ⁻¹ᵁ U) (hU : IsAffineOpen U) :
    IsPullback (Spec.map (f.appLE U V hV.le))
      (Spec.map (CommRingCat.ofHom (algebraMap M' Γ(X', V))))
      (Spec.map (CommRingCat.ofHom (algebraMap M Γ(X, U)))) (specAlgebraMap M M') := by
  have hV' := isAffineOpen_of_isPullback f hsq hV hU
  subst hV
  have h := (isPullback_morphismRestrict f U).paste_vert hsq
  refine h.of_iso' hV'.isoSpec.symm hU.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (specMap_appLE_isoSpec_inv f hU hV').symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, fromSpec_comp_over]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, fromSpec_comp_over]
  · simp

/-- **Finite étaleness along a finite separable base change.** For `X' = Spec M' ×_{Spec M} X`
with `M'/M` finite separable, an affine open `U ⊆ X` and `V = f⁻¹ U`,
`Spec Γ(X', V) ⟶ Spec Γ(X, U)` is finite étale. -/
theorem isFiniteEtale_specΓ [FiniteDimensional M M'] [Algebra.IsSeparable M M'] {U : X.Opens}
    {V : X'.Opens} (hV : V = f ⁻¹ᵁ U) (hU : IsAffineOpen U) :
    IsFiniteEtale (Spec.map (f.appLE U V hV.le)) :=
  haveI := isFiniteEtale_specAlgebraMap (M := M) (M' := M')
  MorphismProperty.of_isPullback (P := @IsFiniteEtale) (isPullback_specΓ f hsq hV hU).flip
    inferInstance

end Affine

end CurvesJacobian.Cusp

end
