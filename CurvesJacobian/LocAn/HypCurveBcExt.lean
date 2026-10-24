/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HypBaseChange
import CurvesJacobian.Cusp.GenusBaseChange
import CurvesJacobian.Cusp.GenusLocAnEq

/-!
# Base change of hyperbolic curves along an arbitrary extension (MR7 S1, [LocAn] Cor. 15.5)

[LocAn] Cor. 15.5 (the descent `DescentNF` of `LocAn/ExistsAssembly.lean`) base-changes curves over
a number field `K` to a finite extension `L` of `ℚ_p` containing `K`; `L/K` is not algebraic, so
`Belyi.Anabelian.HypCurve.bc` (algebraic extensions, `Cusp/HypBaseChange.lean`) does not apply. In
characteristic `0` the genus is invariant under every base change
(`CurvesJacobian.Cusp.curveGenus_baseChange`, via Čech cohomology), which gives the general case.

## Main results

* `CurvesJacobian.Cusp.curveGenus_bcX_eq`: `g(X_{M'}) = g(X)` for `X_{M'} = Spec M' ×_{Spec M} X`
  (`dim H⁰(Ω¹)`, `char M = 0`, any extension `M'/M`);
* **`Belyi.Anabelian.HypCurve.bcExt`**: the base change of a hyperbolic curve to any extension
  field; `bcExt_cusp`, `bcExt_proper`: cusps are preserved, proper curves stay proper;
* `Belyi.Anabelian.HypCurve.bcExtOpenIso`: `U_{M'} ≅ Spec M' ×_{Spec M} U`;
  **`Belyi.Anabelian.HypCurve.KIso.bcExt`**: base change of a `k`-isomorphism `U₁ ≅ U₂`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable (M : Type u) [Field M] [CharZero M] (M' : Type u) [Field M'] [Algebra M M']

/-- **The genus is invariant under any base change** in characteristic `0`:
`g(X_{M'} / M') = g(X / M)` for `X_{M'} = Spec M' ×_{Spec M} X`. -/
theorem curveGenus_bcX_eq (X : Scheme.{u}) [X.Over (Spec (.of M))] [IsCurveOver M X] :
    haveI := IsCurveOver.isIntegral M X
    haveI := IsCurveOver.isIntegral M' (bcX M M' X)
    Anabelian.curveGenus M' (bcX M M' X) = Anabelian.curveGenus M X := by
  haveI : CharZero M' := charZero_of_injective_algebraMap (algebraMap M M').injective
  haveI := IsCurveOver.isIntegral M X
  haveI := IsCurveOver.isIntegral M' (bcX M M' X)
  haveI := IsCurveOver.isIntegral M' (baseChange M M' X)
  let e := pullbackSymmetry (X ↘ Spec (.of M)) (specAlgebraMap M M')
  have hid : Spec.map (CommRingCat.ofHom (algebraMap M' M')) = 𝟙 _ := by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  have h1 : Anabelian.curveGenus M' (bcX M M' X) =
      Anabelian.curveGenus M' (baseChange M M' X) := by
    apply le_antisymm
    · refine curveGenus_le_of_genericPoint e.hom ?_ (genericPoint_eq_of_isOpenImmersion _)
      rw [hid, Category.comp_id]
      exact pullbackSymmetry_hom_comp_fst _ _
    · refine curveGenus_le_of_genericPoint e.inv ?_ (genericPoint_eq_of_isOpenImmersion _)
      rw [hid, Category.comp_id]
      exact pullbackSymmetry_inv_comp_snd _ _
  have h2 := curveGenus_baseChange M M' X
  have h3 := locAn_curveGenus_eq M X
  have h4 := locAn_curveGenus_eq M' (baseChange M M' X)
  rw [h1]
  omega

end CurvesJacobian.Cusp

namespace Belyi.Anabelian.HypCurve

open CurvesJacobian.Cusp

variable {M : Type u} [Field M] [CharZero M] (M' : Type u) [Field M'] [Algebra M M']

/-- The **base change** of a hyperbolic curve `C = (X̄, U)` over a field `M` of characteristic `0`
to an arbitrary extension field `M'` (e.g. a number field into a finite extension of `ℚ_p`):
`(X̄_{M'}, U_{M'})`. The genus is unchanged (`curveGenus_bcX_eq`) and the cusp degree does not drop
(`cuspDegree_le_bc`). For algebraic `M'/M` this is `HypCurve.bc`. -/
def bcExt (C : HypCurve M) : HypCurve M' where
  Xbar := bcX M M' C.Xbar
  U := bcπ M M' C.Xbar ⁻¹ᵁ C.U
  nonempty := nonempty_preimage_bcπ M M' C.Xbar C.nonempty
  cusps_finite := by
    haveI : CharZero M' := charZero_of_injective_algebraMap (algebraMap M M').injective
    exact finite_compl_of_isCurveOver (k := M') _ _ (nonempty_preimage_bcπ M M' C.Xbar C.nonempty)
  hyperbolic := by
    haveI := IsCurveOver.isIntegral M C.Xbar
    have h := curveGenus_bcX_eq M M' C.Xbar
    refine Nat.lt_of_lt_of_le C.hyperbolic (Nat.add_le_add ?_
      (cuspDegree_le_bc M M' C.Xbar C.U C.nonempty))
    rw [h]

/-- The base change of a hyperbolic curve with a cusp has a cusp. -/
lemma bcExt_cusp (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    ((C.bcExt M').U : Set (C.bcExt M').Xbar)ᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, rfl⟩ := surjective_bcπ M M' C.Xbar x
  exact ⟨y, hx⟩

/-- The base change of a proper hyperbolic curve is proper (no cusps). -/
lemma bcExt_proper (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ = ∅) :
    ((C.bcExt M').U : Set (C.bcExt M').Xbar)ᶜ = ∅ := by
  rw [Set.compl_empty_iff] at hc ⊢
  refine Set.eq_univ_of_forall fun y ↦ ?_
  change bcπ M M' C.Xbar y ∈ (C.U : Set C.Xbar)
  rw [hc]
  trivial

end Belyi.Anabelian.HypCurve

namespace Belyi.Anabelian.HypCurve

open CurvesJacobian.Cusp

variable {M : Type u} [Field M] [CharZero M] (M' : Type u) [Field M'] [Algebra M M']

/-- `U_{M'} ≅ Spec M' ×_{Spec M} U` for the open `U_{M'} = bcπ⁻¹ U` of `X̄_{M'}`. -/
def bcExtOpenIso (C : HypCurve M) :
    (C.bcExt M').U.toScheme ≅ pullback (specAlgebraMap M M') C.toSpec :=
  (pullbackRestrictIsoRestrict (bcπ M M' C.Xbar) C.U).symm ≪≫
    pullbackLeftPullbackSndIso (specAlgebraMap M M') (C.Xbar ↘ Spec (.of M)) C.U.ι

lemma bcExtOpenIso_hom_fst (C : HypCurve M) :
    (bcExtOpenIso M' C).hom ≫ pullback.fst _ _ = (C.bcExt M').toSpec := by
  simp only [bcExt, toSpec, bcExtOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_hom_fst, comp_over]
  erw [pullbackRestrictIsoRestrict_inv_fst_assoc]
  rfl

/-- Spec M' ×_{Spec M} (−) applied to a `k`-isomorphism of the opens. -/
def pullbackIsoOfKIso {C₁ C₂ : HypCurve M} (f : KIso C₁ C₂) :
    pullback (specAlgebraMap M M') C₁.toSpec ≅ pullback (specAlgebraMap M M') C₂.toSpec where
  hom := pullback.map _ _ _ _ (𝟙 _) f.1.hom (𝟙 _) (by simp) (by simp [f.2])
  inv := pullback.map _ _ _ _ (𝟙 _) f.1.inv (𝟙 _) (by simp) (by
    simp only [Category.comp_id]
    exact (Iso.eq_inv_comp _).2 f.2)
  hom_inv_id := by
    ext
    · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
    · erw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc,
        f.1.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    ext
    · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
    · erw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc,
        f.1.inv_hom_id, Category.comp_id]

/-- **Base change of a `k`-isomorphism** `U₁ ≅ U₂` to `U₁,_{M'} ≅ U₂,_{M'}`. -/
def KIso.bcExt {C₁ C₂ : HypCurve M} (f : KIso C₁ C₂) : KIso (C₁.bcExt M') (C₂.bcExt M') :=
  ⟨bcExtOpenIso M' C₁ ≪≫ pullbackIsoOfKIso M' f ≪≫ (bcExtOpenIso M' C₂).symm, by
    rw [← bcExtOpenIso_hom_fst, ← bcExtOpenIso_hom_fst]
    simp only [pullbackIsoOfKIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    erw [pullback.lift_fst, Category.comp_id]⟩

end Belyi.Anabelian.HypCurve
