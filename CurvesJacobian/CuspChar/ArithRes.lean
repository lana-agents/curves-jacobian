/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Arith
import CurvesJacobian.Cusp.ArithAut
import CurvesJacobian.Cusp.FieldExtIso

/-!
# The arithmetic Galois action over `G_K`, and the cyclotomic character

Let `𝔽 = K(X̄_Ω)^alg` and `L₀ = K(X̄) ⊆ 𝔽` (`CurvesJacobian.Cusp.arithFF`). Every
`τ ∈ Gal(𝔽/L₀)` maps `Ω ⊆ 𝔽` onto `Ω`; its restriction is
`CurvesJacobian.Cusp.resOmega Ω C hc τ ∈ Gal(Ω/K)` (`Cusp/ArithAut.lean`).

* `CurvesJacobian.CuspChar.exists_projGk_arithAction_conj`: there is `t ∈ G_K = π₁ᵉᵗ(Spec K)`
  with `projGk (arithAction τ) = t · resOmega τ · t⁻¹` for all `τ` (`Gal(Ω/K) ≅ G_K` via
  `mulEquivAutFiber`);
* `CurvesJacobian.CuspChar.exists_gkEquivGal_projGk_arithAction`: the same in `Gal(Ω/K)`;
* **`CurvesJacobian.CuspChar.arithCycChar_arithAction`**: the cyclotomic character of `Π_U` on
  `arithAction τ` is the cyclotomic character of `resOmega τ`.

## Proof

Naturality of the Galois action along `U ⟶ Spec K` (`fundamentalGroupMap_galoisAction`) and of
changes of base point (`fundamentalGroupMap_autContinuousMulEquivOfIso`) write
`projGk ∘ arithAction` as the Galois action of `Gal(𝔽/L₀)` through `Spec L₀ ⟶ Spec K` at the
geometric point `Spec 𝔽 ⟶ Spec Ω ⟶ Spec K`, moved to `Spec Ω ⟶ Spec K` by an isomorphism of
fibre functors. The extension of the field `Ω ⊆ 𝔽` (`galoisAction_fieldExt`) identifies this
Galois action with that of `Gal(Ω/K)` on `resOmega τ`; two isomorphisms of fibre functors differ
by an inner automorphism.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory CurvesJacobian.Cusp

universe u

noncomputable section

namespace CurvesJacobian.CuspChar

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

set_option linter.unusedSectionVars false

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [Algebra.IsAlgebraic K Ω] in
/-- `Spec L₀ ⟶ Spec Γ(U) ⟶ Spec K` at `Spec 𝔽` is `Spec 𝔽 ⟶ Spec Ω ⟶ Spec K`. -/
lemma specMap_arithGenPt_strK :
    Spec.map (CommRingCat.ofHom (algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C)))) ≫
        arithGenPt Ω C hc ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      specHom (algebraMap Ω (FFClosure (geomCurve Ω C))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [arithGenPt, specHom, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  exact secEmb_algebraMap Ω C (isAffineOpen_U C hc) c

omit [Algebra.IsAlgebraic K Ω] in
/-- The generic geometric point of `Spec Γ(U)`, mapped to `Spec K`. -/
lemma genPt_strK :
    ((specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫ genOpen Ω C C.U) ≫
        geomToSpec Ω C hc) ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))) =
      specHom (algebraMap Ω (FFClosure (geomCurve Ω C))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← specMap_algebraMap_arithGenPt, Category.assoc]
  exact specMap_arithGenPt_strK Ω C hc

lemma mulEquivAutFiber_eq_galoisAction (g : Ω ≃ₐ[K] Ω) :
    mulEquivAutFiber K Ω g = galoisAction K (𝟙 _) (Category.comp_id _) g := by
  rw [galoisAction, MonoidHom.comp_apply, fundamentalGroupMap_id]
  rfl

/-- **`Π_U ↠ G_K` on the arithmetic Galois action is the restriction to `Ω`, up to an inner
automorphism of `G_K`.** -/
theorem exists_projGk_arithAction_conj :
    ∃ t : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))), ∀ τ,
      projGk Ω C hc (arithAction Ω C hc τ) =
        t * mulEquivAutFiber K Ω (resOmega Ω C hc τ) * t⁻¹ := by
  haveI : ConnectedSpace (Spec (.of K)) := inferInstance
  let ι := algebraMap Ω (FFClosure (geomCurve Ω C))
  let β := fiberIsoMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
    (genPt_strK Ω C hc) (basePoint_spec₂ Ω C hc) (arithFiberIso Ω C hc)
  refine ⟨fieldExtIso ι (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≪≫ β, fun τ ↦ ?_⟩
  have h2 := galoisAction_fieldExt ι (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) K
    (arithFF Ω C hc) (𝟙 _)
    (arithGenPt Ω C hc ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
    (Category.comp_id _) (specMap_arithGenPt_strK Ω C hc) (resOmega Ω C hc τ) τ
    (fun z ↦ algebraMap_resOmega Ω C hc τ z)
  change fundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U))))
      (basePoint_spec₂ Ω C hc) (autContinuousMulEquivOfIso (arithFiberIso Ω C hc)
        (galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc)
          (specMap_algebraMap_arithGenPt Ω C hc) τ)) = _
  rw [fundamentalGroupMap_autContinuousMulEquivOfIso _ (genPt_strK Ω C hc)
      (basePoint_spec₂ Ω C hc),
    fundamentalGroupMap_galoisAction (arithFF Ω C hc) (arithGenPt Ω C hc) _
      (specMap_algebraMap_arithGenPt Ω C hc) (genPt_strK Ω C hc)
      (specMap_arithGenPt_strK Ω C hc) τ,
    ← h2, ← mulEquivAutFiber_eq_galoisAction]
  have key : ∀ α s : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))),
      Iso.conjAut α s = α * s * α⁻¹ := fun α s ↦ by
    rw [Aut.Aut_mul_def, Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.conjAut_apply]
  rw [← key, Iso.trans_conjAut]
  rfl

lemma gkEquivGal_mulEquivAutFiber (g : Ω ≃ₐ[K] Ω) :
    gkEquivGal Ω (mulEquivAutFiber K Ω g) = g :=
  (mulEquivAutFiber K Ω).symm_apply_apply g

/-- **`Π_U ↠ G_K ≅ Gal(Ω/K)` on the arithmetic Galois action is the restriction to `Ω`, up to
an inner automorphism.** -/
theorem exists_gkEquivGal_projGk_arithAction :
    ∃ c : Ω ≃ₐ[K] Ω, ∀ τ, gkEquivGal Ω (projGk Ω C hc (arithAction Ω C hc τ)) =
      c * resOmega Ω C hc τ * c⁻¹ := by
  obtain ⟨t, ht⟩ := exists_projGk_arithAction_conj Ω C hc
  refine ⟨gkEquivGal Ω t, fun τ ↦ ?_⟩
  rw [ht, map_mul, map_mul, map_inv, gkEquivGal_mulEquivAutFiber]

/-- **The cyclotomic character of `Π_U` on the arithmetic Galois action** is the cyclotomic
character of the restriction to `Ω`. -/
theorem arithCycChar_arithAction (l k : ℕ) [NeZero l]
    (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)) :
    arithCycChar Ω C hc l k (arithAction Ω C hc τ) = cycChar K Ω l k (resOmega Ω C hc τ) := by
  obtain ⟨c, hc'⟩ := exists_gkEquivGal_projGk_arithAction Ω C hc
  change cycChar K Ω l k (gkEquivGal Ω (projGk Ω C hc (arithAction Ω C hc τ))) = _
  rw [hc', map_mul, map_mul, map_inv, mul_comm (cycChar K Ω l k c), mul_inv_cancel_right]

end CurvesJacobian.CuspChar
