/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.UniqueProperNF
import CurvesJacobian.Cusp.FillAutUnique
import CurvesJacobian.Cusp.ArithmeticPadic

/-!
# The uniqueness half of the rel-isom-DGC over number fields and `p`-adic fields (MR7, S2 + S8)

* `CurvesJacobian.LocAn.innerRigidProper_of_innerRigid`: inner rigidity of an affine hyperbolic
  curve in MR8's arithmetic model (`InnerRigid`, at `basePoint ≫ baseChangeSpec` of
  `Spec Γ(U)`) gives it at every geometric point of `U` (`InnerRigidProper`, which despite its
  name is stated for every hyperbolic curve), via `U ≅ Spec Γ(U)` and
  `IsConjInduced.transport_id`;
* **`CurvesJacobian.LocAn.innerRigidProper_numberField_all`**: every hyperbolic curve over a
  number field is inner rigid (affine: `innerRigid`; proper: `innerRigidProper_numberField`);
* **`CurvesJacobian.LocAn.relIsomDGC_unique_numberField`**: `RelIsomDGC.Unique K` for every
  number field `K`, in the whitelist form (`Belyi.Anabelian.RelIsomDGC.Unique`, [AbsTopI]
  Def 4.6 (ii), uniqueness half of [LocAn] Theorem A), unconditionally;
* **`CurvesJacobian.LocAn.innerRigidProper_padic_all`**, **`relIsomDGC_unique_padic`**: the same
  over every finite extension of `ℚ_p` (affine: `innerRigid` with `isSlimGk_padic`; proper:
  `innerRigidProper_padic`, `LocAn/UniqueProperMLF.lean`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian HypCurve CurvesJacobian.Cusp

noncomputable section

namespace CurvesJacobian.LocAn

variable {K : Type u} [Field K] [CharZero K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω]

/-- **Inner rigidity in the arithmetic model gives inner rigidity at every geometric point**
(affine hyperbolic curves). -/
theorem innerRigidProper_of_innerRigid (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (hR : InnerRigid Ω C hc) : InnerRigidProper Ω C := by
  intro ξ₀ h H
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  set i := (isAffineOpen_U C hc).isoSpec
  obtain ⟨δ⟩ : Nonempty (fiber ξ₀.x ≅ fiber (arithGeomPt Ω C hc).x) :=
    nonempty_iso_of_fiberFunctor _ _
  have H₂ := H.transport_id δ
  have H₁ := isConjInduced_arithGeomEquiv Ω C hc
  have H₃ := isConjInduced_arithGeomEquiv_symm Ω C hc
  let F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U) := i.symm ≪≫ h.1 ≪≫ i
  have hF : F.hom ≫ sKU C = sKU C := by
    simp only [F, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [isoSpec_hom_sKU C hc, h.2, isoSpec_inv_toSpec C hc]
  have HF : IsConjInduced F.hom
      (id : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) → _) :=
    (((H₁.comp H₂).comp H₃).congr_hom
      (by simp only [F, Iso.trans_hom, Iso.symm_hom, Category.assoc]; rfl)).congr_fun
      fun σ ↦ by simp
  have e := hR F hF HF
  refine KIso.ext (Iso.ext ?_)
  have := congrArg (fun G : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U) ↦ i.hom ≫ G.hom ≫ i.inv) e
  simpa [F] using this

variable [Algebra.IsAlgebraic K Ω]

omit [CharZero K] in
/-- **Every hyperbolic curve over a number field is inner rigid**: a `K`-automorphism of `U`
inducing the identity of `π₁ᵉᵗ(U, ξ₀)` up to a change of base point is the identity. -/
theorem innerRigidProper_numberField_all [NumberField K] (C : HypCurve K) :
    InnerRigidProper Ω C := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  rcases (C.U : Set C.Xbar)ᶜ.eq_empty_or_nonempty with hC | hc
  · exact innerRigidProper_numberField C hC
  · exact innerRigidProper_of_innerRigid C hc (innerRigid Ω C hc)

omit [CharZero K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] in
/-- **The uniqueness half of the rel-isom-DGC over every number field**, in the whitelist form
`Belyi.Anabelian.RelIsomDGC.Unique K` (affine and proper hyperbolic curves). -/
theorem relIsomDGC_unique_numberField (K : Type u) [Field K] [NumberField K] :
    RelIsomDGC.Unique K := by
  intro Ω _ _ _ C₁ C₂ ξ₁ ξ₂ φ _ f f' H H'
  haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  exact eq_of_isConjInduced_of_innerRigidProper (innerRigidProper_numberField_all C₁)
    φ.toMulEquiv H.isConjInduced H'.isConjInduced

section Padic

variable (p : ℕ) [Fact p.Prime]

omit [CharZero K] in
/-- **Every hyperbolic curve over a finite extension of `ℚ_p` is inner rigid**: a
`K`-automorphism of `U` inducing the identity of `π₁ᵉᵗ(U, ξ₀)` up to a change of base point is the
identity (affine and proper curves). -/
theorem innerRigidProper_padic_all [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (C : HypCurve K) : InnerRigidProper Ω C := by
  haveI := charZero_padic p (K := K)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K Ω := ⟨⟩
  rcases (C.U : Set C.Xbar)ᶜ.eq_empty_or_nonempty with hC | hc
  · exact innerRigidProper_padic p C hC
  · haveI := isSlimGk_padic p (K := K) Ω
    exact innerRigidProper_of_innerRigid C hc (innerRigid Ω C hc)

omit [CharZero K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] in
/-- **The uniqueness half of the rel-isom-DGC over every finite extension of `ℚ_p`**, in the
whitelist form `Belyi.Anabelian.RelIsomDGC.Unique L` (affine and proper hyperbolic curves), for
every finite extension `L` of `ℚ_p`. -/
theorem relIsomDGC_unique_padic : ForallMLF.{u} p fun L _ _ ↦ RelIsomDGC.Unique L := by
  intro L _ _ _ Ω _ _ _ C₁ C₂ ξ₁ ξ₂ φ _ f f' H H'
  haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω)
  haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
  exact eq_of_isConjInduced_of_innerRigidProper (innerRigidProper_padic_all p C₁)
    φ.toMulEquiv H.isConjInduced H'.isConjInduced

end Padic

end CurvesJacobian.LocAn
