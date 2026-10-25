/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithAut
import CurvesJacobian.Cusp.ArithKernel
import CurvesJacobian.LocAn.InnerRigidGalois
import CurvesJacobian.Cusp.DGCArith

/-!
# Inner rigidity of affine hyperbolic curves (MR7, step S2)

**`CurvesJacobian.LocAn.innerRigid`**: for a hyperbolic curve `C = (X̄, U)` with a cusp over a
field `K` of characteristic zero whose absolute Galois group is slim (`IsSlimGk K Ω`: number
fields, finite extensions of `ℚ_p` by `CurvesJacobian.Cusp.isSlimGk_padic`), every
`K`-automorphism `F` of `U = Spec Γ(U)` inducing an inner automorphism of `Π_U = π₁ᵉᵗ(U)` is the
identity. Consequently (`eq_of_isConjInduced`) two `K`-isomorphisms
`Spec Γ(U₁) ≅ Spec Γ(U₂)` inducing the same isomorphism `Π_{U₁} ≃ Π_{U₂}` up to a change of base
point are equal: **the uniqueness half of the rel-isom-DGC holds unconditionally** in MR8's
arithmetic model (`[AbsTopI]` Definition 4.6 (ii), whitelist entry for [LocAn] Theorem A).

## Proof

Let `F^* = α` on `Γ(U)`, `L₀ = K(X̄) ⊆ M = K(X̄_Ω)^alg`, `G = Gal(M / L₀)`, `A : G ↠ Π_U` the
arithmetic Galois action.

1. `α` lifts to `s : M ≃ M` fixing `Ω` (`exists_lift_algEquiv`); element-wise functoriality
   (`exists_coverPiHom_arithAction`) and the inner-ness of `π₁ᵉᵗ(F)` give `u ∈ Π_U` with
   `A(s⁻¹ g s) = u⁻¹ A(g) u`. With `A(ρ) = u⁻¹`, `σ = s ∘ ρ` satisfies `A(σ⁻¹ g σ) = A(g)` for all
   `g ∈ G`.
2. `ρ` fixes `Ω`: `σ⁻¹ g σ g⁻¹ ∈ ker A` fixes `Ω` (`arithKernel_fixes_Omega`), so the restriction
   of `ρ` to `Ω` commutes with `Gal(Ω/K)` (`resOmega_surjective`), whose centre is trivial
   (`center_galoisGroup_eq_bot`: `Gal(Ω/K) ≅ G_K` is slim).
3. `σ` preserves `L = K(X̄_Ω)` and the sections `Ω ⊗ Γ(U)`, and conjugation by `σ` does not
   change the action of `H = Gal(M/L)` on `π₁ᵉᵗ(U_Ω)` (`geomToPi` is injective). By
   `eq_of_chartHom_conj` (`LocAn/InnerRigidGalois.lean`), `σ` is the identity on `L`; hence `α`
   is the identity on `Γ(U)` and `F = id`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
open Pi1.Orbifold AffOrbicurve CurvesJacobian.Cusp PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.LocAn

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- **Inner rigidity** of an affine hyperbolic curve `C` over `K`: every `K`-automorphism of
`Spec Γ(U)` that induces the identity of `Π_U` up to a change of base point (equivalently, an
inner automorphism of `Π_U`, `isConjInduced_iff_exists_conj`) is the identity. -/
def InnerRigid (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) : Prop :=
  ∀ F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U), F.hom ≫ sKU C = sKU C →
    IsConjInduced F.hom
      (id : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) → _) →
    F = Iso.refl _

/-- The ring automorphism of `Γ(U)` of a `K`-automorphism of `Spec Γ(U)`. -/
def secAlgEquiv (C : HypCurve K) (F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U))
    (hF : F.hom ≫ sKU C = sKU C) : Γ(C.Xbar, C.U) ≃ₐ[K] Γ(C.Xbar, C.U) :=
  haveI : IsFiniteEtale F.hom := {}
  haveI : IsFiniteEtale F.inv := {}
  { RingEquiv.ofRingHom (coverRing C C F.hom) (coverRing C C F.inv)
      (by
        have : CommRingCat.ofHom ((coverRing C C F.hom).comp (coverRing C C F.inv)) = 𝟙 _ := by
          apply Spec.map_injective
          rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_coverRing, specMap_coverRing,
            F.hom_inv_id, Spec.map_id]
          rfl
        exact congrArg CommRingCat.Hom.hom this)
      (by
        have : CommRingCat.ofHom ((coverRing C C F.inv).comp (coverRing C C F.hom)) = 𝟙 _ := by
          apply Spec.map_injective
          rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_coverRing, specMap_coverRing,
            F.inv_hom_id, Spec.map_id]
          rfl
        exact congrArg CommRingCat.Hom.hom this) with
    commutes' := fun c ↦ by
      have : CommRingCat.ofHom ((coverRing C C F.hom).comp (algebraMap K Γ(C.Xbar, C.U))) =
          CommRingCat.ofHom (algebraMap K Γ(C.Xbar, C.U)) := by
        apply Spec.map_injective
        rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_coverRing]
        exact hF
      exact congrArg (fun f ↦ CommRingCat.Hom.hom f c) this }

lemma secAlgEquiv_apply (C : HypCurve K) (F : Spec Γ(C.Xbar, C.U) ≅ Spec Γ(C.Xbar, C.U))
    (hF : F.hom ≫ sKU C = sKU C) (a : Γ(C.Xbar, C.U)) :
    secAlgEquiv C F hF a = coverRing C C F.hom a := rfl

variable (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

omit [Algebra.IsAlgebraic K Ω] in
/-- A ring automorphism of `M` fixing `Ω` and mapping the sections of `U` into `L` maps `L` into
`L`. -/
lemma mem_L_of_forall (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C))
    (hΩ : ∀ c : Ω, τ (algebraMap Ω _ c) = algebraMap Ω _ c)
    (hA : ∀ a, τ (secEmb Ω C (isAffineOpen_U C hc) a) ∈ (geomData Ω C).L) {x}
    (hx : x ∈ (geomData Ω C).L) : τ x ∈ (geomData Ω C).L := by
  let S : Subfield (FFClosure (geomCurve Ω C)) :=
    (geomData Ω C).L.toSubfield.comap (τ : FFClosure (geomCurve Ω C) →+* _)
  obtain ⟨z, hz⟩ := (curveEquivL Ω (transcendental_geomCoord Ω C)).surjective ⟨x, hx⟩
  have hxz : x = algebraMap (geomCurve Ω C).functionField (FFClosure (geomCurve Ω C)) z := by
    rw [← curveEquivL_apply Ω (transcendental_geomCoord Ω C), hz]
  rw [hxz]
  exact algebraMap_mem_of_le Ω C hc S (fun c ↦ by
      change τ _ ∈ (geomData Ω C).L
      rw [hΩ]
      exact (geomData Ω C).L.algebraMap_mem
        ⟨algebraMap Ω _ c, IntermediateField.algebraMap_mem _ c⟩) hA z

omit [CharZero Ω] in
/-- **`Gal(Ω/K)` has trivial centre** if `G_K = π₁ᵉᵗ(Spec K) ≅ Gal(Ω/K)` is slim. -/
lemma center_galoisGroup_eq_bot [IsSlimGk K Ω] : Subgroup.center (Ω ≃ₐ[K] Ω) = ⊥ := by
  haveI : IsGalois K Ω := ⟨⟩
  let e : (Ω ≃ₐ[K] Ω) ≃* π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    mulEquivAutFiber K Ω
  refine eq_bot_iff.2 fun z hz ↦ ?_
  have hez : e z ∈ Subgroup.center _ := Subgroup.mem_center_iff.2 fun y ↦ by
    obtain ⟨g, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
  rw [(IsSlimGk.isSlim (K := K) (Ω := Ω)).center_eq_bot, Subgroup.mem_bot] at hez
  exact Subgroup.mem_bot.2 (e.injective (hez.trans (map_one e).symm))

/-- **Inner rigidity**: a `K`-automorphism of `Spec Γ(U)` inducing an inner automorphism of `Π_U`
is the identity (`C` hyperbolic with a cusp over a field of characteristic zero with slim
`G_K`). -/
theorem innerRigid [IsSlimGk K Ω] : InnerRigid Ω C hc := by
  intro F hF H
  haveI : IsFiniteEtale F.hom := {}
  set α := secAlgEquiv C F hF with hαdef
  have hU := isAffineOpen_U C hc
  -- (1) the lift `s` of `α`
  obtain ⟨s, hsT, hsΩ, hsA⟩ := exists_lift_algEquiv Ω C hc α
  have hs : ∀ c : arithFF Ω C hc, s (algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C)) c) =
      algebraMap (arithFF Ω C hc) (FFClosure (geomCurve Ω C))
        (coverFF Ω C hc C hc F.hom c) := by
    intro c
    obtain ⟨a, b, rfl⟩ := exists_eq_div_secToArithFF Ω C hc c
    rw [map_div₀ (algebraMap _ _), map_div₀ s, map_div₀ (coverFF Ω C hc C hc F.hom),
      coverFF_secToArithFF, coverFF_secToArithFF, map_div₀ (algebraMap _ _)]
    exact congrArg₂ (· / ·) (hsA a) (hsA b)
  obtain ⟨t₀, ht₀⟩ := exists_coverPiHom_arithAction Ω C hc C hc F.hom s hs
  obtain ⟨t, ht⟩ := (isConjInduced_iff_exists_conj F.hom (coverFib Ω C hc C hc F.hom) _).1 H
  obtain ⟨ρ, hρ⟩ := arithAction_surjective Ω C hc (t * t₀)⁻¹
  -- conjugation by `σ = s ∘ ρ` does not change the arithmetic action
  have hA : ∀ g, arithAction Ω C hc (ρ⁻¹ * arithConj Ω C hc C hc F.hom s hs g * ρ) =
      arithAction Ω C hc g := by
    intro g
    rw [map_mul, map_mul, map_inv, hρ, inv_inv]
    have h1 := ht (arithAction Ω C hc g)
    rw [← coverPiHom_apply, ht₀ g] at h1
    rw [show arithAction Ω C hc g = _ from h1]
    group
  -- (2) `ρ` fixes `Ω`
  have hρΩ : resOmega Ω C hc ρ = 1 := by
    have hcen : ∀ g, resOmega Ω C hc ρ * resOmega Ω C hc g =
        resOmega Ω C hc g * resOmega Ω C hc ρ := by
      intro g
      have hker : (ρ⁻¹ * arithConj Ω C hc C hc F.hom s hs g * ρ) * g⁻¹ ∈ arithKernel Ω C hc := by
        rw [arithKernel, MonoidHom.mem_ker, map_mul, hA, map_inv, mul_inv_cancel]
      have hres : resOmega Ω C hc ((ρ⁻¹ * arithConj Ω C hc C hc F.hom s hs g * ρ) * g⁻¹) = 1 :=
        AlgEquiv.ext fun c ↦ (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
          rw [algebraMap_resOmega, arithKernel_fixes_Omega Ω C hc hker]
          rfl)
      have hconjres : resOmega Ω C hc (arithConj Ω C hc C hc F.hom s hs g) = resOmega Ω C hc g :=
        AlgEquiv.ext fun c ↦ (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by
          rw [algebraMap_resOmega, algebraMap_resOmega, arithConj_apply, hsΩ,
            ← algebraMap_resOmega, RingEquiv.symm_apply_eq, hsΩ])
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hconjres, mul_inv_eq_one] at hres
      calc resOmega Ω C hc ρ * resOmega Ω C hc g =
          resOmega Ω C hc ρ * ((resOmega Ω C hc ρ)⁻¹ * resOmega Ω C hc g * resOmega Ω C hc ρ) := by
            rw [hres]
        _ = resOmega Ω C hc g * resOmega Ω C hc ρ := by group
    have hz : resOmega Ω C hc ρ ∈ Subgroup.center (Ω ≃ₐ[K] Ω) :=
      Subgroup.mem_center_iff.2 fun ψ ↦ by
        obtain ⟨g, rfl⟩ := resOmega_surjective Ω C hc ψ
        exact (hcen g).symm
    rw [center_galoisGroup_eq_bot] at hz
    exact hz
  have hρfixΩ : ∀ c : Ω, ρ (algebraMap Ω (FFClosure (geomCurve Ω C)) c) = algebraMap Ω _ c :=
    fun c ↦ by rw [← algebraMap_resOmega, hρΩ, AlgEquiv.one_apply]
  have hρsec : ∀ a, ρ (secEmb Ω C hU a) = secEmb Ω C hU a := fun a ↦
    ρ.commutes (secToArithFF Ω C hc a)
  -- (3) the automorphism `σ = s ∘ ρ`
  let σ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C) := ρ.toRingEquiv.trans s
  have hσΩ : ∀ c : Ω, σ (algebraMap Ω _ c) = algebraMap Ω _ c := fun c ↦ by
    change s (ρ _) = _
    rw [hρfixΩ, hsΩ]
  have hσsec : ∀ a, σ (secEmb Ω C hU a) = secEmb Ω C hU (α a) := fun a ↦ by
    change s (ρ _) = _
    rw [hρsec, hsA]
  have hσsymm_sec : ∀ a, σ.symm (secEmb Ω C hU a) = secEmb Ω C hU (α.symm a) := fun a ↦ by
    rw [RingEquiv.symm_apply_eq, hσsec, AlgEquiv.apply_symm_apply]
  have hsecL : ∀ a, secEmb Ω C hU a ∈ (geomData Ω C).L := fun a ↦ SetLike.coe_mem _
  have hσL : ∀ x, x ∈ (geomData Ω C).L ↔ σ x ∈ (geomData Ω C).L := fun x ↦ by
    refine ⟨mem_L_of_forall Ω C hc σ hσΩ fun a ↦ hσsec a ▸ hsecL _, fun hx ↦ ?_⟩
    have := mem_L_of_forall Ω C hc σ.symm (fun c ↦ by
        rw [RingEquiv.symm_apply_eq, hσΩ]) (fun a ↦ hσsymm_sec a ▸ hsecL _) hx
    rwa [RingEquiv.symm_apply_apply] at this
  -- `σ` on the sections of `U_Ω`
  have hρT : ∀ r, ρ (tensorEmb Ω C hU r : FFClosure (geomCurve Ω C)) =
      (tensorEmb Ω C hU r : FFClosure (geomCurve Ω C)) := fun r ↦ by
    let S := RingHom.eqLocusField (ρ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C))
      (RingHom.id _)
    exact tensorEmb_mem_of_le Ω C hc S (fun c ↦ hρfixΩ c) (fun a ↦ hρsec a) r
  have hσU : ∀ b : Γ(geomCurve Ω C, geomOpen Ω C), ∃ a : Γ(geomCurve Ω C, geomOpen Ω C),
      σ ((curveEquivL Ω (transcendental_geomCoord Ω C)
        ((geomCurve Ω C).germToFunctionField (geomOpen Ω C) a) : (geomData Ω C).L) :
          FFClosure (geomCurve Ω C)) =
        ((curveEquivL Ω (transcendental_geomCoord Ω C)
          ((geomCurve Ω C).germToFunctionField (geomOpen Ω C) b) : (geomData Ω C).L) :
            FFClosure (geomCurve Ω C)) := by
    intro b
    let θ := Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[K] Ω) α
    refine ⟨(secTensorEquiv Ω C hc).symm (θ.symm (secTensorEquiv Ω C hc b)), ?_⟩
    rw [← tensorEmb_secToTensor Ω C hU, ← tensorEmb_secToTensor Ω C hU]
    change s (ρ _) = _
    rw [hρT, hsT]
    congr 2
    change θ (secTensorEquiv Ω C hc ((secTensorEquiv Ω C hc).symm _)) = secTensorEquiv Ω C hc b
    rw [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  -- conjugation by `σ` does not change the geometric action
  have hconj : ∀ n : (geomData Ω C).H,
      (geomData Ω C).chartHom (curveGaloisData_H_le Ω _) (genOpen Ω C C.U)
          (conjH (curveGaloisData_H_le Ω _) σ hσL n) =
        (geomData Ω C).chartHom (curveGaloisData_H_le Ω _) (genOpen Ω C C.U) n := by
    intro n
    apply geomToPi_injective Ω C hc
    rw [geomToPi_chartHom, geomToPi_chartHom, ← hA (toArithAut Ω C hc n)]
    congr 1
  have hfix := eq_of_chartHom_conj (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (geomOpen Ω C) σ hσL hσΩ hσU hconj
    (compl_finite_baseChangeOpen K Ω C.nonempty) (compl_nonempty_baseChangeOpen K Ω hc)
    (isHyperbolic_baseChange Ω C)
  -- conclusion: `α = id`, so `F = id`
  have hα : ∀ a, α a = a := fun a ↦ secEmb_injective Ω C hU (by
    rw [← hσsec]
    exact hfix _ (hsecL a))
  have hring : coverRing C C F.hom = RingHom.id _ := RingHom.ext hα
  ext1
  rw [Iso.refl_hom, ← specMap_coverRing C C F.hom, hring, CommRingCat.ofHom_id, Spec.map_id]
  rfl

end CurvesJacobian.LocAn
