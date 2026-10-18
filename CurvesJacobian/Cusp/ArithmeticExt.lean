/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithmeticSlim
import CurvesJacobian.Cusp.CurveGaloisData
import Belyi.Anabelian.Chain

/-!
# The arithmetic `CuspidalExt` of an affine hyperbolic curve over a number field (MR8.3 (b))

For a hyperbolic curve `C` over a number field `K` with at least one cusp (`hc`), an algebraic
closure `Ω` of `K`, and `U_Ω ⊆ X̄_Ω` hyperbolic (`hhyp`), the input of the group-theoretic
algorithms of [AbsTopI] §4 / [AbsTopII] §3 (`Belyi.Anabelian.CuspidalExt`):

* `Π = π₁ᵉᵗ(U, x)` (`x` an `Ω`-rational point of `U_Ω`), `G = π₁ᵉᵗ(Spec K) ≅ Gal(Ω/K)`,
  `Π ↠ G` (`CurvesJacobian.Cusp.projGk`), `G` slim, `Δ` slim and nontrivial
  (`CurvesJacobian.Cusp.ArithmeticSlim`);
* the cuspidal inertia groups (`CurvesJacobian.Cusp.arithCusps`): the `Π`-conjugates of the images
  in `Δ ⊆ Π` of the cuspidal inertia groups `cuspInertia U_Ω W` of `π₁ᵉᵗ(U_Ω)` (places `W` of
  `K(X̄_Ω)^alg` over the cusps `X̄_Ω ∖ U_Ω`, `CurvesJacobian.Cusp.cusps`), transported along
  `π₁ᵉᵗ(U_Ω, generic point) ≃ₜ* π₁ᵉᵗ(U_Ω, x) ≃ₜ* Δ` (change of base point, homotopy exact
  sequence). The change of base point is canonical up to inner automorphisms, so the
  conjugation-closed set does not depend on it.

`CurvesJacobian.Cusp.arithmeticExt Ω C hc hhyp : Belyi.Anabelian.CuspidalExt`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite WeilCurves.FunctionField Pi1.Orbifold AffOrbicurve
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Geom

variable {K : Type u} [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  (C : HypCurve K)

/-- The geometric curve `X̄_Ω`. -/
abbrev geomCurve : Scheme.{u} := baseChange K Ω C.Xbar

/-- The geometric open `U_Ω ⊆ X̄_Ω`. -/
abbrev geomOpen : (geomCurve Ω C).Opens := baseChangeOpen K Ω C.U

instance : IsIntegral (geomCurve Ω C) := IsCurveOver.isIntegral Ω (geomCurve Ω C)

instance : Nonempty (geomOpen Ω C) := (nonempty_baseChangeOpen K Ω C.nonempty).to_subtype

/-- A transcendental coordinate `τ ∈ K(X̄_Ω)`. -/
def geomCoord : (geomCurve Ω C).functionField :=
  (exists_transcendental Ω (geomCurve Ω C).functionField).choose

lemma transcendental_geomCoord : Transcendental Ω (geomCoord Ω C) :=
  (exists_transcendental Ω (geomCurve Ω C).functionField).choose_spec

end Geom

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The Galois data of `X̄_Ω`. -/
abbrev geomData := curveGaloisData Ω (transcendental_geomCoord Ω C)

instance : IsGalois (K₀ Ω (coordT (geomCoord Ω C))) (FFClosure (geomCurve Ω C)) :=
  isGalois_K₀_algebraicClosure (k := Ω) _ (transcendental_geomCoord Ω C)

/-- The cuspidal inertia groups of `π₁ᵉᵗ(U_Ω)` at its geometric generic point. -/
def geomCusps : Set (Subgroup π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
    genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (geomOpen Ω C))) :=
  cusps (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C)

/-- A change of base point `π₁ᵉᵗ(U_Ω, generic point) ≃ₜ* π₁ᵉᵗ(U_Ω, x)` (canonical up to inner
automorphisms). -/
def basePointEquiv : π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
    genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (geomOpen Ω C)) ≃ₜ*
    π₁ᵉᵗ(basePoint Ω C hc ≫ (specTensorIsoBaseChangeOpen K Ω (isAffineOpen_U C hc)).hom) :=
  (nonempty_fundamentalGroup_continuousMulEquiv _ _).some

/-- `π₁ᵉᵗ(U_Ω, generic point) → Δ ⊆ Π`: change of base point to `x`, then `Δ ≅ π₁ᵉᵗ(U_Ω, x)`. -/
def geomToPi : π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
    genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (geomOpen Ω C)) →* π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) :=
  (projGk Ω C hc).toMonoidHom.ker.subtype.comp
    ((kerProjGkEquivGeom Ω C hc).symm.toMulEquiv.toMonoidHom.comp
      (basePointEquiv Ω C hc).toMulEquiv.toMonoidHom)

lemma geomToPi_mem_ker (γ) : geomToPi Ω C hc γ ∈ (projGk Ω C hc).toMonoidHom.ker :=
  ((kerProjGkEquivGeom Ω C hc).symm (basePointEquiv Ω C hc γ)).2

/-- **The cuspidal inertia groups of `Π_U`**: the `Π`-conjugates of the images of the cuspidal
inertia groups of `π₁ᵉᵗ(U_Ω)`. -/
def arithCusps : Set (Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :=
  {I | ∃ I₀ ∈ geomCusps Ω C, ∃ g, I = (I₀.map (geomToPi Ω C hc)).map (MulAut.conj g).toMonoidHom}

lemma arithCusps_le {I} (hI : I ∈ arithCusps Ω C hc) : I ≤ (projGk Ω C hc).toMonoidHom.ker := by
  obtain ⟨I₀, -, g, rfl⟩ := hI
  rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
  exact (MonoidHom.normal_ker _).conj_mem _ (geomToPi_mem_ker Ω C hc w) g

/-- **The arithmetic `CuspidalExt` of an affine hyperbolic curve over a number field**:
`Π_U ↠ G_K` with `G_K` and `Δ_U` slim, `Δ_U ≠ 1`, and the cuspidal inertia groups. -/
def arithmeticExt (hhyp : Pi1.SurfaceGroup.IsHyperbolic
    (curveGenus Ω (baseChange K Ω C.Xbar)).toNat
    (Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _))) :
    CuspidalExt.{u + 1} where
  Pi := ProfiniteGrp.of π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))
  G := ProfiniteGrp.of π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  pr := projGk Ω C hc
  pr_surjective := projGk_surjective Ω C hc
  slim_G := isSlim_Gk Ω
  slim_delta := isSlim_Delta Ω C hc hhyp
  nontrivial_delta := Delta_ne_bot Ω C hc hhyp
  cusps := arithCusps Ω C hc
  cusps_le _ hI := arithCusps_le Ω C hc hI

end CurvesJacobian.Cusp
