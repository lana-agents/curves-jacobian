/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.ClosedSurfaceGroupCountable
import CurvesJacobian.Galois.CountableModel
import CurvesJacobian.Galois.AbelianPi1
import CurvesJacobian.Galois.LineCoverModel
import Belyi.Curve.Existence

/-!
# `π₁ᵉᵗ` of a complete curve over any algebraically closed field of characteristic zero

Let `X` be a curve of genus `g` over an algebraically closed field `k` of characteristic zero
(of any cardinality). Then for every geometric point `ξ` of `X`,

  `π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`, the profinite completion of `Π_{g,0} = ⟨a, b | ∏[aᵢ,bᵢ]⟩`

(`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_isAlgClosed`, and
`…₀_of_isAlgClosed` in universe `0`).

## Proof

Choose a closed point `p` and a finite `f : X ⟶ ℙ¹` with `f⁻¹(∞) = {p}`
(`CurvesJacobian.exists_finite_preimage_infty_eq`), so `X ∖ {p} = Spec B` with the coordinate
`t`. The pair `(B, t)` has a model `(B₀, t₀)` over a countable algebraically closed subfield
`k₀ ⊆ k` (`CurvesJacobian.exists_countable_model`), and then `X ≅ X₀ ×_{k₀} k` for the relative
normalisation `X₀` of `ℙ¹_{k₀}` in `Spec B₀ ⟶ 𝔸¹_{k₀}`
(`CurvesJacobian.exists_iso_pullback_normalization_lineCover`); `X₀` is a curve over `k₀`
(belyi's `Belyi.IsCurveOver.of_baseChangeModel`). Hence

  `π₁ᵉᵗ(X) ≅ π₁ᵉᵗ(X₀ ×_{k₀} k) ≅ π₁ᵉᵗ(X₀) ≅ Π̂_{g₀,0}`

by belyi's INV-2 (`AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective'`,
`k₀` countable) and the countable case
(`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_countable`). Finally
`g₀ = g`: both `Hom_cont(π₁ᵉᵗ(X), ℤ/2)` and `Hom_cont(π₁ᵉᵗ(X₀), ℤ/2)` are counted by
`CurvesJacobian.card_continuousMonoidHom_zmod_etaleFundamentalGroup_proper`
(`2^{2g}` and `2^{2g₀}`), and they are in bijection.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField
open scoped TensorProduct
open Pi1.Profinite

universe u

namespace CurvesJacobian

noncomputable section

namespace ClosedSurface

/-- The projection `Y ×_k K ⟶ Y` is surjective, for a field extension `K / k`. -/
lemma surjective_pullback_fst_specAlgebraMap (k K : Type u) [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) :
    Function.Surjective (pullback.fst q (specAlgebraMap k K)).base := by
  haveI : Surjective (specAlgebraMap k K) := by
    refine ⟨fun x ↦ ?_⟩
    haveI : Subsingleton (Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Nonempty (PrimeSpectrum K))
    exact ⟨y, Subsingleton.elim _ _⟩
  haveI : Surjective (pullback.fst q (specAlgebraMap k K)) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  exact Surjective.surj

/-- Every point of a scheme is the image of a geometric point. -/
lemma exists_geometricPoint (Y : Scheme.{u}) (z : Y) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (x : Spec (CommRingCat.of L) ⟶ Y),
      ∀ w, x.base w = z := by
  let L := AlgebraicClosure (Y.residueField z)
  refine ⟨L, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField z) L)) ≫ Y.fromSpecResidueField z, fun w ↦ ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.fromSpecResidueField_apply]

/-- Continuous characters are invariant under topological group isomorphisms. -/
lemma natCard_continuousMonoidHom_congr {G H A : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [Group A] [TopologicalSpace A] (e : G ≃ₜ* H) :
    Nat.card (ContinuousMonoidHom G A) = Nat.card (ContinuousMonoidHom H A) := by
  let i : ContinuousMonoidHom G H := ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩
  let j : ContinuousMonoidHom H G := ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
  refine Nat.card_congr
    { toFun := fun φ ↦ φ.comp j
      invFun := fun φ ↦ φ.comp i
      left_inv := fun φ ↦ ?_
      right_inv := fun φ ↦ ?_ }
  · ext g
    change φ (e.symm (e g)) = φ g
    rw [ContinuousMulEquiv.symm_apply_apply]
  · ext h
    change φ (e (e.symm h)) = φ h
    rw [ContinuousMulEquiv.apply_symm_apply]

end ClosedSurface

open ClosedSurface in
/-- **`π₁ᵉᵗ` of a complete curve over an algebraically closed field of characteristic zero is
the profinite closed surface group**: for a curve `X` over `k` (algebraically closed,
characteristic zero, any cardinality) of genus `g` and every geometric point
`ξ : Spec Ω ⟶ X`, `π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_isAlgClosed {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat 0)))) := by
  classical
  -- a finite map `f : X ⟶ ℙ¹` with a single pole
  obtain ⟨p, hp, hpgen⟩ := exists_isClosed_ne_genericPoint k (X := X)
  obtain ⟨f, hfin, hD, hfk⟩ := exists_finite_preimage_infty_eq k X {p} (Set.finite_singleton p)
    (Set.singleton_nonempty p) (fun x hx ↦ (Set.mem_singleton_iff.1 hx) ▸ hpgen)
  haveI := hfin
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hpgen ((hD _).1 h).symm
  -- the countable model of the affine part
  obtain ⟨k₀, _, _, _, _, B₀, _, _, _, t₀, e, he, -⟩ :=
    exists_countable_model (lineCoverCoord f).t (∅ : Set k) Set.finite_empty
  haveI : CharZero k₀ := (algebraMap k₀ k).charZero
  letI : Algebra (Polynomial k₀) B₀ := (Polynomial.aeval t₀).toRingHom.toAlgebra
  haveI : IsScalarTower k₀ (Polynomial k₀) B₀ :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (Polynomial.aeval_C t₀ c).symm
  have he' : ∀ r : Polynomial k₀, e (1 ⊗ₜ algebraMap (Polynomial k₀) B₀ r) =
      algebraMap (Polynomial k) (lineCoverRing f) (Polynomial.map (algebraMap k₀ k) r) := by
    intro r
    let φ₁ : Polynomial k₀ →+* lineCoverRing f :=
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := k₀) (A := k)
        (B := B₀)).toRingHom).comp (algebraMap (Polynomial k₀) B₀)
    let φ₂ : Polynomial k₀ →+* lineCoverRing f :=
      (algebraMap (Polynomial k) (lineCoverRing f)).comp
        (Polynomial.mapRingHom (algebraMap k₀ k))
    have h : φ₁ = φ₂ := by
      refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
      · change e (1 ⊗ₜ Polynomial.aeval t₀ (Polynomial.C c)) =
          algebraMap (Polynomial k) (lineCoverRing f) (Polynomial.map _ (Polynomial.C c))
        rw [Polynomial.aeval_C, Polynomial.map_C, ← Polynomial.algebraMap_eq (R := k),
          ← IsScalarTower.algebraMap_apply k (Polynomial k) (lineCoverRing f),
          ← AlgEquiv.commutes e, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply]
        exact congrArg e (by rw [Algebra.algebraMap_eq_smul_one (A := B₀),
          Algebra.algebraMap_eq_smul_one (A := k), TensorProduct.smul_tmul])
      · change e (1 ⊗ₜ Polynomial.aeval t₀ Polynomial.X) =
          algebraMap (Polynomial k) (lineCoverRing f) (Polynomial.map _ Polynomial.X)
        rw [Polynomial.aeval_X, Polynomial.map_X, he]
        rfl
    exact congrArg (fun φ : Polynomial k₀ →+* lineCoverRing f ↦ φ r) h
  -- the model `X₀` of `X`
  obtain ⟨E, hE⟩ := exists_iso_pullback_normalization_lineCover f hfk hη e he'
  set y₀ : Spec (CommRingCat.of B₀) ⟶ P1 k₀ :=
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) B₀)) ≫ lineι k₀
  set X₀ := y₀.normalization
  letI : X₀.Over (Spec (CommRingCat.of k₀)) :=
    ⟨y₀.fromNormalization ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀))⟩
  haveI : IsCurveOver k₀ X₀ := IsCurveOver.of_baseChangeModel k₀ k X₀ E hE
  haveI : IsIntegral X₀ := IsCurveOver.isIntegral k₀ X₀
  set G := pullback.fst (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ k)
  haveI : IsIntegral (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ k) :
      Scheme.{u}) :=
    IsCurveOver.isIntegral k _
  haveI hconn : ConnectedSpace (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ k) :
      Scheme.{u}) :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ _).isConnected
  haveI : ConnectedSpace (pullback (y₀.fromNormalization ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)))
      (specAlgebraMap k₀ k) : Scheme.{u}) := hconn
  -- INV-2 for `X₀ ×_{k₀} k ⟶ X₀`
  obtain ⟨τ, hτ⟩ := exists_transcendental_functionField k₀ X₀
  have hτ0 : τ ≠ 0 := fun h ↦ hτ (h ▸ isAlgebraic_zero)
  obtain ⟨z, hz⟩ := surjective_pullback_fst_specAlgebraMap k₀ k
    (X₀ ↘ Spec (CommRingCat.of k₀)) (genericPoint X₀)
  obtain ⟨L, _, _, x, hx⟩ := exists_geometricPoint _ z
  have hbij := FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective' k₀ k X₀
    (chartOne k₀ X₀ τ) (chartZero k₀ X₀ τ) (isAffineOpen_chartOne hτ) (isAffineOpen_chartZero hτ)
    (chartOne_sup_chartZero τ) x (fun w ↦ by
      rw [Scheme.Hom.comp_base, TopCat.comp_app, hx, hz]
      exact ⟨genericPoint_mem_chartOne τ, genericPoint_mem_chartZero hτ0⟩)
  let F := FiniteEtale.fundamentalGroupMap G (rfl : x ≫ G = _)
  let m : π₁ᵉᵗ(x) ≃* π₁ᵉᵗ(x ≫ G) := MulEquiv.ofBijective F.toMonoidHom hbij
  let h : π₁ᵉᵗ(x) ≃ₜ π₁ᵉᵗ(x ≫ G) :=
    Continuous.homeoOfEquivCompactToT2 (f := m.toEquiv) F.continuous_toFun
  let E₁ : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(x ≫ G) :=
    { m with continuous_toFun := h.continuous_toFun, continuous_invFun := h.continuous_invFun }
  obtain ⟨E₂⟩ := FiniteEtale.nonempty_fundamentalGroup_continuousMulEquiv (ξ ≫ E.hom) x
  let Ψ : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(x ≫ G) := (fundamentalGroupEquivOfIso E ξ).trans (E₂.trans E₁)
  -- the countable case for `X₀`
  obtain ⟨Φ⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_countable
    (k := k₀) (X := X₀) (x ≫ G)
  -- the genus
  have hc := card_continuousMonoidHom_zmod_etaleFundamentalGroup_proper (k := k) ξ 2
  have hc₀ := card_continuousMonoidHom_zmod_etaleFundamentalGroup_proper (k := k₀) (x ≫ G) 2
  rw [natCard_continuousMonoidHom_congr Ψ, hc₀] at hc
  have hg : (curveGenus k X).toNat = (curveGenus k₀ X₀).toNat := by
    have := Nat.pow_right_injective (le_refl 2) hc
    omega
  rw [hg]
  exact ⟨Ψ.trans Φ⟩

/-- **`π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`** with pi1's `Pi1.ProfiniteSurfaceGroup` (universe `0`), at every
geometric point, over any algebraically closed field of characteristic zero. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero₀_of_isAlgClosed {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat 0) := by
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_isAlgClosed (k := k) ξ
  exact ⟨e.trans (completionCongr MulEquiv.ulift)⟩

end

end CurvesJacobian
