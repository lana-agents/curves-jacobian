/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.ClosedSurfaceGroup
import CurvesJacobian.Galois.CountableSurfaceGroup
import Oka.Analytification.Pi1.BranchedCoordinateProperAny

/-!
# `π₁ᵉᵗ` of a complete curve over a countable algebraically closed field

Let `X` be a curve of genus `g` over a **countable** algebraically closed field `k` of
characteristic zero. Then for every geometric point `ξ` of `X`,

  `π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`, the profinite completion of `Π_{g,0} = ⟨a, b | ∏[aᵢ,bᵢ]⟩`

(`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_countable`, and
`…₀_of_countable` in universe `0`). This generalises the case `k` algebraic over `ℚ`
(`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero`), which used a Belyi map.

## Proof

Choose a closed point `p` and **any** finite `f : X ⟶ ℙ¹` with `f⁻¹(∞) = {p}`
(`CurvesJacobian.exists_finite_preimage_infty_eq`); `X ∖ {p} = Spec B` with the coordinate
`t = f^*T`, finite over `k[t]`, and étale over `𝔸¹ ∖ S` for a finite nonempty `S ⊆ k`
(`CurvesJacobian.FiniteCoord.exists_etale_branchPolyOf_nonempty`, generic étaleness). Base change
along an embedding `σ : k ⊆ ℂ` (`k` is countable): `X_ℂ^an` is compact Hausdorff and
`Spec (ℂ ⊗ B) ⟶ X_ℂ` is an open immersion onto the complement of the unique point over `p`
(as in `CurvesJacobian.ClosedSurface.nonempty_fundamentalGroup_curveLFT_mulEquiv`). oka's
`ComplexAnalytic.exists_fundamentalGroup_analytification_specLFT_mulEquiv_surfaceGroup_of_finset`
(van Kampen with the `n`-point geometric basis of `π₁(ℂ ∖ σ(S))`) gives
`π₁(X_ℂ^an) ≃* Π_{g',0}` with `2g' + ∑_{s ∈ S} c_s + d = d |S| + 1`, and Riemann–Hurwitz over
`S ∪ {∞}` (`CurvesJacobian.genus_of_finset`) gives `g' = g`
(`CurvesJacobian.ClosedSurface.nonempty_fundamentalGroup_curveLFT_mulEquiv_of_isFinite`).
Finally `π₁ᵉᵗ(X_ℂ) ≅ π₁(X_ℂ^an)^` (oka's comparison theorem) and `π₁ᵉᵗ(X_ℂ) ≅ π₁ᵉᵗ(X)` (belyi's
`AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective'`, `k` countable).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField ComplexAnalytic
open scoped IntermediateField TensorProduct
open Pi1.Profinite

universe u

namespace CurvesJacobian

namespace ClosedSurface

section Analytic

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Algebra k (ULift.{u} ℂ)]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]
  {f : X ⟶ P1 k} [IsFinite f]

/-- **`π₁` of the analytification of `X_ℂ` is the closed surface group of genus `g`**, for any
finite `f : X ⟶ ℙ¹` with a single point `p` over `∞`. -/
theorem nonempty_fundamentalGroup_curveLFT_mulEquiv_of_isFinite
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) {p : X}
    (hp : IsClosed {p}) (hD : ∀ x : X, f.base x = P1.infty k ↔ x = p)
    (hpgen : p ≠ genericPoint X) (y : analytification.obj (curveLFT k X)) :
    Nonempty (FundamentalGroup (analytification.obj (curveLFT k X)) y ≃*
      Pi1.SurfaceGroup (curveGenus k X).toNat 0) := by
  classical
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hpgen ((hD _).1 h).symm
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  haveI := isDomain_lineCoverRing_of hη
  haveI := t2Space_analytification_curveLFT f hfk
  haveI : IsDomain (lineCoverRing f ⊗[k] ULift.{u} ℂ) :=
    Converse.isDomain_tensorProduct_of_isAlgClosed
  haveI : IsDomain (ULift.{u} ℂ ⊗[k] lineCoverRing f) :=
    (Algebra.TensorProduct.comm k (ULift.{u} ℂ) (lineCoverRing f)).toMulEquiv.isDomain
  haveI := smoothOfRelativeDimension_lineCoverRing hfk
  haveI := Converse.FiniteCoord.smoothOfRelativeDimension_baseChange (k := k)
    (Ω := ULift.{u} ℂ) (B := lineCoverRing f) (n := 1)
  -- the branch locus
  obtain ⟨S, hSne, hS⟩ := FiniteCoord.exists_etale_branchPolyOf_nonempty (lineCoverCoord f)
    (lineCoverCoord_injective hη hfk)
  have het := (lineCoverCoord f).etale_baseChange_of (Ω := ULift.{u} ℂ) _ hS
  rw [Converse.map_branchPolyOf] at het
  obtain ⟨a, haS⟩ := Infinite.exists_notMem_finset S
  have hinj : Function.Injective fun s : k ↦ (algebraMap k (ULift.{u} ℂ) s).down :=
    ULift.down_injective.comp (algebraMap k (ULift.{u} ℂ)).injective
  have hc : (algebraMap k (ULift.{u} ℂ) a).down ∉
      S.image fun s ↦ (algebraMap k (ULift.{u} ℂ) s).down := by
    rw [Finset.mem_image]
    rintro ⟨s, hs, h⟩
    exact haS (hinj h ▸ hs)
  -- the unique point of `X_ℂ` over `p`
  obtain ⟨q, hq⟩ := surjective_fst (k := k) (X := X) p
  have hfib : (pullback.fst (X ↘ Spec (CommRingCat.of k))
      (specAlgebraMap k (ULift.{u} ℂ))).base ⁻¹' {p} = {q} :=
    (subsingleton_preimage_fst X hp).eq_singleton_of_mem hq
  have hrange : Set.range (lineCoverιLFT f hfk).hom.left.base = {q}ᶜ := by
    change Set.range (lineCoverιC f hfk).base = _
    rw [range_lineCoverιC, range_lineCoverι f hD, Set.preimage_compl, hfib]
    rfl
  obtain ⟨g, ⟨Φ⟩, hcard⟩ :=
    exists_fundamentalGroup_analytification_specLFT_mulEquiv_surfaceGroup_of_finset
      (A := ULift.{u} ℂ ⊗[k] lineCoverRing f) (lineCoverιLFT f hfk) q hrange
      (1 ⊗ₜ (lineCoverCoord f).t) (lineCoverCoord f).finite_baseChange _ (hSne.image _) het hc y
  rw [Finset.sum_image fun a _ b _ h ↦ hinj h, Finset.card_image_of_injective _ hinj] at hcard
  simp only [fiberCard_algebraMap hη hfk] at hcard
  -- Riemann–Hurwitz
  have hunr : ∀ (Q : Place k X.functionField) (b : k), b ∉ S →
      Q.ord (coordFun f hη - algebraMap k X.functionField b) ≤ 1 :=
    fun Q b hb ↦ ord_coordFun_sub_le_one_of_etale hη hfk _ hS Q b (aeval_branchPolyOf_ne_zero hb)
  have hd := card_ord_sub_pos_eq_finrank hx a (fun Q ↦ hunr Q a haS)
  have hgen := genus_of_finset hx S hunr
  have hpoles := card_ord_coordFun_neg hη hfk {p}
    (fun x ↦ (hD x).trans Set.mem_singleton_iff.symm)
    (fun x hx ↦ (Set.mem_singleton_iff.1 hx) ▸ hpgen)
  rw [hd] at hcard
  simp only [← Nat.card_coe_set_eq, Set.coe_setOf] at hgen
  rw [hpoles, Nat.card_unique (α := ({p} : Set X))] at hgen
  have hcard' : (2 * g : ℤ) + ∑ s ∈ S, (Nat.card {Q : Place k X.functionField //
        0 < Q.ord (coordFun f hη - algebraMap k X.functionField s)} : ℤ) +
      Module.finrank k⟮coordFun f hη⟯ X.functionField =
      Module.finrank k⟮coordFun f hη⟯ X.functionField * S.card + 1 := by
    exact_mod_cast hcard
  have hg : (g : ℤ) = curveGenus k X := by
    unfold curveGenus
    push_cast at hgen
    linarith
  have hg' : g = (curveGenus k X).toNat := by omega
  exact ⟨hg' ▸ Φ⟩

end Analytic

end ClosedSurface

/-- **`π₁ᵉᵗ` of a complete curve over a countable algebraically closed field is the profinite
closed surface group**: for a curve `X` over `k` (algebraically closed, characteristic zero,
countable) of genus `g` and every geometric point `ξ : Spec Ω ⟶ X`, `π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_countable {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] [Countable k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat 0)))) := by
  open ClosedSurface in
  obtain ⟨σ⟩ := Converse.nonempty_ringHom_complex_of_countable k
  letI : Algebra k (ULift.{u} ℂ) :=
    ((ULift.ringEquiv (R := ℂ)).symm.toRingHom.comp σ).toAlgebra
  obtain ⟨p, hp, hpgen⟩ := exists_isClosed_ne_genericPoint k (X := X)
  obtain ⟨f, hfin, hD, hfk⟩ := exists_finite_preimage_infty_eq k X {p} (Set.finite_singleton p)
    (Set.singleton_nonempty p) (fun x hx ↦ (Set.mem_singleton_iff.1 hx) ▸ hpgen)
  haveI := hfin
  have hD' : ∀ x : X, f.base x = P1.infty k ↔ x = p := fun x ↦ (hD x).trans Set.mem_singleton_iff
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hpgen ((hD' _).1 h).symm
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  set τ := coordFun f hη
  have hτ0 : τ ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  set U := chartOne k X τ
  set U' := chartZero k X τ
  -- a closed point of `X_ℂ` over `U ∩ U'`
  set g := pullback.fst (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k (ULift.{u} ℂ))
  have hne : (g.base ⁻¹' ((U ⊓ U' : X.Opens) : Set X)).Nonempty := by
    obtain ⟨z, hz⟩ := surjective_fst (k := k) (X := X) (genericPoint X)
    exact ⟨z, by rw [Set.mem_preimage, hz]; exact ⟨genericPoint_mem_chartOne τ,
      genericPoint_mem_chartZero hτ0⟩⟩
  haveI : JacobsonSpace (curveBC k X) :=
    @LocallyOfFiniteType.jacobsonSpace _ _ (curveLFT k X).obj.hom (curveLFT k X).property _
  obtain ⟨z, hzU, hzc⟩ := nonempty_inter_closedPoints hne
    ((U ⊓ U').isOpen.preimage g.base.hom.continuous).isLocallyClosed
  obtain ⟨y, hy⟩ := (mem_range_analytificationπ_base_iff (curveLFT k X) z).2 hzc
  set ξC := geometricPoint (curveLFT k X) y
  have hξC : ∀ w, (ξC ≫ g).base w ∈ U ⊓ U' := fun w ↦ by
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    change g.base (ξC.base w) ∈ _
    rw [show ξC.base w = z from (geometricPoint_apply (curveLFT k X) y w).trans hy]
    exact hzU
  have hbij := FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective' k (ULift.{u} ℂ) X U U'
    (isAffineOpen_chartOne hx) (isAffineOpen_chartZero hx) (chartOne_sup_chartZero τ) ξC hξC
  -- `π₁ᵉᵗ(X_ℂ) ≃ₜ* π₁ᵉᵗ(X)`
  let F := FiniteEtale.fundamentalGroupMap g (rfl : ξC ≫ g = _)
  let e : π₁ᵉᵗ(ξC) ≃* π₁ᵉᵗ(ξC ≫ g) := MulEquiv.ofBijective F.toMonoidHom hbij
  let h : π₁ᵉᵗ(ξC) ≃ₜ π₁ᵉᵗ(ξC ≫ g) :=
    Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) F.continuous_toFun
  let E₁ : π₁ᵉᵗ(ξC) ≃ₜ* π₁ᵉᵗ(ξC ≫ g) :=
    { e with continuous_toFun := h.continuous_toFun, continuous_invFun := h.continuous_invFun }
  -- the comparison theorem
  obtain ⟨Φ⟩ := nonempty_fundamentalGroup_curveLFT_mulEquiv_of_isFinite hfk hp hD' hpgen y
  let E₂ := etaleFundamentalGroupEquivCompletion (X := curveLFT k X) y
  haveI : ConnectedSpace X :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ X).isConnected
  obtain ⟨E₀⟩ := FiniteEtale.nonempty_fundamentalGroup_continuousMulEquiv ξ (ξC ≫ g)
  exact ⟨E₀.trans (E₁.symm.trans (E₂.trans (completionCongr (Φ.trans MulEquiv.ulift.symm))))⟩

/-- **`π₁ᵉᵗ(X, ξ) ≃ₜ* Π̂_{g,0}`** with pi1's `Pi1.ProfiniteSurfaceGroup` (universe `0`), at every
geometric point, `k` countable. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero₀_of_countable {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] [Countable k] {X : Scheme.{0}}
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat 0) := by
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_countable (k := k) ξ
  exact ⟨e.trans (completionCongr MulEquiv.ulift)⟩

end CurvesJacobian
