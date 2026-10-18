/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.BelyiInfty
import CurvesJacobian.Galois.BelyiSurfaceGroup
import CurvesJacobian.Galois.GenericEtale
import CurvesJacobian.Galois.HurwitzFinset
import Pi1.FundamentalGroup.FiberFunctorIso
import Pi1.Surface.Profinite

/-!
# `π₁ᵉᵗ` of a punctured curve over a countable algebraically closed field

Let `X` be a curve over a **countable** algebraically closed field `k` of characteristic zero, of
genus `g`, and `U ⊆ X` an open subset with finite nonempty complement `D`, `r = |D|`. Then

  `π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}`

(`CurvesJacobian.exists_etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_countable` at a
geometric point `Spec ℂ ⟶ U`;
`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_countable` and
`…₀_of_countable` at every geometric point). This generalises the computation over `ℚ̄`
(`CurvesJacobian.exists_etaleFundamentalGroup_equiv_profiniteSurfaceGroup`) — a curve over `k`
need not be defined over `ℚ̄` (e.g. an elliptic curve with transcendental `j`-invariant), so
instead of a Belyi map we use **any** finite `f : X ⟶ ℙ¹` with `f⁻¹(∞) = D`:

* `CurvesJacobian.exists_finite_preimage_infty_eq`: `f = toP1 τ` for a function `τ` with poles
  exactly at `D` (`CurvesJacobian.exists_chartOne_eq`, Riemann–Roch);
* `CurvesJacobian.FiniteCoord.exists_etale_branchPolyOf`: `f` is étale over `𝔸¹ ∖ S` for a finite
  `S ⊆ k` (generic étaleness in characteristic zero);
* belyi's
  `Belyi.Converse.FiniteCoord.exists_etaleFundamentalGroup_equiv_completion_freeGroup_of_finset`
  (Riemann existence for the branched cover `X ∖ D → 𝔸¹` of `ℂ ∖ σ(S)` and invariance of `π₁ᵉᵗ`
  under `k ⊆ ℂ`, `k` countable): `π₁ᵉᵗ(U)` is the completion of a free group on `ι` with
  `|ι| + d + ∑_{s ∈ S} c_s = d |S| + 1`;
* the counts `d = [K(X) : k(x)]` and `c_s` are counted by places
  (`CurvesJacobian.card_maximalSpectrum_lineCover_eq`, `CurvesJacobian.card_ord_sub_pos_eq_finrank`
  with `CurvesJacobian.ord_coordFun_sub_le_one_of_etale`), and Riemann–Hurwitz over `S ∪ {∞}`
  (`CurvesJacobian.genus_of_finset`) gives `2g - 2 = d (|S| - 1) - r - ∑ c_s`, so
  `|ι| = 2g + r - 1` and `F_{2g+r-1} ≅ Π_{g,r}`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField ComplexAnalytic
open scoped IntermediateField TensorProduct

universe u

namespace CurvesJacobian

noncomputable section

section FiniteMap

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

omit [IsAlgClosed k] in
/-- **Finite maps to `ℙ¹` with `f⁻¹(∞) = D`.** For a curve `X` over an algebraically closed field
`k` of characteristic zero and a nonempty finite set `D` of closed points, there is a finite
`k`-morphism `f : X ⟶ ℙ¹_k` whose fibre over `∞` is exactly `D` (`f = toP1 τ`, `τ` with poles
exactly at `D`). -/
theorem exists_finite_preimage_infty_eq (D : Set X) (hDfin : D.Finite) (hDne : D.Nonempty)
    (hD : ∀ x ∈ D, x ≠ genericPoint X) :
    ∃ f : X ⟶ P1 k, IsFinite f ∧ (∀ x : X, f.base x = P1.infty k ↔ x ∈ D) ∧
      f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k) := by
  classical
  have hDcl : IsClosed D := by
    have := hDfin.isClosed_biUnion (fun x hx ↦ isClosed_closedPoint k X ⟨x, hD x hx⟩)
    simpa using this
  let U : X.Opens := ⟨Dᶜ, hDcl.isOpen_compl⟩
  haveI : Nonempty U := ⟨⟨genericPoint X, fun h ↦ hD _ h rfl⟩⟩
  have hUc : (U : Set X)ᶜ.Finite := by simpa [U] using hDfin
  have hUne : U ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hDne
    intro h
    have hxU : x ∈ (U : Set X) := by rw [h]; trivial
    exact hxU hx
  obtain ⟨τ, hτ, hUτ⟩ := exists_chartOne_eq k U hUc hUne
  refine ⟨toP1 k X τ, isFinite_toP1 hτ, fun x ↦ ?_,
    (Scheme.Hom.isOver_iff (S := Spec (CommRingCat.of k))).mp inferInstance⟩
  rw [toP1_eq_infty_iff, ← hUτ]
  change x ∉ Dᶜ ↔ x ∈ D
  simp

end FiniteMap

section Count

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] {f : X ⟶ P1 k} [IsFinite f]

omit [IsAlgClosed k] in
/-- `k[t] → B` is injective for the coordinate `t` of a finite `f` with `f(η) ≠ ∞` (its image in
`K(X)` is the transcendental `x = f^*T`). -/
theorem lineCoverCoord_injective (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    Function.Injective (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ (lineCoverCoord f).t) := by
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h := congrArg (lineCoverToFunctionField f hη) hp
  rw [map_zero, mvAeval_eq_aeval_finOnePolyEquiv] at h
  change lineCoverToFunctionField f hη (Polynomial.aeval
    (algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X) (finOnePolyEquiv k p)) = 0 at h
  rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply,
    lineCoverToFunctionField_algebraMap, coordHom_eq_aeval hη hfk] at h
  rw [← map_eq_zero_iff _ (finOnePolyEquiv k).injective]
  exact (injective_iff_map_eq_zero _).1 (transcendental_iff_injective.1 hx) _ h

omit [IsAlgClosed k] [CharZero k] in
/-- `P_S(a) ≠ 0` for `a ∉ S`. -/
lemma aeval_branchPolyOf_ne_zero {S : Finset k} {a : k} (ha : a ∉ S) :
    MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ a) (Converse.branchPolyOf S) ≠ 0 := by
  rw [aeval_branchPolyOf, Finset.prod_ne_zero_iff]
  intro s hs h
  rw [Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h
  exact ha (h ▸ hs)

/-- **The numbers of a finite map to `ℙ¹`**: for a finite `f : X ⟶ ℙ¹` with `f⁻¹(∞) = D`,
`r = |D|`, unramified over `𝔸¹ ∖ S`, and `a ∉ S`,
`(2g + r - 1) + d + ∑_{s ∈ S} c_s = d |S| + 1`, where `d` and `c_s` are the numbers of maximal
ideals of `B = Γ(X ∖ D)` containing `t - a` and `t - s` (Riemann–Hurwitz,
`CurvesJacobian.genus_of_finset`). -/
theorem count_relation (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (D : Set X)
    (hD : ∀ p : X, f.base p = P1.infty k ↔ p ∈ D) (hDgen : ∀ p ∈ D, p ≠ genericPoint X)
    (S : Finset k) (hunr : ∀ (Q : Place k X.functionField) (b : k), b ∉ S →
      Q.ord (coordFun f hη - algebraMap k X.functionField b) ≤ 1) {a : k} (ha : a ∉ S) :
    (2 * curveGenus k X + Nat.card D - 1 : ℤ) +
        Nat.card {M : MaximalSpectrum (lineCoverRing f) //
          (lineCoverCoord f).t - algebraMap k (lineCoverRing f) a ∈ M.asIdeal} +
        ∑ s ∈ S, (Nat.card {M : MaximalSpectrum (lineCoverRing f) //
          (lineCoverCoord f).t - algebraMap k (lineCoverRing f) s ∈ M.asIdeal} : ℤ) =
      Nat.card {M : MaximalSpectrum (lineCoverRing f) //
          (lineCoverCoord f).t - algebraMap k (lineCoverRing f) a ∈ M.asIdeal} * S.card + 1 := by
  classical
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  simp only [card_maximalSpectrum_lineCover_eq hη hfk]
  have hd := card_ord_sub_pos_eq_finrank hx a (fun Q ↦ hunr Q a ha)
  have hg := genus_of_finset hx S hunr
  have hpoles := card_ord_coordFun_neg hη hfk D hD hDgen
  rw [hd]
  simp only [← Nat.card_coe_set_eq, Set.coe_setOf] at hg
  rw [hpoles] at hg
  unfold curveGenus
  linarith

/-- **`π₁ᵉᵗ(X ∖ f⁻¹(∞))` is the completion of a free group of rank `2g + r - 1`** for a finite
`f : X ⟶ ℙ¹` with `f⁻¹(∞) = D`, `r = |D|`, `k` countable. -/
theorem exists_etaleFundamentalGroup_lineCover_equiv_of_countable [Countable k]
    [Algebra k (ULift.{u} ℂ)]
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (D : Set X)
    (hD : ∀ p : X, f.base p = P1.infty k ↔ p ∈ D) (hDgen : ∀ p ∈ D, p ≠ genericPoint X)
    (x : analytification.obj (Converse.baseChangeSpec k (lineCoverRing f))) :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (π₁ᵉᵗ(geometricPoint (Converse.baseChangeSpec k (lineCoverRing f)) x ≫
          FiniteEtale.baseChangeSpec k (ULift.{u} ℂ) (lineCoverRing f)) ≃ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup ι))) ∧
      (Nat.card ι : ℤ) = 2 * curveGenus k X + Nat.card D - 1 := by
  classical
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hDgen _ ((hD _).1 h) rfl
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  haveI := isDomain_lineCoverRing_of hη
  haveI := smoothOfRelativeDimension_lineCoverRing hfk
  obtain ⟨S, hS⟩ := CurvesJacobian.FiniteCoord.exists_etale_branchPolyOf (lineCoverCoord f)
    (lineCoverCoord_injective hη hfk)
  obtain ⟨a, haS⟩ := Infinite.exists_notMem_finset S
  have hinj : Function.Injective fun s : k ↦ (algebraMap k (ULift.{u} ℂ) s).down :=
    ULift.down_injective.comp (algebraMap k (ULift.{u} ℂ)).injective
  have hc : (algebraMap k (ULift.{u} ℂ) a).down ∉
      S.image fun s ↦ (algebraMap k (ULift.{u} ℂ) s).down := by
    rw [Finset.mem_image]
    rintro ⟨s, hs, h⟩
    exact haS (hinj h ▸ hs)
  obtain ⟨ι, hι, hπ, hcard⟩ :=
    (lineCoverCoord f).exists_etaleFundamentalGroup_equiv_completion_freeGroup_of_finset S hS hc x
  refine ⟨ι, hι, hπ, ?_⟩
  simp only [fiberCard_algebraMap hη hfk] at hcard
  have hunr : ∀ (Q : Place k X.functionField) (b : k), b ∉ S →
      Q.ord (coordFun f hη - algebraMap k X.functionField b) ≤ 1 :=
    fun Q b hb ↦ ord_coordFun_sub_le_one_of_etale hη hfk _ hS Q b (aeval_branchPolyOf_ne_zero hb)
  have hd := card_ord_sub_pos_eq_finrank hx a (fun Q ↦ hunr Q a haS)
  have hg := genus_of_finset hx S hunr
  have hpoles := card_ord_coordFun_neg hη hfk D hD hDgen
  rw [hd] at hcard
  simp only [← Nat.card_coe_set_eq, Set.coe_setOf] at hg
  rw [hpoles] at hg
  unfold curveGenus
  have hcard' : (Nat.card ι : ℤ) + Module.finrank k⟮coordFun f hη⟯ X.functionField +
      ∑ s ∈ S, (Nat.card {Q : Place k X.functionField //
        0 < Q.ord (coordFun f hη - algebraMap k X.functionField s)} : ℤ) =
      Module.finrank k⟮coordFun f hη⟯ X.functionField * S.card + 1 := by
    exact_mod_cast hcard
  linarith

end Count

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Countable k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **`π₁ᵉᵗ` of a punctured curve over a countable algebraically closed field is the profinite
surface group.** Let `X` be a curve over `k` (algebraically closed, characteristic zero,
countable) and `U ⊆ X` a nonempty open subset whose complement is finite and nonempty, with
`r = |X ∖ U|` points. Then at some geometric point `ξ : Spec ℂ ⟶ U` (for an embedding `k ⊆ ℂ`),

  `π₁ᵉᵗ(U, ξ) ≃ₜ* Π̂_{g,r}`,

`g` the genus of `X`. -/
theorem exists_etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_countable (U : X.Opens)
    [Nonempty U] (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty) :
    ∃ ξ : Spec (CommRingCat.of (ULift.{u} ℂ)) ⟶ U.toScheme,
      Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat
          (Nat.card ((U : Set X)ᶜ : Set X)))))) := by
  obtain ⟨σ⟩ := Converse.nonempty_ringHom_complex_of_countable k
  letI : Algebra k (ULift.{u} ℂ) :=
    ((ULift.ringEquiv (R := ℂ)).symm.toRingHom.comp σ).toAlgebra
  set D : Set X := (U : Set X)ᶜ with hDdef
  have hgenU : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  have hDgen : ∀ p ∈ D, p ≠ genericPoint X := fun p hp h ↦ hp (h ▸ hgenU)
  obtain ⟨f, hfin, hD, hfk⟩ := exists_finite_preimage_infty_eq k X D hUfin hUne hDgen
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hDgen _ ((hD _).1 h) rfl
  haveI := isDomain_lineCoverRing_of hη
  obtain ⟨x⟩ := nonempty_analytification_baseChangeSpec (k := k) (lineCoverRing f)
  obtain ⟨ι, hι, ⟨Φ⟩, hcard⟩ :=
    exists_etaleFundamentalGroup_lineCover_equiv_of_countable hfk D hD hDgen x
  -- the numbers
  have hg0 : 0 ≤ curveGenus k X := genus_nonneg_of_isAlgClosed
  obtain ⟨r, hr⟩ : ∃ r, Nat.card D = r + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by
      haveI := hUfin.to_subtype
      exact (Nat.card_pos_iff.2 ⟨hUne.to_subtype, inferInstance⟩).ne')
  rw [hr]
  set g := (curveGenus k X).toNat with hgdef
  have hg : (g : ℤ) = curveGenus k X := Int.toNat_of_nonneg hg0
  have hι' : Nat.card ι = Nat.card (ULift.{u} (Pi1.SurfaceGen g r)) := by
    rw [Nat.card_ulift, natCard_surfaceGen]
    rw [hr] at hcard
    omega
  haveI : Finite (Pi1.SurfaceGen g r) := Finite.of_equiv _ (surfaceGenEquiv g r).symm
  haveI : Finite (ULift.{u} (Pi1.SurfaceGen g r)) := Finite.of_equiv _ Equiv.ulift.symm
  obtain ⟨e⟩ := (Finite.card_eq (α := ι) (β := ULift.{u} (Pi1.SurfaceGen g r))).1 hι'
  -- `Spec B ≅ U`
  have hrange : (pullback.fst f (lineι k)).opensRange = U := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    ext p
    change f.base p ∈ Set.range (lineι k).base ↔ p ∈ (U : Set X)
    rw [mem_range_lineι_iff, ne_eq, hD, hDdef, Set.mem_compl_iff, not_not]
  haveI := isAffine_lineCover (f := f)
  let eU : Spec (CommRingCat.of (lineCoverRing f)) ≅ U.toScheme :=
    (lineCover f).isoSpec.symm ≪≫ (pullback.fst f (lineι k)).isoOpensRange ≪≫ X.isoOfEq hrange
  refine ⟨(geometricPoint (Converse.baseChangeSpec k (lineCoverRing f)) x ≫
    FiniteEtale.baseChangeSpec k (ULift.{u} ℂ) (lineCoverRing f)) ≫ eU.hom, ⟨?_⟩⟩
  exact (fundamentalGroupEquivOfIso eU _).symm.trans (Φ.trans
    (ProfiniteGrp.isoToContinuousMulEquiv (ProfiniteGrp.profiniteCompletion.mapIso
      (MulEquiv.toGrpIso (freeGroupEquivSurfaceGroup g r e)))))

/-- **`π₁ᵉᵗ(X ∖ D) ≃ₜ* Π̂_{g,r}` at every geometric point**, `k` countable (algebraically closed,
characteristic zero). -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_countable (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ U.toScheme) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat
          (Nat.card ((U : Set X)ᶜ : Set X)))))) := by
  obtain ⟨ξ₀, ⟨e⟩⟩ :=
    exists_etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_countable (k := k) U hUfin hUne
  obtain ⟨e'⟩ := FiniteEtale.nonempty_fundamentalGroup_continuousMulEquiv ξ ξ₀
  exact ⟨e'.trans e⟩

end Main

section Zero

open Pi1.Profinite

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] [Countable k]
  {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **`π₁ᵉᵗ(X ∖ D) ≃ₜ* Π̂_{g,r}`** with pi1's `Pi1.ProfiniteSurfaceGroup` (universe `0`), at every
geometric point, `k` countable. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup₀_of_countable (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ U.toScheme) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
      (Nat.card ((U : Set X)ᶜ : Set X))) := by
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_countable (k := k) U hUfin
    hUne ξ
  exact ⟨e.trans (completionCongr MulEquiv.ulift)⟩

end Zero

end

end CurvesJacobian
