/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.CountableModel
import CurvesJacobian.Galois.CountableSurfaceGroup

/-!
# `π₁ᵉᵗ` of a punctured curve over any algebraically closed field of characteristic zero

Let `X` be a curve of genus `g` over an algebraically closed field `k` of characteristic zero
(of any cardinality) and `U ⊆ X` an open subset with finite nonempty complement, `r = |X ∖ U|`.
Then at every geometric point `ξ` of `U`,

  `π₁ᵉᵗ(U, ξ) ≃ₜ* Π̂_{g,r}`

(`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_isAlgClosed`, and `…₀…` in
universe `0`).

Proof. Take a finite `f : X ⟶ ℙ¹` with `f⁻¹(∞) = X ∖ U` (`exists_finite_preimage_infty_eq`), so
`U ≅ Spec B`, `B = Γ(X ∖ f⁻¹(∞))` with coordinate `t`. The pair `(B, t)` has a model `(B₀, t₀)`
over a countable algebraically closed subfield `k₀ ⊆ k` (`exists_countable_model`,
`k ⊗[k₀] B₀ ≅ B`), and `B₀` is again a smooth affine curve with a finite coordinate
(`isDomain_of_tensor_equiv`, `smoothOfRelativeDimension_of_tensor_equiv`,
`finite_of_baseChange`), étale over `𝔸¹ ∖ S₀` for a finite `S₀ ⊆ k₀`
(`FiniteCoord.exists_etale_branchPolyOf`). Then:
* `π₁ᵉᵗ(Spec B) ≃ π₁ᵉᵗ(Spec B₀)` (belyi's `FiniteEtale.fundamentalGroupBaseChangeEquiv`: finite
  étale covers descend from `k ⊗ B₀` to `B₀` for countable `k₀`);
* `π₁ᵉᵗ(Spec B₀)` is the completion of a free group on `ι` with
  `|ι| + d + ∑_{s ∈ S₀} c_s = d |S₀| + 1` (belyi, Riemann existence over `ℂ ⊇ k₀`);
* the counts `d`, `c_s` are the same over `ℂ ⊗ B₀`, `B₀`, `k ⊗ B₀ ≅ B`
  (`card_maximalSpectrum_baseChange`), `f` is unramified over `𝔸¹ ∖ S₀` (étaleness ascends
  along `k₀ ⊆ k`), and Riemann–Hurwitz over `k` (`count_relation`) gives `|ι| = 2g + r - 1`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField ComplexAnalytic
open scoped IntermediateField TensorProduct

universe u

namespace CurvesJacobian

noncomputable section

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **`π₁ᵉᵗ` of a punctured curve over an algebraically closed field of characteristic zero is
the profinite surface group**, at every geometric point. Let `X` be a curve of genus `g` over `k`
(algebraically closed, characteristic zero) and `U ⊆ X` a nonempty open subset whose complement
is finite and nonempty, with `r` points. Then `π₁ᵉᵗ(U, ξ) ≃ₜ* Π̂_{g,r}` for every geometric point
`ξ : Spec Ω ⟶ U`. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_isAlgClosed (U : X.Opens)
    [Nonempty U] (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ U.toScheme) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat
          (Nat.card ((U : Set X)ᶜ : Set X)))))) := by
  classical
  set D : Set X := (U : Set X)ᶜ with hDdef
  have hgenU : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  have hDgen : ∀ p ∈ D, p ≠ genericPoint X := fun p hp h ↦ hp (h ▸ hgenU)
  obtain ⟨f, hfin, hD, hfk⟩ := exists_finite_preimage_infty_eq k X D hUfin hUne hDgen
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hDgen _ ((hD _).1 h) rfl
  haveI := isDomain_lineCoverRing_of hη
  haveI := smoothOfRelativeDimension_lineCoverRing hfk
  set t := (lineCoverCoord f).t with ht
  -- the countable model `(B₀, t₀)` over `k₀`
  obtain ⟨k₀, _, _, _, _, B₀, _, _, _, t₀, e, he, -⟩ :=
    exists_countable_model t (∅ : Set k) Set.finite_empty
  haveI : CharZero k₀ := (algebraMap k₀ k).charZero
  haveI : IsDomain B₀ := isDomain_of_tensor_equiv e
  haveI : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k₀ B₀))) :=
    smoothOfRelativeDimension_of_tensor_equiv e
  haveI : IsDomain (k ⊗[k₀] B₀) := e.toMulEquiv.isDomain
  have hinjk : Function.Injective (algebraMap k₀ k) := (algebraMap k₀ k).injective
  -- `e (1 ⊗ p(t₀)) = p(t)`
  have heval : ∀ p : MvPolynomial (Fin 1) k₀,
      e (1 ⊗ₜ MvPolynomial.aeval (fun _ : Fin 1 ↦ t₀) p) =
        MvPolynomial.aeval (fun _ : Fin 1 ↦ t) (MvPolynomial.map (algebraMap k₀ k) p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.aeval_C,
        ← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply,
        show algebraMap k₀ k r ⊗ₜ[k₀] (1 : B₀) = algebraMap k (k ⊗[k₀] B₀) (algebraMap k₀ k r) by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
        AlgEquiv.commutes]
    | add p q hp hq => rw [map_add, TensorProduct.tmul_add, map_add, hp, hq, map_add, map_add]
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X, ← mul_one (1 : k),
        ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, hp, he, map_mul, MvPolynomial.map_X,
        map_mul, MvPolynomial.aeval_X]
  -- finiteness and injectivity of the coordinate `t₀`
  have hfin' : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦
      (1 ⊗ₜ t₀ : k ⊗[k₀] B₀)).Finite := by
    have h : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ (1 ⊗ₜ t₀ : k ⊗[k₀] B₀)) =
        (e.symm : lineCoverRing f →ₐ[k] k ⊗[k₀] B₀).comp (MvPolynomial.aeval fun _ ↦ t) :=
      MvPolynomial.algHom_ext fun _ ↦ by
        rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X, ← he,
          AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
    rw [AlgHom.Finite, h]
    exact RingHom.Finite.comp
      (g := (e.symm : lineCoverRing f →ₐ[k] k ⊗[k₀] B₀).toRingHom)
      (RingHom.Finite.of_surjective _ e.symm.surjective) (lineCoverCoord f).finite
  have hfin₀ := finite_of_baseChange t₀ hfin'
  let D₀ : Converse.FiniteCoord k₀ B₀ := ⟨t₀, hfin₀⟩
  have hinj₀ : Function.Injective (MvPolynomial.aeval (R := k₀) fun _ : Fin 1 ↦ t₀) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h := heval p
    rw [hp, TensorProduct.tmul_zero, map_zero] at h
    have h' := (injective_iff_map_eq_zero _).1 (lineCoverCoord_injective hη hfk) _ h.symm
    exact MvPolynomial.map_injective _ hinjk (h'.trans (map_zero _).symm)
  -- the branch locus over `k₀`, and over `k`
  obtain ⟨S₀, hS₀⟩ := FiniteCoord.exists_etale_branchPolyOf D₀ hinj₀
  set S : Finset k := S₀.image (algebraMap k₀ k) with hSdef
  have hmapP : MvPolynomial.map (algebraMap k₀ k) (Converse.branchPolyOf S₀) =
      Converse.branchPolyOf S := by
    rw [Converse.branchPolyOf, map_prod, Converse.branchPolyOf,
      Finset.prod_image fun a _ b _ h ↦ hinjk h]
    refine Finset.prod_congr rfl fun s _ ↦ ?_
    rw [map_sub, MvPolynomial.map_X, MvPolynomial.map_C]
  have het := D₀.etale_baseChange_of (Ω := k) _ hS₀
  rw [hmapP] at het
  have hunr : ∀ (Q : Place k X.functionField) (b : k), b ∉ S →
      Q.ord (coordFun f hη - algebraMap k X.functionField b) ≤ 1 := by
    intro Q b hb
    refine ord_coordFun_sub_le_one_of_ringEquiv hη hfk e.toRingEquiv b
      ((1 ⊗ₜ t₀ : k ⊗[k₀] B₀) - algebraMap k (k ⊗[k₀] B₀) b)
      (by rw [map_sub, AlgEquiv.coe_ringEquiv, he,
        AlgEquiv.commutes]) (fun M _ hM hne ↦ ?_) Q
    exact sub_notMem_sq_of_etale (B := k ⊗[k₀] B₀) (1 ⊗ₜ t₀) (Converse.branchPolyOf S) het
      (aeval_branchPolyOf_ne_zero hb) M hM hne
  -- `k₀ ⊆ ℂ` and belyi's computation for `B₀`
  obtain ⟨a₀, ha₀⟩ := Infinite.exists_notMem_finset S₀
  obtain ⟨σ⟩ := Converse.nonempty_ringHom_complex_of_countable k₀
  letI : Algebra k₀ (ULift.{u} ℂ) :=
    ((ULift.ringEquiv (R := ℂ)).symm.toRingHom.comp σ).toAlgebra
  obtain ⟨x⟩ := nonempty_analytification_baseChangeSpec (k := k₀) B₀
  have hinjℂ : Function.Injective fun s : k₀ ↦ (algebraMap k₀ (ULift.{u} ℂ) s).down :=
    ULift.down_injective.comp (algebraMap k₀ (ULift.{u} ℂ)).injective
  have hc : (algebraMap k₀ (ULift.{u} ℂ) a₀).down ∉
      S₀.image fun s ↦ (algebraMap k₀ (ULift.{u} ℂ) s).down := by
    rw [Finset.mem_image]
    rintro ⟨s, hs, h⟩
    exact ha₀ (hinjℂ h ▸ hs)
  obtain ⟨ι, hι, ⟨Φ⟩, hcard⟩ :=
    D₀.exists_etaleFundamentalGroup_equiv_completion_freeGroup_of_finset S₀ hS₀ hc x
  -- the counts over `ℂ ⊗ B₀`, `B₀`, `k ⊗ B₀ ≅ B` agree
  have hcnt : ∀ b : k₀, fiberCard (ULift.{u} ℂ ⊗[k₀] B₀) (1 ⊗ₜ D₀.t)
      (algebraMap k₀ (ULift.{u} ℂ) b).down =
        Nat.card {M : MaximalSpectrum (lineCoverRing f) //
          t - algebraMap k (lineCoverRing f) (algebraMap k₀ k b) ∈ M.asIdeal} := by
    intro b
    refine (card_maximalSpectrum_baseChange (Ω := ULift.{u} ℂ) t₀ hfin₀ b).trans ?_
    rw [← card_maximalSpectrum_baseChange (Ω := k) t₀ hfin₀ b]
    refine Nat.card_congr ((maximalSpectrumMemEquiv e.toRingEquiv _).trans
      (Equiv.subtypeEquivRight fun M ↦ ?_))
    rw [map_sub, AlgEquiv.coe_ringEquiv, he, AlgEquiv.commutes]
  simp only [hcnt] at hcard
  -- Riemann–Hurwitz over `k`
  have ha : algebraMap k₀ k a₀ ∉ S := by
    rw [hSdef, Finset.mem_image]
    rintro ⟨s, hs, h⟩
    exact ha₀ (hinjk h ▸ hs)
  have hrel := count_relation hη hfk D hD hDgen S hunr ha
  rw [hSdef, Finset.sum_image fun a _ b _ h ↦ hinjk h,
    Finset.card_image_of_injective _ hinjk] at hrel
  have hcard' : (Nat.card ι : ℤ) = 2 * curveGenus k X + Nat.card D - 1 := by
    have h1 : (Nat.card ι : ℤ) + Nat.card {M : MaximalSpectrum (lineCoverRing f) //
          t - algebraMap k (lineCoverRing f) (algebraMap k₀ k a₀) ∈ M.asIdeal} +
        ∑ s ∈ S₀, (Nat.card {M : MaximalSpectrum (lineCoverRing f) //
          t - algebraMap k (lineCoverRing f) (algebraMap k₀ k s) ∈ M.asIdeal} : ℤ) =
        Nat.card {M : MaximalSpectrum (lineCoverRing f) //
          t - algebraMap k (lineCoverRing f) (algebraMap k₀ k a₀) ∈ M.asIdeal} * S₀.card + 1 := by
      exact_mod_cast hcard
    linarith
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
    rw [hr] at hcard'
    omega
  haveI : Finite (Pi1.SurfaceGen g r) := Finite.of_equiv _ (surfaceGenEquiv g r).symm
  haveI : Finite (ULift.{u} (Pi1.SurfaceGen g r)) := Finite.of_equiv _ Equiv.ulift.symm
  obtain ⟨eι⟩ := (Finite.card_eq (α := ι) (β := ULift.{u} (Pi1.SurfaceGen g r))).1 hι'
  -- `U ≅ Spec B ≅ Spec (k ⊗ B₀)`
  have hrange : (pullback.fst f (lineι k)).opensRange = U := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    ext p
    change f.base p ∈ Set.range (lineι k).base ↔ p ∈ (U : Set X)
    rw [mem_range_lineι_iff, ne_eq, hD, hDdef, Set.mem_compl_iff, not_not]
  haveI := isAffine_lineCover (f := f)
  let eU : Spec (CommRingCat.of (lineCoverRing f)) ≅ U.toScheme :=
    (lineCover f).isoSpec.symm ≪≫ (pullback.fst f (lineι k)).isoOpensRange ≪≫ X.isoOfEq hrange
  let eB : Spec (CommRingCat.of (lineCoverRing f)) ≅ Spec (CommRingCat.of (k ⊗[k₀] B₀)) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let xk : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (k ⊗[k₀] B₀)) :=
    ξ ≫ (eU.symm ≪≫ eB).hom
  haveI : ConnectedSpace (Spec (CommRingCat.of B₀)) := inferInstance
  let ξ₀ := geometricPoint (Converse.baseChangeSpec k₀ B₀) x ≫
    FiniteEtale.baseChangeSpec k₀ (ULift.{u} ℂ) B₀
  obtain ⟨e₃⟩ := FiniteEtale.nonempty_fundamentalGroup_continuousMulEquiv
    (xk ≫ FiniteEtale.baseChangeSpec k₀ k B₀) ξ₀
  exact ⟨(fundamentalGroupEquivOfIso (eU.symm ≪≫ eB) ξ).trans
    ((FiniteEtale.fundamentalGroupBaseChangeEquiv (k := k₀) (Ω := k) (R := B₀) xk).trans
      (e₃.trans (Φ.trans (ProfiniteGrp.isoToContinuousMulEquiv
        (ProfiniteGrp.profiniteCompletion.mapIso
          (MulEquiv.toGrpIso (freeGroupEquivSurfaceGroup g r eι)))))))⟩

end Main

section Zero

open Pi1.Profinite

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **`π₁ᵉᵗ(X ∖ D) ≃ₜ* Π̂_{g,r}`** with pi1's `Pi1.ProfiniteSurfaceGroup` (universe `0`), at every
geometric point, over any algebraically closed field of characteristic zero. -/
theorem etaleFundamentalGroup_equiv_profiniteSurfaceGroup₀_of_isAlgClosed (U : X.Opens)
    [Nonempty U] (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ U.toScheme) :
    Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
      (Nat.card ((U : Set X)ᶜ : Set X))) := by
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup_of_isAlgClosed (k := k) U hUfin
    hUne ξ
  exact ⟨e.trans (completionCongr MulEquiv.ulift)⟩

end Zero

end

end CurvesJacobian
