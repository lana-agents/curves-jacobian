/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.BelyiAffinePart
import Pi1.Surface.Basic

/-!
# `π₁ᵉᵗ` of a punctured curve over `ℚ̄` is the profinite surface group

Let `X` be a curve over an algebraically closed field `k` of characteristic zero, algebraic over
`ℚ` (e.g. `k = ℚ̄`), and `U ⊆ X` an open subset with finite nonempty complement `D`, `r = |D|`,
`g` the genus of `X`. Then

  `π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}`, the profinite completion of `Π_{g,r} = ⟨a, b, c | ∏[aᵢ,bᵢ] ∏ cⱼ⟩`

(`CurvesJacobian.exists_etaleFundamentalGroup_equiv_profiniteSurfaceGroup`), at a geometric point
`Spec ℂ ⟶ U` (for an embedding `k ⊆ ℂ`).

Proof. Take a Belyi map `f : X ⟶ ℙ¹` with `f⁻¹(∞) = D`
(`CurvesJacobian.exists_isBelyiMap_preimage_infty_eq`), so `U = X ×_{ℙ¹} 𝔸¹ = Spec B`. By belyi
(`Belyi.IsBelyiMap.exists_etaleFundamentalGroup_equiv_completion_freeGroup`; Riemann existence and
invariance of `π₁ᵉᵗ` under `k ⊆ ℂ`), `π₁ᵉᵗ(Spec B)` is the profinite completion of a free group on
`ι` with `|ι| + d + c₀ + c₁ = 2d + 1`, where `d, c₀, c₁` count maximal ideals of `ℂ ⊗ B`
containing `t - 2, t, t - 1`. These counts are those of `B` (`card_maximalSpectrum_baseChange`),
hence of places of `K(X)` with `ord_Q (x - a) > 0` (`card_maximalSpectrum_lineCover_eq`) for the
coordinate function `x = f^*(T)`; `x` is unramified over `a ≠ 0, 1` (`ord_coordFun_sub_le_one`),
so `d = [K(X) : k(x)]` (`card_ord_sub_pos_eq_finrank`), and the poles of `x` are `D`
(`card_ord_coordFun_neg`). Riemann–Hurwitz for Belyi maps (weil-curves `genus_belyi`):
`2g - 2 = d - c₀ - c₁ - r`, hence `|ι| = 2g + r - 1`, and `F_{2g+r-1} ≅ Π_{g,r}`
(`Pi1.SurfaceGroup.freeEquiv`, `r ≥ 1`).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi WeilCurves.FunctionField ComplexAnalytic
open scoped IntermediateField TensorProduct

universe u

namespace CurvesJacobian

noncomputable section

/-- The genus of a function field over an algebraically closed field is nonnegative. -/
lemma genus_nonneg_of_isAlgClosed {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    [IsFunctionField k K] : 0 ≤ genus k K := by
  have h := ell_canonical (k := k) (K := K)
  rw [ell_zero_eq_one_of_isAlgClosed] at h
  omega

/-- The generators of `Π_{g,r}`: `g + g + r` of them. -/
def surfaceGenEquiv (g r : ℕ) : Pi1.SurfaceGen g r ≃ (Fin g ⊕ Fin g) ⊕ Fin r where
  toFun
    | .a i => .inl (.inl i)
    | .b i => .inl (.inr i)
    | .c j => .inr j
  invFun
    | .inl (.inl i) => .a i
    | .inl (.inr i) => .b i
    | .inr j => .c j
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (i | i) | j <;> rfl

lemma natCard_surfaceGen (g r : ℕ) : Nat.card (Pi1.SurfaceGen g r) = 2 * g + r := by
  rw [Nat.card_congr (surfaceGenEquiv g r), Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

/-- A free group on `2g + r` generators is `Π_{g,r+1}`. -/
def freeGroupEquivSurfaceGroup {ι : Type u} (g r : ℕ)
    (e : ι ≃ ULift.{u} (Pi1.SurfaceGen g r)) :
    FreeGroup ι ≃* ULift.{u} (Pi1.SurfaceGroup g (r + 1)) :=
  (FreeGroup.freeGroupCongr (e.trans Equiv.ulift)).trans
    ((Pi1.SurfaceGroup.freeEquiv (g := g) (r := r)).symm.trans MulEquiv.ulift.symm)

section Pi1

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- `π₁ᵉᵗ` along an isomorphism of schemes. -/
def fundamentalGroupEquivOfIso {Y Z : Scheme.{u}} (e : Y ≅ Z) (ξ : Spec (.of Ω) ⟶ Y) :
    π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ e.hom) :=
  let φ := FiniteEtale.fundamentalGroupMap e.hom (rfl : ξ ≫ e.hom = _)
  let m : π₁ᵉᵗ(ξ) ≃* π₁ᵉᵗ(ξ ≫ e.hom) := MulEquiv.ofBijective φ.toMonoidHom
    (FiniteEtale.fundamentalGroupMap_bijective_of_isIso e.hom rfl)
  let h : π₁ᵉᵗ(ξ) ≃ₜ π₁ᵉᵗ(ξ ≫ e.hom) :=
    Continuous.homeoOfEquivCompactToT2 (f := m.toEquiv) φ.continuous_toFun
  { m with
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

end Pi1

/-- The analytification of `Spec (ℂ ⊗[k] B)` is nonempty for a domain `B` of finite type. -/
lemma nonempty_analytification_baseChangeSpec {k : Type u} [Field k] [Algebra k (ULift.{u} ℂ)]
    (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] :
    Nonempty (analytification.obj (Converse.baseChangeSpec k B)) := by
  haveI : Nontrivial (ULift.{u} ℂ ⊗[k] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k _ _
      (algebraMap k _).injective (algebraMap k B).injective
  haveI : Nontrivial Γ((Converse.baseChangeSpec k B).obj.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℂ ⊗[k] B))).commRingCatIsoToRingEquiv.toEquiv
      |>.nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ((Converse.baseChangeSpec k B).obj.left, ⊤)
  obtain ⟨v, -⟩ := exists_idealOfPoint_eq (Converse.baseChangeSpec k B) M
  exact ⟨v⟩

section Belyi

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] {f : X ⟶ P1 k} [IsFinite f]

/-- The fibre count of `ℂ ⊗ B` over `a ∈ k` is the number of zeros of `x - a`. -/
lemma fiberCard_algebraMap [Algebra k (ULift.{u} ℂ)] (hf : IsBelyiMap k f)
    (hη : f.base (genericPoint X) ≠ P1.infty k)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (a : k) :
    fiberCard (ULift.{u} ℂ ⊗[k] lineCoverRing f) (1 ⊗ₜ hf.branchedData.t)
        (algebraMap k (ULift.{u} ℂ) a).down =
      Nat.card {Q : Place k X.functionField //
        0 < Q.ord (coordFun f hη - algebraMap k X.functionField a)} := by
  rw [← card_maximalSpectrum_lineCover_eq hf hη hfk a]
  exact card_maximalSpectrum_baseChange (Ω := ULift.{u} ℂ) hf.branchedData.t
    hf.branchedData.finite a

/-- **`π₁ᵉᵗ(X ∖ f⁻¹(∞))` is the completion of a free group of rank `2g + r - 1`** for a Belyi map
`f` with `f⁻¹(∞) = D`, `r = |D|`. -/
theorem exists_etaleFundamentalGroup_lineCover_equiv [Algebra.IsAlgebraic ℚ k]
    [Algebra k (ULift.{u} ℂ)] (hf : IsBelyiMap k f)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) (D : Set X)
    (hD : ∀ p : X, f.base p = P1.infty k ↔ p ∈ D) (hDgen : ∀ p ∈ D, p ≠ genericPoint X)
    (x : analytification.obj (Converse.baseChangeSpec k (lineCoverRing f))) :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (π₁ᵉᵗ(geometricPoint (Converse.baseChangeSpec k (lineCoverRing f)) x ≫
          FiniteEtale.baseChangeSpec k (ULift.{u} ℂ) (lineCoverRing f)) ≃ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup ι))) ∧
      (Nat.card ι : ℤ) = 2 * curveGenus k X + Nat.card D - 1 := by
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hDgen _ ((hD _).1 h) rfl
  haveI := isDominant_of_isFinite f
  have hx := transcendental_coordFun hη hfk
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have h21 : (2 : k) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : k) = ((1 : ℕ) : k) := by exact_mod_cast h
    exact absurd (Nat.cast_injective this) (by norm_num)
  have hinj := (algebraMap k (ULift.{u} ℂ)).injective
  have hc0 : (algebraMap k (ULift.{u} ℂ) 2).down ≠ 0 := fun h ↦
    h2 (hinj (by rw [map_zero]; exact ULift.ext _ _ h))
  have hc1 : (algebraMap k (ULift.{u} ℂ) 2).down ≠ 1 := fun h ↦
    h21 (hinj (by rw [map_one]; exact ULift.ext _ _ h))
  obtain ⟨ι, hι, hπ, hcard⟩ :=
    hf.exists_etaleFundamentalGroup_equiv_completion_freeGroup hfk hc0 hc1 x
  refine ⟨ι, hι, hπ, ?_⟩
  have e0 : (0 : ℂ) = (algebraMap k (ULift.{u} ℂ) 0).down := by simp
  have e1 : (1 : ℂ) = (algebraMap k (ULift.{u} ℂ) 1).down := by simp
  rw [e0, e1, fiberCard_algebraMap hf hη hfk, fiberCard_algebraMap hf hη hfk,
    fiberCard_algebraMap hf hη hfk] at hcard
  have hunr : ∀ (Q : Place k X.functionField) (a : k), a ≠ 0 → a ≠ 1 →
      Q.ord (coordFun f hη - algebraMap k X.functionField a) ≤ 1 :=
    fun Q a ha0 ha1 ↦ ord_coordFun_sub_le_one hf hη hfk Q a ha0 ha1
  have hd := card_ord_sub_pos_eq_finrank hx 2 (fun Q ↦ hunr Q 2 h2 h21)
  have hg := genus_belyi hx hunr
  have hpoles := card_ord_coordFun_neg hη hfk D hD hDgen
  simp only [map_zero, sub_zero, map_one] at hcard
  rw [hd] at hcard
  simp only [← Nat.card_coe_set_eq, Set.coe_setOf] at hg
  rw [hpoles] at hg
  unfold curveGenus
  omega

end Belyi

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

/-- **`π₁ᵉᵗ` of a punctured curve over `ℚ̄` is the profinite surface group.** Let `X` be a curve
over `k` (algebraically closed, characteristic zero, algebraic over `ℚ`, e.g. `ℚ̄`) and `U ⊆ X` a
nonempty open subset whose complement is finite and nonempty, with `r = |X ∖ U|` points. Then at
some geometric point `ξ : Spec ℂ ⟶ U`,

  `π₁ᵉᵗ(U, ξ) ≃ₜ* Π̂_{g,r}`,

the profinite completion of the surface group `Π_{g,r}` (pi1's `Pi1.SurfaceGroup`), `g` the
genus of `X` (`CurvesJacobian.curveGenus`; it is `≥ 0`). -/
theorem exists_etaleFundamentalGroup_equiv_profiniteSurfaceGroup (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty) :
    ∃ ξ : Spec (CommRingCat.of (ULift.{u} ℂ)) ⟶ U.toScheme,
      Nonempty (π₁ᵉᵗ(ξ) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup (curveGenus k X).toNat
          (Nat.card ((U : Set X)ᶜ : Set X)))))) := by
  letI : Algebra k (ULift.{u} ℂ) :=
    (IsAlgClosed.lift (R := ℚ) (S := k) (M := ULift.{u} ℂ)).toRingHom.toAlgebra
  set D : Set X := (U : Set X)ᶜ with hDdef
  have hgenU : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  have hDgen : ∀ p ∈ D, p ≠ genericPoint X := fun p hp h ↦ hp (h ▸ hgenU)
  obtain ⟨f, hf, hD, hfk⟩ := exists_isBelyiMap_preimage_infty_eq k X D hUfin hUne hDgen
  haveI := hf.isFinite
  haveI := isDomain_lineCoverRing hf
  obtain ⟨x⟩ := nonempty_analytification_baseChangeSpec (k := k) (lineCoverRing f)
  obtain ⟨ι, hι, ⟨Φ⟩, hcard⟩ := exists_etaleFundamentalGroup_lineCover_equiv hf hfk D hD hDgen x
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

end Main

end

end CurvesJacobian
