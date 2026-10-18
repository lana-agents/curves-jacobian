/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CurveInertiaIso
import CurvesJacobian.Cusp.FiniteCover
import CurvesJacobian.Cusp.LineTopS
import CurvesJacobian.Cusp.LineInertiaS
import CurvesJacobian.Galois.CountableSurfaceGroup

/-!
# `π₁ᵉᵗ(X ∖ D) ≅ Π̂_{g,r}` compatibly with the cuspidal inertia groups (any `k = k̄`, char `0`)

Let `k` be algebraically closed of characteristic `0`, `X` a curve over `k` with Galois model
`(D, eL)` (`H = H_L`), and `U ⊆ X` open with finite nonempty complement. This generalises
`CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia_curve` (which assumes `k` algebraic
over `ℚ`).

**Main result** (`CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia_curve_of_line`):
assuming the inertia-compatible description of `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞})) ≅ Π̂_{0,|S|+1}` for finite
nonempty `S ⊆ k` (the hypothesis `hline`), for `g` the genus of `X` and `r = |X ∖ U|` there is
`Θ : π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}` mapping every cuspidal inertia group
`CurvesJacobian.Cusp.cuspInertia D X eL hH U W` (`W ⊇ k` a place of `Ω` not centred on `U`) onto a
conjugate of a cuspidal inertia group `Iⱼ = ⟨cⱼ⟩‾`.

Proof: as for `ℚ̄`, with the Belyi map replaced by a finite `f : X ⟶ ℙ¹` with `f⁻¹(∞) = X ∖ U`
(`CurvesJacobian.exists_finite_preimage_infty_eq`) and a finite nonempty `S ⊆ k` such that
`U' = f⁻¹(𝔸¹ ∖ S)` is finite étale over `𝔸¹ ∖ S`
(`CurvesJacobian.Cusp.exists_finset_isFiniteEtale_coverMapS`). Then `π₁ᵉᵗ(U')` is an open
subgroup of `π₁ᵉᵗ(𝔸¹ ∖ S) ≅ Π̂_{0,n+2} ≅ F̂_{n+1}` (`n + 1 = |S|`,
`CurvesJacobian.Cusp.freeEquivN`),
the cuspidal inertia groups of `U'` are the intersections with it of the inertia groups of the
line (`CurvesJacobian.Cusp.map_cuspInertia_coverMapS`), and filling in the points of `U` over `S`
is the group-theoretic filling `CurvesJacobian.Cusp.exists_surfaceGroup_quotient`. The cusps over
`∞` are counted as for `ℚ̄`, using that `⟨x_∞⟩‾ ⊆ F̂_{n+1}` is self-normalising
(`CurvesJacobian.Cusp.mem_basicInertia_xInf_of_map_conj_eq`).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite PreGaloisCategory
open Pi1.ReidemeisterSchreier (xInf)

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### `F(x₀, …, xₙ) ≅ Π_{0,n+2}` -/

section Free

variable (n : ℕ)

/-- The generators `c₀, …, cₙ` of `Π_{0,n+2}` as `Fin (n + 1)`. -/
def genFinN : Pi1.SurfaceGen 0 (n + 1) ≃ Fin (n + 1) where
  toFun
    | .c j => j
    | .a i => i.elim0
    | .b i => i.elim0
  invFun j := .c j
  left_inv := by
    rintro (i | i | j)
    · exact i.elim0
    · exact i.elim0
    · rfl
  right_inv _ := rfl

@[simp] lemma genFinN_c (j : Fin (n + 1)) : genFinN n (.c j) = j := rfl

/-- `F(x₀, …, xₙ) ≃* Π_{0,n+2}`, `xₐ ↦ cₐ` (so `x_∞ = (x₀ ⋯ xₙ)⁻¹ ↦ c_{n+1}`). -/
def freeEquivN : FreeGroup (Fin (n + 1)) ≃* Pi1.SurfaceGroup 0 (n + 2) :=
  ((Pi1.SurfaceGroup.freeEquiv (g := 0) (r := n + 1)).trans
    (FreeGroup.freeGroupCongr (genFinN n))).symm

/-- The words `x₀, …, xₙ, x_∞ = (x₀ ⋯ xₙ)⁻¹`. -/
def lineWordN : Fin (n + 2) → FreeGroup (Fin (n + 1)) :=
  Fin.lastCases (xInf n) fun a ↦ FreeGroup.of a

@[simp] lemma lineWordN_castSucc (a : Fin (n + 1)) :
    lineWordN n a.castSucc = FreeGroup.of a := by
  rw [lineWordN, Fin.lastCases_castSucc]

@[simp] lemma lineWordN_last : lineWordN n (Fin.last (n + 1)) = xInf n := by
  rw [lineWordN, Fin.lastCases_last]

variable {n}

lemma freeEquivN_of (a : Fin (n + 1)) :
    freeEquivN n (FreeGroup.of a) = Pi1.SurfaceGroup.cusp (g := 0) (r := n + 2) a.castSucc := by
  rw [freeEquivN, MulEquiv.symm_apply_eq]
  change FreeGroup.of a = FreeGroup.freeGroupCongr (genFinN n)
    (Pi1.SurfaceGroup.freeEquiv (Pi1.SurfaceGroup.cusp (g := 0) (r := n + 1 + 1) a.castSucc))
  rw [Pi1.SurfaceGroup.freeEquiv_cusp_castSucc, FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
  rfl

variable (n) in
lemma freeEquivN_xInf :
    freeEquivN n (xInf n) =
      Pi1.SurfaceGroup.cusp (g := 0) (r := n + 2) (Fin.last (n + 1)) := by
  rw [freeEquivN, MulEquiv.symm_apply_eq]
  change _ = FreeGroup.freeGroupCongr (genFinN n)
    (Pi1.SurfaceGroup.freeEquiv (Pi1.SurfaceGroup.cusp (g := 0) (r := n + 1 + 1) (Fin.last _)))
  rw [Pi1.SurfaceGroup.freeEquiv_cusp_last, Pi1.SurfaceGroup.lastCuspWord, map_inv, map_mul]
  simp only [Pi1.SurfaceGen.commProd, Pi1.SurfaceGen.ordProd, List.ofFn_zero, List.prod_nil,
    map_one, one_mul, map_list_prod, List.map_ofFn]
  rw [Pi1.ReidemeisterSchreier.xInf]
  congr 3

lemma freeEquivN_lineWordN (j : Fin (n + 2)) :
    freeEquivN n (lineWordN n j) = Pi1.SurfaceGroup.cusp (g := 0) (r := n + 2) j := by
  refine Fin.lastCases ?_ (fun a ↦ ?_) j
  · rw [lineWordN_last, freeEquivN_xInf]
  · rw [lineWordN_castSucc, freeEquivN_of]

/-- `Π̂_{0,n+2} ≃ₜ* F̂_{n+1}` maps `Iⱼ` to `⟨η(wⱼ)⟩‾`. -/
lemma map_inertia_completionCongr_freeEquivN_symm (j : Fin (n + 2)) :
    (Pi1.SurfaceGroup.inertia (g := 0) (r := n + 2) j).map
        ((completionCongr (freeEquivN n)).symm : Pi1.ProfiniteSurfaceGroup 0 (n + 2) →* FHat n) =
      basicInertia (lineWordN n j) := by
  rw [Pi1.SurfaceGroup.inertia, map_topologicalClosure_zpowers_of_compact
    ((completionCongr (freeEquivN n)).symm : Pi1.ProfiniteSurfaceGroup 0 (n + 2) →* FHat n)
    (completionCongr (freeEquivN n)).symm.continuous]
  congr 2
  apply (completionCongr (freeEquivN n)).injective
  change completionCongr (freeEquivN n) ((completionCongr (freeEquivN n)).symm _) = _
  rw [ContinuousMulEquiv.apply_symm_apply, completionCongr_apply, completionMap_eta]
  exact congrArg _ (freeEquivN_lineWordN j).symm

/-- **`⟨x_∞⟩‾ ⊆ F̂_{n+1}` is self-normalising** (it is commensurably terminal,
`Pi1.SurfaceGroup.commensurator_inertia`). -/
lemma mem_basicInertia_xInf_of_map_conj_eq {m : FHat n}
    (h : (basicInertia (xInf n)).map (MulAut.conj m).toMonoidHom =
      basicInertia (xInf n)) :
    m ∈ basicInertia (xInf n) := by
  set E := completionCongr (freeEquivN n)
  have hI : (basicInertia (xInf n)).map
      (E : FHat n →* Pi1.ProfiniteSurfaceGroup 0 (n + 2)) =
      Pi1.SurfaceGroup.inertia (g := 0) (r := n + 2) (Fin.last (n + 1)) := by
    rw [← lineWordN_last, ← map_inertia_completionCongr_freeEquivN_symm, Subgroup.map_map]
    convert Subgroup.map_id _
    ext x
    simp [E]
  have hE : (Pi1.SurfaceGroup.inertia (g := 0) (r := n + 2) (Fin.last (n + 1))).map
      (MulAut.conj (E m)).toMonoidHom = Pi1.SurfaceGroup.inertia (Fin.last (n + 1)) := by
    rw [← hI, Subgroup.map_map]
    conv_rhs => rw [← h, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hc : E m ∈ Subgroup.Commensurable.commensurator
      (Pi1.SurfaceGroup.inertia (g := 0) (r := n + 2) (Fin.last (n + 1))) := by
    rw [Subgroup.Commensurable.commensurator_mem_iff, Subgroup.pointwise_smul_def]
    have : (Pi1.SurfaceGroup.inertia (g := 0) (r := n + 2) (Fin.last (n + 1))).map
        (MulDistribMulAction.toMonoidEnd (ConjAct (Pi1.ProfiniteSurfaceGroup 0 (n + 2))) _
          (ConjAct.toConjAct (E m))) = Pi1.SurfaceGroup.inertia (Fin.last (n + 1)) := by
      rw [← hE]
      congr 1
    simpa only [this] using
      Subgroup.Commensurable.refl
        (Pi1.SurfaceGroup.inertia (g := 0) (r := n + 2) (Fin.last (n + 1)))
  rw [Pi1.SurfaceGroup.commensurator_inertia (g := 0) (r := n) (Fin.last (n + 1))] at hc
  rw [← hI] at hc
  obtain ⟨m', hm', hmn⟩ := hc
  rwa [← E.injective hmn]

end Free

/-! ### Places over the points of `S` -/

section Valuation

open Polynomial

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {W : ValuationSubring Ω}
  (hkW : ∀ c : k, algebraMap k Ω c ∈ W) {S : Finset k} {s : Ω}

include hkW in
/-- A place containing `s` and not `P_S(s)⁻¹` lies over a point `a ∈ S`: `v(s - a) < 1`. -/
lemma exists_mem_valuation_sub_lt_one (hs : s ∈ W) (hinv : (aeval s (polyS S))⁻¹ ∉ W) :
    ∃ a ∈ S, W.valuation (s - algebraMap k Ω a) < 1 := by
  have hlt := valuation_lt_one_of_inv_notMem (aeval_mem hkW hs (polyS S)) hinv
  rw [aeval_polyS, map_prod] at hlt
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have h1 : ∏ a ∈ S, W.valuation (s - algebraMap k Ω a) = 1 :=
    Finset.prod_eq_one fun a ha ↦
      le_antisymm ((W.valuation_le_one_iff _).2 (sub_mem hs (hkW a))) (h a ha)
  rw [h1] at hlt
  exact lt_irrefl _ hlt

include hkW in
/-- A place over a point `a ∈ S` contains `s` but not `P_S(s)⁻¹`. -/
lemma mem_and_inv_aeval_polyS_notMem (h0 : aeval s (polyS S) ≠ 0) {a : k} (ha : a ∈ S)
    (hlt : W.valuation (s - algebraMap k Ω a) < 1) :
    s ∈ W ∧ (aeval s (polyS S))⁻¹ ∉ W := by
  classical
  have h1 : s - algebraMap k Ω a ∈ W := (W.valuation_le_one_iff _).1 hlt.le
  have hs : s ∈ W := by simpa using add_mem h1 (hkW a)
  refine ⟨hs, ?_⟩
  have hprod : aeval s (polyS S) =
      (s - algebraMap k Ω a) * ∏ b ∈ S.erase a, (s - algebraMap k Ω b) := by
    rw [aeval_polyS]
    exact (Finset.mul_prod_erase S (fun b ↦ s - algebraMap k Ω b) ha).symm
  rw [hprod] at h0 ⊢
  exact inv_mul_notMem h1 (prod_mem fun b _ ↦ sub_mem hs (hkW b)) (Or.inl hlt) h0

omit [Field Ω] [Algebra k Ω] in
/-- For `s` transcendental and `a ∈ k`, there is a place `W ⊇ k` with `v(s - a) < 1`. -/
lemma exists_valuationSubring_sub_lt_one [Field Ω] [Algebra k Ω] {s : Ω}
    (hs : Transcendental k s) (a : k) :
    ∃ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) ∧
      W.valuation (s - algebraMap k Ω a) < 1 := by
  let e := Polynomial.algEquivOfTranscendental k s hs
  let ev : (Algebra.adjoin k {s}).toSubring →+* k :=
    (Polynomial.evalRingHom a).comp e.symm.toRingEquiv.toRingHom
  haveI : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨V, hRV, hnon, -⟩ := WeilCurves.FunctionField.exists_valuationSubring_of_prime
    (Algebra.adjoin k {s}).toSubring (RingHom.ker ev)
  refine ⟨V, fun c ↦ hRV (Subalgebra.algebraMap_mem _ c), ?_⟩
  have hmem : s - algebraMap k Ω a ∈ (Algebra.adjoin k {s}).toSubring :=
    Subring.sub_mem _ (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ a)
  have he : (⟨_, hmem⟩ : (Algebra.adjoin k {s}).toSubring) =
      e (Polynomial.X - Polynomial.C a) := by
    apply Subtype.ext
    simp [e, Polynomial.algEquivOfTranscendental_apply]
  have hker : (⟨_, hmem⟩ : (Algebra.adjoin k {s}).toSubring) ∈ RingHom.ker ev := by
    rw [RingHom.mem_ker, he]
    simp [ev]
  have hnu := hnon _ hker (hRV hmem)
  exact (V.valuation_lt_one_iff ⟨_, hRV hmem⟩).1 ((IsLocalRing.mem_maximalIdeal _).2 hnu)

end Valuation

/-! ### The main theorem -/

section Main

variable {k Ω : Type} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] (D : GaloisData k t)
  {X : Scheme.{0}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  (eL : X.functionField ≃+* D.L) (hH : D.H ≤ D.HL)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

set_option maxHeartbeats 1600000 in
-- one long proof assembling the cover, the line, the Schreier filling and the cusp count
include hk hτ in
/-- **`π₁ᵉᵗ(X ∖ D) ≅ Π̂_{g,r}` with the cuspidal inertia groups going to conjugates of the
`Iⱼ`** (`k` algebraically closed of characteristic `0`), assuming the corresponding statement
`hline` for the lines `ℙ¹ ∖ (S ∪ {∞})`, `S ⊆ k` finite nonempty. For `U ⊆ X` open with finite
nonempty complement, `g` the genus of `X` and `r = |X ∖ U|`, there is `Θ : π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}`
such that for every place `W ⊇ k` of `Ω` not centred on `U`, some conjugate of `cuspInertia U W`
is mapped by `Θ` onto some `Iⱼ = ⟨cⱼ⟩‾`. -/
theorem exists_continuousMulEquiv_cuspInertia_curve_of_line
    (hline : ∀ {s : Ω} [IsGalois (K₀ k s) Ω] (S : Finset k) {n : ℕ} (_ : S.card = n + 1)
      (hs : Transcendental k s),
      ∃ (σ : S ≃ Fin (n + 1)) (Θ : π₁ᵉᵗ(lineGenS S hs) ≃ₜ* Pi1.ProfiniteSurfaceGroup 0 (n + 2)),
        ∀ (c : Option S) (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) →
          W.valuation (cuspCoordS (c.map Subtype.val) s) < 1 →
          ∃ τ : π₁ᵉᵗ(lineGenS S hs),
            (lineInertiaS S hs W).map ((Θ : π₁ᵉᵗ(lineGenS S hs) →*
              Pi1.ProfiniteSurfaceGroup 0 (n + 2)).comp (MulAut.conj τ).toMonoidHom) =
              Pi1.SurfaceGroup.inertia (cuspIndex σ c))
    (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty) :
    ∃ Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
        Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X)),
      ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → ¬ IsCentredOn D X eL U W →
        ∃ (j : Fin (Nat.card ((U : Set X)ᶜ : Set X)))
          (σ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)),
          (cuspInertia D X eL hH U W).map ((Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →*
            Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X))).comp
              (MulAut.conj σ).toMonoidHom) =
            Pi1.SurfaceGroup.inertia j := by
  classical
  have hX := valuationRing_stalk_of_isCurveOver k X
  -- a finite map `f : X ⟶ ℙ¹` with `f⁻¹(∞) = X ∖ U`
  have hgenU : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  have hDgen : ∀ p ∈ (U : Set X)ᶜ, p ≠ genericPoint X := fun p hp h ↦ hp (h ▸ hgenU)
  obtain ⟨f, hf, hD, hfk⟩ :=
    CurvesJacobian.exists_finite_preimage_infty_eq k X (U : Set X)ᶜ hUfin hUne hDgen
  haveI := hf
  haveI := Belyi.isDominant_of_isFinite f
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hDgen _ ((hD _).1 h) rfl
  -- a finite set `S ⊆ k` such that `U' = f⁻¹(𝔸¹ ∖ S)` is finite étale over `𝔸¹ ∖ S`
  obtain ⟨S, hSne, hSet⟩ := exists_finset_isFiniteEtale_coverMapS f hη hfk
  haveI := hSet S subset_rfl
  haveI := nonempty_coverOpenS f S
  obtain ⟨n, hS⟩ : ∃ n, S.card = n + 1 := Nat.exists_eq_succ_of_ne_zero hSne.card_pos.ne'
  have hUeq : U = f ⁻¹ᵁ (lineι k).opensRange := by
    ext x
    change x ∈ (U : Set X) ↔ f.base x ∈ Set.range (lineι k).base
    rw [mem_range_lineι_iff, ne_eq, hD, Set.mem_compl_iff, not_not]
  have hle : coverOpenS f S ≤ U := by
    intro x hx
    rw [hUeq]
    change f.base x ∈ Set.range (lineι k).base
    obtain ⟨y, hy⟩ := hx
    rw [← hy, lineSι_eq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hU'fin : (coverOpenS f S : Set X)ᶜ.Finite := finite_compl_of_nonempty k X (coverOpenS f S)
  -- the coordinate `t_f`
  have htB : Transcendental k (coverT D eL f hη) :=
    transcendental_eL D X eL hk (transcendental_coordFun hη hfk)
  haveI : IsGalois (K₀ k (coverT D eL f hη)) Ω :=
    isGalois_K₀_of_mem (E := D.L) D.transcendental (coverT_mem D eL f hη) htB
  have hbase := genericL_coverMapS D eL f hη S hk hfk htB
  haveI : ConnectedSpace (coverOpenS f S) := connectedSpace_opens_of_isIntegral _
  set tB := coverT D eL f hη with htBdef
  have hP0 : Polynomial.aeval tB (polyS S) ≠ 0 := fun h ↦ htB ⟨polyS S, polyS_ne_zero S, h⟩
  -- centredness on `U` and `U'`
  have hcentU : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      (IsCentredOn D X eL U W ↔ tB ∈ W) := by
    intro W hkW
    haveI : Nonempty (f ⁻¹ᵁ (lineι k).opensRange) := hUeq ▸ inferInstance
    have hint := mem_range_germToFunctionField_iff k hX f (lineι k) (coordHom f hη)
      (spec_map_coordHom_comp_lineι hη).symm (coordFun f hη)
      (fun a ↦ by rw [coordHom_eq_aeval hη hfk]; exact Polynomial.aeval_mem_adjoin_singleton k _)
      ⟨Polynomial.X, rfl⟩
    subst hUeq
    constructor
    · rintro ⟨-, hW⟩
      obtain ⟨a, ha⟩ := (hint (coordFun f hη)).2
        (isIntegral_algebraMap (x := (⟨coordFun f hη, Algebra.self_mem_adjoin_singleton k _⟩ :
          Algebra.adjoin k {coordFun f hη})))
      have := hW a
      rwa [ha] at this
    · intro h
      exact ⟨hkW, fun a ↦ mem_of_isIntegral D X eL hk hkW h ((hint _).1 ⟨a, rfl⟩)⟩
  have hcentU' : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      (IsCentredOn D X eL (coverOpenS f S) W ↔
        tB ∈ W ∧ (Polynomial.aeval tB (polyS S))⁻¹ ∈ W) := fun W hkW ↦
    isCentredOn_coverOpenS_iff' D eL f hη S hk hfk htB hkW
  -- `π₁ᵉᵗ(𝔸¹ ∖ S) ≃ₜ* F̂_{n+1}`
  obtain ⟨σS, Θ₀, hΘ₀⟩ := hline S hS htB
  let Θ₂ : π₁ᵉᵗ(lineGenS S htB) ≃ₜ* FHat n := Θ₀.trans (completionCongr (freeEquivN n)).symm
  have hΘ₂ : ∀ (c : Option S) (W : ValuationSubring Ω), (∀ c : k, algebraMap k Ω c ∈ W) →
      W.valuation (cuspCoordS (c.map Subtype.val) tB) < 1 →
      ∃ τ' : FHat n, (lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (lineWordN n (cuspIndex σS c))).map (MulAut.conj τ').toMonoidHom := by
    intro c W hkW hWc
    obtain ⟨σ, hσ⟩ := hΘ₀ c W hkW hWc
    refine ⟨(completionCongr (freeEquivN n)).symm (Θ₀ σ)⁻¹, ?_⟩
    rw [← map_inertia_completionCongr_freeEquivN_symm, ← hσ, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [Θ₂, MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  have hΘfin : ∀ (a : S) (W : ValuationSubring Ω), (∀ c : k, algebraMap k Ω c ∈ W) →
      W.valuation (tB - algebraMap k Ω a) < 1 →
      ∃ τ' : FHat n, (lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (FreeGroup.of (σS a))).map (MulAut.conj τ').toMonoidHom := by
    intro a W hkW hWa
    obtain ⟨τ', hτ'⟩ := hΘ₂ (some a) W hkW hWa
    rw [show cuspIndex σS (some a) = (σS a).castSucc from rfl, lineWordN_castSucc] at hτ'
    exact ⟨τ', hτ'⟩
  have hΘinf : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → tB ∉ W →
      ∃ τ' : FHat n, (lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (xInf n)).map (MulAut.conj τ').toMonoidHom := by
    intro W hkW hW
    obtain ⟨τ', hτ'⟩ := hΘ₂ none W hkW (valuation_inv_lt_one_of_notMem hW)
    rw [show cuspIndex σS none = Fin.last (n + 1) from rfl, lineWordN_last] at hτ'
    exact ⟨τ', hτ'⟩
  -- the fibre of `U'` over the generic point of the line
  set ηU := specPoint D.L Ω ≫ genericL D X eL (coverOpenS f S) with hηU
  haveI hconn : IsConnected (coverObj (coverMapS f S)) :=
    (isConnected_iff_connectedSpace _).2 (inferInstanceAs (ConnectedSpace (coverOpenS f S)))
  let Fb := (FiniteEtale.fiber (lineGenS S htB)).obj (coverObj (coverMapS f S))
  let ω₀ : Fb := coverPt (coverMapS f S) ηU hbase
  letI iP : MulAction (FHat n) Fb :=
    MulAction.compHom Fb (Θ₂.symm : FHat n →* π₁ᵉᵗ(lineGenS S htB))
  letI iF : MulAction (FreeGroup (Fin (n + 1))) Fb :=
    MulAction.compHom Fb ((Θ₂.symm : FHat n →* π₁ᵉᵗ(lineGenS S htB)).comp (etaHom _))
  have hcompat : ∀ (g : FreeGroup (Fin (n + 1))) (y : Fb),
      g • y = etaFn (GrpCat.of (FreeGroup (Fin (n + 1)))) g • y := fun _ _ ↦ rfl
  have hopen : ∀ y : Fb, IsOpen (MulAction.stabilizer (FHat n) y : Set (FHat n)) := fun y ↦
    (stabilizer_isOpen (M := π₁ᵉᵗ(lineGenS S htB)) y).preimage Θ₂.symm.continuous
  have htrans : ∀ ω : Fb, ∃ g : FreeGroup (Fin (n + 1)), g • ω₀ = ω := by
    intro ω
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq π₁ᵉᵗ(lineGenS S htB) ω₀ ω
    have hV : IsOpen {τ' : FHat n | Θ₂.symm τ' • ω₀ = ω} := by
      have : {τ' : FHat n | Θ₂.symm τ' • ω₀ = ω} =
          (fun τ' ↦ (Θ₂ σ)⁻¹ * τ') ⁻¹' (MulAction.stabilizer (FHat n) ω₀ : Set (FHat n)) := by
        ext τ'
        simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          MulAction.mem_stabilizer_iff]
        change _ ↔ Θ₂.symm ((Θ₂ σ)⁻¹ * τ') • ω₀ = ω₀
        rw [map_mul, map_inv, ContinuousMulEquiv.symm_apply_apply, mul_smul, inv_smul_eq_iff, hσ]
      rw [this]
      exact (hopen ω₀).preimage (continuous_const.mul continuous_id)
    obtain ⟨g, hg⟩ := (denseRange (GrpCat.of (FreeGroup (Fin (n + 1))))).exists_mem_open hV
      ⟨Θ₂ σ, by simp [hσ]⟩
    exact ⟨g, hg⟩
  -- `π₁ᵉᵗ(U') ≃ₜ* Stab(ω₀) ⊆ F̂₂`
  have hmemS : ∀ x : MulAction.stabilizer π₁ᵉᵗ(lineGenS S htB) ω₀,
      Θ₂ (x : π₁ᵉᵗ(lineGenS S htB)) ∈ MulAction.stabilizer (FHat n) ω₀ := by
    intro x
    change Θ₂.symm (Θ₂ (x : π₁ᵉᵗ(lineGenS S htB))) • ω₀ = ω₀
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact x.2
  let eS : MulAction.stabilizer π₁ᵉᵗ(lineGenS S htB) ω₀ ≃ₜ* MulAction.stabilizer (FHat n) ω₀ :=
    { toFun x := ⟨Θ₂ (x : π₁ᵉᵗ(lineGenS S htB)), hmemS x⟩
      invFun y := ⟨Θ₂.symm y, y.2⟩
      left_inv x := Subtype.ext (Θ₂.symm_apply_apply (x : π₁ᵉᵗ(lineGenS S htB)))
      right_inv y := Subtype.ext (Θ₂.apply_symm_apply (y : FHat n))
      map_mul' x y := Subtype.ext (map_mul Θ₂ (x : π₁ᵉᵗ(lineGenS S htB)) y)
      continuous_toFun := (Θ₂.continuous.comp continuous_subtype_val).subtype_mk hmemS
      continuous_invFun :=
        (Θ₂.symm.continuous.comp continuous_subtype_val).subtype_mk fun y ↦ y.2 }
  let Φ : π₁ᵉᵗ(ηU) ≃ₜ* MulAction.stabilizer (FHat n) ω₀ :=
    (coverEquiv (coverMapS f S) ηU hbase).trans eS
  have hΦ : ∀ x, (Φ x : FHat n) = Θ₂ (fundamentalGroupMap (coverMapS f S) hbase x) := fun _ ↦ rfl
  have hst : (fundamentalGroupMap (coverMapS f S) hbase).toMonoidHom.range.map
      (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) = MulAction.stabilizer (FHat n) ω₀ := by
    rw [range_fundamentalGroupMap_eq_coverSubgroup]
    ext τ'
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      change Θ₂.symm (Θ₂ σ) • ω₀ = ω₀
      rw [ContinuousMulEquiv.symm_apply_apply]
      exact hσ
    · intro hτ'
      exact ⟨Θ₂.symm τ', hτ', by simp⟩
  have himage : ∀ W : ValuationSubring Ω, cuspImage Φ (cuspInertia D X eL hH (coverOpenS f S) W) =
      (lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) ⊓
        MulAction.stabilizer (FHat n) ω₀ := by
    intro W
    have h1 : cuspImage Φ (cuspInertia D X eL hH (coverOpenS f S) W) =
        ((cuspInertia D X eL hH (coverOpenS f S) W).map
          (fundamentalGroupMap (coverMapS f S) hbase).toMonoidHom).map
            (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) := by
      rw [cuspImage, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, map_cuspInertia_coverMapS D eL f hη hH S htB hbase hτ W,
      Subgroup.map_inf_eq _ _ _ Θ₂.injective, hst]
  have hconjmap : ∀ (T : Subgroup π₁ᵉᵗ(lineGenS S htB)) (g : π₁ᵉᵗ(lineGenS S htB)),
      (T.map (MulAut.conj g).toMonoidHom).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (T.map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n)).map (MulAut.conj (Θ₂ g)).toMonoidHom := by
    intro T g
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  -- the cusps of `U'` over the points of `S`
  let 𝒞 : Set (Subgroup π₁ᵉᵗ(ηU)) := {C | ∃ W : ValuationSubring Ω,
    (IsCentredOn D X eL U W ∧ ¬ IsCentredOn D X eL (coverOpenS f S) W) ∧
      C = cuspInertia D X eL hH (coverOpenS f S) W}
  have h𝒞 : ∀ C ∈ 𝒞, ∃ (a : Fin (n + 1)) (τ' : FHat n), cuspImage Φ C =
      (basicInertia (FreeGroup.of a)).map (MulAut.conj τ').toMonoidHom ⊓
        MulAction.stabilizer (FHat n) ω₀ := by
    rintro _ ⟨W, ⟨hWU, hWU'⟩, rfl⟩
    have hkW := hWU.1
    have h1 := (hcentU W hkW).1 hWU
    have h2 : (Polynomial.aeval tB (polyS S))⁻¹ ∉ W := fun h ↦ hWU' ((hcentU' W hkW).2 ⟨h1, h⟩)
    obtain ⟨a, ha, hlt⟩ := exists_mem_valuation_sub_lt_one hkW h1 h2
    obtain ⟨τ', hτ'⟩ := hΘfin ⟨a, ha⟩ W hkW hlt
    refine ⟨σS ⟨a, ha⟩, τ', ?_⟩
    rw [himage, hτ']
  have h𝒞' : ∀ (a : Fin (n + 1)) (τ' : FHat n), ∃ C ∈ 𝒞, cuspImage Φ C =
      (basicInertia (FreeGroup.of a)).map (MulAut.conj τ').toMonoidHom ⊓
        MulAction.stabilizer (FHat n) ω₀ := by
    intro a τ'
    obtain ⟨W₀, hkW₀, hW₀⟩ := exists_valuationSubring_sub_lt_one htB ((σS.symm a : S) : k)
    obtain ⟨τ₀, hτ₀⟩ := hΘfin (σS.symm a) W₀ hkW₀ hW₀
    rw [Equiv.apply_symm_apply] at hτ₀
    obtain ⟨σ, hσ⟩ := lineGaloisS_surjective S htB (Θ₂.symm (τ' * τ₀⁻¹))
    have hσk : ∀ x ∈ K₀ k tB, σ.symm x = x := fun x hx ↦ σ.symm.commutes ⟨x, hx⟩
    have hkW : ∀ c : k, algebraMap k Ω c ∈ W₀.comap (σ.symm : Ω →+* Ω) := by
      intro c
      rw [ValuationSubring.mem_comap]
      change σ.symm (algebraMap k Ω c) ∈ W₀
      rw [hσk _ (IntermediateField.algebraMap_mem _ c)]
      exact hkW₀ c
    have hmemK : tB - algebraMap k Ω ((σS.symm a : S) : k) ∈ K₀ k tB :=
      sub_mem (IntermediateField.mem_adjoin_simple_self k tB)
        (IntermediateField.algebraMap_mem _ _)
    have hWa : (W₀.comap (σ.symm : Ω →+* Ω)).valuation
        (tB - algebraMap k Ω ((σS.symm a : S) : k)) < 1 := by
      rw [valuation_comap_lt_one_iff]
      change W₀.valuation (σ.symm (tB - algebraMap k Ω ((σS.symm a : S) : k))) < 1
      rw [hσk _ hmemK]
      exact hW₀
    obtain ⟨h1, h2⟩ := mem_and_inv_aeval_polyS_notMem hkW hP0 (σS.symm a).2 hWa
    refine ⟨_, ⟨W₀.comap (σ.symm : Ω →+* Ω),
      ⟨(hcentU _ hkW).2 h1, fun h ↦ h2 ((hcentU' _ hkW).1 h).2⟩, rfl⟩, ?_⟩
    rw [himage, lineInertiaS_comap S htB W₀ σ, hconjmap, hτ₀, hσ,
      ContinuousMulEquiv.apply_symm_apply, Subgroup.map_map]
    have hc : (MulAut.conj (τ' * τ₀⁻¹)).toMonoidHom.comp (MulAut.conj τ₀).toMonoidHom =
        (MulAut.conj τ').toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hc]
  -- the group-theoretic filling
  obtain ⟨g, r, q, hqc, hqs, hqk, ⟨μ', hqcusp⟩, -⟩ :=
    exists_surfaceGroup_quotient hcompat hopen htrans Φ 𝒞 h𝒞 h𝒞'
  -- `π₁ᵉᵗ(U') ↠ π₁ᵉᵗ(U)`
  let p := fundamentalGroupMap (X.homOfLE hle) (specPoint_genericL_homOfLE D X eL hle)
  have hps : Function.Surjective p := by
    intro y
    obtain ⟨σ, rfl⟩ := (genericL_spec D X eL hk hH hτ U hUfin).2 y
    exact ⟨_, fundamentalGroupMap_genericL D X eL hH hle σ⟩
  have hunion : (⋃ C ∈ 𝒞, (C : Set π₁ᵉᵗ(ηU))) = ⋃ (W : ValuationSubring Ω)
      (_ : IsCentredOn D X eL U W ∧ ¬ IsCentredOn D X eL (coverOpenS f S) W),
        (cuspInertia D X eL hH (coverOpenS f S) W : Set π₁ᵉᵗ(ηU)) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨C, ⟨W, hW, rfl⟩, hx⟩
      exact ⟨W, hW, hx⟩
    · rintro ⟨W, hW, hx⟩
      exact ⟨_, ⟨W, hW, rfl⟩, hx⟩
  have hker : p.toMonoidHom.ker = q.ker := by
    rw [ker_fundamentalGroupMap_homOfLE_eq_cuspInertia D X eL hH hk hτ hU'fin hUfin hle, hqk,
      hunion]
  obtain ⟨E, hE⟩ := exists_continuousMulEquiv_of_ker_eq p.toMonoidHom q p.continuous hqc hps hqs
    hker
  -- the cusps over `∞` correspond to the `⟨x_∞⟩`-orbits on the fibre
  have horb : ∀ z ∈ basicInertia (xInf n), ∀ y : Fb,
      (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (xInf n)) Fb)
        (z • y)) = Quotient.mk _ y := by
    intro z hz y
    let S : Set (FHat n) := {z | (Quotient.mk (MulAction.orbitRel
      (Subgroup.zpowers (xInf n)) Fb) (z • y)) = Quotient.mk _ y}
    have hS : IsClosed S := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro z₀ hz₀
      refine ⟨(fun z ↦ z₀⁻¹ * z) ⁻¹' (MulAction.stabilizer (FHat n) y : Set (FHat n)), ?_,
        (hopen y).preimage (continuous_const.mul continuous_id), ?_⟩
      · intro z hzs hzS
        apply hz₀
        have h1 : z • y = z₀ • y := by
          have h2 : (z₀⁻¹ * z) • y = y := hzs
          rwa [mul_smul, inv_smul_eq_iff] at h2
        change Quotient.mk _ (z₀ • y) = _
        rw [← h1]
        exact hzS
      · change (z₀⁻¹ * z₀) • y = y
        rw [inv_mul_cancel, one_smul]
    refine closure_minimal (fun z' hz' ↦ ?_) hS hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
    apply Quotient.sound
    refine ⟨⟨xInf n ^ m, Subgroup.zpow_mem_zpowers _ m⟩, ?_⟩
    change xInf n ^ m • y = _
    rw [hcompat]
    change etaHom _ (xInf n ^ m) • y =
      (etaHom (FreeGroup (Fin (n + 1))) (xInf n)) ^ m • y
    rw [map_zpow]
  have hinfW : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      ¬ IsCentredOn D X eL U W → tB ∉ W := fun W hkW hWU h ↦ hWU ((hcentU W hkW).2 h)
  have hconjL : ∀ (W : ValuationSubring Ω) (ρ : Ω ≃ₐ[K₀ k tB] Ω),
      (lineInertiaS S htB (W.comap (ρ.symm : Ω →+* Ω))).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        ((lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n)).map
          (MulAut.conj (Θ₂ (lineGaloisS S htB ρ))).toMonoidHom := by
    intro W ρ
    rw [lineInertiaS_comap S htB W ρ, hconjmap]
  have hmove : ∀ (W : ValuationSubring Ω) (ρ : Ω ≃ₐ[K₀ k tB] Ω) (τ τ' : FHat n),
      (lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (xInf n)).map (MulAut.conj τ).toMonoidHom →
      (lineInertiaS S htB (W.comap (ρ.symm : Ω →+* Ω))).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (xInf n)).map (MulAut.conj τ').toMonoidHom →
      (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (xInf n)) Fb)
        (τ'⁻¹ • ω₀)) = Quotient.mk _ (τ⁻¹ • ((Θ₂ (lineGaloisS S htB ρ))⁻¹ • ω₀)) := by
    intro W ρ τ τ' hτ hτ'
    have hn : τ'⁻¹ * (Θ₂ (lineGaloisS S htB ρ) * τ) ∈ basicInertia (xInf n) := by
      apply mem_basicInertia_xInf_of_map_conj_eq
      rw [← map_conj_eq_iff, ← map_conj_map_conj, ← hτ, ← hconjL, hτ']
    have he : τ'⁻¹ = (τ'⁻¹ * (Θ₂ (lineGaloisS S htB ρ) * τ)) * τ⁻¹ *
        (Θ₂ (lineGaloisS S htB ρ))⁻¹ := by group
    rw [he, mul_assoc, mul_smul, horb _ hn, mul_smul]
  have hstab : ∀ ρ : Ω ≃ₐ[K₀ k tB] Ω, (Θ₂ (lineGaloisS S htB ρ))⁻¹ • ω₀ = ω₀ →
      ∀ x : D.L, ρ (x : Ω) = x := by
    intro ρ h x
    refine apply_eq_of_lineGaloisS_mem_range D eL f hη S htB hbase ρ ?_ x
    rw [range_fundamentalGroupMap_eq_coverSubgroup]
    change lineGaloisS S htB ρ • ω₀ = ω₀
    have h' : Θ₂.symm (Θ₂ (lineGaloisS S htB ρ))⁻¹ • ω₀ = ω₀ := h
    rw [map_inv, ContinuousMulEquiv.symm_apply_apply, inv_smul_eq_iff] at h'
    exact h'.symm
  have hstab' : ∀ ρ : Ω ≃ₐ[K₀ k tB] Ω, (∀ x : D.L, ρ (x : Ω) = x) →
      (Θ₂ (lineGaloisS S htB ρ))⁻¹ • ω₀ = ω₀ := by
    intro ρ hρ
    have htL : t ∈ D.L := by
      have := (eL τ).2
      rwa [hτ] at this
    let σ : Ω ≃ₐ[K₀ k t] Ω := AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv)
      (fun c ↦ hρ ⟨_, K₀_le_of_mem htL c.2⟩)
    have hσHL : σ ∈ D.HL := by
      rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hρ ⟨x, hx⟩
    have hg : lineGaloisS S htB ρ ∈
        (fundamentalGroupMap (coverMapS f S) hbase).toMonoidHom.range := by
      refine ⟨D.chartHom hH (genericL D X eL (coverOpenS f S)) ⟨σ, D.le hσHL⟩, ?_⟩
      change fundamentalGroupMap (coverMapS f S) hbase _ = _
      rw [fundamentalGroupMap_coverMapS_chartHom D eL f hη hH S htB hbase]
      exact congrArg _ (AlgEquiv.ext fun _ ↦ rfl)
    rw [range_fundamentalGroupMap_eq_coverSubgroup] at hg
    have hg' : lineGaloisS S htB ρ • ω₀ = ω₀ := hg
    change Θ₂.symm (Θ₂ (lineGaloisS S htB ρ))⁻¹ • ω₀ = ω₀
    rw [map_inv, ContinuousMulEquiv.symm_apply_apply, inv_smul_eq_iff]
    exact hg'.symm
  have hclass : ∀ (W W' : ValuationSubring Ω) (τ τ' : FHat n),
      (∀ c : k, algebraMap k Ω c ∈ W) → (∀ c : k, algebraMap k Ω c ∈ W') → tB ∉ W → tB ∉ W' →
      (lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (xInf n)).map (MulAut.conj τ).toMonoidHom →
      (lineInertiaS S htB W').map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (xInf n)).map (MulAut.conj τ').toMonoidHom →
      ((Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (xInf n)) Fb)
        (τ⁻¹ • ω₀)) = Quotient.mk _ (τ'⁻¹ • ω₀) ↔
        W.comap (algebraMap D.L Ω) = W'.comap (algebraMap D.L Ω)) := by
    intro W W' τ τ' hkW hkW' hW hW' hτ hτ'
    constructor
    · intro h
      obtain ⟨ρ, rfl⟩ := exists_algEquiv_comap_eq W W' (comap_K₀_eq_of_notMem hkW hkW' hW hW')
      rw [hmove W ρ τ τ' hτ hτ'] at h
      obtain ⟨⟨x, hx⟩, hxe⟩ := Quotient.exact h.symm
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hxe' : etaFn (GrpCat.of (FreeGroup (Fin (n + 1))))
          (xInf n ^ m) • (τ⁻¹ • ω₀) =
          τ⁻¹ • ((Θ₂ (lineGaloisS S htB ρ))⁻¹ • ω₀) := by
        rw [← hcompat]
        exact hxe
      -- `ι' = τ η(x_∞)^m τ⁻¹ ∈ Θ₂(I_W)`
      have hι' : τ * etaFn (GrpCat.of (FreeGroup (Fin (n + 1))))
          (xInf n ^ m) * τ⁻¹ ∈
          (lineInertiaS S htB W).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) := by
        rw [hτ]
        refine ⟨_, ?_, rfl⟩
        change etaHom _ (xInf n ^ m) ∈ basicInertia (xInf n)
        rw [map_zpow]
        exact Subgroup.zpow_mem _ (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)) m
      obtain ⟨ι, hι, hιe⟩ := hι'
      rw [lineInertiaS_eq_map] at hι
      obtain ⟨i, hi, rfl⟩ := hι
      have hιe' : Θ₂ (lineGaloisS S htB i) = τ * etaFn (GrpCat.of (FreeGroup (Fin (n + 1))))
          (xInf n ^ m) * τ⁻¹ := hιe
      have hfix := hstab (ρ * i) (by
        rw [map_mul, map_mul, hιe', inv_smul_eq_iff, mul_smul, mul_smul, mul_smul, hxe',
          smul_inv_smul, smul_inv_smul])
      ext z
      simp only [ValuationSubring.mem_comap]
      change (z : Ω) ∈ W ↔ ρ.symm (z : Ω) ∈ W
      have hz : ρ.symm (z : Ω) = i z := by
        rw [AlgEquiv.symm_apply_eq]
        exact (hfix z).symm
      rw [hz]
      have hiW := comap_eq_of_mem_inertia (W := W) hi
      exact (SetLike.ext_iff.1 hiW (z : Ω)).symm
    · intro h
      haveI : IsGalois D.L Ω := IsGalois.tower_top_of_isGalois (K₀ k t) D.L Ω
      obtain ⟨κ, hκ⟩ := exists_algEquiv_comap_eq W W' h
      let ρ : Ω ≃ₐ[K₀ k tB] Ω := AlgEquiv.ofRingEquiv (f := κ.toRingEquiv)
        (fun c ↦ κ.commutes ⟨_, K₀_le_of_mem (coverT_mem D eL f hη) c.2⟩)
      have hW'ρ : W' = W.comap (ρ.symm : Ω →+* Ω) := by
        rw [hκ]
        rfl
      subst hW'ρ
      rw [hmove W ρ τ τ' hτ hτ', hstab' ρ (fun x ↦ κ.commutes x)]
  -- one place over each cusp
  haveI := isSeparated_of_over k X
  have hWex : ∀ y : ((U : Set X)ᶜ : Set X), ∃ W : ValuationSubring Ω,
      comapK D X eL hk W = stalkVS k y.1 ∧ (∀ c : k, algebraMap k Ω c ∈ W) ∧
        ¬ IsCentredOn D X eL U W := by
    intro y
    obtain ⟨W, h1, h2, h3⟩ := exists_isCentredOn_not_isCentredOn D X eL hk (V := ⊤) hUfin
      (Set.mem_univ y.1) y.2
    exact ⟨W, h1, h2.1, h3⟩
  choose Wy hWy using hWex
  have hτex : ∀ y : ((U : Set X)ᶜ : Set X), ∃ τ' : FHat n,
      (lineInertiaS S htB (Wy y)).map (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) =
        (basicInertia (xInf n)).map (MulAut.conj τ').toMonoidHom := fun y ↦
    hΘinf (Wy y) (hWy y).2.1 (hinfW _ (hWy y).2.1 (hWy y).2.2)
  choose τy hτy using hτex
  let J : ((U : Set X)ᶜ : Set X) →
      MulAction.orbitRel.Quotient (Subgroup.zpowers (xInf n)) Fb :=
    fun y ↦ Quotient.mk _ ((τy y)⁻¹ • ω₀)
  have hJinj : Function.Injective J := by
    intro y y' h
    have h1 := (hclass _ _ _ _ (hWy y).2.1 (hWy y').2.1 (hinfW _ (hWy y).2.1 (hWy y).2.2)
      (hinfW _ (hWy y').2.1 (hWy y').2.2) (hτy y) (hτy y')).1 h
    have h2 : comapK D X eL hk (Wy y) = comapK D X eL hk (Wy y') := by
      ext z
      exact SetLike.ext_iff.1 h1 (eL z)
    rw [(hWy y).1, (hWy y').1] at h2
    exact Subtype.ext (stalkValuationSubring_injective hX h2)
  have hJsurj : Function.Surjective J := by
    intro c
    obtain ⟨ω, rfl⟩ := Quotient.exists_rep c
    obtain ⟨y₀⟩ : Nonempty ((U : Set X)ᶜ : Set X) := hUne.to_subtype
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq π₁ᵉᵗ(lineGenS S htB) ω₀ (Θ₂.symm (τy y₀) • ω)
    obtain ⟨ρ, hρ⟩ := lineGaloisS_surjective S htB σ⁻¹
    have hρk : ∀ x ∈ K₀ k tB, ρ.symm x = x := fun x hx ↦ ρ.symm.commutes ⟨x, hx⟩
    have hkW : ∀ c : k, algebraMap k Ω c ∈ (Wy y₀).comap (ρ.symm : Ω →+* Ω) := by
      intro c
      rw [ValuationSubring.mem_comap]
      change ρ.symm (algebraMap k Ω c) ∈ Wy y₀
      rw [hρk _ (IntermediateField.algebraMap_mem _ c)]
      exact (hWy y₀).2.1 c
    have hWU : ¬ IsCentredOn D X eL U ((Wy y₀).comap (ρ.symm : Ω →+* Ω)) := by
      rw [hcentU _ hkW, ValuationSubring.mem_comap]
      change ρ.symm tB ∉ Wy y₀
      rw [hρk _ (IntermediateField.mem_adjoin_simple_self k tB)]
      exact hinfW _ (hWy y₀).2.1 (hWy y₀).2.2
    obtain ⟨y, hyU, hy⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW hWU
    refine ⟨⟨y, hyU⟩, ?_⟩
    have hτW : (lineInertiaS S htB ((Wy y₀).comap (ρ.symm : Ω →+* Ω))).map
        (Θ₂ : π₁ᵉᵗ(lineGenS S htB) →* FHat n) = (basicInertia (xInf n)).map
          (MulAut.conj (Θ₂ (lineGaloisS S htB ρ) * τy y₀)).toMonoidHom := by
      rw [hconjL, hτy y₀, map_conj_map_conj]
    have hsame : (Wy ⟨y, hyU⟩).comap (algebraMap D.L Ω) =
        ((Wy y₀).comap (ρ.symm : Ω →+* Ω)).comap (algebraMap D.L Ω) :=
      comap_algebraMap_eq_of_comapK_eq D X eL hk (by rw [(hWy _).1, hy])
    have heq := (hclass _ _ _ _ (hWy _).2.1 hkW (hinfW _ (hWy _).2.1 (hWy _).2.2)
      (hinfW _ hkW hWU) (hτy ⟨y, hyU⟩) hτW).2 hsame
    change Quotient.mk _ _ = _
    rw [heq]
    congr 1
    rw [hρ, mul_inv_rev, mul_smul]
    change Θ₂.symm (τy y₀)⁻¹ • (Θ₂.symm (Θ₂ σ⁻¹)⁻¹ • ω₀) = ω
    rw [map_inv Θ₂.symm (Θ₂ σ⁻¹), ContinuousMulEquiv.symm_apply_apply, inv_inv, hσ, map_inv,
      inv_smul_smul]
  have hr : r = Nat.card ((U : Set X)ᶜ : Set X) := by
    rw [Nat.card_congr (Equiv.ofBijective J ⟨hJinj, hJsurj⟩), Nat.card_congr μ', Nat.card_fin]
  -- the genus, by counting characters of order `2`
  obtain ⟨e₀⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup₀_of_isAlgClosed (k := k) U
    hUfin hUne (specPoint D.L Ω ≫ genericL D X eL U)
  obtain ⟨R, hR⟩ : ∃ R, Nat.card ((U : Set X)ᶜ : Set X) = R + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by
      haveI := hUfin.to_subtype
      exact (Nat.card_pos_iff.2 ⟨hUne.to_subtype, inferInstance⟩).ne')
  have hnum := numChar2_congr (E.symm.trans e₀)
  have hrR : r = R + 1 := hr.trans hR
  have hcnt : ∀ g' : ℕ, numChar2 (Pi1.ProfiniteSurfaceGroup g' (R + 1)) = 2 ^ (g' + g' + R) := by
    intro g'
    rw [numChar2_congr (completionCongr (MulEquiv.ulift (α := Pi1.SurfaceGroup g' (R + 1)))).symm,
      numChar2_surfaceCompletion]
  have h1 : numChar2 (Pi1.ProfiniteSurfaceGroup g r) = 2 ^ (g + g + R) := by
    rw [hrR]
    exact hcnt g
  have h2 : numChar2 (Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
      (Nat.card ((U : Set X)ᶜ : Set X))) =
      2 ^ ((curveGenus k X).toNat + (curveGenus k X).toNat + R) := by
    rw [hR]
    exact hcnt _
  rw [h1, h2] at hnum
  have hg : g = (curveGenus k X).toNat := by
    have := Nat.pow_right_injective (le_refl 2) hnum
    omega
  subst hg
  subst hr
  refine ⟨E, fun W hkW hWU ↦ ?_⟩
  obtain ⟨τ', hτ'⟩ := hΘinf W hkW fun h ↦ hWU ((hcentU W hkW).2 h)
  obtain ⟨κ, hjκ⟩ := hqcusp (cuspInertia D X eL hH (coverOpenS f S) W) τ' (by
    rw [himage, hτ'])
  have hmapU : (cuspInertia D X eL hH (coverOpenS f S) W).map p.toMonoidHom =
      cuspInertia D X eL hH U W := by
    rw [cuspInertia, cuspInertia, MonoidHom.map_closure, ← Set.image_comp]
    congr 1
    ext y
    simp only [Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, (fundamentalGroupMap_genericL D X eL hH hle σ).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, fundamentalGroupMap_genericL D X eL hH hle σ⟩
  have hEq : (cuspInertia D X eL hH U W).map
      (E : _ →* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
        (Nat.card ((U : Set X)ᶜ : Set X))) =
      (Pi1.SurfaceGroup.inertia (μ' (Quotient.mk _ (τ'⁻¹ • ω₀)))).map
        (MulAut.conj κ).toMonoidHom := by
    rw [← hmapU, Subgroup.map_map, ← hjκ]
    congr 1
    ext x
    exact hE x
  refine ⟨μ' (Quotient.mk _ (τ'⁻¹ • ω₀)), E.symm κ⁻¹, ?_⟩
  have h1 : ((E : _ →* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
        (Nat.card ((U : Set X)ᶜ : Set X))).comp (MulAut.conj (E.symm κ⁻¹)).toMonoidHom) =
      (MulAut.conj κ⁻¹).toMonoidHom.comp (E : _ →* Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
        (Nat.card ((U : Set X)ᶜ : Set X))) := by
    ext x
    change E ((E.symm κ⁻¹) * x * (E.symm κ⁻¹)⁻¹) = κ⁻¹ * E x * κ⁻¹⁻¹
    simp only [map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
  have h2 : (MulAut.conj κ⁻¹).toMonoidHom.comp (MulAut.conj κ).toMonoidHom =
      MonoidHom.id (Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat
        (Nat.card ((U : Set X)ᶜ : Set X))) := by
    ext x
    change κ⁻¹ * (κ * x * κ⁻¹) * κ⁻¹⁻¹ = x
    group
  rw [h1, ← Subgroup.map_map, hEq, Subgroup.map_map, h2, Subgroup.map_id]

include hk hτ in
/-- **`π₁ᵉᵗ(X ∖ D) ≅ Π̂_{g,r}` with the cuspidal inertia groups going to conjugates of the
`Iⱼ`, for every algebraically closed field `k` of characteristic `0`.** For `U ⊆ X` open with
finite nonempty complement, `g` the genus of `X` and `r = |X ∖ U|`, there is
`Θ : π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}` such that for every place `W ⊇ k` of `Ω` not centred on `U`, some
conjugate of `cuspInertia U W` is mapped by `Θ` onto some `Iⱼ = ⟨cⱼ⟩‾`. The input on the line
`ℙ¹ ∖ (S ∪ {∞})` is `CurvesJacobian.Cusp.exists_continuousMulEquiv_lineInertiaS`. -/
theorem exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty) :
    ∃ Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
        Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X)),
      ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → ¬ IsCentredOn D X eL U W →
        ∃ (j : Fin (Nat.card ((U : Set X)ᶜ : Set X)))
          (σ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)),
          (cuspInertia D X eL hH U W).map ((Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →*
            Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X))).comp
              (MulAut.conj σ).toMonoidHom) =
            Pi1.SurfaceGroup.inertia j :=
  exists_continuousMulEquiv_cuspInertia_curve_of_line D eL hH hk hτ
    (fun S _ hS hs ↦ exists_continuousMulEquiv_lineInertiaS S hS hs) U hUfin hUne

end Main

end CurvesJacobian.Cusp
