/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiCover
import CurvesJacobian.Cusp.CuspInertiaFacts
import CurvesJacobian.Cusp.CuspSchreier
import CurvesJacobian.Cusp.CuspTerminal
import CurvesJacobian.Cusp.Inertia
import CurvesJacobian.Cusp.LineInertiaIso
import CurvesJacobian.Cusp.SingleCusp
import CurvesJacobian.Galois.AbelianPi1
import CurvesJacobian.Galois.AlgClosedSurfaceGroup
import CurvesJacobian.Galois.BelyiInfty
import CurvesJacobian.Galois.CurveCharts
import CurvesJacobian.Scheme.CurvePlaces
import CurvesJacobian.Scheme.ValuationPoints
import WeilCurves.ConstantExtension.Split

/-!
# `π₁ᵉᵗ(X ∖ D) ≅ Π̂_{g,r}` compatibly with the cuspidal inertia groups (curves over `ℚ̄`)

Let `k` be algebraically closed of characteristic `0` and algebraic over `ℚ` (e.g. `ℚ̄`), `X` a
curve over `k` with Galois model `(D, eL)` (`H = H_L`), and `U ⊆ X` open with finite nonempty
complement.

**Main result** (`CurvesJacobian.Cusp.exists_continuousMulEquiv_cuspInertia_curve`): for `g` the
genus of `X` and `r = |X ∖ U|` there is `Θ : π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}` mapping every cuspidal inertia
group
`CurvesJacobian.Cusp.cuspInertia D X eL hH U W` (`W ⊇ k` a place of `Ω` not centred on `U`) onto a
conjugate of a cuspidal inertia group `Iⱼ = ⟨cⱼ⟩‾`.

Proof: a Belyi map `f : X → ℙ¹` with `f⁻¹(∞) = X ∖ U`
(`CurvesJacobian.exists_isBelyiMap_preimage_infty_eq`)
makes `U' = f⁻¹(ℙ¹ ∖ {0, 1, ∞}) ⊆ U` finite étale over `ℙ¹ ∖ {0, 1, ∞}`, so `π₁ᵉᵗ(U')` is an open
subgroup `O` of `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≅ Π̂_{0,3} ≅ F̂₂` (`CurvesJacobian.Cusp.coverEquiv`), and the
cuspidal inertia groups of `U'` are the intersections with `O` of the inertia groups of the line
(`CurvesJacobian.Cusp.map_cuspInertia_cuspCover`), which are conjugates of `⟨x₀⟩‾`, `⟨x₁⟩‾`,
`⟨x_∞⟩‾` (`CurvesJacobian.Cusp.exists_continuousMulEquiv_lineInertia`). Filling in the points of
`U` over `0, 1` (`CurvesJacobian.Cusp.ker_fundamentalGroupMap_homOfLE_eq_cuspInertia`) is the
group-theoretic filling `CurvesJacobian.Cusp.exists_surfaceGroup_quotient` (pi1's Schreier normal
form), which sends the loops around the points over `∞` to conjugates of the cusps.

The number of cusps of the Schreier normal form is the number of `⟨x_∞⟩`-orbits on the fibre of
`U'` over the generic point; these orbits correspond to the points of `X ∖ U`: the class of a
place `W` over `∞` is the orbit `τ_W⁻¹ ω₀` for `Θ(I_W) = τ_W ⟨x_∞⟩‾ τ_W⁻¹`, and two places over `∞`
(Galois conjugate over `k(t_f)`, as `k(t)` has a single place at `∞`,
`CurvesJacobian.Cusp.comap_K₀_eq_of_notMem`) give the same orbit iff they restrict to the same
place of `K(X)` (`⟨x_∞⟩‾` is self-normalising,
`CurvesJacobian.Cusp.mem_basicInertia_of_map_conj_eq`).
The genus is then read off from the number of characters of order `2` (comparison with the
abstract isomorphism `etaleFundamentalGroup_equiv_profiniteSurfaceGroup₀_of_isAlgClosed`).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### `F(x₀, x₁) ≅ Π_{0,3}` -/

/-- The generators `c₀, c₁` of `Π_{0,3}` as `Fin 2`. -/
def genFinTwo : Pi1.SurfaceGen 0 2 ≃ Fin 2 where
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

/-- `F(x₀, x₁) ≃* Π_{0,3}`, `xₐ ↦ cₐ` (so `x_∞ = (x₀ x₁)⁻¹ ↦ c₂`). -/
def freeTwoEquiv : FreeGroup (Fin (1 + 1)) ≃* Pi1.SurfaceGroup 0 3 :=
  ((Pi1.SurfaceGroup.freeEquiv (g := 0) (r := 2)).trans
    (FreeGroup.freeGroupCongr genFinTwo)).symm

/-- The words `x₀`, `x₁`, `x_∞ = (x₀ x₁)⁻¹`. -/
def lineWord : Fin 3 → FreeGroup (Fin (1 + 1)) :=
  ![FreeGroup.of 0, FreeGroup.of 1, Pi1.ReidemeisterSchreier.xInf 1]

lemma freeTwoEquiv_of (a : Fin 2) :
    freeTwoEquiv (FreeGroup.of a) = Pi1.SurfaceGroup.cusp (g := 0) (r := 3) a.castSucc := by
  rw [freeTwoEquiv, MulEquiv.symm_apply_eq]
  change FreeGroup.of a = FreeGroup.freeGroupCongr genFinTwo
    (Pi1.SurfaceGroup.freeEquiv (Pi1.SurfaceGroup.cusp (g := 0) (r := 2 + 1) a.castSucc))
  rw [Pi1.SurfaceGroup.freeEquiv_cusp_castSucc, FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
  rfl

lemma freeTwoEquiv_lineWord (j : Fin 3) :
    freeTwoEquiv (lineWord j) = Pi1.SurfaceGroup.cusp (g := 0) (r := 3) j := by
  fin_cases j
  · exact freeTwoEquiv_of 0
  · exact freeTwoEquiv_of 1
  · have hx : Pi1.ReidemeisterSchreier.xInf 1 = (FreeGroup.of 0 * FreeGroup.of 1)⁻¹ := by
      rw [Pi1.ReidemeisterSchreier.xInf]
      simp [List.ofFn_succ, Fin.succ_zero_eq_one]
    change freeTwoEquiv (Pi1.ReidemeisterSchreier.xInf 1) = Pi1.SurfaceGroup.cusp (2 : Fin 3)
    rw [hx, map_inv, map_mul, freeTwoEquiv_of 0, freeTwoEquiv_of 1, cusp_two_eq]
    rfl

/-- `Π̂_{0,3} ≃ₜ* F̂₂` maps `Iⱼ` to `⟨η(wⱼ)⟩‾`. -/
lemma map_inertia_completionCongr_symm (j : Fin 3) :
    (Pi1.SurfaceGroup.inertia (g := 0) (r := 3) j).map
        ((completionCongr freeTwoEquiv).symm : Pi1.ProfiniteSurfaceGroup 0 3 →* FHat 1) =
      basicInertia (lineWord j) := by
  rw [Pi1.SurfaceGroup.inertia, map_topologicalClosure_zpowers_of_compact
    ((completionCongr freeTwoEquiv).symm : Pi1.ProfiniteSurfaceGroup 0 3 →* FHat 1)
    (completionCongr freeTwoEquiv).symm.continuous]
  congr 2
  apply (completionCongr freeTwoEquiv).injective
  change completionCongr freeTwoEquiv ((completionCongr freeTwoEquiv).symm _) = _
  rw [ContinuousMulEquiv.apply_symm_apply, completionCongr_apply, completionMap_eta]
  exact congrArg _ (freeTwoEquiv_lineWord j).symm

lemma map_conj_map_conj {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

lemma map_conj_eq_iff {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj a).toMonoidHom = H.map (MulAut.conj b).toMonoidHom ↔
      H.map (MulAut.conj (b⁻¹ * a)).toMonoidHom = H := by
  constructor
  · intro h
    rw [← map_conj_map_conj, h, map_conj_map_conj, inv_mul_cancel]
    convert Subgroup.map_id H
    ext x
    simp
  · intro h
    conv_rhs => rw [← h]
    rw [map_conj_map_conj, mul_inv_cancel_left]

/-- **`⟨x_∞⟩‾ ⊆ F̂₂` is self-normalising** (it is commensurably terminal,
`Pi1.SurfaceGroup.commensurator_inertia`). -/
lemma mem_basicInertia_of_map_conj_eq {n : FHat 1}
    (h : (basicInertia (lineWord 2)).map (MulAut.conj n).toMonoidHom = basicInertia (lineWord 2)) :
    n ∈ basicInertia (lineWord 2) := by
  set E := completionCongr freeTwoEquiv
  have hI : (basicInertia (lineWord 2)).map (E : FHat 1 →* Pi1.ProfiniteSurfaceGroup 0 3) =
      Pi1.SurfaceGroup.inertia (g := 0) (r := 3) 2 := by
    rw [← map_inertia_completionCongr_symm, Subgroup.map_map]
    convert Subgroup.map_id _
    ext x
    simp [E]
  have hE : (Pi1.SurfaceGroup.inertia (g := 0) (r := 3) 2).map
      (MulAut.conj (E n)).toMonoidHom = Pi1.SurfaceGroup.inertia 2 := by
    rw [← hI, Subgroup.map_map]
    conv_rhs => rw [← h, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hc : E n ∈ Subgroup.Commensurable.commensurator
      (Pi1.SurfaceGroup.inertia (g := 0) (r := 1 + 2) 2) := by
    rw [Subgroup.Commensurable.commensurator_mem_iff, Subgroup.pointwise_smul_def]
    have : (Pi1.SurfaceGroup.inertia (g := 0) (r := 3) 2).map
        (MulDistribMulAction.toMonoidEnd (ConjAct (Pi1.ProfiniteSurfaceGroup 0 3)) _
          (ConjAct.toConjAct (E n))) = Pi1.SurfaceGroup.inertia 2 := by
      rw [← hE]
      congr 1
    simpa only [this] using
      Subgroup.Commensurable.refl (Pi1.SurfaceGroup.inertia (g := 0) (r := 3) 2)
  rw [Pi1.SurfaceGroup.commensurator_inertia (g := 0) (r := 1) 2] at hc
  change E n ∈ Pi1.SurfaceGroup.inertia (g := 0) (r := 3) 2 at hc
  rw [← hI] at hc
  obtain ⟨m, hm, hmn⟩ := hc
  rwa [← E.injective hmn]

/-! ### The cuspidal inertia groups of `U'` inside `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞})` -/

section Cover

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  {X : Scheme.{0}} [X.Over (Spec (.of k))] [IsIntegral X] (eL : X.functionField ≃+* D.L)
  (f : X ⟶ P1 k) [Nonempty (cuspOpen f)] (hη : f.base (genericPoint X) ≠ P1.infty k)
  [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] (hH : D.H ≤ D.HL)
  (ht : Transcendental k (belyiT D eL f hη)) [IsGalois (K₀ k (belyiT D eL f hη)) Ω]
  (hbase : (specPoint D.L Ω ≫ genericL D X eL (cuspOpen f)) ≫ cuspCover f = lineGen ht)
  [IsFiniteEtale (cuspCover f)] {τ₀ : X.functionField} (hτ₀ : ((eL τ₀ : D.L) : Ω) = t)

omit [X.Over (Spec (.of k))] in
include hbase hτ₀ in
/-- **The cuspidal inertia groups of `U'` in `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞})`**: `π₁ᵉᵗ(U') → π₁ᵉᵗ(line)`
maps `cuspInertia U' W` onto the intersection of the inertia group of `W` with its image. -/
theorem map_cuspInertia_cuspCover (W : ValuationSubring Ω) :
    (cuspInertia D X eL hH (cuspOpen f) W).map
        (fundamentalGroupMap (cuspCover f) hbase).toMonoidHom =
      lineInertia ht W ⊓ (fundamentalGroupMap (cuspCover f) hbase).toMonoidHom.range := by
  rw [cuspInertia_eq_map, lineInertia_eq_map, Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have h := fundamentalGroupMap_cuspCover_chartHom D eL f hη hH ht hbase σ
    refine ⟨⟨toLine D eL f hη hH σ, ?_, ?_⟩, ⟨_, rfl⟩⟩
    · intro a ha
      exact hσ a ha
    · exact h.symm
  · rintro ⟨⟨σ', hσ', rfl⟩, hr⟩
    have hfix := apply_eq_of_lineGalois_mem_range D eL f hη ht hbase σ' hr
    have htL : t ∈ D.L := by
      have := (eL τ₀).2
      rwa [hτ₀] at this
    let σ : Ω ≃ₐ[K₀ k t] Ω := AlgEquiv.ofRingEquiv (f := σ'.toRingEquiv)
      (fun c ↦ hfix ⟨_, K₀_le_of_mem htL c.2⟩)
    have hσHL : σ ∈ D.HL := by
      rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hfix ⟨x, hx⟩
    refine ⟨⟨σ, D.le hσHL⟩, ?_, ?_⟩
    · intro a ha
      exact hσ' a ha
    · change fundamentalGroupMap (cuspCover f) hbase
        (D.chartHom hH (genericL D X eL (cuspOpen f)) ⟨σ, D.le hσHL⟩) = lineGalois ht σ'
      rw [fundamentalGroupMap_cuspCover_chartHom D eL f hη hH ht hbase]
      exact congrArg _ (AlgEquiv.ext fun _ ↦ rfl)

end Cover

/-! ### Valuations -/

section Valuation

variable {Ω : Type*} [Field Ω] {W : ValuationSubring Ω}

lemma valuation_lt_one_of_inv_notMem {x : Ω} (hx : x ∈ W) (hinv : x⁻¹ ∉ W) :
    W.valuation x < 1 := by
  refine lt_of_le_of_ne ((W.valuation_le_one_iff x).2 hx) fun h ↦ hinv ?_
  rw [← W.valuation_le_one_iff, map_inv₀, h, inv_one]

lemma valuation_inv_lt_one_of_notMem {x : Ω} (hx : x ∉ W) : W.valuation x⁻¹ < 1 := by
  refine valuation_lt_one_of_inv_notMem ((W.mem_or_inv_mem x).resolve_left hx) ?_
  rwa [inv_inv]

variable {k : Type*} [Field k] [Algebra k Ω] (hkW : ∀ c : k, algebraMap k Ω c ∈ W)

include hkW in
lemma aeval_mem {s : Ω} (hs : s ∈ W) (p : Polynomial k) : Polynomial.aeval s p ∈ W := by
  induction p using Polynomial.induction_on with
  | C a => simpa using hkW a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a _ =>
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact mul_mem (hkW a) (pow_mem hs _)

variable [CharZero k] {s : Ω}

include hkW in
/-- A place not containing `s` lies over `∞`: `v(2 / (2s - 1)) < 1`. -/
lemma valuation_cuspCoord_two_lt_one (hs : s ∉ W) : W.valuation (cuspCoord 2 s) < 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have h2 : (2 : Ω) ≠ 0 := two_ne_zero
  have hc : cuspCoord 2 s = (s - 2⁻¹)⁻¹ := by
    change 2 / (2 * s - 1) = _
    rw [show s - 2⁻¹ = (2 * s - 1) / 2 by field_simp, inv_div]
  rw [hc]
  refine valuation_inv_lt_one_of_notMem fun h ↦ hs ?_
  have := add_mem h (show (2 : Ω)⁻¹ ∈ W by simpa [map_inv₀, map_ofNat] using hkW 2⁻¹)
  simpa using this

/-- A place containing `s` and not `(s (s - 1))⁻¹` lies over `0` or `1`. -/
lemma exists_valuation_cuspCoord_lt_one (hs : s ∈ W) (hinv : (s * (s - 1))⁻¹ ∉ W) :
    ∃ a : Fin 2, W.valuation (cuspCoord a.castSucc s) < 1 := by
  have h1 : s - 1 ∈ W := sub_mem hs (one_mem W)
  have hlt := valuation_lt_one_of_inv_notMem (mul_mem hs h1) hinv
  rw [map_mul] at hlt
  by_cases h0 : W.valuation s < 1
  · exact ⟨0, h0⟩
  · refine ⟨1, ?_⟩
    have he : W.valuation s = 1 :=
      le_antisymm ((W.valuation_le_one_iff s).2 hs) (not_lt.1 h0)
    rw [he, one_mul] at hlt
    exact hlt

omit [Algebra k Ω] [CharZero k] in
lemma inv_mul_notMem {x y : Ω} (hx : x ∈ W) (hy : y ∈ W)
    (hlt : W.valuation x < 1 ∨ W.valuation y < 1) (hxy : x * y ≠ 0) : (x * y)⁻¹ ∉ W := by
  intro h
  have h1 := (W.valuation_le_one_iff _).2 h
  have hx1 := (W.valuation_le_one_iff _).2 hx
  have hy1 := (W.valuation_le_one_iff _).2 hy
  have hv : W.valuation (x * y) < 1 := by
    rw [map_mul]
    rcases hlt with h' | h'
    · calc W.valuation x * W.valuation y ≤ W.valuation x * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    · calc W.valuation x * W.valuation y ≤ 1 * W.valuation y := by gcongr
        _ < 1 := by rwa [one_mul]
  have hne : W.valuation (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 hxy
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hne)] at h1
  exact absurd hv (not_lt.2 h1)

omit [Algebra k Ω] [CharZero k] in
/-- A place over `0` or `1` contains `s` but not `(s (s - 1))⁻¹`. -/
lemma mem_and_inv_notMem_of_valuation_lt_one (hs0 : s * (s - 1) ≠ 0) (a : Fin 2)
    (ha : W.valuation (cuspCoord a.castSucc s) < 1) : s ∈ W ∧ (s * (s - 1))⁻¹ ∉ W := by
  fin_cases a
  · change W.valuation s < 1 at ha
    have hs : s ∈ W := (W.valuation_le_one_iff _).1 ha.le
    exact ⟨hs, inv_mul_notMem hs (sub_mem hs (one_mem W)) (Or.inl ha) hs0⟩
  · change W.valuation (s - 1) < 1 at ha
    have h1 : s - 1 ∈ W := (W.valuation_le_one_iff _).1 ha.le
    have hs : s ∈ W := by simpa using add_mem h1 (one_mem W)
    exact ⟨hs, inv_mul_notMem hs h1 (Or.inr ha) hs0⟩

end Valuation


/-! ### The place at infinity of `k(s)` -/

section Infinity

open Polynomial

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {W : ValuationSubring Ω}
  (hkW : ∀ c : k, algebraMap k Ω c ∈ W) {s : Ω} (hs : s ∉ W)

include hkW hs in
/-- At a place with `v(s) > 1`, `v(p(s)) = v(s)^{deg p}`. -/
lemma valuation_aeval_eq_pow (p : k[X]) (hp : p ≠ 0) :
    W.valuation (aeval s p) = W.valuation s ^ p.natDegree := by
  have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ W.zero_mem)
  letI : Invertible s := invertibleOfNonzero hs0
  have hu : (⅟s : Ω) = s⁻¹ := invOf_eq_inv s
  have huW : s⁻¹ ∈ W := (W.mem_or_inv_mem s).resolve_left hs
  have hult : W.valuation s⁻¹ < 1 := valuation_inv_lt_one_of_notMem hs
  have hrev := eval₂_reverse_mul_pow (algebraMap k Ω) s p
  rw [aeval_def, ← hrev, map_mul, map_pow]
  suffices h : W.valuation (eval₂ (algebraMap k Ω) (⅟s) (reverse p)) = 1 by rw [h, one_mul]
  rw [hu, ← divX_mul_X_add (reverse p), eval₂_add, eval₂_mul, eval₂_X, eval₂_C,
    coeff_zero_reverse]
  have hlc : algebraMap k Ω p.leadingCoeff ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap k Ω).injective]
    exact leadingCoeff_ne_zero.2 hp
  have hv1 : W.valuation (algebraMap k Ω p.leadingCoeff) = 1 := by
    refine le_antisymm ((W.valuation_le_one_iff _).2 (hkW _)) ?_
    have h := (W.valuation_le_one_iff _).2 (hkW p.leadingCoeff⁻¹)
    rw [map_inv₀, map_inv₀] at h
    exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hlc))).1 h
  rw [Valuation.map_add_eq_of_lt_right, hv1]
  rw [hv1, map_mul]
  have h1 : W.valuation (eval₂ (algebraMap k Ω) s⁻¹ (divX (reverse p))) ≤ 1 := by
    rw [W.valuation_le_one_iff, ← aeval_def]
    exact aeval_mem hkW huW _
  calc _ ≤ 1 * W.valuation s⁻¹ := by gcongr
    _ < 1 := by rw [one_mul]; exact hult

include hkW hs in
/-- At a place with `v(s) > 1`, `p(s)/q(s) ∈ W` iff `deg p ≤ deg q` (or `p = 0`). -/
lemma aeval_div_mem_iff (p q : k[X]) (hq : q ≠ 0) :
    aeval s p / aeval s q ∈ W ↔ p = 0 ∨ p.natDegree ≤ q.natDegree := by
  by_cases hp : p = 0
  · simp [hp, W.zero_mem]
  have hs1 : 1 < W.valuation s := by
    by_contra h
    exact hs ((W.valuation_le_one_iff s).1 (not_lt.1 h))
  have hq0 : W.valuation (aeval s q) ≠ 0 := by
    rw [valuation_aeval_eq_pow hkW hs q hq]
    exact pow_ne_zero _ (zero_lt_one.trans hs1).ne'
  rw [← W.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 hq0),
    valuation_aeval_eq_pow hkW hs p hp, valuation_aeval_eq_pow hkW hs q hq,
    pow_le_pow_iff_right₀ hs1]
  simp [hp]

omit hs in
include hkW in
/-- **Uniqueness of the place at `∞` of `k(s)`**: places `W, W' ⊇ k` of `Ω` with `s ∉ W, W'`
restrict to the same valuation ring of `k(s)`. -/
lemma comap_K₀_eq_of_notMem {W' : ValuationSubring Ω} (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hs : s ∉ W) (hs' : s ∉ W') :
    W.comap (algebraMap (K₀ k s) Ω) = W'.comap (algebraMap (K₀ k s) Ω) := by
  ext x
  change (x : Ω) ∈ W ↔ (x : Ω) ∈ W'
  obtain ⟨r, hr, t, ht, hx⟩ := IntermediateField.mem_adjoin_iff_div.1 x.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr ht
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := ht
  rw [hx]
  by_cases hq : q = 0
  · simp [hq, W.zero_mem, W'.zero_mem]
  change aeval s p / aeval s q ∈ W ↔ aeval s p / aeval s q ∈ W'
  rw [aeval_div_mem_iff hkW hs p q hq, aeval_div_mem_iff hkW' hs' p q hq]

end Infinity


/-! ### The main theorem -/

section Main

variable {k Ω : Type} [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] (D : GaloisData k t)
  {X : Scheme.{0}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  (eL : X.functionField ≃+* D.L) (hH : D.H ≤ D.HL)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

set_option maxHeartbeats 1600000 in
-- one long proof assembling the cover, the line, the Schreier filling and the cusp count
include hk hτ in
/-- **`π₁ᵉᵗ(X ∖ D) ≅ Π̂_{g,r}` with the cuspidal inertia groups going to conjugates of the
`Iⱼ`** (`k` algebraically closed of characteristic `0`, algebraic over `ℚ`). For `U ⊆ X` open
with finite nonempty complement, `g` the genus of `X` and `r = |X ∖ U|`, there is
`Θ : π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}` such that for every place `W ⊇ k` of `Ω` not centred on `U`, some
conjugate of `cuspInertia U W` is mapped by `Θ` onto some `Iⱼ = ⟨cⱼ⟩‾`. -/
theorem exists_continuousMulEquiv_cuspInertia_curve (U : X.Opens) [Nonempty U]
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
  haveI : Countable k := Belyi.Converse.countable_of_isAlgebraic_rat k
  have hX := valuationRing_stalk_of_isCurveOver k X
  -- a Belyi map with `f⁻¹(∞) = X ∖ U`
  have hgenU : genericPoint X ∈ U := genericPoint_mem_of_nonempty U
  have hDgen : ∀ p ∈ (U : Set X)ᶜ, p ≠ genericPoint X := fun p hp h ↦ hp (h ▸ hgenU)
  obtain ⟨f, hf, hD, hfk⟩ := exists_isBelyiMap_preimage_infty_eq k X (U : Set X)ᶜ hUfin hUne hDgen
  haveI := hf.isFinite
  haveI := Belyi.isDominant_of_isFinite f
  have hη : f.base (genericPoint X) ≠ P1.infty k := fun h ↦ hDgen _ ((hD _).1 h) rfl
  haveI : Nonempty (cuspOpen f) := by
    refine ⟨⟨genericPoint X, ?_⟩⟩
    have := Belyi.genericPoint_mem_preimage_puncturedLine hf
    rw [← opensRange_puncturedι] at this
    exact this
  have hUeq : U = f ⁻¹ᵁ (lineι k).opensRange := by
    ext x
    change x ∈ (U : Set X) ↔ f.base x ∈ Set.range (lineι k).base
    rw [mem_range_lineι_iff, ne_eq, hD, Set.mem_compl_iff, not_not]
  have hle : cuspOpen f ≤ U := by
    intro x hx
    rw [hUeq]
    change f.base x ∈ Set.range (lineι k).base
    obtain ⟨y, hy⟩ := hx
    rw [← hy, puncturedι_eq_comp_lineι, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hU'fin : (cuspOpen f : Set X)ᶜ.Finite := finite_compl_of_nonempty k X (cuspOpen f)
  -- the coordinate `t_f`
  have htB : Transcendental k (belyiT D eL f hη) :=
    transcendental_eL D X eL hk (transcendental_coordFun hη hfk)
  haveI : IsGalois (K₀ k (belyiT D eL f hη)) Ω :=
    isGalois_K₀_of_mem (E := D.L) D.transcendental (belyiT_mem D eL f hη) htB
  have hbase := genericL_cuspCover D eL f hη hk hfk htB
  haveI := isFiniteEtale_cuspCover f hf
  haveI : ConnectedSpace (cuspOpen f) := connectedSpace_opens_of_isIntegral _
  set tB := belyiT D eL f hη with htBdef
  have htB0 : tB * (tB - 1) ≠ 0 := by
    have h0 := ne_algebraMap_of_transcendental htB 0
    have h1 := ne_algebraMap_of_transcendental htB 1
    simp only [map_zero, map_one] at h0 h1
    exact mul_ne_zero h0 (sub_ne_zero.2 h1)
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
      (IsCentredOn D X eL (cuspOpen f) W ↔ tB ∈ W ∧ (tB * (tB - 1))⁻¹ ∈ W) := by
    intro W hkW
    rw [isCentredOn_cuspOpen_iff D eL f hkW, eLineΩ_eq D eL f hη hk hfk htB]
    have hT : (lineToΩ htB).toRingHom (lineT k) = tB := lineToΩ_lineT htB
    have hS : ∀ p : Polynomial k, (lineToΩ htB).toRingHom (algebraMap _ (lineRing k) p) =
        Polynomial.aeval tB p := by
      intro p
      have : (lineToΩ htB).comp (IsScalarTower.toAlgHom k (Polynomial k) (lineRing k)) =
          Polynomial.aeval tB := by
        refine Polynomial.algHom_ext ?_
        rw [AlgHom.comp_apply, Polynomial.aeval_X]
        exact lineToΩ_lineT htB
      exact DFunLike.congr_fun this p
    have hinvS : (lineToΩ htB).toRingHom
        (IsLocalization.Away.invSelf (Polynomial.X * (Polynomial.X - 1) : Polynomial k)) =
        (tB * (tB - 1))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have h := congrArg (lineToΩ htB).toRingHom
        (IsLocalization.Away.mul_invSelf (S := lineRing k)
          (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
      rw [map_mul, map_one, hS] at h
      simpa [mul_comm] using h
    constructor
    · intro h
      exact ⟨hT ▸ h (lineT k), hinvS ▸ h _⟩
    · rintro ⟨h1, h2⟩ x
      obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
        (Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k)) x
      have hspec := congrArg (lineToΩ htB).toRingHom (IsLocalization.mk'_spec (lineRing k) p
        (⟨(Polynomial.X * (Polynomial.X - 1)) ^ n, n, rfl⟩ :
          Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k)))
      rw [map_mul, hS, hS, map_pow, map_mul, map_sub, Polynomial.aeval_X, map_one] at hspec
      have hval : (lineToΩ htB).toRingHom (IsLocalization.mk' (lineRing k) p
          (⟨(Polynomial.X * (Polynomial.X - 1)) ^ n, n, rfl⟩ :
            Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))) =
          Polynomial.aeval tB p * ((tB * (tB - 1))⁻¹) ^ n := by
        rw [← hspec, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ htB0), mul_one]
      rw [hval]
      exact mul_mem (aeval_mem hkW h1 p) (pow_mem h2 n)
  -- `π₁ᵉᵗ(ℙ¹ ∖ {0, 1, ∞}) ≃ₜ* F̂₂`
  obtain ⟨Θ₀, hΘ₀⟩ := exists_continuousMulEquiv_lineInertia htB
  let Θ₂ : π₁ᵉᵗ(lineGen htB) ≃ₜ* FHat 1 := Θ₀.trans (completionCongr freeTwoEquiv).symm
  have hΘ₂ : ∀ (j : Fin 3) (W : ValuationSubring Ω), (∀ c : k, algebraMap k Ω c ∈ W) →
      W.valuation (cuspCoord j tB) < 1 →
      ∃ τ' : FHat 1, (lineInertia htB W).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        (basicInertia (lineWord j)).map (MulAut.conj τ').toMonoidHom := by
    intro j W hkW hWj
    obtain ⟨σ, hσ⟩ := hΘ₀ j W hkW hWj
    refine ⟨(completionCongr freeTwoEquiv).symm (Θ₀ σ)⁻¹, ?_⟩
    rw [← map_inertia_completionCongr_symm, ← hσ, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [Θ₂, MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  -- the fibre of `U'` over the generic point of the line
  set ηU := specPoint D.L Ω ≫ genericL D X eL (cuspOpen f) with hηU
  haveI hconn : IsConnected (coverObj (cuspCover f)) :=
    (isConnected_iff_connectedSpace _).2 (inferInstanceAs (ConnectedSpace (cuspOpen f)))
  let Fb := (FiniteEtale.fiber (lineGen htB)).obj (coverObj (cuspCover f))
  let ω₀ : Fb := coverPt (cuspCover f) ηU hbase
  letI iP : MulAction (FHat 1) Fb :=
    MulAction.compHom Fb (Θ₂.symm : FHat 1 →* π₁ᵉᵗ(lineGen htB))
  letI iF : MulAction (FreeGroup (Fin (1 + 1))) Fb :=
    MulAction.compHom Fb ((Θ₂.symm : FHat 1 →* π₁ᵉᵗ(lineGen htB)).comp (etaHom _))
  have hcompat : ∀ (g : FreeGroup (Fin (1 + 1))) (y : Fb),
      g • y = etaFn (GrpCat.of (FreeGroup (Fin (1 + 1)))) g • y := fun _ _ ↦ rfl
  have hopen : ∀ y : Fb, IsOpen (MulAction.stabilizer (FHat 1) y : Set (FHat 1)) := fun y ↦
    (stabilizer_isOpen (M := π₁ᵉᵗ(lineGen htB)) y).preimage Θ₂.symm.continuous
  have htrans : ∀ ω : Fb, ∃ g : FreeGroup (Fin (1 + 1)), g • ω₀ = ω := by
    intro ω
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq π₁ᵉᵗ(lineGen htB) ω₀ ω
    have hV : IsOpen {τ' : FHat 1 | Θ₂.symm τ' • ω₀ = ω} := by
      have : {τ' : FHat 1 | Θ₂.symm τ' • ω₀ = ω} =
          (fun τ' ↦ (Θ₂ σ)⁻¹ * τ') ⁻¹' (MulAction.stabilizer (FHat 1) ω₀ : Set (FHat 1)) := by
        ext τ'
        simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          MulAction.mem_stabilizer_iff]
        change _ ↔ Θ₂.symm ((Θ₂ σ)⁻¹ * τ') • ω₀ = ω₀
        rw [map_mul, map_inv, ContinuousMulEquiv.symm_apply_apply, mul_smul, inv_smul_eq_iff, hσ]
      rw [this]
      exact (hopen ω₀).preimage (continuous_const.mul continuous_id)
    obtain ⟨g, hg⟩ := (denseRange (GrpCat.of (FreeGroup (Fin (1 + 1))))).exists_mem_open hV
      ⟨Θ₂ σ, by simp [hσ]⟩
    exact ⟨g, hg⟩
  -- `π₁ᵉᵗ(U') ≃ₜ* Stab(ω₀) ⊆ F̂₂`
  have hmemS : ∀ x : MulAction.stabilizer π₁ᵉᵗ(lineGen htB) ω₀,
      Θ₂ (x : π₁ᵉᵗ(lineGen htB)) ∈ MulAction.stabilizer (FHat 1) ω₀ := by
    intro x
    change Θ₂.symm (Θ₂ (x : π₁ᵉᵗ(lineGen htB))) • ω₀ = ω₀
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact x.2
  let eS : MulAction.stabilizer π₁ᵉᵗ(lineGen htB) ω₀ ≃ₜ* MulAction.stabilizer (FHat 1) ω₀ :=
    { toFun x := ⟨Θ₂ (x : π₁ᵉᵗ(lineGen htB)), hmemS x⟩
      invFun y := ⟨Θ₂.symm y, y.2⟩
      left_inv x := Subtype.ext (Θ₂.symm_apply_apply (x : π₁ᵉᵗ(lineGen htB)))
      right_inv y := Subtype.ext (Θ₂.apply_symm_apply (y : FHat 1))
      map_mul' x y := Subtype.ext (map_mul Θ₂ (x : π₁ᵉᵗ(lineGen htB)) y)
      continuous_toFun := (Θ₂.continuous.comp continuous_subtype_val).subtype_mk hmemS
      continuous_invFun :=
        (Θ₂.symm.continuous.comp continuous_subtype_val).subtype_mk fun y ↦ y.2 }
  let Φ : π₁ᵉᵗ(ηU) ≃ₜ* MulAction.stabilizer (FHat 1) ω₀ :=
    (coverEquiv (cuspCover f) ηU hbase).trans eS
  have hΦ : ∀ x, (Φ x : FHat 1) = Θ₂ (fundamentalGroupMap (cuspCover f) hbase x) := fun _ ↦ rfl
  have hst : (fundamentalGroupMap (cuspCover f) hbase).toMonoidHom.range.map
      (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) = MulAction.stabilizer (FHat 1) ω₀ := by
    rw [range_fundamentalGroupMap_eq_coverSubgroup]
    ext τ'
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      change Θ₂.symm (Θ₂ σ) • ω₀ = ω₀
      rw [ContinuousMulEquiv.symm_apply_apply]
      exact hσ
    · intro hτ'
      exact ⟨Θ₂.symm τ', hτ', by simp⟩
  have himage : ∀ W : ValuationSubring Ω, cuspImage Φ (cuspInertia D X eL hH (cuspOpen f) W) =
      (lineInertia htB W).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) ⊓
        MulAction.stabilizer (FHat 1) ω₀ := by
    intro W
    have h1 : cuspImage Φ (cuspInertia D X eL hH (cuspOpen f) W) =
        ((cuspInertia D X eL hH (cuspOpen f) W).map
          (fundamentalGroupMap (cuspCover f) hbase).toMonoidHom).map
            (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) := by
      rw [cuspImage, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, map_cuspInertia_cuspCover D eL f hη hH htB hbase hτ W,
      Subgroup.map_inf_eq _ _ _ Θ₂.injective, hst]
  have hconjmap : ∀ (S : Subgroup π₁ᵉᵗ(lineGen htB)) (g : π₁ᵉᵗ(lineGen htB)),
      (S.map (MulAut.conj g).toMonoidHom).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        (S.map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1)).map (MulAut.conj (Θ₂ g)).toMonoidHom := by
    intro S g
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hword : ∀ a : Fin 2, lineWord a.castSucc = FreeGroup.of a := by
    intro a
    fin_cases a <;> rfl
  -- the cusps of `U'` over `0, 1`
  let 𝒞 : Set (Subgroup π₁ᵉᵗ(ηU)) := {C | ∃ W : ValuationSubring Ω,
    (IsCentredOn D X eL U W ∧ ¬ IsCentredOn D X eL (cuspOpen f) W) ∧
      C = cuspInertia D X eL hH (cuspOpen f) W}
  have h𝒞 : ∀ C ∈ 𝒞, ∃ (a : Fin (1 + 1)) (τ' : FHat 1), cuspImage Φ C =
      (basicInertia (FreeGroup.of a)).map (MulAut.conj τ').toMonoidHom ⊓
        MulAction.stabilizer (FHat 1) ω₀ := by
    rintro _ ⟨W, ⟨hWU, hWU'⟩, rfl⟩
    have hkW := hWU.1
    have h1 := (hcentU W hkW).1 hWU
    have h2 : (tB * (tB - 1))⁻¹ ∉ W := fun h ↦ hWU' ((hcentU' W hkW).2 ⟨h1, h⟩)
    obtain ⟨a, ha⟩ := exists_valuation_cuspCoord_lt_one h1 h2
    obtain ⟨τ', hτ'⟩ := hΘ₂ a.castSucc W hkW ha
    refine ⟨a, τ', ?_⟩
    rw [himage, hτ', hword]
  have hexW : ∀ a : Fin 2, ∃ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) ∧
      W.valuation (cuspCoord a.castSucc tB) < 1 := by
    intro a
    let e := Polynomial.algEquivOfTranscendental k tB htB
    let ev : (Algebra.adjoin k {tB}).toSubring →+* k :=
      (Polynomial.evalRingHom ((a : ℕ) : k)).comp e.symm.toRingEquiv.toRingHom
    haveI : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
    obtain ⟨V, hRV, hnon, -⟩ := WeilCurves.FunctionField.exists_valuationSubring_of_prime
      (Algebra.adjoin k {tB}).toSubring (RingHom.ker ev)
    refine ⟨V, fun c ↦ hRV (Subalgebra.algebraMap_mem _ c), ?_⟩
    have hc : cuspCoord a.castSucc tB = tB - ((a : ℕ) : Ω) := by
      fin_cases a <;> simp [cuspCoord]
    have hmem : tB - ((a : ℕ) : Ω) ∈ (Algebra.adjoin k {tB}).toSubring :=
      Subring.sub_mem _ (Algebra.subset_adjoin rfl) (natCast_mem _ _)
    have he : (⟨_, hmem⟩ : (Algebra.adjoin k {tB}).toSubring) =
        e (Polynomial.X - Polynomial.C ((a : ℕ) : k)) := by
      apply Subtype.ext
      simp [e, Polynomial.algEquivOfTranscendental_apply]
    have hker : (⟨_, hmem⟩ : (Algebra.adjoin k {tB}).toSubring) ∈ RingHom.ker ev := by
      rw [RingHom.mem_ker, he]
      simp [ev]
    have hnu := hnon _ hker (hRV hmem)
    rw [hc]
    exact (V.valuation_lt_one_iff ⟨_, hRV hmem⟩).1 ((IsLocalRing.mem_maximalIdeal _).2 hnu)
  have h𝒞' : ∀ (a : Fin (1 + 1)) (τ' : FHat 1), ∃ C ∈ 𝒞, cuspImage Φ C =
      (basicInertia (FreeGroup.of a)).map (MulAut.conj τ').toMonoidHom ⊓
        MulAction.stabilizer (FHat 1) ω₀ := by
    intro a τ'
    obtain ⟨W₀, hkW₀, hW₀⟩ := hexW a
    obtain ⟨τ₀, hτ₀⟩ := hΘ₂ a.castSucc W₀ hkW₀ hW₀
    obtain ⟨σ, hσ⟩ := lineGalois_surjective htB (Θ₂.symm (τ' * τ₀⁻¹))
    have hσk : ∀ x ∈ K₀ k tB, σ.symm x = x := fun x hx ↦ σ.symm.commutes ⟨x, hx⟩
    have hkW : ∀ c : k, algebraMap k Ω c ∈ W₀.comap (σ.symm : Ω →+* Ω) := by
      intro c
      rw [ValuationSubring.mem_comap]
      change σ.symm (algebraMap k Ω c) ∈ W₀
      rw [hσk _ (IntermediateField.algebraMap_mem _ c)]
      exact hkW₀ c
    have hWa : (W₀.comap (σ.symm : Ω →+* Ω)).valuation (cuspCoord a.castSucc tB) < 1 := by
      rw [valuation_comap_lt_one_iff]
      change W₀.valuation (σ.symm (cuspCoord a.castSucc tB)) < 1
      rw [hσk _ (cuspCoord_mem _)]
      exact hW₀
    obtain ⟨h1, h2⟩ := mem_and_inv_notMem_of_valuation_lt_one htB0 a hWa
    refine ⟨_, ⟨W₀.comap (σ.symm : Ω →+* Ω),
      ⟨(hcentU _ hkW).2 h1, fun h ↦ h2 ((hcentU' _ hkW).1 h).2⟩, rfl⟩, ?_⟩
    rw [himage, lineInertia_comap htB W₀ σ, hconjmap, hτ₀, hσ,
      ContinuousMulEquiv.apply_symm_apply, Subgroup.map_map, hword]
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
      (_ : IsCentredOn D X eL U W ∧ ¬ IsCentredOn D X eL (cuspOpen f) W),
        (cuspInertia D X eL hH (cuspOpen f) W : Set π₁ᵉᵗ(ηU)) := by
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
  have horb : ∀ z ∈ basicInertia (lineWord 2), ∀ y : Fb,
      (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (Pi1.ReidemeisterSchreier.xInf 1)) Fb)
        (z • y)) = Quotient.mk _ y := by
    intro z hz y
    let S : Set (FHat 1) := {z | (Quotient.mk (MulAction.orbitRel
      (Subgroup.zpowers (Pi1.ReidemeisterSchreier.xInf 1)) Fb) (z • y)) = Quotient.mk _ y}
    have hS : IsClosed S := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro z₀ hz₀
      refine ⟨(fun z ↦ z₀⁻¹ * z) ⁻¹' (MulAction.stabilizer (FHat 1) y : Set (FHat 1)), ?_,
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
    refine ⟨⟨Pi1.ReidemeisterSchreier.xInf 1 ^ m, Subgroup.zpow_mem_zpowers _ m⟩, ?_⟩
    change Pi1.ReidemeisterSchreier.xInf 1 ^ m • y = _
    rw [hcompat]
    change etaHom _ (Pi1.ReidemeisterSchreier.xInf 1 ^ m) • y =
      (etaHom (FreeGroup (Fin (1 + 1))) (lineWord 2)) ^ m • y
    rw [map_zpow]
    rfl
  have hinfW : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      ¬ IsCentredOn D X eL U W → tB ∉ W := fun W hkW hWU h ↦ hWU ((hcentU W hkW).2 h)
  have hconjL : ∀ (W : ValuationSubring Ω) (ρ : Ω ≃ₐ[K₀ k tB] Ω),
      (lineInertia htB (W.comap (ρ.symm : Ω →+* Ω))).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        ((lineInertia htB W).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1)).map
          (MulAut.conj (Θ₂ (lineGalois htB ρ))).toMonoidHom := by
    intro W ρ
    rw [lineInertia_comap htB W ρ, hconjmap]
  have hmove : ∀ (W : ValuationSubring Ω) (ρ : Ω ≃ₐ[K₀ k tB] Ω) (τ τ' : FHat 1),
      (lineInertia htB W).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        (basicInertia (lineWord 2)).map (MulAut.conj τ).toMonoidHom →
      (lineInertia htB (W.comap (ρ.symm : Ω →+* Ω))).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        (basicInertia (lineWord 2)).map (MulAut.conj τ').toMonoidHom →
      (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (Pi1.ReidemeisterSchreier.xInf 1)) Fb)
        (τ'⁻¹ • ω₀)) = Quotient.mk _ (τ⁻¹ • ((Θ₂ (lineGalois htB ρ))⁻¹ • ω₀)) := by
    intro W ρ τ τ' hτ hτ'
    have hn : τ'⁻¹ * (Θ₂ (lineGalois htB ρ) * τ) ∈ basicInertia (lineWord 2) := by
      apply mem_basicInertia_of_map_conj_eq
      rw [← map_conj_eq_iff, ← map_conj_map_conj, ← hτ, ← hconjL, hτ']
    have he : τ'⁻¹ = (τ'⁻¹ * (Θ₂ (lineGalois htB ρ) * τ)) * τ⁻¹ *
        (Θ₂ (lineGalois htB ρ))⁻¹ := by group
    rw [he, mul_assoc, mul_smul, horb _ hn, mul_smul]
  have hstab : ∀ ρ : Ω ≃ₐ[K₀ k tB] Ω, (Θ₂ (lineGalois htB ρ))⁻¹ • ω₀ = ω₀ →
      ∀ x : D.L, ρ (x : Ω) = x := by
    intro ρ h x
    refine apply_eq_of_lineGalois_mem_range D eL f hη htB hbase ρ ?_ x
    rw [range_fundamentalGroupMap_eq_coverSubgroup]
    change lineGalois htB ρ • ω₀ = ω₀
    have h' : Θ₂.symm (Θ₂ (lineGalois htB ρ))⁻¹ • ω₀ = ω₀ := h
    rw [map_inv, ContinuousMulEquiv.symm_apply_apply, inv_smul_eq_iff] at h'
    exact h'.symm
  have hstab' : ∀ ρ : Ω ≃ₐ[K₀ k tB] Ω, (∀ x : D.L, ρ (x : Ω) = x) →
      (Θ₂ (lineGalois htB ρ))⁻¹ • ω₀ = ω₀ := by
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
    have hg : lineGalois htB ρ ∈ (fundamentalGroupMap (cuspCover f) hbase).toMonoidHom.range := by
      refine ⟨D.chartHom hH (genericL D X eL (cuspOpen f)) ⟨σ, D.le hσHL⟩, ?_⟩
      change fundamentalGroupMap (cuspCover f) hbase _ = _
      rw [fundamentalGroupMap_cuspCover_chartHom D eL f hη hH htB hbase]
      exact congrArg _ (AlgEquiv.ext fun _ ↦ rfl)
    rw [range_fundamentalGroupMap_eq_coverSubgroup] at hg
    have hg' : lineGalois htB ρ • ω₀ = ω₀ := hg
    change Θ₂.symm (Θ₂ (lineGalois htB ρ))⁻¹ • ω₀ = ω₀
    rw [map_inv, ContinuousMulEquiv.symm_apply_apply, inv_smul_eq_iff]
    exact hg'.symm
  have hclass : ∀ (W W' : ValuationSubring Ω) (τ τ' : FHat 1),
      (∀ c : k, algebraMap k Ω c ∈ W) → (∀ c : k, algebraMap k Ω c ∈ W') → tB ∉ W → tB ∉ W' →
      (lineInertia htB W).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        (basicInertia (lineWord 2)).map (MulAut.conj τ).toMonoidHom →
      (lineInertia htB W').map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        (basicInertia (lineWord 2)).map (MulAut.conj τ').toMonoidHom →
      ((Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (Pi1.ReidemeisterSchreier.xInf 1)) Fb)
        (τ⁻¹ • ω₀)) = Quotient.mk _ (τ'⁻¹ • ω₀) ↔
        W.comap (algebraMap D.L Ω) = W'.comap (algebraMap D.L Ω)) := by
    intro W W' τ τ' hkW hkW' hW hW' hτ hτ'
    constructor
    · intro h
      obtain ⟨ρ, rfl⟩ := exists_algEquiv_comap_eq W W' (comap_K₀_eq_of_notMem hkW hkW' hW hW')
      rw [hmove W ρ τ τ' hτ hτ'] at h
      obtain ⟨⟨x, hx⟩, hxe⟩ := Quotient.exact h.symm
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hxe' : etaFn (GrpCat.of (FreeGroup (Fin (1 + 1))))
          (Pi1.ReidemeisterSchreier.xInf 1 ^ m) • (τ⁻¹ • ω₀) =
          τ⁻¹ • ((Θ₂ (lineGalois htB ρ))⁻¹ • ω₀) := by
        rw [← hcompat]
        exact hxe
      -- `ι' = τ η(x_∞)^m τ⁻¹ ∈ Θ₂(I_W)`
      have hι' : τ * etaFn (GrpCat.of (FreeGroup (Fin (1 + 1))))
          (Pi1.ReidemeisterSchreier.xInf 1 ^ m) * τ⁻¹ ∈
          (lineInertia htB W).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) := by
        rw [hτ]
        refine ⟨_, ?_, rfl⟩
        change etaHom _ (Pi1.ReidemeisterSchreier.xInf 1 ^ m) ∈ basicInertia (lineWord 2)
        rw [map_zpow]
        exact Subgroup.zpow_mem _ (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)) m
      obtain ⟨ι, hι, hιe⟩ := hι'
      rw [lineInertia_eq_map] at hι
      obtain ⟨i, hi, rfl⟩ := hι
      have hιe' : Θ₂ (lineGalois htB i) = τ * etaFn (GrpCat.of (FreeGroup (Fin (1 + 1))))
          (Pi1.ReidemeisterSchreier.xInf 1 ^ m) * τ⁻¹ := hιe
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
        (fun c ↦ κ.commutes ⟨_, K₀_le_of_mem (belyiT_mem D eL f hη) c.2⟩)
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
  have hτex : ∀ y : ((U : Set X)ᶜ : Set X), ∃ τ' : FHat 1,
      (lineInertia htB (Wy y)).map (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) =
        (basicInertia (lineWord 2)).map (MulAut.conj τ').toMonoidHom := fun y ↦
    hΘ₂ 2 (Wy y) (hWy y).2.1 (valuation_cuspCoord_two_lt_one (hWy y).2.1
      (hinfW _ (hWy y).2.1 (hWy y).2.2))
  choose τy hτy using hτex
  let J : ((U : Set X)ᶜ : Set X) →
      MulAction.orbitRel.Quotient (Subgroup.zpowers (Pi1.ReidemeisterSchreier.xInf 1)) Fb :=
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
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq π₁ᵉᵗ(lineGen htB) ω₀ (Θ₂.symm (τy y₀) • ω)
    obtain ⟨ρ, hρ⟩ := lineGalois_surjective htB σ⁻¹
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
    have hτW : (lineInertia htB ((Wy y₀).comap (ρ.symm : Ω →+* Ω))).map
        (Θ₂ : π₁ᵉᵗ(lineGen htB) →* FHat 1) = (basicInertia (lineWord 2)).map
          (MulAut.conj (Θ₂ (lineGalois htB ρ) * τy y₀)).toMonoidHom := by
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
  have hWinf : W.valuation (cuspCoord 2 tB) < 1 :=
    valuation_cuspCoord_two_lt_one hkW fun h ↦ hWU ((hcentU W hkW).2 h)
  obtain ⟨τ', hτ'⟩ := hΘ₂ 2 W hkW hWinf
  obtain ⟨κ, hjκ⟩ := hqcusp (cuspInertia D X eL hH (cuspOpen f) W) τ' (by
    rw [himage, hτ']
    rfl)
  have hmapU : (cuspInertia D X eL hH (cuspOpen f) W).map p.toMonoidHom =
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

end Main

end CurvesJacobian.Cusp
