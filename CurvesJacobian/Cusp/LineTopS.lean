/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LineAnalyticS
import CurvesJacobian.Cusp.LineInertiaIso
import Oka.Topology.Covering.BranchedSurfaceAny

/-!
# `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞})) ≅ Π̂_{0,n+2}`, with cusp generators fixing points of covers with branches

Let `k` be a countable algebraically closed field of characteristic `0`, `S ⊆ k` with
`|S| = n + 1`, `U = ℙ¹ ∖ (S ∪ {∞}) = Spec k[t, 1/P_S(t)]` (`CurvesJacobian.Cusp.lineRingS`) and
`x` a geometric point of `U`.

**Main theorem** (`CurvesJacobian.Cusp.exists_continuousMulEquiv_lineS_branch`): there are a
numbering `σ : S ≃ {0, …, n}` and an isomorphism of topological groups
`Θ : π₁ᵉᵗ(U, x) ≃ₜ* Π̂_{0,n+2}` such that for every cusp `c` (a point `a ∈ S`, or `∞`) and every
finite étale `Y ⟶ U` with a branch at `c` (`CurvesJacobian.Cusp.PBranch` with relation
`t = a + s` resp. `t s = 1`), the cuspidal generator `c_{σ a}` resp. `c_{n+1}` of `Π̂_{0,n+2}`
(`CurvesJacobian.Cusp.cuspIndex`) acts on the fibre of `Y` over `x` with a fixed point.

## Proof

A self-homeomorphism `τ` of `ℂ` moves the image `S' ⊆ ℂ` of `S` onto `{0, …, n}`
(oka's `BranchedCover.Gen.exists_homeomorph_image_eq_pts`), and `π₁(ℂ ∖ {0, …, n})` has a free
basis of loops `g_i` around the points `i` whose product is a big circle
(oka's `Complex.PuncturedPlane.LineBasis.exists_basis_univ`). Transported along `τ⁻¹`, the
`g_i` are loops near the points of `S'` and their product is a loop near `∞`
(`CurvesJacobian.Cusp.IsNearLoop`, using that `τ⁻¹` is continuous and `τ` maps compact sets to
bounded sets). With `Π_{0,n+2} ≅ F(c_0, …, c_n)` (`c_{n+1} = (c_0 ⋯ c_n)⁻¹`) this gives
`Π_{0,n+2} ≅ π₁(U_ℂ^an)`, and `Θ` is obtained as in `CurvesJacobian.Cusp.LineInertiaIso`
(comparison theorem, invariance of `π₁ᵉᵗ` under base change to `ℂ`, change of fibre functor).
A branch at `c` base-changes to `ℂ` (`CurvesJacobian.Cusp.PBranch.baseChange`), so loops near
`c` fix points of the fibre (`CurvesJacobian.Cusp.exists_monodromy_fixed_of_pBranch`).
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic Topology Metric PreGaloisCategory
open ProfiniteGrp.ProfiniteCompletion Complex.PuncturedPlane Complex.PuncturedPlane.LineBasis
open BranchedCover.Gen
open scoped TensorProduct

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Fundamental groups and homeomorphisms -/

section Homeo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)

lemma mapOfEq_homeo_map_symm (y : Y) (p : FundamentalGroup Y y) :
    FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ (e.apply_symm_apply y)
      (FundamentalGroup.map ⟨e.symm, e.symm.continuous⟩ y p) = p := by
  revert p
  refine Path.Homotopic.Quotient.ind (fun q ↦ ?_)
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.cast
    (((Path.Homotopic.Quotient.mk q).map ⟨e.symm, e.symm.continuous⟩).map
      ⟨e, e.continuous⟩) _ _ = _
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  congr 1
  exact Path.ext (funext fun θ ↦ e.apply_symm_apply (q θ))

lemma map_symm_mapOfEq_homeo (y : Y) (p : FundamentalGroup X (e.symm y)) :
    FundamentalGroup.map ⟨e.symm, e.symm.continuous⟩ y
      (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ (e.apply_symm_apply y) p) = p := by
  revert p
  refine Path.Homotopic.Quotient.ind (fun q ↦ ?_)
  rw [FundamentalGroup.mapOfEq_apply]
  change (((Path.Homotopic.Quotient.mk q).map ⟨e, e.continuous⟩).cast _ _).map
    ⟨e.symm, e.symm.continuous⟩ = _
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    ← Path.Homotopic.Quotient.mk_map]
  congr 1
  exact Path.ext (funext fun θ ↦ e.symm_apply_apply (q θ))

/-- **A homeomorphism `e : X ≃ₜ Y` induces `π₁(Y, y) ≅ π₁(X, e⁻¹(y))`** (through `e⁻¹`). -/
def homeoFundamentalGroupEquiv (y : Y) :
    FundamentalGroup Y y ≃* FundamentalGroup X (e.symm y) where
  toFun := FundamentalGroup.map ⟨e.symm, e.symm.continuous⟩ y
  invFun := FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ (e.apply_symm_apply y)
  left_inv := mapOfEq_homeo_map_symm e y
  right_inv := map_symm_mapOfEq_homeo e y
  map_mul' := map_mul _

lemma homeoFundamentalGroupEquiv_apply (y : Y) (p : FundamentalGroup Y y) :
    homeoFundamentalGroupEquiv e y p = FundamentalGroup.map ⟨e.symm, e.symm.continuous⟩ y p :=
  rfl

end Homeo

/-! ### Transporting loops near points along homeomorphisms of `ℂ` -/

section Near

variable {T S' : Finset ℂ}

/-- A self-homeomorphism `τ` of `ℂ` with `τ(S') = T` as a homeomorphism `ℂ ∖ S' ≃ₜ ℂ ∖ T`. -/
def regionHomeo (τ : ℂ ≃ₜ ℂ) (hST : ∀ z, τ z ∈ T ↔ z ∈ S') :
    Region Set.univ S' ≃ₜ Region Set.univ T where
  toFun z := ⟨τ z, trivial, fun hz ↦ z.2.2 ((hST z).1 hz)⟩
  invFun z := ⟨τ.symm z, trivial, fun hz ↦ z.2.2 (by
    rw [← τ.apply_symm_apply (z : ℂ)]
    exact (hST _).2 hz)⟩
  left_inv z := Subtype.ext (τ.symm_apply_apply (z : ℂ))
  right_inv z := Subtype.ext (τ.apply_symm_apply (z : ℂ))
  continuous_toFun := (τ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (τ.symm.continuous.comp continuous_subtype_val).subtype_mk _

lemma coe_regionHomeo_symm (τ : ℂ ≃ₜ ℂ) (hST : ∀ z, τ z ∈ T ↔ z ∈ S')
    (z : Region Set.univ T) : ((regionHomeo τ hST).symm z : ℂ) = τ.symm z := rfl

/-- **Images of loops are near `c`** if they have representatives whose images lie in arbitrarily
small punctured neighbourhoods of `c`. -/
lemma isNearLoop_map (F : C(Region Set.univ T, Region Set.univ S')) {x₀ : Region Set.univ T}
    (γ' : FundamentalGroup (Region Set.univ T) x₀) (c : Option ℂ)
    (H : ∀ r > (0 : ℝ), ∃ (y : Region Set.univ T) (γ : Path y y)
      (δ : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk y),
      γ' = δ ≫ ⟦γ⟧ ≫ Groupoid.inv δ ∧ ∀ θ, (F (γ θ) : ℂ) ∈ nearSet c r) :
    IsNearLoop c (FundamentalGroup.map F x₀ γ') := by
  intro r hr
  obtain ⟨y, γ, δ, hγ, hθ⟩ := H r hr
  refine ⟨F y, γ.map F.continuous, (FundamentalGroupoid.map F).map δ, ?_, hθ⟩
  change (FundamentalGroupoid.map F).map γ' = _
  subst hγ
  rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Functor.map_inv,
    ← Groupoid.inv_eq_inv]
  rfl

/-- **Loops around a point `p` are transported to loops near `τ⁻¹(p)`.** -/
lemma isNearLoop_of_isLoopAround (τ : ℂ ≃ₜ ℂ) (hST : ∀ z, τ z ∈ T ↔ z ∈ S')
    {x₀ : Region Set.univ T} {γ' : FundamentalGroup (Region Set.univ T) x₀} {p : ℂ}
    (hγ : IsLoopAround γ' p) :
    IsNearLoop (some (τ.symm p)) (FundamentalGroup.map
      ⟨(regionHomeo τ hST).symm, (regionHomeo τ hST).symm.continuous⟩ x₀ γ') := by
  obtain ⟨r₀, h₀, δ, hδ⟩ := hγ
  refine isNearLoop_map _ _ _ fun r hr ↦ ?_
  obtain ⟨ρ, hρ, hρr⟩ := Metric.continuous_iff.1 τ.symm.continuous p r hr
  set r₁ := min ρ r₀ / 2 with hr₁def
  have hm : 0 < min ρ r₀ := lt_min hρ h₀.pos
  have hr₁ : 0 < r₁ := by positivity
  have hr₁ρ : r₁ < ρ := by
    have := min_le_left ρ r₀
    linarith
  have hr₁r₀ : r₁ ≤ r₀ := by
    have := min_le_right ρ r₀
    linarith
  have h₁ : Admissible Set.univ T p r₁ :=
    ⟨hr₁, Set.subset_univ _, fun s' hs' hb ↦
      h₀.isolated s' hs' (closedBall_subset_closedBall hr₁r₀ hb)⟩
  obtain ⟨β, hβ⟩ := circleArrow_eq_conj h₀ h₁
  refine ⟨_, circlePath h₁, δ ≫ β, ?_, fun θ ↦ ?_⟩
  · rw [hδ, hβ]
    simp only [Groupoid.inv_eq_inv, IsIso.inv_comp, Category.assoc]
    rfl
  · change τ.symm (circleFun p r₁ θ) ∈ ball (τ.symm p) r \ {τ.symm p}
    have hn := norm_circleFun_sub p hr₁.le θ
    refine ⟨hρr _ ?_, fun heq ↦ ?_⟩
    · rw [dist_eq_norm, hn]
      exact hr₁ρ
    · have := τ.symm.injective (Set.mem_singleton_iff.1 heq)
      rw [this, sub_self, norm_zero] at hn
      exact hr₁.ne hn

/-- **Circles of radius `rad n` and `R ≥ rad n` around `n/2` are conjugate** in
`ℂ ∖ {0, …, n}`. -/
lemma circ_conj_big {n : ℕ} {R : ℝ} (hR : rad n ≤ R) :
    ∃ β : FundamentalGroupoid.mk (theta (circleIn_univ (le_refl (rad n))) 0) ⟶
        FundamentalGroupoid.mk (theta (circleIn_univ hR) 0),
      (⟦circ (circleIn_univ (le_refl (rad n))) 0⟧ : FundamentalGroupoid.mk _ ⟶
        FundamentalGroupoid.mk _) = β ≫ ⟦circ (circleIn_univ hR) 0⟧ ≫ Groupoid.inv β :=
  eq_conj_of_lerp _ _ fun s t ↦ by
    refine ⟨trivial, notMem_pts_of_lt ?_⟩
    change (n : ℝ) / 2 < ‖(1 - (s : ℝ)) • thetaFun (cen n) (rad n) (0 + 2 * Real.pi * t) +
      (s : ℝ) • thetaFun (cen n) R (0 + 2 * Real.pi * t) - cen n‖
    have e : (1 - (s : ℝ)) • thetaFun (cen n) (rad n) (0 + 2 * Real.pi * t) +
        (s : ℝ) • thetaFun (cen n) R (0 + 2 * Real.pi * t) - cen n =
        (((1 - (s : ℝ)) * rad n + s * R : ℝ) : ℂ) *
          Complex.exp (((0 + 2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
      simp only [thetaFun, Complex.real_smul]
      push_cast
      ring
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hX : (n : ℝ) / 2 < (1 - (s : ℝ)) * rad n + s * R := by
      nlinarith [half_lt_rad n]
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
    exact hX

/-- **The big circle is transported to a loop near `∞`**: `τ` maps the closed disc of radius
`1/r` to a bounded set, so the circles of large radius around `n/2` are mapped by `τ⁻¹` outside
that disc. -/
lemma isNearLoop_none_of_circ {n : ℕ} (τ : ℂ ≃ₜ ℂ) (hST : ∀ z, τ z ∈ pts n ↔ z ∈ S')
    {x₀ : Region Set.univ (pts n)} (γ' : FundamentalGroup (Region Set.univ (pts n)) x₀)
    (δ : FundamentalGroupoid.mk x₀ ⟶
      FundamentalGroupoid.mk (theta (circleIn_univ (le_refl (rad n))) 0))
    (hγ : γ' = δ ≫ ⟦circ (circleIn_univ (le_refl (rad n))) 0⟧ ≫ Groupoid.inv δ) :
    IsNearLoop none (FundamentalGroup.map
      ⟨(regionHomeo τ hST).symm, (regionHomeo τ hST).symm.continuous⟩ x₀ γ') := by
  refine isNearLoop_map _ _ _ fun r hr ↦ ?_
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1
    ((isCompact_closedBall (0 : ℂ) r⁻¹).image τ.continuous).isBounded
  set R := max (rad n) (B + ‖cen n‖ + 1) with hRdef
  have hR : rad n ≤ R := le_max_left _ _
  have hRB : B + ‖cen n‖ + 1 ≤ R := le_max_right _ _
  obtain ⟨β, hβ⟩ := circ_conj_big hR
  refine ⟨_, circ (circleIn_univ hR) 0, δ ≫ β, ?_, fun θ ↦ ?_⟩
  · rw [hγ, hβ]
    simp only [Groupoid.inv_eq_inv, IsIso.inv_comp, Category.assoc]
  · rw [nearSet_none, Set.mem_setOf_eq]
    change r⁻¹ < ‖τ.symm (circ (circleIn_univ hR) 0 θ : ℂ)‖
    by_contra hle
    rw [not_lt] at hle
    set z : ℂ := (circ (circleIn_univ hR) 0 θ : ℂ) with hzdef
    have hz : ‖z - cen n‖ = R :=
      norm_thetaFun_sub (cen n) ((rad_pos n).le.trans hR) (0 + 2 * Real.pi * θ)
    have hK : z ∈ τ '' closedBall 0 r⁻¹ :=
      ⟨τ.symm z, by rw [mem_closedBall, dist_zero_right]; exact hle, τ.apply_symm_apply z⟩
    have h1 := hB z hK
    have h2 : ‖z - cen n‖ ≤ ‖z‖ + ‖cen n‖ := norm_sub_le _ _
    linarith

end Near

/-! ### The surface group -/

section Surface

/-- The free generators `c_0, …, c_n` of `Π_{0,n+2}`, indexed by `Fin (n + 1)`. -/
def surfaceGenEquivFin (n : ℕ) : Pi1.SurfaceGen 0 (n + 1) ≃ Fin (n + 1) where
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

@[simp]
lemma surfaceGenEquivFin_c (n : ℕ) (j : Fin (n + 1)) : surfaceGenEquivFin n (.c j) = j := rfl

/-- In `Π_{0,n+2}`, `c_{n+1} = (c_0 ⋯ c_n)⁻¹`. -/
lemma cusp_last_eq (n : ℕ) : Pi1.SurfaceGroup.cusp (g := 0) (r := n + 1 + 1) (Fin.last (n + 1)) =
    (Pi1.SurfaceGen.ordProd fun j : Fin (n + 1) ↦
      Pi1.SurfaceGroup.cusp (g := 0) (r := n + 1 + 1) j.castSucc)⁻¹ := by
  have h := Pi1.SurfaceGroup.relation (g := 0) (r := n + 1 + 1)
  rw [Pi1.SurfaceGen.ordProd_succ] at h
  simp only [Pi1.SurfaceGen.commProd, List.ofFn_zero, List.prod_nil, one_mul] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The index of the cuspidal generator of `Π_{0,n+2}` at a cusp `c` of `ℙ¹ ∖ (S ∪ {∞})`:
`σ a` for `c = a ∈ S`, `n + 1` for `c = ∞` (`none`). -/
def cuspIndex {α : Type*} {n : ℕ} (σ : α ≃ Fin (n + 1)) : Option α → Fin (n + 2)
  | some a => (σ a).castSucc
  | none => Fin.last (n + 1)

@[simp] lemma cuspIndex_some {α : Type*} {n : ℕ} (σ : α ≃ Fin (n + 1)) (a : α) :
    cuspIndex σ (some a) = (σ a).castSucc := rfl

@[simp] lemma cuspIndex_none {α : Type*} {n : ℕ} (σ : α ≃ Fin (n + 1)) :
    cuspIndex σ none = Fin.last (n + 1) := rfl

lemma neg_one_notMem_pts (n : ℕ) : (-1 : ℂ) ∉ pts n := fun hm ↦ by
  obtain ⟨i, -, hi, -⟩ := re_mem_pts hm
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  simp only [Complex.neg_re, Complex.one_re] at hi
  linarith

end Surface

/-! ### The main theorem -/

section Main

/-- **`π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞})) ≅ Π̂_{0,n+2}`, with the cuspidal generators fixing points of covers
with branches at the corresponding cusps.** For `k` countable algebraically closed of
characteristic `0`, `S ⊆ k` with `|S| = n + 1` and a geometric point `x` of
`U = ℙ¹ ∖ (S ∪ {∞})`, there are a numbering `σ : S ≃ Fin (n + 1)` and
`Θ : π₁ᵉᵗ(U, x) ≃ₜ* Π̂_{0,n+2}` such that for every cusp `c : Option S` (`none` is `∞`) and every
finite étale `Y ⟶ U` with a branch at `c` (relation `t = a + s` resp. `t s = 1`), the cuspidal
generator `c_{cuspIndex σ c}` acts on the fibre of `Y` at `x` with a fixed point. -/
theorem exists_continuousMulEquiv_lineS_branch {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [Countable k] (S : Finset k) {n : ℕ} (hS : S.card = n + 1) {L : Type} [Field L]
    [IsSepClosed L] (x : Spec (.of L) ⟶ Spec (.of (lineRingS S))) :
    ∃ (σ : S ≃ Fin (n + 1)) (Θ : π₁ᵉᵗ(x) ≃ₜ* Pi1.ProfiniteSurfaceGroup 0 (n + 2)),
      ∀ (c : Option S) (Y : AlgebraicGeometry.FiniteEtale (Spec (.of (lineRingS S)))),
        PBranch k (lineTS S) Y.hom (cuspP (c.map Subtype.val)) (cuspQ (c.map Subtype.val)) →
        ∃ y : (FiniteEtale.fiber x).obj Y,
          Θ.symm (etaFn _ (Pi1.SurfaceGroup.cusp (cuspIndex σ c))) • y = y := by
  classical
  obtain ⟨φ⟩ := Belyi.Converse.nonempty_ringHom_complex_of_countable k
  letI : Algebra k (ULift.{0} ℂ) := (ULift.ringEquiv.symm.toRingHom.comp φ).toAlgebra
  -- the image `S'` of `S` in `ℂ`, moved onto `{0, …, n}`
  have hinj : Function.Injective fun a : k ↦ (algebraMap k (ULift.{0} ℂ) a).down :=
    fun a b hab ↦ (algebraMap k (ULift.{0} ℂ)).injective (ULift.ext _ _ hab)
  have hS' : (imageS S).card = n + 1 := by
    rw [imageS, Finset.card_image_of_injective _ hinj, hS]
  obtain ⟨τ, hτ⟩ := exists_homeomorph_image_eq_pts (imageS S) hS'
  have hST : ∀ z, τ z ∈ pts n ↔ z ∈ imageS S := fun z ↦ by
    rw [← hτ, Finset.mem_image]
    exact ⟨fun ⟨a, ha, he⟩ ↦ τ.injective he ▸ ha, fun hz ↦ ⟨z, hz, rfl⟩⟩
  have hmem : ∀ a : S, τ (algebraMap k (ULift.{0} ℂ) a).down ∈ pts n := fun a ↦
    (hST _).2 (Finset.mem_image_of_mem _ a.2)
  let σf : S → Fin (n + 1) := fun a ↦ ptsEquiv n ⟨_, hmem a⟩
  have hσinj : Function.Injective σf := fun a b hab ↦ Subtype.ext (hinj (τ.injective
    (congrArg Subtype.val ((ptsEquiv n).injective hab))))
  let σ : S ≃ Fin (n + 1) := Equiv.ofBijective σf
    ((Fintype.bijective_iff_injective_and_card σf).2 ⟨hσinj, by simp [hS]⟩)
  have hσ : ∀ a : S, (((σ a : ℕ)) : ℂ) = τ (algebraMap k (ULift.{0} ℂ) a).down := fun a ↦
    coe_ptsEquiv n ⟨_, hmem a⟩
  -- the geometric basis of `π₁(ℂ ∖ {0, …, n})`, transported to `π₁(U_ℂ^an)`
  let e₂ := regionHomeo τ hST
  let x₀ : Region Set.univ (pts n) := ⟨-1, trivial, neg_one_notMem_pts n⟩
  obtain ⟨g, hl, hb, δ, hp⟩ := exists_basis_univ n (le_refl (rad n)) x₀ 0
  let xS := e₂.symm x₀
  let M₂ := homeoFundamentalGroupEquiv e₂ x₀
  let M₁ := homeoFundamentalGroupEquiv (lineHomeoS S) xS
  let xa := lineInvS S xS
  let ψ : FreeGroup (Fin (n + 1)) ≃* FundamentalGroup (Region Set.univ (pts n)) x₀ :=
    MulEquiv.ofBijective (FreeGroup.lift g) hb
  let ι : Pi1.SurfaceGroup 0 (n + 2) ≃* FundamentalGroup (analytification.obj (lineXS S)) xa :=
    (Pi1.SurfaceGroup.freeEquiv (g := 0) (r := n + 1)).trans
      ((FreeGroup.freeGroupCongr (surfaceGenEquivFin n)).trans (ψ.trans (M₂.trans M₁)))
  have hιj : ∀ i : Fin (n + 1), ι (Pi1.SurfaceGroup.cusp (g := 0) (r := n + 1 + 1) i.castSucc) =
      (M₂.trans M₁).toMonoidHom (g i) := by
    intro i
    simp only [ι, ψ, MulEquiv.trans_apply, Pi1.SurfaceGroup.freeEquiv_cusp_castSucc,
      FreeGroup.freeGroupCongr_apply, FreeGroup.map.of, surfaceGenEquivFin_c,
      MulEquiv.ofBijective_apply, FreeGroup.lift_apply_of]
    rfl
  have hιlast : ι (Pi1.SurfaceGroup.cusp (g := 0) (r := n + 1 + 1) (Fin.last (n + 1))) =
      (FundamentalGroup.map (lineInvS S) xS (M₂ (List.ofFn g).prod))⁻¹ := by
    rw [cusp_last_eq, map_inv]
    congr 1
    have e2 := Pi1.SurfaceGen.map_ordProd ι.toMonoidHom
      (fun j : Fin (n + 1) ↦ Pi1.SurfaceGroup.cusp (g := 0) (r := n + 1 + 1) j.castSucc)
    have e3 := Pi1.SurfaceGen.map_ordProd (M₂.trans M₁).toMonoidHom g
    refine e2.trans (Eq.trans ?_ e3.symm)
    exact congrArg (Pi1.SurfaceGen.ordProd (r := n + 1)) (funext hιj)
  have hnear : ∀ c : Option S, ∃ γ : FundamentalGroup (Region Set.univ (imageS S)) xS,
      IsNearLoop ((c.map Subtype.val).map fun a ↦ (algebraMap k (ULift.{0} ℂ) a).down) γ ∧
      (ι (Pi1.SurfaceGroup.cusp (cuspIndex σ c)) = FundamentalGroup.map (lineInvS S) xS γ ∨
        ι (Pi1.SurfaceGroup.cusp (cuspIndex σ c)) =
          (FundamentalGroup.map (lineInvS S) xS γ)⁻¹) := by
    rintro (_ | a)
    · exact ⟨M₂ (List.ofFn g).prod, isNearLoop_none_of_circ τ hST _ δ hp, Or.inr hιlast⟩
    · refine ⟨M₂ (g (σ a)), ?_, Or.inl (hιj (σ a))⟩
      have h := isNearLoop_of_isLoopAround τ hST (hl (σ a))
      rw [hσ a, Homeomorph.symm_apply_apply] at h
      exact h
  -- the chain of isomorphisms
  haveI : ConnectedSpace (lineXS S).obj.left :=
    inferInstanceAs (ConnectedSpace (Spec (.of (ULift.{0} ℂ ⊗[k] lineRingS S))))
  let ξ := geometricPoint (lineXS S) xa
  let bc := FiniteEtale.baseChangeSpec k (ULift.{0} ℂ) (lineRingS S)
  let Cmp := etaleFundamentalGroupEquivCompletion xa
  let Inv := FiniteEtale.fundamentalGroupBaseChangeEquiv (k := k) (Ω := ULift.{0} ℂ)
    (R := lineRingS S) ξ
  obtain ⟨α⟩ := nonempty_iso_of_fiberFunctor (FiniteEtale.fiber x) (FiniteEtale.fiber (ξ ≫ bc))
  let Bp := autContinuousMulEquivOfIso α
  let Θ : π₁ᵉᵗ(x) ≃ₜ* Pi1.ProfiniteSurfaceGroup 0 (n + 2) :=
    Bp.trans (Inv.symm.trans (Cmp.trans (Pi1.Profinite.completionCongr ι).symm))
  let Φ : FundamentalGroup (analytification.obj (lineXS S)) xa →* π₁ᵉᵗ(x) :=
    (α.conjAut.symm.toMonoidHom.comp (Inv.symm.symm.toMulEquiv.toMonoidHom.comp
      (Cmp.symm.toMulEquiv.toMonoidHom.comp
        (eta (GrpCat.of (FundamentalGroup (analytification.obj (lineXS S)) xa))).hom)))
  have hΘ : ∀ z : Pi1.SurfaceGroup 0 (n + 2), Θ.symm (etaFn _ z) = Φ (ι z) := by
    intro z
    change Bp.symm (Inv (Cmp.symm (Pi1.Profinite.completionCongr ι (etaFn _ z)))) = _
    rw [Pi1.Profinite.completionCongr_apply, Pi1.Profinite.completionMap_eta]
    rfl
  refine ⟨σ, Θ, fun c Y b ↦ ?_⟩
  obtain ⟨γ, hγnear, hγι⟩ := hnear c
  let Yc := (FiniteEtale.pullback bc).obj Y
  obtain ⟨e, he⟩ := exists_monodromy_fixed_of_pBranch (Y' := Yc) (c.map Subtype.val)
    (b.baseChange (ULift.{0} ℂ)) hγnear
  obtain ⟨y₁, hy₁⟩ := exists_fixed_etaleFundamentalGroupEquivCompletion xa _ Yc e he
  have hy₂ := fiberAutMap_fixed (FiniteEtale.pullbackFiberIso bc rfl)
    (Cmp.symm (etaFn _ (FundamentalGroup.map (lineInvS S) xS γ))) y₁ hy₁
  have hy₃ := exists_fixed_conjAut_symm α _ _ hy₂
  refine ⟨α.inv.app Y ((FiniteEtale.pullbackFiberIso bc rfl).hom.app Y y₁), ?_⟩
  have hΦ : Φ (FundamentalGroup.map (lineInvS S) xS γ) •
      α.inv.app Y ((FiniteEtale.pullbackFiberIso bc rfl).hom.app Y y₁) =
      α.inv.app Y ((FiniteEtale.pullbackFiberIso bc rfl).hom.app Y y₁) := hy₃
  refine (congrArg (· • _) (hΘ _)).trans ?_
  rcases hγι with h | h
  · exact (congrArg (fun z ↦ Φ z • _) h).trans hΦ
  · exact (congrArg (fun z ↦ Φ z • _) h).trans
      ((congrArg (· • _) (map_inv Φ _)).trans (inv_smul_eq_iff.2 hΦ.symm))

end Main

end CurvesJacobian.Cusp
