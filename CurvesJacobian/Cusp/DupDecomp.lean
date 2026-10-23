/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.DupSubgroup
import CurvesJacobian.Cusp.ArithDecomp
import CurvesJacobian.Cusp.FillStep

/-!
# The `[2]`-subgroup `Π_U ⊆ Π_{E∖O}` is preserved by isomorphisms ([AbsTopII] Cor 3.4, step G2)

Let `E` be an elliptic curve over a number field `K` with `K`-rational `E[2]`, `X = E ∖ {O}`,
`Π = Π_X ↠ G_K` with kernel `Δ`, and `Π_U = dupPiU` the image of `π₁(E ∖ E[2])` under `[2]`
(`DupSubgroup.lean`, where `Π_U ⊓ Δ = Δ^{(2)}` is proved). Here:

* **(G2a)** `exists_mem_commensurator_pr_eq₂`: for a hyperbolic curve with exactly one geometric
  cusp, the commensurator `D = Comm_Π(I)` of a cuspidal inertia group (its cuspidal decomposition
  group, `commensurator_arithInertia`) surjects onto `G_K`: given `g`, lift it to `τ₀` over
  `L₀ = K(X̄)`; the places `W` and `τ₀ W` lie over the unique geometric cusp, so they restrict to
  the same place of `L = K(X̄_Ω)` (`comap_algebraMap_eq_of_isCentredOn`) and are conjugate by
  `n ∈ Gal(K(X̄_Ω)^alg / L)` (`exists_algEquiv_comap_eq`), which acts through `Δ`; then
  `n⁻¹ τ₀ ∈ D_W` lies over `g`.
* **(G2b)** `commensurator_le_dupPiU₂`: every cuspidal decomposition group lies in `Π_U`. The
  `[2]`-cover is `B = K[E][1/ψ]` over `K[E]`; for `τ` over `L₀` the map `τ ∘ ε`
  (`ε : B → K(X̄_Ω)^alg` through `coverσ`) is another point of the fibre, hence `ε ∘ σ_T` for a
  translation `σ_T` by `E[2]` (`exists_sigma2_eq₂`, a degree count `[K(E) : [2]^* K(E)] = 4`).
  If `τ` fixes a place `W` lying over the place at infinity of the source `K(E)`, then `σ_T`
  fixes the place at infinity, and a translation by an affine point makes `x` regular at
  infinity, so `T = O` (`eq_zero_of_translateAut_preserves₂`): `τ` fixes `ε(B)`, and
  `arithAction τ ∈ Π_U` (`arithAction_mem_dupPiU_of_fix₂`, via `exists_coverPiHom_arithAction`).
  All cusp places are conjugate (one geometric cusp) and `Π_U` is normal, which gives every cusp.
* **(G2c)** `CuspidalExt.Iso.map_eq_of_cuspDecomp₂`: group theory: `Π_U = D · Δ^{(2)}`, and an
  isomorphism of cuspidal extensions maps cusps to cusps, commensurators to commensurators
  (`commensurator_map_mulEquiv`) and `Δ^{(2)}` to `Δ^{(2)}`.
* **`map_dupPiU`**: every isomorphism `Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of cuspidal extensions maps
  `Π_{U₁}` onto `Π_{U₂}`.

`Topics in Absolute Anabelian Geometry II.txt` l.4540–4600 (Cor 3.4).

The facts on the place at infinity of `K(E)` (`ordInftyVS₂`, `ordInfty_translateEndo_genX_sub₂`,
`ordInfty_mulByTwoEndo_genX₂`) follow `EllipticCurves.FunctionField.ValuationAtInfinity`,
`TranslationPlaceAtInfinity` and `MulByTwoPlaceAtInfinity` of the `elliptic-curves` package, whose
modules are not built in this project; they are re-derived from the built `ordInfty` calculus.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-! ### The group-theoretic step (G2c) -/

/-- **(G2c), one inclusion.** Let `H_A ⊆ Π_A` with `H_A ⊓ Δ_A = Δ_A^{(2)}`, containing the
commensurator `D` of a cuspidal inertia group `I₀` with `pr(D) = G_A`, and let `H_B ⊆ Π_B` contain
`Δ_B^{(2)}` and the commensurators of all cuspidal inertia groups. Then `Φ(H_A) ⊆ H_B`. -/
theorem _root_.Belyi.Anabelian.CuspidalExt.Iso.map_le_of_cuspDecomp₂ {A B : CuspidalExt.{u}}
    (Φ : A.Iso B) {HA : Subgroup A.Pi} {HB : Subgroup B.Pi}
    (hA : HA ⊓ A.Delta = dupSqClosure A.Delta) (hB : dupSqClosure B.Delta ≤ HB)
    {I₀ : Subgroup A.Pi} (hI₀ : I₀ ∈ A.cusps)
    (hsurj : ∀ y : A.G, ∃ d ∈ Subgroup.Commensurable.commensurator I₀, A.pr d = y)
    (hdA : Subgroup.Commensurable.commensurator I₀ ≤ HA)
    (hdB : ∀ I ∈ B.cusps, Subgroup.Commensurable.commensurator I ≤ HB) :
    HA.map Φ.pi.toMulEquiv.toMonoidHom ≤ HB := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, hd, hdx⟩ := hsurj (A.pr x)
  have hxd : x * d⁻¹ ∈ dupSqClosure A.Delta := by
    rw [← hA]
    refine Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (hdA hd)), ?_⟩
    change A.pr (x * d⁻¹) = 1
    rw [map_mul, map_inv, hdx, mul_inv_cancel]
  have h1' : Φ.pi (x * d⁻¹) ∈ dupSqClosure B.Delta := by
    rw [← Φ.map_dupSqClosure₂]
    exact ⟨_, hxd, rfl⟩
  have h2 : Φ.pi d ∈ HB := by
    refine hdB _ ((Φ.cusps_map I₀).1 hI₀) ?_
    rw [← commensurator_map_mulEquiv]
    exact ⟨d, hd, rfl⟩
  have e : Φ.pi x = Φ.pi (x * d⁻¹) * Φ.pi d := by rw [← map_mul, inv_mul_cancel_right]
  change Φ.pi x ∈ HB
  rw [e]
  exact mul_mem (hB h1') h2

/-- **(G2c)**: if on both sides `H ⊓ Δ = Δ^{(2)}`, `H` contains the commensurators of all cuspidal
inertia groups, and one of these commensurators surjects onto `G`, then `Φ(H_A) = H_B`. -/
theorem _root_.Belyi.Anabelian.CuspidalExt.Iso.map_eq_of_cuspDecomp₂ {A B : CuspidalExt.{u}}
    (Φ : A.Iso B) {HA : Subgroup A.Pi} {HB : Subgroup B.Pi}
    (hA : HA ⊓ A.Delta = dupSqClosure A.Delta) (hB : HB ⊓ B.Delta = dupSqClosure B.Delta)
    {I₀ : Subgroup A.Pi} (hI₀ : I₀ ∈ A.cusps)
    (hsurjA : ∀ y : A.G, ∃ d ∈ Subgroup.Commensurable.commensurator I₀, A.pr d = y)
    {J₀ : Subgroup B.Pi} (hJ₀ : J₀ ∈ B.cusps)
    (hsurjB : ∀ y : B.G, ∃ d ∈ Subgroup.Commensurable.commensurator J₀, B.pr d = y)
    (hdA : ∀ I ∈ A.cusps, Subgroup.Commensurable.commensurator I ≤ HA)
    (hdB : ∀ I ∈ B.cusps, Subgroup.Commensurable.commensurator I ≤ HB) :
    HA.map Φ.pi.toMulEquiv.toMonoidHom = HB := by
  refine le_antisymm (Φ.map_le_of_cuspDecomp₂ hA (hB.symm.le.trans inf_le_left) hI₀ hsurjA
    (hdA _ hI₀) hdB) ?_
  have h := Φ.symm.map_le_of_cuspDecomp₂ hB (hA.symm.le.trans inf_le_left) hJ₀ hsurjB
    (hdB _ hJ₀) hdA
  intro y hy
  exact ⟨Φ.pi.symm y, h ⟨y, hy, rfl⟩, Φ.pi.apply_symm_apply y⟩

/-! ### (G2a) A cuspidal decomposition group surjects onto `G_K` (one geometric cusp) -/

section G2a

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [NumberField K] [Algebra.IsAlgebraic K Ω] in
/-- Every place `V ⊇ Ω` is centred on the proper curve `X̄_Ω`. -/
lemma isCentredOn_top_geom₂ {V : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hkV : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ V) :
    haveI : Nonempty (⊤ : (geomCurve Ω C).Opens) :=
      ⟨⟨(Nonempty.some (inferInstance : Nonempty (geomOpen Ω C))).1, trivial⟩⟩
    IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C)) ⊤
      V := by
  haveI : Nonempty (⊤ : (geomCurve Ω C).Opens) :=
    ⟨⟨(Nonempty.some (inferInstance : Nonempty (geomOpen Ω C))).1, trivial⟩⟩
  by_contra h
  obtain ⟨z, hz, -⟩ := exists_notMem_of_not_isCentredOn (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveEquivL_algebraMap Ω (transcendental_geomCoord Ω C)) ⊤ hkV h
  exact hz trivial

/-- **One geometric cusp**: two places over cusps restrict to the same place of
`L = K(X̄_Ω)`. -/
lemma comap_L_eq_of_isCuspPlace₂
    (h1 : ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)).Subsingleton)
    {W W' : ValuationSubring (FFClosure (geomCurve Ω C))} (hW : IsCuspPlace Ω C hc W)
    (hW' : IsCuspPlace Ω C hc W') :
    W.comap (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C))) =
      W'.comap (algebraMap (geomData Ω C).L (FFClosure (geomCurve Ω C))) := by
  haveI : Nonempty (⊤ : (geomCurve Ω C).Opens) :=
    ⟨⟨(Nonempty.some (inferInstance : Nonempty (geomOpen Ω C))).1, trivial⟩⟩
  have hU : ∀ {V}, IsCuspPlace Ω C hc V → ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) V :=
    fun hV h ↦ hV.2 ((isCentredOn_geomOpen_iff Ω C hc _).1 h).2
  exact comap_algebraMap_eq_of_isCentredOn (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveEquivL_algebraMap Ω (transcendental_geomCoord Ω C)) (by simp)
    (h1.anti fun _ hx ↦ hx.2) (isCentredOn_top_geom₂ Ω C hW.1) (hU hW)
    (isCentredOn_top_geom₂ Ω C hW'.1) (hU hW')

/-- **Places over the unique geometric cusp are conjugate under `Gal(K(X̄_Ω)^alg / K(X̄_Ω))`**,
by an element `n` over `L₀` whose image in `Π_U` lies in `Δ_U`. -/
theorem exists_comap_eq_of_isCuspPlace₂
    (h1 : ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)).Subsingleton)
    {W W' : ValuationSubring (FFClosure (geomCurve Ω C))} (hW : IsCuspPlace Ω C hc W)
    (hW' : IsCuspPlace Ω C hc W') :
    ∃ n : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C),
      projGk Ω C hc (arithAction Ω C hc n) = 1 ∧
        W' = W.comap (n.symm : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C)) := by
  have hL := comap_L_eq_of_isCuspPlace₂ Ω C hc h1 hW hW'
  haveI : IsGalois (geomData Ω C).L (FFClosure (geomCurve Ω C)) :=
    IsGalois.tower_top_of_isGalois (K₀ Ω (coordT (geomCoord Ω C))) (geomData Ω C).L
      (FFClosure (geomCurve Ω C))
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comap_eq W W' hL
  have hσL : σ.restrictScalars (K₀ Ω (coordT (geomCoord Ω C))) ∈ (geomData Ω C).HL := by
    have hcl : IsClosed ((geomData Ω C).HL : Set (FFClosure (geomCurve Ω C) ≃ₐ[K₀ Ω
        (coordT (geomCoord Ω C))] FFClosure (geomCurve Ω C))) := (geomData Ω C).isClosed_HL
    have h := InfiniteGalois.fixingSubgroup_fixedField
      (⟨(geomData Ω C).HL, hcl⟩ : ClosedSubgroup _)
    change σ.restrictScalars _ ∈ (⟨(geomData Ω C).HL, hcl⟩ : ClosedSubgroup _).toSubgroup
    rw [← h, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  refine ⟨toArithAut Ω C hc ⟨σ.restrictScalars _, (geomData Ω C).le hσL⟩, ?_, ?_⟩
  · rw [← geomToPi_chartHom]
    exact geomToPi_mem_ker Ω C hc _
  · have hinv : ∀ z, (toArithAut Ω C hc ⟨σ.restrictScalars _, (geomData Ω C).le hσL⟩).symm z =
        σ.symm z := fun z ↦ by
      apply (toArithAut Ω C hc ⟨σ.restrictScalars _, (geomData Ω C).le hσL⟩).injective
      rw [AlgEquiv.apply_symm_apply]
      exact (σ.apply_symm_apply z).symm
    rw [hσ]
    ext z
    simp only [ValuationSubring.mem_comap, RingHom.coe_coe, hinv]

/-- **(G2a), place form**: if `X̄_Ω ∖ U_Ω` has at most one point, the decomposition group
`D_W ⊆ Π_U` of a place `W` over the cusp surjects onto `G_K`. -/
theorem exists_mem_arithDecomp_projGk_eq₂
    (h1 : ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)).Subsingleton)
    {W : ValuationSubring (FFClosure (geomCurve Ω C))} (hW : IsCuspPlace Ω C hc W)
    (y : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) :
    ∃ d ∈ arithDecomp Ω C hc W, projGk Ω C hc d = y := by
  obtain ⟨g, hg⟩ := projGk_surjective Ω C hc y
  obtain ⟨τ₀, rfl⟩ := arithAction_surjective Ω C hc g
  obtain ⟨n, hpr, hn⟩ := exists_comap_eq_of_isCuspPlace₂ Ω C hc h1 hW
    (isCuspPlace_comap Ω C hc τ₀.symm hW)
  refine ⟨arithAction Ω C hc (n⁻¹ * τ₀), ⟨_, fun x ↦ ?_, rfl⟩, ?_⟩
  · have h2 := SetLike.ext_iff.1 hn (τ₀ x)
    simp only [ValuationSubring.mem_comap, RingHom.coe_coe, AlgEquiv.symm_apply_apply] at h2
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, ← h2]
  · simp only [map_mul, map_inv, hpr, inv_one, one_mul, hg]

/-- `Π_U` has a cuspidal inertia group (a place over a cusp exists). -/
theorem exists_isCuspPlace₂ : ∃ W, IsCuspPlace Ω C hc W := by
  obtain ⟨x, hx⟩ := compl_nonempty_baseChangeOpen K Ω hc
  haveI : Nonempty (⊤ : (geomCurve Ω C).Opens) :=
    ⟨⟨(Nonempty.some (inferInstance : Nonempty (geomOpen Ω C))).1, trivial⟩⟩
  obtain ⟨W, -, hWV, hWU⟩ := exists_isCentredOn_not_isCentredOn (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveEquivL_algebraMap Ω (transcendental_geomCoord Ω C)) (V := ⊤)
    (compl_finite_baseChangeOpen K Ω C.nonempty) trivial hx
  exact ⟨W, hWV.1, fun h ↦ hWU ((isCentredOn_geomOpen_iff Ω C hc W).2 ⟨hWV.1, h⟩)⟩

/-- **(G2a)**: if `X̄_Ω ∖ U_Ω` has at most one point, the commensurator of every cuspidal inertia
group of `Π_U` (its cuspidal decomposition group) surjects onto `G_K`. -/
theorem exists_mem_commensurator_pr_eq₂
    (h1 : ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)).Subsingleton)
    {I} (hI : I ∈ (arithmeticExt Ω C hc).cusps) (y : (arithmeticExt Ω C hc).G) :
    ∃ d ∈ Subgroup.Commensurable.commensurator I, (arithmeticExt Ω C hc).pr d = y := by
  obtain ⟨W, hW, rfl⟩ := (mem_arithCusps_iff Ω C hc).1 hI
  rw [commensurator_arithInertia Ω C hc hW]
  exact exists_mem_arithDecomp_projGk_eq₂ Ω C hc h1 hW y

/-- A cuspidal inertia group exists. -/
theorem exists_mem_cusps₂ : ∃ I, I ∈ (arithmeticExt Ω C hc).cusps := by
  obtain ⟨W, hW⟩ := exists_isCuspPlace₂ Ω C hc
  exact ⟨_, (mem_arithCusps_iff Ω C hc).2 ⟨W, hW, rfl⟩⟩

end G2a

/-! ### The place at infinity of `K(E)` (after `EllipticCurves.FunctionField`)

`ValuationAtInfinity`, `TranslationPlaceAtInfinity` and `MulByTwoPlaceAtInfinity` of the
`elliptic-curves` package are not among the built modules, so the three facts needed here are
re-derived from the (built) `ordInfty` calculus of `PlaceAtInfinity`, following those files. -/

section Infinity

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

variable (W) in
/-- The place at infinity of `F(W)`, as a valuation subring (`ordInfty ≥ 0`). -/
def ordInftyVS₂ : ValuationSubring W.FunctionField where
  carrier := {f | 0 ≤ ordInfty W f}
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    rcases eq_or_ne g 0 with rfl | hg0
    · simp
    rw [ordInfty_mul hf0 hg0]; omega
  one_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    rcases eq_or_ne f 0 with rfl | hf0
    · simpa using hg
    rcases eq_or_ne g 0 with rfl | hg0
    · simpa using hf
    rcases eq_or_ne (f + g) 0 with h | h
    · simp [h]
    have := le_ordInfty_add hf0 hg0 h
    omega
  zero_mem' := by simp
  neg_mem' := by
    intro f hf
    simp only [Set.mem_setOf_eq] at *
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    have : (-f) = algebraMap F W.FunctionField (-1) * f := by simp
    rw [this, ordInfty_mul (by simp) hf0, ordInfty_algebraMap_base (by norm_num : (-1 : F) ≠ 0)]
    omega
  mem_or_inv_mem' := by
    intro f
    simp only [Set.mem_setOf_eq]
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    rw [ordInfty_inv]
    omega

lemma mem_ordInftyVS₂ {f : W.FunctionField} : f ∈ ordInftyVS₂ W ↔ 0 ≤ ordInfty W f := Iff.rfl

lemma algebraMap_mem_ordInftyVS₂ (c : F) : algebraMap F W.FunctionField c ∈ ordInftyVS₂ W := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  simp [mem_ordInftyVS₂, ordInfty_algebraMap_base hc]

lemma genX_notMem_ordInftyVS₂ : genX W ∉ ordInftyVS₂ W := by
  simp [mem_ordInftyVS₂, ordInfty_genX]

lemma ordInfty_le_of_div_mem₂ {u g : W.FunctionField} (hu : u ≠ 0) (hu0 : ordInfty W u ≤ 0)
    (h : g / u ∈ ordInftyVS₂ W) : ordInfty W u ≤ ordInfty W g := by
  rcases eq_or_ne g 0 with rfl | hg
  · simpa using hu0
  · rw [mem_ordInftyVS₂, ordInfty_div hg hu] at h
    omega

lemma neg_three_le_ordInfty_linear₂ (c₀ c₁ c₂ : F) :
    (-3 : ℤ) ≤ ordInfty W (algebraMap F W.FunctionField c₀
      + algebraMap F W.FunctionField c₁ * genX W + algebraMap F W.FunctionField c₂ * genY W) := by
  have hY : genY W ≠ 0 := genY_ne_zero
  have hmem : (algebraMap F W.FunctionField c₀ + algebraMap F W.FunctionField c₁ * genX W
      + algebraMap F W.FunctionField c₂ * genY W) / genY W ∈ ordInftyVS₂ W := by
    have hrw : (algebraMap F W.FunctionField c₀ + algebraMap F W.FunctionField c₁ * genX W
        + algebraMap F W.FunctionField c₂ * genY W) / genY W
        = algebraMap F W.FunctionField c₀ * (genY W)⁻¹
          + algebraMap F W.FunctionField c₁ * (genX W / genY W)
          + algebraMap F W.FunctionField c₂ := by
      field_simp
    rw [hrw]
    refine add_mem (add_mem (mul_mem (algebraMap_mem_ordInftyVS₂ _) ?_)
        (mul_mem (algebraMap_mem_ordInftyVS₂ _) ?_))
      (algebraMap_mem_ordInftyVS₂ _)
    · simp [mem_ordInftyVS₂, ordInfty_inv]
    · simp [mem_ordInftyVS₂, ordInfty_genX_div_genY]
  have hle := ordInfty_le_of_div_mem₂ hY (by simp) hmem
  rwa [ordInfty_genY] at hle

lemma ordInfty_genX_sub₂ (x₂ : F) :
    ordInfty W (genX W - algebraMap F W.FunctionField x₂) = -2 := by
  have hgen : genX W - algebraMap F W.FunctionField x₂ = genPsi W (XClass W x₂) := by
    rw [XClass, Polynomial.C_sub, map_sub, map_sub, ← genX, ← genPsi_mk_CC (W := W) x₂]
  rw [hgen, genPsi, ordInfty_algebraMap (XClass_ne_zero x₂), XClass, deg_mk_C,
    Polynomial.natDegree_X_sub_C]
  norm_num

variable [W.IsElliptic] {x₂ y₂ : F}

open Classical in
lemma translateEndo_genX_sub_mul_sq₂ (h₂ : W.Equation x₂ y₂) :
    (translateEndo h₂ (genX W) - algebraMap F W.FunctionField x₂)
        * (genX W - algebraMap F W.FunctionField x₂) ^ 2
      = algebraMap F W.FunctionField (y₂ ^ 2 - 2 * x₂ ^ 3 + W.a₆ - W.a₂ * x₂ ^ 2 + W.a₁ * x₂ * y₂)
        + algebraMap F W.FunctionField (3 * x₂ ^ 2 + W.a₄ + 2 * W.a₂ * x₂ - W.a₁ * y₂) * genX W
        + algebraMap F W.FunctionField (-2 * y₂ - W.a₃ - W.a₁ * x₂) * genY W := by
  have hne : genX W ≠ algebraMap F W.FunctionField x₂ := genX_ne x₂
  have hd : genX W - algebraMap F W.FunctionField x₂ ≠ 0 := sub_ne_zero_of_ne hne
  have hs : (W.map (algebraMap F W.FunctionField)).slope (genX W)
        (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)
        * (genX W - algebraMap F W.FunctionField x₂)
      = genY W - algebraMap F W.FunctionField y₂ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hne, div_mul_cancel₀ _ hd]
  have hgen := equation_gen (W := W)
  rw [WeierstrassCurve.Affine.equation_iff] at hgen
  rw [translateEndo_genX h₂]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hgen ⊢
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]
  linear_combination ((W.map (algebraMap F W.FunctionField)).slope (genX W)
      (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)
      * (genX W - algebraMap F W.FunctionField x₂)
    + (genY W - algebraMap F W.FunctionField y₂)
    + algebraMap F W.FunctionField W.a₁ * (genX W - algebraMap F W.FunctionField x₂)) * hs + hgen

/-- **Translation by an affine point makes `x` regular at infinity.** -/
lemma ordInfty_translateEndo_genX_sub₂ (h₂ : W.Equation x₂ y₂) :
    1 ≤ ordInfty W (translateEndo h₂ (genX W) - algebraMap F W.FunctionField x₂) := by
  have hne : genX W ≠ algebraMap F W.FunctionField x₂ := genX_ne x₂
  have hd : genX W - algebraMap F W.FunctionField x₂ ≠ 0 := sub_ne_zero_of_ne hne
  have hdord : ordInfty W (genX W - algebraMap F W.FunctionField x₂) = -2 := ordInfty_genX_sub₂ x₂
  have hsub : translateEndo h₂ (genX W) - algebraMap F W.FunctionField x₂ ≠ 0 :=
    sub_ne_zero_of_ne (translateEndo_genX_ne h₂ x₂)
  have hkey := translateEndo_genX_sub_mul_sq₂ h₂
  have hbound := neg_three_le_ordInfty_linear₂ (W := W)
    (y₂ ^ 2 - 2 * x₂ ^ 3 + W.a₆ - W.a₂ * x₂ ^ 2 + W.a₁ * x₂ * y₂)
    (3 * x₂ ^ 2 + W.a₄ + 2 * W.a₂ * x₂ - W.a₁ * y₂) (-2 * y₂ - W.a₃ - W.a₁ * x₂)
  rw [← hkey, ordInfty_mul hsub (pow_ne_zero 2 hd), ordInfty_pow, hdord] at hbound
  omega

omit [W.IsElliptic] in
lemma genPsi_mk_C_eq_eval_map₂ (q : F[X]) :
    genPsi W (mk W (C q)) = (q.map (algebraMap F W.FunctionField)).eval (genX W) := by
  rw [genPsi_mk_map_evalEval, Polynomial.map_C, coe_mapRingHom, evalEval_C]

omit [W.IsElliptic] in
lemma eval_map_genX_ne_zero₂ {q : F[X]} (hq : q ≠ 0) :
    (q.map (algebraMap F W.FunctionField)).eval (genX W) ≠ 0 := by
  rw [← genPsi_mk_C_eq_eval_map₂]
  exact fun h => mk_C_ne_zero hq
    ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ h)

omit [W.IsElliptic] in
lemma ordInfty_eval_map_genX₂ {q : F[X]} (hq : q ≠ 0) :
    ordInfty W ((q.map (algebraMap F W.FunctionField)).eval (genX W))
      = -(2 * q.natDegree : ℤ) := by
  rw [← genPsi_mk_C_eq_eval_map₂, genPsi, ordInfty_algebraMap (mk_C_ne_zero hq), deg_mk_C]
  push_cast
  ring

omit [W.IsElliptic] in
/-- **`x ∘ [2]` has a double pole at infinity.** -/
lemma ordInfty_mulByTwoEndo_genX₂ (h2 : (2 : F) ≠ 0) :
    ordInfty W (mulByTwoEndo h2 (genX W)) = -2 := by
  have h4 : (4 : F) ≠ 0 := by
    have h : (4 : F) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  have hΦ : ((W.map (algebraMap F W.FunctionField)).Φ 2)
      = (W.Φ 2).map (algebraMap F W.FunctionField) := WeierstrassCurve.map_Φ ..
  have hΨ : ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq)
      = W.Ψ₂Sq.map (algebraMap F W.FunctionField) := WeierstrassCurve.map_Ψ₂Sq ..
  rw [mulByTwoEndo_genX h2, hΦ, hΨ,
    ordInfty_div (eval_map_genX_ne_zero₂ (W.Φ_ne_zero 2))
      (eval_map_genX_ne_zero₂ (W.Ψ₂Sq_ne_zero h4)),
    ordInfty_eval_map_genX₂ (W.Φ_ne_zero 2), ordInfty_eval_map_genX₂ (W.Ψ₂Sq_ne_zero h4),
    W.natDegree_Φ 2, W.natDegree_Ψ₂Sq h4]
  decide

end Infinity

/-! ### (G2b), field-theoretic part: the fibre of `[2]` over the place at infinity -/

section Fibre

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [Field K] [CharZero K] {E : WeierstrassCurve K} [E.IsElliptic]
  {e₁ e₂ e₃ : K} (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))

local notation "A" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField

/-- A map `ρ : B = K[E][1/ψ] → L` into a field which is injective on `[2]^* K[E]` is injective. -/
lemma injective_of_comp_dupHom₂ {L : Type*} [Field L] (ρ : coverRingE E →+* L)
    (h : Function.Injective (ρ.comp (dupHom E))) : Function.Injective ρ :=
  injective_of_isIntegral (dupHom E) (dupHom_isIntegral E) ρ h

/-- Two maps `B → L` agreeing on `[2]^* K[E]` have extensions to `K(E)` agreeing on
`[2]^* K(E)`. -/
lemma lift_mulByTwoEndo₂ {L : Type*} [Field L] (ρ ρ' : coverRingE E →+* L)
    (hρ : Function.Injective (ρ.comp (dupHom E))) (hρ' : Function.Injective (ρ'.comp (dupHom E)))
    (h : ρ.comp (dupHom E) = ρ'.comp (dupHom E)) (u : FF) :
    IsFractionRing.lift (injective_of_comp_dupHom₂ ρ hρ) (mulByTwoEndo two_ne_zero u) =
      IsFractionRing.lift (injective_of_comp_dupHom₂ ρ' hρ') (mulByTwoEndo two_ne_zero u) := by
  have : (IsFractionRing.lift (injective_of_comp_dupHom₂ ρ hρ)).comp
      (mulByTwoEndo (W := E.toAffine) two_ne_zero) =
      (IsFractionRing.lift (injective_of_comp_dupHom₂ ρ' hρ')).comp
        (mulByTwoEndo (W := E.toAffine) two_ne_zero) :=
    IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← algebraMap_dupHom E a, IsFractionRing.lift_algebraMap,
        IsFractionRing.lift_algebraMap]
      exact RingHom.congr_fun h a)
  exact RingHom.congr_fun this u

/-- **The fibre of `[2]` has exactly the four translates**: if `ρ, ε : B → L` agree on
`[2]^* K[E]` (and are injective there), then `ρ = ε ∘ σ_i` for a translation `σ_i` by `E[2]`. -/
theorem exists_sigma2_eq₂ {L : Type*} [Field L] (ε ρ : coverRingE E →+* L)
    (hε : Function.Injective (ε.comp (dupHom E))) (h : ρ.comp (dupHom E) = ε.comp (dupHom E)) :
    ∃ i, ρ = ε.comp (sigma2 he i).toRingHom := by
  set L' := (mulByTwoEndoAlgHom (W := E.toAffine) two_ne_zero).fieldRange
  have hεi := injective_of_comp_dupHom₂ ε hε
  letI : Algebra L' L := ((IsFractionRing.lift hεi).comp (algebraMap L' FF)).toAlgebra
  have hdeg : Module.finrank L' FF = 4 := finrank_mulByTwoFieldRange two_ne_zero
  haveI : Module.Free L' FF := Module.Free.of_divisionRing L' FF
  haveI : Module.Finite L' FF := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  have hSinj : ∀ ρ' : {ρ' : coverRingE E →+* L // ρ'.comp (dupHom E) = ε.comp (dupHom E)},
      Function.Injective (ρ'.1.comp (dupHom E)) := fun ρ' ↦ by rw [ρ'.2]; exact hε
  let Φ : {ρ' : coverRingE E →+* L // ρ'.comp (dupHom E) = ε.comp (dupHom E)} →
      (FF →ₐ[L'] L) := fun ρ' ↦
    { IsFractionRing.lift (injective_of_comp_dupHom₂ ρ'.1 (hSinj ρ')) with
      commutes' := fun l ↦ by
        obtain ⟨u, hu⟩ := AlgHom.mem_fieldRange.1 l.2
        change IsFractionRing.lift (injective_of_comp_dupHom₂ ρ'.1 (hSinj ρ')) (l : FF) =
          IsFractionRing.lift hεi (l : FF)
        rw [← hu]
        exact lift_mulByTwoEndo₂ ρ'.1 ε (hSinj ρ') hε ρ'.2 u }
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ hg
    refine Subtype.ext (RingHom.ext fun b ↦ ?_)
    have h' := DFunLike.congr_fun hg (algebraMap (coverRingE E) FF b)
    have e : ∀ g, (Φ g) (algebraMap (coverRingE E) FF b) = g.1 b := fun g ↦
      IsFractionRing.lift_algebraMap (injective_of_comp_dupHom₂ g.1 (hSinj g)) b
    rwa [e, e] at h'
  haveI : Finite {ρ' : coverRingE E →+* L // ρ'.comp (dupHom E) = ε.comp (dupHom E)} :=
    Finite.of_injective Φ hΦ
  have hcard : Nat.card {ρ' : coverRingE E →+* L // ρ'.comp (dupHom E) = ε.comp (dupHom E)} ≤
      4 := (Nat.card_le_card_of_injective Φ hΦ).trans
    ((card_algHom_le_finrank L' FF L).trans hdeg.le)
  let ψ : Fin 4 → {ρ' : coverRingE E →+* L // ρ'.comp (dupHom E) = ε.comp (dupHom E)} :=
    fun i ↦ ⟨ε.comp (sigma2 he i).toRingHom, RingHom.ext fun a ↦ by
      change ε (sigma2 he i (dupHom E a)) = ε (dupHom E a)
      rw [sigma2_dupHom]⟩
  have hψ : Function.Injective ψ := fun i j hij ↦ sigma2_injective he
    (RingEquiv.ext fun b ↦ hεi (RingHom.congr_fun (congrArg Subtype.val hij) b))
  obtain ⟨i, hi⟩ := (hψ.bijective_of_nat_card_le (by simpa using hcard)).2 ⟨ρ, h⟩
  exact ⟨i, (congrArg Subtype.val hi).symm⟩

omit [CharZero K] in
/-- **A translation preserving the place at infinity is trivial** (translation by an affine
point `T` makes `x` regular at infinity, `ordInfty_translateEndo_genX_sub`). -/
lemma eq_zero_of_translateAut_preserves₂ (P : E.toAffine.Point)
    (h : ∀ f : FF, translateAut P f ∈ ordInftyVS₂ E.toAffine ↔
      f ∈ ordInftyVS₂ E.toAffine) : P = 0 := by
  rcases P with _ | ⟨x₂, y₂, hP⟩
  · rfl
  · exfalso
    have h1 := ordInfty_translateEndo_genX_sub₂ hP.left
    have hc : algebraMap K FF x₂ ∈ ordInftyVS₂ E.toAffine :=
      algebraMap_mem_ordInftyVS₂ x₂
    have hd : translateEndo hP.left (genX E.toAffine) - algebraMap K FF x₂ ∈
        ordInftyVS₂ E.toAffine := mem_ordInftyVS₂.2 (by omega)
    have h2 : translateAut (.some x₂ y₂ hP) (genX E.toAffine) ∈
        ordInftyVS₂ E.toAffine := by
      rw [translateAut_apply_some]
      simpa using add_mem hd hc
    exact genX_notMem_ordInftyVS₂ ((h _).1 h2)

lemma sigma2_zero₂ (b : coverRingE E) : sigma2 he 0 b = b := by
  apply IsFractionRing.injective (coverRingE E) FF
  have h1 := algebraMap_restrictRingEquiv (dupHom E) (dupHom_isIntegral E)
    (tau2 he 0).toRingEquiv (tau2_dupHom he 0) b
  change algebraMap _ FF (restrictRingEquiv _ _ _ _ b) = _
  rw [h1]
  rfl

include he in
/-- **(G2b), field form.** Let `ε : B → L` be injective on `[2]^* K[E]`, `W ⊆ L` a valuation
subring lying over the place at infinity of the source `K(E)` (via the extension of `ε`), and
`τ` an automorphism of `L` fixing `ε([2]^* K[E])` and preserving `W`. Then `τ` fixes `ε(B)`:
the place at infinity splits completely in `[2]` (`E[2]` is rational), so the decomposition
group of `W` acts trivially on the cover. -/
theorem apply_eq_of_preserves₂ {L : Type*} [Field L] (ε : coverRingE E →+* L)
    (hε : Function.Injective (ε.comp (dupHom E))) (εL : FF →+* L)
    (hεL : ∀ b, εL (algebraMap (coverRingE E) FF b) = ε b) (τ : L ≃+* L)
    (hτ : ∀ a, τ (ε (dupHom E a)) = ε (dupHom E a)) (W : ValuationSubring L)
    (hW : W.comap εL = ordInftyVS₂ E.toAffine)
    (hτW : ∀ z, τ z ∈ W ↔ z ∈ W) (b : coverRingE E) : τ (ε b) = ε b := by
  obtain ⟨i, hi⟩ := exists_sigma2_eq₂ he ε (τ.toRingHom.comp ε) hε
    (RingHom.ext fun a ↦ hτ a)
  have hL : τ.toRingHom.comp εL = εL.comp (tau2 he i).toRingEquiv.toRingHom :=
    IsLocalization.ringHom_ext (nonZeroDivisors (coverRingE E)) (RingHom.ext fun c ↦ by
      have e1 := RingHom.congr_fun hi c
      have e2 := algebraMap_restrictRingEquiv (dupHom E) (dupHom_isIntegral E)
        (tau2 he i).toRingEquiv (tau2_dupHom he i) c
      change τ (εL (algebraMap (coverRingE E) FF c)) =
        εL ((tau2 he i).toRingEquiv (algebraMap (coverRingE E) FF c))
      rw [← e2, hεL, hεL]
      exact e1)
  have hpres : ∀ f : FF, tau2 he i f ∈ ordInftyVS₂ E.toAffine ↔
      f ∈ ordInftyVS₂ E.toAffine := fun f ↦ by
    have e3 : τ (εL f) = εL (tau2 he i f) := RingHom.congr_fun hL f
    rw [← hW, ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← hτW (εL f), e3]
  have hi0 : i = 0 := twoTorsionPt_injective he
    ((eq_zero_of_translateAut_preserves₂ (twoTorsionPt he i) hpres).trans rfl)
  subst hi0
  have e4 := RingHom.congr_fun hi b
  change τ (ε b) = ε (sigma2 he 0 b) at e4
  rw [e4, sigma2_zero₂]

end Fibre

/-! ### (G2b) The cuspidal decomposition groups of `Π_{E∖O}` lie in `Π_U` -/

/-- **Extension of places**: every valuation subring of `k` is the restriction of a valuation
subring of `L` along a field map `k → L`. -/
lemma exists_valuationSubring_comap_eq₂ {k L : Type*} [Field k] [Field L] (f : k →+* L)
    (O : ValuationSubring k) : ∃ W : ValuationSubring L, W.comap f = O := by
  let g : O →+* L := f.comp O.subtype
  obtain ⟨W, hW⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range g)
  obtain ⟨hle, hloc⟩ := hW
  refine ⟨W, le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ hle ⟨⟨x, hx⟩, rfl⟩)⟩
  by_contra hxO
  have hx0 : x ≠ 0 := by rintro rfl; exact hxO O.zero_mem
  have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  let a : (LocalSubring.range g).toSubring := ⟨g ⟨x⁻¹, hinv⟩, ⟨⟨x⁻¹, hinv⟩, rfl⟩⟩
  have hfx : f x⁻¹ * f x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have hunit : IsUnit (Subring.inclusion hle a) := by
    refine IsUnit.of_mul_eq_one ⟨f x, hx⟩ (Subtype.ext ?_)
    exact hfx
  obtain ⟨b, hb⟩ := (isUnit_of_map_unit _ a hunit).exists_right_inv
  obtain ⟨⟨c, hc⟩, hcb⟩ := b.2
  apply hxO
  have hval : f x⁻¹ * f c = 1 := by
    have h1 := congrArg Subtype.val hb
    have h2 : (b : L) = f c := hcb.symm
    simp only [Subring.coe_mul, Subring.coe_one] at h1
    rw [← h2]
    exact h1
  have hcx : c = x := by
    apply f.injective
    have hne : f x⁻¹ ≠ 0 := by
      intro h; rw [h, zero_mul] at hfx; exact zero_ne_one hfx
    exact mul_left_cancel₀ hne (hval.trans hfx.symm)
  rw [← hcx]
  exact hc

section G2b

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (E : WeierstrassCurve K) [E.IsElliptic]

attribute [local instance] isAlgClosure_of_isAlgebraic

local notation "A" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `X_Ω = (E ∖ O)_Ω` has (at most) one cusp. -/
lemma subsingleton_compl_geomOpen_XE₂ : ((geomOpen Ω (hypCurveX E) :
    Set (geomCurve Ω (hypCurveX E)))ᶜ : Set (geomCurve Ω (hypCurveX E))).Subsingleton := by
  have := card_compl_baseChangeOpen_XE E Ω
  rw [Nat.card_eq_one_iff_unique] at this
  exact fun a ha b hb ↦ congrArg Subtype.val (this.1.elim ⟨a, ha⟩ ⟨b, hb⟩)

/-- **(G2a) for `E ∖ {O}`**: some cuspidal decomposition group surjects onto `G_K`. -/
theorem exists_cusp_commensurator_surj₂ :
    ∃ I ∈ (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).cusps,
      ∀ y, ∃ d ∈ Subgroup.Commensurable.commensurator I,
        (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).pr d = y := by
  obtain ⟨I, hI⟩ := exists_mem_cusps₂ Ω (hypCurveX E) (compl_XE_nonempty E)
  exact ⟨I, hI, exists_mem_commensurator_pr_eq₂ Ω (hypCurveX E) (compl_XE_nonempty E)
    (subsingleton_compl_geomOpen_XE₂ Ω E) hI⟩

/-- `σ : K(X̄_Ω)^alg ≅ K(V̄_Ω)^alg` over `[2]^* : L₀(X) → L₀(V)`. -/
abbrev dupσ₂ :
    FFClosure (geomCurve Ω (hypCurveX E)) ≃+* FFClosure (geomCurve Ω (hypCurveV E)) :=
  coverσ Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E) (coverXMorK E)

/-- `ε : B = Γ(E ∖ E[2]) → K(X̄_Ω)^alg`, the embedding through `σ⁻¹`. -/
def dupEps₂ : coverRingE E →+* FFClosure (geomCurve Ω (hypCurveX E)) :=
  (dupσ₂ Ω E).symm.toRingHom.comp ((secEmb Ω (hypCurveV E)
    (isAffineOpen_U (hypCurveV E) (hcV_dup E))).comp (sectionsVEEquiv E).symm.toRingHom)

/-- `κ : K[E] = Γ(E ∖ O) → L₀ ⊆ K(X̄_Ω)^alg`. -/
def dupKappa₂ : A →+* FFClosure (geomCurve Ω (hypCurveX E)) :=
  (secEmb Ω (hypCurveX E) (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E))).comp
    (sectionsXEAlgEquiv E).symm.toRingEquiv.toRingHom

lemma coverRing_coverXMorK₂ :
    coverRing (hypCurveX E) (hypCurveV E) (coverXMorK E) = coverXHom E := by
  have h : CommRingCat.ofHom (coverRing (hypCurveX E) (hypCurveV E) (coverXMorK E)) =
      CommRingCat.ofHom (coverXHom E) :=
    Spec.map_injective (specMap_coverRing (hypCurveX E) (hypCurveV E) (coverXMorK E))
  exact congrArg CommRingCat.Hom.hom h

lemma dupEps_dupHom₂ (a : A) : dupEps₂ Ω E (dupHom E a) = dupKappa₂ Ω E a := by
  have h := coverσ_secEmb Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
    (coverXMorK E) ((sectionsXEAlgEquiv E).symm a)
  have hr : coverRing (hypCurveX E) (hypCurveV E) (coverXMorK E) ((sectionsXEAlgEquiv E).symm a) =
      (sectionsVEEquiv E).symm (dupHom E a) := by
    rw [coverRing_coverXMorK₂]
    change (sectionsVEEquiv E).symm (dupHom E (sectionsXEAlgEquiv E
      ((sectionsXEAlgEquiv E).symm a))) = _
    rw [AlgEquiv.apply_symm_apply]
  change (dupσ₂ Ω E).symm (secEmb Ω (hypCurveV E) (isAffineOpen_U (hypCurveV E) (hcV_dup E))
    ((sectionsVEEquiv E).symm (dupHom E a))) = secEmb Ω (hypCurveX E)
      (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E)) ((sectionsXEAlgEquiv E).symm a)
  rw [← hr, ← h, RingEquiv.symm_apply_apply]

omit [Algebra.IsAlgebraic K Ω] in
lemma dupKappa_injective₂ : Function.Injective (dupKappa₂ Ω E) :=
  (secEmb_injective Ω (hypCurveX E) (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E))).comp
    (sectionsXEAlgEquiv E).symm.injective

lemma dupEps_comp_injective₂ : Function.Injective ((dupEps₂ Ω E).comp (dupHom E)) := by
  have h : (dupEps₂ Ω E).comp (dupHom E) = dupKappa₂ Ω E := RingHom.ext (dupEps_dupHom₂ Ω E)
  rw [h]
  exact dupKappa_injective₂ Ω E

omit [Algebra.IsAlgebraic K Ω] in
lemma dupKappa_mem₂ (a : A) : dupKappa₂ Ω E a ∈ arithFF Ω (hypCurveX E) (compl_XE_nonempty E) :=
  secEmb_mem_arithFF Ω (hypCurveX E) (compl_XE_nonempty E) _

/-- The automorphism `σ τ σ⁻¹` of `K(V̄_Ω)^alg` over `L₀(V)`, for `τ` fixing `σ⁻¹(L₀(V))`. -/
def dupConjAut₂
    (τ : FFClosure (geomCurve Ω (hypCurveX E)) ≃ₐ[arithFF Ω (hypCurveX E) (compl_XE_nonempty E)]
      FFClosure (geomCurve Ω (hypCurveX E)))
    (hfix : ∀ c : arithFF Ω (hypCurveV E) (hcV_dup E),
      τ ((dupσ₂ Ω E).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveV E))) c)) =
        (dupσ₂ Ω E).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveV E))) c)) :
    FFClosure (geomCurve Ω (hypCurveV E)) ≃ₐ[arithFF Ω (hypCurveV E) (hcV_dup E)]
      FFClosure (geomCurve Ω (hypCurveV E)) :=
  { ((dupσ₂ Ω E).symm.trans τ.toRingEquiv).trans (dupσ₂ Ω E) with
    commutes' := fun c ↦ by
      change dupσ₂ Ω E (τ ((dupσ₂ Ω E).symm (algebraMap _ _ c))) = _
      rw [hfix, RingEquiv.apply_symm_apply] }

open Polynomial in
/-- **`τ ∈ Gal(K(X̄_Ω)^alg / L₀)` fixing `ε(B)` acts through `Π_U`.** -/
theorem arithAction_mem_dupPiU_of_fix₂ {e₁ e₂ e₃ : K}
    (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))
    (τ : FFClosure (geomCurve Ω (hypCurveX E)) ≃ₐ[arithFF Ω (hypCurveX E) (compl_XE_nonempty E)]
      FFClosure (geomCurve Ω (hypCurveX E)))
    (hτ : ∀ b, τ (dupEps₂ Ω E b) = dupEps₂ Ω E b) :
    arithAction Ω (hypCurveX E) (compl_XE_nonempty E) τ ∈ dupPiU Ω E := by
  have hV : ∀ a : Γ(curveE E, VE E), τ ((dupσ₂ Ω E).symm (secEmb Ω (hypCurveV E)
      (isAffineOpen_U (hypCurveV E) (hcV_dup E)) a)) = (dupσ₂ Ω E).symm (secEmb Ω (hypCurveV E)
        (isAffineOpen_U (hypCurveV E) (hcV_dup E)) a) := fun a ↦ by
    have h := hτ (sectionsVEEquiv E a)
    change τ ((dupσ₂ Ω E).symm (secEmb Ω (hypCurveV E) (isAffineOpen_U (hypCurveV E) (hcV_dup E))
      ((sectionsVEEquiv E).symm (sectionsVEEquiv E a)))) = (dupσ₂ Ω E).symm (secEmb Ω
        (hypCurveV E) (isAffineOpen_U (hypCurveV E) (hcV_dup E))
          ((sectionsVEEquiv E).symm (sectionsVEEquiv E a))) at h
    rwa [RingEquiv.symm_apply_apply] at h
  have hfix : ∀ c : arithFF Ω (hypCurveV E) (hcV_dup E),
      τ ((dupσ₂ Ω E).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveV E))) c)) =
        (dupσ₂ Ω E).symm (algebraMap _ (FFClosure (geomCurve Ω (hypCurveV E))) c) := fun c ↦ by
    obtain ⟨a, b, rfl⟩ := exists_eq_div_secToArithFF Ω (hypCurveV E) (hcV_dup E) c
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hV a) (hV b)
  obtain ⟨t₀, ht₀⟩ := exists_coverPiHom_arithAction Ω (hypCurveX E) (compl_XE_nonempty E)
    (hypCurveV E) (hcV_dup E) (coverXMorK E) (dupσ₂ Ω E)
    (coverσ_algebraMap Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
      (coverXMorK E))
  have hconj : arithConj Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
      (coverXMorK E) (dupσ₂ Ω E) (coverσ_algebraMap Ω (hypCurveX E) (compl_XE_nonempty E)
        (hypCurveV E) (hcV_dup E) (coverXMorK E)) (dupConjAut₂ Ω E τ hfix) = τ :=
    AlgEquiv.ext fun x ↦ by
      rw [arithConj_apply]
      change (dupσ₂ Ω E).symm (dupσ₂ Ω E (τ ((dupσ₂ Ω E).symm (dupσ₂ Ω E x)))) = τ x
      rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  have h1 := ht₀ (dupConjAut₂ Ω E τ hfix)
  rw [hconj] at h1
  have hmem : coverPiHom Ω (hypCurveX E) (compl_XE_nonempty E) (hypCurveV E) (hcV_dup E)
      (coverXMorK E) (arithAction Ω (hypCurveV E) (hcV_dup E) (dupConjAut₂ Ω E τ hfix)) ∈
        dupPiU Ω E := ⟨_, rfl⟩
  rw [h1] at hmem
  have h2 := (dupPiU_normal Ω E he).conj_mem _ hmem t₀⁻¹
  rwa [show ∀ y, t₀⁻¹ * (t₀ * y * t₀⁻¹) * t₀⁻¹⁻¹ = y from fun y ↦ by group] at h2

/-- The extension `K(E) → K(X̄_Ω)^alg` of `ε`. -/
abbrev dupEpsL₂ : FF →+* FFClosure (geomCurve Ω (hypCurveX E)) :=
  IsFractionRing.lift (injective_of_comp_dupHom₂ (dupEps₂ Ω E) (dupEps_comp_injective₂ Ω E))

lemma dupEpsL_algebraMap₂ (b : coverRingE E) :
    dupEpsL₂ Ω E (algebraMap (coverRingE E) FF b) = dupEps₂ Ω E b :=
  IsFractionRing.lift_algebraMap _ _

lemma dupEpsL_mulByTwoEndo₂ (a : A) :
    dupEpsL₂ Ω E (mulByTwoEndo two_ne_zero (algebraMap A FF a)) = dupKappa₂ Ω E a := by
  rw [← algebraMap_dupHom E a, dupEpsL_algebraMap₂, dupEps_dupHom₂]

/-- **A place over the cusp of `X` lying over the place at infinity of the source of `[2]`.** -/
theorem exists_isCuspPlace_comap_dupEpsL₂ :
    ∃ W, IsCuspPlace Ω (hypCurveX E) (compl_XE_nonempty E) W ∧
      W.comap (dupEpsL₂ Ω E) = ordInftyVS₂ E.toAffine := by
  obtain ⟨W, hW⟩ := exists_valuationSubring_comap_eq₂ (dupEpsL₂ Ω E) (ordInftyVS₂ E.toAffine)
  have hmem : ∀ f, dupEpsL₂ Ω E f ∈ W ↔ f ∈ ordInftyVS₂ E.toAffine := fun f ↦ by
    rw [← hW]
    rfl
  have hK : ∀ k : K, algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E))) (algebraMap K Ω k) ∈
      W := fun k ↦ by
    have e1 : algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E))) (algebraMap K Ω k) =
        dupKappa₂ Ω E (algebraMap K A k) := by
      change _ = secEmb Ω (hypCurveX E) (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E))
        ((sectionsXEAlgEquiv E).symm (algebraMap K A k))
      rw [AlgEquiv.commutes]
      exact (secEmb_algebraMap Ω (hypCurveX E)
        (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E)) k).symm
    rw [e1, ← dupEpsL_mulByTwoEndo₂, ← IsScalarTower.algebraMap_apply,
      mulByTwoEndo_algebraMap_base, hmem]
    exact algebraMap_mem_ordInftyVS₂ k
  refine ⟨W, ⟨fun c ↦ ?_, fun h ↦ ?_⟩, hW⟩
  · let φ : K →+* W := ((algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E)))).comp
      (algebraMap K Ω)).codRestrict W hK
    have hint : IsIntegral K c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
    have h2 : IsIntegral W (algebraMap Ω (FFClosure (geomCurve Ω (hypCurveX E))) c) :=
      hint.map_of_comp_eq φ (algebraMap Ω _) (RingHom.ext fun _ ↦ rfl)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    rw [← hy]
    exact y.2
  · have h3 := h ((sectionsXEAlgEquiv E).symm (mk E.toAffine (C X)))
    have e2 : secEmb Ω (hypCurveX E) (isAffineOpen_U (hypCurveX E) (compl_XE_nonempty E))
        ((sectionsXEAlgEquiv E).symm (mk E.toAffine (C X))) =
          dupEpsL₂ Ω E (mulByTwoEndo two_ne_zero (genX E.toAffine)) :=
      (dupEpsL_mulByTwoEndo₂ Ω E (mk E.toAffine (C X))).symm
    rw [e2, hmem, mem_ordInftyVS₂, ordInfty_mulByTwoEndo_genX₂] at h3
    exact absurd h3 (by norm_num)

open Polynomial in
/-- **(G2b) for one place**: the decomposition group of the place `W₀` (over the cusp of `X`,
over the place at infinity of the source of `[2]`) lies in `Π_U`. -/
theorem arithDecomp_le_dupPiU₂ {e₁ e₂ e₃ : K}
    (he : E.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))
    {W : ValuationSubring (FFClosure (geomCurve Ω (hypCurveX E)))}
    (hW : W.comap (dupEpsL₂ Ω E) = ordInftyVS₂ E.toAffine) :
    arithDecomp Ω (hypCurveX E) (compl_XE_nonempty E) W ≤ dupPiU Ω E := by
  rintro _ ⟨τ, hτ, rfl⟩
  refine arithAction_mem_dupPiU_of_fix₂ Ω E he τ fun b ↦ ?_
  exact apply_eq_of_preserves₂ he (dupEps₂ Ω E) (dupEps_comp_injective₂ Ω E) (dupEpsL₂ Ω E)
    (dupEpsL_algebraMap₂ Ω E) τ.toRingEquiv
    (fun a ↦ by
      change τ (dupEps₂ Ω E (dupHom E a)) = dupEps₂ Ω E (dupHom E a)
      rw [dupEps_dupHom₂]
      exact τ.commutes ⟨_, dupKappa_mem₂ Ω E a⟩)
    W hW (fun z ↦ hτ z) b

open Polynomial in
/-- **(G2b)**: for `E` with rational `2`-torsion, the commensurator (cuspidal decomposition group)
of every cuspidal inertia group of `Π_{E∖O}` lies in `Π_U`. -/
theorem commensurator_le_dupPiU₂ (hE : E.Ψ₂Sq.Splits)
    {I} (hI : I ∈ (arithmeticExt Ω (hypCurveX E) (compl_XE_nonempty E)).cusps) :
    Subgroup.Commensurable.commensurator I ≤ dupPiU Ω E := by
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_roots_of_splits E hE
  haveI := dupPiU_normal Ω E he
  obtain ⟨W₀, hW₀, hW₀c⟩ := exists_isCuspPlace_comap_dupEpsL₂ Ω E
  obtain ⟨W, hW, rfl⟩ := (mem_arithCusps_iff Ω (hypCurveX E) (compl_XE_nonempty E)).1 hI
  have h1 := subsingleton_compl_geomOpen_XE₂ Ω E
  obtain ⟨n, -, hn⟩ := exists_comap_eq_of_isCuspPlace₂ Ω (hypCurveX E) (compl_XE_nonempty E) h1
    hW₀ hW
  subst hn
  rw [arithInertia_comap, ← commensurator_map_mulEquiv,
    commensurator_arithInertia Ω (hypCurveX E) (compl_XE_nonempty E) hW₀]
  rintro _ ⟨d, hd, rfl⟩
  exact (dupPiU_normal Ω E he).conj_mem d (arithDecomp_le_dupPiU₂ Ω E he hW₀c hd) _

end G2b

/-! ### Specialisation to `E ∖ {O}` -/

section Transport

variable {K₁ : Type u} [Field K₁] [NumberField K₁] (Ω₁ : Type u) [Field Ω₁] [Algebra K₁ Ω₁]
  [IsAlgClosed Ω₁] [Algebra.IsAlgebraic K₁ Ω₁] [CharZero Ω₁] (E₁ : WeierstrassCurve K₁)
  [E₁.IsElliptic]
  {K₂ : Type u} [Field K₂] [NumberField K₂] (Ω₂ : Type u) [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] (E₂ : WeierstrassCurve K₂)
  [E₂.IsElliptic]

/-- **[AbsTopII] Cor 3.4 (G2), conditional form**: given (G2a) and (G2b) on both sides. -/
theorem map_dupPiU_of_decomp
    (Φ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Iso
      (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)))
    (hE₁ : E₁.Ψ₂Sq.Splits) (hE₂ : E₂.Ψ₂Sq.Splits)
    (hsurj₁ : ∃ I ∈ (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).cusps,
      ∀ y, ∃ d ∈ Subgroup.Commensurable.commensurator I,
        (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).pr d = y)
    (hsurj₂ : ∃ I ∈ (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).cusps,
      ∀ y, ∃ d ∈ Subgroup.Commensurable.commensurator I,
        (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).pr d = y)
    (hle₁ : ∀ I ∈ (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).cusps,
      Subgroup.Commensurable.commensurator I ≤ dupPiU Ω₁ E₁)
    (hle₂ : ∀ I ∈ (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)).cusps,
      Subgroup.Commensurable.commensurator I ≤ dupPiU Ω₂ E₂) :
    (dupPiU Ω₁ E₁).map Φ.pi.toMulEquiv.toMonoidHom = dupPiU Ω₂ E₂ := by
  obtain ⟨I₀, hI₀, hs₁⟩ := hsurj₁
  obtain ⟨J₀, hJ₀, hs₂⟩ := hsurj₂
  exact Φ.map_eq_of_cuspDecomp₂ (dupPiU_inf_Delta Ω₁ E₁ hE₁) (dupPiU_inf_Delta Ω₂ E₂ hE₂)
    hI₀ hs₁ hJ₀ hs₂ hle₁ hle₂

/-- **[AbsTopII] Cor 3.4, step G2: the `[2]`-subgroup is preserved by every isomorphism.** For
elliptic curves `E_i` over number fields with rational `2`-torsion, every isomorphism
`Φ : Π_{E₁∖O} ≅ Π_{E₂∖O}` of cuspidal extensions maps `Π_{U₁}` onto `Π_{U₂}`
(`Π_{U_i}` = image of `π₁(E_i ∖ E_i[2])` under `[2]`). -/
theorem map_dupPiU
    (Φ : (arithmeticExt Ω₁ (hypCurveX E₁) (compl_XE_nonempty E₁)).Iso
      (arithmeticExt Ω₂ (hypCurveX E₂) (compl_XE_nonempty E₂)))
    (hE₁ : E₁.Ψ₂Sq.Splits) (hE₂ : E₂.Ψ₂Sq.Splits) :
    (dupPiU Ω₁ E₁).map Φ.pi.toMulEquiv.toMonoidHom = dupPiU Ω₂ E₂ :=
  map_dupPiU_of_decomp Ω₁ E₁ Ω₂ E₂ Φ hE₁ hE₂ (exists_cusp_commensurator_surj₂ Ω₁ E₁)
    (exists_cusp_commensurator_surj₂ Ω₂ E₂) (fun _ hI ↦ commensurator_le_dupPiU₂ Ω₁ E₁ hE₁ hI)
    (fun _ hI ↦ commensurator_le_dupPiU₂ Ω₂ E₂ hE₂ hI)

end Transport

end CurvesJacobian.Cusp
