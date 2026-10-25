/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.WeightTop
import CurvesJacobian.CuspChar.KummerSep
import CurvesJacobian.CuspChar.ArithRes
import CurvesJacobian.CuspChar.Final
import CurvesJacobian.CuspChar.CuspStab
import CurvesJacobian.CuspChar.SchreierRank
import CurvesJacobian.Cusp.CuspTerminalFew
import CurvesJacobian.Cusp.SingleCusp
import CurvesJacobian.Cusp.ArithDecomp

/-!
# The arithmetic Galois action on the geometric Galois model

For an affine hyperbolic curve `C` over a number field `K`, `𝔽 = K(X̄_Ω)^alg`, the Galois model
`D = geomData Ω C` of `X̄_Ω` (`F D = L = K(X̄_Ω)`) and `τ ∈ Gal(𝔽 / K(X̄))` with image
`x = arithAction τ ∈ Π_U`:

* `CurvesJacobian.CuspChar.tau_mem_F`: `τ` maps `F D` onto itself and the constants `Ω` onto
  themselves (`tau_mem_range`);
* `CurvesJacobian.CuspChar.toArithAut_conjH`: `toArithAut (τ σ τ⁻¹) = τ · toArithAut σ · τ⁻¹`;
* `CurvesJacobian.CuspChar.psiOf`: conjugation by `x` on `Δ_U`, transported to
  `π₁ᵉᵗ(U_Ω)` along `deltaGeomEquiv`, with `psiOf_qU`: `Ψ(q σ) = q(τ σ τ⁻¹)`;
* `CurvesJacobian.CuspChar.tau_mu`: `τ` acts on `μ_{l^k}(𝔽)` by the cyclotomic character of `x`.

**Main result** (`CurvesJacobian.CuspChar.weight_top`, the case `H = Δ_U` of the cusp weight
identity): on the open subgroup `P = cuspStab Δ_U` of `Π_U` fixing every cusp,
`det(x | Hom(Δ_U, ℤ/3^k))² = χ_{3^k}(x)^{χ₀ + r}`. Proof: transport to `π₁ᵉᵗ(U_Ω)` along
`deltaGeomEquiv` (`charDet_top_conj`) and apply the generic `det_pull_sq_of_equiv` (the
Galois-model weight identity `det_pull_sq` with the rank `2g + r - 1` from
`π₁ᵉᵗ(U_Ω) ≃ Π̂_{g,r}` and `#Pic(F)[n] = n^{2g}`); `τ` fixes the cusps of `F` because conjugate
cuspidal inertia groups lie over the same place (`mem_iff_of_cuspInertia_conj_hyp`, by
terminality), which also gives `r(⊤) = r` (`cuspCount_cusps_top`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Orbifold KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer
  CurvesJacobian.Cusp

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.CuspChar

attribute [local instance] isAlgClosure_of_isAlgebraic isFunctionField_F

/-! ### Group-theoretic bookkeeping -/

section GroupAux

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (Δ : Subgroup Γ)
  [Δ.Normal]

lemma map_conjD_subtype (x : Γ) (J : Subgroup Δ) :
    (J.map (conjD Δ x).toMulEquiv.toMonoidHom).map Δ.subtype =
      (J.map Δ.subtype).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  exact congrArg J.map (MonoidHom.ext fun _ ↦ rfl)

lemma map_eq_map_subtype {G : Type*} [Group G] (f : G →* Γ) (e : G ≃* Δ)
    (hf : ∀ g, f g = (e g : Γ)) (A : Subgroup G) :
    A.map f = (A.map e.toMonoidHom).map Δ.subtype := by
  rw [Subgroup.map_map]
  exact congrArg A.map (MonoidHom.ext hf)

/-- If `f = Δ.subtype ∘ e` maps `A'` to the `x`-conjugate of the image of `A`, and conjugation by
`x` maps `e(A)` to a `Δ`-conjugate `δ e(A) δ⁻¹`, then `A'` is a conjugate of `A`. -/
lemma eq_map_conj_of_map {G : Type*} [Group G] (f : G →* Γ) (e : G ≃* Δ)
    (hf : ∀ g, f g = (e g : Γ)) (A A' : Subgroup G) (x : Γ)
    (h : A'.map f = (A.map f).map (MulAut.conj x).toMonoidHom) (δ : Δ)
    (hδ : (A.map e.toMonoidHom).map (conjD Δ x).toMulEquiv.toMonoidHom =
      conjSub δ (A.map e.toMonoidHom)) :
    A' = A.map (MulAut.conj (e.symm δ)).toMonoidHom := by
  have h1 : (A'.map e.toMonoidHom).map Δ.subtype =
      (conjSub δ (A.map e.toMonoidHom)).map Δ.subtype := by
    rw [← map_eq_map_subtype Δ f e hf A', h, map_eq_map_subtype Δ f e hf A,
      ← map_conjD_subtype Δ x (A.map e.toMonoidHom), hδ]
  have h2 := Subgroup.map_injective Δ.subtype_injective h1
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [h2, conjSub, Subgroup.map_map, Subgroup.map_map]
  exact congrArg A.map (MonoidHom.ext fun g ↦ by simp)

end GroupAux

section DetAux

variable {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  {D' : Type*} [Group D'] [TopologicalSpace D'] [IsTopologicalGroup D'] {p : ℕ}

lemma charDet_sub_congr (τ : D ≃ₜ* D) {H H' : OpenSubgroup D} (e : H = H')
    (h : mapOpenSub τ H = H) (h' : mapOpenSub τ H' = H') :
    charDet (p := p) τ H h = charDet (p := p) τ H' h' := by
  subst e
  rfl

lemma mapOpenSub_top_any (Φ : D ≃ₜ* D') : mapOpenSub Φ (⊤ : OpenSubgroup D) = ⊤ := by
  ext y
  obtain ⟨x, rfl⟩ := Φ.surjective y
  exact iff_of_true (mem_mapOpenSub.2 (OpenSubgroup.mem_top x)) (OpenSubgroup.mem_top _)

/-- The determinant on all characters is invariant under transport along `Φ`. -/
lemma charDet_top_conj (Φ : D ≃ₜ* D') (τ : D ≃ₜ* D) (h : mapOpenSub τ ⊤ = ⊤)
    (h' : mapOpenSub (Φ.symm.trans (τ.trans Φ)) ⊤ = ⊤) :
    charDet (p := p) τ ⊤ h = charDet (p := p) (Φ.symm.trans (τ.trans Φ)) ⊤ h' := by
  have e := mapOpenSub_top_any Φ
  have h2 : mapOpenSub (Φ.symm.trans (τ.trans Φ)) (mapOpenSub Φ ⊤) = mapOpenSub Φ ⊤ := by
    rw [e]
    exact h'
  rw [← charDet_conj Φ τ ⊤ h h2]
  exact charDet_sub_congr _ e _ _

end DetAux

/-! ### The weight identity for a hyperbolic `U` in a Galois model -/

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [IsAlgClosed k] [CharZero k]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] [IsCurveOver k X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  (hH : D.H ≤ D.HL) {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U : X.Opens} [Nonempty U] (n : ℕ) [NeZero n] (hU : (U : Set X)ᶜ.Finite)
  (hhyp : 2 < 2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X))

include hk hτ hU hhyp in
/-- **Places with conjugate cuspidal inertia groups lie over the same place of `F`** (`U`
hyperbolic): by terminality (`exists_mem_ker_comap_eq`). -/
theorem mem_iff_of_cuspInertia_conj_hyp {W W' : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hW : ¬ Cusp.IsCentredOn D X eL U W) (hW' : ¬ Cusp.IsCentredOn D X eL U W')
    (hc : ∃ γ, Cusp.cuspInertia D X eL hH U W' =
      (Cusp.cuspInertia D X eL hH U W).map (MulAut.conj γ).toMonoidHom) (x : F D) :
    ((x : F D) : Ω) ∈ W ↔ ((x : F D) : Ω) ∈ W' := by
  obtain ⟨γ, hγ⟩ := hc
  obtain ⟨σ, rfl⟩ := qU_surjective D X eL hk hH hτ hU γ
  have hσL : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.HL := hH σ.2
  have hF : ∀ y : F D, ((y : F D) : Ω) ∈ W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω) ↔
      ((y : F D) : Ω) ∈ W := fun y ↦ by
    rw [ValuationSubring.mem_comap]
    change (σ : Ω ≃ₐ[K₀ k t] Ω).symm (y : Ω) ∈ W ↔ _
    rw [(AlgEquiv.symm_apply_eq _).2 (fixes_F D σ y).symm]
  have hkW₁ : ∀ c : k, algebraMap k Ω c ∈
      W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω) := fun c ↦ by
    rw [ValuationSubring.mem_comap]
    change (σ : Ω ≃ₐ[K₀ k t] Ω).symm (algebraMap k Ω c) ∈ W
    rw [IsScalarTower.algebraMap_apply k (K₀ k t) Ω, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    exact hkW c
  have hW₁ : ¬ Cusp.IsCentredOn D X eL U (W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω)) :=
    fun h ↦ hW ((isCentredOn_comap_iff D X eL U hσL W).1 h)
  have h1 : Cusp.cuspInertia D X eL hH U (W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω)) =
      Cusp.cuspInertia D X eL hH U W' :=
    (cuspInertia_comap D X eL hH U W σ).trans hγ.symm
  have hcomm : (Cusp.cuspInertia D X eL hH U
      (W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω))).relIndex
        (Cusp.cuspInertia D X eL hH U W') ≠ 0 := by
    rw [h1, Subgroup.relIndex_self]
    exact one_ne_zero
  have hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X) ∨ ∃ O₀ : Subgroup D.H, O₀.Normal ∧
      IsOpen (O₀ : Set D.H) ∧ (D.chartHom hH (genericL D X eL U)).ker ≤ O₀ ∧
        CuspSep D O₀ (W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω)) := by
    by_cases h3 : 2 < Nat.card ((U : Set X)ᶜ : Set X)
    · exact Or.inl h3
    · exact Or.inr (exists_cuspSep D X eL hH hk hτ (by omega) hU hkW₁ hW₁)
  obtain ⟨m, -, hm⟩ := exists_mem_ker_comap_eq D X eL hH hk hτ hU hU3 hkW₁ hkW' hW₁ hW' hcomm
  rw [← hF x, ← hm, ValuationSubring.mem_comap]
  change (m : Ω ≃ₐ[K₀ k t] Ω) (x : Ω) ∈ W' ↔ _
  rw [fixes_F D m x]

include hk hU in
/-- A cusp exists if `X ∖ U` is nonempty. -/
lemma nonempty_cuspPl (hr : 0 < Nat.card ((U : Set X)ᶜ : Set X)) :
    Nonempty (CuspPl D X eL hH U) := by
  haveI := hU.to_subtype
  obtain ⟨⟨y, hy⟩⟩ := (Nat.card_pos_iff.1 hr).1
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨(Nonempty.some (inferInstance : Nonempty U)).1, trivial⟩⟩
  obtain ⟨W, -, hWV, hWU⟩ := exists_isCentredOn_not_isCentredOn D X eL hk (V := ⊤) hU trivial hy
  exact ⟨⟨placeBelow D W hWV.1 (comap_ne_top_of_not_isCentredOn D X eL hH hWU hWV.1),
    fun h ↦ hWU ((isCentredOn_iff_isCentredP D X eL hH U (fun _ ↦ Iff.rfl)).2 h)⟩⟩

include hhyp in
/-- `Hom_cont(π₁ᵉᵗ(U), ℤ/n)` is free of rank `2g + r - 1`. -/
lemma charSpace_facts (Θ : PiU D X eL U ≃ₜ*
      Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X)))
    (hr : 0 < Nat.card ((U : Set X)ᶜ : Set X)) [Fact (1 < n)] :
    Module.Free (ZMod n) (Mch D X eL n U) ∧ Module.Finite (ZMod n) (Mch D X eL n U) ∧
      Module.finrank (ZMod n) (Mch D X eL n U) =
        2 * (curveGenus k X).toNat + Nat.card ((U : Set X)ᶜ : Set X) - 1 := by
  haveI : Finite (Mch D X eL n U) := Nat.finite_of_card_ne_zero (by
    rw [natCard_charSpace_top Θ hr (by omega) n]
    exact pow_ne_zero _ (NeZero.ne n))
  exact ⟨free_charSpace_top Θ hr n, Module.Finite.of_finite,
    finrank_charSpace_top Θ hr (by omega) n⟩

include hk hH in
/-- `#Pic(F)[n] = n^{2g}`. -/
lemma natCard_picTorsion_F :
    Nat.card (picTorsion k (F D) n) = n ^ (2 * (curveGenus k X).toNat) := by
  rw [← natCard_picTorsion_eq (functionFieldEquivF hH hk) n]
  exact natCard_picTorsion n

include hk hτ hU hhyp in
/-- **`r(⊤)` is the number of punctures**: the cusp classes of `π₁ᵉᵗ(U)` are the cusps of `F`
(`cuspCount_cusps_eq`, separation by `mem_iff_of_cuspInertia_conj_hyp`), and there are
`|X ∖ U|` of them (`card_cuspPl_eq` at `n = 3`). -/
theorem cuspCount_cusps_top (Θ : PiU D X eL U ≃ₜ*
      Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X)))
    (hr : 0 < Nat.card ((U : Set X)ᶜ : Set X)) :
    cuspCount (Cusp.cusps D X eL hH U) ⊤ = Nat.card ((U : Set X)ᶜ : Set X) := by
  classical
  haveI := finite_cuspPl D X eL hk hH U hU
  haveI := Fintype.ofFinite (CuspPl D X eL hH U)
  haveI : Fact (1 < 3 ^ 1) := ⟨by norm_num⟩
  haveI : NeZero (3 ^ 1) := ⟨by norm_num⟩
  obtain ⟨hfree, hfin, hrank⟩ := charSpace_facts D X eL (3 ^ 1) hhyp Θ hr
  obtain ⟨c₀⟩ := nonempty_cuspPl D X eL hk hH hU hr
  rw [cuspCount_cusps_eq D X eL hH fun W W' hkW hkW' hW hW' hc x ↦
    mem_iff_of_cuspInertia_conj_hyp D X eL hk hH hτ hU hhyp hkW hkW' hW hW' hc x]
  exact card_cuspPl_eq D X eL hk hH hτ (3 ^ 1) hU (isLocalRing_zmod_pow 3 1 one_pos) _ _ hrank
    (natCard_picTorsion_F D X eL hk hH (3 ^ 1)) hr c₀

include hk hτ hU hhyp in
/-- **The weight identity on `π₁ᵉᵗ(U)`** in the form `det(Ψ^*)² = χ^{2g + 2(r − 1)}`, `r = |X ∖ U|`
(`det_pull_sq` with the rank from `π₁ᵉᵗ(U) ≃ Π̂_{g,r}` and `#Pic(F)[n] = n^{2g}`). -/
theorem det_pull_sq_of_equiv (Θ : PiU D X eL U ≃ₜ*
      Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X)))
    (hr : 0 < Nat.card ((U : Set X)ᶜ : Set X)) [Fact (1 < n)] (hl : IsLocalRing (ZMod n))
    (φ : Ω ≃+* Ω) (hφF : ∀ x : F D, φ (x : Ω) ∈ F D)
    (hφF' : ∀ x : F D, φ.symm (x : Ω) ∈ F D)
    (hφk : ∀ c : k, φ (algebraMap k Ω c) ∈ Set.range (algebraMap k Ω) ∧
      φ.symm (algebraMap k Ω c) ∈ Set.range (algebraMap k Ω))
    (Ψ : PiU D X eL U ≃ₜ*
      PiU D X eL U)
    (hΨ : ∀ σ, Ψ (qU D X eL hH σ) = qU D X eL hH (conjH D φ hφF' σ))
    (χ : (ZMod n)ˣ)
    (hχ : ∀ ζ : Mu n Ω, φ ((Mu.val ζ : Ωˣ) : Ω) = ((Mu.val ζ : Ωˣ) : Ω) ^ (χ : ZMod n).val)
    (hcusp : ∀ c : CuspPl D X eL hH U, ∀ x : F D, phiF D φ hφF hφF' x ∈ c.1.1 ↔ x ∈ c.1.1) :
    charDet (p := n) Ψ ⊤ (mapOpenSub_top' D X eL Ψ) ^ 2 =
      χ ^ (2 * (curveGenus k X).toNat + 2 * (Nat.card ((U : Set X)ᶜ : Set X) - 1)) := by
  haveI := finite_cuspPl D X eL hk hH U hU
  obtain ⟨hfree, hfin, hrank⟩ := charSpace_facts D X eL n hhyp Θ hr
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact det_pull_sq D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp hl _ _ hrank
    (natCard_picTorsion_F D X eL hk hH n)

end Generic

/-! ### The arithmetic Galois action -/

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

instance charZero_FFClosure : CharZero (FFClosure (geomCurve Ω C)) :=
  charZero_of_injective_algebraMap (algebraMap Ω (FFClosure (geomCurve Ω C))).injective

variable (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C))

lemma tau_mem_range (c : Ω) :
    τ (algebraMap Ω (FFClosure (geomCurve Ω C)) c) ∈
      Set.range (algebraMap Ω (FFClosure (geomCurve Ω C))) :=
  ⟨resOmega Ω C hc τ c, algebraMap_resOmega Ω C hc τ c⟩

lemma algebraMap_mem_L (c : Ω) :
    algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ (geomData Ω C).L := by
  rw [← curveEquivL_algebraMap Ω (transcendental_geomCoord Ω C) c]
  exact SetLike.coe_mem _

/-- `τ` maps `L = K(X̄_Ω)` into itself. -/
lemma tau_mem_L {y : FFClosure (geomCurve Ω C)} (hy : y ∈ (geomData Ω C).L) :
    τ y ∈ (geomData Ω C).L := by
  set S : Subfield (FFClosure (geomCurve Ω C)) :=
    ((geomData Ω C).L.toSubfield).comap (τ : FFClosure (geomCurve Ω C) →+*
      FFClosure (geomCurve Ω C))
  have hS := algebraMap_mem_of_le Ω C hc S (fun c ↦ by
      change τ (algebraMap Ω _ c) ∈ (geomData Ω C).L
      obtain ⟨c', hc'⟩ := tau_mem_range Ω C hc τ c
      rw [← hc']
      exact algebraMap_mem_L Ω C c')
    (fun a ↦ by
      change τ (secEmb Ω C (isAffineOpen_U C hc) a) ∈ (geomData Ω C).L
      have hfix : τ (secEmb Ω C (isAffineOpen_U C hc) a) = secEmb Ω C (isAffineOpen_U C hc) a :=
        τ.commutes ⟨_, secEmb_mem_arithFF Ω C hc a⟩
      rw [hfix, secEmb, RingHom.comp_apply, IntermediateField.algebraMap_apply]
      exact SetLike.coe_mem _)
    ((curveEquivL Ω (transcendental_geomCoord Ω C)).symm ⟨y, hy⟩)
  rw [← curveEquivL_apply Ω (transcendental_geomCoord Ω C), RingEquiv.apply_symm_apply] at hS
  exact hS

lemma mem_F_iff_mem_L (y : FFClosure (geomCurve Ω C)) :
    y ∈ F (geomData Ω C) ↔ y ∈ (geomData Ω C).L := by
  constructor
  · intro hy
    rw [GaloisData.L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact (IntermediateField.mem_fixedField_iff _ _).1 hy σ ((geomData Ω C).le hσ)
  · exact fun hy ↦ mem_F_of_mem_L (geomData Ω C) (curveGaloisData_H_le Ω _) hy

/-- `τ` maps `F D` into itself. -/
lemma tau_mem_F (x : F (geomData Ω C)) :
    (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C)) (x : FFClosure _) ∈
      F (geomData Ω C) :=
  (mem_F_iff_mem_L Ω C _).2 (tau_mem_L Ω C hc τ ((mem_F_iff_mem_L Ω C _).1 x.2))

lemma tau_symm_mem_F (x : F (geomData Ω C)) :
    (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C)).symm (x : FFClosure _) ∈
      F (geomData Ω C) :=
  tau_mem_F Ω C hc τ⁻¹ x

lemma tau_hk (c : Ω) :
    (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C))
        (algebraMap Ω (FFClosure (geomCurve Ω C)) c) ∈
        Set.range (algebraMap Ω (FFClosure (geomCurve Ω C))) ∧
      (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C)).symm
        (algebraMap Ω (FFClosure (geomCurve Ω C)) c) ∈
        Set.range (algebraMap Ω (FFClosure (geomCurve Ω C))) :=
  ⟨tau_mem_range Ω C hc τ c, tau_mem_range Ω C hc τ⁻¹ c⟩

/-- **Conjugation by `τ` and the arithmetic Galois action.** -/
lemma toArithAut_conjH (σ : (geomData Ω C).H) :
    toArithAut Ω C hc (conjH (geomData Ω C)
        (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C))
        (tau_symm_mem_F Ω C hc τ) σ) =
      τ * toArithAut Ω C hc σ * τ⁻¹ := by
  ext y
  rfl

/-- The Galois action `q : H → π₁ᵉᵗ(U_Ω)` of the geometric Galois model. -/
abbrev qG : (geomData Ω C).H →* π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
      genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C)) :=
  qU (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C)) (U := geomOpen Ω C)

/-- Conjugation by `x ∈ Π_U` on `Δ_U`, transported to `π₁ᵉᵗ(U_Ω)`. -/
def psiOf (x : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) :
    π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
      genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C)) ≃ₜ*
    π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
      genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C)) :=
  (deltaGeomEquiv Ω C hc).symm.trans ((conjD (deltaU Ω C hc) x).trans (deltaGeomEquiv Ω C hc))

/-- **`Ψ_x(q σ) = q(τ σ τ⁻¹)`** for `x = arithAction τ`. -/
lemma psiOf_qU (σ : (geomData Ω C).H) :
    psiOf Ω C hc (arithAction Ω C hc τ) (qG Ω C σ) =
      qG Ω C (conjH (geomData Ω C) (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C))
        (tau_symm_mem_F Ω C hc τ) σ) := by
  apply (deltaGeomEquiv Ω C hc).symm.injective
  apply Subtype.ext
  simp only [psiOf, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.symm_apply_apply]
  rw [conjD_apply_coe, ← geomToPi_eq_deltaGeomEquiv, ← geomToPi_eq_deltaGeomEquiv,
    geomToPi_chartHom, geomToPi_chartHom, toArithAut_conjH, map_mul, map_mul, map_inv]

/-- **`τ` acts on `μ_{l^k}` by the cyclotomic character of `arithAction τ`.** -/
lemma tau_mu [IsSlimGk K Ω] (l k : ℕ) [NeZero l] [NeZero (l ^ k)]
    (ζ : Mu (l ^ k) (FFClosure (geomCurve Ω C))) :
    (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C))
        ((Mu.val ζ : (FFClosure (geomCurve Ω C))ˣ) : FFClosure (geomCurve Ω C)) =
      ((Mu.val ζ : (FFClosure (geomCurve Ω C))ˣ) : FFClosure (geomCurve Ω C)) ^
        ((arithCycChar Ω C hc l k (arithAction Ω C hc τ) : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)).val
    := by
  set z : FFClosure (geomCurve Ω C) :=
    ((Mu.val ζ : (FFClosure (geomCurve Ω C))ˣ) : FFClosure (geomCurve Ω C)) with hzdef
  have hz : z ^ (l ^ k) = 1 := by
    rw [hzdef, ← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]
  obtain ⟨c, hcz⟩ := Cusp.exists_algebraMap_eq_of_isAlgebraic Ω C z
    ⟨Polynomial.X ^ (l ^ k) - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero
      (Nat.pos_of_ne_zero (NeZero.ne _)) 1, by simp [hz]⟩
  have hc1 : c ^ (l ^ k) = 1 :=
    (algebraMap Ω (FFClosure (geomCurve Ω C))).injective (by rw [map_pow, hcz, hz, map_one])
  set cu : Ωˣ := Units.mk0 c (by
    rintro rfl
    rw [zero_pow (NeZero.ne _)] at hc1
    exact zero_ne_one hc1)
  have hcu : cu ∈ rootsOfUnity (l ^ k) Ω := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    simp [cu, hc1]
  have hspec := cycChar_spec (K := K) l k (resOmega Ω C hc τ) hcu
  rw [arithCycChar_arithAction]
  change τ z = z ^ _
  rw [← hcz, ← algebraMap_resOmega]
  change algebraMap Ω _ (resOmega Ω C hc τ (cu : Ω)) = algebraMap Ω _ (cu : Ω) ^ _
  rw [hspec, map_pow]

section Transport

variable {Δ Δ' : Type*} [Group Δ] [Group Δ']

/-- **The number of cusp classes is invariant under isomorphisms.** -/
theorem cuspCount_top_congr (Φ : Δ ≃* Δ') (S : Set (Subgroup Δ)) (S' : Set (Subgroup Δ'))
    (hS : ∀ J : Subgroup Δ, J ∈ S ↔ J.map Φ.toMonoidHom ∈ S') :
    cuspCount S ⊤ = cuspCount S' ⊤ := by
  have hback : ∀ J' : Subgroup Δ', (J'.map Φ.symm.toMonoidHom).map Φ.toMonoidHom = J' := by
    intro J'
    rw [Subgroup.map_map]
    convert Subgroup.map_id J'
    ext y
    exact Φ.apply_symm_apply y
  have hfwd : ∀ J : Subgroup Δ, (J.map Φ.toMonoidHom).map Φ.symm.toMonoidHom = J := by
    intro J
    rw [Subgroup.map_map]
    convert Subgroup.map_id J
    ext y
    exact Φ.symm_apply_apply y
  have hconj : ∀ (h : Δ) (J : Subgroup Δ),
      (conjSub h J).map Φ.toMonoidHom = conjSub (Φ h) (J.map Φ.toMonoidHom) := by
    intro h J
    ext y
    simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨Φ z, ⟨z, hz, rfl⟩, by simp [map_mul, map_inv]⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨h * z * h⁻¹, ⟨z, hz, rfl⟩, by simp [map_mul, map_inv]⟩
  let e : S ≃ S' :=
    { toFun := fun J ↦ ⟨J.1.map Φ.toMonoidHom, (hS _).1 J.2⟩
      invFun := fun J' ↦ ⟨J'.1.map Φ.symm.toMonoidHom, (hS _).2 (by rw [hback]; exact J'.2)⟩
      left_inv := fun J ↦ Subtype.ext (hfwd J.1)
      right_inv := fun J' ↦ Subtype.ext (hback J'.1) }
  refine Nat.card_congr (Quotient.congr e fun I J ↦ ?_)
  constructor
  · rintro ⟨h, -, hIJ⟩
    exact ⟨Φ h, Subgroup.mem_top _, by
      change conjSub (Φ h) (I.1.map Φ.toMonoidHom) = J.1.map Φ.toMonoidHom
      rw [← hconj, hIJ]⟩
  · rintro ⟨h', -, hIJ⟩
    refine ⟨Φ.symm h', Subgroup.mem_top _, ?_⟩
    have h1 : (conjSub (Φ.symm h') I.1).map Φ.toMonoidHom = J.1.map Φ.toMonoidHom := by
      rw [hconj, Φ.apply_symm_apply]
      exact hIJ
    rw [← hfwd (conjSub (Φ.symm h') I.1), h1, hfwd]

end Transport

/-- **The cusp groups of `Δ_U` correspond to the cuspidal inertia groups of `π₁ᵉᵗ(U_Ω)`**. -/
lemma mem_deltaCusps_iff_map (J : Subgroup (deltaU Ω C hc)) :
    J ∈ deltaCusps Ω C hc ↔
      J.map (deltaGeomEquiv Ω C hc).toMulEquiv.toMonoidHom ∈ geomCusps Ω C := by
  have key : ∀ I₀ : Subgroup π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
      genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (geomOpen Ω C)),
      J.map (deltaU Ω C hc).subtype = I₀.map (geomToPi Ω C hc) ↔
        J.map (deltaGeomEquiv Ω C hc).toMulEquiv.toMonoidHom = I₀ := by
    intro I₀
    constructor
    · intro h
      ext γ
      constructor
      · rintro ⟨δ, hδ, rfl⟩
        have : (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∈
            I₀.map (geomToPi Ω C hc) := h ▸ ⟨δ, hδ, rfl⟩
        obtain ⟨γ', hγ', e⟩ := this
        rw [geomToPi_eq_deltaGeomEquiv] at e
        have e' := Subtype.ext e
        change (deltaGeomEquiv Ω C hc) δ ∈ I₀
        rw [← e', ContinuousMulEquiv.apply_symm_apply]
        exact hγ'
      · intro hγ
        have : geomToPi Ω C hc γ ∈ J.map (deltaU Ω C hc).subtype := h ▸ ⟨γ, hγ, rfl⟩
        obtain ⟨δ, hδ, e⟩ := this
        rw [geomToPi_eq_deltaGeomEquiv] at e
        refine ⟨δ, hδ, ?_⟩
        change (deltaGeomEquiv Ω C hc) δ = γ
        rw [show δ = (deltaGeomEquiv Ω C hc).symm γ from Subtype.ext e,
          ContinuousMulEquiv.apply_symm_apply]
    · rintro rfl
      ext y
      constructor
      · rintro ⟨δ, hδ, rfl⟩
        refine ⟨(deltaGeomEquiv Ω C hc) δ, ⟨δ, hδ, rfl⟩, ?_⟩
        rw [geomToPi_eq_deltaGeomEquiv, ContinuousMulEquiv.symm_apply_apply]
        rfl
      · rintro ⟨_, ⟨δ, hδ, rfl⟩, rfl⟩
        refine ⟨δ, hδ, ?_⟩
        rw [geomToPi_eq_deltaGeomEquiv]
        change (δ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) =
          ((deltaGeomEquiv Ω C hc).symm ((deltaGeomEquiv Ω C hc) δ) : _)
        rw [ContinuousMulEquiv.symm_apply_apply]
  constructor
  · intro hJ
    obtain ⟨I₀, hI₀, hI⟩ := exists_geomCusps_of_mem_arithCusps Ω C hc hJ
    rw [(key I₀).1 hI]
    exact hI₀
  · intro hJ
    refine ⟨_, hJ, 1, ?_⟩
    rw [(key _).2 rfl]
    ext y
    simp

/-- **`r(⊤)` for `Δ_U` is the number of cusp classes of `π₁ᵉᵗ(U_Ω)`.** -/
lemma cuspCount_deltaCusps_top :
    cuspCount (deltaCusps Ω C hc) ⊤ = cuspCount (geomCusps Ω C) ⊤ :=
  cuspCount_top_congr (deltaGeomEquiv Ω C hc).toMulEquiv _ _ (mem_deltaCusps_iff_map Ω C hc)

/-! ### The weight identity for `H = ⊤` -/

/-- **`τ` fixes the cusps** (the places of `F` over cusps of `U_Ω`) if `arithAction τ` maps every
cusp group of `Δ_U` to a `Δ_U`-conjugate of itself. -/
lemma tau_sep (hx : arithAction Ω C hc τ ∈ cuspStab (deltaU Ω C hc) (deltaCusps Ω C hc))
    {W : ValuationSubring (FFClosure (geomCurve Ω C))} (hW : IsCuspPlace Ω C hc W)
    (y : F (geomData Ω C)) :
    (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C))
        ((y : F (geomData Ω C)) : FFClosure (geomCurve Ω C)) ∈ W ↔
      ((y : F (geomData Ω C)) : FFClosure (geomCurve Ω C)) ∈ W := by
  have hW' := isCuspPlace_comap Ω C hc (τ⁻¹).symm hW
  have hx' : arithAction Ω C hc τ⁻¹ ∈ cuspStab (deltaU Ω C hc) (deltaCusps Ω C hc) := by
    rw [map_inv]
    exact inv_mem_cuspStab hx
  have hJ : (geomCuspInertia Ω C W).map (deltaGeomEquiv Ω C hc).symm.toMulEquiv.toMonoidHom ∈
      deltaCusps Ω C hc := by
    change ((geomCuspInertia Ω C W).map
      (deltaGeomEquiv Ω C hc).symm.toMulEquiv.toMonoidHom).map (deltaU Ω C hc).subtype ∈
        arithCusps Ω C hc
    rw [← map_eq_map_subtype (deltaU Ω C hc) (geomToPi Ω C hc)
      (deltaGeomEquiv Ω C hc).symm.toMulEquiv (geomToPi_eq_deltaGeomEquiv Ω C hc),
      ← arithInertia_eq_map_geom Ω C hc hW.1]
    exact (mem_arithCusps_iff Ω C hc).2 ⟨W, hW, rfl⟩
  obtain ⟨δ, hδ⟩ := mem_cuspStab.1 hx' _ hJ
  have h : (geomCuspInertia Ω C (W.comap ((τ⁻¹).symm : FFClosure (geomCurve Ω C) →+*
        FFClosure (geomCurve Ω C)))).map (geomToPi Ω C hc) =
      ((geomCuspInertia Ω C W).map (geomToPi Ω C hc)).map
        (MulAut.conj (arithAction Ω C hc τ⁻¹)).toMonoidHom :=
    (arithInertia_eq_map_geom Ω C hc hW'.1).symm.trans ((arithInertia_comap Ω C hc W τ⁻¹).trans
      (congrArg (fun I ↦ I.map (MulAut.conj (arithAction Ω C hc τ⁻¹)).toMonoidHom)
        (arithInertia_eq_map_geom Ω C hc hW.1)))
  have hconj := eq_map_conj_of_map (deltaU Ω C hc) (geomToPi Ω C hc)
    (deltaGeomEquiv Ω C hc).symm.toMulEquiv (geomToPi_eq_deltaGeomEquiv Ω C hc) _ _ _ h δ hδ
  have key := mem_iff_of_cuspInertia_conj_hyp (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveEquivL_algebraMap Ω _)
    (curveGaloisData_H_le Ω _) (curveEquivL_τ Ω _) (compl_finite_baseChangeOpen K Ω C.nonempty)
    (isHyperbolic_genusU Ω C) hW.1 hW'.1
    (fun h ↦ hW.2 ((isCentredOn_geomOpen_iff Ω C hc W).1 h).2)
    (fun h ↦ hW'.2 ((isCentredOn_geomOpen_iff Ω C hc _).1 h).2) ⟨_, hconj⟩ y
  rw [ValuationSubring.mem_comap] at key
  exact key.symm

/-- **`τ` fixes every cusp of `F`** (the hypothesis `hcusp` of `det_pull_sq`). -/
lemma tau_fixes_cusps
    (hx : arithAction Ω C hc τ ∈ cuspStab (deltaU Ω C hc) (deltaCusps Ω C hc))
    (c : CuspPl (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C))
    (y : F (geomData Ω C)) :
    phiF (geomData Ω C) (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C))
        (tau_mem_F Ω C hc τ) (tau_symm_mem_F Ω C hc τ) y ∈ c.1.1 ↔ y ∈ c.1.1 := by
  have hW : IsCuspPlace Ω C hc (cuspW (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _) c) :=
    ⟨k_le_cuspW _ _ _ _ c, fun h ↦ not_isCentredOn_cuspW _ _ _ _ c
      ((isCentredOn_geomOpen_iff Ω C hc _).2 ⟨k_le_cuspW _ _ _ _ c, h⟩)⟩
  exact (cuspW_spec _ _ _ _ c _).symm.trans
    ((tau_sep Ω C hc τ hx hW y).trans (cuspW_spec _ _ _ _ c y))

/-- **The cusp weight identity of `U` for `H = Δ_U`** ([AbsTopI] Lemma 4.5 (v), case `H = ⊤`):
on the open subgroup `P ⊆ Π_U` of elements fixing every cusp,
`det(x | Hom(Δ_U, ℤ/3^k))² = χ_{3^k}(x)^{χ₀ + r}`. -/
theorem weight_top [IsSlimGk K Ω] :
    ∃ P : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)),
    IsOpen (P : Set π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))) ∧
    ∀ x ∈ P, ∀ k : ℕ,
      charDet (p := 3 ^ k) (conjD (deltaU Ω C hc) x) ⊤ (mapOpenSub_top _) ^ 2 =
        cyc3 Ω C hc k x ^ (eulerU Ω C + cuspCount (deltaCusps Ω C hc) ⊤) := by
  have hS := isCuspSet_deltaCusps Ω C hc fun _ _ hr h j _ _ hx hx1 hz ↦
    mem_inertia_of_commute hr h j hx hx1 hz
  haveI : Finite (CuspQuot (deltaCusps Ω C hc) ⊤) := hS.2.2.2.2.2.1 ⊤
  have hSconj : ∀ (x : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))),
      ∀ J ∈ deltaCusps Ω C hc,
        J.map (conjD (deltaU Ω C hc) x).toMulEquiv.toMonoidHom ∈ deltaCusps Ω C hc := by
    intro x J hJ
    change (J.map (conjD (deltaU Ω C hc) x).toMulEquiv.toMonoidHom).map (deltaU Ω C hc).subtype ∈
      arithCusps Ω C hc
    rw [map_conjD_subtype]
    exact map_conj_mem_arithCusps Ω C hc hJ x
  refine ⟨cuspStab (deltaU Ω C hc) (deltaCusps Ω C hc),
    isOpen_cuspStab (fun J hJ ↦ hS.isClosed hJ) hSconj, ?_⟩
  obtain ⟨Θ, -⟩ := exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed (geomData Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (geomOpen Ω C)
    (compl_finite_baseChangeOpen K Ω C.nonempty) (compl_nonempty_baseChangeOpen K Ω hc)
  have hhyp : 2 < 2 * genusU Ω C + cuspsU Ω C := isHyperbolic_genusU Ω C
  have hr : 0 < cuspsU Ω C := cuspsU_pos Ω C hc
  have hcount : cuspCount (deltaCusps Ω C hc) ⊤ = cuspsU Ω C :=
    (cuspCount_deltaCusps_top Ω C hc).trans (cuspCount_cusps_top (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveEquivL_algebraMap Ω _)
      (curveGaloisData_H_le Ω _) (curveEquivL_τ Ω _)
      (compl_finite_baseChangeOpen K Ω C.nonempty) hhyp Θ hr)
  have hexp : 2 * genusU Ω C + 2 * (cuspsU Ω C - 1) =
      eulerU Ω C + cuspCount (deltaCusps Ω C hc) ⊤ := by
    rw [hcount]
    unfold eulerU
    omega
  refine (arithAction_surjective Ω C hc).forall.2 fun τ hτ k ↦ ?_
  cases k with
  | zero =>
    haveI : Subsingleton (ZMod (3 ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero 3)
    exact Units.ext (Subsingleton.elim _ _)
  | succ k =>
    haveI : Fact (1 < 3 ^ (k + 1)) := ⟨Nat.one_lt_pow (Nat.succ_ne_zero k) (by norm_num)⟩
    have hdet := charDet_top_conj (p := 3 ^ (k + 1)) (deltaGeomEquiv Ω C hc)
      (conjD (deltaU Ω C hc) (arithAction Ω C hc τ)) (mapOpenSub_top _) (mapOpenSub_top_any _)
    have hw := det_pull_sq_of_equiv (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveEquivL_algebraMap Ω _)
      (curveGaloisData_H_le Ω _) (curveEquivL_τ Ω _) (3 ^ (k + 1))
      (compl_finite_baseChangeOpen K Ω C.nonempty) hhyp Θ hr
      (isLocalRing_zmod_pow 3 (k + 1) k.succ_pos)
      (τ : FFClosure (geomCurve Ω C) ≃+* FFClosure (geomCurve Ω C)) (tau_mem_F Ω C hc τ)
      (tau_symm_mem_F Ω C hc τ) (tau_hk Ω C hc τ) (psiOf Ω C hc (arithAction Ω C hc τ))
      (psiOf_qU Ω C hc τ) (cyc3 Ω C hc (k + 1) (arithAction Ω C hc τ)) (tau_mu Ω C hc τ 3 (k + 1))
      (tau_fixes_cusps Ω C hc τ hτ)
    exact (congrArg (· ^ 2) hdet).trans (hw.trans
      (congrArg (fun e ↦ cyc3 Ω C hc (k + 1) (arithAction Ω C hc τ) ^ e) hexp))

end CurvesJacobian.CuspChar
