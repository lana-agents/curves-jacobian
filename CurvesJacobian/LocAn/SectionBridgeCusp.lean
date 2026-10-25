/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithDecomp
import CurvesJacobian.Galois.ChartOfOpen
import CurvesJacobian.CuspChar.ArithRes

/-!
# Cusps are determined by their inertia groups ([GalSect] Thm 1.3 (i), (ii) for cusps)

[GalSect] = Mochizuki, *Galois Sections in Absolute Anabelian Geometry*
(`Galois Sections.txt` l.246–286, statement l.263–269). For a hyperbolic curve `X_K` and a closed
point `x` of the compactification, `D_x ⊆ Π_{X_K}` is its decomposition group and
`I_x = D_x ∩ Δ_X` (l.250–257); Theorem 1.3:
"(i) … If `x` is a cusp, then `x` is completely determined by the conjugacy class of the closed
subgroup `I_x ⊆ Π_{X_K}`. (ii) … If `x` is a cusp, then `D_x = C_{Π_{X_K}}(H)` for any open
subgroup `H ⊆ I_x`" (`C_G(H)` = commensurator, l.61–66). The proof of (i) for cusps "follows from
elementary facts about fundamental groups of topological surfaces"; here it follows from the
geometric terminality of cuspidal inertia groups (`CurvesJacobian.Cusp.exists_mem_ker_comap_eq`).

This is the **cusp form (2d) of the section bridge** (MR7 plan; the closed-point form (2c) for
rational points is `LocAn/SectionBridgeThmC.lean`). It is stated in MR8's arithmetic model of
`Π_U = π₁ᵉᵗ(Spec Γ(U))` for a hyperbolic curve `C = (X̄, U)` with a cusp
(`CurvesJacobian.Cusp.arithInertia`, `arithDecomp`; `F = K(X̄_Ω)^alg ⊇ L₀ = ι(K(X̄))`, places `W`
of `F` over cusps: `IsCuspPlace`). A place `W` lies over the closed point `x` of `X̄` if
`ι⁻¹(W) = 𝒪_{X̄,x}`. The base field `K` is any field of characteristic zero (number fields and
finite extensions of `ℚ_p` in particular); no slimness of `G_K` is used.

## Main results

* `CurvesJacobian.LocAn.mem_of_germ_mem_stalkVS`: if every section over `V` (finite complement) is
  regular at `y`, then `y ∈ V`;
* **`CurvesJacobian.LocAn.exists_isCuspPlace_comap_eq`**: every cusp `x ∉ U` carries a place `W`
  over a cusp with `ι⁻¹(W) = 𝒪_{X̄,x}` (so `I_x := arithInertia W` is defined for every cusp);
* `CurvesJacobian.LocAn.comap_ffEmb_eq_of_relIndex_ne_zero`: places over cusps whose geometric
  cuspidal inertia groups are commensurable (one way) restrict to the same place of `K(X̄)`;
* **`CurvesJacobian.LocAn.comap_ffEmb_eq_of_relIndex_conj`**: the same for the arithmetic
  inertia groups up to conjugation in `Π_U` (`I_{W'}` ∩ `γ I_W γ⁻¹` of finite index in `I_{W'}`),
  with `comap_ffEmb_eq_of_arithInertia_conj` (`I_{W'} = γ I_W γ⁻¹`);
* **`CurvesJacobian.LocAn.eq_of_arithInertia_conj`** ([GalSect] Thm 1.3 (i), cusps): two cusps
  `x, y` with conjugate inertia groups are equal; `eq_of_relIndex_conj` with commensurability;
* **`CurvesJacobian.LocAn.arithDecomp_inf_ker`**: `I_x = D_x ∩ Δ_U` (the definition of `I_x` in
  [GalSect]); **`eq_of_arithDecomp_conj`**: cusps with conjugate decomposition groups are equal;
* **`CurvesJacobian.LocAn.commensurator_eq_arithDecomp`** ([GalSect] Thm 1.3 (ii), cusps): for
  every subgroup `H ≤ I_x` of finite index, the commensurator of `H` in `Π_U` is `D_x`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve CurvesJacobian.Cusp

universe u

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.LocAn

/-! ### Points of an open of a curve -/

section Chart

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

variable (k) in
/-- **A point at which all sections over `V` are regular lies in `V`** (`V` with finite
complement): for `V ≠ X`, `V` is the chart `π⁻¹ D₊(X₁)` of a rational function `τ` regular on `V`
(`exists_chartOne_eq`), and `τ ∈ 𝒪_{X,y}` forces `y ∈ V` (`mem_chartOne_iff`). -/
lemma mem_of_germ_mem_stalkVS (V : X.Opens) [Nonempty V] (hV : (V : Set X)ᶜ.Finite) {y : X}
    (h : ∀ a : Γ(X, V), X.germToFunctionField V a ∈ stalkVS k y) : y ∈ V := by
  by_cases hne : V = ⊤
  · subst hne
    trivial
  obtain ⟨τ, hτ, hVτ⟩ := exists_chartOne_eq k V hV hne
  subst hVτ
  obtain ⟨a, ha⟩ := (mem_range_germ_chartOne_iff hτ τ).2
    (isIntegral_algebraMap (x := (⟨τ, Algebra.self_mem_adjoin_singleton k τ⟩ :
      Algebra.adjoin k {τ})))
  have h1 := h a
  rw [ha] at h1
  exact (mem_chartOne_iff k hτ y).2 h1

end Chart

/-! ### Cusps and their inertia groups in `Π_U` -/

section Arith

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- Automorphisms over `L₀ = ι(K(X̄))` fix `ι(K(X̄))`. -/
lemma apply_ffEmb (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C))
    (z : C.Xbar.functionField) : τ (ffEmb Ω C hc z) = ffEmb Ω C hc z :=
  τ.commutes ⟨ffEmb Ω C hc z, z, rfl⟩

/-- **Every cusp carries a place over a cusp**: for a closed point `x ∉ U` of `X̄` there is a place
`W` of `K(X̄_Ω)^alg` over a cusp of `U` with `ι⁻¹(W) = 𝒪_{X̄,x}` (extension of `𝒪_{X̄,x}` along
`ι`, Mathlib `IsLocalRing.exists_factor_valuationRing`; `Ω ⊆ W` since `Ω` is integral over
`K ⊆ 𝒪_{X̄,x}`). -/
theorem exists_isCuspPlace_comap_eq {x : C.Xbar} (hx : x ∉ C.U) :
    ∃ W : ValuationSubring (FFClosure (geomCurve Ω C)),
      IsCuspPlace Ω C hc W ∧ W.comap (ffEmb Ω C hc) = stalkVS K x := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  set O := stalkVS K x
  let f : O →+* FFClosure (geomCurve Ω C) := (ffEmb Ω C hc).comp O.subtype
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hO : A.comap (ffEmb Ω C hc) = O := by
    apply le_antisymm
    · intro z hz
      by_contra hzO
      have hz0 : z ≠ 0 := fun h ↦ hzO (h ▸ zero_mem O)
      have hzi : z⁻¹ ∈ O := (O.mem_or_inv_mem z).resolve_left hzO
      have hu : IsUnit (f.codRestrict A.toSubring hA ⟨z⁻¹, hzi⟩) := by
        refine IsUnit.of_mul_eq_one ⟨_, hz⟩ (Subtype.ext ?_)
        change ffEmb Ω C hc z⁻¹ * ffEmb Ω C hc z = 1
        rw [map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hz0)]
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ((hloc.map_nonunit _) hu)
      have hb' : z⁻¹ * (b : C.Xbar.functionField) = 1 := congrArg Subtype.val hb
      rw [inv_mul_eq_one₀ hz0] at hb'
      exact hzO (hb' ▸ b.2)
    · intro z hz
      exact hA ⟨z, hz⟩
  have hK : ∀ d : K, algebraMap Ω (FFClosure (geomCurve Ω C)) (algebraMap K Ω d) ∈ A := fun d ↦ by
    rw [← ffEmb_algebraMap Ω C hc d]
    exact hA ⟨_, algebraMap_mem_stalkValuationSubring K _ x d⟩
  refine ⟨A, ⟨fun c ↦ ?_, fun hAU ↦ hx ?_⟩, hO⟩
  · let g : K →+* A :=
      ((algebraMap Ω (FFClosure (geomCurve Ω C))).comp (algebraMap K Ω)).codRestrict A.toSubring hK
    have hci : IsIntegral K c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
    have hint : IsIntegral A (algebraMap Ω (FFClosure (geomCurve Ω C)) c) := by
      refine ⟨(minpoly K c).map g, (minpoly.monic hci).map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have e : (algebraMap A (FFClosure (geomCurve Ω C))).comp g =
          (algebraMap Ω (FFClosure (geomCurve Ω C))).comp (algebraMap K Ω) := rfl
      rw [e, ← Polynomial.hom_eval₂]
      have := minpoly.aeval K c
      rw [Polynomial.aeval_def] at this
      rw [this, map_zero]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hz]
    exact z.2
  · refine mem_of_germ_mem_stalkVS K C.U C.cusps_finite fun a ↦ ?_
    have hmem : C.Xbar.germToFunctionField C.U a ∈ A.comap (ffEmb Ω C hc) := by
      rw [ValuationSubring.mem_comap, ffEmb_germ]
      exact hAU a
    rwa [hO] at hmem

/-- **Places over cusps with commensurable geometric inertia groups restrict to the same place of
`K(X̄)`**: by terminality (`exists_mem_ker_comap_eq`) `W = n⁻¹(W')` for some `n` acting trivially on
`π₁ᵉᵗ(U_Ω)`, and `n` fixes `ι(K(X̄))`. -/
theorem comap_ffEmb_eq_of_relIndex_ne_zero {W W' : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) (hW' : IsCuspPlace Ω C hc W')
    (hcomm : (geomCuspInertia Ω C W).relIndex (geomCuspInertia Ω C W') ≠ 0) :
    W.comap (ffEmb Ω C hc) = W'.comap (ffEmb Ω C hc) := by
  have hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W :=
    fun h ↦ hW.2 ((isCentredOn_geomOpen_iff Ω C hc W).1 h).2
  have hW'U : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W' :=
    fun h ↦ hW'.2 ((isCentredOn_geomOpen_iff Ω C hc W').1 h).2
  have hfin := compl_finite_baseChangeOpen K Ω C.nonempty
  have hhyp : 2 < 2 * (curveGenus Ω (geomCurve Ω C)).toNat +
      Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)) :=
    isHyperbolic_baseChange Ω C
  have hU3 : 2 < Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)) ∨
      ∃ O₀ : Subgroup (geomData Ω C).H, O₀.Normal ∧ IsOpen (O₀ : Set (geomData Ω C).H) ∧
        ((geomData Ω C).chartHom (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C))
          (genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
            (geomOpen Ω C))).ker ≤ O₀ ∧ CuspSep (geomData Ω C) O₀ W := by
    by_cases h3 : 2 < Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C))
    · exact Or.inl h3
    · exact Or.inr (exists_cuspSep (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
        (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (by omega) hfin hW.1 hWU)
  obtain ⟨n, -, hnW⟩ := exists_mem_ker_comap_eq (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) hfin hU3 hW.1 hW'.1 hWU hW'U hcomm
  ext z
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← hnW, ValuationSubring.mem_comap]
  change toArithAut Ω C hc n (ffEmb Ω C hc z) ∈ W' ↔ _
  rw [apply_ffEmb]

/-- **Places over cusps whose inertia groups are commensurable up to conjugation in `Π_U` restrict
to the same place of `K(X̄)`**: `γ = arithAction τ` moves `I_W` to `I_{τ W}` (`arithInertia_comap`),
`geomToPi` is injective, and `τ` fixes `ι(K(X̄))`. -/
theorem comap_ffEmb_eq_of_relIndex_conj {W W' : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) (hW' : IsCuspPlace Ω C hc W')
    (γ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (h : ((arithInertia Ω C hc W).map (MulAut.conj γ).toMonoidHom).relIndex
      (arithInertia Ω C hc W') ≠ 0) :
    W.comap (ffEmb Ω C hc) = W'.comap (ffEmb Ω C hc) := by
  obtain ⟨τ, rfl⟩ := arithAction_surjective Ω C hc γ
  rw [← arithInertia_comap] at h
  have hW₁ := isCuspPlace_comap Ω C hc τ.symm hW
  rw [arithInertia_eq_map_geom Ω C hc hW₁.1, arithInertia_eq_map_geom Ω C hc hW'.1,
    Subgroup.relIndex_map_map_of_injective _ _ (geomToPi_injective Ω C hc)] at h
  rw [← comap_ffEmb_eq_of_relIndex_ne_zero Ω C hc hW₁ hW' h]
  ext z
  simp only [ValuationSubring.mem_comap, RingHom.coe_coe]
  rw [apply_ffEmb]

/-- **Conjugate cuspidal inertia groups lie over the same place of `K(X̄)`.** -/
theorem comap_ffEmb_eq_of_arithInertia_conj {W W' : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) (hW' : IsCuspPlace Ω C hc W')
    (γ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (h : arithInertia Ω C hc W' = (arithInertia Ω C hc W).map (MulAut.conj γ).toMonoidHom) :
    W.comap (ffEmb Ω C hc) = W'.comap (ffEmb Ω C hc) :=
  comap_ffEmb_eq_of_relIndex_conj Ω C hc hW hW' γ
    (by rw [h, Subgroup.relIndex_self]; exact one_ne_zero)

/-- **[GalSect] Theorem 1.3 (i) for cusps, commensurable form**: if the inertia group `I_y` of a
cusp `y` meets a conjugate of the inertia group `I_x` of a cusp `x` in a subgroup of finite index
of `I_y`, then `x = y`. -/
theorem eq_of_relIndex_conj {x y : C.Xbar} {W W' : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) (hW' : IsCuspPlace Ω C hc W')
    (hx : W.comap (ffEmb Ω C hc) = stalkVS K x) (hy : W'.comap (ffEmb Ω C hc) = stalkVS K y)
    (γ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (h : ((arithInertia Ω C hc W).map (MulAut.conj γ).toMonoidHom).relIndex
      (arithInertia Ω C hc W') ≠ 0) : x = y := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI := isSeparated_of_over K C.Xbar
  exact stalkValuationSubring_injective (valuationRing_stalk_of_isCurveOver K C.Xbar)
    (hx.symm.trans ((comap_ffEmb_eq_of_relIndex_conj Ω C hc hW hW' γ h).trans hy))

/-- **[GalSect] Theorem 1.3 (i) for cusps** (`Galois Sections.txt` l.266–267: "If `x` is a cusp,
then `x` is completely determined by the conjugacy class of the closed subgroup `I_x ⊆ Π_{X_K}`"):
two cusps `x, y` of `U` whose inertia groups `I_x = arithInertia W`, `I_y = arithInertia W'` (for
places `W`, `W'` over `x`, `y`, `exists_isCuspPlace_comap_eq`) are conjugate in `Π_U` are equal. -/
theorem eq_of_arithInertia_conj {x y : C.Xbar}
    {W W' : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) (hW' : IsCuspPlace Ω C hc W')
    (hx : W.comap (ffEmb Ω C hc) = stalkVS K x) (hy : W'.comap (ffEmb Ω C hc) = stalkVS K y)
    (γ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (h : arithInertia Ω C hc W' = (arithInertia Ω C hc W).map (MulAut.conj γ).toMonoidHom) :
    x = y :=
  eq_of_relIndex_conj Ω C hc hW hW' hx hy γ
    (by rw [h, Subgroup.relIndex_self]; exact one_ne_zero)

/-- **[GalSect] Theorem 1.3 (ii) for cusps** (`Galois Sections.txt` l.269: "If `x` is a cusp, then
`D_x = C_{Π_{X_K}}(H)` for any open subgroup `H ⊆ I_x`"): for every subgroup `H ≤ I_W` of
finite index, the commensurator of `H` in `Π_U` is the decomposition group `arithDecomp W`. -/
theorem commensurator_eq_arithDecomp {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W)
    {H : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hle : H ≤ arithInertia Ω C hc W) (hfin : H.relIndex (arithInertia Ω C hc W) ≠ 0) :
    Subgroup.Commensurable.commensurator H = arithDecomp Ω C hc W := by
  have hc' : H.Commensurable (arithInertia Ω C hc W) :=
    ⟨hfin, by rw [Subgroup.relIndex_eq_one.2 hle]; exact one_ne_zero⟩
  exact (Subgroup.Commensurable.eq hc').trans (commensurator_arithInertia Ω C hc hW)

/-! ### `I_x = D_x ∩ Δ` and the decomposition-group form -/

/-- An automorphism over `L₀` fixing `Ω` fixes `L = K(X̄_Ω)`. -/
lemma fixes_L_of_fixes_Omega
    {τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C)}
    (hτ : ∀ c : Ω, τ (algebraMap Ω (FFClosure (geomCurve Ω C)) c) =
      algebraMap Ω (FFClosure (geomCurve Ω C)) c) (x : (geomData Ω C).L) : τ x = x := by
  let S := (τ : FFClosure (geomCurve Ω C) →+* FFClosure (geomCurve Ω C)).eqLocusField
    (RingHom.id _)
  have := algebraMap_mem_of_le Ω C hc S hτ
    (fun a ↦ τ.commutes ⟨_, secEmb_mem_arithFF Ω C hc a⟩)
    ((curveEquivL Ω (transcendental_geomCoord Ω C)).symm x)
  rw [← curveEquivL_apply Ω (transcendental_geomCoord Ω C), RingEquiv.apply_symm_apply] at this
  exact this

/-- An automorphism over `L₀` fixing `Ω`, as an element of `H = Gal(K(X̄_Ω)^alg / K(X̄_Ω))`. -/
def toGeomH (τ : FFClosure (geomCurve Ω C) ≃ₐ[arithFF Ω C hc] FFClosure (geomCurve Ω C))
    (hτ : ∀ c : Ω, τ (algebraMap Ω (FFClosure (geomCurve Ω C)) c) =
      algebraMap Ω (FFClosure (geomCurve Ω C)) c) : (geomData Ω C).H :=
  let τ' : FFClosure (geomCurve Ω C) ≃ₐ[K₀ Ω (coordT (geomCoord Ω C))]
      FFClosure (geomCurve Ω C) :=
    AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x ↦
      fixes_L_of_fixes_Omega Ω C hc hτ ⟨_, (geomData Ω C).L.algebraMap_mem x⟩
  ⟨τ', (geomData Ω C).le (by
    have hcl : IsClosed ((geomData Ω C).HL : Set (FFClosure (geomCurve Ω C) ≃ₐ[K₀ Ω
      (coordT (geomCoord Ω C))] FFClosure (geomCurve Ω C))) := (geomData Ω C).isClosed_HL
    have h := InfiniteGalois.fixingSubgroup_fixedField (⟨(geomData Ω C).HL, hcl⟩ : ClosedSubgroup _)
    change τ' ∈ (⟨(geomData Ω C).HL, hcl⟩ : ClosedSubgroup _).toSubgroup
    rw [← h, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact fixes_L_of_fixes_Omega Ω C hc hτ ⟨x, hx⟩)⟩

/-- **The inertia group of a cusp is the geometric part of its decomposition group**:
`I_W = D_W ∩ Δ_U` in `Π_U` ([GalSect] l.253–257: "`I_x := D_x ∩ Δ_X`"). An element of
`D_W ∩ Δ_U` is `arithAction τ` with `τ(W) = W` and `τ|_Ω = 1` (`exists_projGk_arithAction_conj`),
so `τ ∈ H` fixes the cusp place `W`, and `D_W ∩ H = I_W ∩ H` (`mem_decompH_iff_mem_inertia`). -/
theorem arithDecomp_inf_ker {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) :
    arithDecomp Ω C hc W ⊓ (projGk Ω C hc).toMonoidHom.ker = arithInertia Ω C hc W := by
  apply le_antisymm
  · rintro _ ⟨⟨τ, hτD, rfl⟩, hker⟩
    obtain ⟨t, ht⟩ := CuspChar.exists_projGk_arithAction_conj Ω C hc
    have h0 : projGk Ω C hc (arithAction Ω C hc τ) = 1 := hker
    rw [ht τ] at h0
    have h1 : mulEquivAutFiber K Ω (resOmega Ω C hc τ) = 1 := by
      have := congrArg (fun z ↦ t⁻¹ * z * t) h0
      simpa [mul_assoc] using this
    have h2 : resOmega Ω C hc τ = 1 :=
      (mulEquivAutFiber K Ω).injective (h1.trans (map_one _).symm)
    have hΩ : ∀ c : Ω, τ (algebraMap Ω (FFClosure (geomCurve Ω C)) c) =
        algebraMap Ω (FFClosure (geomCurve Ω C)) c := fun c ↦ by
      rw [← algebraMap_resOmega Ω C hc τ c, h2]
      rfl
    have hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W :=
      fun h ↦ hW.2 ((isCentredOn_geomOpen_iff Ω C hc W).1 h).2
    have hρD : toGeomH Ω C hc τ hΩ ∈ decompH (geomData Ω C) W :=
      mem_decompGal_iff_comap.1 hτD
    have hρI := (mem_decompH_iff_mem_inertia (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) hW.1 hWU _).1 hρD
    exact Subgroup.subset_closure ⟨τ, hρI, rfl⟩
  · refine le_inf ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨τ, hτ, rfl⟩
      exact ⟨τ, mem_decompGal_iff_comap.2 (comap_eq_of_mem_inertia hτ), rfl⟩
    · rw [arithInertia_eq_map_geom Ω C hc hW.1]
      rintro _ ⟨g, -, rfl⟩
      exact geomToPi_mem_ker Ω C hc g

/-- **Conjugate cuspidal decomposition groups have conjugate inertia groups** (`I = D ∩ Δ`,
`Δ_U` normal). -/
theorem arithInertia_eq_map_of_arithDecomp_conj
    {W W' : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) (hW' : IsCuspPlace Ω C hc W')
    (γ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (h : arithDecomp Ω C hc W' = (arithDecomp Ω C hc W).map (MulAut.conj γ).toMonoidHom) :
    arithInertia Ω C hc W' = (arithInertia Ω C hc W).map (MulAut.conj γ).toMonoidHom := by
  rw [← arithDecomp_inf_ker Ω C hc hW, ← arithDecomp_inf_ker Ω C hc hW', h,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj γ).injective]
  congr 1
  exact (Subgroup.Normal.map_conj_eq _ γ).symm

/-- **[GalSect] Theorem 1.3 (i), decomposition-group form for cusps** (`Galois Sections.txt`
l.265–266: "The closed point `x` is completely determined by the conjugacy class of the closed
subgroup `D_x ⊆ Π_{X_K}`", here for cusps `x, y`): cusps with conjugate decomposition groups are
equal. -/
theorem eq_of_arithDecomp_conj {x y : C.Xbar}
    {W W' : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hW : IsCuspPlace Ω C hc W) (hW' : IsCuspPlace Ω C hc W')
    (hx : W.comap (ffEmb Ω C hc) = stalkVS K x) (hy : W'.comap (ffEmb Ω C hc) = stalkVS K y)
    (γ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    (h : arithDecomp Ω C hc W' = (arithDecomp Ω C hc W).map (MulAut.conj γ).toMonoidHom) :
    x = y :=
  eq_of_arithInertia_conj Ω C hc hW hW' hx hy γ
    (arithInertia_eq_map_of_arithDecomp_conj Ω C hc hW hW' γ h)

end Arith

end CurvesJacobian.LocAn
