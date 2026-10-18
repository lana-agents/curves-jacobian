/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithDecomp
import CurvesJacobian.Cusp.CurveInertiaIsoAny
import CurvesJacobian.Cusp.DGCArith
import CurvesJacobian.Picard.CurveGenus

/-!
# Automorphisms preserving the filling kernel extend over the filled cusps (MR8.6)

Let `U ⊆ U'` be nonempty opens of the smooth compactification `X̄` of a hyperbolic curve over a
number field `K`, both with a cusp, `U'_Ω` hyperbolic, and `N = ker(Π_U ↠ Π_{U'})` the filling
kernel (`CurvesJacobian.Cusp.fillMap`). For a finite étale `F : Spec Γ(U) ⟶ Spec Γ(U)` (e.g. a
`K`-automorphism given by the rel-isom-DGC) whose map `π₁ᵉᵗ(F)` (`coverPiHom`) preserves `N`, the
ring map `F^* : Γ(U) → Γ(U)` preserves `Γ(U') ⊆ Γ(U)`
(**`CurvesJacobian.Cusp.exists_resAlg_coverRing`**). This is the automorphism-extension step of
the uniqueness parts of [AbsTopII] Corollary 3.7 (b) and Corollary 3.8 (`Topics in Absolute
Anabelian Geometry II.txt` l.4698–4842): an automorphism of `U` compatible with the filling
`Π_U ↠ Π_{U'}` permutes the cusps of `U` lying in `U'`.

Proof. Places `W ⊇ Ω` of `K(X̄_Ω)^alg`:
* if `W` lies over a point of `U' ∖ U`, its inertia group `I_W` lies in `N`
  (`geomCuspInertia_map_le_ker`, from the filling formula `ker_fillMap_eq_map_iUnion`);
* if `W` lies over a cusp of `U'`, no finite-index subgroup of a conjugate of `I_W` lies in `N`
  (`false_of_le_ker`): its image in `Π_{U'}` is the cuspidal inertia group of `U'_Ω`
  (`map_cuspInertia_homOfLE`), which is nontrivial (`cuspInertia_fill_ne_bot`, via
  `Π̂_{g,r}` and the injectivity of `ℤ̂ → Π̂_{g,r}` for `r ≥ 2` or `g ≥ 1`) and torsion-free
  (`eq_one_of_isOfFinOrder_pi1`);
* `π₁ᵉᵗ(F)` maps `I_W` into `I_{σ⁻¹W}` with finite index (`exists_map_cuspAt_coverHom_le`),
  `σ` extending `F^*` to `K(X̄_Ω)^alg` (`coverσ`); hence `σ⁻¹` maps places centred on `U'_Ω` to
  places centred on `U'_Ω`;
* an element of `Γ(U)` lying in every place centred on `U'_Ω` is a section over `U'`
  (`exists_resAlg_eq_of_forall_mem`: places dominating the stalks `𝒪_{X̄,y}`, `y ∈ U'`, and the
  sheaf property `exists_section_of_forall_mem_stalk`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite WeilCurves.FunctionField Pi1.Orbifold AffOrbicurve
  ProfiniteGrp.ProfiniteCompletion PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- `ℤ̂` is nontrivial: the image of `1 ∈ ℤ` is not `1`. -/
lemma zhat_eta_ne_one :
    etaFn (GrpCat.of (Multiplicative ℤ)) (Multiplicative.ofAdd (1 : ℤ)) ≠ 1 := by
  let f : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))
  intro h
  have h2 : f (Multiplicative.ofAdd (1 : ℤ)) = 1 :=
    (liftFinite_eta f (Multiplicative.ofAdd (1 : ℤ))).symm.trans
      ((congrArg (liftFinite f) h).trans (map_one _))
  have h3 : Multiplicative.toAdd (f (Multiplicative.ofAdd (1 : ℤ))) = (1 : ZMod 2) := by simp [f]
  rw [h2, toAdd_one] at h3
  exact absurd h3 (by decide)

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U' : C.Xbar.Opens} (h : C.U ≤ U')
  (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-! ### Centred places of an affine open -/

omit [NumberField K] [Algebra.IsAlgebraic K Ω] in
/-- **Centred places of an affine open `V`**: `W` is centred on `V_Ω` iff `W ⊇ Ω` and
`W ⊇ Γ(V)`. -/
lemma isCentredOn_baseChangeOpen_iff {V : C.Xbar.Opens} (hV : IsAffineOpen V)
    [Nonempty (baseChangeOpen K Ω V)] (W : ValuationSubring (FFClosure (geomCurve Ω C))) :
    IsCentredOn (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
        (baseChangeOpen K Ω V) W ↔
      (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W) ∧
        ∀ a : Γ(C.Xbar, V), secEmb Ω C hV a ∈ W := by
  refine ⟨fun hW ↦ ⟨hW.1, fun a ↦ ?_⟩, fun hW ↦ ⟨hW.1, fun s ↦ ?_⟩⟩
  · obtain ⟨s, hs⟩ := secToTensor_surjective Ω C hV (1 ⊗ₜ a)
    have := hW.2 s
    rw [secEmb_apply, ← hs, tensorEmb_secToTensor]
    exact this
  · have key : ∀ t : Ω ⊗[K] Γ(C.Xbar, V),
        (tensorEmb Ω C hV t : FFClosure (geomCurve Ω C)) ∈ W := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        rw [coe_tensorEmb_tmul]
        exact mul_mem (hW.1 c) (hW.2 a)
      | add x y hx hy =>
        rw [map_add, IntermediateField.coe_add]
        exact add_mem hx hy
    have := key (secToTensor Ω C hV s)
    rw [tensorEmb_secToTensor] at this
    exact this

/-! ### Sections over `U'` -/

omit [Algebra.IsAlgebraic K Ω] in
include h hc' in
/-- `ι(Γ(U')) = secEmb (Γ(U'))` through `K(X̄)`. -/
lemma ffEmb_germ_of_le [Nonempty (baseChangeOpen K Ω U')] (a : Γ(C.Xbar, U')) :
    haveI := IsCurveOver.isIntegral K C.Xbar
    haveI : Nonempty U' := (C.nonempty.mono h).to_subtype
    ffEmb Ω C hc (C.Xbar.germToFunctionField U' a) =
      secEmb Ω C (isAffineOpen_of_le C h hc') a := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  haveI : Nonempty U' := (C.nonempty.mono h).to_subtype
  rw [← germ_resAlg C h a, ffEmb_germ, secEmb_resAlg Ω C hc h hc']

include h hc' in
/-- **An element of `Γ(U)` lying in every place centred on `U'_Ω` is a section over `U'`.** -/
theorem exists_resAlg_eq_of_forall_mem [Nonempty (baseChangeOpen K Ω U')]
    (b : Γ(C.Xbar, C.U))
    (hb : ∀ W : ValuationSubring (FFClosure (geomCurve Ω C)),
      (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W) →
      (∀ a : Γ(C.Xbar, U'), secEmb Ω C (isAffineOpen_of_le C h hc') a ∈ W) →
        secEmb Ω C (isAffineOpen_U C hc) b ∈ W) :
    ∃ a : Γ(C.Xbar, U'), resAlg K h a = b := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  haveI : Nonempty U' := (C.nonempty.mono h).to_subtype
  suffices hst : ∀ y ∈ U', C.Xbar.germToFunctionField C.U b ∈
      Set.range (algebraMap (C.Xbar.presheaf.stalk y) C.Xbar.functionField) by
    obtain ⟨a, ha⟩ := exists_section_of_forall_mem_stalk U' _ hst
    refine ⟨a, C.Xbar.germToFunctionField_injective C.U ?_⟩
    rw [germ_resAlg C h a, ha]
  intro y hy
  set O := stalkVS K y
  let f : O →+* FFClosure (geomCurve Ω C) := (ffEmb Ω C hc).comp O.subtype
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hO : A.comap (ffEmb Ω C hc) = O := by
    apply le_antisymm
    · intro z hz
      by_contra hzO
      have hz0 : z ≠ 0 := fun h0 ↦ hzO (h0 ▸ zero_mem O)
      have hzi : z⁻¹ ∈ O := (O.mem_or_inv_mem z).resolve_left hzO
      have hu : IsUnit (f.codRestrict A.toSubring hA ⟨z⁻¹, hzi⟩) := by
        refine IsUnit.of_mul_eq_one ⟨_, hz⟩ (Subtype.ext ?_)
        change ffEmb Ω C hc z⁻¹ * ffEmb Ω C hc z = 1
        rw [map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hz0)]
      obtain ⟨c, hcu⟩ := isUnit_iff_exists_inv.1 ((hloc.map_nonunit _) hu)
      have hc' : z⁻¹ * (c : C.Xbar.functionField) = 1 := congrArg Subtype.val hcu
      rw [inv_mul_eq_one₀ hz0] at hc'
      exact hzO (hc' ▸ c.2)
    · intro z hz
      exact hA ⟨z, hz⟩
  have hKA : ∀ c : K, algebraMap Ω (FFClosure (geomCurve Ω C)) (algebraMap K Ω c) ∈ A :=
    fun c ↦ by
      rw [← ffEmb_algebraMap Ω C hc]
      exact hA ⟨_, algebraMap_mem_stalkValuationSubring K _ y c⟩
  have hΩA : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ A := fun c ↦ by
    let g : K →+* A.toSubring := ((algebraMap Ω (FFClosure (geomCurve Ω C))).comp
      (algebraMap K Ω)).codRestrict A.toSubring hKA
    have hcomp : (algebraMap A.toSubring (FFClosure (geomCurve Ω C))).comp g =
        (algebraMap Ω (FFClosure (geomCurve Ω C))).comp (algebraMap K Ω) := rfl
    have hint : IsIntegral K c := Algebra.IsIntegral.isIntegral c
    have hcA := hint.map_of_comp_eq g (algebraMap Ω (FFClosure (geomCurve Ω C))) hcomp
    haveI : IsIntegrallyClosedIn A.toSubring (FFClosure (geomCurve Ω C)) :=
      inferInstanceAs (IsIntegrallyClosedIn A (FFClosure (geomCurve Ω C)))
    obtain ⟨z, hz⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hcA
    rw [← hz]
    exact z.2
  have hU'A : ∀ a : Γ(C.Xbar, U'), secEmb Ω C (isAffineOpen_of_le C h hc') a ∈ A := fun a ↦ by
    rw [← ffEmb_germ_of_le Ω C hc h hc']
    exact hA ⟨C.Xbar.germToFunctionField U' a, C.Xbar.presheaf.germ U' y hy a,
      by rw [Scheme.algebraMap_germ_eq_germToFunctionField]⟩
  have hbA := hb A hΩA hU'A
  rw [← ffEmb_germ] at hbA
  have hmem : C.Xbar.germToFunctionField C.U b ∈ O := by
    rw [← hO]
    exact hbA
  exact hmem

/-! ### Inertia groups and the filling kernel -/

include hc' in
/-- **Inertia groups of places over `U' ∖ U` lie in the filling kernel.** -/
lemma geomCuspInertia_map_le_ker [Nonempty (baseChangeOpen K Ω U')]
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hWV : IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (baseChangeOpen K Ω U') W)
    (hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W) :
    (geomCuspInertia Ω C W).map (geomToPi Ω C hc) ≤ (fillMap Ω C hc h).toMonoidHom.ker := by
  rw [ker_fillMap_eq_map_iUnion Ω C hc h hc']
  refine Subgroup.map_mono fun g hg ↦ Subgroup.le_topologicalClosure _
    (Subgroup.subset_normalClosure (Set.mem_iUnion₂.2 ⟨W, ⟨hWV, hWU⟩, hg⟩))

omit [NumberField K] [Algebra.IsAlgebraic K Ω] in
include h hc' in
/-- **The cuspidal inertia groups of `U'_Ω` are nontrivial** (also for a single cusp: via
`π₁ᵉᵗ(U'_Ω) ≃ₜ* Π̂_{g,r}` and the injectivity of `ℤ̂ → Π̂_{g,r}`, `r ≥ 2` or `g ≥ 1`). -/
theorem cuspInertia_fill_ne_bot [Nonempty (baseChangeOpen K Ω U')]
    (hhyp : Pi1.SurfaceGroup.IsHyperbolic (curveGenus Ω (geomCurve Ω C)).toNat
      (Nat.card ((baseChangeOpen K Ω U' : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C))))
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hkW : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W)
    (hW : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (baseChangeOpen K Ω U') W) :
    cuspInertia (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
      (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C)) (baseChangeOpen K Ω U') W ≠ ⊥ := by
  have hfin := compl_finite_baseChangeOpen K Ω (C.nonempty.mono h)
  have hne := compl_nonempty_baseChangeOpen K Ω hc'
  obtain ⟨Θ, hΘ⟩ := exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed (geomData Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (baseChangeOpen K Ω U') hfin hne
  obtain ⟨j, σ, hj⟩ := hΘ W hkW hW
  have hr0 : 0 < Nat.card ((baseChangeOpen K Ω U' : Set (geomCurve Ω C))ᶜ : Set _) :=
    haveI := hfin.to_subtype
    Nat.card_pos_iff.2 ⟨hne.to_subtype, inferInstance⟩
  have hr : 1 < Nat.card ((baseChangeOpen K Ω U' : Set (geomCurve Ω C))ᶜ : Set _) ∨
      0 < (curveGenus Ω (geomCurve Ω C)).toNat := by
    unfold Pi1.SurfaceGroup.IsHyperbolic at hhyp
    omega
  intro hbot
  rw [hbot, Subgroup.map_bot] at hj
  have hmem : Pi1.SurfaceGroup.cuspInertia j
      (etaFn (GrpCat.of (Multiplicative ℤ)) (Multiplicative.ofAdd (1 : ℤ))) ∈
        Pi1.SurfaceGroup.inertia j :=
    (Pi1.SurfaceGroup.cuspInertiaEquiv hr j _).2
  rw [← hj, Subgroup.mem_bot] at hmem
  exact zhat_eta_ne_one
    ((Pi1.SurfaceGroup.cuspInertia_injective hr j) (hmem.trans (map_one _).symm))

/-- `geomToPiFill` is injective. -/
lemma geomToPiFill_injective [Nonempty (baseChangeOpen K Ω U')] :
    Function.Injective (geomToPiFill Ω C hc h hc') := fun a b hab ↦ by
  haveI := isIntegral_specTensor_of_le Ω C h hc'
  haveI : Algebra.IsSeparable K Ω := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have := fundamentalGroupMap_baseChange_injective (k := K) (Ω := Ω) (R := Γ(C.Xbar, U'))
    (fillPoint Ω C hc h) hab
  exact (autContinuousMulEquivOfIso _).injective
    ((fundamentalGroupEquivOfIso _ _).symm.injective this)

omit [Algebra.IsAlgebraic K Ω] in
lemma geomToPiFill_one [Nonempty (baseChangeOpen K Ω U')] :
    geomToPiFill Ω C hc h hc' 1 = 1 := by
  simp only [geomToPiFill, map_one]

include hc' in
/-- **No finite-index subgroup of a conjugate of the inertia group of a cusp of `U'` lies in
the filling kernel.** -/
theorem false_of_le_ker [Nonempty (baseChangeOpen K Ω U')]
    (hhyp : Pi1.SurfaceGroup.IsHyperbolic (curveGenus Ω (geomCurve Ω C)).toNat
      (Nat.card ((baseChangeOpen K Ω U' : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C))))
    {W : ValuationSubring (FFClosure (geomCurve Ω C))}
    (hkW : ∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W)
    (hW : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (baseChangeOpen K Ω U') W)
    (t : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)))
    {J : Subgroup π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))}
    (hJ : J.relIndex (((geomCuspInertia Ω C W).map (geomToPi Ω C hc)).map
      (MulAut.conj t).toMonoidHom) ≠ 0)
    (hJN : J ≤ (fillMap Ω C hc h).toMonoidHom.ker) : False := by
  have hfin := compl_finite_baseChangeOpen K Ω (C.nonempty.mono h)
  have hne := compl_nonempty_baseChangeOpen K Ω hc'
  haveI : Nonempty (geomOpen Ω C) := inferInstance
  apply cuspInertia_fill_ne_bot Ω C h hc' hhyp hkW hW
  rw [← map_cuspInertia_homOfLE (geomData Ω C) (geomCurve Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C)) (curveGaloisData_H_le Ω _)
    (baseChangeOpen_mono K Ω h) W, eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  have hi : t * geomToPi Ω C hc g * t⁻¹ ∈
      ((geomCuspInertia Ω C W).map (geomToPi Ω C hc)).map (MulAut.conj t).toMonoidHom :=
    ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hJ hi
  have h1 : fillMap Ω C hc h ((t * geomToPi Ω C hc g * t⁻¹) ^ n) = 1 := hJN hmem.1
  rw [conj_pow, map_mul, map_mul, map_inv, conj_eq_one_iff, ← map_pow,
    fillMap_geomToPi Ω C hc h hc', map_pow, ← geomToPiFill_one Ω C hc h hc'] at h1
  have h2 := geomToPiFill_injective Ω C hc h hc' h1
  have hfo : IsOfFinOrder (geomFill Ω C h g) := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, h2⟩
  exact eq_one_of_isOfFinOrder_pi1 Ω (baseChangeOpen K Ω U') hfin hne _ hfo

/-! ### The extension lemma -/

include hc' in
/-- **Automorphism extension** ([AbsTopII] Cor 3.7 (b), Cor 3.8, uniqueness): if
`π₁ᵉᵗ(F)` (`coverPiHom`, for a finite étale `F : Spec Γ(U) ⟶ Spec Γ(U)`) preserves the filling
kernel `ker(Π_U ↠ Π_{U'})`, then `F^* : Γ(U) → Γ(U)` maps `Γ(U') ⊆ Γ(U)` into `Γ(U')`. -/
theorem exists_resAlg_coverRing [Nonempty (baseChangeOpen K Ω U')]
    (hhyp : Pi1.SurfaceGroup.IsHyperbolic (curveGenus Ω (geomCurve Ω C)).toNat
      (Nat.card ((baseChangeOpen K Ω U' : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C))))
    (F : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale F]
    (hN : ∀ n ∈ (fillMap Ω C hc h).toMonoidHom.ker,
      coverPiHom Ω C hc C hc F n ∈ (fillMap Ω C hc h).toMonoidHom.ker)
    (a : Γ(C.Xbar, U')) : ∃ a' : Γ(C.Xbar, U'), coverRing C C F (resAlg K h a) = resAlg K h a' := by
  suffices hall : ∀ W : ValuationSubring (FFClosure (geomCurve Ω C)),
      (∀ c : Ω, algebraMap Ω (FFClosure (geomCurve Ω C)) c ∈ W) →
      (∀ b : Γ(C.Xbar, U'), secEmb Ω C (isAffineOpen_of_le C h hc') b ∈ W) →
        secEmb Ω C (isAffineOpen_U C hc) (coverRing C C F (resAlg K h a)) ∈ W by
    obtain ⟨a', ha'⟩ := exists_resAlg_eq_of_forall_mem Ω C hc h hc' _ hall
    exact ⟨a', ha'.symm⟩
  intro W hkW hW'
  set σ := coverσ Ω C hc C hc F
  have key : ∀ b : Γ(C.Xbar, U'),
      secEmb Ω C (isAffineOpen_of_le C h hc') b ∈ W.comap (σ : _ →+* _) := by
    by_cases hWU : ∀ b : Γ(C.Xbar, C.U), secEmb Ω C (isAffineOpen_U C hc) b ∈ W
    · intro b
      rw [ValuationSubring.mem_comap, ← secEmb_resAlg Ω C hc h hc', RingEquiv.coe_toRingHom,
        coverσ_secEmb]
      exact hWU _
    have hWcusp : IsCuspPlace Ω C hc W := ⟨hkW, hWU⟩
    have hWV : IsCentredOn (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C)) (baseChangeOpen K Ω U') W :=
      (isCentredOn_baseChangeOpen_iff Ω C (isAffineOpen_of_le C h hc') W).2 ⟨hkW, hW'⟩
    have hWU' : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W := fun h' ↦
      hWU ((isCentredOn_geomOpen_iff Ω C hc W).1 h').2
    have hW'cusp := (isCuspPlace_comap_coverσ Ω C hc C hc F W).1 hWcusp
    by_contra hcon
    have hW'V : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
        (curveEquivL Ω (transcendental_geomCoord Ω C)) (baseChangeOpen K Ω U')
          (W.comap (σ : _ →+* _)) := fun h' ↦
      hcon ((isCentredOn_baseChangeOpen_iff Ω C (isAffineOpen_of_le C h hc') _).1 h').2
    obtain ⟨β, hβ⟩ := exists_map_cuspAt_coverHom_le Ω C hc C hc F (arithIso Ω C hc)
    obtain ⟨-, hidx⟩ := hβ W
    obtain ⟨t, ht⟩ := exists_cuspAt_eq_conj Ω C hc β
    rw [ht, arithInertia_eq_map_geom Ω C hc hW'cusp.1] at hidx
    refine false_of_le_ker Ω C hc h hc' hhyp hW'cusp.1 hW'V t hidx ?_
    rintro _ ⟨n, hn, rfl⟩
    apply hN
    rw [cuspAt_arithIso, arithInertia_eq_map_geom Ω C hc hkW] at hn
    exact geomCuspInertia_map_le_ker Ω C hc h hc' hWV hWU' hn
  rw [← coverσ_secEmb, secEmb_resAlg Ω C hc h hc']
  exact key a

end CurvesJacobian.Cusp
