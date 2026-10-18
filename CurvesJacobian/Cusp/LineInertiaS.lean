/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LineTopS
import CurvesJacobian.Cusp.InertiaDescent
import CurvesJacobian.Cusp.LineBranchS

/-!
# `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞})) ≅ Π̂_{0,n+2}` with inertia, over any algebraically closed field

Let `k` be an algebraically closed field of characteristic `0` (of any cardinality), `S ⊆ k` with
`|S| = n + 1`, `U = ℙ¹ ∖ (S ∪ {∞}) = Spec k[t, 1/P_S(t)]` (`CurvesJacobian.Cusp.lineRingS`), and
`η` the geometric generic point of `U` given by a transcendental `t ∈ Ω`, `Ω / k(t)` Galois and
`Ω` separably closed (`CurvesJacobian.Cusp.lineGenS`).

**Main theorem** (`CurvesJacobian.Cusp.exists_continuousMulEquiv_lineInertiaS`): there are a
numbering `σ : S ≃ {0, …, n}` and `Θ : π₁ᵉᵗ(U, η) ≃ₜ* Π̂_{0,n+2}` such that for every cusp `c`
(`a ∈ S` or `∞`) and every place `W ⊇ k` of `Ω` over `c`, some conjugate of the inertia group of
`W` (`CurvesJacobian.Cusp.lineInertiaS`) is mapped by `Θ` onto the cuspidal inertia group
`I_{σ a}` resp. `I_{n+1}` (`CurvesJacobian.Cusp.cuspIndex`).

## Proof

Choose a countable algebraically closed `k₀ ⊆ k` containing `S`
(`CurvesJacobian.exists_countable_isAlgClosed_subfield`) and `S₀ ⊆ k₀` with image `S`. Then
`k ⊗[k₀] k₀[t, 1/P_{S₀}(t)] ≅ k[t, 1/P_S(t)]` (`CurvesJacobian.Cusp.lineRingSBaseChange`), so
by belyi's invariance of `π₁ᵉᵗ` under extension of algebraically closed fields the projection
`U ⟶ U₀ = ℙ¹_{k₀} ∖ (S₀ ∪ {∞})` induces `c : π₁ᵉᵗ(U, η) ≃ₜ* π₁ᵉᵗ(U₀, η₀)`, compatibly with the
Galois actions (`CurvesJacobian.Cusp.exists_continuousMulEquiv_lineGenS_baseChange`). Over the
countable `k₀`, `CurvesJacobian.Cusp.exists_continuousMulEquiv_lineS_branch` gives
`Θ₀ : π₁ᵉᵗ(U₀, η₀) ≃ₜ* Π̂_{0,n+2}`, and `Θ = Θ₀ ∘ c`.

If `c(I_W)` fixes a point of the fibre of a finite étale `Y₀ ⟶ U₀`, this point is a ring map
`φ : Γ(Y₀) → Ω` fixed by the inertia elements of `W`; it takes values in the relative algebraic
closure `Ω₀` of `k₀(t)` in `Ω`, and by descent of unramifiedness
(`CurvesJacobian.Cusp.inertia_fix_descent`) it is fixed by the inertia elements of `W ∩ Ω₀`
over `k₀(t)`. Hence `Y₀` has a branch at the cusp over `k₀`
(`CurvesJacobian.Cusp.nonempty_pBranch_of_ringHom_descent`), and the cuspidal generator acts with a
fixed point. The fixed-point criterion `CurvesJacobian.Cusp.exists_conj_mem_of_fixedPoints` gives
a conjugate of `Θ⁻¹(I_j)` inside `I_W`, and since `I_W` is abelian and `I_j` is commensurably
terminal, equality (`CurvesJacobian.Cusp.eq_inertia_of_inertia_le`).
-/

open CategoryTheory AlgebraicGeometry Polynomial AffOrbicurve PreGaloisCategory
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### The line over a subfield -/

section BaseChange

variable (k₀ k : Type u) [Field k₀] [Field k] [Algebra k₀ k] in
/-- The embedding `k₀ ↪ k` of fields. -/
abbrev fieldEmb : k₀ ↪ k := ⟨algebraMap k₀ k, (algebraMap k₀ k).injective⟩

variable {k₀ k : Type u} [Field k₀] [Field k] [Algebra k₀ k] {S₀ : Finset k₀} {S : Finset k}

/-- If `S` is the image of `S₀`, then `P_{S₀}` and `P_S` take the same values. -/
lemma aeval_polyS_eq_of_image (hS : S₀.map (fieldEmb k₀ k) = S) {A : Type*}
    [CommRing A] [Algebra k₀ A] [Algebra k A] [IsScalarTower k₀ k A] (x : A) :
    aeval x (polyS S₀) = aeval x (polyS S) := by
  rw [aeval_polyS, aeval_polyS, ← hS, Finset.prod_map]
  exact Finset.prod_congr rfl fun a _ ↦ by rw [IsScalarTower.algebraMap_apply k₀ k A]; rfl

variable (hS : S₀.map (fieldEmb k₀ k) = S)

/-- `k₀[t, 1/P_{S₀}(t)] → k[t, 1/P_S(t)]`, `t ↦ t`. -/
def lineRingSMap : lineRingS S₀ →ₐ[k₀] lineRingS S :=
  lineLiftS (lineTS S) (by rw [aeval_polyS_eq_of_image hS]; exact isUnit_aeval_lineTS S)

/-- `k[t, 1/P_S(t)] → k ⊗[k₀] k₀[t, 1/P_{S₀}(t)]`, `t ↦ 1 ⊗ t`. -/
def lineRingSMapTensor : lineRingS S →ₐ[k] k ⊗[k₀] lineRingS S₀ :=
  lineLiftS (1 ⊗ₜ lineTS S₀) (by
    rw [← aeval_polyS_eq_of_image hS]
    have h : aeval (1 ⊗ₜ lineTS S₀ : k ⊗[k₀] lineRingS S₀) (polyS S₀) =
        Algebra.TensorProduct.includeRight (aeval (lineTS S₀) (polyS S₀)) := by
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    rw [h]
    exact (isUnit_aeval_lineTS S₀).map _)

/-- **Base change of the line**: `k ⊗[k₀] k₀[t, 1/P_{S₀}(t)] ≅ k[t, 1/P_S(t)]` for `S` the image
of `S₀`. -/
def lineRingSBaseChange : (k ⊗[k₀] lineRingS S₀) ≃ₐ[k] lineRingS S :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId k (lineRingS S)) (lineRingSMap hS)
      fun _ _ ↦ Commute.all _ _)
    (lineRingSMapTensor hS)
    (lineRingS_algHom_ext (by
      simp [lineRingSMapTensor, lineRingSMap, Algebra.TensorProduct.lift_tmul]))
    (Algebra.TensorProduct.ext' fun a b ↦ by
      have hb : ((lineRingSMapTensor hS).restrictScalars k₀).comp
          (((Algebra.TensorProduct.lift (Algebra.ofId k (lineRingS S)) (lineRingSMap hS)
            fun _ _ ↦ Commute.all _ _).restrictScalars k₀).comp
              Algebra.TensorProduct.includeRight) = Algebra.TensorProduct.includeRight :=
        lineRingS_algHom_ext (by
          simp [lineRingSMapTensor, lineRingSMap])
      have hab : (a ⊗ₜ b : k ⊗[k₀] lineRingS S₀) = a • (1 ⊗ₜ b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hab, map_smul, map_smul]
      exact congrArg (a • ·) (DFunLike.congr_fun hb b))

@[simp]
lemma lineRingSBaseChange_tmul_lineTS :
    lineRingSBaseChange hS (1 ⊗ₜ lineTS S₀) = lineTS S := by
  simp [lineRingSBaseChange, lineRingSMap, Algebra.TensorProduct.lift_tmul]

end BaseChange

/-! ### Invariance of `π₁ᵉᵗ` of the line, with the Galois action -/

section Invariance

variable {k₀ k Ω : Type u} [Field k₀] [Field k] [Algebra k₀ k] [Field Ω] [Algebra k Ω]
  [Algebra k₀ Ω] [IsScalarTower k₀ k Ω] {t : Ω} {S₀ : Finset k₀} {S : Finset k}

/-- The projection `U ⟶ U₀` maps the geometric generic point of `U` to that of `U₀`. -/
lemma lineGenS_comp_baseChange (hS : S₀.map (fieldEmb k₀ k) = S) (ht : Transcendental k t)
    (ht' : Transcendental k₀ t) :
    lineGenS S ht ≫
      (Scheme.Spec.mapIso (lineRingSBaseChange hS).toRingEquiv.toCommRingCatIso.op).hom ≫
        FiniteEtale.baseChangeSpec k₀ k (lineRingS S₀) = lineGenS S₀ ht' := by
  rw [lineGenS_eq, lineGenS_eq]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  refine lineRingS_ringHom_ext (fun x ↦ ?_) ?_
  · change lineToΩS S ht (lineRingSBaseChange hS (1 ⊗ₜ algebraMap k₀ (lineRingS S₀) x)) =
      lineToΩS S₀ ht' (algebraMap k₀ (lineRingS S₀) x)
    have h : (1 ⊗ₜ algebraMap k₀ (lineRingS S₀) x : k ⊗[k₀] lineRingS S₀) =
        algebraMap k (k ⊗[k₀] lineRingS S₀) (algebraMap k₀ k x) := by
      rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h, AlgEquiv.commutes, AlgHom.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply k₀ k Ω]
  · change lineToΩS S ht (lineRingSBaseChange hS (1 ⊗ₜ lineTS S₀)) = lineToΩS S₀ ht' (lineTS S₀)
    rw [lineRingSBaseChange_tmul_lineTS, lineToΩS_lineTS, lineToΩS_lineTS]

variable [IsAlgClosed k₀] [CharZero k₀] [Countable k₀] [IsAlgClosed k] [IsSepClosed Ω]

/-- **`π₁ᵉᵗ` of the line descends to a countable algebraically closed subfield**, compatibly
with the Galois actions: for `k₀ ⊆ k` countable algebraically closed and `S` the image of
`S₀ ⊆ k₀`, there is `c : π₁ᵉᵗ(U, η) ≃ₜ* π₁ᵉᵗ(U₀, η₀)` (`U₀ = ℙ¹_{k₀} ∖ (S₀ ∪ {∞})`), under which
`g ∈ Gal(Ω / k(t))` acts on points `Spec Ω ⟶ Y₀` of finite étale `U₀`-schemes by precomposition
with `Spec g`. -/
theorem exists_continuousMulEquiv_lineGenS_baseChange [IsGalois (K₀ k t) Ω]
    (hS : S₀.map (fieldEmb k₀ k) = S) (ht : Transcendental k t)
    (ht' : Transcendental k₀ t) :
    ∃ c : π₁ᵉᵗ(lineGenS S ht) ≃ₜ* π₁ᵉᵗ(lineGenS S₀ ht'),
      ∀ (g : Ω ≃ₐ[K₀ k t] Ω) (Y : FiniteEtale (Spec (.of (lineRingS S₀))))
        (y : (FiniteEtale.fiber (lineGenS S₀ ht')).obj Y),
        (FiniteEtale.fiberObjEquivHom _ Y ((c (lineGaloisS S ht g)).hom.app Y y)).left =
          Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫
            (FiniteEtale.fiberObjEquivHom _ Y y).left := by
  let eB := Scheme.Spec.mapIso (lineRingSBaseChange hS).toRingEquiv.toCommRingCatIso.op
  let bc := FiniteEtale.baseChangeSpec k₀ k (lineRingS S₀)
  have hpt : lineGenS S ht ≫ eB.hom ≫ bc = lineGenS S₀ ht' := lineGenS_comp_baseChange hS ht ht'
  have hbc : ∀ (η : Spec (.of Ω) ⟶ Spec (.of (lineRingS S₀)))
      (h : (lineGenS S ht ≫ eB.hom) ≫ bc = η),
      Function.Bijective (FiniteEtale.fundamentalGroupMap bc h) := by
    rintro η rfl
    exact FiniteEtale.fundamentalGroupMap_baseChange_bijective_of_isAlgClosed
      (lineGenS S ht ≫ eB.hom)
  let F := FiniteEtale.fundamentalGroupMap (eB.hom ≫ bc) hpt
  have hbij : Function.Bijective F := by
    have h := FiniteEtale.fundamentalGroupMap_comp eB.hom bc rfl
      ((Category.assoc _ _ _).trans hpt) hpt
    change Function.Bijective (FiniteEtale.fundamentalGroupMap (eB.hom ≫ bc) hpt)
    rw [h, ContinuousMonoidHom.coe_comp]
    exact (hbc _ _).comp (FiniteEtale.fundamentalGroupMap_bijective_of_isIso _ rfl)
  let e : π₁ᵉᵗ(lineGenS S ht) ≃* π₁ᵉᵗ(lineGenS S₀ ht') := MulEquiv.ofBijective F.toMonoidHom hbij
  have hcont : Continuous e := F.continuous_toFun
  let c : π₁ᵉᵗ(lineGenS S ht) ≃ₜ* π₁ᵉᵗ(lineGenS S₀ ht') :=
    { e with
      continuous_toFun := hcont
      continuous_invFun := (hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }
  refine ⟨c, fun g Y y ↦ ?_⟩
  have hj : Spec.map (CommRingCat.ofHom (algebraMap (K₀ k t) Ω)) ≫
      Spec.map (CommRingCat.ofHom (lineToK₀S S ht).toRingHom) ≫ eB.hom ≫ bc =
        lineGenS S₀ ht' :=
    (Category.assoc _ _ _).symm.trans hpt
  have h := FiniteEtale.fundamentalGroupMap_galoisAction (K₀ k t)
    (Spec.map (CommRingCat.ofHom (lineToK₀S S ht).toRingHom)) (eB.hom ≫ bc) rfl hpt hj g
  have hc : c (lineGaloisS S ht g) = FiniteEtale.galoisAction (K₀ k t)
      (Spec.map (CommRingCat.ofHom (lineToK₀S S ht).toRingHom) ≫ eB.hom ≫ bc) hj g := h
  rw [hc, FiniteEtale.galoisAction_hom_app_left]

end Invariance

/-! ### Descent of fixed ring maps -/

section Descent

variable {Ω : Type u} [Field Ω]

/-- **The ring map of a geometric point**: a point `y : Spec Ω ⟶ Y` over `Spec ψ` gives
`φ : Γ(Y) → Ω` over `ψ`, and `φ` is fixed by every `g : Ω → Ω` with `Spec g ≫ y = y`. -/
lemma exists_ringHom_of_point {R : Type u} [CommRing R] (ψ : R →+* Ω)
    (Y : FiniteEtale (Spec (.of R))) (y : Spec (.of Ω) ⟶ Y.left)
    (hy : y ≫ Y.hom = Spec.map (CommRingCat.ofHom ψ)) (I : Set (Ω →+* Ω))
    (hI : ∀ g ∈ I, Spec.map (CommRingCat.ofHom g) ≫ y = y) :
    ∃ φ : Γ(Y.left, ⊤) →+* Ω,
      φ.comp (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) = ψ ∧
      ∀ g ∈ I, ∀ b, g (φ b) = φ b := by
  refine ⟨pointRingHom y, ?_, fun g hg b ↦ ?_⟩
  · have h : (pointRingHom y).comp Y.hom.appTop.hom =
        ψ.comp (Scheme.ΓSpecIso (.of R)).hom.hom :=
      ((pointRingHom_comp y Y.hom).symm.trans (congrArg pointRingHom hy)).trans
        (pointRingHom_specMap _)
    refine RingHom.ext fun r ↦ ?_
    have h' := RingHom.congr_fun h ((Scheme.ΓSpecIso (.of R)).inv.hom r)
    have e : (Scheme.ΓSpecIso (.of R)).hom.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) = r := by
      simp
    exact h'.trans (congrArg ψ e)
  · have h3 := congrArg pointRingHom (hI g hg)
    rw [pointRingHom_specMap_comp] at h3
    exact RingHom.congr_fun h3 b

variable {k₀ k : Type u} [Field k₀] [Field k] [Algebra k₀ k] [Algebra k Ω]
  [Algebra k₀ Ω] [IsScalarTower k₀ k Ω] {t : Ω}

set_option maxHeartbeats 1000000 in
-- elaborating the coordinate rings over `Ω₀ = lineAlgClosure k₀ t` is slow
/-- **A fixed ring map gives a branch over the subfield.** Let `k₀ ⊆ k` be algebraically closed
of characteristic `0`, `S₀ ⊆ k₀`, and `φ : Γ(Y₀) → Ω` a ring map over
`k₀[t, 1/P_{S₀}(t)] → Ω` (`Y₀` finite étale over `ℙ¹_{k₀} ∖ (S₀ ∪ {∞})`) fixed by the inertia
elements over `k(t)` of a place `W ⊇ k` of `Ω` over the cusp `c` (`v_W(u_c) < 1`). Then `Y₀` has
a branch at `c` over `k₀`: `φ` lands in the relative algebraic closure `Ω₀` of `k₀(t)` and is fixed
by the inertia elements of `W ∩ Ω₀` (`CurvesJacobian.Cusp.inertia_fix_descent`). -/
theorem nonempty_pBranch_of_ringHom_descent [IsAlgClosed k₀] [CharZero k] [IsSepClosed Ω]
    [IsGalois (K₀ k t) Ω] (S₀ : Finset k₀) (ht : Transcendental k t)
    (ht' : Transcendental k₀ t) (c : Option k₀) (hc : ∀ a, c = some a → a ∈ S₀)
    {W : ValuationSubring Ω} (hWk : ∀ x : k, algebraMap k Ω x ∈ W)
    (hWc : W.valuation (cuspCoordS (c.map (algebraMap k₀ k)) t) < 1)
    (Y : FiniteEtale (Spec (.of (lineRingS S₀)))) (φ : Γ(Y.left, ⊤) →+* Ω)
    (hφ : φ.comp (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (lineRingS S₀))).inv.hom) =
      (lineToΩS S₀ ht').toRingHom)
    (hfix : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, ∀ b, σ (φ b) = φ b) :
    Nonempty (PBranch k₀ (lineTS S₀) Y.hom (cuspP c) (cuspQ c)) := by
  haveI : CharZero k₀ := RingHom.charZero (algebraMap k₀ k)
  set ρ := Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (lineRingS S₀))).inv.hom with hρdef
  have hYfin : IsFinite Y.hom := inferInstance
  have hρ : ρ.Finite :=
    (@Scheme.Hom.finite_appTop _ (Spec (.of (lineRingS S₀))) Y.hom inferInstance hYfin).comp
      (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of (lineRingS S₀))).commRingCatIsoToRingEquiv.symm.surjective)
  -- `φ` lands in `Ω₀`
  have hmem : ∀ b, φ b ∈ lineAlgClosure k₀ t := by
    intro b
    obtain ⟨p, hp, hpb⟩ := hρ.to_isIntegral b
    refine mem_algebraicClosure_iff'.2 ⟨p.map (lineToK₀S S₀ ht').toRingHom, hp.map _, ?_⟩
    rw [eval₂_map]
    have h : (algebraMap (K₀ k₀ t) Ω).comp (lineToK₀S S₀ ht').toRingHom = φ.comp ρ := hφ.symm
    rw [h, ← Polynomial.hom_eval₂]
    exact (congrArg φ hpb).trans (map_zero φ)
  let φ₀ : Γ(Y.left, ⊤) →+* lineAlgClosure k₀ t := φ.codRestrict _ hmem
  have ht₀ : Transcendental k₀ (lineAlgGen k₀ t) := transcendental_lineGen ht
  have hφ₀ : φ₀.comp ρ = (lineToΩS S₀ ht₀).toRingHom := by
    ext r
    change φ (ρ r) = lineIncl k₀ t (lineToΩS S₀ ht₀ r)
    exact (RingHom.congr_fun hφ r).trans (DFunLike.congr_fun (lineRingS_algHom_ext
      (f := lineToΩS S₀ ht') (g := (lineIncl k₀ t).comp (lineToΩS S₀ ht₀))
      (by rw [lineToΩS_lineTS, AlgHom.comp_apply, lineToΩS_lineTS, lineIncl_lineGen])) r)
  -- the local coordinate `u₀ ∈ Ω₀`
  set u₀ : lineAlgClosure k₀ t := cuspCoordS c (lineAlgGen k₀ t) with hu₀
  have hιu : lineIncl k₀ t u₀ = cuspCoordS (c.map (algebraMap k₀ k)) t := by
    cases c with
    | none => simp only [u₀, cuspCoordS_none, Option.map_none, map_inv₀, lineIncl_lineGen]
    | some a =>
      simp only [u₀, cuspCoordS_some, Option.map_some, map_sub, AlgHom.commutes,
        lineIncl_lineGen]
      rw [IsScalarTower.algebraMap_apply k₀ k Ω]
  have hK : K₀ k (lineIncl k₀ t u₀) = K₀ k t := by rw [hιu, K₀_cuspCoordS]
  haveI : IsGalois (K₀ k (lineIncl k₀ t u₀)) Ω := hK ▸ inferInstance
  have hK₀ : K₀ k₀ u₀ = K₀ k₀ (lineAlgGen k₀ t) := K₀_cuspCoordS c (lineAlgGen k₀ t)
  haveI : IsGalois (K₀ k₀ u₀) (lineAlgClosure k₀ t) := hK₀ ▸ inferInstance
  have htu : Transcendental k (lineIncl k₀ t u₀) := hιu ▸ transcendental_cuspCoordS ht _
  have hWu : W.valuation (lineIncl k₀ t u₀) < 1 := hιu ▸ hWc
  have hdesc := fun b ↦ inertia_fix_descent (lineIncl k₀ t) (t₀ := u₀) htu hWk hWu (φ₀ b)
    (fun σ hσ ↦ hfix (algEquivOfK₀Eq hK σ) hσ b)
  -- the place `W₀ = W ∩ Ω₀`
  have hWk₀ : ∀ x : k₀, algebraMap k₀ (lineAlgClosure k₀ t) x ∈
      W.comap (lineIncl k₀ t : lineAlgClosure k₀ t →+* Ω) := fun x ↦ by
    rw [ValuationSubring.mem_comap]
    change lineIncl k₀ t (algebraMap k₀ (lineAlgClosure k₀ t) x) ∈ W
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k₀ k Ω]
    exact hWk _
  have hWc₀ : (W.comap (lineIncl k₀ t : lineAlgClosure k₀ t →+* Ω)).valuation
      (cuspCoordS c (lineAlgGen k₀ t)) < 1 :=
    (valuation_comap_lt_one_iff W _ _).2 hWu
  exact nonempty_pBranch_of_ringHom S₀ ht₀ c hc hWk₀ hWc₀ Y φ₀ hφ₀
    fun σ₀ hσ₀ b ↦ hdesc b (algEquivOfK₀Eq hK₀.symm σ₀) hσ₀

end Descent

/-! ### The main theorem -/

section Main

/-- **`π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞})) ≅ Π̂_{0,n+2}` with the inertia groups at the cusps going to conjugates
of the cuspidal inertia groups, over any algebraically closed field of characteristic `0`.** For
`S ⊆ k` with `|S| = n + 1` and `η` the geometric generic point of `U = ℙ¹ ∖ (S ∪ {∞})`
(`CurvesJacobian.Cusp.lineGenS`), there are a numbering `σ : S ≃ Fin (n + 1)` and
`Θ : π₁ᵉᵗ(U, η) ≃ₜ* Π̂_{0,n+2}` such that for every cusp `c : Option S` (`none` is `∞`) and every
place `W ⊇ k` of `Ω` over `c` (`v_W(u_c) < 1` for the local coordinate `u_c`), some conjugate of
the inertia group of `W` is mapped by `Θ` onto `I_{cuspIndex σ c}`. -/
theorem exists_continuousMulEquiv_lineInertiaS {k Ω : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω]
    (S : Finset k) {n : ℕ} (hS : S.card = n + 1) (ht : Transcendental k t) :
    ∃ (σ : S ≃ Fin (n + 1)) (Θ : π₁ᵉᵗ(lineGenS S ht) ≃ₜ* Pi1.ProfiniteSurfaceGroup 0 (n + 2)),
      ∀ (c : Option S) (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) →
        W.valuation (cuspCoordS (c.map Subtype.val) t) < 1 →
        ∃ τ : π₁ᵉᵗ(lineGenS S ht),
          (lineInertiaS S ht W).map ((Θ : π₁ᵉᵗ(lineGenS S ht) →*
            Pi1.ProfiniteSurfaceGroup 0 (n + 2)).comp
            (MulAut.conj τ).toMonoidHom) = Pi1.SurfaceGroup.inertia (cuspIndex σ c) := by
  classical
  -- the countable subfield `k₀` and `S₀ ⊆ k₀`
  obtain ⟨k₀, _, _, _, _, hsub⟩ :=
    exists_countable_isAlgClosed_subfield k (S : Set k) S.countable_toSet
  haveI : CharZero k₀ := RingHom.charZero (algebraMap k₀ k)
  letI : Algebra k₀ Ω := ((algebraMap k Ω).comp (algebraMap k₀ k)).toAlgebra
  haveI : IsScalarTower k₀ k Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hinj : Function.Injective (algebraMap k₀ k) := (algebraMap k₀ k).injective
  let S₀ : Finset k₀ := S.preimage (algebraMap k₀ k) hinj.injOn
  have hS₀ : S₀.map (fieldEmb k₀ k) = S := by
    ext b
    simp only [Finset.mem_map, fieldEmb,
      Function.Embedding.coeFn_mk, Finset.mem_preimage, S₀]
    refine ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ha, fun hb ↦ ?_⟩
    obtain ⟨a, h⟩ := hsub hb
    exact ⟨a, h ▸ hb, h⟩
  have hcard : S₀.card = n + 1 := by
    rw [← hS, ← hS₀, Finset.card_map]
  let eS : S₀ ≃ S := Equiv.ofBijective (fun a ↦ ⟨algebraMap k₀ k a, Finset.mem_preimage.1 a.2⟩)
    ⟨fun a b h ↦ Subtype.ext (hinj (congrArg Subtype.val h)), fun b ↦ by
      obtain ⟨a, h⟩ := hsub b.2
      exact ⟨⟨a, Finset.mem_preimage.2 (h ▸ b.2)⟩, Subtype.ext h⟩⟩
  have heS : ∀ b : S, algebraMap k₀ k (eS.symm b : k₀) = b := fun b ↦
    congrArg Subtype.val (eS.apply_symm_apply b)
  have ht' : Transcendental k₀ t := fun h ↦ ht (h.tower_top k)
  -- `π₁ᵉᵗ(U) ≅ π₁ᵉᵗ(U₀)` and the topological theorem over `k₀`
  obtain ⟨cπ, hcπ⟩ := exists_continuousMulEquiv_lineGenS_baseChange hS₀ ht ht'
  obtain ⟨σ₀, Θ₀, hΘ₀⟩ := exists_continuousMulEquiv_lineS_branch S₀ hcard (lineGenS S₀ ht')
  refine ⟨eS.symm.trans σ₀, cπ.trans Θ₀, fun cc W hWk hWc ↦ ?_⟩
  set c₀ : Option S₀ := cc.map eS.symm with hc₀
  have hcc : (c₀.map Subtype.val).map (algebraMap k₀ k) = cc.map Subtype.val := by
    cases cc with
    | none => rfl
    | some b =>
      simp only [c₀, Option.map_some]
      exact congrArg some (heS b)
  have hidx : cuspIndex (eS.symm.trans σ₀) cc = cuspIndex σ₀ c₀ := by
    cases cc <;> rfl
  have hcS : ∀ a, cc.map Subtype.val = some a → a ∈ S := by
    rintro a h
    cases cc with
    | none => exact absurd h (by simp)
    | some b =>
      simp only [Option.map_some, Option.some.injEq] at h
      exact h ▸ b.2
  have hc₀S : ∀ a, c₀.map Subtype.val = some a → a ∈ S₀ := by
    rintro a h
    cases hd : c₀ with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some b =>
      rw [hd] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact h ▸ b.2
  rw [hidx]
  set j := cuspIndex σ₀ c₀ with hj
  set A := lineInertiaS S ht W with hA
  have hAcl : IsClosed (A : Set π₁ᵉᵗ(lineGenS S ht)) := Subgroup.isClosed_topologicalClosure _
  let A' : Subgroup π₁ᵉᵗ(lineGenS S₀ ht') :=
    A.map (cπ : π₁ᵉᵗ(lineGenS S ht) →* π₁ᵉᵗ(lineGenS S₀ ht'))
  have hA'cl : IsClosed (A' : Set π₁ᵉᵗ(lineGenS S₀ ht')) := by
    rw [Subgroup.coe_map]
    exact cπ.toHomeomorph.isClosedMap _ hAcl
  -- a fixed point of `A'` gives a fixed point of `Θ₀⁻¹(c_j)`
  have key : ∀ (Y : FiniteEtale (Spec (.of (lineRingS S₀))))
      (y : (FiniteEtale.fiber (lineGenS S₀ ht')).obj Y), (∀ g ∈ A', g • y = y) →
        ∃ y' : (FiniteEtale.fiber (lineGenS S₀ ht')).obj Y,
          Θ₀.symm (ProfiniteGrp.ProfiniteCompletion.etaFn _ (Pi1.SurfaceGroup.cusp j)) • y' =
            y' := by
    intro Y y hy
    let y₁ := (FiniteEtale.fiberObjEquivHom (lineGenS S₀ ht') Y y).left
    have hy₁ : y₁ ≫ Y.hom = Spec.map (CommRingCat.ofHom (lineToΩS S₀ ht').toRingHom) :=
      (Over.w (FiniteEtale.fiberObjEquivHom (lineGenS S₀ ht') Y y)).trans (lineGenS_eq S₀ ht')
    have hI : ∀ g ∈ (fun σ : Ω ≃ₐ[K₀ k t] Ω ↦ (σ : Ω →+* Ω)) ''
        GaloisPi1.inertia (P := K₀ k t) W, Spec.map (CommRingCat.ofHom g) ≫ y₁ = y₁ := by
      rintro _ ⟨σ, hσ, rfl⟩
      have h1 : cπ (lineGaloisS S ht σ) • y = y :=
        hy _ ⟨_, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨σ, hσ, rfl⟩), rfl⟩
      rw [← hcπ σ Y y]
      exact congrArg (fun z ↦ (FiniteEtale.fiberObjEquivHom (lineGenS S₀ ht') Y z).left) h1
    obtain ⟨φ, hφ, hfixφ⟩ := exists_ringHom_of_point _ Y y₁ hy₁ _ hI
    obtain ⟨b⟩ := nonempty_pBranch_of_ringHom_descent S₀ ht ht' (c₀.map Subtype.val) hc₀S hWk
      (hcc ▸ hWc) Y φ hφ fun σ hσ ↦ hfixφ _ ⟨σ, hσ, rfl⟩
    exact hΘ₀ c₀ Y b
  have hfix : ∀ (Y : FiniteEtale (Spec (.of (lineRingS S₀))))
      (y : (FiniteEtale.fiber (lineGenS S₀ ht')).obj Y), (∀ g ∈ A', g • y = y) →
        ∃ y' : (FiniteEtale.fiber (lineGenS S₀ ht')).obj Y,
          ∀ τ ∈ (Pi1.SurfaceGroup.inertia (g := 0) j).map
          (Θ₀.symm : Pi1.ProfiniteSurfaceGroup 0 (n + 2) →* π₁ᵉᵗ(lineGenS S₀ ht')),
          τ • y' = y' := by
    intro Y y hy
    obtain ⟨y', hy'⟩ := key Y y hy
    refine ⟨y', ?_⟩
    have hS' : Pi1.SurfaceGroup.inertia (g := 0) j ≤
        (MulAction.stabilizer π₁ᵉᵗ(lineGenS S₀ ht') y').comap
          (Θ₀.symm : Pi1.ProfiniteSurfaceGroup 0 (n + 2) →* π₁ᵉᵗ(lineGenS S₀ ht')) := by
      refine Subgroup.topologicalClosure_minimal _ ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact hy'
      · exact (Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen _ y')).preimage
          Θ₀.symm.continuous
    rintro _ ⟨z, hz, rfl⟩
    exact hS' hz
  obtain ⟨g', hg'⟩ :=
    exists_conj_mem_of_fixedPoints (FiniteEtale.fiber (lineGenS S₀ ht')) hA'cl hfix
  refine ⟨(cπ.symm g')⁻¹, eq_inertia_of_inertia_le (g := 0) (r := n) j ?_ ?_⟩
  · intro z hz
    obtain ⟨a, ha, hca⟩ := hg' _ ⟨z, hz, rfl⟩
    have hca' : cπ a = g' * Θ₀.symm z * g'⁻¹ := hca
    have e1 : cπ ((cπ.symm g')⁻¹ * a * (cπ.symm g')⁻¹⁻¹) = g'⁻¹ * cπ a * g' := by
      rw [inv_inv, map_mul, map_mul, map_inv, cπ.apply_symm_apply]
    refine ⟨a, ha, ?_⟩
    change Θ₀ (cπ ((cπ.symm g')⁻¹ * a * (cπ.symm g')⁻¹⁻¹)) = z
    rw [e1, hca']
    simp [mul_assoc]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, lineInertiaS_comm S ht (cc.map Subtype.val) hcS hWk hWc a ha b hb]

end Main

end CurvesJacobian.Cusp
