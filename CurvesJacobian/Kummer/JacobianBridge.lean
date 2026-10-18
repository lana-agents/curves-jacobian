/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.BaseChangeFunctionField
import CurvesJacobian.Picard.DivisorPic
import CurvesJacobian.Picard.PicDescentInj
import CurvesJacobian.Galois.PicTorsionCount
import CurvesJacobian.Scheme.ConstantField

/-!
# The Galois model's `Pic(F k̄)` and the Jacobian; Kummer-faithfulness for `J`

Let `X` be a curve over a field `k` of characteristic `0` with a rational point `σ`, `τ ∈ K(X)`
transcendental, `D = curveGaloisData k hτ` its Galois model, `k̄ = kbar k Ω` and
`X_{k̄} = baseChangeKbar k X`. We compare the divisor class group `Pic(F k̄)` of the Galois model
(on which `H` acts by `picAct`) with the rigidified Picard group `Pic_{X/k,σ}(k̄)` (on which
`G_k` acts by `picGal`), and deduce `IsKummerFaithfulJac D` from `⋂_N N · J(k) = 0`.

* `CurvesJacobian.Kummer.picFFEquiv`: `Pic(F k̄) ≃ Pic(K(X_{k̄}))`, induced by `ffEquiv`;
  it preserves degrees (`deg_picFFEquiv`).
* `CurvesJacobian.Kummer.picPsi`: `Pic(F k̄) ↪ Pic_{X/k,σ}(k̄)` (`picPsi_injective`), with
  `picPsi x ∈ J(k̄)` iff `deg x = 0` (`picPsi_mem_jacPoints_iff`), and
  **`CurvesJacobian.Kummer.jacPsi : Pic⁰(F k̄) →+ J(k̄)`**, `jacPsi_injective`.
* **`CurvesJacobian.Kummer.picPsi_picAct`** (`G_k`-equivariance): for `h ∈ H` and
  `g = hToGk h`, `picPsi (picAct h x) = picGal g (picPsi x)`. On generators `[P]`: the pull-back
  of the divisor `x_{P'}` of the rational point at `P' = ffEquiv(P)` along
  `α_g = 𝟙_X ×_k Spec(g)` is the divisor of the section `Spec(g) ≫ x_{P'} ≫ α_g⁻¹`, which is
  the rational point at the place `ffEquiv(h P)` (`pointOfPlace_placeMap_autF`, from
  `ffEquiv_autF` and `galFF_mem_stalkValuationSubring_iff`).
* `CurvesJacobian.Kummer.mem_range_of_isAlgebraic_F`: `k` is algebraically closed in `F D`
  (`F D = L ≅ K(X)`), so `hToGk` is surjective.
* **`CurvesJacobian.Kummer.isKummerFaithfulJac_curveGaloisData`**: if
  `⋂_{N ≥ 1} N · J(k) = 0` for `J(k) = jacPoints X σ hσ k`, then `IsKummerFaithfulJac D`.

**On the hypothesis of the last theorem.** [AbsTopIII] Def. 1.5 (Kummer-faithful field), applied
to the semi-abelian variety `A = J` (the Jacobian of `X`) over `k_H = k`, says exactly
`⋂_{N ≥ 1} N · J(k) = 0`. The Jacobian of this library is not (yet) a `k`-scheme, so this input
is taken as the explicit hypothesis `hJ` on the group `J(k) = Pic⁰_{X/k,σ}(k)` of `k`-points; this
is recorded debt until `J` is available as a `k`-scheme. Everything else is proved: an element of
`⋂_N N · Pic(F k̄)^{G_k}` has degree `0`, maps to `⋂_N N · J(k̄)^{G_k}`, and
`J(k) ≅ J(k̄)^{G_k}` (`jacPointsEquivInv`).
-/

open CategoryTheory Limits AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian.Kummer

open CurvesJacobian.Cusp

section Degree

variable {κ K K' : Type*} [Field κ] [IsAlgClosed κ] [Field K] [Field K'] [Algebra κ K]
  [Algebra κ K'] [IsFunctionField κ K] [IsFunctionField κ K']

/-- Over an algebraically closed field, `k`-isomorphisms of function fields preserve degrees of
divisors. -/
lemma deg_divisorEquivOfAlgEquiv (e : K ≃ₐ[κ] K') (E : Divisor κ K) :
    (divisorEquivOfAlgEquiv e E).deg = E.deg := by
  induction E using Finsupp.induction_linear with
  | zero => rw [map_zero]; rfl
  | add a b ha hb => rw [map_add, Divisor.deg_add, Divisor.deg_add, ha, hb]
  | single P n =>
    change Divisor.deg (Finsupp.equivMapDomain (placeEquivOfAlgEquiv e) (Finsupp.single P n)) = _
    rw [Finsupp.equivMapDomain_single, Divisor.deg_single, Divisor.deg_single, Place.deg_eq_one,
      Place.deg_eq_one]

end Degree

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- Shortcut for the `k̄`-algebra structure of `F k̄` (a slow instance search otherwise). -/
instance algebraKbarF :
    Algebra (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) :=
  inferInstance

/-! ### The bridge `Pic(F k̄) ↪ Pic_{X/k,σ}(k̄)` -/

section Bridge

/-- **`Pic(F k̄) ≃ Pic(K(X_{k̄}))`**, induced by `ffEquiv : F k̄ ≃ₐ[k̄] K(X_{k̄})`. -/
def picFFEquiv : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≃+
    Pic (kbar k (FFClosure X)) (baseChangeKbar k X).functionField :=
  picEquivOfAlgEquiv (ffEquiv k hτ)

lemma picFFEquiv_mk
    (E : Divisor (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) :
    picFFEquiv k hτ (E : Pic _ _) = (divisorEquivOfAlgEquiv (ffEquiv k hτ) E : Pic _ _) :=
  rfl

/-- `picFFEquiv` preserves degrees. -/
lemma deg_picFFEquiv
    (x : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) :
    Pic.deg _ _ (picFFEquiv k hτ x) = Pic.deg _ _ x := by
  induction x using QuotientAddGroup.induction_on with
  | H E => exact deg_divisorEquivOfAlgEquiv _ E

variable (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- **The map `Pic(F k̄) → Pic_{X/k,σ}(k̄)`**: `Pic(F k̄) ≃ Pic(K(X_{k̄}))` followed by
`[∑ nᵢ Pᵢ] ↦ ∑ nᵢ [𝒪(x_{Pᵢ})]` (`picDivPt`). -/
def picPsi : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) →+
    picPt X σ hσ (kbar k (FFClosure X)) :=
  (picDivPt X (kbar k (FFClosure X)) σ hσ).comp (picFFEquiv k hτ).toAddMonoidHom

lemma coe_picPsi (x : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) :
    (picPsi k hτ σ hσ x : (baseChangeKbar k X).Pic) =
      picDivPic X (kbar k (FFClosure X)) (picFFEquiv k hτ x) :=
  rfl

/-- `Pic(F k̄) → Pic_{X/k,σ}(k̄)` is injective. -/
theorem picPsi_injective : Function.Injective (picPsi k hτ σ hσ) :=
  (picDivPt_injective X (kbar k (FFClosure X)) σ hσ).comp (picFFEquiv k hτ).injective

/-- `picPsi x` lies in `J(k̄)` iff `deg x = 0`. -/
theorem picPsi_mem_jacPoints_iff
    (x : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) :
    picPsi k hτ σ hσ x ∈ jacPoints X σ hσ (kbar k (FFClosure X)) ↔ Pic.deg _ _ x = 0 := by
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [mem_jacPoints_iff_degPic, coe_picPsi, picFFEquiv_mk, picDivPic_mk, degPic_divPic,
    deg_divisorEquivOfAlgEquiv]
  rfl

/-- **The bridge `Pic⁰(F k̄) → J(k̄)`** for the Galois model of `X`: `ffEquiv` followed by
`jacBridge`. -/
def jacPsi : (Pic.deg (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))).ker →+
    jacPoints X σ hσ (kbar k (FFClosure X)) :=
  (jacBridge X (kbar k (FFClosure X)) σ hσ).comp
    (((picFFEquiv k hτ).toAddMonoidHom.comp (Pic.deg _ _).ker.subtype).codRestrict
      (Pic.deg (kbar k (FFClosure X)) (baseChangeKbar k X).functionField).ker fun x ↦
        AddMonoidHom.mem_ker.2 ((deg_picFFEquiv k hτ x.1).trans x.2))

@[simp]
lemma coe_jacPsi
    (x : (Pic.deg (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))).ker) :
    (jacPsi k hτ σ hσ x : picPt X σ hσ (kbar k (FFClosure X))) = picPsi k hτ σ hσ x :=
  rfl

/-- **The bridge `Pic⁰(F k̄) → J(k̄)` is injective.** -/
theorem jacPsi_injective : Function.Injective (jacPsi k hτ σ hσ) := fun x y h ↦
  Subtype.ext (picPsi_injective k hτ σ hσ (by
    rw [← coe_jacPsi, ← coe_jacPsi, h]))

end Bridge

/-! ### `G_k`-equivariance -/

section Equivariance

/-- **Places and points under the Galois action**: if `α_g(y)` is the point of the place
`ffEquiv(Q)` (`g = hToGk h`), then `y` is the point of the place `ffEquiv(h Q)`. -/
theorem pointOfPlace_placeMap_autF (h : (curveGaloisData k hτ).H)
    (Q : Place (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))))
    (y : baseChangeKbar k X)
    (hy : galMap k (hToGk _ h) y = pointOfPlace (kbar k (FFClosure X)) (baseChangeKbar k X)
      (CurvesJacobian.placeMap (ffEquiv k hτ) Q)) :
    pointOfPlace (kbar k (FFClosure X)) (baseChangeKbar k X)
      (CurvesJacobian.placeMap (ffEquiv k hτ) (Kummer.placeMap (autF _ h) Q)) = y := by
  haveI := isSeparated_of_over (kbar k (FFClosure X)) (baseChangeKbar k X)
  apply stalkValuationSubring_injective
    (valuationRing_stalk_of_isCurveOver (kbar k (FFClosure X)) (baseChangeKbar k X))
  rw [← place_val_eq (kbar k (FFClosure X)) (baseChangeKbar k X)]
  ext f
  obtain ⟨x, rfl⟩ : ∃ x, ffEquiv k hτ ((autF _ h : F (Kummer.baseChange (curveGaloisData k hτ))
      ≃+* F (Kummer.baseChange (curveGaloisData k hτ))) x) = f :=
    ⟨_, by rw [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]⟩
  rw [CurvesJacobian.mem_placeMap_apply (ffEquiv k hτ)]
  refine (Kummer.mem_placeMap (τ := autF _ h) (Q := Q)).trans ?_
  refine (iff_of_eq (congrArg (· ∈ Q.1) (RingEquiv.symm_apply_apply _ x))).trans ?_
  rw [ffEquiv_autF k hτ h x, galFF_mem_stalkValuationSubring_iff k _ (hToGk _ h) y]
  have h1 := place_val_eq (kbar k (FFClosure X)) (baseChangeKbar k X)
    (CurvesJacobian.placeMap (ffEquiv k hτ) Q)
  rw [← hy] at h1
  have h2 := CurvesJacobian.mem_placeMap_apply (ffEquiv k hτ) Q x
  rw [h1] at h2
  exact h2.symm

omit [CharZero k] [IsCurveOver k X] in
lemma specAut_comp_specAut_inv (g : Gk k (FFClosure X)) :
    specAut g ≫ specAut g⁻¹ = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  exact congrArg Subtype.val (g.apply_symm_apply c)

/-- **The divisor of a rational point under the Galois action**: the pull-back of `𝒪(x_{P'})`,
`P' = ffEquiv(Q)`, along `α_g` (`g = hToGk h`) is `𝒪(x_{ffEquiv(h Q)})`. -/
theorem map_picClass_pointDiv_galMap (h : (curveGaloisData k hτ).H)
    (Q : Place (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) :
    Scheme.Pic.map (galMap k (hToGk _ h))
        (pointDiv X (kbar k (FFClosure X)) (CurvesJacobian.placeMap (ffEquiv k hτ) Q)).picClass =
      (pointDiv X (kbar k (FFClosure X))
        (CurvesJacobian.placeMap (ffEquiv k hτ) (Kummer.placeMap (autF _ h) Q))).picClass := by
  set g := hToGk _ h
  set s := placeSection (kbar k (FFClosure X)) (baseChangeKbar k X)
    (CurvesJacobian.placeMap (ffEquiv k hτ) Q)
  have hs : s ≫ pullback.snd _ _ = 𝟙 _ := placeSection_comp _
  set s' := specAut g ≫ s ≫ galMap k g⁻¹
  have h1 : s' ≫ galMap k g = specAut g ≫ s := by
    simp only [s', Category.assoc, ← galMap_mul, inv_mul_cancel, galMap_one, Category.comp_id]
  have hs' : s' ≫ pullback.snd _ _ = 𝟙 _ := by
    simp only [s', Category.assoc, galMap_snd, reassoc_of% hs]
    exact specAut_comp_specAut_inv k g
  have hpt : ∀ z, s' z = pointOfPlace (kbar k (FFClosure X)) (baseChangeKbar k X)
      (CurvesJacobian.placeMap (ffEquiv k hτ) (Kummer.placeMap (autF _ h) Q)) := fun z ↦
    (pointOfPlace_placeMap_autF k hτ h Q (s' z) (by
      rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, placeSection_apply])).symm
  have hsec := placeSection_unique _ s' hs' hpt
  haveI := isClosedImmersion_of_section X (specAlgebraMap (k₀ := k) (kbar k (FFClosure X))) s hs
  have hker := ker_comap_bcMap (X ↘ Spec (CommRingCat.of k)) (specAut g) _ _
    (specAut_comp_specAlgebraMap g) s hs s' hs' h1
  refine RelEffCartier.map_picClass_of_ideal_eq _ _ _ ?_
  rw [pointDiv_ideal, pointDiv_ideal, ← hsec, ← hker]
  rfl

/-- **`G_k`-equivariance of the bridge**: for `h ∈ H` with image `g = hToGk h ∈ G_k`,
`picPsi (picAct h x) = picGal g (picPsi x)`. -/
theorem picPsi_picAct (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (h : (curveGaloisData k hτ).H)
    (x : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) :
    picPsi k hτ σ hσ (picAct _ h x) = picGal X σ hσ (hToGk _ h) (picPsi k hτ σ hσ x) := by
  apply Subtype.ext
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  change divPic X (kbar k (FFClosure X)) (divisorEquivOfAlgEquiv (ffEquiv k hτ)
      (divMap (autF _ h) E)) = Scheme.Pic.map (galMap k (hToGk _ h))
        (divPic X (kbar k (FFClosure X)) (divisorEquivOfAlgEquiv (ffEquiv k hτ) E))
  have key : ((divPic X (kbar k (FFClosure X))).comp
      ((divisorEquivOfAlgEquiv (ffEquiv k hτ)).toAddMonoidHom.comp (divMap (autF _ h)))) =
      (Scheme.Pic.map (galMap k (hToGk _ h))).comp ((divPic X (kbar k (FFClosure X))).comp
        (divisorEquivOfAlgEquiv (ffEquiv k hτ)).toAddMonoidHom) := by
    refine Finsupp.addHom_ext fun P n ↦ ?_
    change divPic X _ (Finsupp.equivMapDomain _ (Finsupp.equivMapDomain _ (Finsupp.single P n))) =
      Scheme.Pic.map _ (divPic X _ (Finsupp.equivMapDomain _ (Finsupp.single P n)))
    rw [Finsupp.equivMapDomain_single, Finsupp.equivMapDomain_single,
      Finsupp.equivMapDomain_single, divPic_single, divPic_single, map_zsmul]
    exact congrArg (n • ·) (map_picClass_pointDiv_galMap k hτ h P).symm
  exact DFunLike.congr_fun key E

end Equivariance

/-! ### Kummer-faithfulness for the Jacobian -/

section Faithful

omit [IsGalois (K₀ k (coordT τ)) (FFClosure X)] in
/-- **`k` is algebraically closed in `F D`**: `F D = L ≅ K(X)` and `k` is algebraically closed in
the function field of the curve `X`. -/
theorem mem_range_of_isAlgebraic_F (x : F (curveGaloisData k hτ)) (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k (F (curveGaloisData k hτ))) := by
  set e := (curveEquivL k hτ).symm ⟨x, x.2⟩
  have he : algebraMap X.functionField (FFClosure X) e = x := by
    rw [← curveEquivL_apply k hτ, RingEquiv.apply_symm_apply]
  have hx' : IsAlgebraic k (x : FFClosure X) :=
    (isAlgebraic_algHom_iff ((F (curveGaloisData k hτ)).val.restrictScalars k)
      Subtype.val_injective).mpr hx
  have he' : IsAlgebraic k e := by
    rw [← he] at hx'
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom k X.functionField (FFClosure X))
      (algebraMap X.functionField (FFClosure X)).injective).mp hx'
  obtain ⟨c, hc⟩ := curve_mem_range_algebraMap_of_isAlgebraic k X he'
  refine ⟨c, Subtype.ext ?_⟩
  change algebraMap k (FFClosure X) c = x
  rw [IsScalarTower.algebraMap_apply k X.functionField (FFClosure X), hc, he]

variable (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- A `G_k`-invariant class of degree `0` in `Pic(F k̄)` maps to a `G_k`-invariant point of
`J(k̄)`. -/
theorem picPsi_mem_jacPoints_inf_picInv
    {y : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))}
    (hy : y ∈ picInv (curveGaloisData k hτ)) (hy0 : Pic.deg _ _ y = 0) :
    picPsi k hτ σ hσ y ∈ (jacPoints X σ hσ (kbar k (FFClosure X)) ⊓
      CurvesJacobian.picInv X σ hσ k (kbar k (FFClosure X))) :=
  AddSubgroup.mem_inf.mpr ⟨(picPsi_mem_jacPoints_iff k hτ σ hσ y).2 hy0, fun g ↦ by
    obtain ⟨h, rfl⟩ := hToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ) g
    rw [← picPsi_picAct, hy h]⟩

/-- **Descent to `J(k)`**: a `G_k`-invariant class `y` of degree `0` in `Pic(F k̄)` comes from a
`k`-point of the Jacobian: `picPsi y = picRes z` for some `z ∈ J(k)` (`jacPointsEquivInv`). -/
theorem exists_jacPoints_picRes_eq_picPsi
    {y : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))}
    (hy : y ∈ picInv (curveGaloisData k hτ)) (hy0 : Pic.deg _ _ y = 0) :
    ∃ z ∈ jacPoints X σ hσ k, picRes X σ hσ k (kbar k (FFClosure X)) z = picPsi k hτ σ hσ y := by
  set w := (jacPointsEquivInv X σ hσ k (kbar k (FFClosure X))).symm
    ⟨_, picPsi_mem_jacPoints_inf_picInv k hτ σ hσ hy hy0⟩
  refine ⟨w, w.2, ?_⟩
  rw [← coe_jacPointsEquivInv, AddEquiv.apply_symm_apply]

/-- An element of `⋂_{N ≥ 1} N · Pic(F k̄)` has degree `0`. -/
lemma deg_eq_zero_of_forall_nsmul
    {x : Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))}
    (hx : ∀ N : ℕ, 0 < N → ∃ y, N • y = x) : Pic.deg _ _ x = 0 := by
  obtain ⟨y, hy⟩ := hx ((Pic.deg _ _ x).natAbs + 1) (Nat.succ_pos _)
  have hd := congrArg (Pic.deg _ _) hy
  rw [map_nsmul, nsmul_eq_mul] at hd
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨_, hd.symm⟩
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

/-- **Kummer-faithfulness of the Jacobian from [AbsTopIII] Def. 1.5** (MR5 "J1").

The hypothesis `hJ` is `⋂_{N ≥ 1} N · J(k) = 0` for the group `J(k) = Pic⁰_{X/k,σ}(k)` of
`k`-points of the Jacobian: this is [AbsTopIII] Def. 1.5 (Kummer-faithfulness of `k`) for the
semi-abelian variety `A = J` over `k_H = k`. It enters as an explicit hypothesis because the
Jacobian is not yet available as a `k`-scheme (recorded debt). -/
theorem isKummerFaithfulJac_curveGaloisData
    (hJ : ∀ z ∈ jacPoints X σ hσ k,
      (∀ N : ℕ, 0 < N → ∃ y ∈ jacPoints X σ hσ k, N • y = z) → z = 0) :
    IsKummerFaithfulJac (curveGaloisData k hτ) := by
  intro x hx
  have hdeg0 : Pic.deg _ _ x = 0 := deg_eq_zero_of_forall_nsmul k hτ fun N hN ↦
    (hx N hN).imp fun _ h ↦ h.2
  have hxinv : x ∈ picInv (curveGaloisData k hτ) := by
    obtain ⟨y, hy, hyx⟩ := hx 1 one_pos
    rw [one_smul] at hyx
    exact hyx ▸ hy
  obtain ⟨z, hz, hzx⟩ := exists_jacPoints_picRes_eq_picPsi k hτ σ hσ hxinv hdeg0
  have hz0 : z = 0 := hJ z hz fun N hN ↦ by
    obtain ⟨y, hy, hyx⟩ := hx N hN
    have hy0 : Pic.deg _ _ y = 0 := by
      have h := congrArg (Pic.deg _ _) hyx
      rw [map_nsmul, hdeg0, nsmul_eq_mul, mul_eq_zero] at h
      exact h.resolve_left (by exact_mod_cast hN.ne')
    obtain ⟨w, hw, hwy⟩ := exists_jacPoints_picRes_eq_picPsi k hτ σ hσ hy hy0
    refine ⟨w, hw, picRes_injective X σ hσ k (kbar k (FFClosure X)) ?_⟩
    rw [map_nsmul, hwy, hzx, ← map_nsmul, hyx]
  apply picPsi_injective k hτ σ hσ
  rw [map_zero, ← hzx, hz0, map_zero]

end Faithful

end CurvesJacobian.Kummer
