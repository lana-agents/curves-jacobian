/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.KummerPicTop

/-!
# Semilinear automorphisms and the Kummer characters of `π₁ᵉᵗ(U)`

Setting of `CurvesJacobian/CuspChar/KummerPicTop.lean`. Let `φ` be a ring automorphism of `Ω`
mapping `F` and `k` onto themselves (e.g. an element of `Gal(Ω / K(X̄))` for a curve `X̄` over a
number field, acting on the geometric model), acting on `μ_n(Ω)` by `ζ ↦ ζ^χ`, and `Ψ` an
automorphism of `π₁ᵉᵗ(U)` with `Ψ(q σ) = q(φ σ φ⁻¹)` (`CurvesJacobian.CuspChar.conjH`). Then:

* `CurvesJacobian.CuspChar.pull_kumMap`: the pull-back along `Ψ` of the Kummer character of `v`
  is `χ` times the Kummer character of `φ⁻¹ v`;
* `CurvesJacobian.CuspChar.resMap_pull`: if `φ` fixes every cusp, the residue map is
  `χ`-equivariant;
* `CurvesJacobian.CuspChar.pull_picChar`: on `Pic(F)[n]` the pull-back is `χ · φ⁻¹`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Pi1.Orbifold
  KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.CuspChar

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [IsAlgClosed k] [CharZero k]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] [IsCurveOver k X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  (hH : D.H ≤ D.HL) {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U : X.Opens} [Nonempty U] (n : ℕ) [NeZero n] (hU : (U : Set X)ᶜ.Finite)

attribute [local instance] isFunctionField_F

section Semilinear

variable (φ : Ω ≃+* Ω) (hφF : ∀ x : F D, φ (x : Ω) ∈ F D)
  (hφF' : ∀ x : F D, φ.symm (x : Ω) ∈ F D)

lemma fixes_F (σ : D.H) (x : F D) : (σ : Ω ≃ₐ[K₀ k t] Ω) (x : Ω) = x :=
  (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ σ.2

/-- `φ` restricted to `F`. -/
def phiF : F D ≃+* F D where
  toFun x := ⟨φ x, hφF x⟩
  invFun x := ⟨φ.symm x, hφF' x⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply (x : Ω))
  right_inv x := Subtype.ext (φ.apply_symm_apply (x : Ω))
  map_mul' x y := Subtype.ext (map_mul φ (x : Ω) (y : Ω))
  map_add' x y := Subtype.ext (map_add φ (x : Ω) (y : Ω))

include hφF' in
/-- **Conjugation by `φ`** on `H = Gal(Ω/F)`: `σ ↦ φ σ φ⁻¹`. -/
def conjH (σ : D.H) : D.H :=
  let σ' : Ω ≃ₐ[K₀ k t] Ω := AlgEquiv.ofRingEquiv
    (f := (φ.symm.trans ((σ : Ω ≃ₐ[K₀ k t] Ω) : Ω ≃+* Ω)).trans φ) fun x ↦ by
      change φ ((σ : Ω ≃ₐ[K₀ k t] Ω) (φ.symm (algebraMap (K₀ k t) Ω x))) = _
      have hx : algebraMap (K₀ k t) Ω x ∈ F D := (F D).algebraMap_mem x
      have := fixes_F D σ ⟨_, hφF' ⟨_, hx⟩⟩
      simp only at this
      rw [this, φ.apply_symm_apply]
  ⟨σ', by
    have h := InfiniteGalois.fixingSubgroup_fixedField (⟨D.H, D.isClosed_H⟩ : ClosedSubgroup _)
    change σ' ∈ (⟨D.H, D.isClosed_H⟩ : ClosedSubgroup _).toSubgroup
    rw [← h, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change φ ((σ : Ω ≃ₐ[K₀ k t] Ω) (φ.symm x)) = x
    have := fixes_F D σ ⟨_, hφF' ⟨x, hx⟩⟩
    simp only at this
    rw [this, φ.apply_symm_apply]⟩

lemma conjH_apply (σ : D.H) (x : Ω) :
    (conjH D φ hφF' σ : Ω ≃ₐ[K₀ k t] Ω) x = φ ((σ : Ω ≃ₐ[K₀ k t] Ω) (φ.symm x)) :=
  rfl

/-- `φ⁻¹` on units of `F`. -/
def phiInvU : (F D)ˣ →* (F D)ˣ := Units.map (phiF D φ hφF hφF').symm.toMonoidHom

/-- The Kummer character of `v` at `σ` is the Kummer class evaluated at `σ` acting on `Ω/F`. -/
lemma kc_eq_evalTriv (v : (F D)ˣ) (σ : D.H) :
    kc D n v σ = ContH1.evalTriv (toGalF D σ) (galF_smul_mu D n _) (kummer n (F D) Ω v) := by
  change charOfH D n (kummer n (F D) Ω v) σ = _
  generalize kummer n (F D) Ω v = χ
  induction χ using ContH1.induction_on with
  | h c => rw [charOfH_mk, ContH1.evalTriv_mk]

lemma evalTriv_congr' {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M]
    [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M] {g g' : G} (e : g = g')
    (h : ∀ m : M, g • m = m) (h' : ∀ m : M, g' • m = m) (x : ContH1 G M) :
    ContH1.evalTriv g h x = ContH1.evalTriv g' h' x := by
  subst e
  rfl

/-- **Semilinear transport of Kummer characters**: `κ(v)(φ σ φ⁻¹) = φ(κ(φ⁻¹ v)(σ))`. -/
lemma kc_conjH (v : (F D)ˣ) (σ : D.H) :
    ((Mu.val (kc D n v (conjH D φ hφF' σ)) : Ωˣ) : Ω) =
      φ ((Mu.val (kc D n (phiInvU D φ hφF hφF' v) σ) : Ωˣ) : Ω) := by
  have hφ : ∀ x : F D, φ (algebraMap (F D) Ω x) ∈ (algebraMap (F D) Ω).range :=
    fun x ↦ ⟨⟨_, hφF x⟩, rfl⟩
  have hconj : conjAut φ hφ (toGalF D (conjH D φ hφF' σ)) = toGalF D σ := by
    ext x
    change φ.symm (φ ((σ : Ω ≃ₐ[K₀ k t] Ω) (φ.symm (φ x)))) = (σ : Ω ≃ₐ[K₀ k t] Ω) x
    rw [φ.symm_apply_apply, φ.symm_apply_apply]
  rw [kc_eq_evalTriv, kc_eq_evalTriv]
  have hw : algebraMap (F D) Ω ((v : (F D)ˣ) : F D) =
      φ (algebraMap (F D) Ω ((phiInvU D φ hφF hφF' v : (F D)ˣ) : F D)) := by
    change ((v : F D) : Ω) = φ (φ.symm ((v : F D) : Ω))
    rw [φ.apply_symm_apply]
  rw [val_evalTriv_kummer_map φ hφ (phiInvU D φ hφF hφF' v) v hw _ (galF_smul_mu D n _)
    (by rw [hconj]; exact galF_smul_mu D n _)]
  exact congrArg (fun z : Mu n Ω ↦ φ ((Mu.val z : Ωˣ) : Ω)) (evalTriv_congr' hconj _ _ _)

variable (Ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) ≃ₜ*
    π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U))
  (hΨ : ∀ σ, Ψ (qU D X eL hH σ) = qU D X eL hH (conjH D φ hφF' σ))
  (χ : (ZMod n)ˣ)
  (hχ : ∀ ζ : Mu n Ω, φ ((Mu.val ζ : Ωˣ) : Ω) = ((Mu.val ζ : Ωˣ) : Ω) ^ (χ : ZMod n).val)

include hχ in
lemma logMu_of_val_eq {ζ η : Mu n Ω} (h : ((Mu.val ζ : Ωˣ) : Ω) = φ ((Mu.val η : Ωˣ) : Ω)) :
    Multiplicative.toAdd (logMu n Ω ζ) = (χ : ZMod n) * Multiplicative.toAdd (logMu n Ω η) := by
  have hζ : ζ = η ^ (χ : ZMod n).val := by
    apply Mu.ext
    apply Units.ext
    rw [h, hχ, map_pow, Units.val_pow_eq_pow_val]
  rw [hζ, map_pow, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]

include hΨ hk hτ hU in
/-- `φ⁻¹` preserves the units unramified over `U`. -/
lemma unramU_phiInv {v : (F D)ˣ} (hv : UnramU D X eL U n v) :
    UnramU D X eL U n (phiInvU D φ hφF hφF' v) := by
  intro σ hσ
  have hσk : σ ∈ (qU D X eL hH (U := U)).ker := by
    rw [ker_qU D X eL hk hH hτ hU]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure ⟨1, D.H.one_mem, σ, hσ, by simp⟩))
  have h1 : conjH D φ hφF' σ ∈ (qU D X eL hH (U := U)).ker := by
    rw [MonoidHom.mem_ker, ← hΨ, MonoidHom.mem_ker.1 hσk, map_one]
  rw [ker_qU D X eL hk hH hτ hU] at h1
  have h2 := kernel_SU_le_ker_kc D X eL U n hv h1
  rw [MonoidHom.mem_ker] at h2
  have h3 := kc_conjH D n φ hφF hφF' v σ
  rw [h2] at h3
  apply Mu.ext
  apply Units.ext
  apply φ.injective
  rw [← h3]
  simp

/-- `φ⁻¹` on `kumU`. -/
def phiInvKum (v : kumU D X eL U n) : kumU D X eL U n :=
  ⟨Additive.ofMul (phiInvU D φ hφF hφF' (Additive.toMul v.1)),
    (mem_kumU D X eL U n).2 (unramU_phiInv D X eL hk hH hτ n hU φ hφF hφF' Ψ hΨ
      ((mem_kumU D X eL U n).1 v.2))⟩

lemma mapOpenSub_top' :
    mapOpenSub Ψ (⊤ : OpenSubgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) = ⊤ := by
  ext y
  obtain ⟨x, rfl⟩ := Ψ.surjective y
  exact iff_of_true (mem_mapOpenSub.2 (OpenSubgroup.mem_top x)) (OpenSubgroup.mem_top _)

/-- The pull-back along `Ψ` on `Hom_cont(π₁ᵉᵗ(U), ℤ/n)`. -/
abbrev pullΨ := pullEquivOf (p := n) Ψ ⊤ ⊤ (mapOpenSub_top' D X eL Ψ)

include hχ in
/-- **The pull-back of a Kummer character** along `Ψ` is `χ` times the Kummer character of
`φ⁻¹ v`. -/
theorem pull_kumMap (v : kumU D X eL U n) :
    pullΨ D X eL n Ψ (kumMap D X eL hk hH hτ n hU v) =
      (χ : ZMod n) • kumMap D X eL hk hH hτ n hU
        (phiInvKum D X eL hk hH hτ n hU φ hφF hφF' Ψ hΨ v) := by
  refine charSpace_ext_qU D X eL hk hH hτ n hU fun σ ↦ ?_
  simp only [ξv_pullEquivOf]
  simp only [hΨ]
  simp only [ξv_kumMap]
  rw [Submodule.coe_smul, ξv_smul', ξv_kumMap]
  exact logMu_of_val_eq n φ χ hχ (kc_conjH D n φ hφF hφF' _ σ)

section Const

variable (hφk : ∀ c : k, φ (algebraMap k Ω c) ∈ Set.range (algebraMap k Ω) ∧
    φ.symm (algebraMap k Ω c) ∈ Set.range (algebraMap k Ω))

include hφk in
lemma phiF_mem_constAut : (phiF D φ hφF hφF' : F D ≃+* F D) ∈ constAut k (F D) := by
  intro c
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := hφk c
  refine ⟨⟨c₁, Subtype.ext ?_⟩, ⟨c₂, Subtype.ext ?_⟩⟩
  · change algebraMap k Ω c₁ = φ (algebraMap (F D) Ω (algebraMap k (F D) c))
    rw [← IsScalarTower.algebraMap_apply, h₁]
  · change algebraMap k Ω c₂ = φ.symm (algebraMap (F D) Ω (algebraMap k (F D) c))
    rw [← IsScalarTower.algebraMap_apply, h₂]

/-- `φ` as an element of `constAut k F`. -/
def phiC : constAut k (F D) := ⟨phiF D φ hφF hφF', phiF_mem_constAut D φ hφF hφF' hφk⟩

/-- `φ⁻¹` as an element of `constAut k F`. -/
def phiCi : constAut k (F D) := (phiC D φ hφF hφF' hφk)⁻¹

lemma coe_phiC_inv (x : F D) :
    ((phiCi D φ hφF hφF' hφk : constAut k (F D)) : F D ≃+* F D) x =
      (phiF D φ hφF hφF').symm x :=
  rfl

variable (hcusp : ∀ c : CuspPl D X eL hH U, ∀ x : F D, phiF D φ hφF hφF' x ∈ c.1.1 ↔ x ∈ c.1.1)

include hcusp hφk in
lemma ord_phiInv (c : CuspPl D X eL hH U) (x : F D) :
    c.1.ord ((phiF D φ hφF hφF').symm x) = c.1.ord x := by
  have hP : CurvesJacobian.Kummer.placeMap (phiCi D φ hφF hφF' hφk) c.1 = c.1 := by
    apply Place.ext
    ext y
    rw [CurvesJacobian.Kummer.mem_placeMap]
    change phiF D φ hφF hφF' y ∈ c.1.1 ↔ _
    exact hcusp c y
  have := CurvesJacobian.Kummer.ord_placeMap_apply (phiCi D φ hφF hφF' hφk) c.1 x
  rwa [hP, coe_phiC_inv] at this

include hk hτ hU hΨ hχ hcusp hφk in
/-- **The residue map is `χ`-equivariant** when `φ` fixes the cusps. -/
theorem resMap_pull
    (a : charSpace n (⊤ : OpenSubgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U))) :
    resMap D X eL hH n (pullΨ D X eL n Ψ a) = (χ : ZMod n) • resMap D X eL hH n a := by
  revert a
  refine (kumMap_surjective D X eL hk hH hτ n hU).forall.2 fun v ↦ ?_
  simp only [pull_kumMap D X eL hk hH hτ n hU φ hφF hφF' Ψ hΨ χ hχ, map_smul]
  congr 1
  funext c
  simp only [resMap_kumMap]
  change ((c.1.ord ((phiF D φ hφF hφF').symm _) : ℤ) : ZMod n) = _
  rw [ord_phiInv D X eL hH φ hφF hφF' hφk hcusp]

include hΨ hχ in
/-- **On `Pic(F)[n]` the pull-back is `χ · φ⁻¹`.** -/
theorem pull_picChar (x : picTorsion k (F D) n) :
    pullΨ D X eL n Ψ (picChar D X eL hk hH hτ n hU x) =
      (χ : ZMod n) • picChar D X eL hk hH hτ n hU
        ⟨picMap (phiCi D φ hφF hφF' hφk) x, picMap_mem_picTorsion' _ x.2⟩ := by
  revert x
  refine (kummerToPic_surjective (Nat.pos_of_ne_zero (NeZero.ne n))).forall.2 fun f ↦ ?_
  have hE : (⟨picMap (phiCi D φ hφF hφF' hφk) (kummerToPic _ f),
      picMap_mem_picTorsion' _ (kummerToPic _ f).2⟩ : picTorsion k (F D) n) =
      kummerToPic (Nat.pos_of_ne_zero (NeZero.ne n))
        (kummerClassMap (phiCi D φ hφF hφF' hφk) f) :=
    Subtype.ext (kummerToPic_kummerClassMap _ _ f).symm
  simp only [hE]
  simp only [picChar_kummerToPic]
  simp only [jHom_apply]
  simp only [pull_kumMap D X eL hk hH hτ n hU φ hφF hφF' Ψ hΨ χ hχ]
  rfl

end Const

end Semilinear

end CurvesJacobian.CuspChar
