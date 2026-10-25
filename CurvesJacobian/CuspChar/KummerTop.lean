/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.Delta
import CurvesJacobian.Galois.AbelianPi1
import CurvesJacobian.Kummer.JacobianTorsion

/-!
# Kummer characters of `π₁ᵉᵗ(U)` for an open `U` of a curve

Galois model of `Galois/EtalePi1Open.lean`: `k` algebraically closed of characteristic `0`,
`D : GaloisData k t` with `H = H_L` (`hH`), `X` a curve over `k` with `eL : K(X) ≃ L`, and a
nonempty open `U ⊆ X` with finite complement; `q : H ↠ π₁ᵉᵗ(U)` is the Galois action at the
geometric generic point (`CurvesJacobian.genericL_spec`: kernel `⟨⟨S_U⟩⟩`).

For `v ∈ F^×` (`F = F D ≅ K(X)`) the Kummer character `σ ↦ σ(v^{1/n})/v^{1/n}` of `H`
(`CurvesJacobian.CuspChar.kc`) descends to `π₁ᵉᵗ(U)` if it kills the inertia at the places
centred on `U` (`CurvesJacobian.CuspChar.UnramU`), equivalently if `n ∣ ord_P v` at every place
`P` of `F` centred on `U` (`CurvesJacobian.CuspChar.unramU_iff`, the open-curve form of
`CurvesJacobian.isUnramifiedKummer_iff`). With a primitive `n`-th root of unity fixed
(`CurvesJacobian.CuspChar.muEquiv`), this gives the **Kummer map**

  `CurvesJacobian.CuspChar.kumMap : {v unramified over U} →+ Hom_cont(π₁ᵉᵗ(U), ℤ/n)`

(values in `CurvesJacobian.CuspChar.charSpace n ⊤`), surjective (`kumMap_surjective`, Kummer
theory and Hilbert 90) with kernel the `n`-th powers (`kumMap_eq_zero_iff`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Pi1.Orbifold
  KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.CuspChar

section Mu

variable (n : ℕ) [NeZero n] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

lemma exists_primitiveRoot_mu : ∃ ζ : Ωˣ, IsPrimitiveRoot ζ n := by
  haveI : NeZero (n : Ω) := NeZero.charZero
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  exact ⟨hμ.toRootsOfUnity, IsPrimitiveRoot.coe_units_iff.1 hμ⟩

/-- A chosen primitive `n`-th root of unity. -/
def zetaU : Ωˣ := (exists_primitiveRoot_mu n Ω).choose

lemma isPrimitiveRoot_zetaU : IsPrimitiveRoot (zetaU n Ω) n :=
  (exists_primitiveRoot_mu n Ω).choose_spec

/-- **`ℤ/n ≅ μ_n(Ω)`**, `a ↦ ζ^a` for the chosen primitive root `ζ`. -/
def muEquiv : ZMod n ≃+ Additive (Mu n Ω) :=
  (isPrimitiveRoot_zetaU n Ω).zmodEquivZPowers.trans
    (MulEquiv.subgroupCongr (isPrimitiveRoot_zetaU n Ω).zpowers_eq).toAdditive

lemma val_muEquiv_intCast (i : ℤ) :
    ((Mu.val (Additive.toMul (muEquiv n Ω (i : ZMod n))) : Ωˣ)) = zetaU n Ω ^ i := by
  have h := (isPrimitiveRoot_zetaU n Ω).zmodEquivZPowers_apply_coe_int i
  simp only [muEquiv, AddEquiv.trans_apply, h]
  rfl

/-- `μ_n(Ω) ≃ ℤ/n` (multiplicatively), inverse to `CurvesJacobian.CuspChar.muEquiv`. -/
def logMu : Mu n Ω ≃* Multiplicative (ZMod n) where
  toFun ζ := Multiplicative.ofAdd ((muEquiv n Ω).symm (Additive.ofMul ζ))
  invFun a := Additive.toMul (muEquiv n Ω (Multiplicative.toAdd a))
  left_inv ζ := by simp
  right_inv a := by simp
  map_mul' ζ η := by simp [← ofAdd_add, ← map_add]

end Mu

section Generic

lemma isOpen_map_of_surjective {G G' : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [T2Space G'] (f : G →* G') (hf : Continuous f)
    (hs : Function.Surjective f) (A : Subgroup G) (hA : IsOpen (A : Set G)) :
    IsOpen ((A.map f : Subgroup G') : Set G') := by
  have hAc : IsCompact (A : Set G) := (Subgroup.isClosed_of_isOpen A hA).isCompact
  have hcl : IsClosed ((A.map f : Subgroup G') : Set G') := by
    rw [Subgroup.coe_map]
    exact (hAc.image hf).isClosed
  haveI : Finite (G ⧸ A) := Subgroup.quotient_finite_of_isOpen A hA
  have hfi : (A.map f).FiniteIndex := by
    have hA0 : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact ⟨fun h ↦ hA0 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd A hs))⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {p : ℕ}

lemma ξv_charSpaceTopEquiv_symm (φ : {φ : G →* Multiplicative (ZMod p) // IsOpen (φ.ker : Set G)})
    (x : G) :
    ξv ((⊤ : OpenSubgroup G) : Subgroup G) ((charSpaceTopEquiv p).symm φ).1 x =
      Multiplicative.toAdd (φ.1 x) := by
  rw [ξv_of_mem (OpenSubgroup.mem_top x)]
  rfl

lemma ξv_add' (H : Subgroup G) (a b : Additive H →+ ZMod p) (x : G) :
    ξv H (a + b) x = ξv H a x + ξv H b x := by
  by_cases hx : x ∈ H <;> simp [ξv, hx]

lemma ξv_zero' (H : Subgroup G) (x : G) : ξv H (0 : Additive H →+ ZMod p) x = 0 := by
  by_cases hx : x ∈ H <;> simp [ξv, hx]

lemma ξv_smul' (H : Subgroup G) (a : ZMod p) (b : Additive H →+ ZMod p) (x : G) :
    ξv H (a • b) x = a * ξv H b x := by
  by_cases hx : x ∈ H <;> simp [ξv, hx]

end Generic

section Model

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [IsAlgClosed k] [CharZero k]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] [IsCurveOver k X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  (hH : D.H ≤ D.HL) {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  (U : X.Opens) [Nonempty U] (n : ℕ) [NeZero n]

attribute [local instance] isFunctionField_F

/-- The Kummer character `H → μ_n` of `v ∈ F^×`: `σ ↦ σ(α)/α` for `αⁿ = v`. -/
abbrev kc (v : (F D)ˣ) : D.H →* Mu n Ω := charOfH D n (kummer n (F D) Ω v)

lemma kc_mul (v w : (F D)ˣ) (σ : D.H) : kc D n (v * w) σ = kc D n v σ * kc D n w σ := by
  simp only [kc, charOfH, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]

lemma kc_one (σ : D.H) : kc D n 1 σ = 1 := by
  simp only [kc, charOfH, MonoidHom.coe_mk, OneHom.coe_mk, map_one]

lemma kc_inv (v : (F D)ˣ) (σ : D.H) : kc D n v⁻¹ σ = (kc D n v σ)⁻¹ := by
  simp only [kc, charOfH, MonoidHom.coe_mk, OneHom.coe_mk, map_inv]

/-- `v ∈ F^×` is **unramified over `U`**: its Kummer character kills the inertia elements of the
places centred on `U`. -/
def UnramU (v : (F D)ˣ) : Prop :=
  ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ SU D X eL U → kc D n v σ = 1

/-- The group of units of `F` unramified over `U`. -/
def kumUMul : Subgroup (F D)ˣ where
  carrier := {v | UnramU D X eL U n v}
  one_mem' σ _ := kc_one D n σ
  mul_mem' {v w} hv hw σ hσ := by
    rw [kc_mul, hv σ hσ, hw σ hσ, one_mul]
  inv_mem' {v} hv σ hσ := by
    rw [kc_inv, hv σ hσ, inv_one]

/-- The group of units of `F` unramified over `U` (written additively). -/
def kumU : AddSubgroup (Additive (F D)ˣ) where
  carrier := {v | UnramU D X eL U n (Additive.toMul v)}
  zero_mem' := (kumUMul D X eL U n).one_mem
  add_mem' hv hw := (kumUMul D X eL U n).mul_mem hv hw
  neg_mem' hv := (kumUMul D X eL U n).inv_mem hv

lemma mem_kumU {v : Additive (F D)ˣ} :
    v ∈ kumU D X eL U n ↔ UnramU D X eL U n (Additive.toMul v) :=
  Iff.rfl

set_option maxHeartbeats 400000 in
-- closure computations in the Krull topology of `Gal(Ω/k(t))` are slow to elaborate
/-- An unramified character kills the closed normal subgroup generated by `S_U`. -/
lemma kernel_SU_le_ker_kc {v : (F D)ˣ} (hv : UnramU D X eL U n v) :
    GaloisPi1.kernel D.H (SU D X eL U) ≤ (kc D n v).ker := by
  intro σ hσ
  let K : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := (kc D n v).ker.map D.H.subtype
  have hKclosed : IsClosed (K : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
    have h1 : IsClosed ((kc D n v).ker : Set D.H) :=
      (isClosed_discrete ({1} : Set (Mu n Ω))).preimage (continuous_charOfH D n _)
    have h2 := (D.isClosed_H.isClosedEmbedding_subtypeVal).isClosed_iff_image_isClosed.1 h1
    have hK : (K : Set (Ω ≃ₐ[K₀ k t] Ω)) = Subtype.val '' ((kc D n v).ker : Set D.H) := by
      rw [Subgroup.coe_map]; rfl
    rw [hK]
    exact h2
  have hconj : GaloisPi1.conjSet D.H (SU D X eL U) ⊆ K := by
    rintro _ ⟨h, hh, s, hs, rfl⟩
    have hsH : s ∈ D.H := SU_subset_H D X eL U hs
    refine ⟨⟨h, hh⟩ * ⟨s, hsH⟩ * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, mul_comm, ← mul_assoc, map_inv,
      inv_mul_cancel, one_mul]
    exact hv ⟨s, hsH⟩ hs
  have hle : GaloisPi1.ambientKernel D.H (SU D X eL U) ≤ K :=
    Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le K).2 hconj) hKclosed
  have hσ' : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.ambientKernel D.H (SU D X eL U) :=
    Subgroup.mem_subgroupOf.1 hσ
  obtain ⟨ρ, hρ, hρσ⟩ := Subgroup.mem_map.1 (hle hσ')
  have : ρ = σ := Subtype.ext hρσ
  rw [← this]
  exact hρ

variable {U} (hU : (U : Set X)ᶜ.Finite)

/-- The Galois action `q : H → π₁ᵉᵗ(U)` at the geometric generic point. -/
abbrev qU : D.H →* π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) :=
  D.chartHom hH (genericL D X eL U)

include hk hτ hU in
lemma qU_surjective : Function.Surjective (qU D X eL hH (U := U)) :=
  (genericL_spec D X eL hk hH hτ U hU).2

include hk hτ hU in
lemma ker_qU : (qU D X eL hH (U := U)).ker = GaloisPi1.kernel D.H (SU D X eL U) :=
  (genericL_spec D X eL hk hH hτ U hU).1

include hk hτ hU in
/-- Characters of `π₁ᵉᵗ(U)` are determined by their values on the image of `H`. -/
lemma charSpace_ext_qU
    {e₁ e₂ : charSpace n (⊤ : OpenSubgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U))}
    (h : ∀ σ : D.H, ξv _ e₁.1 (qU D X eL hH σ) = ξv _ e₂.1 (qU D X eL hH σ)) : e₁ = e₂ := by
  apply charSpace_ext
  intro x
  obtain ⟨σ, rfl⟩ := qU_surjective D X eL hk hH hτ hU x
  exact h σ

include hk hτ hU in
/-- A unit whose Kummer character kills the kernel of `H → π₁ᵉᵗ(U)` is unramified over `U`. -/
lemma unramU_of_ker {v : (F D)ˣ} (h : ∀ σ, qU D X eL hH (U := U) σ = 1 → kc D n v σ = 1) :
    UnramU D X eL U n v := by
  intro σ hσ
  refine h σ ?_
  have hσk : σ ∈ (qU D X eL hH (U := U)).ker := by
    rw [ker_qU D X eL hk hH hτ hU]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure ⟨1, D.H.one_mem, σ, hσ, by simp⟩))
  exact hσk

/-- The Kummer character of `v` unramified over `U`, as a character of `π₁ᵉᵗ(U)`. -/
def kcU (v : (F D)ˣ) (hv : UnramU D X eL U n v) :
    π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Mu n Ω :=
  (QuotientGroup.lift (qU D X eL hH (U := U)).ker (kc D n v) (by
      rw [ker_qU D X eL hk hH hτ hU]
      exact kernel_SU_le_ker_kc D X eL U n hv)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (qU_surjective D X eL hk hH hτ hU)).symm.toMonoidHom

lemma kcU_qU (v : (F D)ˣ) (hv : UnramU D X eL U n v) (σ : D.H) :
    kcU D X eL hk hH hτ n hU v hv (qU D X eL hH σ) = kc D n v σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (qU_surjective D X eL hk hH hτ hU)).symm (qU D X eL hH σ) = (σ : D.H ⧸ _) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  simp only [kcU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]

/-- The Kummer character of `v`, with values in `ℤ/n`. -/
def kumChar (v : (F D)ˣ) (hv : UnramU D X eL U n v) :
    π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →* Multiplicative (ZMod n) :=
  (logMu n Ω).toMonoidHom.comp (kcU D X eL hk hH hτ n hU v hv)

lemma kumChar_qU (v : (F D)ˣ) (hv : UnramU D X eL U n v) (σ : D.H) :
    kumChar D X eL hk hH hτ n hU v hv (qU D X eL hH σ) = logMu n Ω (kc D n v σ) := by
  simp only [kumChar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, kcU_qU]

lemma isOpen_ker_kumChar (v : (F D)ˣ) (hv : UnramU D X eL U n v) :
    IsOpen ((kumChar D X eL hk hH hτ n hU v hv).ker :
      Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) := by
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  have hker : (kumChar D X eL hk hH hτ n hU v hv).ker = (kc D n v).ker.map (qU D X eL hH) := by
    ext x
    obtain ⟨σ, rfl⟩ := qU_surjective D X eL hk hH hτ hU x
    rw [MonoidHom.mem_ker, kumChar_qU]
    constructor
    · intro h
      have h' : kc D n v σ = 1 := (logMu n Ω).injective (h.trans (map_one _).symm)
      exact Subgroup.mem_map.2 ⟨σ, h', rfl⟩
    · rintro ⟨ρ, hρ, e⟩
      have h1 : kc D n v ρ = 1 := hρ
      have h2 : kumChar D X eL hk hH hτ n hU v hv (qU D X eL hH ρ) = 1 := by
        rw [kumChar_qU, h1, map_one]
      rwa [e, kumChar_qU] at h2
  rw [hker]
  have h1 : IsOpen (((kc D n v).ker : Subgroup D.H) : Set D.H) :=
    (isOpen_discrete ({1} : Set (Mu n Ω))).preimage (continuous_charOfH D n _)
  exact isOpen_map_of_surjective _ (D.continuous_chartHom hH _)
    (qU_surjective D X eL hk hH hτ hU) _ h1

/-- The character `kumChar v` as an element of `Hom_cont(π₁ᵉᵗ(U), ℤ/n)`. -/
def kumMapFun (v : (F D)ˣ) (hv : UnramU D X eL U n v) :
    charSpace n (⊤ : OpenSubgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) :=
  (charSpaceTopEquiv (D := π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) n).symm
    ⟨kumChar D X eL hk hH hτ n hU v hv, isOpen_ker_kumChar D X eL hk hH hτ n hU v hv⟩

lemma ξv_kumMapFun (v : (F D)ˣ) (hv : UnramU D X eL U n v) (σ : D.H) :
    ξv _ (kumMapFun D X eL hk hH hτ n hU v hv).1 (qU D X eL hH σ) =
      Multiplicative.toAdd (logMu n Ω (kc D n v σ)) := by
  rw [kumMapFun, ξv_charSpaceTopEquiv_symm, kumChar_qU]

/-- **The Kummer map** `{v ∈ F^× unramified over U} → Hom_cont(π₁ᵉᵗ(U), ℤ/n)`. -/
def kumMap : kumU D X eL U n →+
    charSpace n (⊤ : OpenSubgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) :=
  AddMonoidHom.mk' (fun v ↦ kumMapFun D X eL hk hH hτ n hU (Additive.toMul v.1)
      ((mem_kumU D X eL U n).1 v.2)) fun v w ↦ by
    refine charSpace_ext_qU D X eL hk hH hτ n hU fun σ ↦ ?_
    simp only [ξv_kumMapFun, Submodule.coe_add, ξv_add', AddSubgroup.coe_add, toMul_add, kc_mul,
      map_mul, toAdd_mul]

lemma ξv_kumMap (v : kumU D X eL U n) (σ : D.H) :
    ξv _ (kumMap D X eL hk hH hτ n hU v).1 (qU D X eL hH σ) =
      Multiplicative.toAdd (logMu n Ω (kc D n (Additive.toMul v.1) σ)) :=
  ξv_kumMapFun D X eL hk hH hτ n hU _ ((mem_kumU D X eL U n).1 v.2) σ

/-- The Kummer character determines the Kummer class. -/
lemma eq_one_of_charOfH_eq_one (χ : ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω))
    (h : ∀ σ, charOfH D n χ σ = 1) : χ = 1 := by
  induction χ using ContH1.induction_on with
  | h c =>
    have hc : ∀ τ, (c : (Ω ≃ₐ[F D] Ω) → Mu n Ω) τ = 1 := fun τ ↦ by
      have := h (ofGalF D τ)
      rwa [charOfH_mk, toGalF_ofGalF] at this
    have : c = 1 := Subtype.ext (funext hc)
    rw [this]
    rfl

/-- **Kummer theory and Hilbert 90**: every continuous character of `H` is a Kummer
character. -/
lemma exists_kc_eq (f : D.H →* Mu n Ω) (hf : Continuous f) :
    ∃ v : (F D)ˣ, ∀ σ, kc D n v σ = f σ := by
  obtain ⟨v, hv⟩ := kummer_surjective n (F D) Ω (classOfH D n ⟨f, hf⟩)
  exact ⟨v, fun σ ↦ by rw [kc, hv]; exact charOfH_classOfH D n ⟨f, hf⟩ σ⟩

/-- The Kummer character of `v` is trivial iff `v` is an `n`-th power. -/
lemma kc_eq_one_iff (v : (F D)ˣ) :
    (∀ σ, kc D n v σ = 1) ↔ v ∈ (powMonoidHom n : (F D)ˣ →* (F D)ˣ).range := by
  rw [← ker_kummer n (F D) Ω, MonoidHom.mem_ker]
  constructor
  · exact eq_one_of_charOfH_eq_one D n _
  · intro h σ
    simp only [kc, h, charOfH, MonoidHom.coe_mk, OneHom.coe_mk, map_one]

lemma continuous_of_isOpen_ker' {G Q : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] (f : G →* Q)
    (h : IsOpen (f.ker : Set G)) : Continuous f := by
  rw [continuous_discrete_rng]
  intro q
  by_cases hq : ∃ x, f x = q
  · obtain ⟨x, rfl⟩ := hq
    have e : f ⁻¹' {f x} = (fun y ↦ x⁻¹ * y) ⁻¹' (f.ker : Set G) := by
      ext y
      rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_preimage, SetLike.mem_coe,
        MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, eq_comm]
    rw [e]
    exact h.preimage (continuous_const_mul _)
  · have e : f ⁻¹' {q} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hy ↦ hq ⟨y, hy⟩
    rw [e]
    exact isOpen_empty

set_option maxHeartbeats 800000 in
-- unifying the instance paths on the subfields `F D`, `K₀ k t` of the Galois model is slow
/-- **The Kummer map is onto** (Kummer theory and Hilbert 90 for `Ω/F`). -/
theorem kumMap_surjective : Function.Surjective (kumMap D X eL hk hH hτ n hU) := by
  refine ((charSpaceTopEquiv (D := π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U))
    n).symm.surjective).forall.2 fun φ0 ↦ ?_
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  obtain ⟨f, hfdef⟩ : ∃ f : D.H →* Mu n Ω,
      ∀ σ, f σ = (logMu n Ω).symm (φ0.1 (qU D X eL hH (U := U) σ)) :=
    ⟨(logMu n Ω).symm.toMonoidHom.comp (φ0.1.comp (qU D X eL hH (U := U))), fun _ ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]⟩
  have hset : ((f.ker : Subgroup D.H) : Set D.H) =
      (qU D X eL hH (U := U)) ⁻¹' ((φ0.1.ker : Subgroup _) : Set _) := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, hfdef, Set.mem_preimage]
    exact (logMu n Ω).symm.map_eq_one_iff
  have hf : Continuous f := by
    refine continuous_of_isOpen_ker' f ?_
    rw [hset]
    exact φ0.2.preimage (D.continuous_chartHom hH (genericL D X eL U))
  obtain ⟨v, hkc⟩ := exists_kc_eq D n f hf
  have hunr : UnramU D X eL U n v := unramU_of_ker D X eL hk hH hτ n hU fun σ hσ ↦ by
    rw [hkc, hfdef, hσ, map_one, map_one]
  refine ⟨⟨Additive.ofMul v, (mem_kumU D X eL U n).2 hunr⟩, ?_⟩
  refine charSpace_ext_qU D X eL hk hH hτ n hU fun σ ↦ ?_
  simp only [ξv_kumMap, ξv_charSpaceTopEquiv_symm]
  change Multiplicative.toAdd (logMu n Ω (kc D n v σ)) = _
  simp only [hkc, hfdef, MulEquiv.apply_symm_apply]

/-- **The kernel of the Kummer map** is the group of `n`-th powers. -/
theorem kumMap_eq_zero_iff (v : kumU D X eL U n) :
    kumMap D X eL hk hH hτ n hU v = 0 ↔
      Additive.toMul v.1 ∈ (powMonoidHom n : (F D)ˣ →* (F D)ˣ).range := by
  simp only [← kc_eq_one_iff]
  constructor
  · intro h σ
    have h1 := ξv_kumMap D X eL hk hH hτ n hU v σ
    have h0 : ξv _ (kumMap D X eL hk hH hτ n hU v).1 (qU D X eL hH σ) = 0 := by
      have e := congrArg (fun c : charSpace n
        (⊤ : OpenSubgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) ↦
          ξv _ c.1 (qU D X eL hH σ)) h
      exact e.trans (ξv_zero' _ _)
    simp only [h0] at h1
    apply (logMu n Ω).injective
    rw [map_one]
    exact toAdd_eq_zero.1 h1.symm
  · intro h
    refine charSpace_ext_qU D X eL hk hH hτ n hU fun σ ↦ ?_
    simp only [ξv_kumMap]
    refine Eq.trans ?_ (ξv_zero' _ _).symm
    simp only [h σ, map_one, toAdd_one]

end Model

end CurvesJacobian.CuspChar
