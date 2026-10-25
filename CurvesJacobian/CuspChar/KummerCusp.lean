/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.KummerTop
import WeilCurves.Hurwitz.Belyi
import CurvesJacobian.Kummer.PicDivisible

/-!
# Unramified Kummer classes over an open `U` and their residues at the cusps

Setting of `CurvesJacobian/CuspChar/KummerTop.lean` (Galois model `D`, curve `X`, open `U`).

* `CurvesJacobian.CuspChar.unramU_iff`: `v ∈ F^×` is unramified over `U` iff `n ∣ ord_P v` for
  every place `P` of `F` centred on `U` (`CurvesJacobian.CuspChar.IsCentredP`); the local
  computation is `CurvesJacobian.CuspChar.kc_eq_zpow` (`κ(v)|_{I_W} = κ(π)|_{I_W}^{ord_P v}`).
* `CurvesJacobian.CuspChar.CuspPl`: the places of `F` not centred on `U` (the cusps), a finite
  type.
* `CurvesJacobian.CuspChar.resMap`: the residue map
  `Hom_cont(π₁ᵉᵗ(U), ℤ/n) → (ℤ/n)^{cusps}`, evaluation at tame generators of the cuspidal
  inertia; on Kummer characters it is `v ↦ (ord_c v mod n)_c` (`resMap_kumMap`).
* `CurvesJacobian.CuspChar.range_resMap`: its image is the sum-zero submodule (the degree of a
  principal divisor is `0`, and `Pic⁰(F)` is divisible).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Pi1.Orbifold
  KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

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
  (U : X.Opens) [Nonempty U] (n : ℕ) [NeZero n]

attribute [local instance] isFunctionField_F

section Local

include hH in
lemma mem_F_of_mem_L {x : Ω} (hx : x ∈ D.L) : x ∈ F D := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ (hH hσ)

/-- The element `eL(a)` of `F` for a section `a ∈ Γ(U, 𝒪_X)`. -/
def secF (a : Γ(X, U)) : F D :=
  ⟨((eL (X.germToFunctionField U a) : D.L) : Ω), mem_F_of_mem_L D hH (eL _).2⟩

/-- A place `P` of `F` is **centred on `U`** if `Γ(U, 𝒪_X) ⊆ P` (through `eL`). -/
def IsCentredP (P : Place k (F D)) : Prop := ∀ a : Γ(X, U), secF D X eL hH U a ∈ P.1

/-- The place of `F` below a valuation subring `W ⊇ k` of `Ω` which is not trivial on `F`. -/
def placeBelow (W : ValuationSubring Ω) (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hA : W.comap (algebraMap (F D) Ω) ≠ ⊤) : Place k (F D) :=
  ⟨W.comap (algebraMap (F D) Ω), hA, fun c ↦ by
    change algebraMap (F D) Ω (algebraMap k (F D) c) ∈ W
    rw [← IsScalarTower.algebraMap_apply k (F D) Ω]
    exact hkW c⟩

lemma mem_placeBelow {W : ValuationSubring Ω} {hkW : ∀ c : k, algebraMap k Ω c ∈ W}
    {hA : W.comap (algebraMap (F D) Ω) ≠ ⊤} {x : F D} :
    x ∈ (placeBelow D W hkW hA).1 ↔ ((x : F D) : Ω) ∈ W :=
  Iff.rfl

/-- For `W` lying over a place `P`, uniformisers of `P` have the largest `W`-value `< 1`. -/
lemma uniformizer_spec {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) {π : F D} (hπ1 : P.ord π = 1) :
    W.valuation ((π : F D) : Ω) < 1 ∧
      ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω) := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  have hπmem : π ∈ P.1 ∧ π⁻¹ ∉ P.1 := by
    refine ⟨P.mem_of_ord_nonneg (by rw [hπ1]; norm_num), fun h ↦ ?_⟩
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, hπ1] at this
    norm_num at this
  refine ⟨(valuation_lt_one_iff hW hπ0).2 hπmem, fun f hf hlt ↦ ?_⟩
  let x : F D := ⟨f, hf⟩
  rcases eq_or_ne x 0 with hx0 | hx0
  · have : f = 0 := congrArg Subtype.val hx0
    rw [this, map_zero]; exact zero_le
  obtain ⟨hxP, hxP'⟩ := (valuation_lt_one_iff hW hx0).1 hlt
  have hord : 1 ≤ P.ord x := by
    have h0 := P.ord_nonneg_of_mem hxP
    rcases (show P.ord x = 0 ∨ 1 ≤ P.ord x by omega) with h | h
    · exact absurd ((P.ord_eq_zero_iff hx0).1 h).2 hxP'
    · exact h
  have hdiv : x / π ∈ P.1 := P.mem_of_ord_nonneg (by rw [P.ord_div hx0 hπ0, hπ1]; omega)
  have hdivW := (W.valuation_le_one_iff _).2 ((hW _).2 hdiv)
  rw [IntermediateField.coe_div, map_div₀] at hdivW
  have hπΩ : W.valuation ((π : F D) : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact fun h ↦ hπ0 (Subtype.ext h)
  exact (div_le_one₀ (zero_lt_iff.2 hπΩ)).1 hdivW

/-- **Local Kummer computation**: on the inertia group of `W` over `P`,
`κ(v) = κ(π)^{ord_P v}` for a uniformiser `π` of `P`. -/
lemma kc_eq_zpow {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) {σ : D.H}
    (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (π v : (F D)ˣ)
    (hπ1 : P.ord (π : F D) = 1) :
    kc D n v σ = kc D n π σ ^ P.ord (v : F D) := by
  have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW _).2 (P.algebraMap_mem c)
  let m := P.ord (v : F D)
  have hunit : P.ord ((v * π ^ (-m) : (F D)ˣ) : F D) = 0 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, P.ord_mul v.ne_zero
      (zpow_ne_zero _ π.ne_zero), P.ord_zpow, hπ1]
    ring
  obtain ⟨hu1, hu2⟩ := (P.ord_eq_zero_iff (Units.ne_zero _)).1 hunit
  exact evalTriv_res_kummer_eq_zpow hkW hσ n v π m ((hW _).2 hu1)
    ((hW _).2 (by simpa using hu2))

/-- If `n ∣ ord_P v` then `κ(v)` kills the inertia of every `W` over `P`. -/
lemma kc_eq_one_of_dvd {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) {σ : D.H}
    (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (v : (F D)ˣ)
    (hv : (n : ℤ) ∣ P.ord (v : F D)) : kc D n v σ = 1 := by
  obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  rw [kc_eq_zpow D n hW hσ (Units.mk0 π hπ0) v hπ1]
  obtain ⟨m', hm'⟩ := hv
  rw [hm', zpow_mul]
  have hpow : ∀ ζ : Mu n Ω, ζ ^ (n : ℤ) = 1 := fun ζ ↦ by
    apply Mu.ext
    rw [map_zpow, zpow_natCast, Mu.val_pow_n, map_one]
  rw [hpow, one_zpow]

/-- A place `W ⊇ k` of `Ω` is centred on `U` iff the place of `F` below it is. -/
lemma isCentredOn_iff_isCentredP {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) :
    Cusp.IsCentredOn D X eL U W ↔ IsCentredP D X eL hH U P := by
  have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW _).2 (P.algebraMap_mem c)
  constructor
  · intro h a
    exact (hW _).1 (h.2 a)
  · intro h
    exact ⟨hkW, fun a ↦ (hW (secF D X eL hH U a)).2 (h a)⟩

/-- **Unramified over `U` ⟺ divisible orders at the places centred on `U`.** -/
theorem unramU_iff (v : (F D)ˣ) :
    UnramU D X eL U n v ↔ ∀ P : Place k (F D), IsCentredP D X eL hH U P →
      (n : ℤ) ∣ P.ord (v : F D) := by
  constructor
  · intro hun P hP
    obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver D P
    refine dvd_ord_of_evalTriv_eq_one D n v P hW fun hkW σ hσ ↦ hun σ ?_
    exact (Cusp.mem_SU_iff D X eL U _).2
      ⟨σ.2, W, (isCentredOn_iff_isCentredP D X eL hH U hW).2 hP, hσ⟩
  · intro hdiv σ hσ
    obtain ⟨-, W, hWU, hσW⟩ := (Cusp.mem_SU_iff D X eL U _).1 hσ
    by_cases hA : W.comap (algebraMap (F D) Ω) = ⊤
    · have hv : ((v : F D) : Ω) ∈ W := by
        have : (v : F D) ∈ W.comap (algebraMap (F D) Ω) := hA ▸ ValuationSubring.mem_top _
        exact this
      have hv' : (((v⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W := by
        have : ((v⁻¹ : (F D)ˣ) : F D) ∈ W.comap (algebraMap (F D) Ω) :=
          hA ▸ ValuationSubring.mem_top _
        exact this
      exact evalTriv_res_kummer_of_unit hWU.1 hσW n v hv hv'
    · set P := placeBelow D W hWU.1 hA
      have hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1 := fun _ ↦ Iff.rfl
      exact kc_eq_one_of_dvd D n hW hσW v
        (hdiv P ((isCentredOn_iff_isCentredP D X eL hH U hW).1 hWU))

end Local

section Cusps

/-- **The cusps**: the places of `F` not centred on `U`. -/
def CuspPl : Type u := {P : Place k (F D) // ¬ IsCentredP D X eL hH U P}

include hk in
/-- Two places of `F` with the same restriction to `K(X)` (through `eL`) agree. -/
lemma place_eq_of_comapK {P Q : Place k (F D)} {W W' : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1)
    (hW' : ∀ x : F D, ((x : F D) : Ω) ∈ W' ↔ x ∈ Q.1)
    (h : comapK D X eL hk W = comapK D X eL hk W') : P = Q := by
  apply Place.ext
  ext x
  have hxL : ((x : F D) : Ω) ∈ D.L := by
    rw [GaloisData.L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ (D.le hσ)
  let z := eL.symm ⟨_, hxL⟩
  have hz : ((x : F D) : Ω) = embK D X eL hk z := by
    rw [embK_apply, RingEquiv.apply_symm_apply]
  rw [← hW, ← hW', hz]
  change z ∈ comapK D X eL hk W ↔ z ∈ comapK D X eL hk W'
  rw [h]

include hk in
/-- **There are finitely many cusps.** -/
theorem finite_cuspPl (hU : (U : Set X)ᶜ.Finite) : Finite (CuspPl D X eL hH U) := by
  haveI := hU.to_subtype
  have key : ∀ P : CuspPl D X eL hH U, ∃ W : ValuationSubring Ω,
      (∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1.1) ∧
        ∃ y : X, y ∉ U ∧ stalkVS k y = comapK D X eL hk W := by
    intro P
    obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver D P.1
    have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k (F D) Ω]
      exact (hW _).2 (P.1.algebraMap_mem c)
    have hnc : ¬ Cusp.IsCentredOn D X eL U W := fun h ↦
      P.2 ((isCentredOn_iff_isCentredP D X eL hH U hW).1 h)
    exact ⟨W, hW, exists_notMem_of_not_isCentredOn D X eL hk U hkW hnc⟩
  choose W hW y hyU hy using key
  refine Finite.of_injective (fun P ↦ (⟨y P, hyU P⟩ : ((U : Set X)ᶜ : Set X))) fun P Q hPQ ↦ ?_
  have h1 : y P = y Q := congrArg Subtype.val hPQ
  apply Subtype.ext
  exact place_eq_of_comapK D X eL hk (hW P) (hW Q) (by rw [← hy, ← hy, h1])

/-- A **tame generator** at a place `P`: a place `W` of `Ω` over `P`, a uniformiser `π` and an
inertia element `σ` with `κ(π)(σ) = ζ` (the chosen primitive root of unity). -/
lemma exists_tame (P : Place k (F D)) :
    ∃ W : ValuationSubring Ω, (∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) ∧
      ∃ π : (F D)ˣ, P.ord (π : F D) = 1 ∧ ∃ σ : D.H,
        (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W ∧
          kc D n π σ = Additive.toMul (muEquiv n Ω 1) := by
  obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver D P
  have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW _).2 (P.algebraMap_mem c)
  obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  obtain ⟨h1, h2⟩ := uniformizer_spec D hW hπ1
  obtain ⟨σ, hσ, hσζ⟩ := evalTriv_kummer_surjective (D := D) hkW (Units.mk0 π hπ0) h1 h2 n
    (Additive.toMul (muEquiv n Ω 1))
  exact ⟨W, hW, Units.mk0 π hπ0, hπ1, σ, hσ, hσζ⟩

/-- The chosen tame generator at a cusp. -/
def tameGen (c : CuspPl D X eL hH U) : D.H :=
  (exists_tame D n c.1).choose_spec.2.choose_spec.2.choose

lemma tameGen_spec (c : CuspPl D X eL hH U) (v : (F D)ˣ) :
    kc D n v (tameGen D X eL hH U n c) = Additive.toMul (muEquiv n Ω (c.1.ord (v : F D))) := by
  have hspec := (exists_tame D n c.1).choose_spec.2.choose_spec.2.choose_spec
  rw [tameGen, kc_eq_zpow D n (exists_tame D n c.1).choose_spec.1 hspec.1
    (exists_tame D n c.1).choose_spec.2.choose v
    (exists_tame D n c.1).choose_spec.2.choose_spec.1, hspec.2]
  rw [← toMul_zsmul, ← map_zsmul, zsmul_eq_mul, mul_one]

variable {U}
variable (hU : (U : Set X)ᶜ.Finite)

/-- **The residue map** `Hom_cont(π₁ᵉᵗ(U), ℤ/n) → (ℤ/n)^{cusps}`: evaluation at the tame
generators of the cuspidal inertia groups. -/
def resMap : charSpace n (⊤ : OpenSubgroup (PiU D X eL U)) →ₗ[ZMod n]
    (CuspPl D X eL hH U → ZMod n) where
  toFun e0 c := ξv _ e0.1 (qU D X eL hH (tameGen D X eL hH U n c))
  map_add' e0 η := by
    funext c
    simp only [Submodule.coe_add, ξv_add', Pi.add_apply]
  map_smul' a e0 := by
    funext c
    simp only [Submodule.coe_smul, ξv_smul', Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- **The residue map on Kummer characters** is `v ↦ (ord_c v mod n)_c`. -/
theorem resMap_kumMap (v : kumU D X eL U n) (c : CuspPl D X eL hH U) :
    resMap D X eL hH n (kumMap D X eL hk hH hτ n hU v) c =
      (c.1.ord ((Additive.toMul v.1 : (F D)ˣ) : F D) : ZMod n) := by
  change ξv _ (kumMap D X eL hk hH hτ n hU v).1 _ = _
  rw [ξv_kumMap, tameGen_spec]
  simp [logMu]

end Cusps

section SumZero

variable {U} (hU : (U : Set X)ᶜ.Finite) [Fintype (CuspPl D X eL hH U)]

/-- The **sum-zero** submodule of `(ℤ/n)^{cusps}`. -/
def sumZero : Submodule (ZMod n) (CuspPl D X eL hH U → ZMod n) where
  carrier := {a | ∑ c, a c = 0}
  add_mem' {a b} ha hb := by
    change ∑ c, (a c + b c) = 0
    rw [Finset.sum_add_distrib, ha, hb, add_zero]
  zero_mem' := by
    change ∑ _c, (0 : ZMod n) = 0
    simp
  smul_mem' r a ha := by
    change ∑ c, r * a c = 0
    rw [← Finset.mul_sum, ha, mul_zero]

/-- **The orders of an unramified `v` at the cusps sum to `0` modulo `n`** (`deg div v = 0`, all
places have degree `1`, and the orders at the places centred on `U` are divisible by `n`). -/
theorem sum_ord_cusps_eq_zero (v : (F D)ˣ)
    (hv : ∀ P : Place k (F D), IsCentredP D X eL hH U P → (n : ℤ) ∣ P.ord (v : F D)) :
    ∑ c : CuspPl D X eL hH U, (c.1.ord (v : F D) : ZMod n) = 0 := by
  classical
  let f : Place k (F D) → ZMod n := fun P ↦ (P.ord (v : F D) : ZMod n)
  have hdeg := Divisor.deg_div (k := k) ((v : (F D)ˣ) : F D)
  rw [Divisor.deg, Finsupp.sum] at hdeg
  have hS : ∑ P ∈ (Divisor.div k (v : F D)).support, f P = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod n) hdeg
    simp only [Int.cast_sum, Place.deg_eq_one, Nat.cast_one, mul_one, Int.cast_zero,
      Divisor.div_apply] at this
    exact this
  let S := (Divisor.div k (v : F D)).support
  let T : Finset (Place k (F D)) := Finset.univ.image (fun c : CuspPl D X eL hH U ↦ c.1)
  have h1 : ∑ P ∈ S, f P = ∑ P ∈ S ∪ T, f P := by
    refine Finset.sum_subset Finset.subset_union_left fun P _ hPS ↦ ?_
    rw [Finsupp.notMem_support_iff, Divisor.div_apply] at hPS
    simp [f, hPS]
  have h2 : ∑ P ∈ T, f P = ∑ P ∈ S ∪ T, f P := by
    refine Finset.sum_subset Finset.subset_union_right fun P _ hPT ↦ ?_
    have hP : IsCentredP D X eL hH U P := by
      by_contra hc
      exact hPT (Finset.mem_image.2 ⟨⟨P, hc⟩, Finset.mem_univ _, rfl⟩)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (hv P hP)
  have h3 : ∑ c : CuspPl D X eL hH U, (c.1.ord (v : F D) : ZMod n) = ∑ P ∈ T, f P :=
    (Finset.sum_image (f := f) (s := Finset.univ) (g := fun c : CuspPl D X eL hH U ↦ c.1)
      fun a _ b _ hab ↦ Subtype.ext hab).symm
  rw [h3, h2, ← h1, hS]

include hk hτ hU in
/-- The residues of a continuous character sum to zero. -/
theorem resMap_mem_sumZero
    (e0 : charSpace n (⊤ : OpenSubgroup (PiU D X eL U))) :
    resMap D X eL hH n e0 ∈ sumZero D X eL hH n := by
  obtain ⟨v, rfl⟩ := kumMap_surjective D X eL hk hH hτ n hU e0
  change ∑ c, resMap D X eL hH n (kumMap D X eL hk hH hτ n hU v) c = 0
  simp only [resMap_kumMap]
  exact sum_ord_cusps_eq_zero D X eL hH n _
    ((unramU_iff D X eL hH U n _).1 ((mem_kumU D X eL U n).1 v.2))

include hk in
/-- **Every sum-zero family of orders at the cusps occurs** (divisibility of `Pic⁰(F)`): there is
`f ≠ 0` with `n ∣ ord_P f` at the places centred on `U` and `ord_c f ≡ a_c` at the cusps. -/
theorem exists_ord_eq (a : CuspPl D X eL hH U → ZMod n) (ha : a ∈ sumZero D X eL hH n) :
    ∃ f : F D, f ≠ 0 ∧ (∀ P : Place k (F D), IsCentredP D X eL hH U P → (n : ℤ) ∣ P.ord f) ∧
      ∀ c : CuspPl D X eL hH U, ((c.1.ord f : ℤ) : ZMod n) = a c := by
  classical
  by_cases hne : IsEmpty (CuspPl D X eL hH U)
  · exact ⟨1, one_ne_zero, fun P _ ↦ by rw [P.ord_one]; exact dvd_zero _, fun c ↦ hne.elim c⟩
  obtain ⟨c₀⟩ := not_isEmpty_iff.1 hne
  let A : CuspPl D X eL hH U → ℤ := fun c ↦ ((a c).val : ℤ)
  have hsum : ((∑ c, A c : ℤ) : ZMod n) = 0 := by
    have : ∑ c, a c = 0 := ha
    simpa [A] using this
  obtain ⟨s, hs⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 hsum
  let E₀ : Divisor k (F D) := ∑ c, Finsupp.single c.1 (A c) - Finsupp.single c₀.1 (n * s)
  have hE₀ : ∀ c : CuspPl D X eL hH U, E₀ c.1 = A c - if c = c₀ then (n : ℤ) * s else 0 := by
    intro c
    simp only [E₀, Finsupp.coe_sub, Finsupp.coe_finsetSum, Pi.sub_apply, Finset.sum_apply,
      Finsupp.single_apply]
    congr 1
    · rw [Finset.sum_eq_single c (fun b _ hb ↦ if_neg fun h ↦ hb (Subtype.ext h))
        (fun h ↦ absurd (Finset.mem_univ c) h), if_pos rfl]
    · by_cases h : c = c₀
      · rw [if_pos (congrArg Subtype.val h).symm, if_pos h]
      · rw [if_neg fun h' ↦ h (Subtype.ext h'.symm), if_neg h]
  have hE₀' : ∀ P : Place k (F D), IsCentredP D X eL hH U P → E₀ P = 0 := by
    intro P hP
    simp only [E₀, Finsupp.coe_sub, Finsupp.coe_finsetSum, Pi.sub_apply, Finset.sum_apply,
      Finsupp.single_apply]
    rw [Finset.sum_eq_zero fun c _ ↦ if_neg fun h ↦ c.2 (by rw [h]; exact hP),
      if_neg fun h ↦ c₀.2 (by rw [h]; exact hP), sub_zero]
  have hdeg : E₀.deg = 0 := by
    have h1 : Divisor.deg (∑ c, Finsupp.single c.1 (A c) : Divisor k (F D)) = ∑ c, A c := by
      rw [← Divisor.degHom_apply, map_sum]
      simp only [Divisor.degHom_apply, Divisor.deg_single, Place.deg_eq_one, Nat.cast_one,
        mul_one]
    change Divisor.deg (∑ c, Finsupp.single c.1 (A c) - Finsupp.single c₀.1 ((n : ℤ) * s)) = 0
    rw [Divisor.deg_sub, h1, Divisor.deg_single, Place.deg_eq_one, Nat.cast_one, mul_one, hs,
      sub_self]
  obtain ⟨x, hx⟩ := exists_nsmul_eq_of_deg_eq_zero hH hk (n := n) (NeZero.ne n)
    ⟨(E₀ : Pic k (F D)), hdeg⟩
  obtain ⟨E₁, hE₁⟩ := QuotientAddGroup.mk_surjective (x : Pic k (F D))
  have hprin : E₀ - n • E₁ ∈ principal k (F D) := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul,
      hE₁]
    have := congrArg Subtype.val hx
    simp only [AddSubgroup.coe_nsmul] at this
    rw [this, sub_self]
  obtain ⟨f, hf0, hf⟩ := (mem_principal (k := k)).1 hprin
  have hord : ∀ P : Place k (F D), P.ord f = E₀ P - n * E₁ P := by
    intro P
    rw [← Divisor.div_apply, hf]
    simp
  refine ⟨f, hf0, fun P hP ↦ ?_, fun c ↦ ?_⟩
  · rw [hord, hE₀' P hP, zero_sub]
    exact (Dvd.intro _ rfl).neg_right
  · rw [hord, hE₀ c]
    push_cast
    by_cases h : c = c₀ <;> simp [h, A]

set_option maxHeartbeats 400000 in
-- unifying the instance paths on the subfields `F D`, `K₀ k t` of the Galois model is slow
/-- **Every sum-zero family of residues occurs** (divisibility of `Pic⁰(F)`). -/
theorem exists_resMap_eq (a : CuspPl D X eL hH U → ZMod n) (ha : a ∈ sumZero D X eL hH n) :
    ∃ v : kumU D X eL U n, resMap D X eL hH n (kumMap D X eL hk hH hτ n hU v) = a := by
  obtain ⟨f, hf0, hcent, hc⟩ := exists_ord_eq D X eL hk hH n a ha
  refine ⟨⟨Additive.ofMul (Units.mk0 f hf0),
    (mem_kumU D X eL U n).2 ((unramU_iff D X eL hH U n _).2 hcent)⟩, funext fun c ↦ ?_⟩
  simp only [resMap_kumMap]
  exact hc c

include hk hτ hU in
/-- **The image of the residue map is the sum-zero submodule.** -/
theorem range_resMap :
    LinearMap.range (resMap D X eL hH n (U := U)) = sumZero D X eL hH n := by
  apply le_antisymm
  · rintro _ ⟨e0, rfl⟩
    exact resMap_mem_sumZero D X eL hk hH hτ n hU e0
  · intro a ha
    obtain ⟨v, hv⟩ := exists_resMap_eq D X eL hk hH hτ n hU a ha
    exact ⟨_, hv⟩

end SumZero

end CurvesJacobian.CuspChar
