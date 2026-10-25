/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.KummerCusp
import CurvesJacobian.Cusp.CuspConj

/-!
# Kummer characters separate the cusps (at least three cusps)

Setting of `CurvesJacobian/CuspChar/KummerCusp.lean`. If `F` has at least three cusps, two
places `W, W'` of `Ω` over cusps whose cuspidal inertia groups in `π₁ᵉᵗ(U)` are conjugate lie
over the same place of `F` (`CurvesJacobian.CuspChar.mem_iff_of_cuspInertia_conj`): otherwise a
Kummer character with residues `1` at `W ∩ F`, `-1` at a third cusp and `0` elsewhere
(`exists_resMap_eq`, divisibility of `Pic⁰`) would be trivial on one group and not on the other.
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
  {U : X.Opens} [Nonempty U] (n : ℕ) [NeZero n] (hU : (U : Set X)ᶜ.Finite)

attribute [local instance] isFunctionField_F

lemma ξv_conj_of_mem {G : Type*} [Group G] (H : Subgroup G) (a : Additive H →+ ZMod n)
    {γ x : G} (hγ : γ ∈ H) (hx : x ∈ H) : ξv H a (γ * x * γ⁻¹) = ξv H a x := by
  rw [ξv_mul (H.mul_mem hγ hx) (H.inv_mem hγ), ξv_mul hγ hx]
  have h : ξv H a (γ * γ⁻¹) = ξv H a γ + ξv H a γ⁻¹ := ξv_mul hγ (H.inv_mem hγ)
  rw [mul_inv_cancel] at h
  have h1 : ξv H a 1 = 0 := by rw [ξv_of_mem H.one_mem]; exact a.map_zero
  rw [h1] at h
  linear_combination -h

include hH in
lemma comap_ne_top_of_not_isCentredOn {W : ValuationSubring Ω}
    (hW : ¬ Cusp.IsCentredOn D X eL U W) (hkW : ∀ c : k, algebraMap k Ω c ∈ W) :
    W.comap (algebraMap (F D) Ω) ≠ ⊤ := by
  intro h
  refine hW ⟨hkW, fun a ↦ ?_⟩
  have : secF D X eL hH U a ∈ W.comap (algebraMap (F D) Ω) := h ▸ ValuationSubring.mem_top _
  exact this

set_option maxHeartbeats 400000 in
-- unifying the instance paths on the subfields `F D`, `K₀ k t` of the Galois model is slow
include hk hτ hU in
/-- **Kummer characters separate the cusps** (at least three cusps). -/
theorem mem_iff_of_cuspInertia_conj [Fact (1 < n)] [Fintype (CuspPl D X eL hH U)]
    (h3 : 3 ≤ Fintype.card (CuspPl D X eL hH U)) {W W' : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hW : ¬ Cusp.IsCentredOn D X eL U W) (hW' : ¬ Cusp.IsCentredOn D X eL U W')
    (hc : ∃ γ, Cusp.cuspInertia D X eL hH U W' =
      (Cusp.cuspInertia D X eL hH U W).map (MulAut.conj γ).toMonoidHom) (x : F D) :
    ((x : F D) : Ω) ∈ W ↔ ((x : F D) : Ω) ∈ W' := by
  classical
  let P := placeBelow D W hkW (comap_ne_top_of_not_isCentredOn D X eL hH hW hkW)
  let P' := placeBelow D W' hkW' (comap_ne_top_of_not_isCentredOn D X eL hH hW' hkW')
  have hWP : ∀ y : F D, ((y : F D) : Ω) ∈ W ↔ y ∈ P.1 := fun _ ↦ Iff.rfl
  have hWP' : ∀ y : F D, ((y : F D) : Ω) ∈ W' ↔ y ∈ P'.1 := fun _ ↦ Iff.rfl
  by_cases hPP : P = P'
  · rw [hWP, hWP', hPP]
  exfalso
  have hcP : ¬ IsCentredP D X eL hH U P :=
    fun h ↦ hW ((isCentredOn_iff_isCentredP D X eL hH U hWP).2 h)
  have hcP' : ¬ IsCentredP D X eL hH U P' :=
    fun h ↦ hW' ((isCentredOn_iff_isCentredP D X eL hH U hWP').2 h)
  let c : CuspPl D X eL hH U := ⟨P, hcP⟩
  let c' : CuspPl D X eL hH U := ⟨P', hcP'⟩
  have hcc' : c ≠ c' := fun h ↦ hPP (congrArg Subtype.val h)
  obtain ⟨c'', hc''⟩ : ((Finset.univ.erase c).erase c').Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hcc'.symm,
      Finset.mem_univ _⟩), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨hc''c', hc''c⟩ : c'' ≠ c' ∧ c'' ≠ c := by
    simp only [Finset.mem_erase] at hc''
    exact ⟨hc''.1, hc''.2.1⟩
  let a : CuspPl D X eL hH U → ZMod n := Pi.single c 1 - Pi.single c'' 1
  have ha : a ∈ sumZero D X eL hH n := by
    change ∑ d, a d = 0
    simp [a, Finset.sum_sub_distrib]
  obtain ⟨v, hv⟩ := exists_resMap_eq D X eL hk hH hτ n hU a ha
  obtain ⟨e, he⟩ : ∃ e, e = kumMap D X eL hk hH hτ n hU v := ⟨_, rfl⟩
  -- `e` kills the inertia of `W'`
  have hdiv' : (n : ℤ) ∣ P'.ord ((Additive.toMul v.1 : (F D)ˣ) : F D) := by
    have := congrFun hv c'
    rw [resMap_kumMap] at this
    have ha' : a c' = 0 := by simp [a, hcc'.symm, hc''c'.symm]
    rw [ha'] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 this
  have hker : Cusp.cuspInertia D X eL hH U W' ≤ kerSub _ e.1 := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨σ, hσ, rfl⟩
    refine mem_kerSub_iff.2 ⟨OpenSubgroup.mem_top _, ?_⟩
    rw [he, ξv_kumMap, kc_eq_one_of_dvd D n hWP' hσ _ hdiv', map_one, toAdd_one]
  -- the tame generator at `c`
  obtain ⟨hWc, -⟩ := (exists_tame D n c.1).choose_spec
  have hspec := (exists_tame D n c.1).choose_spec.2.choose_spec.2.choose_spec
  let Wc := (exists_tame D n c.1).choose
  have hmem : qU D X eL hH (tameGen D X eL hH U n c) ∈ Cusp.cuspInertia D X eL hH U Wc :=
    Subgroup.subset_closure ⟨_, hspec.1, rfl⟩
  have hL : W.comap (algebraMap D.L Ω) = Wc.comap (algebraMap D.L Ω) := by
    ext y
    have hy : (y : Ω) ∈ F D := mem_F_of_mem_L D hH y.2
    change (y : Ω) ∈ W ↔ (y : Ω) ∈ Wc
    exact (hWP ⟨_, hy⟩).trans (hWc ⟨_, hy⟩).symm
  obtain ⟨γ₁, hγ₁⟩ := Cusp.exists_cuspInertia_eq_conj D X eL hH U W Wc hL
  obtain ⟨γ, hγ⟩ := hc
  rw [hγ₁] at hmem
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hmem
  have hy' : γ * y * γ⁻¹ ∈ Cusp.cuspInertia D X eL hH U W' := by
    rw [hγ]
    exact ⟨y, hy, rfl⟩
  have h0 := (mem_kerSub_iff.1 (hker hy')).2
  rw [ξv_conj_of_mem n _ _ (OpenSubgroup.mem_top γ) (OpenSubgroup.mem_top y)] at h0
  have h1 : ξv _ e.1 (qU D X eL hH (tameGen D X eL hH U n c)) = 1 := by
    have := congrFun hv c
    rw [← he] at this
    have ha1 : a c = 1 := by simp [a, hc''c.symm]
    rw [ha1] at this
    exact this
  rw [← hyx] at h1
  change ξv _ e.1 (γ₁ * y * γ₁⁻¹) = 1 at h1
  rw [ξv_conj_of_mem n _ _ (OpenSubgroup.mem_top γ₁) (OpenSubgroup.mem_top y), h0] at h1
  exact zero_ne_one h1

section Count

/-- The place of `Ω` chosen over a cusp. -/
def cuspW (c : CuspPl D X eL hH U) : ValuationSubring Ω :=
  (exists_valuationSubring_liesOver D c.1).choose

lemma cuspW_spec (c : CuspPl D X eL hH U) :
    ∀ x : F D, ((x : F D) : Ω) ∈ cuspW D X eL hH c ↔ x ∈ c.1.1 :=
  (exists_valuationSubring_liesOver D c.1).choose_spec

lemma k_le_cuspW (c : CuspPl D X eL hH U) : ∀ a : k, algebraMap k Ω a ∈ cuspW D X eL hH c :=
  fun a ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (cuspW_spec D X eL hH c _).2 (c.1.algebraMap_mem a)

lemma not_isCentredOn_cuspW (c : CuspPl D X eL hH U) :
    ¬ Cusp.IsCentredOn D X eL U (cuspW D X eL hH c) :=
  fun h ↦ c.2 ((isCentredOn_iff_isCentredP D X eL hH U (cuspW_spec D X eL hH c)).1 h)

include hH in
lemma comap_L_eq {W W' : ValuationSubring Ω}
    (h : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ ((x : F D) : Ω) ∈ W') :
    W.comap (algebraMap D.L Ω) = W'.comap (algebraMap D.L Ω) := by
  ext y
  exact h ⟨_, mem_F_of_mem_L D hH y.2⟩

/-- **The cusp classes of `π₁ᵉᵗ(U)` are the cusps of `F`**, given that conjugate cuspidal inertia
groups lie over the same place (`hsep`). -/
theorem cuspCount_cusps_eq [Fintype (CuspPl D X eL hH U)]
    (hsep : ∀ W W' : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) →
      (∀ c : k, algebraMap k Ω c ∈ W') → ¬ Cusp.IsCentredOn D X eL U W →
      ¬ Cusp.IsCentredOn D X eL U W' → (∃ γ, Cusp.cuspInertia D X eL hH U W' =
        (Cusp.cuspInertia D X eL hH U W).map (MulAut.conj γ).toMonoidHom) →
      ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ ((x : F D) : Ω) ∈ W') :
    cuspCount (Cusp.cusps D X eL hH U) ⊤ = Fintype.card (CuspPl D X eL hH U) := by
  classical
  let f : CuspPl D X eL hH U → CuspQuot (Cusp.cusps D X eL hH U) ⊤ := fun c ↦
    Quotient.mk _ ⟨Cusp.cuspInertia D X eL hH U (cuspW D X eL hH c),
      cuspW D X eL hH c, k_le_cuspW D X eL hH c, not_isCentredOn_cuspW D X eL hH c, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' hcc
      obtain ⟨γ, -, hγ⟩ := Quotient.exact hcc
      have h := hsep _ _ (k_le_cuspW D X eL hH c) (k_le_cuspW D X eL hH c')
        (not_isCentredOn_cuspW D X eL hH c) (not_isCentredOn_cuspW D X eL hH c') ⟨γ, hγ.symm⟩
      apply Subtype.ext
      apply Place.ext
      ext x
      rw [← cuspW_spec D X eL hH c, ← cuspW_spec D X eL hH c', h]
    · rintro ⟨⟨I, W, hkW, hW, rfl⟩⟩
      let P := placeBelow D W hkW (comap_ne_top_of_not_isCentredOn D X eL hH hW hkW)
      have hcP : ¬ IsCentredP D X eL hH U P :=
        fun h ↦ hW ((isCentredOn_iff_isCentredP D X eL hH U (fun _ ↦ Iff.rfl)).2 h)
      refine ⟨⟨P, hcP⟩, Quotient.sound ?_⟩
      obtain ⟨γ, hγ⟩ := Cusp.exists_cuspInertia_eq_conj D X eL hH U
        (cuspW D X eL hH ⟨P, hcP⟩) W (comap_L_eq D hH fun x ↦
          (cuspW_spec D X eL hH ⟨P, hcP⟩ x).trans Iff.rfl)
      exact ⟨γ, Subgroup.mem_top _, hγ.symm⟩
  rw [cuspCount, Nat.card_congr (Equiv.ofBijective f hf).symm, Nat.card_eq_fintype_card]

end Count

end CurvesJacobian.CuspChar
