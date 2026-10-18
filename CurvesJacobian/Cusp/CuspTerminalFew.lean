/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspTerminal
import CurvesJacobian.Galois.AbelianPi1
import CurvesJacobian.Galois.ClosedSurfaceGroupAlgClosed

/-!
# Commensurable terminality of cuspidal inertia for curves with few cusps (MR8.3)

[AbsTopI] Lemma 4.1 (i) (`Topics in Absolute Anabelian Geometry I.txt` l.2742–2745): the
decomposition group of a cusp "is a torsion-free, commensurably terminal infinite subgroup of
`Δ`". `CurvesJacobian.Cusp.commensurator_cuspInertia` proves this for `U` with at least three
cusps. Here we remove that restriction for curves of genus `g ≥ 1` (every hyperbolic `U` with at
most two cusps has `g ≥ 1`).

Proof: the algebraic route of `CuspTerminal` passes to finite étale covers of `U` and needs these
to have at least three cusps. If `y` is the cusp under `W` and `V = U ∪ {y}`, then `π₁ᵉᵗ(V)` has
at least four continuous characters to `ℤ/2` (it is `Π̂_{g,r-1}` with `g ≥ 1`;
`numChar2_pi1`, resp. `card_continuousMonoidHom_zmod_etaleFundamentalGroup_proper` if `V = X`).
Two distinct nontrivial ones cut out an open normal subgroup `O₀` of `H` of index `4`
containing the decomposition group of `W`; the translates of `W` by representatives of three
cosets lie over three distinct cusps of every cover with Galois data inside `O₀`
(`CurvesJacobian.Cusp.CuspSep`).

## Main results

* `exists_two_chars`: a topological group with at least three continuous `ℤ/2`-characters has
  two distinct nontrivial ones, separated by elements `a, b`;
* `exists_cuspSep`: the open normal subgroup `O₀` with three separated translates of `W`;
* **`commensurator_cuspInertia_of_genus`**: `Comm(I_W) = I_W` in `π₁ᵉᵗ(U)` for every `U` with a
  cusp on a curve of genus `g ≥ 1`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

namespace CurvesJacobian.Cusp

section Chars

lemma eq_of_ne_one_zmod2 : ∀ u v : Multiplicative (ZMod 2), u ≠ 1 → v ≠ 1 → u = v := by
  decide

lemma mul_eq_one_of_ne_one_zmod2 :
    ∀ u v : Multiplicative (ZMod 2), u ≠ 1 → v ≠ 1 → u * v = 1 := by
  decide

/-- **Two separated characters.** A topological group with at least three continuous characters
to `ℤ/2` has continuous characters `χ₁, χ₂` and elements `a, b` with `χ₁ a ≠ 1`, `χ₁ b = 1`,
`χ₂ b ≠ 1`. -/
lemma exists_two_chars {G : Type*} [Group G] [TopologicalSpace G] (h : 2 < numChar2 G) :
    ∃ χ₁ χ₂ : G →* Multiplicative (ZMod 2), IsOpen (χ₁.ker : Set G) ∧ IsOpen (χ₂.ker : Set G) ∧
      ∃ a b : G, χ₁ a ≠ 1 ∧ χ₁ b = 1 ∧ χ₂ b ≠ 1 := by
  have hfin : Finite {φ : G →* Multiplicative (ZMod 2) // IsOpen (φ.ker : Set G)} :=
    Nat.finite_of_card_ne_zero (by unfold numChar2 at h; omega)
  haveI := Fintype.ofFinite {φ : G →* Multiplicative (ZMod 2) // IsOpen (φ.ker : Set G)}
  unfold numChar2 at h
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.1 h
  -- two distinct nontrivial characters
  obtain ⟨χ₁, χ₂, h₁, h₂, h12⟩ : ∃ χ₁ χ₂ : {φ : G →* Multiplicative (ZMod 2) //
      IsOpen (φ.ker : Set G)}, χ₁.1 ≠ 1 ∧ χ₂.1 ≠ 1 ∧ χ₁ ≠ χ₂ := by
    by_cases hx : x.1 = 1
    · refine ⟨y, z, fun hy ↦ hxy (Subtype.ext (hx.trans hy.symm)),
        fun hz ↦ hxz (Subtype.ext (hx.trans hz.symm)), hyz⟩
    · by_cases hy : y.1 = 1
      · exact ⟨x, z, hx, fun hz ↦ hyz (Subtype.ext (hy.trans hz.symm)), hxz⟩
      · exact ⟨x, y, hx, hy, hxy⟩
  refine ⟨χ₁.1, χ₂.1, χ₁.2, χ₂.2, ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, χ₁.1 a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h₁ (MonoidHom.ext hcon)
  obtain ⟨z₀, hz₀⟩ : ∃ z, χ₂.1 z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h₂ (MonoidHom.ext hcon)
  by_contra hcon
  push Not at hcon
  have hsub : ∀ b, χ₁.1 b = 1 → χ₂.1 b = 1 := fun b hb ↦ hcon a b ha hb
  have hz₁ : χ₁.1 z₀ ≠ 1 := fun h' ↦ hz₀ (hsub z₀ h')
  refine h12 (Subtype.ext (MonoidHom.ext fun w ↦ ?_))
  by_cases hw : χ₁.1 w = 1
  · rw [hw, hsub w hw]
  · have hwz : χ₁.1 (w * z₀) = 1 := by
      rw [map_mul]
      exact mul_eq_one_of_ne_one_zmod2 _ _ hw hz₁
    have h2 := hsub _ hwz
    rw [map_mul] at h2
    have hw2 : χ₂.1 w ≠ 1 := fun h' ↦ by
      rw [h', one_mul] at h2
      exact hz₀ h2
    exact eq_of_ne_one_zmod2 _ _ hw hw2

/-- A homomorphism to `ℤ/2` with open kernel is continuous. -/
lemma continuous_of_isOpen_ker_zmod2 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (φ : G →* Multiplicative (ZMod 2)) (h : IsOpen (φ.ker : Set G)) :
    Continuous φ := by
  rw [continuous_discrete_rng]
  intro c
  by_cases hc : ∃ x, φ x = c
  · obtain ⟨x, rfl⟩ := hc
    have e : φ ⁻¹' {φ x} = (fun y ↦ x⁻¹ * y) ⁻¹' (φ.ker : Set G) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker,
        map_mul, map_inv]
      constructor
      · intro hy
        rw [hy, inv_mul_cancel]
      · intro hy
        exact (inv_mul_eq_one.1 hy).symm
    rw [e]
    exact h.preimage (continuous_const.mul continuous_id)
  · push Not at hc
    convert isOpen_empty
    ext y
    simpa using hc y

/-- `numChar2` counts the continuous characters to `ℤ/2`. -/
lemma numChar2_eq_card_continuousMonoidHom {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    numChar2 G = Nat.card (ContinuousMonoidHom G (Multiplicative (ZMod 2))) :=
  Nat.card_congr
    { toFun := fun φ ↦ ⟨φ.1, continuous_of_isOpen_ker_zmod2 φ.1 φ.2⟩
      invFun := fun ψ ↦ ⟨ψ.toMonoidHom, by
        rw [MonoidHom.coe_ker]
        exact (isOpen_discrete _).preimage ψ.continuous⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Three values separated by two `ℤ/2`-valued functions. -/
lemma fin3_sep (f₁ f₂ : Fin 3 → Multiplicative (ZMod 2)) (h0₁ : f₁ 0 = 1) (h1₁ : f₁ 1 ≠ 1)
    (h2₁ : f₁ 2 = 1) (h0₂ : f₂ 0 = 1) (h2₂ : f₂ 2 ≠ 1) :
    ∀ i j, i ≠ j → f₁ i = f₁ j → f₂ i = f₂ j → False := by
  intro i j hij e1 e2
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h1₁ (e1.symm.trans h0₁)
    | exact h1₁ (e1.trans h0₁)
    | exact h2₂ (e2.symm.trans h0₂)
    | exact h2₂ (e2.trans h0₂)
    | exact h1₁ (e1.trans h2₁)
    | exact h1₁ (e1.symm.trans h2₁)

end Chars

section Few

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

omit [Algebra k Ω] in
include k in
/-- `π₁ᵉᵗ(V)` of an open `V` (finite complement) of a curve of genus `g ≥ 1` has at least three
continuous characters to `ℤ/2`. -/
lemma two_lt_numChar2_pi1 (hg : 1 ≤ (curveGenus k X).toNat) (V : X.Opens) [Nonempty V]
    (hV : (V : Set X)ᶜ.Finite) (x₀ : Spec (CommRingCat.of Ω) ⟶ V.toScheme) :
    2 < numChar2 π₁ᵉᵗ(x₀) := by
  by_cases hVc : (V : Set X)ᶜ.Nonempty
  · obtain ⟨r, hr⟩ : ∃ r, Nat.card ((V : Set X)ᶜ : Set X) = r + 1 := by
      haveI := hV.to_subtype
      have : 0 < Nat.card ((V : Set X)ᶜ : Set X) :=
        Nat.card_pos_iff.2 ⟨hVc.to_subtype, inferInstance⟩
      exact ⟨_, (Nat.succ_pred_eq_of_pos this).symm⟩
    rw [numChar2_pi1 k V hV hr x₀]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ((curveGenus k X).toNat + (curveGenus k X).toNat + r) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hVtop : V = ⊤ := by
      ext x
      simp only [Opens.coe_top, Set.mem_univ, iff_true]
      by_contra hx
      exact hVc ⟨x, hx⟩
    subst hVtop
    have e := fundamentalGroupEquivOfIso (asIso (⊤ : X.Opens).ι) x₀
    rw [numChar2_eq_card_continuousMonoidHom,
      CurvesJacobian.ClosedSurface.natCard_continuousMonoidHom_congr e,
      card_continuousMonoidHom_zmod_etaleFundamentalGroup_proper (k := k)]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (curveGenus k X).toNat) := Nat.pow_le_pow_right (by norm_num) (by omega)

include hk hτ in
/-- **Three separated translates of a cusp place** (genus `g ≥ 1`): for a place `W ⊇ k` not
centred on `U`, there is an open normal subgroup `O₀ ⊇ ker(H ↠ π₁ᵉᵗ(U))` of `H` with
`CuspSep D O₀ W`. -/
theorem exists_cuspSep (hg : 1 ≤ (curveGenus k X).toNat) {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) :
    ∃ O₀ : Subgroup D.H, O₀.Normal ∧ IsOpen (O₀ : Set D.H) ∧
      (D.chartHom hH (genericL D X eL U)).ker ≤ O₀ ∧ CuspSep D O₀ W := by
  obtain ⟨y, hyU, hy⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW hWU
  obtain ⟨V, hVeq⟩ := exists_opens_coe_eq_insert k X U hU y
  have hyV : y ∈ V := by
    rw [← SetLike.mem_coe, hVeq]
    exact Set.mem_insert _ _
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  have h : U ≤ V := fun x hx ↦ by
    rw [← SetLike.mem_coe, hVeq]
    exact Set.mem_insert_of_mem _ hx
  have hV : (V : Set X)ᶜ.Finite := by
    rw [hVeq]
    exact hU.subset (Set.compl_subset_compl.2 (Set.subset_insert _ _))
  have hWV : IsCentredOn D X eL V W := isCentredOn_of_stalkVS_eq D X eL hk V hkW hyV hy
  obtain ⟨χ₁, χ₂, ho₁, ho₂, a, b, ha, hb1, hb2⟩ :=
    exists_two_chars (two_lt_numChar2_pi1 X hg V hV (specPoint D.L Ω ≫ genericL D X eL V))
  let F := D.chartHom hH (genericL D X eL V)
  have hF : ∀ σ, F σ = fundamentalGroupMap (X.homOfLE h) (specPoint_genericL_homOfLE D X eL h)
      (D.chartHom hH (genericL D X eL U) σ) := fun σ ↦
    (fundamentalGroupMap_genericL D X eL hH h σ).symm
  have hsurj := (genericL_spec D X eL hk hH hτ V hV).2
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have hd : ∀ d ∈ decompH D W, F d = 1 := fun d hd ↦ by
    rw [hF]
    have hmem : D.chartHom hH (genericL D X eL U) d ∈ cuspInertia D X eL hH U W := by
      rw [cuspInertia_eq_map_decompH D X eL hH U hkW hWU]
      exact ⟨d, hd, rfl⟩
    exact cuspInertia_le_ker D X eL hH hk hτ hU hV h hWV hWU hmem
  refine ⟨(χ₁.ker ⊓ χ₂.ker).comap F, ?_, ?_, ?_, ?_⟩
  · haveI : (χ₁.ker ⊓ χ₂.ker).Normal := Subgroup.normal_inf_normal _ _
    exact Subgroup.Normal.comap inferInstance F
  · rw [Subgroup.coe_comap, Subgroup.coe_inf]
    exact (ho₁.inter ho₂).preimage (D.continuous_chartHom hH _)
  · intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    change F σ ∈ χ₁.ker ⊓ χ₂.ker
    rw [hF, hσ, map_one]
    exact one_mem _
  · let s : Fin 3 → D.H := ![1, a', b']
    have h0₁ : χ₁ (F (s 0)) = 1 := by
      change χ₁ (F 1) = 1
      rw [map_one, map_one]
    have h0₂ : χ₂ (F (s 0)) = 1 := by
      change χ₂ (F 1) = 1
      rw [map_one, map_one]
    have hdist := fin3_sep (fun i ↦ χ₁ (F (s i))) (fun i ↦ χ₂ (F (s i))) h0₁ ha hb1 h0₂ hb2
    refine ⟨s, fun i j hij o ho d hd' heq ↦ ?_⟩
    have ho' : F o ∈ χ₁.ker ⊓ χ₂.ker := ho
    have e1 : χ₁ (F (s i)) = χ₁ (F (s j)) := by
      rw [heq, map_mul, map_mul, map_mul, map_mul, hd d hd', map_one, mul_one, ho'.1, one_mul]
    have e2 : χ₂ (F (s i)) = χ₂ (F (s j)) := by
      rw [heq, map_mul, map_mul, map_mul, map_mul, hd d hd', map_one, mul_one, ho'.2, one_mul]
    exact hdist i j hij e1 e2

include hk hτ in
/-- **Cuspidal inertia groups are commensurably terminal** ([AbsTopI] Lemma 4.1 (i),
`Topics in Absolute Anabelian Geometry I.txt` l.2742–2745) on a curve of genus `g ≥ 1`, for any
`U` with finite complement (any number of cusps). -/
theorem commensurator_cuspInertia_of_genus (hg : 1 ≤ (curveGenus k X).toNat) {U : X.Opens}
    [Nonempty U] (hU : (U : Set X)ᶜ.Finite) {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hWU : ¬ IsCentredOn D X eL U W) :
    Subgroup.Commensurable.commensurator (cuspInertia D X eL hH U W) =
      cuspInertia D X eL hH U W :=
  commensurator_cuspInertia_of_or D X eL hH hk hτ hU
    (Or.inr (exists_cuspSep D X eL hH hk hτ hg hU hkW hWU)) hkW hWU

include hk hτ in
/-- **Cuspidal inertia groups are commensurably terminal** for every hyperbolic `U`: either `U`
has at least three cusps or the genus is at least one. -/
theorem commensurator_cuspInertia_of_hyperbolic {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite)
    (hhyp : 2 < Nat.card ((U : Set X)ᶜ : Set X) ∨ 1 ≤ (curveGenus k X).toNat)
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) :
    Subgroup.Commensurable.commensurator (cuspInertia D X eL hH U W) =
      cuspInertia D X eL hH U W := by
  rcases hhyp with h3 | hg
  · exact commensurator_cuspInertia D X eL hH hk hτ hU h3 hkW hWU
  · exact commensurator_cuspInertia_of_genus D X eL hH hk hτ hg hU hkW hWU

end Few

end CurvesJacobian.Cusp
