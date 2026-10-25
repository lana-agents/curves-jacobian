/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspInertiaFacts
import CurvesJacobian.Galois.ClosedSurfaceGroupAlgClosed
import CurvesJacobian.Galois.BelyiSurfaceGroup

/-!
# The two cusps of a curve with two cusps have non-conjugate inertia groups

Setting of `CurvesJacobian.Cusp.Inertia` (`k` algebraically closed of characteristic `0`, `X` a
curve over `k` with Galois model `(D, eL)`, `H ≤ H_L`). Let `U ⊆ X` be open with exactly two
cusps and `X` of genus `g ≥ 1`.

* `CurvesJacobian.CuspChar.comapK_eq_of_cuspInertia_conj_two`: **if the cuspidal inertia groups
  of two places `W, W'` over cusps of `U` are conjugate in `π₁ᵉᵗ(U)`, then `W` and `W'` lie over
  the same cusp** (`comapK W = comapK W'`).

## Proof

Suppose `W, W'` lie over the two different cusps `y ≠ y'`. Fill in `y`: `V = U ∪ {y}` has the
single cusp `y'`. The filling map `π₁ᵉᵗ(U) ↠ π₁ᵉᵗ(V)` kills `cuspInertia U W`
(`CurvesJacobian.Cusp.cuspInertia_le_ker`), hence its conjugate `cuspInertia U W'`, whose image
is `cuspInertia V W'` (`CurvesJacobian.Cusp.map_cuspInertia_homOfLE`). But
`cuspInertia V W' ≠ ⊥` (`cuspInertia_ne_bot_of_card_eq_one`): otherwise filling in `y'` would be
an isomorphism `π₁ᵉᵗ(V) ≃ₜ* π₁ᵉᵗ(X)`, i.e. `Π̂_{g,1} ≃ₜ* Π̂_{g,0}`. These are distinguished by
counting continuous homomorphisms to a finite nonabelian group `P` (here `P = S₃`):
`Π_{g,1}` is free on `2g` generators, so it has `|P| ^ 2g` of them
(`natCard_monoidHom_surfaceGroup_one`), while `Π_{g,0}` has fewer
(`natCard_monoidHom_surfaceGroup_zero_lt`: the assignment `a₀ ↦ σ, b₀ ↦ τ` with `στ ≠ τσ` and
all other generators `↦ 1` violates the relation `∏ [aᵢ, bᵢ] = 1`).
-/

set_option linter.unusedSectionVars false

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite

universe u

noncomputable section

namespace CurvesJacobian.CuspChar

/-! ### Counting homomorphisms from `Π_{g,1}` and `Π_{g,0}` to a finite group -/

section Count

variable {g : ℕ} {P : Type*} [Group P]

/-- `Π_{g,1}` is free on `2g` generators, so it has `|P| ^ 2g` homomorphisms to a finite `P`. -/
lemma natCard_monoidHom_surfaceGroup_one [Finite P] :
    Nat.card (ULift.{u} (Pi1.SurfaceGroup g 1) →* P) = Nat.card P ^ (2 * g) := by
  haveI : Finite (Pi1.SurfaceGen g 0) :=
    Finite.of_equiv _ (CurvesJacobian.surfaceGenEquiv g 0).symm
  rw [Nat.card_congr (Cusp.homEquivOfMulEquiv
    (MulEquiv.ulift.trans (Pi1.SurfaceGroup.freeEquiv (g := g) (r := 0)))),
    natCard_monoidHom_freeGroup, CurvesJacobian.natCard_surfaceGen, add_zero]

/-- The product of commutators `∏ᵢ [xᵢ, yᵢ]` with `x₀ = σ`, `y₀ = τ` and all other entries `1`
is `[σ, τ]`. -/
lemma commProd_ite_zero {n : ℕ} (σ τ : P) :
    Pi1.SurfaceGen.commProd (fun i : Fin (n + 1) ↦ if i = 0 then σ else 1)
      (fun i ↦ if i = 0 then τ else 1) = σ * τ * σ⁻¹ * τ⁻¹ := by
  rw [Pi1.SurfaceGen.commProd, List.ofFn_succ, List.prod_cons]
  simp [Fin.succ_ne_zero]

/-- For `g ≥ 1` and a group `P` with two non-commuting elements, `Π_{g,0}` has fewer than
`|P| ^ 2g` homomorphisms to `P`. -/
lemma natCard_monoidHom_surfaceGroup_zero_lt [Finite P] (hg : 0 < g) {σ τ : P}
    (hστ : σ * τ ≠ τ * σ) :
    Nat.card (ULift.{u} (Pi1.SurfaceGroup g 0) →* P) < Nat.card P ^ (2 * g) := by
  classical
  haveI : Finite (Pi1.SurfaceGen g 0) :=
    Finite.of_equiv _ (CurvesJacobian.surfaceGenEquiv g 0).symm
  let ev : (ULift.{u} (Pi1.SurfaceGroup g 0) →* P) → (Pi1.SurfaceGen g 0 → P) :=
    fun φ s ↦ φ (ULift.up (PresentedGroup.of s))
  have hinj : Function.Injective ev := by
    intro φ ψ h
    have h' : φ.comp (MulEquiv.ulift.symm.toMonoidHom) =
        ψ.comp (MulEquiv.ulift.symm.toMonoidHom) :=
      PresentedGroup.ext fun s ↦ congrFun h s
    ext x
    exact DFunLike.congr_fun h' x.down
  have hns : ¬ Function.Surjective ev := by
    obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
    intro hs
    obtain ⟨φ, hφ⟩ := hs fun s ↦ match s with
      | .a i => if i = 0 then σ else 1
      | .b i => if i = 0 then τ else 1
      | .c _ => 1
    let φ' := φ.comp (MulEquiv.ulift.symm.toMonoidHom)
    have ha : ∀ i, φ' (Pi1.SurfaceGroup.genA i) = if i = 0 then σ else 1 :=
      fun i ↦ congrFun hφ (.a i)
    have hb : ∀ i, φ' (Pi1.SurfaceGroup.genB i) = if i = 0 then τ else 1 :=
      fun i ↦ congrFun hφ (.b i)
    have hrel := congrArg φ' (Pi1.SurfaceGroup.relation (g := n + 1) (r := 0))
    rw [map_one, map_mul, Pi1.SurfaceGen.map_commProd, Pi1.SurfaceGen.map_ordProd] at hrel
    simp only [ha, hb] at hrel
    rw [commProd_ite_zero] at hrel
    have h0 : Pi1.SurfaceGen.ordProd (fun j : Fin 0 ↦ φ' (Pi1.SurfaceGroup.cusp j)) = 1 := by
      simp [Pi1.SurfaceGen.ordProd]
    rw [h0, mul_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hrel
    exact hστ hrel
  haveI : Finite (ULift.{u} (Pi1.SurfaceGroup g 0) →* P) := Finite.of_injective ev hinj
  letI := Fintype.ofFinite (ULift.{u} (Pi1.SurfaceGroup g 0) →* P)
  letI := Fintype.ofFinite (Pi1.SurfaceGen g 0 → P)
  have hlt := Fintype.card_lt_of_injective_not_surjective ev hinj hns
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_fun,
    CurvesJacobian.natCard_surfaceGen, add_zero] at hlt
  exact hlt

/-- The permutations `(0 1)` and `(1 2)` of a three-element set do not commute. -/
lemma swap_mul_swap_ne :
    Equiv.swap (ULift.up.{u} (0 : Fin 3)) (ULift.up 1) * Equiv.swap (ULift.up 1) (ULift.up 2) ≠
      Equiv.swap (ULift.up 1) (ULift.up 2) *
        Equiv.swap (ULift.up.{u} (0 : Fin 3)) (ULift.up 1) := by
  intro h
  have h0 := DFunLike.congr_fun h (ULift.up 0)
  simp [Equiv.swap_apply_def] at h0

/-- **`Π̂_{g,1} ≄ Π̂_{g,0}` for `g ≥ 1`**: they have different numbers of continuous homomorphisms
to `S₃`. -/
theorem isEmpty_continuousMulEquiv_completion_surfaceGroup (hg : 0 < g) {r : ℕ} (hr : r = 1) :
    IsEmpty (completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g r))) ≃ₜ*
      completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g 0)))) := by
  subst hr
  refine ⟨fun e ↦ ?_⟩
  let S := Equiv.Perm (ULift.{u} (Fin 3))
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  have h := natCard_continuousMonoidHom_congr_left (A := S) e
  rw [natCard_continuousMonoidHom_completion, natCard_continuousMonoidHom_completion,
    natCard_monoidHom_surfaceGroup_one] at h
  have hlt := natCard_monoidHom_surfaceGroup_zero_lt (P := S) hg swap_mul_swap_ne
  rw [← h] at hlt
  exact lt_irrefl _ hlt

end Count

/-! ### The geometric statement -/

section Geometry

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

include hk hτ in
/-- **The cuspidal inertia group of a curve of genus `g ≥ 1` with one cusp is nontrivial**: for
`V ⊆ X` with exactly one cusp and a place `W' ⊇ k` not centred on `V`, `cuspInertia V W' ≠ ⊥`.
Otherwise filling in the cusp is an isomorphism `π₁ᵉᵗ(V) ≃ₜ* π₁ᵉᵗ(X)`, i.e.
`Π̂_{g,1} ≃ₜ* Π̂_{g,0}`. -/
theorem cuspInertia_ne_bot_of_card_eq_one {V : X.Opens} [Nonempty V]
    (hV : (V : Set X)ᶜ.Finite) (hV1 : Nat.card ((V : Set X)ᶜ : Set X) = 1)
    (hg : 0 < (curveGenus k X).toNat) {W' : ValuationSubring Ω}
    (hkW' : ∀ c : k, algebraMap k Ω c ∈ W') (hW'V : ¬ Cusp.IsCentredOn D X eL V W') :
    Cusp.cuspInertia D X eL hH V W' ≠ ⊥ := by
  intro hbot
  obtain ⟨y', hy'V, hy'⟩ := exists_notMem_of_not_isCentredOn D X eL hk V hkW' hW'V
  have hy'T : y' ∈ (⊤ : X.Opens) := by simp
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨y', hy'T⟩⟩
  have h : V ≤ ⊤ := le_top
  have hT : ((⊤ : X.Opens) : Set X)ᶜ.Finite := by simp
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 ((Nat.card_coe_set_eq _).symm.trans hV1)
  have hsub : (((⊤ : X.Opens) : Set X) \ V).Subsingleton := by
    rintro x ⟨-, hx⟩ z ⟨-, hz⟩
    have hx' : x ∈ ((V : Set X)ᶜ) := hx
    have hz' : z ∈ ((V : Set X)ᶜ) := hz
    rw [ha, Set.mem_singleton_iff] at hx' hz'
    rw [hx', hz']
  have hW'T : Cusp.IsCentredOn D X eL ⊤ W' :=
    Cusp.isCentredOn_of_stalkVS_eq D X eL hk ⊤ hkW' hy'T hy'
  let F := fundamentalGroupMap (X.homOfLE h) (specPoint_genericL_homOfLE D X eL h)
  -- the filling map is injective
  have hker := Cusp.ker_fundamentalGroupMap_homOfLE_eq_normalClosure D X eL hk hH hτ hV hT h
    hsub hW'T hW'V
  rw [hbot] at hker
  have hinj : Function.Injective F := by
    refine (MonoidHom.ker_eq_bot_iff F.toMonoidHom).1 (le_bot_iff.1 ?_)
    rw [hker]
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · exact Subgroup.normalClosure_le_normal (by simp)
    · rw [Subgroup.coe_bot]
      exact isClosed_singleton
  -- the filling map is surjective
  have hsurj : Function.Surjective F := fun z ↦ by
    obtain ⟨σ, rfl⟩ := (genericL_spec D X eL hk hH hτ ⊤ hT).2 z
    exact ⟨_, fundamentalGroupMap_genericL D X eL hH h σ⟩
  let hm := (F.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩))
  let e := ContinuousMulEquiv.mk' hm (fun a b ↦ map_mul F a b)
  -- `π₁ᵉᵗ(V) ≃ₜ* Π̂_{g,1}` and `π₁ᵉᵗ(X) ≃ₜ* Π̂_{g,0}`
  have hVne : (V : Set X)ᶜ.Nonempty := ⟨y', hy'V⟩
  obtain ⟨e₁⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup (k := k) V hV hVne
    (specPoint D.L Ω ≫ genericL D X eL V)
  let e₃ := fundamentalGroupEquivOfIso (asIso (⊤ : X.Opens).ι)
    (specPoint D.L Ω ≫ genericL D X eL ⊤)
  obtain ⟨e₂⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup_zero_of_isAlgClosed (k := k)
    ((specPoint D.L Ω ≫ genericL D X eL ⊤) ≫ (asIso (⊤ : X.Opens).ι).hom)
  exact (isEmpty_continuousMulEquiv_completion_surfaceGroup hg hV1).false
    (e₁.symm.trans (e.trans (e₃.trans e₂)))

include hk hτ in
/-- **The two cusps of a curve with exactly two cusps have non-conjugate inertia groups.** Let
`X` have genus `g ≥ 1`, `U ⊆ X` open with exactly two cusps, and `W, W' ⊇ k` places of `Ω` not
centred on `U`. If `cuspInertia U W'` is a `π₁ᵉᵗ(U)`-conjugate of `cuspInertia U W`, then `W` and
`W'` lie over the same cusp: `comapK W = comapK W'`. -/
theorem comapK_eq_of_cuspInertia_conj_two {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU2 : Nat.card ((U : Set X)ᶜ : Set X) = 2)
    (hg : 0 < (curveGenus k X).toNat) {W W' : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hkW' : ∀ c : k, algebraMap k Ω c ∈ W')
    (hWU : ¬ Cusp.IsCentredOn D X eL U W) (hW'U : ¬ Cusp.IsCentredOn D X eL U W')
    (hconj : ∃ γ, Cusp.cuspInertia D X eL hH U W' =
      (Cusp.cuspInertia D X eL hH U W).map (MulAut.conj γ).toMonoidHom) :
    comapK D X eL hk W = comapK D X eL hk W' := by
  obtain ⟨γ, hγ⟩ := hconj
  obtain ⟨y, hyU, hy⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW hWU
  obtain ⟨y', hy'U, hy'⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW' hW'U
  by_cases hyy : y' = y
  · rw [← hy, ← hy', hyy]
  exfalso
  -- fill in the cusp `y` under `W`
  obtain ⟨V, hVeq⟩ := Cusp.exists_opens_coe_eq_insert k X U hU y
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
  have hcard : Nat.card ((V : Set X)ᶜ : Set X) + 1 = Nat.card ((U : Set X)ᶜ : Set X) := by
    rw [hVeq]
    exact Cusp.card_compl_insert_add_one hU hyU
  have hV1 : Nat.card ((V : Set X)ᶜ : Set X) = 1 := by omega
  have hWV : Cusp.IsCentredOn D X eL V W := Cusp.isCentredOn_of_stalkVS_eq D X eL hk V hkW hyV hy
  have hW'V : ¬ Cusp.IsCentredOn D X eL V W' := fun hW'V ↦ by
    have hy'V := Cusp.mem_of_isCentredOn D X eL hk V hV hW'V hy'
    rw [← SetLike.mem_coe, hVeq] at hy'V
    rcases hy'V with h' | h'
    · exact hyy h'
    · exact hy'U h'
  -- the filling map kills `cuspInertia U W` and hence its conjugate `cuspInertia U W'`
  let f := (fundamentalGroupMap (X.homOfLE h) (specPoint_genericL_homOfLE D X eL h)).toMonoidHom
  have hker : Cusp.cuspInertia D X eL hH U W ≤ f.ker :=
    Cusp.cuspInertia_le_ker D X eL hH hk hτ hU hV h hWV hWU
  have hker' : Cusp.cuspInertia D X eL hH U W' ≤ f.ker := by
    rw [hγ]
    rintro _ ⟨b, hb, rfl⟩
    exact (MonoidHom.normal_ker f).conj_mem b (hker hb) γ
  apply cuspInertia_ne_bot_of_card_eq_one D X eL hH hk hτ hV hV1 hg hkW' hW'V
  rw [← Cusp.map_cuspInertia_homOfLE D X eL hH h W']
  exact (Subgroup.map_eq_bot_iff _).2 hker'

end Geometry

end CurvesJacobian.CuspChar
