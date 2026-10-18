/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspCommensurable
import CurvesJacobian.Cusp.TorsionFree
import CurvesJacobian.Galois.SurfaceGroupAnyPoint

/-!
# Cuspidal inertia groups are torsion-free and nontrivial (MR8.3)

[AbsTopI] Lemma 4.1 (i) (`Topics in Absolute Anabelian Geometry I.txt` l.2742–2745): the
decomposition group of a cusp "is a torsion-free, commensurably terminal infinite subgroup of
`Δ`". Setting of `CurvesJacobian.Cusp.Inertia` (`k` algebraically closed of characteristic `0`,
`X` a curve over `k`, `V ⊆ X` open with finite nonempty complement).

* `CurvesJacobian.Cusp.eq_one_of_isOfFinOrder_pi1`: **`π₁ᵉᵗ(V)` is torsion-free** at every
  geometric point (`π₁ᵉᵗ(V) ≃ₜ* Π̂_{g,r}`, `r ≥ 1`, is free profinite);
  `cuspInertia_torsionFree`: hence so are the cuspidal inertia groups;
* `CurvesJacobian.Cusp.numChar2`: the number of continuous characters `T → ℤ/2`, an invariant of
  topological groups (`numChar2_congr`); `numChar2_surfaceCompletion`:
  `numChar2 Π̂_{g,r+1} = 2 ^ (2g + r)`;
* `CurvesJacobian.Cusp.cuspInertia_ne_bot`: **cuspidal inertia groups are nontrivial** if `V` has
  at least two cusps: otherwise filling in the cusp under `W'` is a continuous bijection
  `π₁ᵉᵗ(V) → π₁ᵉᵗ(V ∪ {y'})`, i.e. `Π̂_{g,r} ≅ Π̂_{g,r-1}` with `r - 1 ≥ 1`, which have
  `2 ^ (2g + r - 1) ≠ 2 ^ (2g + r - 2)` continuous characters to `ℤ/2`;
* `CurvesJacobian.Cusp.comapK_comap_eq_of_relIndex_ne_zero_of_two_lt`: **a Galois element
  commensurating a cuspidal inertia group of `U` fixes its cusp**, if `U` has at least three
  cusps (unconditional form of `comapK_comap_eq_of_relIndex_ne_zero`).
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Counting continuous characters to `ℤ/2` -/

/-- The number of continuous characters `T → ℤ/2` (homomorphisms with open kernel). -/
def numChar2 (T : Type*) [Group T] [TopologicalSpace T] : ℕ :=
  Nat.card {φ : T →* Multiplicative (ZMod 2) // IsOpen (φ.ker : Set T)}

/-- `numChar2` is invariant under topological group isomorphisms. -/
lemma numChar2_congr {A B : Type*} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
    (e : A ≃ₜ* B) : numChar2 A = numChar2 B :=
  Nat.card_congr
    { toFun := fun φ ↦ ⟨φ.1.comp e.symm.toMulEquiv.toMonoidHom, φ.2.preimage e.symm.continuous⟩
      invFun := fun ψ ↦ ⟨ψ.1.comp e.toMulEquiv.toMonoidHom, ψ.2.preimage e.continuous⟩
      left_inv := fun φ ↦ Subtype.ext (MonoidHom.ext fun x ↦ congrArg φ.1 (e.symm_apply_apply x))
      right_inv := fun ψ ↦ Subtype.ext (MonoidHom.ext fun x ↦
        congrArg ψ.1 (e.apply_symm_apply x)) }

/-- Two characters of `Ĝ` with open kernels agreeing on `G` are equal. -/
lemma eq_of_comp_eta {G : Type u} [Group G]
    {φ φ' : completion (GrpCat.of G) →* Multiplicative (ZMod 2)}
    (h₁ : IsOpen (φ.ker : Set (completion (GrpCat.of G))))
    (h₂ : IsOpen (φ'.ker : Set (completion (GrpCat.of G))))
    (h : ∀ x, φ (etaFn (GrpCat.of G) x) = φ' (etaFn (GrpCat.of G) x)) : φ = φ' := by
  ext z
  have hO : IsOpen {y : completion (GrpCat.of G) | z⁻¹ * y ∈ φ.ker ⊓ φ'.ker} :=
    (h₁.inter h₂).preimage (continuous_const.mul continuous_id)
  obtain ⟨x, hx⟩ := (denseRange (GrpCat.of G)).exists_mem_open hO ⟨z, by simp⟩
  have ha : φ (z⁻¹ * etaFn (GrpCat.of G) x) = 1 := hx.1
  have hb : φ' (z⁻¹ * etaFn (GrpCat.of G) x) = 1 := hx.2
  rw [map_mul, map_inv, inv_mul_eq_one] at ha hb
  rw [ha, hb, h]

/-- `numChar2 Ĝ` is the number of characters `G → ℤ/2`. -/
lemma numChar2_completion (G : Type u) [Group G] :
    numChar2 (completion (GrpCat.of G)) = Nat.card (G →* Multiplicative (ZMod 2)) := by
  let M := Multiplicative (ZMod 2)
  let up : M ≃* ULift.{u} M := MulEquiv.ulift.symm
  let lft : (G →* M) → (completion (GrpCat.of G) →* M) := fun ψ ↦
    up.symm.toMonoidHom.comp (liftFinite (up.toMonoidHom.comp ψ))
  have hlft : ∀ ψ, IsOpen ((lft ψ).ker : Set (completion (GrpCat.of G))) := fun ψ ↦ by
    convert isOpen_liftFinite_fiber (up.toMonoidHom.comp ψ) 1 using 1
    ext z
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, lft,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact (MulEquiv.map_eq_one_iff up.symm)
  have hlft_eta : ∀ ψ x, lft ψ (etaFn (GrpCat.of G) x) = ψ x := fun ψ x ↦ by
    simp [lft]
  exact Nat.card_congr
    { toFun := fun φ ↦ φ.1.comp (eta (GrpCat.of G)).hom
      invFun := fun ψ ↦ ⟨lft ψ, hlft ψ⟩
      left_inv := fun φ ↦ Subtype.ext (eq_of_comp_eta (hlft _) φ.2 fun x ↦ by
        rw [hlft_eta]
        rfl)
      right_inv := fun ψ ↦ MonoidHom.ext fun x ↦ hlft_eta ψ x }

/-- `SurfaceGen g r ≃ (Fin g ⊕ Fin g) ⊕ Fin r`. -/
def surfaceGenEquiv (g r : ℕ) : Pi1.SurfaceGen g r ≃ (Fin g ⊕ Fin g) ⊕ Fin r where
  toFun
    | .a i => .inl (.inl i)
    | .b i => .inl (.inr i)
    | .c j => .inr j
  invFun
    | .inl (.inl i) => .a i
    | .inl (.inr i) => .b i
    | .inr j => .c j
  left_inv s := by cases s <;> rfl
  right_inv x := by rcases x with (i | i) | j <;> rfl

/-- Characters transported along a group isomorphism. -/
def homEquivOfMulEquiv {A B M : Type*} [Group A] [Group B] [Group M] (e : A ≃* B) :
    (A →* M) ≃ (B →* M) where
  toFun φ := φ.comp e.symm.toMonoidHom
  invFun ψ := ψ.comp e.toMonoidHom
  left_inv φ := MonoidHom.ext fun x ↦ by simp
  right_inv ψ := MonoidHom.ext fun x ↦ by simp

/-- **`Π̂_{g,r+1}` has `2 ^ (2g + r)` continuous characters to `ℤ/2`** (it is free profinite on
`2g + r` generators). -/
lemma numChar2_surfaceCompletion (g r : ℕ) :
    numChar2 (completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g (r + 1))))) =
      2 ^ (g + g + r) := by
  haveI : Finite (Pi1.SurfaceGen g r) := Finite.of_equiv _ (surfaceGenEquiv g r).symm
  rw [numChar2_completion, Nat.card_congr (homEquivOfMulEquiv
    (MulEquiv.ulift.trans Pi1.SurfaceGroup.freeEquiv)), Nat.card_congr FreeGroup.lift.symm,
    Nat.card_fun, Nat.card_congr (surfaceGenEquiv g r)]
  simp

/-- `(insert y s)ᶜ` has one element less than `sᶜ` if `y ∉ s`. -/
lemma card_compl_insert_add_one {α : Type*} {s : Set α} (hs : sᶜ.Finite) {y : α} (hy : y ∉ s) :
    Nat.card ((insert y s)ᶜ : Set α) + 1 = Nat.card (sᶜ : Set α) := by
  have hc : (insert y s)ᶜ = sᶜ \ {y} := by
    ext x
    simp [not_or, and_comm]
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hc]
  exact Set.ncard_sdiff_singleton_add_one hy hs

/-! ### Torsion-freeness -/

section TorsionFree

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

include k in
/-- **`π₁ᵉᵗ(V)` is torsion-free** for `V ⊆ X` with finite nonempty complement, at every geometric
point. -/
theorem eq_one_of_isOfFinOrder_pi1 (V : X.Opens) [Nonempty V] (hVfin : (V : Set X)ᶜ.Finite)
    (hVne : (V : Set X)ᶜ.Nonempty) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x₀ : Spec (CommRingCat.of Ω) ⟶ V.toScheme) {γ : π₁ᵉᵗ(x₀)} (hγ : IsOfFinOrder γ) : γ = 1 := by
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup (k := k) V hVfin hVne x₀
  have hr : 0 < Nat.card ((V : Set X)ᶜ : Set X) :=
    haveI := hVfin.to_subtype
    Nat.card_pos_iff.2 ⟨hVne.to_subtype, inferInstance⟩
  have h := eq_one_of_isOfFinOrder_surfaceCompletion hr
    ((e.toMulEquiv.injective.isOfFinOrder_iff (f := e.toMulEquiv.toMonoidHom)).2 hγ)
  exact e.injective (h.trans (map_one e).symm)

include k in
/-- `numChar2 π₁ᵉᵗ(V) = 2 ^ (2g + r - 1)` for `V` with `r ≥ 1` cusps. -/
lemma numChar2_pi1 (V : X.Opens) [Nonempty V] (hVfin : (V : Set X)ᶜ.Finite) {r : ℕ}
    (hr : Nat.card ((V : Set X)ᶜ : Set X) = r + 1) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x₀ : Spec (CommRingCat.of Ω) ⟶ V.toScheme) :
    numChar2 π₁ᵉᵗ(x₀) = 2 ^ ((curveGenus k X).toNat + (curveGenus k X).toNat + r) := by
  have hVne : (V : Set X)ᶜ.Nonempty := by
    haveI := hVfin.to_subtype
    have : 0 < Nat.card ((V : Set X)ᶜ : Set X) := by omega
    exact Set.nonempty_coe_sort.1 (Nat.card_pos_iff.1 this).1
  obtain ⟨e⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup (k := k) V hVfin hVne x₀
  rw [numChar2_congr e]
  generalize Nat.card ((V : Set X)ᶜ : Set X) = n at hr ⊢
  subst hr
  exact numChar2_surfaceCompletion _ _

end TorsionFree

/-! ### Cuspidal inertia groups -/

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (hH : D.H ≤ D.HL)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

/-- **Cuspidal inertia groups are torsion-free.** -/
theorem cuspInertia_torsionFree (V : X.Opens) [Nonempty V] (hVfin : (V : Set X)ᶜ.Finite)
    (hVne : (V : Set X)ᶜ.Nonempty) (W : ValuationSubring Ω) :
    ∀ g ∈ cuspInertia D X eL hH V W, IsOfFinOrder g → g = 1 :=
  fun _ _ hg ↦ eq_one_of_isOfFinOrder_pi1 k V hVfin hVne _ hg

omit [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] [IsAlgClosed k] in
include hk in
/-- A place over the stalk at `y ∈ V` is centred on `V`. -/
lemma isCentredOn_of_stalkVS_eq (V : X.Opens) [Nonempty V] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) {y : X} (hyV : y ∈ V)
    (hy : stalkVS k y = comapK D X eL hk W) : IsCentredOn D X eL V W := by
  refine ⟨hkW, fun a ↦ ?_⟩
  have hmem : X.germToFunctionField V a ∈ stalkVS k y :=
    ⟨X.presheaf.germ _ y hyV a, by rw [Scheme.algebraMap_germ_eq_germToFunctionField]⟩
  rw [hy] at hmem
  exact hmem

include hk hτ in
/-- **Cuspidal inertia groups are nontrivial** when `V` has at least two cusps: for a place
`W' ⊇ k` not centred on `V`, `cuspInertia V W' ≠ ⊥`. -/
theorem cuspInertia_ne_bot {V : X.Opens} [Nonempty V] (hV : (V : Set X)ᶜ.Finite)
    (hV2 : 1 < Nat.card ((V : Set X)ᶜ : Set X)) {W' : ValuationSubring Ω}
    (hkW' : ∀ c : k, algebraMap k Ω c ∈ W') (hW'V : ¬ IsCentredOn D X eL V W') :
    cuspInertia D X eL hH V W' ≠ ⊥ := by
  intro hbot
  obtain ⟨y', hy'V, hy'⟩ := exists_notMem_of_not_isCentredOn D X eL hk V hkW' hW'V
  obtain ⟨V', hV'eq⟩ := exists_opens_coe_eq_insert k X V hV y'
  have hy'V' : y' ∈ V' := by
    rw [← SetLike.mem_coe, hV'eq]
    exact Set.mem_insert _ _
  haveI : Nonempty V' := ⟨⟨y', hy'V'⟩⟩
  have h : V ≤ V' := fun x hx ↦ by
    rw [← SetLike.mem_coe, hV'eq]
    exact Set.mem_insert_of_mem _ hx
  have hV' : (V' : Set X)ᶜ.Finite := by
    rw [hV'eq]
    exact hV.subset (Set.compl_subset_compl.2 (Set.subset_insert _ _))
  have hcard : Nat.card ((V' : Set X)ᶜ : Set X) + 1 = Nat.card ((V : Set X)ᶜ : Set X) := by
    rw [hV'eq]
    exact card_compl_insert_add_one hV hy'V
  have hsub : ((V' : Set X) \ V).Subsingleton := by
    rw [hV'eq]
    rintro a ⟨ha, haV⟩ b ⟨hb, hbV⟩
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact absurd hb hbV
    · exact absurd ha haV
  have hW'V' : IsCentredOn D X eL V' W' :=
    isCentredOn_of_stalkVS_eq D X eL hk V' hkW' hy'V' hy'
  let F := fundamentalGroupMap (X.homOfLE h) (specPoint_genericL_homOfLE D X eL h)
  -- the filling map is injective
  have hker := ker_fundamentalGroupMap_homOfLE_eq_normalClosure D X eL hk hH hτ hV hV' h hsub
    hW'V' hW'V
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
    obtain ⟨σ, rfl⟩ := (genericL_spec D X eL hk hH hτ V' hV').2 z
    exact ⟨_, fundamentalGroupMap_genericL D X eL hH h σ⟩
  let hm := (F.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩))
  let e := ContinuousMulEquiv.mk' hm (fun a b ↦ map_mul F a b)
  have he := numChar2_congr e
  obtain ⟨r, hr⟩ : ∃ r, Nat.card ((V' : Set X)ᶜ : Set X) = r + 1 :=
    ⟨Nat.card ((V' : Set X)ᶜ : Set X) - 1, by omega⟩
  rw [numChar2_pi1 k V hV (r := r + 1) (by omega), numChar2_pi1 k V' hV' hr] at he
  have := Nat.pow_right_injective (le_refl 2) he
  omega

include hk hτ in
/-- **A Galois element commensurating a cuspidal inertia group fixes its cusp** (for `U` with at
least three cusps). Let `W ⊇ k` be a place not centred on `U`, `σ ∈ H` with image
`γ ∈ π₁ᵉᵗ(U)`, and suppose `I_W ∩ γ I_W γ⁻¹` has finite index in `γ I_W γ⁻¹ = I_{σ(W)}`. Then
`σ(W)` lies over the same point of `X ∖ U` as `W`. -/
theorem comapK_comap_eq_of_relIndex_ne_zero_of_two_lt {U : X.Opens} [Nonempty U]
    (hU : (U : Set X)ᶜ.Finite) (hU3 : 2 < Nat.card ((U : Set X)ᶜ : Set X))
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) (σ : D.H)
    (hcomm : (cuspInertia D X eL hH U W).relIndex ((cuspInertia D X eL hH U W).map
      (MulAut.conj (D.chartHom hH (genericL D X eL U) σ)).toMonoidHom) ≠ 0) :
    comapK D X eL hk (W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω)) = comapK D X eL hk W := by
  let W' : ValuationSubring Ω := W.comap ((σ : Ω ≃ₐ[K₀ k t] Ω).symm : Ω →+* Ω)
  have hkW' : ∀ c : k, algebraMap k Ω c ∈ W' := fun c ↦ by
    change (σ : Ω ≃ₐ[K₀ k t] Ω).symm (algebraMap k Ω c) ∈ W
    rw [IsScalarTower.algebraMap_apply k (K₀ k t) Ω, AlgEquiv.commutes]
    rw [← IsScalarTower.algebraMap_apply k (K₀ k t) Ω]
    exact hkW c
  have hW'U : ¬ IsCentredOn D X eL U W' := (isCentredOn_comap_iff D X eL U (hH σ.2) W).not.2 hWU
  obtain ⟨y, hyU, hy⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW hWU
  obtain ⟨y', hy'U, hy'⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW' hW'U
  by_cases hyy : y' = y
  · change comapK D X eL hk W' = _
    rw [← hy, ← hy', hyy]
  exfalso
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
  have hcard : Nat.card ((V : Set X)ᶜ : Set X) + 1 = Nat.card ((U : Set X)ᶜ : Set X) := by
    rw [hVeq]
    exact card_compl_insert_add_one hU hyU
  have hWV : IsCentredOn D X eL V W := isCentredOn_of_stalkVS_eq D X eL hk V hkW hyV hy
  have hW'V : ¬ IsCentredOn D X eL V W' := fun hW'V ↦ by
    have hy'V := mem_of_isCentredOn D X eL hk V hV hW'V hy'
    rw [← SetLike.mem_coe, hVeq] at hy'V
    rcases hy'V with h' | h'
    · exact hyy h'
    · exact hy'U h'
  have hVne : (V : Set X)ᶜ.Nonempty := ⟨y', fun h' ↦ hW'V
    (isCentredOn_of_stalkVS_eq D X eL hk V hkW' h' hy')⟩
  have hne := cuspInertia_ne_bot D X eL hH hk hτ hV (by omega) hkW' hW'V
  have htf := cuspInertia_torsionFree D X eL hH V hV hVne W'
  apply hcomm
  rw [← cuspInertia_comap]
  exact relIndex_cuspInertia_eq_zero D X eL hH hk hτ hU hV h hWV hWU hne htf

end CurvesJacobian.Cusp
