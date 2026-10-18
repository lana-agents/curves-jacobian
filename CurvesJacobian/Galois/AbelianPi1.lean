/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.PiCharacters
import CurvesJacobian.Galois.EtalePi1Open
import CurvesJacobian.Galois.CurveGaloisData
import CurvesJacobian.Galois.SurfaceGroupAnyPoint
import CurvesJacobian.Scheme.CurvePic
import CurvesJacobian.Cusp.Inertia

/-!
# The abelianised `π₁ᵉᵗ` of a proper curve: `Hom(π₁ᵉᵗ(X), ℤ/n) ≅ (ℤ/n)^{2g}`

Let `X` be a (proper, smooth) curve over an algebraically closed field `k` of characteristic `0`
and `x₀ ∈ X` a closed point, `U = X ∖ {x₀}`. Every continuous character `π₁ᵉᵗ(U) → μₙ` factors
through `π₁ᵉᵗ(X)`: in the Galois model it is a Kummer class `κ(v)` (`v ∈ K(X)ˣ`) unramified at
all places centred on `U`, i.e. `n ∣ ord_P v` for all `P ≠ x₀`
(`CurvesJacobian.dvd_ord_of_evalTriv_eq_one`, the local half of `isUnramifiedKummer_iff`); since
`deg (div v) = 0` and all places have degree `1`, also `n ∣ ord_{x₀} v`
(`CurvesJacobian.dvd_ord_of_forall_ne`), so `κ(v)` is unramified everywhere
(`CurvesJacobian.kernel_SAll_le_of_kernel_SU_le`). Geometrically: the inertia at a single puncture
of `X ∖ {x₀}` is a product of commutators, invisible to abelian covers.

In characteristic zero we know `π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,1}`, the profinite completion of a free group
of rank `2g` (`CurvesJacobian.etaleFundamentalGroup_equiv_profiniteSurfaceGroup`), hence:

* `CurvesJacobian.card_continuousMonoidHom_etaleFundamentalGroup_proper`: for every geometric
  point `ξ` of `X` and every discrete group `A ≃* ℤ/n`,
  `#Hom_cont(π₁ᵉᵗ(X, ξ), A) = n^{2g}`;
* `CurvesJacobian.card_continuousMonoidHom_zmod_etaleFundamentalGroup_proper`: the same for
  `A = Multiplicative (ZMod n)`.

This is the abelian part of `π₁ᵉᵗ(X) ≃ Π̂_g` (r = 0); the non-abelian statement needs the
identification of the cusp loop with `∏ [aᵢ, bᵢ]` (normal form of the surface).
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale
open Pi1.Orbifold AffOrbicurve KummerTheory Curve WeilCurves.FunctionField Pi1.Profinite

universe u

noncomputable section

namespace CurvesJacobian

/-! ### Characters through a continuous surjection of compact groups -/

section Surjection

variable {G Q A : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [Group Q]
  [TopologicalSpace Q] [T2Space Q] [Group A] [TopologicalSpace A] [DiscreteTopology A]

omit [DiscreteTopology A] in
/-- Continuous characters of a quotient `G ↠ Q` (compact onto Hausdorff) are the continuous
characters of `G` killing the kernel. -/
theorem natCard_continuousMonoidHom_of_surjective (p : G →* Q) (hp : Continuous p)
    (hsurj : Function.Surjective p) :
    Nat.card (ContinuousMonoidHom Q A) =
      Nat.card {φ : ContinuousMonoidHom G A // p.ker ≤ φ.toMonoidHom.ker} := by
  let pc : ContinuousMonoidHom G Q := { p with continuous_toFun := hp }
  have hq : Topology.IsQuotientMap p := (hp.isClosedMap).isQuotientMap hp hsurj
  refine Nat.card_congr (Equiv.ofBijective (fun ψ ↦ ⟨ψ.comp pc, fun g hg ↦ ?_⟩) ⟨?_, ?_⟩)
  · change ψ (p g) = 1
    rw [MonoidHom.mem_ker.1 hg, map_one]
  · intro ψ₁ ψ₂ h
    ext q
    obtain ⟨g, rfl⟩ := hsurj q
    exact DFunLike.congr_fun (congrArg Subtype.val h) g
  · rintro ⟨φ, hφ⟩
    let f : Q →* A := (QuotientGroup.lift p.ker φ.toMonoidHom hφ).comp
      (QuotientGroup.quotientKerEquivOfSurjective p hsurj).symm.toMonoidHom
    have hf : ∀ g, f (p g) = φ g := fun g ↦ by
      change QuotientGroup.lift p.ker φ.toMonoidHom hφ
        ((QuotientGroup.quotientKerEquivOfSurjective p hsurj).symm (p g)) = φ g
      have : (QuotientGroup.quotientKerEquivOfSurjective p hsurj).symm (p g) =
          (QuotientGroup.mk g : G ⧸ p.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      rw [this]
      rfl
    have hfc : Continuous f := by
      rw [hq.continuous_iff]
      have : (f ∘ p) = φ := funext hf
      rw [this]
      exact φ.continuous
    refine ⟨{ f with continuous_toFun := hfc }, Subtype.ext ?_⟩
    ext g
    exact hf g

end Surjection

/-! ### Kummer classes and a single exceptional place -/

section Kummer

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]
  (n : ℕ) [NeZero n]

attribute [local instance] isFunctionField_F

/-- **The local half of `isUnramifiedKummer_iff`**: if the Kummer class of `v` is trivial on the
inertia group of one place `W` over the place `P` of `F`, then `n ∣ ord_P v`. -/
theorem dvd_ord_of_evalTriv_eq_one (v : (F D)ˣ) (P : Place k (F D)) {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1)
    (hun : ∀ (hk : ∀ c : k, algebraMap k Ω c ∈ W) (σ : D.H)
      (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W),
      ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω v)) = 1) :
    (n : ℤ) ∣ P.ord (v : F D) := by
  have hk : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW _).2 (P.algebraMap_mem c)
  obtain ⟨π, hπ1⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  have hπmem : π ∈ P.1 ∧ π⁻¹ ∉ P.1 := by
    refine ⟨P.mem_of_ord_nonneg (by rw [hπ1]; norm_num), fun h ↦ ?_⟩
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, hπ1] at this
    norm_num at this
  have hπW : W.valuation ((π : F D) : Ω) < 1 := (valuation_lt_one_iff hW hπ0).2 hπmem
  have hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω) := by
    intro f hf hlt
    set x : F D := ⟨f, hf⟩
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
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := NeZero.charZero
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  let ζ : Mu n Ω := hμ.toRootsOfUnity
  obtain ⟨σ, hσ, hσζ⟩ := evalTriv_kummer_surjective (D := D) hk (Units.mk0 π hπ0) hπW hπ n ζ
  set m := P.ord (v : F D)
  have hunit : P.ord ((v * (Units.mk0 π hπ0) ^ (-m) : (F D)ˣ) : F D) = 0 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, P.ord_mul v.ne_zero
      (zpow_ne_zero _ hπ0), P.ord_zpow, hπ1]
    ring
  have hu0 : ((v * (Units.mk0 π hπ0) ^ (-m) : (F D)ˣ) : F D) ≠ 0 := Units.ne_zero _
  obtain ⟨hu1, hu2⟩ := (P.ord_eq_zero_iff hu0).1 hunit
  have heq := evalTriv_res_kummer_eq_zpow hk hσ n v (Units.mk0 π hπ0) m ((hW _).2 hu1)
    ((hW _).2 (by simpa using hu2))
  rw [hun hk σ hσ, hσζ] at heq
  have h1 : (Mu.val ζ) ^ m = 1 := by rw [← map_zpow, ← heq, map_one]
  have h2 : μ ^ m = 1 := by
    have := congrArg (fun z : Ωˣ ↦ (z : Ω)) h1
    simp only [Units.val_zpow_eq_zpow_val, Units.val_one] at this
    exact this
  exact (hμ.zpow_eq_one_iff_dvd m).1 h2

/-- The class attached to a continuous character of `H` (`H ≅ Gal(Ω/F)` acts trivially on
`μₙ`). -/
def classOfH [IsAlgClosed k] (φ : ContinuousMonoidHom D.H (Mu n Ω)) :
    ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω) :=
  ContH1.mk (ContH1.mkCocycle (fun τ ↦ φ (ofGalF D τ))
    (φ.continuous.comp (continuous_ofGalF D))
    (fun g h ↦ by
      change φ (ofGalF D (g * h)) = g • φ (ofGalF D h) * φ (ofGalF D g)
      rw [galF_smul_mu, map_mul (ofGalF D), map_mul φ, mul_comm]))

lemma charOfH_classOfH [IsAlgClosed k] (φ : ContinuousMonoidHom D.H (Mu n Ω)) (σ : D.H) :
    charOfH D n (classOfH D n φ) σ = φ σ := by
  unfold classOfH
  rw [charOfH_mk]
  change φ (ofGalF D (toGalF D σ)) = _
  rw [show ofGalF D (toGalF D σ) = σ from (galFEquiv D).symm_apply_apply σ]

end Kummer

section Degree

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K]

/-- If `n ∣ ord_P v` at all places but one, then also at the remaining one (`deg (div v) = 0`
and all places have degree `1`). -/
theorem dvd_ord_of_forall_ne (n : ℤ) (v : K) (P₀ : Place k K)
    (h : ∀ P : Place k K, P ≠ P₀ → n ∣ P.ord v) : n ∣ P₀.ord v := by
  classical
  have hdeg := Divisor.deg_div (k := k) v
  rw [Divisor.deg, Finsupp.sum] at hdeg
  simp only [Divisor.div_apply, Place.deg_eq_one, Nat.cast_one, mul_one] at hdeg
  by_cases hP₀ : P₀ ∈ (Divisor.div k v).support
  · rw [← Finset.add_sum_erase _ _ hP₀] at hdeg
    have hrest : n ∣ ∑ P ∈ (Divisor.div k v).support.erase P₀, P.ord v :=
      Finset.dvd_sum fun P hP ↦ h P (Finset.ne_of_mem_erase hP)
    have : P₀.ord v = -∑ P ∈ (Divisor.div k v).support.erase P₀, P.ord v := by omega
    rw [this]
    exact (dvd_neg).2 hrest
  · rw [Finsupp.notMem_support_iff, Divisor.div_apply] at hP₀
    rw [hP₀]
    exact dvd_zero n

/-- If `n ∣ ord_P v` outside a set of at most one place, then everywhere. -/
theorem dvd_ord_of_subsingleton (n : ℤ) (v : K) (E : Set (Place k K)) (hE : E.Subsingleton)
    (h : ∀ P : Place k K, P ∉ E → n ∣ P.ord v) (P : Place k K) : n ∣ P.ord v := by
  by_cases hP : P ∈ E
  · exact dvd_ord_of_forall_ne n v P fun Q hQ ↦ h Q fun hQE ↦ hQ (hE hQE hP)
  · exact h P hP

end Degree

/-! ### Characters of `π₁ᵉᵗ(X ∖ {x₀})` factor through `π₁ᵉᵗ(X)` -/

section Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  [IsAlgClosed k] [CharZero k] [IsCurveOver k X]

/-- The valuation subring of `K(X)` below a valuation subring `W` of `Ω`. -/
abbrev comapK (W : ValuationSubring Ω) : ValuationSubring X.functionField :=
  W.comap (embK D X eL hk).toRingHom

omit [IsAlgClosed k] in
include hk in
/-- A place `W ⊇ k` of `Ω` not centred on `U` lies over the stalk at a point outside `U`. -/
lemma exists_notMem_of_not_isCentredOn (U : X.Opens) [Nonempty U] {W : ValuationSubring Ω}
    (hkW : ∀ c : k, algebraMap k Ω c ∈ W) (hW : ¬ Cusp.IsCentredOn D X eL U W) :
    ∃ y : X, y ∉ U ∧ stalkVS k y = comapK D X eL hk W := by
  haveI := isSeparated_of_over k X
  have hX := valuationRing_stalk_of_isCurveOver k X
  have hkO : ∀ c : k, algebraMap k X.functionField c ∈ comapK D X eL hk W := fun c ↦ by
    change ((eL (algebraMap k X.functionField c) : D.L) : Ω) ∈ W
    rw [hk]
    exact hkW c
  set y := (pointEquivValuationSubringOver k hX).symm ⟨_, hkO⟩
  have hy : stalkVS k y = comapK D X eL hk W := by
    have := congrArg Subtype.val ((pointEquivValuationSubringOver k hX).apply_symm_apply ⟨_, hkO⟩)
    rw [pointEquivValuationSubringOver_apply] at this
    exact this
  refine ⟨y, fun hyU ↦ hW ⟨hkW, fun a ↦ ?_⟩, hy⟩
  have hmem : X.germToFunctionField U a ∈ stalkVS k y :=
    ⟨X.presheaf.germ _ y hyU a, by rw [Scheme.algebraMap_germ_eq_germToFunctionField]⟩
  rw [hy] at hmem
  exact hmem

attribute [local instance] isFunctionField_F

omit [IsAlgClosed k] in
include hk in
/-- Two places `W, W' ⊇ k` of `Ω` which are not centred on `U = X ∖ {x₀}` induce the same place
on `F`. -/
lemma eq_of_not_isCentredOn (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ.Subsingleton)
    {W W' : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hkW' : ∀ c : k, algebraMap k Ω c ∈ W') (hW : ¬ Cusp.IsCentredOn D X eL U W)
    (hW' : ¬ Cusp.IsCentredOn D X eL U W') (x : F D) :
    ((x : F D) : Ω) ∈ W ↔ ((x : F D) : Ω) ∈ W' := by
  obtain ⟨y, hyU, hy⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW hW
  obtain ⟨y', hyU', hy'⟩ := exists_notMem_of_not_isCentredOn D X eL hk U hkW' hW'
  have hyy : y = y' := hU hyU hyU'
  have hWW : comapK D X eL hk W = comapK D X eL hk W' := by rw [← hy, ← hy', hyy]
  have hxL : ((x : F D) : Ω) ∈ D.L := by
    rw [GaloisData.L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ (D.le hσ)
  set z := eL.symm ⟨_, hxL⟩
  have hz : ((x : F D) : Ω) = embK D X eL hk z := by
    rw [embK_apply, RingEquiv.apply_symm_apply]
  rw [hz]
  change z ∈ comapK D X eL hk W ↔ z ∈ comapK D X eL hk W'
  rw [hWW]

variable [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] (n : ℕ) [NeZero n]

set_option maxHeartbeats 1000000 in
-- closure computations in the Krull topology of `Gal(Ω/k(t))` are slow to elaborate
include hk in
/-- **Characters of `π₁ᵉᵗ(X ∖ {x₀})` are unramified at `x₀`**: a continuous character `H → μₙ`
killing `⟨⟨S_U⟩⟩` (`U = X ∖ {x₀}`) kills `⟨⟨S_X⟩⟩`. -/
theorem kernel_SAll_le_of_kernel_SU_le (U : X.Opens) [Nonempty U]
    (hU : (U : Set X)ᶜ.Subsingleton) (φ : ContinuousMonoidHom D.H (Mu n Ω))
    (hφ : GaloisPi1.kernel D.H (SU D X eL U) ≤ φ.toMonoidHom.ker) :
    GaloisPi1.kernel D.H (SAll D) ≤ φ.toMonoidHom.ker := by
  -- `φ` kills the inertia elements of the places centred on `U`
  have hφS : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ SU D X eL U → φ σ = 1 := fun σ hσ ↦
    hφ (Subgroup.mem_subgroupOf.2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_closure
      ⟨1, D.H.one_mem, σ, hσ, by simp⟩)))
  obtain ⟨v, hv⟩ := kummer_surjective n (F D) Ω (classOfH D n φ)
  -- the exceptional places
  let E : Set (Place k (F D)) := {P | ∃ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) ∧
    (∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) ∧ ¬ Cusp.IsCentredOn D X eL U W}
  have hE : E.Subsingleton := by
    rintro P ⟨W, hkW, hWP, hW⟩ P' ⟨W', hkW', hWP', hW'⟩
    refine Place.ext (SetLike.ext' (Set.ext fun x ↦ ?_))
    change x ∈ P.1 ↔ x ∈ P'.1
    rw [← hWP, ← hWP']
    exact eq_of_not_isCentredOn D X eL hk U hU hkW hkW' hW hW' x
  have hdiv : ∀ P : Place k (F D), P ∉ E → (n : ℤ) ∣ P.ord (v : F D) := by
    intro P hPE
    obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver D P
    have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k (F D) Ω]
      exact (hW _).2 (P.algebraMap_mem c)
    have hcent : Cusp.IsCentredOn D X eL U W := by
      by_contra hc
      exact hPE ⟨W, hkW, hW, hc⟩
    refine dvd_ord_of_evalTriv_eq_one D n v P hW fun hk' σ hσ ↦ ?_
    have h1 : charOfH D n (kummer n (F D) Ω v) σ = 1 := by
      rw [hv, charOfH_classOfH]
      exact hφS σ ((Cusp.mem_SU_iff D X eL U _).2 ⟨σ.2, W, hcent, hσ⟩)
    exact h1
  have hunr : IsUnramifiedKummer D n v :=
    (isUnramifiedKummer_iff D n v).2 (dvd_ord_of_subsingleton _ _ E hE hdiv)
  have hle := kernel_le_ker_charOfH D n ⟨kummer n (F D) Ω v, hunr⟩
  intro σ hσ
  have := hle hσ
  rw [MonoidHom.mem_ker] at this ⊢
  change charOfH D n (kummer n (F D) Ω v) σ = 1 at this
  rw [hv, charOfH_classOfH] at this
  exact this

end Curve

/-! ### Counting characters -/

section Count

variable {G G' A B : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  [Group A] [TopologicalSpace A] [DiscreteTopology A] [Group B] [TopologicalSpace B]
  [DiscreteTopology B]

omit [DiscreteTopology A] in
/-- Precomposition with an isomorphism of topological groups. -/
lemma natCard_continuousMonoidHom_congr_left (e : G ≃ₜ* G') :
    Nat.card (ContinuousMonoidHom G A) = Nat.card (ContinuousMonoidHom G' A) :=
  Nat.card_congr
    { toFun := fun ψ ↦ ⟨ψ.toMonoidHom.comp e.symm.toMonoidHom, ψ.continuous.comp e.symm.continuous⟩
      invFun := fun ψ ↦ ⟨ψ.toMonoidHom.comp e.toMonoidHom, ψ.continuous.comp e.continuous⟩
      left_inv := fun ψ ↦ by
        ext g
        change ψ (e.symm (e g)) = ψ g
        rw [e.symm_apply_apply]
      right_inv := fun ψ ↦ by
        ext g
        change ψ (e (e.symm g)) = ψ g
        rw [e.apply_symm_apply] }

/-- Postcomposition with an isomorphism of discrete groups. -/
lemma natCard_continuousMonoidHom_congr_right (e : A ≃* B) :
    Nat.card (ContinuousMonoidHom G A) = Nat.card (ContinuousMonoidHom G B) :=
  Nat.card_congr
    { toFun := fun ψ ↦ ⟨e.toMonoidHom.comp ψ.toMonoidHom,
        (continuous_of_discreteTopology (f := ⇑e)).comp ψ.continuous⟩
      invFun := fun ψ ↦ ⟨e.symm.toMonoidHom.comp ψ.toMonoidHom,
        (continuous_of_discreteTopology (f := ⇑e.symm)).comp ψ.continuous⟩
      left_inv := fun ψ ↦ by
        ext g
        change e.symm (e (ψ g)) = ψ g
        rw [e.symm_apply_apply]
      right_inv := fun ψ ↦ by
        ext g
        change e (e.symm (ψ g)) = ψ g
        rw [e.apply_symm_apply] }

/-- Continuous characters of a profinite completion with values in a finite discrete group are the
characters of the group. -/
lemma natCard_continuousMonoidHom_completion {H P : Type u} [Group H] [Group P] [Finite P]
    [TopologicalSpace P] [DiscreteTopology P] :
    Nat.card (ContinuousMonoidHom (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of H)) P) =
      Nat.card (H →* P) := by
  let η : H →* ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of H) :=
    (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of H)).hom
  have hcont : ∀ f : H →* P, Continuous (liftFinite f) := fun f ↦
    continuous_discrete_rng.2 fun p ↦ isOpen_liftFinite_fiber f p
  refine Nat.card_congr
    { toFun := fun ψ ↦ ψ.toMonoidHom.comp η
      invFun := fun f ↦ ⟨liftFinite f, hcont f⟩
      left_inv := fun ψ ↦ ?_
      right_inv := fun f ↦ ?_ }
  · apply ContinuousMonoidHom.ext
    intro x
    have := (ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of H)).equalizer (hcont _)
      ψ.continuous (funext fun h ↦ liftFinite_eta (ψ.toMonoidHom.comp η) h)
    exact congrFun this x
  · ext h
    exact liftFinite_eta f h

/-- Characters of a free group. -/
lemma natCard_monoidHom_freeGroup {ι P : Type*} [Group P] [Finite ι] :
    Nat.card (FreeGroup ι →* P) = Nat.card P ^ Nat.card ι := by
  rw [Nat.card_congr FreeGroup.lift.symm, Nat.card_fun]

end Count

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

set_option synthInstance.maxHeartbeats 200000 in
-- the group structure on the quotient `PiX D` takes long to synthesize
set_option maxHeartbeats 1000000 in
-- the Galois model of `π₁ᵉᵗ` is slow to elaborate
/-- **`Hom_cont(π₁ᵉᵗ(X), μₙ)` has `n^{2g}` elements** for a curve `X` of genus `g` over `k`
(algebraically closed, characteristic `0`), at every geometric point, for
every discrete group `A ≃ ℤ/n`. -/
theorem card_continuousMonoidHom_etaleFundamentalGroup_proper {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω'] (pt : Spec (CommRingCat.of Ω') ⟶ X) (n : ℕ) [NeZero n]
    {A : Type*} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (eA : A ≃* Multiplicative (ZMod n)) :
    Nat.card (ContinuousMonoidHom π₁ᵉᵗ(pt) A) = n ^ (2 * (curveGenus k X).toNat) := by
  obtain ⟨Ω, _, _, _, t, _, D, eL, τ, hk, hτ, hH⟩ := exists_curveGaloisData (k := k) X
  -- `μₙ(Ω) ≃ ℤ/n`
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := NeZero.charZero
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hcardMu : Nat.card (Mu n Ω) = n := hμ.card_rootsOfUnity
  haveI : IsCyclic (Mu n Ω) := inferInstanceAs (IsCyclic (rootsOfUnity n Ω))
  let eMu : Multiplicative (ZMod n) ≃* Mu n Ω := by
    have e := zmodCyclicMulEquiv (inferInstance : IsCyclic (Mu n Ω))
    rw [hcardMu] at e
    exact e
  rw [natCard_continuousMonoidHom_congr_right (eA.trans eMu)]
  -- the open `U = X ∖ {x₀}`
  obtain ⟨x₀⟩ := nonempty_closedPoint k X
  let U : X.Opens := ⟨{x₀.1}ᶜ, (isClosed_closedPoint k X x₀).isOpen_compl⟩
  have hUc : (U : Set X)ᶜ = {x₀.1} := compl_compl _
  haveI : Nonempty U := ⟨⟨genericPoint X, fun h ↦ x₀.2 h.symm⟩⟩
  have hUfin : (U : Set X)ᶜ.Finite := hUc ▸ Set.finite_singleton _
  have hUne : (U : Set X)ᶜ.Nonempty := hUc ▸ Set.singleton_nonempty _
  have hUsub : (U : Set X)ᶜ.Subsingleton := hUc ▸ Set.subsingleton_singleton
  have hU1 : Nat.card ((U : Set X)ᶜ : Set X) = 1 := by rw [hUc, Nat.card_unique]
  haveI : CompactSpace D.H := isCompact_iff_compactSpace.1 D.isClosed_H.isCompact
  -- `π₁ᵉᵗ(X)` in the Galois model
  obtain ⟨e₁⟩ := FiniteEtale.nonempty_fundamentalGroup_continuousMulEquiv pt
    (geometricGenericPoint D X eL)
  rw [natCard_continuousMonoidHom_congr_left e₁]
  let eX := etalePi1EquivPiX' D X eL hk hτ hH
  let pX : D.H →* π₁ᵉᵗ(geometricGenericPoint D X eL) :=
    eX.symm.toMonoidHom.comp (QuotientGroup.mk' (GaloisPi1.kernel D.H (SAll D)))
  have hpX : Continuous pX := eX.symm.continuous.comp QuotientGroup.continuous_mk
  have hpXs : Function.Surjective pX :=
    eX.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hpXk : pX.ker = GaloisPi1.kernel D.H (SAll D) := by
    ext σ
    rw [MonoidHom.mem_ker]
    change eX.symm (QuotientGroup.mk σ) = 1 ↔ _
    rw [map_eq_one_iff _ eX.symm.injective, QuotientGroup.eq_one_iff]
  rw [natCard_continuousMonoidHom_of_surjective pX hpX hpXs, hpXk]
  -- `π₁ᵉᵗ(U)` in the Galois model
  obtain ⟨hkerU, hsurjU⟩ := genericL_spec D X eL hk hH hτ U hUfin
  have hU := natCard_continuousMonoidHom_of_surjective (A := Mu n Ω)
    (D.chartHom hH (genericL D X eL U)) (D.continuous_chartHom hH _) hsurjU
  rw [hkerU] at hU
  -- the two sets of characters agree
  have hsets : Nat.card {φ : ContinuousMonoidHom D.H (Mu n Ω) //
      GaloisPi1.kernel D.H (SAll D) ≤ φ.toMonoidHom.ker} =
      Nat.card {φ : ContinuousMonoidHom D.H (Mu n Ω) //
        GaloisPi1.kernel D.H (SU D X eL U) ≤ φ.toMonoidHom.ker} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩)
    · refine le_trans (fun σ hσ ↦ ?_) h
      have hSU : SU D X eL U ⊆ SAll D := fun σ hσ ↦ by
        obtain ⟨hσH, W, hW, hσW⟩ := (Cusp.mem_SU_iff D X eL U σ).1 hσ
        exact ⟨hσH, W, hW.1, hσW⟩
      exact GaloisPi1.kernel_le_comap le_rfl hSU hσ
    · exact kernel_SAll_le_of_kernel_SU_le D X eL hk n U hUsub φ h
  rw [hsets, ← hU]
  -- `π₁ᵉᵗ(U) ≃ Π̂_{g,1}`
  obtain ⟨e₂⟩ := etaleFundamentalGroup_equiv_profiniteSurfaceGroup (k := k) U hUfin hUne
    (specPoint D.L Ω ≫ genericL D X eL U)
  rw [natCard_continuousMonoidHom_congr_left e₂, natCard_continuousMonoidHom_completion]
  set g := (curveGenus k X).toNat
  have eF : ULift.{u} (Pi1.SurfaceGroup g (Nat.card ((U : Set X)ᶜ : Set X))) ≃*
      FreeGroup (Pi1.SurfaceGen g 0) := by
    rw [hU1]
    exact MulEquiv.ulift.trans Pi1.SurfaceGroup.freeEquiv
  haveI : Finite (Pi1.SurfaceGen g 0) := Finite.of_equiv _ (surfaceGenEquiv g 0).symm
  rw [Nat.card_congr (MulEquiv.monoidHomCongrLeftEquiv eF), natCard_monoidHom_freeGroup, hcardMu,
    natCard_surfaceGen, add_zero]

/-- **`Hom_cont(π₁ᵉᵗ(X), ℤ/n) ≅ (ℤ/n)^{2g}`** (cardinality form) for a proper curve `X` of genus `g`
over `k` (algebraically closed, characteristic `0`), at every geometric
point. -/
theorem card_continuousMonoidHom_zmod_etaleFundamentalGroup_proper {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω'] (pt : Spec (CommRingCat.of Ω') ⟶ X) (n : ℕ) [NeZero n] :
    Nat.card (ContinuousMonoidHom π₁ᵉᵗ(pt) (Multiplicative (ZMod n))) =
      n ^ (2 * (curveGenus k X).toNat) :=
  card_continuousMonoidHom_etaleFundamentalGroup_proper pt n (MulEquiv.refl _)

end Main

end CurvesJacobian
