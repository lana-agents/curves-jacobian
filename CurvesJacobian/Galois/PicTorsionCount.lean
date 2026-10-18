/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.AbelianPi1

/-!
# `#Pic(X)[n] = n^{2g}` over `ℚ̄`

* `CurvesJacobian.placeEquivOfAlgEquiv`, `CurvesJacobian.ord_placeEquivOfAlgEquiv`,
  `CurvesJacobian.picTorsionEquivOfAlgEquiv`: places, orders, divisor class groups and their
  `n`-torsion are invariant under `k`-isomorphisms of function fields.
* `CurvesJacobian.natCard_picTorsion`: for a curve `X` of genus `g` over `k` (algebraically
  closed, characteristic `0`, algebraic over `ℚ`) and `n ≥ 1`, `#Pic(K(X))[n] = n^{2g}`.

Proof: `Pic(F)[n] ≃ Hom_cont(Π_X, μₙ)` (`CurvesJacobian.picTorsionEquivPiChars`, Kummer theory),
`Π_X ≃ π₁ᵉᵗ(X)` (`CurvesJacobian.etalePi1EquivPiX'`) and
`#Hom_cont(π₁ᵉᵗ(X), μₙ) = n^{2g}`
(`CurvesJacobian.card_continuousMonoidHom_etaleFundamentalGroup_proper`, from
`π₁ᵉᵗ(X ∖ {x₀}) ≃ₜ* Π̂_{g,1}`).
-/

open CategoryTheory AlgebraicGeometry Belyi Pi1.Orbifold AffOrbicurve KummerTheory Curve
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian

section Transport

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  (e : K ≃ₐ[k] K')

/-- The place of `K'` corresponding to a place of `K` under `e : K ≃ₐ[k] K'`. -/
def placeMap (P : Place k K) : Place k K' :=
  ⟨P.1.comap e.symm.toRingHom, fun h ↦ P.ne_top (eq_top_iff.2 fun x _ ↦ by
      have : e x ∈ P.1.comap e.symm.toRingHom := h ▸ ValuationSubring.mem_top _
      simpa using this),
    fun c ↦ by
      change e.symm (algebraMap k K' c) ∈ P.1
      rw [AlgEquiv.commutes]
      exact P.algebraMap_mem c⟩

lemma mem_placeMap (P : Place k K) (y : K') : y ∈ (placeMap e P).1 ↔ e.symm y ∈ P.1 := Iff.rfl

lemma mem_placeMap_apply (P : Place k K) (x : K) : e x ∈ (placeMap e P).1 ↔ x ∈ P.1 := by
  rw [mem_placeMap, AlgEquiv.symm_apply_apply]

/-- Places of isomorphic function fields. -/
def placeEquivOfAlgEquiv : Place k K ≃ Place k K' where
  toFun := placeMap e
  invFun := placeMap e.symm
  left_inv P := Place.ext (by ext x; simp [mem_placeMap])
  right_inv Q := Place.ext (by ext x; simp [mem_placeMap])

/-- Divisors of isomorphic function fields. -/
def divisorEquivOfAlgEquiv : Divisor k K ≃+ Divisor k K' :=
  Finsupp.domCongr (placeEquivOfAlgEquiv e)

variable [PerfectField k] [IsFunctionField k K] [IsFunctionField k K']

/-- Units at `P` map to units at `placeMap e P`. -/
lemma ord_placeMap_of_ord_eq_zero (P : Place k K) {u : K} (hu : u ≠ 0) (h : P.ord u = 0) :
    (placeMap e P).ord (e u) = 0 := by
  obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff hu).1 h
  refine ((placeMap e P).ord_eq_zero_iff (by simpa using hu)).2
    ⟨(mem_placeMap_apply e P u).2 h1, ?_⟩
  rw [← map_inv₀]
  exact (mem_placeMap_apply e P _).2 h2

/-- Every nonzero `f` is `π^{ord f} · u` with `u` a unit. -/
lemma eq_zpow_mul_unit (P : Place k K) {π : K} (hπ : P.ord π = 1) {f : K} (hf : f ≠ 0) :
    ∃ u : K, u ≠ 0 ∧ P.ord u = 0 ∧ f = π ^ P.ord f * u := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  refine ⟨f * π ^ (-P.ord f), mul_ne_zero hf (zpow_ne_zero _ hπ0), ?_, ?_⟩
  · rw [P.ord_mul hf (zpow_ne_zero _ hπ0), P.ord_zpow, hπ]
    ring
  · rw [mul_comm f, ← mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, one_mul]

lemma ord_pos_of_mem_of_inv_notMem (P : Place k K) {x : K} (hx : x ≠ 0) (h1 : x ∈ P.1)
    (h2 : x⁻¹ ∉ P.1) : 0 < P.ord x := by
  have h0 := P.ord_nonneg_of_mem h1
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd ((P.ord_eq_zero_iff hx).1 h.symm).2 h2

/-- Uniformisers map to uniformisers. -/
lemma ord_placeMap_uniformizer (P : Place k K) {π : K} (hπ : P.ord π = 1) :
    (placeMap e P).ord (e π) = 1 := by
  set P' := placeMap e P
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have hπmem : π ∈ P.1 := P.mem_of_ord_nonneg (by rw [hπ]; norm_num)
  have hπinv : π⁻¹ ∉ P.1 := fun h ↦ by
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, hπ] at this
    norm_num at this
  have heπ0 : e π ≠ 0 := by simpa using hπ0
  have ha : 0 < P'.ord (e π) := ord_pos_of_mem_of_inv_notMem P' heπ0
    ((mem_placeMap_apply e P π).2 hπmem)
    (by rw [← map_inv₀, mem_placeMap_apply]; exact hπinv)
  obtain ⟨π', hπ'⟩ := P'.exists_ord_eq_one
  have hπ'0 : π' ≠ 0 := by rintro rfl; simp at hπ'
  set y := e.symm π'
  have hy0 : y ≠ 0 := by simpa [y] using hπ'0
  have hymem : y ∈ P.1 := (mem_placeMap e P π').1 (P'.mem_of_ord_nonneg (by rw [hπ']; norm_num))
  have hyinv : y⁻¹ ∉ P.1 := fun h ↦ by
    have h' : π'⁻¹ ∈ P'.1 := by
      rw [mem_placeMap, map_inv₀]
      exact h
    have := P'.ord_nonneg_of_mem h'
    rw [P'.ord_inv, hπ'] at this
    norm_num at this
  have hb : 0 < P.ord y := ord_pos_of_mem_of_inv_notMem P hy0 hymem hyinv
  obtain ⟨w, hw0, hw, hyw⟩ := eq_zpow_mul_unit P hπ hy0
  have hπ'eq : π' = e π ^ P.ord y * e w := by
    have h' : π' = e (π ^ P.ord y * w) := by rw [← hyw]; simp [y]
    rw [h', map_mul, map_zpow₀]
  have h1 : P'.ord π' = P.ord y * P'.ord (e π) := by
    rw [hπ'eq, P'.ord_mul (zpow_ne_zero _ heπ0) (by simpa using hw0), P'.ord_zpow,
      ord_placeMap_of_ord_eq_zero e P hw0 hw, add_zero]
  rw [hπ'] at h1
  nlinarith

/-- **Orders are invariant**: `ord_{e P}(e f) = ord_P f`. -/
theorem ord_placeMap (P : Place k K) (f : K) : (placeMap e P).ord (e f) = P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  obtain ⟨u, hu0, hu, hfu⟩ := eq_zpow_mul_unit P hπ hf
  conv_lhs => rw [hfu, map_mul, map_zpow₀]
  rw [(placeMap e P).ord_mul (zpow_ne_zero _ (by simpa using hπ0)) (by simpa using hu0),
    (placeMap e P).ord_zpow, ord_placeMap_uniformizer e P hπ,
    ord_placeMap_of_ord_eq_zero e P hu0 hu]
  ring

lemma div_algEquiv (f : K) :
    Divisor.div k (e f) = divisorEquivOfAlgEquiv e (Divisor.div k f) := by
  ext Q
  change Q.ord (e f) = Divisor.div k f ((placeEquivOfAlgEquiv e).symm Q)
  rw [Divisor.div_apply]
  conv_lhs => rw [← (placeEquivOfAlgEquiv e).apply_symm_apply Q]
  exact ord_placeMap e _ f

lemma map_principal :
    (principal k K).map (divisorEquivOfAlgEquiv e).toAddMonoidHom = principal k K' := by
  ext D'
  simp only [AddSubgroup.mem_map, mem_principal]
  constructor
  · rintro ⟨D, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨e f, by simpa using hf, div_algEquiv e f⟩
  · rintro ⟨f', hf', rfl⟩
    refine ⟨Divisor.div k (e.symm f'), ⟨_, by simpa using hf', rfl⟩, ?_⟩
    change divisorEquivOfAlgEquiv e _ = _
    rw [← div_algEquiv, AlgEquiv.apply_symm_apply]

/-- Divisor class groups of isomorphic function fields. -/
def picEquivOfAlgEquiv : Pic k K ≃+ Pic k K' :=
  QuotientAddGroup.congr _ _ (divisorEquivOfAlgEquiv e) (map_principal e)

include e in
/-- **`#Pic(K)[n] = #Pic(K')[n]`** for `k`-isomorphic function fields. -/
theorem natCard_picTorsion_eq (n : ℕ) :
    Nat.card (picTorsion k K n) = Nat.card (picTorsion k K' n) := by
  refine Nat.card_congr ((picEquivOfAlgEquiv e).toEquiv.subtypeEquiv fun x ↦ ?_)
  change n • x = 0 ↔ n • (picEquivOfAlgEquiv e) x = 0
  rw [← map_nsmul, AddEquiv.map_eq_zero_iff]

end Transport

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] [IsIntegral X]

attribute [local instance] isFunctionField_F

set_option synthInstance.maxHeartbeats 200000 in
-- the group structure on the quotient `PiX D` takes long to synthesize
/-- **`#Pic(X)[n] = n^{2g}`** for a curve `X` of genus `g` over `k` (algebraically closed,
characteristic `0`, algebraic over `ℚ`) and `n ≥ 1`; `Pic(X) = Pic(K(X))` is weil-curves'
divisor class group of the function field (all places have degree `1`, so this is `Pic⁰[n]`). -/
theorem natCard_picTorsion (n : ℕ) [NeZero n] :
    Nat.card (picTorsion k X.functionField n) = n ^ (2 * (curveGenus k X).toNat) := by
  obtain ⟨Ω, _, _, _, t, _, D, eL, τ, hk, hτ, hH⟩ := exists_curveGaloisData (k := k) X
  -- `K(X) ≃ F`
  have hHL : D.H = D.HL := le_antisymm hH D.le
  have hLF : D.L = F D := by rw [GaloisData.L, F, hHL]
  let eF : X.functionField ≃ₐ[k] F D :=
    { eL.trans (IntermediateField.equivOfEq hLF).toRingEquiv with
      commutes' := fun c ↦ Subtype.ext (by
        change ((eL (algebraMap k X.functionField c) : D.L) : Ω) = _
        rw [hk]
        rfl) }
  rw [natCard_picTorsion_eq eF n,
    Nat.card_congr (picTorsionEquivPiChars D n (Nat.pos_of_ne_zero (NeZero.ne n))).toEquiv,
    Nat.card_congr Additive.toMul]
  -- `Hom_cont(Π_X, μₙ)`
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := NeZero.charZero
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hcardMu : Nat.card (Mu n Ω) = n := hμ.card_rootsOfUnity
  haveI : IsCyclic (Mu n Ω) := inferInstanceAs (IsCyclic (rootsOfUnity n Ω))
  let eMu : Multiplicative (ZMod n) ≃* Mu n Ω := by
    have e := zmodCyclicMulEquiv (inferInstance : IsCyclic (Mu n Ω))
    rw [hcardMu] at e
    exact e
  rw [← natCard_continuousMonoidHom_congr_left (etalePi1EquivPiX' D X eL hk hτ hH)]
  exact card_continuousMonoidHom_etaleFundamentalGroup_proper _ n eMu.symm

end Main

end CurvesJacobian
