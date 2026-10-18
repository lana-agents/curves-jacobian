/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.InertiaEtale
import CurvesJacobian.Galois.CountableSubfield
import CurvesJacobian.Cusp.PlaceTransitivity

/-!
# Unramifiedness descends along constant field extensions

Let `k` be a field of characteristic `0`, `t ∈ Ω` transcendental over `k` with `Ω / k(t)` Galois,
and `W` a valuation subring of `Ω` with `k ⊆ W` and `v_W(t) < 1`. For a finite extension
`N / k(t)` inside `Ω`, the inertia group `I_W` fixes `N` if and only if the uniformizer `t` of
`k[t]` at `t = 0` is not in the square of the centre `u_W(N)` of `W` on the normalization
`coordRing k t N` of `k[t]` in `N` (`CurvesJacobian.Cusp.inertia_le_fixingSubgroup_iff`): both
say that `u_W(N)` is unramified over `k[t]` (pi1's `AffOrbicurve.ramificationIdx_eq_one_iff` in
a Galois closure, plus surjectivity of inertia).

The second condition is visibly stable under constant field extension: for `k₀ ⊆ k`,
`ι : Ω₀ → Ω` and `t = ι t₀`, the inclusion `ι` maps `coordRing k₀ t₀ N₀` into `coordRing k t N`
(`N₀ = k₀(t₀)(z)`, `N = k(t)(ι z)`) and `u_{W₀}(N₀)` into `u_W(N)` (`W₀ = ι⁻¹ W`). Hence
(`CurvesJacobian.Cusp.inertia_fix_descent`): **if `I_W` fixes `ι z`, then `I_{W₀}` fixes `z`.**

Finally, for `k₀ → k` and `Ω` separably closed of characteristic `0`, the relative algebraic
closure `Ω₀ = CurvesJacobian.Cusp.lineAlgClosure k₀ t` of `k₀(t)` in `Ω` provides such an `Ω₀`
(algebraically closed, Galois over `k₀(t₀)`), with `t₀ = CurvesJacobian.Cusp.lineAlgGen k₀ t` and
`ι = CurvesJacobian.Cusp.lineIncl k₀ t`; `CurvesJacobian.Cusp.inertia_fix_descent_lineAlgClosure`
is the descent statement in this situation.
-/

open AffOrbicurve IntermediateField Polynomial IntermediateField.algebraAdjoinAdjoin

universe u

namespace CurvesJacobian.Cusp

section Valuation

variable {K L : Type*} [Field K] [Field L]

/-- `v_A(x) < 1` iff `x ∈ A` and `x` is zero or not a unit of `A`. -/
lemma valuationSubring_valuation_lt_one_iff (A : ValuationSubring K) (x : K) :
    A.valuation x < 1 ↔ x ∈ A ∧ (x = 0 ∨ x⁻¹ ∉ A) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [A.zero_mem]
  · rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ ((Valuation.pos_iff _).2 hx)]
    simp only [hx, false_or, not_le]
    exact ⟨fun h ↦ ⟨h.le, h⟩, fun h ↦ h.2⟩

end Valuation

section Criterion

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- The coordinate `t` lies in the centre `u_W(N)` when `v_W(t) < 1`. -/
lemma coordRingMap_X_mem_centerIdeal (ht : Transcendental k t) {W : ValuationSubring Ω}
    (hW : IsCentered k t W) (hWt : W.valuation t < 1) (N : IntermediateField (K₀ k t) Ω) :
    coordRingMap ht N X ∈ centerIdeal hW N :=
  (mem_centerIdeal hW).2 (by rw [toΩ_apply, coordRingMap_apply, aeval_X]; exact hWt)

/-- The centre `u_W(N)` is nonzero when `v_W(t) < 1`. -/
lemma centerIdeal_ne_bot_of_lt_one (ht : Transcendental k t) {W : ValuationSubring Ω}
    (hW : IsCentered k t W) (hWt : W.valuation t < 1) (N : IntermediateField (K₀ k t) Ω) :
    centerIdeal hW N ≠ ⊥ := by
  intro h
  have hmem := coordRingMap_X_mem_centerIdeal ht hW hWt N
  rw [h, Ideal.mem_bot] at hmem
  have h0 := coordRingMap_apply ht N X
  rw [hmem, aeval_X] at h0
  exact (fun h ↦ ht (h ▸ isAlgebraic_zero) : t ≠ 0) (by simpa using h0.symm)

set_option maxHeartbeats 1000000 in
-- the algebra structure `algRing` makes instance search and unification slow
set_option synthInstance.maxHeartbeats 400000 in
/-- **Unramified iff the uniformizer is not in the square**: the ramification index of `u_W(N)`
over `k[t]` is `1` iff `t ∉ u_W(N)²` (the prime of `k[t]` below `u_W(N)` is `(t)`). -/
lemma ramificationIdx_centerIdeal_eq_one_iff (ht : Transcendental k t)
    {W : ValuationSubring Ω} (hW : IsCentered k t W) (hWt : W.valuation t < 1)
    (N : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) N]
    [Algebra.IsSeparable (K₀ k t) N] :
    (letI := algRing t (bot_le : (⊥ : IntermediateField (K₀ k t) Ω) ≤ N);
      (centerIdeal hW N).ramificationIdx (coordRing k t ⊥)) = 1 ↔
      coordRingMap ht N X ∉ centerIdeal hW N ^ 2 := by
  have hbot : (⊥ : IntermediateField (K₀ k t) Ω) ≤ N := bot_le
  letI iR := algRing t hbot
  haveI := isDedekindDomain_ring t ht N
  haveI := isDedekindDomain_ring t ht (⊥ : IntermediateField (K₀ k t) Ω)
  haveI : Module.IsTorsionFree (coordRing k t ⊥) (coordRing k t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t hbot
  set P := centerIdeal hW N
  let X' := coordRingBotEquiv (Ω := Ω) ht X
  have hX : algebraMap (coordRing k t ⊥) (coordRing k t N) X' = coordRingMap ht N X := rfl
  let p := P.under (coordRing k t ⊥)
  have hXp : X' ∈ p := by
    change algebraMap (coordRing k t ⊥) (coordRing k t N) X' ∈ P
    rw [hX]; exact coordRingMap_X_mem_centerIdeal ht hW hWt N
  have hmax : (Ideal.span {X'}).IsMaximal := by
    haveI : (Ideal.span {(X : k[X])}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
    have := Ideal.map_isMaximal_of_equiv (coordRingBotEquiv (Ω := Ω) ht)
      (p := Ideal.span {(X : k[X])})
    rwa [Ideal.map_span, Set.image_singleton] at this
  have hp : p = Ideal.span {X'} :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).2 hXp)).symm
  have hp0 : p ≠ ⊥ := by
    rw [hp, Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (coordRingBotEquiv (Ω := Ω) ht).injective).2 X_ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx p P hp0, ← not_iff_not, not_not, ← ne_eq,
    Ideal.ramificationIdx'_ne_one_iff (p := p) (P := P) (Ideal.map_le_iff_le_comap.2 le_rfl), hp,
    Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_le_iff_mem, hX]

variable [CharZero k]

set_option maxHeartbeats 1000000 in
-- the algebra structure `algRing` makes instance search and unification slow
set_option synthInstance.maxHeartbeats 400000 in
/-- **Inertia fixes `N` iff `t ∉ u_W(N)²`.** For `W` centred on the `t`-line with `v_W(t) < 1`
and `N / k(t)` finite, the inertia group `I_W` fixes `N` if and only if the coordinate `t` is
not in the square of the centre `u_W(N)` of `W` on `coordRing k t N`. -/
theorem inertia_le_fixingSubgroup_iff [IsGalois (K₀ k t) Ω] (ht : Transcendental k t)
    {W : ValuationSubring Ω} (hW : IsCentered k t W) (hWt : W.valuation t < 1)
    (N : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) N] :
    (∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, σ ∈ N.fixingSubgroup) ↔
      coordRingMap ht N X ∉ centerIdeal hW N ^ 2 := by
  haveI := isSeparable_of_charZero N
  rw [← ramificationIdx_centerIdeal_eq_one_iff ht hW hWt N]
  let M := normalClosure (K₀ k t) N Ω
  haveI : FiniteDimensional (K₀ k t) M := normalClosure.is_finiteDimensional _ _ _
  haveI : IsGalois (K₀ k t) M := IsGalois.normalClosure _ _ _
  haveI := isSeparable_of_charZero M
  have hNM : N ≤ M := IntermediateField.le_normalClosure N
  have hneM : centerIdeal hW M ≠ ⊥ := centerIdeal_ne_bot_of_lt_one ht hW hWt M
  haveI := isMaximal_centerIdeal ht hW M hneM
  have hbot : (⊥ : IntermediateField (K₀ k t) Ω) ≤ N := bot_le
  have key := ramificationIdx_eq_one_iff t ht hbot hNM (centerIdeal hW M)
  rw [comap_centerIdeal hW hNM] at key
  rw [key]
  constructor
  · intro hfix τ hτ
    obtain ⟨σ, hσ, -, rfl⟩ :=
      exists_mem_inertia_fixingSubgroup_restrictNormal_eq ht hW (bot_le.trans hNM) hneM τ hτ
    exact restrictNormal_mem_fixSub M (hfix σ hσ)
  · intro hle σ hσ
    have hτ := hle ⟨restrictNormal_mem_inertia hW M hσ, by rw [fixSub_bot]; trivial⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have := congrArg (fun y : M ↦ (y : Ω)) (hτ ⟨x, hNM hx⟩ hx)
    simpa using this

end Criterion

section Descent

variable {k₀ k Ω₀ Ω : Type u} [Field k₀] [Field k] [CharZero k] [Algebra k₀ k]
  [Field Ω₀] [Field Ω] [Algebra k₀ Ω₀] [Algebra k Ω] [Algebra k₀ Ω] [IsScalarTower k₀ k Ω]

set_option maxHeartbeats 1000000 in
-- instances on the coordinate rings and their ideals are slow to synthesize
set_option synthInstance.maxHeartbeats 400000 in
omit [CharZero k] in
/-- **Transfer of `t ∉ u_W(N)²` along `ι`.** If `ι` maps `N₀` into `N`, `t₀` to `t` and the
maximal ideal of `W₀` into that of `W`, then `t ∉ u_W(N)²` implies `t₀ ∉ u_{W₀}(N₀)²`. -/
lemma notMem_sq_of_map (ι : Ω₀ →ₐ[k₀] Ω) {t₀ : Ω₀} (ht₀ : Transcendental k₀ t₀)
    (ht : Transcendental k (ι t₀)) {W₀ : ValuationSubring Ω₀} {W : ValuationSubring Ω}
    (hW₀ : IsCentered k₀ t₀ W₀) (hW : IsCentered k (ι t₀) W)
    (hWW : ∀ x, W₀.valuation x < 1 → W.valuation (ι x) < 1)
    {N₀ : IntermediateField (K₀ k₀ t₀) Ω₀} {N : IntermediateField (K₀ k (ι t₀)) Ω}
    (hN : ∀ x ∈ N₀, ι x ∈ N) (hP : coordRingMap ht N X ∉ centerIdeal hW N ^ 2) :
    coordRingMap ht₀ N₀ X ∉ centerIdeal hW₀ N₀ ^ 2 := by
  have hA : ∀ x : A₀ k₀ t₀, ι x ∈ A₀ k (ι t₀) := by
    have : A₀ k₀ t₀ ≤ ((A₀ k (ι t₀)).restrictScalars k₀).comap ι :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 (Algebra.self_mem_adjoin_singleton k _))
    exact fun x ↦ this x.2
  let χ : A₀ k₀ t₀ →+* A₀ k (ι t₀) :=
    (ι.toRingHom.comp (A₀ k₀ t₀).val.toRingHom).codRestrict (A₀ k (ι t₀)) hA
  let ψ : N₀ →+* N := (ι.toRingHom.comp N₀.val.toRingHom).codRestrict N fun x ↦ hN x x.2
  have hcomp : (algebraMap (A₀ k (ι t₀)) N).comp χ = ψ.comp (algebraMap (A₀ k₀ t₀) N₀) :=
    RingHom.ext fun _ ↦ rfl
  let φ : coordRing k₀ t₀ N₀ →+* coordRing k (ι t₀) N :=
    (ψ.comp (coordRing k₀ t₀ N₀).val.toRingHom).codRestrict (coordRing k (ι t₀) N) fun a ↦
      (mem_integralClosure_iff _ _).2 (IsIntegral.map_of_comp_eq χ ψ hcomp
        ((mem_integralClosure_iff _ _).1 a.2))
  have hφ : ∀ a, toΩ (ι t₀) N (φ a) = ι (toΩ t₀ N₀ a) := fun _ ↦ rfl
  have hφX : φ (coordRingMap ht₀ N₀ X) = coordRingMap ht N X := by
    apply toΩ_injective N
    rw [hφ, toΩ_apply, toΩ_apply, coordRingMap_apply, coordRingMap_apply, aeval_X, aeval_X]
  have hPP : centerIdeal hW₀ N₀ ≤ (centerIdeal hW N).comap φ := fun a ha ↦ by
    rw [Ideal.mem_comap, mem_centerIdeal, hφ]
    exact hWW _ ((mem_centerIdeal hW₀).1 ha)
  intro h
  apply hP
  rw [← hφX]
  have h1 := Ideal.mem_map_of_mem φ h
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPP) 2 h1

set_option maxHeartbeats 1000000 in
-- instances on the coordinate rings and their ideals are slow to synthesize
set_option synthInstance.maxHeartbeats 400000 in
/-- **Unramifiedness descends along constant field extensions.** Let `k₀ → k` (characteristic
`0`), `ι : Ω₀ → Ω` over `k₀`, `t₀ ∈ Ω₀` with `ι t₀` transcendental over `k`, `Ω₀ / k₀(t₀)` and
`Ω / k(ι t₀)` Galois, and `W` a valuation subring of `Ω` with `k ⊆ W` and `v_W(ι t₀) < 1`. If the
inertia group of `W` fixes `ι z`, then the inertia group of `W₀ = ι⁻¹ W` fixes `z`. -/
theorem inertia_fix_descent (ι : Ω₀ →ₐ[k₀] Ω) {t₀ : Ω₀} [IsGalois (K₀ k₀ t₀) Ω₀]
    [IsGalois (K₀ k (ι t₀)) Ω] (ht : Transcendental k (ι t₀)) {W : ValuationSubring Ω}
    (hWk : ∀ c : k, algebraMap k Ω c ∈ W) (hWt : W.valuation (ι t₀) < 1) (z : Ω₀)
    (hz : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k (ι t₀)) W, σ (ι z) = ι z) :
    ∀ σ₀ ∈ GaloisPi1.inertia (P := K₀ k₀ t₀) (W.comap (ι : Ω₀ →+* Ω)), σ₀ z = z := by
  haveI : CharZero k₀ := RingHom.charZero (algebraMap k₀ k)
  have ht₀ : Transcendental k₀ t₀ := fun h ↦ ht ((h.algHom ι).tower_top k)
  have hW : IsCentered k (ι t₀) W := ⟨hWk, (W.valuation_le_one_iff _).1 hWt.le⟩
  have hW₀ : IsCentered k₀ t₀ (W.comap (ι : Ω₀ →+* Ω)) := by
    refine ⟨fun c ↦ ?_, ?_⟩
    · rw [ValuationSubring.mem_comap]
      change ι (algebraMap k₀ Ω₀ c) ∈ W
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k₀ k Ω]
      exact hWk _
    · exact ValuationSubring.mem_comap.2 hW.2
  have hWt₀ : (W.comap (ι : Ω₀ →+* Ω)).valuation t₀ < 1 :=
    (valuation_comap_lt_one_iff W _ t₀).2 hWt
  let N := IntermediateField.adjoin (K₀ k (ι t₀)) {ι z}
  let N₀ := IntermediateField.adjoin (K₀ k₀ t₀) {z}
  haveI : FiniteDimensional (K₀ k (ι t₀)) N :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  haveI : FiniteDimensional (K₀ k₀ t₀) N₀ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  -- over `k`: `I_W` fixes `N`, so `t ∉ u_W(N)²`
  have hfix : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k (ι t₀)) W, σ ∈ N.fixingSubgroup := by
    intro σ hσ
    have hle : N ≤ fixedField (MulAction.stabilizer (Ω ≃ₐ[K₀ k (ι t₀)] Ω) (ι z)) :=
      adjoin_simple_le_iff.2 fun τ ↦ τ.2
    exact (IntermediateField.le_iff_le _ _).1 hle (MulAction.mem_stabilizer_iff.2 (hz σ hσ))
  have hP := (inertia_le_fixingSubgroup_iff ht hW hWt N).1 hfix
  -- `ι` maps `k₀(t₀)` into `k(ι t₀)`, `N₀` into `N` and `k₀[t₀]` into `k[ι t₀]`
  have hK : ∀ x ∈ K₀ k₀ t₀, ι x ∈ K₀ k (ι t₀) := by
    have : K₀ k₀ t₀ ≤ ((K₀ k (ι t₀)).restrictScalars k₀).comap ι :=
      adjoin_simple_le_iff.2 (mem_adjoin_simple_self k (ι t₀))
    exact fun x hx ↦ this hx
  have hN : ∀ x ∈ N₀, ι x ∈ N := by
    let S : IntermediateField (K₀ k₀ t₀) Ω₀ :=
      (N.toSubfield.comap (ι : Ω₀ →+* Ω)).toIntermediateField fun c ↦
        N.algebraMap_mem ⟨ι c, hK c c.2⟩
    have : N₀ ≤ S := adjoin_simple_le_iff.2 (mem_adjoin_simple_self (K₀ k (ι t₀)) (ι z))
    exact fun x hx ↦ this hx
  have hP₀ := notMem_sq_of_map ι ht₀ ht hW₀ hW (fun x ↦ (valuation_comap_lt_one_iff W _ x).1)
    hN hP
  have hfix₀ := (inertia_le_fixingSubgroup_iff ht₀ hW₀ hWt₀ N₀).2 hP₀
  intro σ₀ hσ₀
  exact (mem_fixingSubgroup_iff _ _).1 (hfix₀ σ₀ hσ₀) z (mem_adjoin_simple_self _ z)

end Descent

section Construction

variable {k₀ Ω : Type u} [Field k₀] [Field Ω] [Algebra k₀ Ω]

variable (k₀) in
/-- **The algebraic closure of the `t`-line**: the relative algebraic closure
`Ω₀ = {x ∈ Ω | x algebraic over k₀(t)}` of `k₀(t)` in `Ω`. -/
abbrev lineAlgClosure (t : Ω) : IntermediateField (K₀ k₀ t) Ω := algebraicClosure (K₀ k₀ t) Ω

variable (k₀) in
/-- The coordinate `t₀ = t ∈ Ω₀`. -/
def lineAlgGen (t : Ω) : lineAlgClosure k₀ t :=
  ⟨t, (lineAlgClosure k₀ t).algebraMap_mem ⟨t, mem_adjoin_simple_self k₀ t⟩⟩

variable (k₀) in
/-- The inclusion `ι : Ω₀ → Ω` over `k₀`. -/
def lineIncl (t : Ω) : lineAlgClosure k₀ t →ₐ[k₀] Ω :=
  { (lineAlgClosure k₀ t).val.toRingHom with commutes' := fun _ ↦ rfl }

@[simp] lemma lineIncl_apply (t : Ω) (x : lineAlgClosure k₀ t) :
    lineIncl k₀ t x = (x : Ω) := rfl

@[simp] lemma lineIncl_lineGen (t : Ω) : lineIncl k₀ t (lineAlgGen k₀ t) = t := rfl

instance [CharZero k₀] [IsSepClosed Ω] (t : Ω) : IsAlgClosed (lineAlgClosure k₀ t) :=
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k₀ Ω).injective
  isAlgClosed_algebraicClosure _ _

lemma isAlgebraic_lineAlgClosure (t : Ω) :
    Algebra.IsAlgebraic (K₀ k₀ (lineAlgGen k₀ t)) (lineAlgClosure k₀ t) := by
  have hmap : (K₀ k₀ (lineAlgGen k₀ t)).map (lineIncl k₀ t) = K₀ k₀ t := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, lineIncl_lineGen]
  let e : K₀ k₀ (lineAlgGen k₀ t) ≃ₐ[k₀] K₀ k₀ t :=
    (IntermediateField.equivMap _ (lineIncl k₀ t)).trans (IntermediateField.equivOfEq hmap)
  refine ⟨fun x ↦ IsAlgebraic.of_ringHom_of_comp_eq (e : K₀ k₀ (lineAlgGen k₀ t) →+* K₀ k₀ t)
    ((lineIncl k₀ t : lineAlgClosure k₀ t →+* Ω)) ?_ e.surjective (lineIncl k₀ t).injective
    (RingHom.ext fun _ ↦ rfl)⟩
  exact mem_algebraicClosure_iff.1 x.2

set_option synthInstance.maxHeartbeats 400000 in
-- `Module.IsTorsionFree` for the intermediate field types is slow to synthesize
instance [CharZero k₀] [IsSepClosed Ω] (t : Ω) :
    IsGalois (K₀ k₀ (lineAlgGen k₀ t)) (lineAlgClosure k₀ t) := by
  haveI := isAlgebraic_lineAlgClosure (k₀ := k₀) t
  haveI : CharZero (K₀ k₀ (lineAlgGen k₀ t)) :=
    charZero_of_injective_algebraMap (algebraMap k₀ (K₀ k₀ (lineAlgGen k₀ t))).injective
  haveI : IsAlgClosure (K₀ k₀ (lineAlgGen k₀ t)) (lineAlgClosure k₀ t) :=
    (isAlgClosure_iff _ _).2 ⟨inferInstance, inferInstance⟩
  exact isGalois_iff.2 ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, inferInstance⟩

/-- `t₀` is transcendental over `k₀` when `t` is transcendental over an extension `k` of `k₀`. -/
lemma transcendental_lineGen {k : Type u} [Field k] [Algebra k₀ k] [Algebra k Ω]
    [IsScalarTower k₀ k Ω] {t : Ω} (ht : Transcendental k t) :
    Transcendental k₀ (lineAlgGen k₀ t) :=
  fun h ↦ ht ((h.algHom (lineIncl k₀ t)).tower_top k)

variable {k : Type u} [Field k] [CharZero k] [Algebra k₀ k] [Algebra k Ω] [IsScalarTower k₀ k Ω]

/-- **Descent of inertia-fixed elements to `Ω₀`** (`inertia_fix_descent` for
`Ω₀ = lineAlgClosure k₀ t`): if `Ω` is separably closed, `Ω / k(t)` is Galois and the inertia group
of `W` (`k ⊆ W`, `v_W(t) < 1`) fixes `z ∈ Ω₀`, then the inertia group of `W ∩ Ω₀` in
`Gal(Ω₀ / k₀(t₀))` fixes `z`. -/
theorem inertia_fix_descent_lineAlgClosure [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω]
    (ht : Transcendental k t) {W : ValuationSubring Ω} (hWk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWt : W.valuation t < 1) (z : lineAlgClosure k₀ t)
    (hz : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, σ z = z) :
    ∀ σ₀ ∈ GaloisPi1.inertia (P := K₀ k₀ (lineAlgGen k₀ t))
      (W.comap (lineIncl k₀ t : lineAlgClosure k₀ t →+* Ω)), σ₀ z = z := by
  haveI : CharZero k₀ := RingHom.charZero (algebraMap k₀ k)
  haveI : IsGalois (K₀ k (lineIncl k₀ t (lineAlgGen k₀ t))) Ω := ‹IsGalois (K₀ k t) Ω›
  exact inertia_fix_descent (lineIncl k₀ t) ht hWk hWt z hz

end Construction

end CurvesJacobian.Cusp
