/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LineS
import CurvesJacobian.Cusp.InertiaComm

/-!
# Unramified branches at the cusps of `ℙ¹ ∖ (S ∪ {∞})`

The generalisation of `CurvesJacobian.Cusp.LineBranch` (hard-wired to the cusps `0, 1, ∞`) to the
line `U_S = ℙ¹ ∖ (S ∪ {∞}) = Spec k[t, 1/P_S(t)]` for a finite set `S ⊆ k`
(`CurvesJacobian.Cusp.lineRingS`). The cusps are indexed by `c : Option k`: `some a` (`a ∈ S`) is
the cusp `a`, with local coordinate `t - a`, and `none` is `∞`, with local coordinate `1/t`
(`CurvesJacobian.Cusp.cuspCoordS`).

Near the cusp `c`, `t` is `a + s` resp. `1/s` in the local coordinate `s`; `P_S(t)` becomes
`s G(s)` resp. `G(s)/s^|S|` for a polynomial `G` with `G(0) ≠ 0`
(`CurvesJacobian.Cusp.cuspPolyS`), so `t ↦ a + s` resp. `1/s` defines
`k[t, 1/P_S(t)] → k[s, 1/(s G(s))]` (`CurvesJacobian.Cusp.cuspLineS`).

## Main results

* `CurvesJacobian.Cusp.nonempty_pBranch_of_ringHom`: if a ring map `φ : Γ(Y) → Ω` over
  `k[t, 1/P_S(t)] → Ω` is fixed by the inertia elements of a place `W` over the cusp `c`, then
  the finite étale `Y ⟶ U_S` has a branch at `c` (`CurvesJacobian.Cusp.PBranch` with the
  relation `T · Q(s) = P(s)` of `CurvesJacobian.Cusp.cuspP`, `CurvesJacobian.Cusp.cuspQ`).
* `CurvesJacobian.Cusp.nonempty_pBranch_of_fixed`: the same for a point of the fibre of `Y` at
  the geometric generic point fixed by the inertia group.
* `CurvesJacobian.Cusp.lineInertiaS_comm`: the inertia group of a place over a cusp in
  `π₁ᵉᵗ(U_S, η)` is abelian.
-/

open CategoryTheory AlgebraicGeometry Polynomial AffOrbicurve IntermediateField
open IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### The cusps and the local rings -/

section Cusp

variable {K : Type u} [Field K] (S : Finset K)

open scoped Classical in
/-- The polynomial `G` with `P_S(a + s) = s G(s)` at the finite cusp `a ∈ S` and
`P_S(1/s) = G(s) / s^|S|` at `∞` (`none`). -/
def cuspPolyS : Option K → K[X]
  | some a => ∏ b ∈ S.erase a, (X + C (a - b))
  | none => ∏ b ∈ S, (1 - C b * X)

lemma cuspPolyS_eval_zero (c : Option K) : (cuspPolyS S c).eval 0 ≠ 0 := by
  cases c with
  | none => simp [cuspPolyS, eval_prod]
  | some a =>
    classical
    rw [cuspPolyS, eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun b hb ↦ by
      simpa [sub_eq_zero] using (Finset.ne_of_mem_erase hb).symm

/-- The localization `K[s, 1/(s G(s))]` at the cusp `c`. -/
abbrev cuspLocalS (c : Option K) : Type u := Localization.Away (X * cuspPolyS S c)

/-- Divisors of `X G` are units in `K[s, 1/(s G(s))]`. -/
lemma isUnit_cuspLocalS_of_dvd {c : Option K} {p : K[X]} (h : p ∣ X * cuspPolyS S c) :
    IsUnit (algebraMap K[X] (cuspLocalS S c) p) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit _)

/-- The image of `t` in `K[s, 1/(s G(s))]`: `a + s` at the cusp `a`, `1/s` at `∞`. -/
def cuspTS : (c : Option K) → cuspLocalS S c
  | some a => algebraMap K[X] _ (C a + X)
  | none => algebraMap K[X] _ (cuspPolyS S none) *
      IsLocalization.Away.invSelf (X * cuspPolyS S none)

/-- An algebra map out of a `K[X]`-algebra sends `p` to `p` evaluated at the image of `X`. -/
lemma algHom_algebraMap_eq_aeval {R B : Type*} [CommRing R] [Algebra K R] [Algebra K[X] R]
    [IsScalarTower K K[X] R] [CommRing B] [Algebra K B] (κ : R →ₐ[K] B) (p : K[X]) :
    κ (algebraMap K[X] R p) = aeval (κ (algebraMap K[X] R X)) p := by
  have : κ.comp (IsScalarTower.toAlgHom K K[X] R) = aeval (κ (algebraMap K[X] R X)) :=
    Polynomial.algHom_ext (by simp)
  exact DFunLike.congr_fun this p

/-- **The coordinate relation at the cusp `c`**: `T · Q(s) = P(s)` between the images of `t`
and `s` under any algebra map out of `K[s, 1/(s G(s))]`. -/
lemma cuspTS_rel {B : Type*} [CommRing B] [Algebra K B] (c : Option K)
    (κ : cuspLocalS S c →ₐ[K] B) :
    κ (cuspTS S c) * aeval (κ (algebraMap K[X] _ X)) (cuspQ c) =
      aeval (κ (algebraMap K[X] _ X)) (cuspP c) := by
  cases c with
  | some a =>
    rw [show cuspTS S (some a) = algebraMap K[X] _ (C a + X) from rfl,
      algHom_algebraMap_eq_aeval]
    simp
  | none =>
    have hinv := congrArg κ
      (IsLocalization.Away.mul_invSelf (S := cuspLocalS S none) (X * cuspPolyS S none))
    simp only [map_mul, map_one] at hinv
    change κ (algebraMap K[X] _ (cuspPolyS S none) *
      IsLocalization.Away.invSelf (X * cuspPolyS S none)) * aeval _ X = aeval _ 1
    rw [map_mul, aeval_X, map_one]
    linear_combination hinv

/-- `P_S(t)` is a unit in `K[s, 1/(s G(s))]`. -/
lemma isUnit_cuspTS (c : Option K) (hc : ∀ a, c = some a → a ∈ S) :
    IsUnit (aeval (cuspTS S c) (polyS S)) := by
  classical
  cases c with
  | some a =>
    have ha : a ∈ S := hc a rfl
    have e : aeval (C a + X) (polyS S) = X * cuspPolyS S (some a) := by
      rw [aeval_polyS, ← Finset.mul_prod_erase S _ ha, cuspPolyS]
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun b _ ↦ ?_
        rw [C_sub, Polynomial.algebraMap_eq]
        ring
    change IsUnit (aeval (algebraMap K[X] (cuspLocalS S (some a)) (C a + X)) (polyS S))
    rw [Polynomial.aeval_algebraMap_apply, e]
    exact IsLocalization.Away.algebraMap_isUnit _
  | none =>
    have hinv := IsLocalization.Away.mul_invSelf (S := cuspLocalS S none) (X * cuspPolyS S none)
    have hGu : IsUnit (algebraMap K[X] (cuspLocalS S none) (cuspPolyS S none)) :=
      isUnit_cuspLocalS_of_dvd S (Dvd.intro_left _ rfl)
    have hTx : cuspTS S none * algebraMap K[X] _ X = 1 := by
      change algebraMap K[X] _ (cuspPolyS S none) *
        IsLocalization.Away.invSelf (X * cuspPolyS S none) * _ = 1
      rw [map_mul] at hinv
      linear_combination hinv
    have hT : IsUnit (cuspTS S none) := IsUnit.of_mul_eq_one _ hTx
    have hG : algebraMap K[X] (cuspLocalS S none) (cuspPolyS S none) =
        ∏ b ∈ S, (1 - algebraMap K (cuspLocalS S none) b * algebraMap K[X] _ X) := by
      refine (algHom_algebraMap_eq_aeval (AlgHom.id K _) _).trans ?_
      simp [cuspPolyS, map_prod]
    have e : ∏ b ∈ S, (cuspTS S none - algebraMap K _ b) =
        cuspTS S none ^ S.card * algebraMap K[X] _ (cuspPolyS S none) := by
      rw [hG, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ ↦ ?_
      linear_combination (algebraMap K (cuspLocalS S none) b) * hTx
    rw [aeval_polyS, e]
    exact (hT.pow _).mul hGu

/-- `K[t, 1/P_S(t)] → K[s, 1/(s G(s))]`, `t ↦ a + s` resp. `1/s`. -/
def cuspLineS (c : Option K) (hc : ∀ a, c = some a → a ∈ S) : lineRingS S →ₐ[K] cuspLocalS S c :=
  lineLiftS (cuspTS S c) (isUnit_cuspTS S c hc)

end Cusp

/-! ### Local coordinates at the cusps -/

section Coord

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

lemma cuspCoordS_mem (c : Option k) (t : Ω) : cuspCoordS c t ∈ K₀ k t := by
  have ht := IntermediateField.mem_adjoin_simple_self k t
  cases c with
  | some a => exact sub_mem ht (IntermediateField.algebraMap_mem _ a)
  | none => exact inv_mem ht

lemma mem_K₀_cuspCoordS (c : Option k) (t : Ω) : t ∈ K₀ k (cuspCoordS c t) := by
  have hu := IntermediateField.mem_adjoin_simple_self k (cuspCoordS c t)
  cases c with
  | some a =>
    have h := add_mem hu (IntermediateField.algebraMap_mem (K₀ k (cuspCoordS (some a) t)) a)
    rwa [cuspCoordS_some, sub_add_cancel] at h
  | none =>
    have h := inv_mem hu
    rwa [cuspCoordS_none, inv_inv] at h

/-- The local coordinate at a cusp generates the same field as `t`. -/
lemma K₀_cuspCoordS (c : Option k) (t : Ω) : K₀ k (cuspCoordS c t) = K₀ k t :=
  le_antisymm (IntermediateField.adjoin_simple_le_iff.2 (cuspCoordS_mem c t))
    (IntermediateField.adjoin_simple_le_iff.2 (mem_K₀_cuspCoordS c t))

lemma transcendental_cuspCoordS (ht : Transcendental k t) (c : Option k) :
    Transcendental k (cuspCoordS c t) := by
  intro hu
  haveI : FiniteDimensional k (K₀ k (cuspCoordS c t)) :=
    IntermediateField.adjoin.finiteDimensional hu.isIntegral
  have h := (Algebra.IsAlgebraic.isAlgebraic (R := k)
    (⟨t, mem_K₀_cuspCoordS c t⟩ : K₀ k (cuspCoordS c t)))
  exact ht ((isAlgebraic_algebraMap_iff (algebraMap (K₀ k (cuspCoordS c t)) Ω).injective).2 h)

lemma cuspCoordS_ne_zero (ht : Transcendental k t) (c : Option k) : cuspCoordS c t ≠ 0 :=
  fun h ↦ transcendental_cuspCoordS ht c (h ▸ isAlgebraic_zero)

lemma isUnit_aeval_cuspCoordS (ht : Transcendental k t) (S : Finset k) (c : Option k) :
    IsUnit (aeval (cuspCoordS c t) (X * cuspPolyS S c)) := by
  refine isUnit_iff_ne_zero.2 fun h ↦ transcendental_cuspCoordS ht c ⟨X * cuspPolyS S c, ?_, h⟩
  exact mul_ne_zero X_ne_zero fun h0 ↦ cuspPolyS_eval_zero S c (by rw [h0, eval_zero])

end Coord

/-! ### From a fixed point of inertia to a branch -/

section Branch

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (S : Finset k)

/-- `k[s, 1/(s G(s))] → Ω`, `s ↦ u_c` (the local coordinate at the cusp `c`). -/
def cuspToΩS (ht : Transcendental k t) (c : Option k) : cuspLocalS S c →ₐ[k] Ω :=
  IsLocalization.Away.liftAlgHom (X * cuspPolyS S c) (f := aeval (cuspCoordS c t))
    (isUnit_aeval_cuspCoordS ht S c)

lemma cuspToΩS_algebraMap (ht : Transcendental k t) (c : Option k) (p : k[X]) :
    cuspToΩS S ht c (algebraMap k[X] _ p) = aeval (cuspCoordS c t) p := by
  simp [cuspToΩS, IsLocalization.Away.liftAlgHom_apply]

lemma cuspToΩS_cuspTS (ht : Transcendental k t) (c : Option k) :
    cuspToΩS S ht c (cuspTS S c) = t := by
  have h := cuspTS_rel S c (cuspToΩS S ht c)
  rw [cuspToΩS_algebraMap, aeval_X] at h
  cases c with
  | some a => simpa using h
  | none =>
    have ht0 : t ≠ 0 := by simpa using ne_algebraMap_of_transcendental ht 0
    simp only [cuspQ_none, cuspP_none, aeval_X, map_one, cuspCoordS_none] at h
    exact (mul_inv_eq_one₀ ht0).1 h

lemma cuspToΩS_comp_cuspLineS (ht : Transcendental k t) (c : Option k)
    (hc : ∀ a, c = some a → a ∈ S) :
    (cuspToΩS S ht c).comp (cuspLineS S c hc) = lineToΩS S ht :=
  lineRingS_algHom_ext (by simp [cuspLineS, cuspToΩS_cuspTS S ht c])

/-- **The ring map of a fixed point.** A point `x` of the fibre of `Y` at `η` fixed by the
inertia elements of `W` is a ring map `φ : Γ(Y) → Ω` over `k[t, 1/P_S(t)] → Ω`, fixed by the
inertia elements. -/
lemma exists_fixed_ringHomS [IsSepClosed Ω] [IsGalois (K₀ k t) Ω] (ht : Transcendental k t)
    (W : ValuationSubring Ω) (Y : FiniteEtale (Spec (.of (lineRingS S))))
    (x : (FiniteEtale.fiber (lineGenS S ht)).obj Y)
    (hx : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, (lineGaloisS S ht σ).hom.app Y x = x) :
    ∃ φ : Γ(Y.left, ⊤) →+* Ω,
      φ.comp (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (lineRingS S))).inv.hom) =
        (lineToΩS S ht).toRingHom ∧
      ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, ∀ b, σ (φ b) = φ b := by
  let y : Spec (.of Ω) ⟶ Y.left := (FiniteEtale.fiberObjEquivHom (lineGenS S ht) Y x).left
  have hy : y ≫ Y.hom = lineGenS S ht :=
    Over.w (FiniteEtale.fiberObjEquivHom (lineGenS S ht) Y x)
  refine ⟨pointRingHom y, ?_, fun σ hσ b ↦ ?_⟩
  · have h : (pointRingHom y).comp Y.hom.appTop.hom =
        (lineToΩS S ht).toRingHom.comp (Scheme.ΓSpecIso (.of (lineRingS S))).hom.hom :=
      ((pointRingHom_comp y Y.hom).symm.trans
        (congrArg pointRingHom (hy.trans (lineGenS_eq S ht)))).trans (pointRingHom_specMap _)
    refine RingHom.ext fun r ↦ ?_
    have h' := RingHom.congr_fun h ((Scheme.ΓSpecIso (.of (lineRingS S))).inv.hom r)
    have e : (Scheme.ΓSpecIso (.of (lineRingS S))).hom.hom
        ((Scheme.ΓSpecIso (.of (lineRingS S))).inv.hom r) = r := by simp
    exact h'.trans (congrArg (fun z ↦ (lineToΩS S ht) z) e)
  · have h1 := FiniteEtale.galoisAction_hom_app_left (K₀ k t)
      (Spec.map (CommRingCat.ofHom (lineToK₀S S ht).toRingHom)) rfl σ Y x
    have h2 : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ y = y :=
      h1.symm.trans
        (congrArg (fun z ↦ (FiniteEtale.fiberObjEquivHom (lineGenS S ht) Y z).left) (hx σ hσ))
    have h3 := congrArg pointRingHom h2
    rw [pointRingHom_specMap_comp] at h3
    exact RingHom.congr_fun h3 b

/-- **The field of a fixed ring map.** For `ρ : k[t, 1/P_S(t)] → B` finite and `φ : B → Ω` over
`k[t, 1/P_S(t)] → Ω` fixed by the inertia elements of `W`, the field `N = k(u)(φ(B))` is finite
over `k(u)` (for any `u` with `k(u) = k(t)`) and fixed by the inertia group of `W` over `k(u)`. -/
lemma exists_intermediateField_of_fixedS (ht : Transcendental k t) {u : Ω}
    (hK : K₀ k u = K₀ k t) (W : ValuationSubring Ω) {B : Type u} [CommRing B]
    (ρ : lineRingS S →+* B) (hρ : ρ.Finite)
    (φ : B →+* Ω) (hφρ : φ.comp ρ = (lineToΩS S ht).toRingHom)
    (hfix : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, ∀ b, σ (φ b) = φ b) :
    ∃ N : IntermediateField (K₀ k u) Ω, FiniteDimensional (K₀ k u) N ∧
      (∀ b, φ b ∈ N) ∧
      ∀ σ ∈ GaloisPi1.inertia (P := K₀ k u) W, σ ∈ N.fixingSubgroup := by
  classical
  have htu : t ∈ K₀ k u := by
    rw [hK]
    exact IntermediateField.mem_adjoin_simple_self k t
  let lam : lineRingS S →ₐ[k] K₀ k u :=
    lineLiftS ⟨t, htu⟩ (isUnit_aeval_polyS_of_transcendental S ht htu)
  have hlam : (IsScalarTower.toAlgHom k (K₀ k u) Ω).comp lam = lineToΩS S ht :=
    lineRingS_algHom_ext (by simp [lam])
  have hφρ' : ∀ r, φ (ρ r) = algebraMap (K₀ k u) Ω (lam r) := by
    intro r
    rw [← RingHom.comp_apply φ ρ, hφρ, ← hlam]
    rfl
  letI : Algebra (lineRingS S) B := ρ.toAlgebra
  haveI : Module.Finite (lineRingS S) B := hρ
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := lineRingS S) (M := B)
  let N : IntermediateField (K₀ k u) Ω :=
    IntermediateField.adjoin (K₀ k u) ((fun b ↦ φ b) '' (T : Set B))
  have hint : ∀ b, IsIntegral (K₀ k u) (φ b) := by
    intro b
    obtain ⟨p, hp, hpb⟩ := hρ.to_isIntegral b
    refine ⟨p.map lam.toRingHom, hp.map _, ?_⟩
    rw [eval₂_map]
    have : (algebraMap (K₀ k u) Ω).comp lam.toRingHom = φ.comp ρ :=
      RingHom.ext fun r ↦ (hφρ' r).symm
    rw [this, ← Polynomial.hom_eval₂, hpb, map_zero]
  haveI : FiniteDimensional (K₀ k u) N := IntermediateField.finiteDimensional_adjoin
    (fun z hz ↦ by obtain ⟨b, -, rfl⟩ := hz; exact hint b)
  have hφN : ∀ b, φ b ∈ N := by
    intro b
    have hb : b ∈ Submodule.span (lineRingS S) (T : Set B) := hT ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
    | smul r z _ hz =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hz
      change φ (ρ r) ∈ N
      rw [hφρ' r]
      exact N.algebraMap_mem _
  refine ⟨N, inferInstance, hφN, fun σ hσ ↦ ?_⟩
  have hσ' : algEquivOfK₀Eq hK σ ∈ GaloisPi1.inertia (P := K₀ k t) W := hσ
  have hle : N ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨b, -, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hs : σ ∈ MulAction.stabilizer (Ω ≃ₐ[K₀ k u] Ω) (φ b) := hfix _ hσ' b
    exact (Subgroup.zpowers_le.2 hs hg : g ∈ MulAction.stabilizer _ _)
  exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers σ)

set_option maxHeartbeats 2000000 in
-- many instances on localizations of `coordRing k u N`
set_option synthInstance.maxHeartbeats 400000 in
/-- **The ring-theoretic branch.** In the situation of `exists_intermediateField_of_fixedS`, if
`W` lies over the cusp `c`, the normalization of `k[u]` in `N` is étale over `k[u]` near the
centre of `W`; localizing gives `A`, `s = u`, the point `ε` (the centre),
`θ : k[t, 1/P_S(t)] → A[1/s]` and `ψ : B → A[1/s]` over `θ`. -/
lemma exists_branch_ringS [IsAlgClosed k] [CharZero k] [IsGalois (K₀ k t) Ω]
    (ht : Transcendental k t) (c : Option k) (hc : ∀ a, c = some a → a ∈ S)
    {W : ValuationSubring Ω} (hWk : ∀ x : k, algebraMap k Ω x ∈ W)
    (hWc : W.valuation (cuspCoordS c t) < 1)
    {B : Type u} [CommRing B] (ρ : lineRingS S →+* B) (hρ : ρ.Finite)
    (φ : B →+* Ω) (hφρ : φ.comp ρ = (lineToΩS S ht).toRingHom)
    (N : IntermediateField (K₀ k (cuspCoordS c t)) Ω)
    [FiniteDimensional (K₀ k (cuspCoordS c t)) N]
    (hφN : ∀ b, φ b ∈ N)
    (hNfix : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k (cuspCoordS c t)) W, σ ∈ N.fixingSubgroup) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A) (_ : Algebra.FiniteType k A) (s : A)
      (_ : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ s).toRingHom.Etale)
      (ε : A →ₐ[k] k) (_ : ε s = 0)
      (θ : lineRingS S →ₐ[k] Localization.Away s)
      (_ : θ (lineTS S) * aeval (algebraMap A (Localization.Away s) s) (cuspQ c) =
        aeval (algebraMap A (Localization.Away s) s) (cuspP c))
      (ψ : B →+* Localization.Away s), ψ.comp ρ = θ.toRingHom := by
  classical
  have hu : Transcendental k (cuspCoordS c t) := transcendental_cuspCoordS ht c
  have hK : K₀ k (cuspCoordS c t) = K₀ k t := K₀_cuspCoordS c t
  haveI : IsGalois (K₀ k (cuspCoordS c t)) Ω := hK ▸ inferInstance
  have hu0 : (cuspCoordS c t) ≠ 0 := cuspCoordS_ne_zero ht c
  have huW : (cuspCoordS c t) ∈ W := (W.valuation_le_one_iff _).1 hWc.le
  have hW : IsCentered k (cuspCoordS c t) W := ⟨hWk, huW⟩
  haveI := isSeparable_of_charZero N
  -- the centre of `W` on `N`
  let cX := coordRingMap hu N X
  have hcX : toΩ (cuspCoordS c t) N cX = (cuspCoordS c t) := by
    rw [toΩ_apply, coordRingMap_apply, aeval_X]
  have hcXmem : cX ∈ centerIdeal hW N := (mem_centerIdeal hW).2 (by rw [hcX]; exact hWc)
  have hne : centerIdeal hW N ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hcXmem
    exact hu0 (by rw [← hcX, hcXmem, map_zero])
  let cG := coordRingMap hu N (cuspPolyS S c)
  have hcG : cG ∉ centerIdeal hW N := by
    rw [mem_centerIdeal]
    intro hlt
    obtain ⟨q, hq⟩ := X_dvd_sub_C (p := cuspPolyS S c)
    rw [coeff_zero_eq_eval_zero] at hq
    have hG : toΩ (cuspCoordS c t) N cG = algebraMap k Ω ((cuspPolyS S c).eval 0) +
        (cuspCoordS c t) * toΩ (cuspCoordS c t) N (coordRingMap hu N q) := by
      have h' := congrArg (aeval (cuspCoordS c t)) hq
      rw [map_sub, aeval_C, map_mul, aeval_X] at h'
      rw [toΩ_apply, toΩ_apply, coordRingMap_apply, coordRingMap_apply]
      linear_combination h'
    have hqW : W.valuation (toΩ (cuspCoordS c t) N (coordRingMap hu N q)) ≤ 1 :=
      valuation_le_one hW _
    have hc1 := valuation_algebraMap_eq_one hWk (cuspPolyS_eval_zero S c)
    have hlt' : W.valuation (algebraMap k Ω ((cuspPolyS S c).eval 0)) < 1 := by
      have e : algebraMap k Ω ((cuspPolyS S c).eval 0) =
          toΩ (cuspCoordS c t) N cG -
            (cuspCoordS c t) * toΩ (cuspCoordS c t) N (coordRingMap hu N q) := by
        rw [hG]; ring
      rw [e]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hlt ?_)
      rw [map_mul]
      calc W.valuation (cuspCoordS c t) *
            W.valuation (toΩ (cuspCoordS c t) N (coordRingMap hu N q))
          ≤ W.valuation (cuspCoordS c t) * 1 := mul_le_mul_right hqW _
        _ < 1 := by rw [mul_one]; exact hWc
    rw [hc1] at hlt'
    exact lt_irrefl _ hlt'
  -- the étale neighbourhood `A = coordRing[1/r]`
  obtain ⟨r, hr, hrG, hrEt⟩ := exists_etale_away_of_inertia_le hu hW N hne hNfix cG hcG
  haveI hPmax := isMaximal_centerIdeal hu hW N hne
  haveI : Algebra.FiniteType k (coordRing k (cuspCoordS c t) N) :=
    finiteType_ring (cuspCoordS c t) hu N
  have hr0 : r ≠ 0 := fun h ↦ hr (h ▸ zero_mem _)
  let A := Localization.Away r
  have hrnz : Submonoid.powers r ≤ nonZeroDivisors (coordRing k (cuspCoordS c t) N) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain A := IsLocalization.isDomain_localization hrnz
  haveI : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (S := coordRing k (cuspCoordS c t) N) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) A)
  have hinjCA : Function.Injective (algebraMap (coordRing k (cuspCoordS c t) N) A) :=
    IsLocalization.injective A hrnz
  let s : A := algebraMap (coordRing k (cuspCoordS c t) N) A cX
  have htoΩinj : Function.Injective (toΩ (cuspCoordS c t) N) :=
    fun a b h ↦ Subtype.val_injective (Subtype.val_injective h)
  have hcX0 : cX ≠ 0 := fun h ↦ hu0 (by rw [← hcX, h, map_zero])
  have hs0 : s ≠ 0 := fun h ↦ hcX0 (hinjCA (h.trans (map_zero _).symm))
  -- `ι₁ : A → Ω`, `ι : A[1/s] → Ω`
  have hunit_r : IsUnit (toΩ (cuspCoordS c t) N r) :=
    isUnit_iff_ne_zero.2 (fun h ↦ hr0 (htoΩinj (h.trans (map_zero _).symm)))
  let ι₁ : A →+* Ω := IsLocalization.Away.lift r hunit_r
  have hι₁ : ∀ x, ι₁ (algebraMap (coordRing k (cuspCoordS c t) N) A x) =
      toΩ (cuspCoordS c t) N x :=
    IsLocalization.Away.lift_eq r hunit_r
  have hι₁inj : Function.Injective ι₁ :=
    (IsLocalization.lift_injective_iff (M := Submonoid.powers r) (S := A) _).2
      fun a b ↦ ⟨fun h ↦ by rw [hinjCA h], fun h ↦ by rw [htoΩinj h]⟩
  let As := Localization.Away s
  have hsnz : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs0
  have hinjAAs : Function.Injective (algebraMap A As) := IsLocalization.injective As hsnz
  have hι₁s : ι₁ s = (cuspCoordS c t) := by rw [hι₁, hcX]
  have hunit_s : IsUnit (ι₁ s) := by rw [hι₁s]; exact isUnit_iff_ne_zero.2 hu0
  let ι : As →+* Ω := IsLocalization.Away.lift s hunit_s
  have hι : ∀ a, ι (algebraMap A As a) = ι₁ a := IsLocalization.Away.lift_eq s hunit_s
  have hιinj : Function.Injective ι :=
    (IsLocalization.lift_injective_iff (M := Submonoid.powers s) (S := As) _).2
      fun a b ↦ ⟨fun h ↦ by rw [hinjAAs h], fun h ↦ by rw [hι₁inj h]⟩
  have hιk : ∀ x : k, ι (algebraMap k As x) = algebraMap k Ω x := by
    intro x
    rw [IsScalarTower.algebraMap_apply k A As, hι, IsScalarTower.algebraMap_apply k
      (coordRing k (cuspCoordS c t) N) A, hι₁]
    rfl
  -- polynomials in `s`
  have hagree : ∀ p : k[X], aeval (algebraMap A As s) p =
      algebraMap A As (algebraMap (coordRing k (cuspCoordS c t) N) A (coordRingMap hu N p)) := by
    intro p
    have e : (aeval (algebraMap A As s)).toRingHom = (algebraMap A As).comp
        ((algebraMap (coordRing k (cuspCoordS c t) N) A).comp (coordRingMap hu N)) := by
      refine Polynomial.ringHom_ext (fun x ↦ ?_) ?_
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.coe_comp,
          Function.comp_apply, coordRingMap_C]
        rw [← IsScalarTower.algebraMap_apply k (coordRing k (cuspCoordS c t) N) A,
          ← IsScalarTower.algebraMap_apply k A As]
      · simp [s, cX]
    exact RingHom.congr_fun e p
  have hagree' : ∀ p : k[X], aeval s p =
      algebraMap (coordRing k (cuspCoordS c t) N) A (coordRingMap hu N p) := by
    intro p
    apply hinjAAs
    rw [← Polynomial.aeval_algebraMap_apply]
    exact hagree p
  -- étaleness over `k[s]`
  have het : (aeval (R := k) s).toRingHom.Etale := by
    have e : (aeval (R := k) s).toRingHom =
        (algebraMap (coordRing k (cuspCoordS c t) N) A).comp (coordRingMap hu N) :=
      RingHom.ext fun p ↦ hagree' p
    rw [e]
    exact hrEt
  -- the point `ε`
  obtain ⟨ε₀, hε₀⟩ := exists_algHom_ker_eq (k := k) (centerIdeal hW N)
  have hε₀r : IsUnit (ε₀ r) :=
    isUnit_iff_ne_zero.2 fun h ↦ hr (hε₀ ▸ (RingHom.mem_ker).2 h)
  let ε : A →ₐ[k] k := IsLocalization.Away.liftAlgHom r (f := ε₀) hε₀r
  have hεs : ε s = 0 := by
    change IsLocalization.Away.lift r hε₀r (algebraMap _ A cX) = 0
    rw [IsLocalization.Away.lift_eq]
    exact (RingHom.mem_ker).1 (hε₀ ▸ hcXmem)
  -- `θ : k[t, 1/P_S(t)] → A[1/s]`
  have hsAs : IsUnit (algebraMap A As s) := IsLocalization.Away.algebraMap_isUnit s
  have hGAs : IsUnit (algebraMap A As (algebraMap (coordRing k (cuspCoordS c t) N) A cG)) :=
    hrG.map _
  have hXG : IsUnit (aeval (algebraMap A As s) (X * cuspPolyS S c)) := by
    rw [map_mul, aeval_X, hagree]
    exact hsAs.mul hGAs
  let κ : cuspLocalS S c →ₐ[k] As :=
    IsLocalization.Away.liftAlgHom (X * cuspPolyS S c) (f := aeval (algebraMap A As s)) hXG
  have hκ : ∀ p, κ (algebraMap k[X] _ p) = aeval (algebraMap A As s) p := fun p ↦
    IsLocalization.Away.lift_eq _ hXG p
  let θ : lineRingS S →ₐ[k] As := κ.comp (cuspLineS S c hc)
  have hrel : θ (lineTS S) * aeval (algebraMap A As s) (cuspQ c) =
      aeval (algebraMap A As s) (cuspP c) := by
    have h := cuspTS_rel S c κ
    have hθT : θ (lineTS S) = κ (cuspTS S c) := by simp [θ, cuspLineS]
    rw [hκ, aeval_X] at h
    rwa [hθT]
  -- `ι ∘ θ = (k[t, 1/P_S(t)] → Ω)`
  have hικ : ι.comp κ.toRingHom = (cuspToΩS S ht c).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (X * cuspPolyS S c))
      (Polynomial.ringHom_ext (fun x ↦ ?_) ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hκ, cuspToΩS_algebraMap, aeval_C, aeval_C, hιk]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hκ, cuspToΩS_algebraMap, aeval_X, aeval_X, hι, hι₁s]
  have hιθ : ι.comp θ.toRingHom = (lineToΩS S ht).toRingHom := by
    rw [← cuspToΩS_comp_cuspLineS S ht c hc]
    change ι.comp (κ.toRingHom.comp (cuspLineS S c hc).toRingHom) = _
    rw [← RingHom.comp_assoc, hικ]
    rfl
  -- `φ(B) ⊆ ι(A[1/s])`
  letI : Algebra (cuspLocalS S c) Ω := (cuspToΩS S ht c).toRingHom.toAlgebra
  letI : Algebra k[X] Ω := (aeval (cuspCoordS c t)).toRingHom.toAlgebra
  haveI : IsScalarTower k[X] (cuspLocalS S c) Ω :=
    IsScalarTower.of_algebraMap_eq fun p ↦ (cuspToΩS_algebraMap S ht c p).symm
  have hrange : ∀ b, φ b ∈ ι.range := by
    intro b
    have hintL : IsIntegral (cuspLocalS S c) (φ b) := by
      obtain ⟨p, hp, hpb⟩ := hρ.to_isIntegral b
      refine ⟨p.map (cuspLineS S c hc).toRingHom, hp.map _, ?_⟩
      rw [eval₂_map]
      have e : (algebraMap (cuspLocalS S c) Ω).comp (cuspLineS S c hc).toRingHom = φ.comp ρ := by
        rw [hφρ, ← cuspToΩS_comp_cuspLineS S ht c hc]
        rfl
      rw [e, ← Polynomial.hom_eval₂, hpb, map_zero]
    obtain ⟨⟨_, n, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Submonoid.powers (X * cuspPolyS S c)) (φ b) hintL
    have hz : ((X * cuspPolyS S c) ^ n : k[X]) • φ b =
        aeval (cuspCoordS c t) (X * cuspPolyS S c) ^ n * φ b := by
      rw [Algebra.smul_def, ← map_pow]
      rfl
    rw [Submonoid.smul_def] at hm
    simp only at hm
    rw [hz] at hm
    let a₀ : A₀ k (cuspCoordS c t) :=
      ⟨(cuspCoordS c t), Algebra.self_mem_adjoin_singleton k (cuspCoordS c t)⟩
    letI : Algebra k[X] (A₀ k (cuspCoordS c t)) := (aeval a₀).toRingHom.toAlgebra
    haveI : IsScalarTower k[X] (A₀ k (cuspCoordS c t)) Ω :=
      IsScalarTower.of_algebraMap_eq fun p ↦ by
      change aeval (cuspCoordS c t) p = ((aeval a₀ p : A₀ k (cuspCoordS c t)) : Ω)
      rw [← Subalgebra.val_apply, ← Polynomial.aeval_algHom_apply]
      rfl
    have hzA := hm.tower_top (A := A₀ k (cuspCoordS c t))
    have hdN : aeval (cuspCoordS c t) (X * cuspPolyS S c) ∈ N := by
      rw [← coordRingMap_apply hu N]
      exact ((coordRingMap hu N (X * cuspPolyS S c)) : N).2
    have hzN : aeval (cuspCoordS c t) (X * cuspPolyS S c) ^ n * φ b ∈ N :=
      mul_mem (pow_mem hdN n) (hφN b)
    haveI : IsScalarTower (A₀ k (cuspCoordS c t)) N Ω :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hzN' : IsIntegral (A₀ k (cuspCoordS c t))
        (⟨aeval (cuspCoordS c t) (X * cuspPolyS S c) ^ n * φ b, hzN⟩ : N) :=
      (isIntegral_algebraMap_iff (algebraMap N Ω).injective).1 hzA
    let a : coordRing k (cuspCoordS c t) N := ⟨⟨_, hzN⟩, hzN'⟩
    have ha : toΩ (cuspCoordS c t) N a =
        aeval (cuspCoordS c t) (X * cuspPolyS S c) ^ n * φ b := rfl
    have hd0 : aeval (cuspCoordS c t) (X * cuspPolyS S c) ≠ 0 :=
      (isUnit_aeval_cuspCoordS ht S c).ne_zero
    have hcu : IsUnit (algebraMap A As (algebraMap (coordRing k (cuspCoordS c t) N) A
        (coordRingMap hu N (X * cuspPolyS S c)))) := by
      rw [← hagree]
      exact hXG
    have hιc : ι (algebraMap A As (algebraMap (coordRing k (cuspCoordS c t) N) A
        (coordRingMap hu N (X * cuspPolyS S c)))) =
          aeval (cuspCoordS c t) (X * cuspPolyS S c) := by
      rw [hι, hι₁, toΩ_apply, coordRingMap_apply]
    refine ⟨algebraMap A As (algebraMap (coordRing k (cuspCoordS c t) N) A a) *
      ((hcu.unit⁻¹ ^ n : Asˣ) : As), ?_⟩
    have hιinv : ι ((hcu.unit⁻¹ : Asˣ) : As) =
        (aeval (cuspCoordS c t) (X * cuspPolyS S c))⁻¹ := by
      rw [← hιc]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul, hcu.val_inv_mul, map_one]
    rw [map_mul, hι, hι₁, ha, Units.val_pow_eq_pow_val, map_pow, hιinv, inv_pow,
      mul_comm (aeval (cuspCoordS c t) _ ^ n), mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hd0),
      mul_one]
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_forall_mem_range hιinj hrange
  refine ⟨A, inferInstance, inferInstance, inferInstance, s, etale_mvAeval_of_etale_aeval het, ε,
    hεs, θ, hrel, ψ, ?_⟩
  refine RingHom.ext fun r' ↦ hιinj ?_
  rw [← RingHom.comp_apply ι, ← RingHom.comp_assoc, hψ, hφρ, ← hιθ]
  rfl

/-- **A fixed ring map gives a branch.** If a ring map `φ : Γ(Y) → Ω` over
`k[t, 1/P_S(t)] → Ω` is fixed by the inertia elements of a place `W ⊇ k` of `Ω` over the cusp
`c` (`v_W(u_c) < 1`), then `Y` has a branch at `c` (an unramified point over the cusp), with the
coordinate relation `t = a + s` resp. `t s = 1`. -/
theorem nonempty_pBranch_of_ringHom [IsAlgClosed k] [CharZero k] [IsGalois (K₀ k t) Ω]
    (ht : Transcendental k t) (c : Option k) (hc : ∀ a, c = some a → a ∈ S)
    {W : ValuationSubring Ω} (hWk : ∀ x : k, algebraMap k Ω x ∈ W)
    (hWc : W.valuation (cuspCoordS c t) < 1)
    (Y : AlgebraicGeometry.FiniteEtale (Spec (.of (lineRingS S))))
    (φ : Γ(Y.left, ⊤) →+* Ω)
    (hφ : φ.comp (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (lineRingS S))).inv.hom) =
      (lineToΩS S ht).toRingHom)
    (hfix : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, ∀ b, σ (φ b) = φ b) :
    Nonempty (PBranch k (lineTS S) Y.hom (cuspP c) (cuspQ c)) := by
  have hYfin : IsFinite Y.hom := inferInstance
  have hρ : (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (lineRingS S))).inv.hom).Finite :=
    (@Scheme.Hom.finite_appTop _ (Spec (.of (lineRingS S))) Y.hom inferInstance hYfin).comp
      (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of (lineRingS S))).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨N, hNfd, hφN, hNfix⟩ :=
    exists_intermediateField_of_fixedS S ht (K₀_cuspCoordS c t) W _ hρ φ hφ hfix
  obtain ⟨A, _, _, _, s, het, ε, hεs, θ, hrel, ψ, hψ⟩ :=
    exists_branch_ringS S ht c hc hWk hWc _ hρ φ hφ N hφN hNfix
  have hYaff : IsAffineHom Y.hom := inferInstance
  have hYleft : IsAffine Y.left :=
    @isAffine_of_isAffineHom _ (Spec (.of (lineRingS S))) Y.hom hYaff inferInstance
  refine ⟨PBranch.mk A s het ε hεs θ hrel
    (Spec.map (CommRingCat.ofHom ψ) ≫ Y.left.isoSpec.inv) ?_⟩
  have e1 : Y.left.isoSpec.inv ≫ Y.hom =
      Spec.map Y.hom.appTop ≫ (Spec (.of (lineRingS S))).isoSpec.inv :=
    (@Scheme.isoSpec_inv_naturality Y.left (Spec (.of (lineRingS S))) hYleft inferInstance
      Y.hom).symm
  calc (Spec.map (CommRingCat.ofHom ψ) ≫ Y.left.isoSpec.inv) ≫ Y.hom
      = Spec.map (CommRingCat.ofHom ψ) ≫ (Y.left.isoSpec.inv ≫ Y.hom) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map Y.hom.appTop ≫
          (Spec (.of (lineRingS S))).isoSpec.inv) :=
        congrArg (fun g ↦ Spec.map (CommRingCat.ofHom ψ) ≫ g) e1
    _ = Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map Y.hom.appTop ≫
          Spec.map (Scheme.ΓSpecIso (.of (lineRingS S))).inv) := by
        rw [Scheme.isoSpec_Spec_inv]; rfl
    _ = Spec.map ((Scheme.ΓSpecIso (.of (lineRingS S))).inv ≫ Y.hom.appTop ≫
          CommRingCat.ofHom ψ) := by
        simp only [Spec.map_comp, Category.assoc]; rfl
    _ = Spec.map (CommRingCat.ofHom θ.toRingHom) :=
        congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r ↦ RingHom.congr_fun hψ r))

/-- **A fixed point of inertia gives a branch.** If the inertia group of a place `W ⊇ k` of `Ω`
over the cusp `c` (`v_W(u_c) < 1`) fixes a point of the fibre of `Y` at the geometric generic
point, then `Y` has a branch at `c` (an unramified point over the cusp). -/
theorem nonempty_pBranch_of_fixed [IsAlgClosed k] [CharZero k] [IsSepClosed Ω]
    [IsGalois (K₀ k t) Ω] (ht : Transcendental k t) (c : Option k)
    (hc : ∀ a, c = some a → a ∈ S) {W : ValuationSubring Ω}
    (hWk : ∀ x : k, algebraMap k Ω x ∈ W) (hWc : W.valuation (cuspCoordS c t) < 1)
    (Y : AlgebraicGeometry.FiniteEtale (Spec (.of (lineRingS S))))
    (x : (FiniteEtale.fiber (lineGenS S ht)).obj Y)
    (hx : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, (lineGaloisS S ht σ).hom.app Y x = x) :
    Nonempty (PBranch k (lineTS S) Y.hom (cuspP c) (cuspQ c)) := by
  obtain ⟨φ, hφ, hfix⟩ := exists_fixed_ringHomS S ht W Y x hx
  exact nonempty_pBranch_of_ringHom S ht c hc hWk hWc Y φ hφ hfix

end Branch

/-! ### Inertia groups at the cusps are abelian -/

section Comm

variable {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- **Inertia elements over a cusp of `ℙ¹ ∖ (S ∪ {∞})` commute.** -/
theorem inertia_commute_of_cuspS [IsGalois (K₀ k t) Ω] (ht : Transcendental k t)
    (c : Option k) {W : ValuationSubring Ω} (hWk : ∀ x : k, algebraMap k Ω x ∈ W)
    (hWc : W.valuation (cuspCoordS c t) < 1) {σ τ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ GaloisPi1.inertia W) (hτ : τ ∈ GaloisPi1.inertia W) : σ * τ = τ * σ := by
  have hu : Transcendental k (cuspCoordS c t) := transcendental_cuspCoordS ht c
  have hK : K₀ k (cuspCoordS c t) = K₀ k t := K₀_cuspCoordS c t
  haveI : IsGalois (K₀ k (cuspCoordS c t)) Ω := hK ▸ inferInstance
  have hW : IsCentered k (cuspCoordS c t) W := ⟨hWk, (W.valuation_le_one_iff _).1 hWc.le⟩
  have h := inertia_commute hu hW hWc (σ := algEquivOfK₀Eq hK.symm σ)
    (τ := algEquivOfK₀Eq hK.symm τ) hσ hτ
  ext z
  have := congrArg (fun ρ : Ω ≃ₐ[K₀ k (cuspCoordS c t)] Ω ↦ ρ z) h
  simpa [AlgEquiv.mul_apply] using this

/-- **The inertia group of a place over a cusp of `ℙ¹ ∖ (S ∪ {∞})` is abelian.** -/
theorem lineInertiaS_comm (S : Finset k) [IsSepClosed Ω] [IsGalois (K₀ k t) Ω]
    (ht : Transcendental k t) (c : Option k) (hc : ∀ a, c = some a → a ∈ S)
    {W : ValuationSubring Ω} (hWk : ∀ x : k, algebraMap k Ω x ∈ W)
    (hWc : W.valuation (cuspCoordS c t) < 1) :
    ∀ a ∈ lineInertiaS S ht W, ∀ b ∈ lineInertiaS S ht W, a * b = b * a := by
  let G₀ := lineGaloisS S ht '' GaloisPi1.inertia (P := K₀ k t) W
  have hG₀ : ∀ a ∈ G₀, ∀ b ∈ G₀, a * b = b * a := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [← map_mul, ← map_mul, inertia_commute_of_cuspS ht c hWk hWc hσ hτ]
  -- the subgroup generated by `G₀` is abelian
  have h1 : Subgroup.closure G₀ ≤ Subgroup.centralizer G₀ :=
    (Subgroup.closure_le _).2 fun a ha b hb ↦ hG₀ b hb a ha
  have h2 : Subgroup.closure G₀ ≤ Subgroup.centralizer (Subgroup.closure G₀ : Set _) :=
    (Subgroup.closure_le _).2 fun a ha b hb ↦ (h1 hb a ha).symm
  let G := (Subgroup.closure G₀).commGroupTopologicalClosure fun x y ↦
    Subtype.ext (h2 y.2 x x.2)
  have _ := hc
  intro a ha b hb
  exact congrArg Subtype.val (@mul_comm (lineInertiaS S ht W) G.toCommMagma ⟨a, ha⟩ ⟨b, hb⟩)

end Comm

end CurvesJacobian.Cusp
