/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CurveInertiaIsoAny
import CurvesJacobian.Cusp.CoverCusps

/-!
# Finite quotients of `π₁ᵉᵗ(U)` in which a cuspidal inertia generator has order `m`

The cuspidal inertia groups of a hyperbolic curve are isomorphic to `ℤ̂`; what the MR7
uniqueness argument (`LocAn/InnerRigidAffine.lean`, step G3 of the MR7 plan "S2 route") needs
from this is: for every `m > 0` there is a finite étale Galois cover in which the ramification
index at a given cusp is divisible by `m`. Group-theoretically:

* `exists_open_normal_surface_cusp_pow`: `Π̂_{g,r}` (`r ≥ 2` or `g ≥ 1`) has an open normal
  subgroup `V` with `cⱼ ^ n ∈ V → m ∣ n` (pi1's finite quotients `exists_orderOf_cusp_of_two_le`,
  `exists_orderOf_cusp_of_genus_pos`, extended to the completion);
* `exists_open_normal_cuspInertia_pow`: the same for an element of `cuspInertia U W` in
  `π₁ᵉᵗ(U)`, `U` a curve over an algebraically closed field of characteristic `0`, through
  `π₁ᵉᵗ(U) ≃ₜ* Π̂_{g,r}` (`exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed`);
* `exists_open_normal_geomCuspInertia_pow`: the specialisation to `U_Ω` for a hyperbolic curve
  over a number field with a cusp (MR8's arithmetic model).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1.Profinite PreGaloisCategory
open Belyi.Anabelian

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### The surface group -/

section Surface

variable {g r : ℕ}

/-- For `r ≥ 2` or `g ≥ 1`, `Π_{g,r}` has a finite quotient in which `cⱼ` has order `n`. -/
lemma exists_finite_orderOf_cusp (hr : 1 < r ∨ 0 < g) (j : Fin r) (n : ℕ) [NeZero n] :
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (ρ : Pi1.SurfaceGroup g r →* P),
      orderOf (ρ (Pi1.SurfaceGroup.cusp j)) = n := by
  rcases lt_or_ge 1 r with hr2 | hr2
  · obtain ⟨ρ, hρ⟩ := Pi1.SurfaceGroup.exists_orderOf_cusp_of_two_le (g := g) n hr2 j
    exact ⟨_, _, inferInstanceAs (Finite (ZMod n)), ρ, hρ⟩
  · have hg := hr.resolve_left (not_lt.2 hr2)
    obtain rfl : r = 1 := by have := j.pos; omega
    obtain ⟨ρ, hρ⟩ := Pi1.SurfaceGroup.exists_orderOf_cusp_of_genus_pos n hg j
    exact ⟨_, _, inferInstance, ρ, hρ⟩

/-- For `r ≥ 2` or `g ≥ 1` and `m > 0`, `Π̂_{g,r}` has an open normal subgroup `V` such that
`cⱼ ^ n ∈ V` only if `m ∣ n`. -/
theorem exists_open_normal_surface_cusp_pow (hr : 1 < r ∨ 0 < g) (j : Fin r) {m : ℕ}
    (hm : 0 < m) :
    ∃ V : Subgroup (Pi1.ProfiniteSurfaceGroup g r), V.Normal ∧
      IsOpen (V : Set (Pi1.ProfiniteSurfaceGroup g r)) ∧
      ∀ n : ℕ, etaFn (GrpCat.of (Pi1.SurfaceGroup g r)) (Pi1.SurfaceGroup.cusp j) ^ n ∈ V →
        m ∣ n := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨P, _, _, ρ, hρ⟩ := exists_finite_orderOf_cusp hr j m
  refine ⟨(liftFinite ρ).ker, inferInstance, isOpen_liftFinite_fiber ρ 1, fun n hn ↦ ?_⟩
  rw [MonoidHom.mem_ker, map_pow, liftFinite_eta] at hn
  exact hρ ▸ orderOf_dvd_of_pow_eq_one hn

end Surface

/-! ### Curves over an algebraically closed field of characteristic `0` -/

section Main

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] (D : GaloisData k t)
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  (eL : X.functionField ≃+* D.L) (hH : D.H ≤ D.HL)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)

include hk hτ in
/-- **Cuspidal inertia generators of order `m` in a finite quotient.** Let `U ⊆ X` be open with
finite nonempty complement, with at least two cusps or `X` of positive genus, `W ⊇ k` a place
of `Ω` not centred on `U`, and `m > 0`. Then `π₁ᵉᵗ(U)` has an open normal subgroup `V` and an
element `y` of the cuspidal inertia group `cuspInertia U W` such that `y ^ n ∈ V` only if
`m ∣ n` (so the image of `cuspInertia U W` in the finite group `π₁ᵉᵗ(U) / V` has order
divisible by `m`). -/
theorem exists_open_normal_cuspInertia_pow (U : X.Opens) [Nonempty U]
    (hUfin : (U : Set X)ᶜ.Finite) (hUne : (U : Set X)ᶜ.Nonempty)
    (hhyp : 1 < Nat.card ((U : Set X)ᶜ : Set X) ∨ 0 < (curveGenus k X).toNat)
    {W : ValuationSubring Ω} (hkW : ∀ c : k, algebraMap k Ω c ∈ W)
    (hWU : ¬ IsCentredOn D X eL U W) {m : ℕ} (hm : 0 < m) :
    ∃ V : Subgroup π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U), V.Normal ∧
      IsOpen (V : Set π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U)) ∧
      ∃ y ∈ cuspInertia D X eL hH U W, ∀ n : ℕ, y ^ n ∈ V → m ∣ n := by
  obtain ⟨Θ, hΘ⟩ :=
    exists_continuousMulEquiv_cuspInertia_curve_of_isAlgClosed D eL hH hk hτ U hUfin hUne
  obtain ⟨j, σ, hj⟩ := hΘ W hkW hWU
  obtain ⟨V, hVn, hVo, hV⟩ := exists_open_normal_surface_cusp_pow hhyp j hm
  set φ := (Θ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL U) →*
    Pi1.ProfiniteSurfaceGroup (curveGenus k X).toNat (Nat.card ((U : Set X)ᶜ : Set X))).comp
    (MulAut.conj σ).toMonoidHom with hφ
  have hφc : Continuous φ :=
    Θ.continuous.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hmem : etaFn (GrpCat.of (Pi1.SurfaceGroup _ _)) (Pi1.SurfaceGroup.cusp j) ∈
      (cuspInertia D X eL hH U W).map φ := by
    rw [hj]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
  obtain ⟨y, hy, hyx⟩ := hmem
  refine ⟨V.comap φ, hVn.comap φ, hVo.preimage hφc, y, hy, fun n hn ↦ hV n ?_⟩
  rwa [Subgroup.mem_comap, map_pow, hyx] at hn

end Main

/-! ### The geometric curve `U_Ω` of a hyperbolic curve over a number field -/

section Geom

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Cuspidal inertia generators of order `m` in a finite quotient of `π₁ᵉᵗ(U_Ω)`**, for `C` a
hyperbolic curve over a number field `K` with a cusp and `W` a place of `K(X̄_Ω)^alg` over a
cusp: `π₁ᵉᵗ(U_Ω)` has an open normal subgroup `V` and an element `y` of `cuspInertia U_Ω W` with
`y ^ n ∈ V` only if `m ∣ n`. (Hyperbolicity `2 < 2g + r` gives `r ≥ 2` or `g ≥ 1`.) -/
theorem exists_open_normal_geomCuspInertia_pow
    {W : ValuationSubring (FFClosure (geomCurve Ω C))} (hW : IsCuspPlace Ω C hc W)
    {m : ℕ} (hm : 0 < m) :
    ∃ V : Subgroup π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
        genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
          (geomOpen Ω C)), V.Normal ∧
      IsOpen (V : Set π₁ᵉᵗ(specPoint (geomData Ω C).L (FFClosure (geomCurve Ω C)) ≫
        genericL (geomData Ω C) (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
          (geomOpen Ω C))) ∧
      ∃ y ∈ geomCuspInertia Ω C W, ∀ n : ℕ, y ^ n ∈ V → m ∣ n := by
  have hhyp : 2 < 2 * (curveGenus Ω (geomCurve Ω C)).toNat +
      Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)) :=
    isHyperbolic_baseChange Ω C
  have hWU : ¬ IsCentredOn (geomData Ω C) (geomCurve Ω C)
      (curveEquivL Ω (transcendental_geomCoord Ω C)) (geomOpen Ω C) W :=
    fun h ↦ hW.2 ((isCentredOn_geomOpen_iff Ω C hc W).1 h).2
  exact exists_open_normal_cuspInertia_pow (geomData Ω C)
    (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveGaloisData_H_le Ω (transcendental_geomCoord Ω C))
    (curveEquivL_algebraMap Ω _) (curveEquivL_τ Ω _) (geomOpen Ω C)
    (compl_finite_baseChangeOpen K Ω C.nonempty) (compl_nonempty_baseChangeOpen K Ω hc)
    (by omega) hW.1 hWU hm

end Geom

end CurvesJacobian.Cusp
