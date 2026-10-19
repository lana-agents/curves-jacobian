/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianPi1
import CurvesJacobian.Cusp.PlaceTransitivity

/-!
# `t_x` does not depend on the place above `x` (up to `Δ_X`-conjugation)

Setting of `Kummer/JacobianPi1.lean` ([Cusp] §2, [AbsTopIII] Prop. 1.6(ii)). A `k`-rational point
`x` of `X` is given there by a place `A` of `Ω` above it (`RatPoint`), and
`t_x : G_k → Π_{J¹}` (`tSection`) is built from the decomposition group `D_A`. Here:

* `CurvesJacobian.Kummer.tSection_hToGk`: **`t_x(g) = [τ]`** for every `τ ∈ D_A` acting on `k̄`
  as `g` (the image of `τ` in `Π_{J¹}`), and `exists_hToGk_eq` (every `g ∈ G_k` is the action on
  `k̄` of some `τ ∈ D_A`);
* **`CurvesJacobian.Kummer.exists_tSection_conj`**: if the places `A, A'` of two rational points
  restrict to the same place of `F` (the same point of `X`), then `t_{x'} = q t_x q⁻¹` for some
  `q ∈ Δ_X^{ab} = ker(Π_{J¹} → G_k)`. Proof: `A' = ρ(A)` for some `ρ ∈ Gal(Ω/F)`
  (`Cusp.exists_algEquiv_comap_eq`), so `D_{A'} = ρ D_A ρ⁻¹` and
  `t_{x'}(g) = [ρ] t_x(ρ̄⁻¹ g ρ̄) [ρ]⁻¹` (`ρ̄` the action of `ρ` on `k̄`); take `q = [ρ] t_x(ρ̄)⁻¹`;
* `CurvesJacobian.Kummer.diffClass_tSection_eq_one`: hence `[t_x − t_{x'}] = 0` in
  `H¹(G_k, Δ_X^{ab})`, so the classes `η_D` only depend on the points of `X`.
-/

open KummerTheory Curve AffOrbicurve IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CurvesJacobian.Kummer

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- `D_A → Gal(κ(A)/k)` is the action on `k̄` transported along `k̄ ≅ κ(A)`. -/
theorem autCongr_hToGk_ofGalF (x : RatPoint D) (τ : x.A.decompositionSubgroup (F D)) :
    AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) (hToGk D (ofGalF D τ.1)) =
      Decomposition.decompositionMap (F D) x.A x.hk x.hkres τ := by
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := (kbarEquiv x.A x.hk x.hkres).surjective y
  rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, kbarEquiv_apply, kbarEquiv_apply]
  exact kbarResidue_piToGk_decompToPi D x.A x.hk x.hkres τ z

/-- **`t_x(g) = [τ]`** for `τ ∈ D_A` acting on `k̄` as `g`. -/
theorem tSection_hToGk (x : RatPoint D) (τ : x.A.decompositionSubgroup (F D)) :
    (tSection x).toHom (hToGk D (ofGalF D τ.1)) = piXToPiJ1 D (decompToPiX D x.A τ) := by
  rw [tSection_apply, autCongr_hToGk_ofGalF, xSection_decompositionMap]

/-- Every `g ∈ G_k` is the action on `k̄` of an element of the decomposition group `D_A` of a
rational point. -/
theorem exists_hToGk_eq (x : RatPoint D) (g : Gk k Ω) :
    ∃ τ : x.A.decompositionSubgroup (F D), hToGk D (ofGalF D τ.1) = g := by
  obtain ⟨τ, hτ⟩ := x.decompositionMap_surjective
    (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g)
  exact ⟨τ, (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).injective
    ((autCongr_hToGk_ofGalF x τ).trans hτ)⟩

/-- `decompToPiX` is the image of the element of `H`. -/
theorem decompToPiX_apply (A : ValuationSubring Ω) (τ : A.decompositionSubgroup (F D)) :
    decompToPiX D A τ = ((ofGalF D τ.1 : D.H) : PiX D) := rfl

/-- **`t_x` does not depend on the place above `x`, up to `Δ_X`-conjugation**: if the places of
two rational points `x, x'` restrict to the same place of `F`, then `t_{x'} = q t_x q⁻¹` with
`q ∈ ker(Π_{J¹} → G_k) = Δ_X^{ab}`. -/
theorem exists_tSection_conj (x x' : RatPoint D)
    (h : x.A.comap (algebraMap (F D) Ω) = x'.A.comap (algebraMap (F D) Ω)) :
    ∃ q ∈ (piJ1ToGk D).ker, ∀ g, (tSection x').toHom g = q * (tSection x).toHom g * q⁻¹ := by
  haveI : IsGalois (F D) Ω := IsGalois.tower_top_of_isGalois (K₀ k t) (F D) Ω
  obtain ⟨ρ, hρ⟩ := Cusp.exists_algEquiv_comap_eq x.A x'.A h
  have hA' : x'.A = ρ • x.A := by
    rw [hρ]
    ext a
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  set r : PiJ1 D := piXToPiJ1 D ((ofGalF D ρ : D.H) : PiX D) with hr
  set ρb : Gk k Ω := hToGk D (ofGalF D ρ) with hρb
  have hrG : piJ1ToGk D r = ρb := by
    rw [hr, piJ1ToGk_piXToPiJ1, piXToGk_mk]
  refine ⟨r * ((tSection x).toHom ρb)⁻¹, ?_, fun g => ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, (tSection x).piJ1ToGk_toHom, hrG, mul_inv_cancel]
  obtain ⟨τ, hτ⟩ := exists_hToGk_eq x (ρb⁻¹ * g * ρb)
  have hmem : ρ * τ.1 * ρ⁻¹ ∈ x'.A.decompositionSubgroup (F D) := by
    change (ρ * τ.1 * ρ⁻¹) • x'.A = x'.A
    have hτA : τ.1 • x.A = x.A := τ.2
    rw [hA', mul_smul, mul_smul, inv_smul_smul, hτA]
  have hg : hToGk D (ofGalF D (ρ * τ.1 * ρ⁻¹)) = g := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← hρb, hτ]
    group
  have key := tSection_hToGk x' ⟨_, hmem⟩
  rw [hg] at key
  have key' := tSection_hToGk x τ
  rw [hτ, decompToPiX_apply] at key'
  rw [key, decompToPiX_apply, map_mul, map_mul, map_inv, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv, ← hr, ← key',
    map_mul, map_mul, map_inv]
  group

/-- **The difference class of two choices of `t_x` vanishes**: places above the same point of
`X` give the same class in `H¹(G_k, Δ_X^{ab})`. -/
theorem diffClass_tSection_eq_one [Fact (Function.Surjective (piJ1ToGk D))] (x x' : RatPoint D)
    (h : x.A.comap (algebraMap (F D) Ω) = x'.A.comap (algebraMap (F D) Ω)) :
    diffClass (tSection x) (tSection x') = 1 := by
  obtain ⟨q, hq, hconj⟩ := exists_tSection_conj x x' h
  exact diffClass_eq_one_of_conj _ _ hq hconj

end CurvesJacobian.Kummer
