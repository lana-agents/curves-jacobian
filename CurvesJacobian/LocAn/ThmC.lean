/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.PrincipalDescent
import WeilCurves.Hurwitz.Belyi

/-!
# [LocAn] Theorem C, profinite version: points are determined by their sections

Mochizuki, *The local pro-`p` anabelian geometry of curves* ([LocAn]), Theorem C (§19, txt
l.5050): for a hyperbolic curve `X` over a (sub-)`p`-adic field `K`, the map
`X(K) → Sect(Γ_K, Π_X)` (points to sections, up to `Δ_X`-conjugation) is injective. For the
*profinite* version [LocAn] remarks (l.5116–5118) that it "can be proven much more easily, by
using the 'Kummer exact sequence' for the Jacobian". This file carries out that argument in
`pi1`'s Galois model (`D : GaloisData k t`, `Π_U = Pi D`, `Π_X = PiX D`), over any field `k` of
characteristic `0` for which the Jacobian is Kummer-faithful (`IsKummerFaithfulJac D`,
i.e. `⋂_N N · J(k) = 0`; for a curve with a rational point over a Kummer-faithful field this is
`isKummerFaithfulJac_of_isKummerFaithful`).

Argument. If the sections `s_x, s_y : G_k → Π_X` of two rational points are `Δ_X`-conjugate, then
so are their images `t_x, t_y : G_k → Π_{J¹}`, so the class `η_{x − y} = [t_x − t_y]` vanishes
(`diffClass_eq_one_of_conj`), hence `x − y` is principal on `X_{k̄}` ([AbsTopIII] Prop. 1.6(ii),
`eta_eq_one_iff`; this is where the Kummer sequence of `J` and Kummer-faithfulness enter). A
function with divisor `x − y`, `x ≠ y`, has degree `1`, which forces genus `0`
(`eq_of_div_eq_single_sub_single`).

## Main results

* `WeilCurves.FunctionField.eq_of_div_eq_single_sub_single`: over an algebraically closed field,
  on a function field of genus `≠ 0`, `div u = P − Q` implies `P = Q`;
* `CurvesJacobian.LocAn.xSectionGk`: the section `s_x : G_k → Π_X` of a rational point;
* **`CurvesJacobian.LocAn.placeOfF_eq_of_xSectionGk_conj`** ([LocAn] Thm C, profinite, for the
  proper curve `X`): `Δ_X`-conjugate sections `s_x, s_y` come from the same point of `X`, if the
  geometric genus is `≠ 0` and `J` is Kummer-faithful;
* **`CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj`**: the same for sections of
  `Π_U → G_k` at rational points of the affine curve `U` and `Δ_U`-conjugation;
* `CurvesJacobian.LocAn.placeOfF_eq_of_xSectionGk_conj_curve`,
  `CurvesJacobian.LocAn.placeOfF_eq_of_ratSectionGk_conj_curve`: for the Galois model
  `curveGaloisData k hτ` of a curve `X` with a rational point, with the hypothesis
  `⋂_N N · J(k) = 0` stated on the Jacobian `J(k) = jacPoints X σ hσ k`, and for Kummer-faithful
  `k` (`_of_isKummerFaithful`).

The genus-`0` case (`U ⊆ ℙ¹` with at least three geometric cusps) needs Kummer classes of units
instead of the Jacobian and is not treated here.
-/

universe u

open WeilCurves.FunctionField
open scoped IntermediateField

namespace WeilCurves.FunctionField

open Divisor

/-- **A function with divisor `P − Q` forces genus `0`** (over an algebraically closed field):
if `genus k K ≠ 0` and `div u = P − Q`, then `P = Q`. Otherwise `u` is transcendental with a
single simple pole of degree `1`, so `[K : k(u)] = 1` and `K` has genus `0`. -/
theorem eq_of_div_eq_single_sub_single {k K : Type*} [Field k] [IsAlgClosed k] [Field K]
    [Algebra k K] [IsFunctionField k K] (hg : genus k K ≠ 0) {P Q : Place k K} {u : K}
    (hu : div k u = Finsupp.single P 1 - Finsupp.single Q 1) : P = Q := by
  classical
  by_contra hPQ
  have hord : ∀ R : Place k K, R.ord u = (if R = P then 1 else 0) - (if R = Q then 1 else 0) := by
    intro R
    rw [← div_apply, hu, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp only [eq_comm]
  have hQ : Q.ord u = -1 := by
    rw [hord, if_neg (Ne.symm hPQ), if_pos rfl]; rfl
  have ht : Transcendental k u := fun h => by
    have := (Place.isAlgebraic_iff_forall_ord_eq_zero.1 h) Q
    omega
  have hsum := Place.sum_ord_mul_deg_poles u ht
  have hT : (Place.finite_setOf_ord_neg (k := k) u).toFinset = {Q} := by
    ext R
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
    rw [hord]
    by_cases hRQ : R = Q
    · subst hRQ
      simp [Ne.symm hPQ]
    · by_cases hRP : R = P
      · subst hRP
        simp [hRQ]
      · simp [hRQ, hRP]
  rw [hT, Finset.sum_singleton, hQ, Place.deg_eq_one] at hsum
  have h1 : Module.finrank k⟮u⟯ K = 1 := by
    have h2 : ((Module.finrank k⟮u⟯ K : ℕ) : ℤ) = 1 := by rw [← hsum]; norm_num
    exact_mod_cast h2
  exact hg (genus_eq_zero_of_finrank_eq_one ell_zero_eq_one_of_isAlgClosed ht h1)

end WeilCurves.FunctionField

namespace CurvesJacobian.LocAn

open CurvesJacobian.Kummer KummerTheory Curve AffOrbicurve

section General

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

/-- **The section `s_x : G_k → Π_X` of a rational point**, `xSection` transported along
`G_k ≅ Gal(κ(A)/k)` (`kbarEquiv`). Its image in `Π_{J¹}` is `t_x` (`tSection_toHom`). -/
noncomputable def xSectionGk (x : RatPoint D) : Gk k Ω →* PiX D :=
  (xSection x).comp (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).toMonoidHom

theorem tSection_toHom (x : RatPoint D) (g : Gk k Ω) :
    (tSection x).toHom g = piXToPiJ1 D (xSectionGk x g) := rfl

/-- `s_x` is a section of `Π_X → G_k`. -/
theorem piXToGk_xSectionGk (x : RatPoint D) (g : Gk k Ω) : piXToGk D (xSectionGk x g) = g := by
  have h := (tSection x).piJ1ToGk_toHom g
  rwa [tSection_toHom, piJ1ToGk_piXToPiJ1] at h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- `Δ_X`-conjugate sections of rational points have trivial difference class in
`H¹(G_k, Δ_X^{ab})`. -/
theorem diffClass_tSection_eq_one_of_conj [Fact (Function.Surjective (piJ1ToGk D))]
    {x y : RatPoint D} {δ : PiX D} (hδ : δ ∈ DeltaX D)
    (h : ∀ g, xSectionGk y g = δ * xSectionGk x g * δ⁻¹) :
    diffClass (tSection x) (tSection y) = 1 := by
  refine diffClass_eq_one_of_conj _ _ (q := piXToPiJ1 D δ) ?_ fun g => ?_
  · rw [MonoidHom.mem_ker, piJ1ToGk_piXToPiJ1]
    exact hδ
  · rw [tSection_toHom, tSection_toHom, h, map_mul, map_mul, map_inv]

/-- `η_{x − y} = [t_x − t_y]`. -/
theorem eta_single_sub_single [Fact (Function.Surjective (piJ1ToGk D))] (x y : RatPoint D) :
    eta (Finsupp.single x 1 - Finsupp.single y 1) = diffClass (tSection x) (tSection y) := by
  have hf : ((Finsupp.single x 1 - Finsupp.single y 1 : RatPoint D →₀ ℤ).sum
      fun _ m => m) = 0 := by
    rw [sub_eq_add_neg, ← Finsupp.single_neg, Finsupp.sum_add_index' (fun _ => rfl)
      (fun _ _ _ => rfl), Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    norm_num
  rw [eta_eq_etaDiv _ hf y, etaDiv, etaWith, sub_eq_add_neg, ← Finsupp.single_neg,
    Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _),
    Finsupp.prod_single_index (zpow_zero _), Finsupp.prod_single_index (zpow_zero _),
    diffClass_self, one_zpow, mul_one, zpow_one]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
theorem sum_single_sub_single (x y : RatPoint D) :
    ((Finsupp.single x 1 - Finsupp.single y 1 : RatPoint D →₀ ℤ).sum fun _ m => m) = 0 := by
  rw [sub_eq_add_neg, ← Finsupp.single_neg, Finsupp.sum_add_index' (fun _ => rfl)
    (fun _ _ _ => rfl), Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  norm_num

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for a proper curve, generic Galois model**: if the sections
`s_x, s_y : G_k → Π_X` of two rational points are `Δ_X`-conjugate, then `x` and `y` are the same
point of `X`, provided `X_{k̄}` has genus `≠ 0` and the Jacobian is Kummer-faithful. The other
hypotheses (divisibility of `J(k̄)`, perfectness of the Weil pairing, finiteness of `J[N]`) are
those of `eta_eq_one_iff`; for curves they are discharged in
`placeOfF_eq_of_xSectionGk_conj_curve`. -/
theorem placeOfF_eq_of_xSectionGk_conj [Fact (Function.Surjective (piJ1ToGk D))]
    (hKF : IsKummerFaithfulJac D)
    (hdivJ : ∀ N : ℕ, 0 < N → ∀ y : Pic (kbar k Ω) (F (baseChange D)), Pic.deg _ _ y = 0 →
      ∃ w, N • w = y)
    (hperf : ∀ (N : ℕ) [NeZero N],
      Function.Bijective (weilDual (κ := kbar k Ω) (K := F (baseChange D)) (n := N)))
    (hfin : ∀ (N : ℕ) [NeZero N], Finite (picTorsion (kbar k Ω) (F (baseChange D)) N))
    (hg : genus (kbar k Ω) (F (baseChange D)) ≠ 0)
    {x y : RatPoint D} {δ : PiX D} (hδ : δ ∈ DeltaX D)
    (h : ∀ g, xSectionGk y g = δ * xSectionGk x g * δ⁻¹) :
    placeOfF x = placeOfF y := by
  have he : eta (Finsupp.single x 1 - Finsupp.single y 1) = 1 := by
    rw [eta_single_sub_single, diffClass_tSection_eq_one_of_conj hδ h]
  have hp := (eta_eq_one_iff hKF hdivJ hperf hfin _ (sum_single_sub_single x y)).1 he
  rw [QuotientAddGroup.eq_zero_iff] at hp
  obtain ⟨u, -, hu⟩ := mem_principal.1 hp
  rw [ratDiv, Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single] at hu
  exact (placeOf_eq_placeOf_iff y x).1 (eq_of_div_eq_single_sub_single hg hu)

/-- **The section `G_k → Π_U` of a rational point of `U`** (`t ∈ A`, `H_L = H`):
continuous-kummer-theory's `ratSectionMap` transported along `G_k ≅ Gal(κ(A)/k)`. -/
noncomputable def ratSectionGk (x : RatPoint D) (hHL : D.HL = D.H) (ht : t ∈ x.A) :
    Gk k Ω →* Pi D :=
  (ratSectionMap D x.A x.hk x.hkres x.hrat hHL ht).comp
    (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).toMonoidHom

theorem piUToPiX_ratSectionGk (x : RatPoint D) (hHL : D.HL = D.H) (ht : t ∈ x.A) (g : Gk k Ω) :
    piUToPiX D (ratSectionGk x hHL ht g) = xSectionGk x g :=
  piUToPiX_ratSectionMap x hHL ht _

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- `Δ_U`-conjugate sections of `Π_U → G_k` have `Δ_X`-conjugate images in `Π_X`. -/
theorem xSectionGk_conj_of_ratSectionGk_conj (hHL : D.HL = D.H) {x y : RatPoint D}
    (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D} (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹) :
    piUToPiX D δ ∈ DeltaX D ∧
      ∀ g, xSectionGk y g = piUToPiX D δ * xSectionGk x g * (piUToPiX D δ)⁻¹ := by
  refine ⟨?_, fun g => ?_⟩
  · change piXToGk D (piUToPiX D δ) = 1
    rw [piXToGk_piUToPiX]
    exact hδ
  · rw [← piUToPiX_ratSectionGk x hHL hx, ← piUToPiX_ratSectionGk y hHL hy, h, map_mul, map_mul,
      map_inv]

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for the affine curve `U`, generic Galois model**: rational points
of `U` with `Δ_U`-conjugate sections of `Π_U → G_k` are the same point. -/
theorem placeOfF_eq_of_ratSectionGk_conj [Fact (Function.Surjective (piJ1ToGk D))]
    (hKF : IsKummerFaithfulJac D)
    (hdivJ : ∀ N : ℕ, 0 < N → ∀ y : Pic (kbar k Ω) (F (baseChange D)), Pic.deg _ _ y = 0 →
      ∃ w, N • w = y)
    (hperf : ∀ (N : ℕ) [NeZero N],
      Function.Bijective (weilDual (κ := kbar k Ω) (K := F (baseChange D)) (n := N)))
    (hfin : ∀ (N : ℕ) [NeZero N], Finite (picTorsion (kbar k Ω) (F (baseChange D)) N))
    (hg : genus (kbar k Ω) (F (baseChange D)) ≠ 0) (hHL : D.HL = D.H)
    {x y : RatPoint D} (hx : t ∈ x.A) (hy : t ∈ y.A) {δ : Pi D} (hδ : δ ∈ (piToGk D).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  let h' := xSectionGk_conj_of_ratSectionGk_conj hHL hx hy hδ h
  placeOfF_eq_of_xSectionGk_conj hKF hdivJ hperf hfin hg h'.1 h'.2

end General

/-! ### Curves -/

section Curve

open AlgebraicGeometry Belyi CurvesJacobian.Cusp CategoryTheory

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for a proper curve `X`** with a rational point `σ` (Galois model
`curveGaloisData k hτ`): if `⋂_{N ≥ 1} N · J(k) = 0` for the Jacobian `J(k) = jacPoints X σ hσ k`
(Kummer-faithfulness of `J`; for `k` finite over `ℚ_p` this is the statement of [AbsTopIII]
Rem. 1.5.4(i) for `J`) and `X_{k̄}` has genus `≠ 0`, then rational points with `Δ_X`-conjugate
sections `s_x, s_y : G_k → Π_X` are equal. -/
theorem placeOfF_eq_of_xSectionGk_conj_curve (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hJ : ∀ z ∈ jacPoints X σ hσ k,
      (∀ N : ℕ, 0 < N → ∃ y ∈ jacPoints X σ hσ k, N • y = z) → z = 0)
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {x y : RatPoint (curveGaloisData k hτ)} {δ : PiX (curveGaloisData k hτ)}
    (hδ : δ ∈ DeltaX (curveGaloisData k hτ))
    (h : ∀ g, xSectionGk y g = δ * xSectionGk x g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  placeOfF_eq_of_xSectionGk_conj (isKummerFaithfulJac_curveGaloisData k hτ σ hσ hJ)
    (fun N hN y hy => by
      obtain ⟨w, hw⟩ := exists_nsmul_eq_jacPsi k hτ σ hσ hN.ne' ⟨y, hy⟩
      exact ⟨w, congrArg Subtype.val hw⟩)
    (fun N _ => weilDual_bijective_baseChange k hτ)
    (fun N _ => finite_picTorsion_baseChange k hτ) hg hδ h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for a proper curve over a Kummer-faithful field** (e.g. a number
field or a finite extension of `ℚ_p`, once their Kummer-faithfulness is available). -/
theorem placeOfF_eq_of_xSectionGk_conj_of_isKummerFaithful (hk : IsKummerFaithful k)
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    {x y : RatPoint (curveGaloisData k hτ)} {δ : PiX (curveGaloisData k hτ)}
    (hδ : δ ∈ DeltaX (curveGaloisData k hτ))
    (h : ∀ g, xSectionGk y g = δ * xSectionGk x g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  placeOfF_eq_of_xSectionGk_conj_curve k hτ σ hσ (jacPoints_eq_zero_of_isKummerFaithful X σ hσ hk)
    hg hδ h

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_X`, `Π_U` is found slowly
/-- **[LocAn] Thm C (profinite) for the affine curve `U = Spec R`** (Galois model
`curveGaloisData k hτ`, `t ∈ A` for the points, `H_L = H`): rational points of `U` whose sections
of `Π_U → G_k` are `Δ_U`-conjugate are equal, if `⋂_N N · J(k) = 0` and the compactification has
geometric genus `≠ 0`. -/
theorem placeOfF_eq_of_ratSectionGk_conj_curve (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hJ : ∀ z ∈ jacPoints X σ hσ k,
      (∀ N : ℕ, 0 < N → ∃ y ∈ jacPoints X σ hσ k, N • y = z) → z = 0)
    (hg : genus (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) ≠ 0)
    (hHL : (curveGaloisData k hτ).HL = (curveGaloisData k hτ).H)
    {x y : RatPoint (curveGaloisData k hτ)} (hx : coordT τ ∈ x.A) (hy : coordT τ ∈ y.A)
    {δ : Pi (curveGaloisData k hτ)} (hδ : δ ∈ (piToGk (curveGaloisData k hτ)).ker)
    (h : ∀ g, ratSectionGk y hHL hy g = δ * ratSectionGk x hHL hx g * δ⁻¹) :
    placeOfF x = placeOfF y :=
  let h' := xSectionGk_conj_of_ratSectionGk_conj hHL hx hy hδ h
  placeOfF_eq_of_xSectionGk_conj_curve k hτ σ hσ hJ hg h'.1 h'.2

end Curve

end CurvesJacobian.LocAn
