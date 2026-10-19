/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.PrincipalEta

/-!
# Descent of principality from `X_{k̄}` to `X` ([AbsTopIII] Prop. 1.6(ii))

Galois model `D : GaloisData k t` of a proper curve `X/k` (`char k = 0`), `F = F D` the function
field of `X` (a function field over `k`, `isFunctionField_F`) and `F k̄ = F (baseChange D)` the
function field of `X_{k̄}`. A divisor of `X` supported on `k`-rational points is
`ratDivF f = ∑ nᵢ xᵢ` (`f : RatPoint D →₀ ℤ`), its pull-back to `X_{k̄}` is `ratDiv f`.

* `ιF D : F → F k̄`; `placeOfF x`, the place of `F` below a rational point (residue field `k`);
* **`ord_placeOf_ιF`**: `ord_{x_{k̄}}(u) = ord_x(u)` for `u ∈ F` — the constant field extension is
  unramified at rational points. Proof: a uniformiser `π` of `x` with `ord_{x_{k̄}} π = e ≥ 2`
  would be `ρ^e w` with `ρ ∈ F k̄` and `w` a unit; the tame character of `π`
  (`exists_inertia_tameChar`) gives `σ ∈ I_A ∩ H` with `σ(π^{1/e}) = ζ_e π^{1/e}`; `σ` fixes `k̄`
  (`inertia_fix_algebraic`), hence `F k̄` and `ρ`, so `σ` multiplies the unit `π^{1/e}/ρ` by
  `ζ_e`, impossible in the inertia group (`eq_of_mem_inertia`);
* **`eq_placeOf_of_liesOver`**: `x_{k̄}` is the only place of `F k̄` above `x` (two places of `Ω`
  above `x` are `Gal(Ω/F)`-conjugate, `Cusp.exists_algEquiv_comap_eq`, and `D_A ↠ G_k`);
* **`div_ιF_eq_ratDiv_iff`**: `div_{F k̄} u = ratDiv f ⟺ div_F u = ratDivF f` for `u ∈ Fˣ`;
* **`exists_mem_F_of_div_eq_ratDiv`** (descent, Hilbert 90): if `div_{F k̄} g = ratDiv f`, then
  `h(g)/g ∈ k̄ˣ` for `h ∈ H` (the divisor is `H`-invariant), `σ ↦ h_σ(g)/g` is a continuous
  `1`-cocycle of `G_k` (`hToGk` is open on the stabiliser of `g`), hence `= σ(β)/β`
  (`isMulCoboundary₁_of_eventually_eq_one`), and `g/β ∈ (F k̄)^H = F`;
* **`mk_ratDiv_eq_zero_iff`**: `[ratDiv f] = 0` in `Pic(X_{k̄})` iff `ratDivF f` is principal
  on `X`;
* `eta_eq_one_iff_exists_conj`: `η_D = 0` iff `σ ↦ ∏ (t_{xᵢ}(σ) t_{x₀}(σ)⁻¹)^{nᵢ}` is
  `σ ↦ q σ(q)⁻¹` for some `q ∈ Δ_X^{ab}` (`t_D` is `Δ_X`-conjugate to the identity section);
* **`eta_eq_one_iff_principal`**, **`eta_eq_one_iff_principal_curve`** and
  **`tD_conj_identity_iff_principal_curve`**: [AbsTopIII] Prop. 1.6(ii) (T3 l.1993–2000) as stated
  there: for a degree-`0` divisor `D` on `X` supported on `X(k)`, `t_D` coincides up to
  `Δ_X`-conjugation with the identity section iff `D` is principal (on `X`, over `k`);
  [Cusp] Prop. 2.3(i) (txt l.2077–2104).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CurvesJacobian.Kummer

universe u

section General

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] isFunctionField_F

variable (D) in
/-- `F ⊆ F k̄` as a ring homomorphism. -/
def ιF : F D →+* F (baseChange D) where
  toFun u := ⟨u, le_F_baseChange D u.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[simp]
lemma coe_ιF (u : F D) : ((ιF D u : F (baseChange D)) : Ω) = u :=
  -- not `rfl`: the kernel would compare the two `Subtype.val`s' predicates first
  Subtype.coe_mk _ _

/-- The place of `Ω` of a rational point does not contain `F`. -/
lemma RatPoint.comapF_ne_top (x : RatPoint D) : x.A.comap (algebraMap (F D) Ω) ≠ ⊤ := by
  intro htop
  have hF : ∀ y : F D, (y : Ω) ∈ x.A := fun y => by
    have : y ∈ x.A.comap (algebraMap (F D) Ω) := by rw [htop]; trivial
    exact this
  -- `t - c ∈ F` has residue `0` but is a unit of `A`
  have htF : t ∈ F D := (F D).algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩
  obtain ⟨c, hc⟩ := x.hrat ⟨t, htF⟩ (hF ⟨t, htF⟩)
  set w := t - algebraMap k Ω c with hw
  have hw0 : w ≠ 0 := by
    intro h0
    rw [hw, sub_eq_zero] at h0
    exact (D.transcendental (h0 ▸ isAlgebraic_algebraMap c)).elim
  have hwF : w ∈ F D := sub_mem htF ((F D).algebraMap_mem (algebraMap k (K₀ k t) c))
  have hwA : w ∈ x.A := hF ⟨w, hwF⟩
  have hwm : (⟨w, hwA⟩ : x.A) ∈ maximalIdeal x.A := by
    rw [← residue_eq_zero_iff]
    have : residue x.A ⟨w, hwA⟩ =
        residue x.A ⟨t, hF ⟨t, htF⟩⟩ - residue x.A ⟨algebraMap k Ω c, x.hk c⟩ := by
      rw [← map_sub]; rfl
    rw [this, hc, RatPoint.hkres, sub_self]
  have hwi : w⁻¹ ∈ x.A := hF ⟨w⁻¹, inv_mem hwF⟩
  have hunit : IsUnit (⟨w, hwA⟩ : x.A) :=
    isUnit_iff_exists_inv.2 ⟨⟨w⁻¹, hwi⟩, Subtype.ext (mul_inv_cancel₀ hw0)⟩
  exact ((mem_maximalIdeal _).1 hwm hunit).elim

/-- **The place `x` of `F` (a `k`-rational point of `X`) below the place of a rational point.** -/
noncomputable def placeOfF (x : RatPoint D) : Place k (F D) :=
  ⟨x.A.comap (algebraMap (F D) Ω), x.comapF_ne_top, fun c => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact x.hk c⟩

lemma mem_placeOfF {x : RatPoint D} {u : F D} : u ∈ (placeOfF x).1 ↔ (u : Ω) ∈ x.A := Iff.rfl

lemma ιF_mem_placeOf {x : RatPoint D} {u : F D} : ιF D u ∈ (placeOf x).1 ↔ u ∈ (placeOfF x).1 := by
  rw [mem_placeOf, coe_ιF, mem_placeOfF]

/-- **The divisor `∑ nᵢ xᵢ` of `X`** for `f = ∑ nᵢ [xᵢ]` supported on rational points. -/
noncomputable def ratDivF (f : RatPoint D →₀ ℤ) : Divisor k (F D) :=
  Finsupp.mapDomain placeOfF f

/-! ### `x_{k̄}` is the only place of `F k̄` above `x` -/

lemma coe_autF_symm_apply (h : D.H) (y : F (baseChange D)) :
    ((((autF D h : F (baseChange D) ≃+* F (baseChange D)).symm y : F (baseChange D)) : Ω)) =
      (h : Ω ≃ₐ[K₀ k t] Ω).symm y := rfl

/-- Every `h ∈ H` fixes the place `x_{k̄}` (it acts on `F k̄` as an element of `D_A`). -/
lemma placeMap_autF_placeOf' (h : D.H) (x : RatPoint D) :
    placeMap (autF D h) (placeOf x) = placeOf x := by
  obtain ⟨τ, hτ⟩ := exists_hToGk_eq x (hToGk D h)
  rw [← autF_eq_of_hToGk_eq hτ, placeMap_autF_placeOf]

/-- **`x_{k̄}` is the only place of `F k̄` above the rational point `x`**: two places of `Ω` above
`x` are `Gal(Ω/F)`-conjugate, and `Gal(Ω/F)` acts on `F k̄` through `D_A`. -/
theorem eq_placeOf_of_liesOver (x : RatPoint D) (Q : Place (kbar k Ω) (F (baseChange D)))
    (hQ : ∀ u : F D, ιF D u ∈ Q.1 ↔ u ∈ (placeOfF x).1) : Q = placeOf x := by
  haveI : IsGalois (F D) Ω := IsGalois.tower_top_of_isGalois (K₀ k t) (F D) Ω
  obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver (baseChange D) Q
  have hc : x.A.comap (algebraMap (F D) Ω) = W.comap (algebraMap (F D) Ω) := by
    ext u
    have h1 := hW (ιF D u)
    rw [coe_ιF] at h1
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, IntermediateField.algebraMap_apply,
      h1, hQ, mem_placeOfF]
  obtain ⟨ρ, hρ⟩ := Cusp.exists_algEquiv_comap_eq x.A W hc
  have key : Q = placeMap (autF D (ofGalF D ρ)) (placeOf x) := by
    apply Place.ext
    ext y
    rw [← hW, mem_placeMap, mem_placeOf, hρ, ValuationSubring.mem_comap, coe_autF_symm_apply]
    have : ((ofGalF D ρ : D.H) : Ω ≃ₐ[K₀ k t] Ω).symm y = ρ.symm y := by
      rw [AlgEquiv.symm_apply_eq, ofGalF_apply, AlgEquiv.apply_symm_apply]
    rw [this]
    rfl
  rw [key, placeMap_autF_placeOf']

lemma placeOf_eq_placeOf_iff (x y : RatPoint D) :
    placeOf y = placeOf x ↔ placeOfF y = placeOfF x := by
  constructor
  · intro h
    apply Place.ext
    ext u
    rw [← ιF_mem_placeOf, ← ιF_mem_placeOf, h]
  · intro h
    exact eq_placeOf_of_liesOver x (placeOf y) fun u => by rw [ιF_mem_placeOf, h]

lemma ratDiv_apply_placeOf (f : RatPoint D →₀ ℤ) (x : RatPoint D) :
    ratDiv f (placeOf x) = ratDivF f (placeOfF x) := by
  classical
  rw [ratDiv, ratDivF, Finsupp.mapDomain, Finsupp.mapDomain, Finsupp.sum_apply,
    Finsupp.sum_apply]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : placeOfF y = placeOfF x
  · rw [if_pos h, if_pos ((placeOf_eq_placeOf_iff x y).2 h)]
  · rw [if_neg h, if_neg fun h' => h ((placeOf_eq_placeOf_iff x y).1 h')]

lemma ratDiv_apply_of_forall_ne (f : RatPoint D →₀ ℤ) {Q : Place (kbar k Ω) (F (baseChange D))}
    (hQ : ∀ x, placeOf x ≠ Q) : ratDiv f Q = 0 :=
  Finsupp.mapDomain_notin_range _ _ fun ⟨x, hx⟩ => hQ x hx

lemma ratDivF_apply_of_forall_ne (f : RatPoint D →₀ ℤ) {P : Place k (F D)}
    (hP : ∀ x, placeOfF x ≠ P) : ratDivF f P = 0 :=
  Finsupp.mapDomain_notin_range _ _ fun ⟨x, hx⟩ => hP x hx

/-! ### The constant field extension is unramified at rational points -/

/-- **A uniformiser at a rational point `x` stays a uniformiser at `x_{k̄}`.** -/
theorem ord_placeOf_ιF_of_ord_eq_one (x : RatPoint D) {π : F D}
    (hπ1 : (placeOfF x).ord π = 1) : (placeOf x).ord (ιF D π) = 1 := by
  set P := placeOfF x with hP
  set Q := placeOf x with hQ
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  have hπmem : π ∈ P.1 ∧ π⁻¹ ∉ P.1 := by
    refine ⟨P.mem_of_ord_nonneg (by rw [hπ1]; norm_num), fun h ↦ ?_⟩
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, hπ1] at this
    norm_num at this
  have hιπ0 : ιF D π ≠ 0 := (map_ne_zero _).2 hπ0
  -- `e = ord_Q π ≥ 1`
  have hpos : 0 < Q.ord (ιF D π) := by
    have h0 := Q.ord_nonneg_of_mem (ιF_mem_placeOf.2 hπmem.1)
    rcases h0.lt_or_eq with h | h
    · exact h
    · refine absurd ((Q.ord_eq_zero_iff hιπ0).1 h.symm).2 fun h' => hπmem.2 ?_
      rw [← map_inv₀] at h'
      exact ιF_mem_placeOf.1 h'
  by_contra hne
  set n : ℕ := (Q.ord (ιF D π)).toNat with hn
  have hnZ : (n : ℤ) = Q.ord (ιF D π) := Int.toNat_of_nonneg hpos.le
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨hn0.ne'⟩
  -- a uniformiser `ρ` of `Q` and the unit `w = π / ρⁿ`
  obtain ⟨ρ, hρ⟩ := Q.exists_ord_eq_one
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at hρ
  set w : F (baseChange D) := ιF D π / ρ ^ n with hw
  have hw0 : w ≠ 0 := div_ne_zero hιπ0 (pow_ne_zero _ hρ0)
  have hword : Q.ord w = 0 := by
    rw [hw, Q.ord_div hιπ0 (pow_ne_zero _ hρ0), Q.ord_pow, hρ, ← hnZ]
    ring
  obtain ⟨hw1, hw2⟩ := (Q.ord_eq_zero_iff hw0).1 hword
  have hwA : (w : Ω) ∈ x.A := mem_placeOf.1 hw1
  have hwA' : ((w : Ω))⁻¹ ∈ x.A := by
    have := mem_placeOf.1 hw2
    rwa [IntermediateField.coe_inv] at this
  have hwΩ : (w : Ω) = (π : Ω) / (ρ : Ω) ^ n := by
    rw [hw, IntermediateField.coe_div, IntermediateField.coe_pow, coe_ιF]
  -- an `n`-th root `α` of `π` and a primitive `n`-th root of unity `ζ`
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (π : Ω) hn0
  -- `π` is a uniformiser of `A ∩ F`
  have hW : ∀ u : F D, ((u : F D) : Ω) ∈ x.A ↔ u ∈ P.1 := fun u => mem_placeOfF.symm
  have hπΩ0 : ((π : F D) : Ω) ≠ 0 := fun h ↦ hπ0 (Subtype.ext h)
  have hπW : x.A.valuation ((π : F D) : Ω) < 1 := (valuation_lt_one_iff hW hπ0).2 hπmem
  have hπunif : ∀ f ∈ F D, x.A.valuation f < 1 → x.A.valuation f ≤ x.A.valuation (π : Ω) := by
    intro f hf hlt
    set y : F D := ⟨f, hf⟩
    rcases eq_or_ne y 0 with hy0 | hy0
    · have : f = 0 := congrArg Subtype.val hy0
      rw [this, map_zero]; exact zero_le
    obtain ⟨hyP, hyP'⟩ := (valuation_lt_one_iff hW hy0).1 hlt
    have hord : 1 ≤ P.ord y := by
      have h0 := P.ord_nonneg_of_mem hyP
      rcases (show P.ord y = 0 ∨ 1 ≤ P.ord y by omega) with h | h
      · exact absurd ((P.ord_eq_zero_iff hy0).1 h).2 hyP'
      · exact h
    have hdiv : y / π ∈ P.1 := P.mem_of_ord_nonneg (by rw [P.ord_div hy0 hπ0, hπ1]; omega)
    have hdivW := (x.A.valuation_le_one_iff _).2 ((hW _).2 hdiv)
    rw [IntermediateField.coe_div, map_div₀] at hdivW
    have hπv : x.A.valuation ((π : F D) : Ω) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hπΩ0
    exact (div_le_one₀ (zero_lt_iff.2 hπv)).1 hdivW
  -- the tame character: `σ ∈ I_A ∩ H` with `σ α = ζ α`
  obtain ⟨σ, hσI, hσα⟩ := exists_inertia_tameChar (D := D) x.hk π.2 hπΩ0 hπW hπunif hn0 hα
    (hζ.pow_eq_one)
  have hσk : ∀ z ∈ kbar k Ω, (σ : Ω ≃ₐ[K₀ k t] Ω) z = z := fun z hz =>
    inertia_fix_algebraic x.hk hσI (mem_algebraicClosure_iff.mp hz)
  have hσρ : (σ : Ω ≃ₐ[K₀ k t] Ω) ρ = ρ := fixes_F_baseChange D σ.2 hσk ρ.2
  -- `β = α / ρ` is a unit of `A` multiplied by `ζ` under `σ`
  have hρΩ0 : (ρ : Ω) ≠ 0 := fun h ↦ hρ0 (Subtype.ext h)
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0.ne'] at hα
    exact hπΩ0 hα.symm
  set β : Ω := α / ρ with hβ
  have hβ0 : β ≠ 0 := div_ne_zero hα0 hρΩ0
  have hβn : β ^ n = (w : Ω) := by rw [hβ, div_pow, hα, hwΩ]
  have hβA : β ∈ x.A := mem_of_pow_mem hn0 (by rw [hβn]; exact hwA)
  have hβA' : β⁻¹ ∈ x.A := mem_of_pow_mem hn0 (by rw [inv_pow, hβn]; exact hwA')
  have hv := valuation_eq_one_of_mem hβA hβA' hβ0
  have hσβ : (σ : Ω ≃ₐ[K₀ k t] Ω) β = ζ * β := by
    rw [hβ, map_div₀, hσα, hσρ, mul_div_assoc]
  have hfix := eq_of_mem_inertia (k := k) x.hk hσI hβA hv hn0 hζ.pow_eq_one hσβ
  rw [hσβ] at hfix
  have hζ1 : ζ = 1 := mul_right_cancel₀ hβ0 (hfix.trans (one_mul β).symm)
  rw [hζ1, IsPrimitiveRoot.one_left_iff] at hζ
  omega

/-- **`ord_{x_{k̄}}(u) = ord_x(u)` for `u ∈ F`**: the constant field extension `F k̄ / F` is
unramified at the rational point `x`. -/
theorem ord_placeOf_ιF (x : RatPoint D) (u : F D) :
    (placeOf x).ord (ιF D u) = (placeOfF x).ord u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  obtain ⟨π, hπ1⟩ := (placeOfF x).exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  set m := (placeOfF x).ord u
  set w := u * π ^ (-m) with hw
  have hw0 : w ≠ 0 := mul_ne_zero hu0 (zpow_ne_zero _ hπ0)
  have hword : (placeOfF x).ord w = 0 := by
    rw [hw, (placeOfF x).ord_mul hu0 (zpow_ne_zero _ hπ0), (placeOfF x).ord_zpow, hπ1]
    ring
  have hu : u = w * π ^ m := by
    rw [hw, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  obtain ⟨h1, h2⟩ := ((placeOfF x).ord_eq_zero_iff hw0).1 hword
  have hιw0 : ιF D w ≠ 0 := (map_ne_zero _).2 hw0
  have hιw : (placeOf x).ord (ιF D w) = 0 :=
    ((placeOf x).ord_eq_zero_iff hιw0).2 ⟨ιF_mem_placeOf.2 h1, by
      rw [← map_inv₀]; exact ιF_mem_placeOf.2 h2⟩
  rw [hu, map_mul, map_zpow₀, (placeOf x).ord_mul hιw0 (zpow_ne_zero _ ((map_ne_zero _).2 hπ0)),
    (placeOf x).ord_zpow, hιw, ord_placeOf_ιF_of_ord_eq_one x hπ1]
  ring

/-! ### Comparison of `div_F` and `div_{F k̄}` -/

lemma ιF_algebraMap (c : k) :
    ιF D (algebraMap k (F D) c) =
      algebraMap (kbar k Ω) (F (baseChange D)) (algebraMap k (kbar k Ω) c) := by
  apply Subtype.ext
  rw [coe_ιF, ← IntermediateField.algebraMap_apply, ← IntermediateField.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- **`div_{F k̄} u = ratDiv f ⟺ div_F u = ratDivF f`** for `u ∈ Fˣ`: away from the rational
points both divisors vanish together, and at a rational point the orders agree
(`ord_placeOf_ιF`, `eq_placeOf_of_liesOver`). -/
theorem div_ιF_eq_ratDiv_iff (f : RatPoint D →₀ ℤ) {u : F D} (hu : u ≠ 0) :
    Divisor.div (kbar k Ω) (ιF D u) = ratDiv f ↔ Divisor.div k u = ratDivF f := by
  have hιu : ιF D u ≠ 0 := (map_ne_zero _).2 hu
  constructor
  · intro h
    ext P
    rw [Divisor.div_apply]
    by_cases hP : ∃ x, placeOfF x = P
    · obtain ⟨x, rfl⟩ := hP
      rw [← ord_placeOf_ιF, ← Divisor.div_apply (k := kbar k Ω), h, ratDiv_apply_placeOf]
    · push Not at hP
      rw [ratDivF_apply_of_forall_ne f hP]
      obtain ⟨W, hW⟩ := exists_valuationSubring_liesOver D P
      have hk : ∀ c : k, algebraMap k Ω c ∈ W := fun c => by
        rw [IsScalarTower.algebraMap_apply k (F D) Ω]
        exact (hW _).2 (P.algebraMap_mem c)
      have hmem : ∀ v : F D,
          ιF D v ∈ W.comap (algebraMap (F (baseChange D)) Ω) ↔ v ∈ P.1 := fun v => by
        rw [ValuationSubring.mem_comap, IntermediateField.algebraMap_apply, coe_ιF, hW]
      have hne : W.comap (algebraMap (F (baseChange D)) Ω) ≠ ⊤ := by
        intro htop
        apply P.ne_top
        refine eq_top_iff.2 fun v _ => (hmem v).1 ?_
        rw [htop]
        trivial
      let Q : Place (kbar k Ω) (F (baseChange D)) := ⟨_, hne, fun c => kbar_mem W hk c⟩
      have hQmem : ∀ v : F D, ιF D v ∈ Q.1 ↔ v ∈ P.1 := hmem
      have hQx : ∀ x, placeOf x ≠ Q := by
        intro x hx
        apply hP x
        apply Place.ext
        ext v
        rw [← ιF_mem_placeOf, hx, hQmem]
      have h0 := congrArg (fun E => E Q) h
      simp only [Divisor.div_apply] at h0
      rw [ratDiv_apply_of_forall_ne f hQx] at h0
      obtain ⟨h1, h2⟩ := (Q.ord_eq_zero_iff hιu).1 h0
      rw [← map_inv₀] at h2
      exact (P.ord_eq_zero_iff hu).2 ⟨(hQmem u).1 h1, (hQmem _).1 h2⟩
  · intro h
    ext Q
    rw [Divisor.div_apply]
    by_cases hQ : ∃ x, placeOf x = Q
    · obtain ⟨x, rfl⟩ := hQ
      rw [ord_placeOf_ιF, ← Divisor.div_apply (k := k), h, ratDiv_apply_placeOf]
    · push Not at hQ
      rw [ratDiv_apply_of_forall_ne f hQ]
      by_cases hA : Q.1.comap (ιF D) = ⊤
      · have h1 : u ∈ Q.1.comap (ιF D) := by rw [hA]; trivial
        have h2 : u⁻¹ ∈ Q.1.comap (ιF D) := by rw [hA]; trivial
        rw [ValuationSubring.mem_comap] at h1 h2
        rw [map_inv₀] at h2
        exact (Q.ord_eq_zero_iff hιu).2 ⟨h1, h2⟩
      · let P : Place k (F D) := ⟨Q.1.comap (ιF D), hA, fun c => by
          rw [ValuationSubring.mem_comap, ιF_algebraMap]
          exact Q.algebraMap_mem _⟩
        have hPmem : ∀ v : F D, ιF D v ∈ Q.1 ↔ v ∈ P.1 := fun v => ValuationSubring.mem_comap.symm
        by_cases hPx : ∃ x, placeOfF x = P
        · obtain ⟨x, hx⟩ := hPx
          exact absurd (eq_placeOf_of_liesOver x Q fun v => by rw [hx, hPmem]).symm (hQ x)
        · push Not at hPx
          have h0 := ratDivF_apply_of_forall_ne f hPx
          rw [← h, Divisor.div_apply] at h0
          obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff hu).1 h0
          refine (Q.ord_eq_zero_iff hιu).2 ⟨(hPmem u).2 h1, ?_⟩
          rw [← map_inv₀]
          exact (hPmem _).2 h2

/-! ### Descent: Hilbert 90 for `k̄/k` -/

/-- `H` fixes the divisor `ratDiv f` of `X_{k̄}`. -/
lemma divMap_autF_ratDiv (h : D.H) (f : RatPoint D →₀ ℤ) :
    divMap (autF D h) (ratDiv f) = ratDiv f := by
  change Finsupp.domCongr (placeEquiv (autF D h)) (ratDiv f) = ratDiv f
  rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain, ratDiv,
    ← Finsupp.mapDomain_comp]
  congr 1
  funext x
  exact placeMap_autF_placeOf' h x

/-- If `div g = ratDiv f`, then `h(g) = c_h g` with `c_h ∈ k̄ˣ` for every `h ∈ H`. -/
lemma exists_const_of_div_eq_ratDiv {f : RatPoint D →₀ ℤ} {g : F (baseChange D)} (hg : g ≠ 0)
    (hdiv : Divisor.div (kbar k Ω) g = ratDiv f) (h : D.H) :
    ∃ c : kbar k Ω, c ≠ 0 ∧ (h : Ω ≃ₐ[K₀ k t] Ω) g = (c : Ω) * g := by
  have hhg : (autF D h : F (baseChange D) ≃+* F (baseChange D)) g ≠ 0 :=
    (RingEquiv.map_ne_zero_iff _).2 hg
  have hd : Divisor.div (kbar k Ω) ((autF D h : F (baseChange D) ≃+* F (baseChange D)) g) =
      Divisor.div (kbar k Ω) g := by
    rw [← divMap_div, hdiv, divMap_autF_ratDiv]
  obtain ⟨c, hc0, hc⟩ := exists_eq_const_mul_of_div_eq hhg hg hd
  refine ⟨c, hc0, ?_⟩
  have e := congrArg (fun y : F (baseChange D) => (y : Ω)) hc
  simp only [coe_autF_apply, IntermediateField.coe_mul] at e
  rw [e, ← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- the instance `SMul G_k k̄ˣ` is slow to synthesize
set_option maxHeartbeats 600000 in
-- the whole proof (cocycle, openness of `hToGk` on the stabiliser, descent) is long
open scoped Topology in
/-- **Descent of principality** (Hilbert 90): if `div_{F k̄} g = ratDiv f`, then some `u ∈ Fˣ`
(namely `g/β`, `β ∈ k̄ˣ`) has `div_{F k̄} u = ratDiv f`. -/
theorem exists_mem_F_of_div_eq_ratDiv (x₀ : RatPoint D) {f : RatPoint D →₀ ℤ}
    {g : F (baseChange D)} (hg : g ≠ 0) (hdiv : Divisor.div (kbar k Ω) g = ratDiv f) :
    ∃ u : F D, u ≠ 0 ∧ Divisor.div (kbar k Ω) (ιF D u) = ratDiv f := by
  classical
  choose c hc0 hc using exists_const_of_div_eq_ratDiv hg hdiv
  have hgΩ : (g : Ω) ≠ 0 := fun h0 => hg (Subtype.ext h0)
  have hcdep : ∀ h h' : D.H, hToGk D h = hToGk D h' → c h = c h' := by
    intro h h' hh
    have e : (h : Ω ≃ₐ[K₀ k t] Ω) g = (h' : Ω ≃ₐ[K₀ k t] Ω) g := by
      have := congrArg (fun τ : constAut (kbar k Ω) (F (baseChange D)) =>
        (((τ : F (baseChange D) ≃+* F (baseChange D)) g : F (baseChange D)) : Ω))
        (autF_eq_of_hToGk_eq hh)
      simpa only [coe_autF_apply] using this
    rw [hc h, hc h'] at e
    exact Subtype.ext (mul_right_cancel₀ hgΩ e)
  have hcmul : ∀ h h' : D.H,
      (c (h * h') : Ω) = (h : Ω ≃ₐ[K₀ k t] Ω) (c h') * c h := by
    intro h h'
    have e := hc (h * h')
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hc h', map_mul, hc h, ← mul_assoc] at e
    exact (mul_right_cancel₀ hgΩ e).symm
  have hsurj : ∀ σ : Gk k Ω, ∃ h : D.H, hToGk D h = σ := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_hToGk_eq x₀ σ
    exact ⟨_, hτ⟩
  choose lift hlift using hsurj
  let cc : Gk k Ω → (kbar k Ω)ˣ := fun σ => Units.mk0 (c (lift σ)) (hc0 _)
  have hcc : ∀ h : D.H, ((cc (hToGk D h) : kbar k Ω) : Ω) = c h := fun h => by
    simp only [cc, Units.val_mk0]
    rw [hcdep _ h (hlift _)]
  have hcoc : groupCohomology.IsMulCocycle₁ cc := by
    intro σ τ
    apply Units.ext
    apply Subtype.ext
    rw [← hlift σ, ← hlift τ, ← map_mul, hcc, Units.val_mul, AlgEquiv.smul_units_def,
      Units.coe_map, MonoidHom.coe_coe, IntermediateField.coe_mul, hcc, hcmul]
    congr 1
    rw [← hcc (lift τ), hlift τ, ← algebraMap_hToGk_apply]
    rfl
  -- `cc = 1` on the image of the (open) stabiliser of `g`
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  let S : Subgroup D.H :=
    (MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) (g : Ω)).comap D.H.subtype
  have hSopen : IsOpen (S : Set D.H) :=
    (stabilizer_isOpen_of_isIntegral (K := K₀ k t) (g : Ω)).preimage continuous_subtype_val
  have hS1 : ∀ h ∈ S, cc (hToGk D h) = 1 := by
    intro h hh
    have hfix : (h : Ω ≃ₐ[K₀ k t] Ω) g = g := hh
    apply Units.ext
    apply Subtype.ext
    rw [hcc, Units.val_one, IntermediateField.coe_one]
    rw [hc h] at hfix
    exact mul_right_cancel₀ hgΩ (hfix.trans (one_mul _).symm)
  have hcl : IsClosedMap (hToGk D) := (continuous_hToGk D).isClosedMap
  let T : Subgroup D.H := (S.map (hToGk D)).comap (hToGk D)
  have hT : IsOpen (T : Set D.H) := Subgroup.isOpen_mono (Subgroup.le_comap_map _ _) hSopen
  have himg : hToGk D '' (T : Set D.H)ᶜ = ((S.map (hToGk D) : Subgroup (Gk k Ω)) : Set _)ᶜ := by
    ext σ
    constructor
    · rintro ⟨h, hhT, rfl⟩ hmem
      exact hhT hmem
    · intro hσ
      refine ⟨lift σ, fun hmem => hσ ?_, hlift σ⟩
      have : hToGk D (lift σ) ∈ S.map (hToGk D) := hmem
      rwa [hlift] at this
  have hopen : IsOpen ((S.map (hToGk D) : Subgroup (Gk k Ω)) : Set (Gk k Ω)) := by
    rw [← isClosed_compl_iff, ← himg]
    exact hcl _ hT.isClosed_compl
  have h1 : {σ | cc σ = 1} ∈ 𝓝 (1 : Gk k Ω) := by
    refine Filter.mem_of_superset (hopen.mem_nhds (one_mem _)) ?_
    rintro σ ⟨h, hS, rfl⟩
    exact hS1 h hS
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_eventually_eq_one hcoc h1
  -- `g / β` is fixed by `H`
  have hβ0 : ((β : kbar k Ω) : Ω) ≠ 0 := fun h0 => β.ne_zero (Subtype.ext h0)
  have hβh : ∀ h : D.H, (h : Ω ≃ₐ[K₀ k t] Ω) (β : kbar k Ω) = c h * (β : kbar k Ω) := by
    intro h
    have hb := congrArg (fun z : (kbar k Ω)ˣ => ((z : kbar k Ω) : Ω)) (hβ (hToGk D h))
    simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map,
      MonoidHom.coe_coe, IntermediateField.coe_div] at hb
    rw [hcc, ← algebraMap_hToGk_apply] at *
    rw [← hb, div_mul_cancel₀ _ hβ0]
    rfl
  obtain ⟨g', hg'⟩ : ∃ g' : Ω, g' = (g : Ω) / ((β : kbar k Ω) : Ω) := ⟨_, rfl⟩
  have hfix : ∀ h : D.H, (h : Ω ≃ₐ[K₀ k t] Ω) g' = g' := by
    intro h
    rw [hg', map_div₀, hc h, hβh h, mul_div_mul_left _ _ (fun h0 => hc0 h (Subtype.ext h0))]
  have hg'F : g' ∈ F D := (IntermediateField.mem_fixedField_iff _ _).2 fun h hh => hfix ⟨h, hh⟩
  have hg'0 : g' ≠ 0 := hg' ▸ div_ne_zero hgΩ hβ0
  have hu0 : (⟨g', hg'F⟩ : F D) ≠ 0 := fun h0 => hg'0 (by
    have := congrArg Subtype.val h0
    rwa [ZeroMemClass.coe_zero] at this)
  refine ⟨⟨g', hg'F⟩, hu0, ?_⟩
  obtain ⟨b, hb⟩ : ∃ b : kbar k Ω, b = (β : kbar k Ω)⁻¹ := ⟨_, rfl⟩
  have e : ιF D ⟨g', hg'F⟩ = g * algebraMap (kbar k Ω) (F (baseChange D)) b := by
    apply Subtype.ext
    have hcoe : ((algebraMap (kbar k Ω) (F (baseChange D)) b : F (baseChange D)) : Ω) = b := by
      rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IntermediateField.algebraMap_apply]
    rw [coe_ιF, Subtype.coe_mk, IntermediateField.coe_mul, hcoe, hg', div_eq_mul_inv, hb,
      IntermediateField.coe_inv]
  have hβinv0 : algebraMap (kbar k Ω) (F (baseChange D)) b ≠ 0 :=
    right_ne_zero_of_mul (e ▸ (map_ne_zero _).2 hu0)
  have hconst : Divisor.div (kbar k Ω) (algebraMap (kbar k Ω) (F (baseChange D)) b) = 0 := by
    ext Q
    rw [Divisor.div_apply, Place.ord_algebraMap_base, Finsupp.coe_zero, Pi.zero_apply]
  rw [e, Divisor.div_mul hg hβinv0, hconst, add_zero, hdiv]

/-- **`D` is principal on `X_{k̄}` iff it is principal on `X`** (for `D` supported on
`k`-rational points). -/
theorem mk_ratDiv_eq_zero_iff (f : RatPoint D →₀ ℤ) :
    (QuotientAddGroup.mk (ratDiv f) : Pic (kbar k Ω) (F (baseChange D))) = 0 ↔
      ratDivF f ∈ principal k (F D) := by
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · intro hp
    obtain ⟨g, hg, hdiv⟩ := mem_principal.1 hp
    rcases isEmpty_or_nonempty (RatPoint D) with hE | ⟨⟨x₀⟩⟩
    · have hf : f = 0 := by
        ext x
        exact hE.elim x
      rw [hf, ratDivF, Finsupp.mapDomain_zero]
      exact zero_mem _
    · obtain ⟨u, hu, hdu⟩ := exists_mem_F_of_div_eq_ratDiv x₀ hg hdiv
      exact mem_principal.2 ⟨u, hu, (div_ιF_eq_ratDiv_iff f hu).1 hdu⟩
  · intro hp
    obtain ⟨u, hu, hdu⟩ := mem_principal.1 hp
    exact mem_principal.2 ⟨ιF D u, (map_ne_zero _).2 hu, (div_ιF_eq_ratDiv_iff f hu).2 hdu⟩

/-! ### [AbsTopIII] Prop. 1.6(ii) in the Galois model -/

variable [Fact (Function.Surjective (piJ1ToGk D))]

/-- **[AbsTopIII] Prop. 1.6(ii) / [Cusp] Prop. 2.3(i) in the Galois model**, with "principal"
in the sense of the paper (on `X`, i.e. the divisor of a function in `F`): for a degree-`0`
divisor `D = ∑ nᵢ xᵢ` supported on `k`-rational points, `η_D = 0` iff `D` is principal. The
hypotheses are those of `eta_eq_one_iff` (theorems for curves: `eta_eq_one_iff_principal_curve`).
-/
theorem eta_eq_one_iff_principal (hKF : IsKummerFaithfulJac D)
    (hdivJ : ∀ N : ℕ, 0 < N → ∀ y : Pic (kbar k Ω) (F (baseChange D)), Pic.deg _ _ y = 0 →
      ∃ w, N • w = y)
    (hperf : ∀ (N : ℕ) [NeZero N],
      Function.Bijective (weilDual (κ := kbar k Ω) (K := F (baseChange D)) (n := N)))
    (hfin : ∀ (N : ℕ) [NeZero N], Finite (picTorsion (kbar k Ω) (F (baseChange D)) N))
    (f : RatPoint D →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    eta f = 1 ↔ ratDivF f ∈ principal k (F D) :=
  (eta_eq_one_iff hKF hdivJ hperf hfin f hf).trans (mk_ratDiv_eq_zero_iff f)

/-- `η_D = 0` iff the combination `t_D = ∑ nᵢ t_{xᵢ}` of the sections `t_x` coincides with the
identity section up to `Δ_X`-conjugation: `∏ (t_{xᵢ}(σ) t_{x₀}(σ)⁻¹)^{nᵢ} = q · σ(q)⁻¹` for one
`q ∈ Δ_X^{ab}` and all `σ ∈ G_k` (in `Π_J = Δ_X^{ab} ⋊ G_k`, `q (1, σ) q⁻¹ = (q σ(q)⁻¹, σ)`). -/
theorem eta_eq_one_iff_exists_conj (f : RatPoint D →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (x₀ : RatPoint D) :
    eta f = 1 ↔ ∃ q : DeltaAb D, ∀ σ : Gk k Ω,
      (etaCocycle f x₀ : Gk k Ω → DeltaAb D) σ = q / (σ • q) := by
  rw [eta_eq_etaDiv f hf x₀, etaDiv_eq_mk, ContH1.mk_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m⁻¹, fun σ => ?_⟩
    rw [← hm σ, smul_inv', div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]
  · rintro ⟨q, hq⟩
    refine ⟨q⁻¹, fun σ => ?_⟩
    rw [hq σ, smul_inv', div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]

end General

/-! ### Curves over Kummer-faithful fields -/

section Curve

open AlgebraicGeometry Belyi CurvesJacobian.Cusp CategoryTheory

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- **[AbsTopIII] Prop. 1.6(ii)** ([Cusp] Prop. 2.3(i)) for a curve `X` with a `k`-point over a
Kummer-faithful field `k` of characteristic `0` (Galois model `curveGaloisData k hτ`, function
field `F ≅ K(X)`): a divisor `D = ∑ nᵢ xᵢ` of degree `0` supported on `k`-rational points
is principal on `X` (`D = div_X(u)` for some `u ∈ K(X)ˣ`) iff `η_D = 0` in `H¹(G_k, Δ_X^{ab})`. -/
theorem eta_eq_one_iff_principal_curve (hk : IsKummerFaithful k)
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  (eta_eq_one_iff_curve k hτ hk σ hσ f hf).trans (mk_ratDiv_eq_zero_iff f)

/-- **[AbsTopIII] Prop. 1.6(ii)**, as stated in the paper (T3 l.1993–2000): for a divisor `D` of
degree `0` on `X` with `Supp(D) ⊆ X(k)`, the section `t_D = ∑ nᵢ t_{xᵢ}` coincides, up to
conjugation by `Δ_X`, with the section determined by the identity element of `J(k)` iff `D` is
principal (`k` Kummer-faithful of characteristic `0`, `X(k) ≠ ∅`). Here the comparison of `t_D`
with the identity section is the difference cocycle `σ ↦ ∏ (t_{xᵢ}(σ) t_{x₀}(σ)⁻¹)^{nᵢ}` with
values in `Δ_X^{ab} = ker(Π_J → G_k)` (`etaCocycle`), and conjugation of the identity section by
`q ∈ Δ_X^{ab}` is `σ ↦ q σ(q)⁻¹`. -/
theorem tD_conj_identity_iff_principal_curve (hk : IsKummerFaithful k)
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (x₀ : RatPoint (curveGaloisData k hτ)) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    (∃ q : DeltaAb (curveGaloisData k hτ), ∀ g : Gk k (FFClosure X),
      (etaCocycle f x₀ : Gk k (FFClosure X) → DeltaAb (curveGaloisData k hτ)) g = q / (g • q)) ↔
      ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  (eta_eq_one_iff_exists_conj f hf x₀).symm.trans
    (eta_eq_one_iff_principal_curve k hτ hk σ hσ f hf)

end Curve

end CurvesJacobian.Kummer
