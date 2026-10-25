/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ChernDivisor
import CurvesJacobian.Cusp.CuspTerminal

/-!
# Inertia fixes an unramified finite cover (the `loc` field of `IsChernRepDiv` on a cover)

Setting of `ChernDivisor` (section `Curve`): `F = F D = Ω^H` the function field, `W` a place of
`Ω` over the place `P` of `F`. Let `L ⊆ Ω` be a finite normal extension of `F`, given as an
`IntermediateField (F D) Ω` (so that `Algebra (F D) L`, `Algebra k L` and
`IsScalarTower k (F D) L` are the standard `IntermediateField` instances, and
`(algebraMap (F D) L x : Ω) = x` holds by `rfl`).

* `placeOfW`: the place `Q = W ∩ L` of `L` (`mem_placeOfW`), lying over `P`
  (`restrict_placeOfW`);
* `fixes_L_of_mem_inertia`: if the Galois group `Gal(L/F)` acts freely on the places of `L`
  (in the form: an automorphism of `L/F` stabilising a place is the identity), every inertia
  element `σ ∈ H` of `W` fixes `L` pointwise (`σ|_L` stabilises `Q`);
* `loc_of_mem_L`: for `F' ∈ Lˣ` with `ord_Q F' ≡ E(Q|_F) (mod n)` at every place `Q` of `L` and
  `L/F` unramified, `F'` satisfies the `loc` condition of `IsChernRepDiv` for `E`.
-/

open AffOrbicurve Pi1.Orbifold Pi1 KummerTheory KummerTheory.Curve
open WeilCurves.FunctionField

namespace CurvesJacobian.ChernClass.CupKummer

universe u

variable {k Ω : Type u} [Field k]
  [Field Ω] [Algebra k Ω] {t : Ω} {D : GaloisData k t}
  {L : IntermediateField (F D) Ω}

/-! ### The place `W ∩ L` -/

/-- **The place `Q = W ∩ L` of `L`** under a place `W` of `Ω` lying over the place `P` of `F`. -/
def placeOfW {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) : Place k L :=
  ⟨W.comap (algebraMap L Ω), fun htop ↦ P.ne_top (top_unique fun x _ ↦ (hW x).1 (by
      have : algebraMap (F D) L x ∈ W.comap (algebraMap L Ω) := htop ▸ trivial
      exact this)),
    fun c ↦ by
      change algebraMap k Ω c ∈ W
      rw [IsScalarTower.algebraMap_apply k (F D) Ω]
      exact (hW _).2 (P.algebraMap_mem c)⟩

lemma mem_placeOfW {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) (x : L) :
    x ∈ (placeOfW (L := L) hW).1 ↔ (x : Ω) ∈ W :=
  Iff.rfl

lemma restrict_placeOfW [Algebra.IsIntegral (F D) L] {P : Place k (F D)}
    {W : ValuationSubring Ω} (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) :
    (placeOfW (L := L) hW).restrict = P := by
  apply Place.ext
  ext x
  rw [Place.mem_restrict, mem_placeOfW]
  exact hW x

attribute [local instance] isFunctionField_F

/-! ### Inertia fixes `L` -/

/-- **Inertia elements of `W` fix `L`** if `Gal(L/F)` acts freely on the places of `L` (`hfree`:
an automorphism of `L/F` stabilising a place of `L` is the identity; for `L/F` Galois this
follows from the freeness of the action of `Gal(L/F)` on the places of `L` over `P`). Indeed `σ`
fixes `F`, so restricts to `g ∈ Gal(L/F)` (`L/F` normal), and `σ` stabilises `W`
(`Cusp.comap_eq_of_mem_inertia`), so `g` stabilises `Q = W ∩ L`. -/
theorem fixes_L_of_mem_inertia [Normal (F D) L] {P : Place k (F D)} {W : ValuationSubring Ω}
    (hW : ∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1)
    (hfree : ∀ (g : L ≃ₐ[F D] L) (Q : Place k L), (∀ x, g x ∈ Q.1 ↔ x ∈ Q.1) → g = 1)
    {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (x : L) :
    (σ : Ω ≃ₐ[K₀ k t] Ω) x = x := by
  let ϕ : Ω →ₐ[F D] Ω :=
    { (σ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv.toRingHom with
      commutes' := fun y ↦ fixes_of_mem_F σ.2 y }
  set g : L ≃ₐ[F D] L := ϕ.restrictNormal' L
  have hg : ∀ y : L, ((g y : L) : Ω) = (σ : Ω ≃ₐ[K₀ k t] Ω) y := fun y ↦
    ϕ.restrictNormal_commutes L y
  have hcomap := Cusp.comap_eq_of_mem_inertia hσ
  have h1 : g = 1 := hfree g (placeOfW (L := L) hW) fun y ↦ by
    rw [mem_placeOfW, mem_placeOfW, hg]
    conv_rhs => rw [← hcomap]
    rfl
  have := hg x
  rw [h1, AlgEquiv.one_apply] at this
  exact this.symm

/-! ### The `loc` condition for an element of `L` -/

/-- **The `loc` field of `IsChernRepDiv D eL hH n E F'` for `F' ∈ Lˣ`**: if
`ord_Q F' ≡ E(Q|_F) (mod n)` at every place `Q` of `L`, `L/F` is unramified (`hram`) and
`Gal(L/F)` acts freely on the places of `L` (`hfree`), then at every place `W` of `Ω` over `P`
the Kummer characters of `F'` and of `u ∈ Fˣ` with `ord_P u = E(P)` agree on the inertia group
of `W`. Proof: `σ` fixes `L` (`fixes_L_of_mem_inertia`); `z = F'/u ∈ L` has order `n m` at
`Q = W ∩ L`, so `z = v πⁿᵐ` with `v` a unit at `Q` and `π ∈ L`; `β/γ = δ πᵐ` with `δⁿ = v`, and
`σ` fixes `δ` (`eq_of_mem_inertia`) and `π`. -/
theorem loc_of_mem_L [IsAlgClosed k] [CharZero k] [IsGalois (K₀ k t) Ω]
    [Algebra.IsIntegral (F D) L] [IsFunctionField k L] [Normal (F D) L] {n : ℕ} [NeZero n]
    {F' : L} (hF' : F' ≠ 0) {E : Divisor k (F D)}
    (hcong : ∀ Q : Place k L, (n : ℤ) ∣ Q.ord F' - E Q.restrict)
    (hram : ∀ (Q : Place k L) (x : F D), Q.ord (algebraMap (F D) L x) = Q.restrict.ord x)
    (hfree : ∀ (g : L ≃ₐ[F D] L) (Q : Place k L), (∀ x, g x ∈ Q.1 ↔ x ∈ Q.1) → g = 1) :
    ∀ (P : Place k (F D)) (W : ValuationSubring Ω),
      (∀ x : F D, ((x : F D) : Ω) ∈ W ↔ x ∈ P.1) → ∀ u : F D, u ≠ 0 → P.ord u = E P →
      ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W →
      ∀ β γ : Ω, β ^ n = ((F' : L) : Ω) → γ ^ n = (u : Ω) → σ • β / β = σ • γ / γ := by
  intro P W hW u hu hord σ hσ β γ hβ hγ
  set Q := placeOfW (L := L) hW
  have hQP : Q.restrict = P := restrict_placeOfW hW
  have hfix := fixes_L_of_mem_inertia hW hfree hσ
  have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW _).2 (P.algebraMap_mem c)
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have huL : algebraMap (F D) L u ≠ 0 := (map_ne_zero _).2 hu
  set z : L := F' / algebraMap (F D) L u
  have hz0 : z ≠ 0 := div_ne_zero hF' huL
  obtain ⟨m, hm⟩ := hcong Q
  rw [hQP] at hm
  have hzord : Q.ord z = n * m := by
    rw [Q.ord_div hF' huL, hram, hQP, hord, hm]
  obtain ⟨π, hπ1⟩ := Q.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  set w : L := π ^ m
  have hw0 : w ≠ 0 := zpow_ne_zero _ hπ0
  set v : L := z / w ^ n
  have hv0 : v ≠ 0 := div_ne_zero hz0 (pow_ne_zero _ hw0)
  have hvord : Q.ord v = 0 := by
    rw [Q.ord_div hz0 (pow_ne_zero _ hw0), Q.ord_pow, Q.ord_zpow, hπ1, hzord]
    ring
  obtain ⟨hv1, hv2⟩ := (Q.ord_eq_zero_iff hv0).1 hvord
  have hF'Ω : ((F' : L) : Ω) ≠ 0 := fun h ↦ hF' (Subtype.ext h)
  have huΩ : ((u : F D) : Ω) ≠ 0 := fun h ↦ hu (Subtype.ext h)
  have hwΩ : ((w : L) : Ω) ≠ 0 := fun h ↦ hw0 (Subtype.ext h)
  have hvΩ : ((v : L) : Ω) ≠ 0 := fun h ↦ hv0 (Subtype.ext h)
  have hβ0 : β ≠ 0 := ne_zero_of_pow_eq hF'Ω hβ
  have hγ0 : γ ≠ 0 := ne_zero_of_pow_eq huΩ hγ
  set δ : Ω := β / γ / (w : Ω)
  have hδ : δ ^ n = (v : Ω) := by
    simp only [δ, v, z, div_pow, hβ, hγ, IntermediateField.coe_div, IntermediateField.coe_pow]
    rfl
  have hδ0 : δ ≠ 0 := ne_zero_of_pow_eq hvΩ hδ
  have hδW : δ ∈ W := mem_of_pow_mem hn (by rw [hδ]; exact (mem_placeOfW hW v).1 hv1)
  have hδW' : δ⁻¹ ∈ W := mem_of_pow_mem hn (by
    rw [inv_pow, hδ, ← IntermediateField.coe_inv]; exact (mem_placeOfW hW _).1 hv2)
  have hpow : ((σ : Ω ≃ₐ[K₀ k t] Ω) δ / δ) ^ n = 1 := by
    rw [div_pow, ← map_pow, hδ, hfix v, div_self hvΩ]
  have hσδ : (σ : Ω ≃ₐ[K₀ k t] Ω) δ = δ :=
    eq_of_mem_inertia (k := k) hkW hσ hδW (valuation_eq_one_of_mem hδW hδW' hδ0) hn hpow
      (by field_simp)
  have hβγ : β / γ = δ * (w : Ω) := by simp only [δ]; field_simp
  have hσβγ : (σ : Ω ≃ₐ[K₀ k t] Ω) (β / γ) = β / γ := by
    rw [hβγ, map_mul, hσδ, hfix w]
  have hσγ0 : (σ : Ω ≃ₐ[K₀ k t] Ω) γ ≠ 0 := (map_ne_zero _).2 hγ0
  rw [map_div₀, div_eq_div_iff hσγ0 hγ0] at hσβγ
  change (σ : Ω ≃ₐ[K₀ k t] Ω) β / β = (σ : Ω ≃ₐ[K₀ k t] Ω) γ / γ
  rw [div_eq_div_iff hβ0 hγ0]
  linear_combination hσβγ

end CurvesJacobian.ChernClass.CupKummer
