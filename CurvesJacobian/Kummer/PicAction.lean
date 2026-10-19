/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ConstantExtension
import WeilCurves.FunctionField.Degree

/-!
# Semilinear automorphisms act on places, divisors and `Pic`; `J(k)` and Kummer-faithfulness

Let `K / κ` be a function field of one variable over a perfect field `κ` (weil-curves). A ring
automorphism `τ` of `K` which maps the constants `κ` onto themselves (but need not fix them
pointwise; e.g. `κ = k̄`, `τ ∈ G_k`) acts on places (`O_Q ↦ τ(O_Q)`), preserving orders
(`ord_{τQ}(τ x) = ord_Q x`), hence on divisors and on `Pic(K) = Div(K)/Prin(K)`.

In the Galois model (`D : GaloisData k t`, `F k̄ = F (baseChange D)`), every `h ∈ H` acts on
`F k̄` (`CurvesJacobian.Kummer.autF h`), hence on `Pic(X_{k̄}) = Pic(F k̄)`
(`CurvesJacobian.Kummer.picAct`); it factors through `G_k`, since `Δ = ker(H → G_k)` fixes
`F k̄` pointwise (`fixes_F_baseChange`).

* `CurvesJacobian.Kummer.picInv D`: the classes fixed by `H`, i.e. `Pic(X_{k̄})^{G_k}`;
* `CurvesJacobian.Kummer.IsKummerFaithfulJac D`: `⋂_{N ≥ 1} N · Pic(X_{k̄})^{G_k} = 0`.

**On the definition.** [AbsTopIII] Def. 1.5 (l.1807–1836 of T3) calls `k` Kummer-faithful if for
every finite `k_H ⊆ k̄` and every semi-abelian variety `A / k_H`, `⋂_{N ≥ 1} N · A(k_H) = {0}`.
The proof of Prop. 1.6(iii) (l.2033–2039) uses this for `A = J` the Jacobian of `X`, `k_H = k`:
`H⁰(G_k, Δ_X^{ab}) = 0`. Since `J(k) = J(k̄)^{G_k} = Pic⁰(X_{k̄})^{G_k}` and the degree of an
element of `⋂_N N · Pic(X_{k̄})^{G_k}` is divisible by every `N`, the condition
`IsKummerFaithfulJac D` is exactly `⋂_N N · J(k) = 0`. It is a property of the curve, used as a
hypothesis here (like `IsKummerFaithfulGm k` for `𝔾_m`); for a curve with a rational point over a
Kummer-faithful field `k` (Def. 1.5, `CurvesJacobian.IsKummerFaithful`) it is proved in
`Kummer/KummerFaithful.lean` (`isKummerFaithfulJac_of_isKummerFaithful`), through the Jacobian
`J_k` as a `k`-scheme.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField
open scoped WithZero

namespace CurvesJacobian.Kummer

universe u

section Semilinear

variable {κ K : Type*} [Field κ] [Field K] [Algebra κ K]

/-- The ring automorphisms of `K` mapping the constants `κ` onto themselves. -/
def constAut (κ K : Type*) [Field κ] [Field K] [Algebra κ K] : Subgroup (K ≃+* K) where
  carrier := {τ | ∀ c : κ, τ (algebraMap κ K c) ∈ Set.range (algebraMap κ K) ∧
    τ.symm (algebraMap κ K c) ∈ Set.range (algebraMap κ K)}
  one_mem' c := ⟨⟨c, rfl⟩, ⟨c, rfl⟩⟩
  mul_mem' {a b} ha hb c := by
    refine ⟨?_, ?_⟩
    · obtain ⟨c', hc'⟩ := (hb c).1
      change a (b _) ∈ _
      rw [← hc']
      exact (ha c').1
    · obtain ⟨c', hc'⟩ := (ha c).2
      change b.symm (a.symm _) ∈ _
      rw [← hc']
      exact (hb c').2
  inv_mem' {a} ha c := ⟨(ha c).2, by
    change a.symm.symm _ ∈ _
    exact (ha c).1⟩

/-- The image `τ(Q)` of a place under `τ ∈ constAut κ K`: valuation ring `τ(O_Q)`. -/
def placeMap (τ : constAut κ K) (Q : Place κ K) : Place κ K :=
  ⟨Q.1.comap ((τ : K ≃+* K).symm : K →+* K), fun h ↦ Q.ne_top (top_unique fun x _ ↦ by
      have : (τ : K ≃+* K) x ∈ Q.1.comap ((τ : K ≃+* K).symm : K →+* K) := by rw [h]; trivial
      simpa using (ValuationSubring.mem_comap.mp this)),
    fun c ↦ ValuationSubring.mem_comap.mpr (by
      obtain ⟨c', hc'⟩ := (τ.2 c).2
      change (τ : K ≃+* K).symm (algebraMap κ K c) ∈ Q.1
      rw [← hc']
      exact Q.algebraMap_mem c')⟩

lemma mem_placeMap {τ : constAut κ K} {Q : Place κ K} {x : K} :
    x ∈ (placeMap τ Q).1 ↔ (τ : K ≃+* K).symm x ∈ Q.1 :=
  ValuationSubring.mem_comap

lemma placeMap_mul (τ σ : constAut κ K) (Q : Place κ K) :
    placeMap (τ * σ) Q = placeMap τ (placeMap σ Q) := by
  ext x
  simp only [mem_placeMap]
  rfl

lemma placeMap_one (Q : Place κ K) : placeMap 1 Q = Q := by
  ext x
  simp only [mem_placeMap]
  rfl

/-- `placeMap τ` as a permutation of the places. -/
def placeEquiv (τ : constAut κ K) : Place κ K ≃ Place κ K where
  toFun := placeMap τ
  invFun := placeMap τ⁻¹
  left_inv Q := by rw [← placeMap_mul, inv_mul_cancel, placeMap_one]
  right_inv Q := by rw [← placeMap_mul, mul_inv_cancel, placeMap_one]

/-- The action on divisors: `(τ D)(P) = D(τ⁻¹ P)`. -/
noncomputable def divMap (τ : constAut κ K) : Divisor κ K →+ Divisor κ K :=
  (Finsupp.domCongr (placeEquiv τ)).toAddMonoidHom

lemma divMap_apply (τ : constAut κ K) (E : Divisor κ K) (P : Place κ K) :
    divMap τ E P = E (placeMap τ⁻¹ P) := rfl

variable [PerfectField κ] [IsFunctionField κ K]

/-- **`ord_{τQ}(τ x) = ord_Q x`**. -/
theorem ord_placeMap_apply (τ : constAut κ K) (Q : Place κ K) (x : K) :
    (placeMap τ Q).ord ((τ : K ≃+* K) x) = Q.ord x := by
  set w : Valuation K ℤᵐ⁰ := Q.valuation.comap ((τ : K ≃+* K).symm : K →+* K)
  have hw : ∀ y, y ∈ (placeMap τ Q).1 ↔ w y ≤ 1 := by
    intro y
    rw [mem_placeMap, Q.mem_iff_valuation_le_one]
    rfl
  obtain ⟨π, hπ⟩ := Q.exists_ord_eq_one
  have hπw : w ((τ : K ≃+* K) π) = WithZero.exp (-1) := by
    have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
    simp only [w, Valuation.comap_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply]
    rw [Q.valuation_eq_exp hπ0, hπ]
  rw [(placeMap τ Q).ord_eq_neg_log w hw ⟨_, hπw⟩ ((τ : K ≃+* K) x)]
  simp only [w, Valuation.comap_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply, Place.ord]

lemma divMap_div (τ : constAut κ K) (f : K) :
    divMap τ (Divisor.div κ f) = Divisor.div κ ((τ : K ≃+* K) f) := by
  ext P
  rw [divMap_apply, Divisor.div_apply, Divisor.div_apply]
  conv_rhs => rw [← placeEquiv τ |>.right_inv P]
  change _ = (placeMap τ (placeMap τ⁻¹ P)).ord _
  rw [ord_placeMap_apply]

lemma divMap_mem_principal (τ : constAut κ K) {E : Divisor κ K} (hE : E ∈ principal κ K) :
    divMap τ E ∈ principal κ K := by
  obtain ⟨f, hf, rfl⟩ := mem_principal.1 hE
  rw [divMap_div]
  exact div_mem_principal ((map_ne_zero _).2 hf)

/-- The action on `Pic`. -/
noncomputable def picMap (τ : constAut κ K) : Pic κ K →+ Pic κ K :=
  QuotientAddGroup.map _ _ (divMap τ) fun _ hE => divMap_mem_principal τ hE

lemma picMap_mk (τ : constAut κ K) (E : Divisor κ K) :
    picMap τ (E : Pic κ K) = (divMap τ E : Pic κ K) := rfl

omit [PerfectField κ] [IsFunctionField κ K] in
/-- Divisors are torsion-free. -/
lemma divisor_nsmul_cancel {n : ℕ} (hn : n ≠ 0) {X Y : Divisor κ K} (h : n • X = n • Y) :
    X = Y := by
  ext P
  have := DFunLike.congr_fun h P
  simp only [Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hn) this

/-- If `n E' = n E + div(gⁿ)`, then `[E'] = [E]` in `Pic`. -/
lemma mk_eq_of_nsmul_eq {n : ℕ} (hn : n ≠ 0) {E E' : Divisor κ K} {g : K} (hg : g ≠ 0)
    (h : n • E' = n • E + Divisor.div κ (g ^ n)) : (E' : Pic κ K) = E := by
  rw [Divisor.div_pow, ← nsmul_add] at h
  rw [divisor_nsmul_cancel hn h, QuotientAddGroup.mk_add,
    (QuotientAddGroup.eq_zero_iff _).2 (div_mem_principal hg), add_zero]

/-- **Invariance of a Kummer divisor class**: if `n E = div a` and `τ a = a bⁿ`, then
`τ [E] = [E]`. -/
lemma picMap_mk_eq_of {n : ℕ} (hn : n ≠ 0) (τ : constAut κ K) {E : Divisor κ K} {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hE : n • E = Divisor.div κ a)
    (hτ : (τ : K ≃+* K) a = a * b ^ n) : picMap τ (E : Pic κ K) = E := by
  rw [picMap_mk]
  refine mk_eq_of_nsmul_eq hn hb ?_
  rw [← map_nsmul, hE, divMap_div, hτ, Divisor.div_mul ha (pow_ne_zero _ hb)]

/-- **Compatibility of Kummer divisor classes**: if `n E = div a`, `(nN) E' = div a'` and
`a' = a gⁿ`, then `N [E'] = [E]`. -/
lemma nsmul_mk_eq_of {n N : ℕ} (hn : n ≠ 0) {E E' : Divisor κ K} {a a' g : K}
    (ha : a ≠ 0) (hg : g ≠ 0) (hE : n • E = Divisor.div κ a)
    (hE' : (n * N) • E' = Divisor.div κ a') (ha' : a' = a * g ^ n) :
    N • (E' : Pic κ K) = E := by
  rw [← QuotientAddGroup.mk_nsmul]
  refine mk_eq_of_nsmul_eq hn hg ?_
  rw [← mul_nsmul', hE', ha', Divisor.div_mul ha (pow_ne_zero _ hg), hE]

end Semilinear

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]

/-- `h ∈ H` as a ring automorphism of `F k̄` (it stabilises `F k̄`, and `k̄`). -/
noncomputable def autF (h : D.H) : constAut (kbar k Ω) (F (baseChange D)) where
  val :=
    { toFun x := ⟨(h : Ω ≃ₐ[K₀ k t] Ω) x, smul_mem_F_baseChange D h.2 x.2⟩
      invFun x := ⟨(h : Ω ≃ₐ[K₀ k t] Ω).symm x,
        smul_mem_F_baseChange D (D.H.inv_mem h.2) x.2⟩
      left_inv x := Subtype.ext (AlgEquiv.symm_apply_apply _ _)
      right_inv x := Subtype.ext (AlgEquiv.apply_symm_apply _ _)
      map_mul' x y := Subtype.ext (map_mul _ (x : Ω) y)
      map_add' x y := Subtype.ext (map_add _ (x : Ω) y) }
  property c := by
    have hmem : ∀ σ : Ω ≃ₐ[K₀ k t] Ω, σ (c : Ω) ∈ kbar k Ω := fun σ => by
      have := c.2
      rw [mem_algebraicClosure_iff] at this ⊢
      exact (this.isIntegral.map (σ.restrictScalars k).toAlgHom).isAlgebraic
    exact ⟨⟨⟨_, hmem h⟩, rfl⟩, ⟨⟨_, hmem (h : Ω ≃ₐ[K₀ k t] Ω).symm⟩, rfl⟩⟩

@[simp]
lemma coe_autF_apply (h : D.H) (x : F (baseChange D)) :
    (((autF D h : F (baseChange D) ≃+* F (baseChange D)) x : F (baseChange D)) : Ω) =
      (h : Ω ≃ₐ[K₀ k t] Ω) x := rfl

variable [CharZero k]

attribute [local instance] isFunctionField_F

/-- The action of `h ∈ H` on `Pic(X_{k̄}) = Pic(F k̄)`. -/
noncomputable def picAct (h : D.H) : Pic (kbar k Ω) (F (baseChange D)) →+
    Pic (kbar k Ω) (F (baseChange D)) :=
  picMap (autF D h)

/-- `Pic(X_{k̄})^{G_k}`: the classes fixed by `H` (equivalently by `G_k`). -/
noncomputable def picInv : AddSubgroup (Pic (kbar k Ω) (F (baseChange D))) where
  carrier := {x | ∀ h : D.H, picAct D h x = x}
  zero_mem' h := map_zero _
  add_mem' ha hb h := by rw [map_add, ha h, hb h]
  neg_mem' ha h := by rw [map_neg, ha h]

/-- **Kummer-faithfulness for the Jacobian** (see the module docstring):
`⋂_{N ≥ 1} N · Pic(X_{k̄})^{G_k} = 0`, i.e. `⋂_N N · J(k) = 0`. -/
def IsKummerFaithfulJac : Prop :=
  ∀ x : Pic (kbar k Ω) (F (baseChange D)), (∀ N : ℕ, 0 < N → ∃ y ∈ picInv D, N • y = x) → x = 0

end Galois

end CurvesJacobian.Kummer
