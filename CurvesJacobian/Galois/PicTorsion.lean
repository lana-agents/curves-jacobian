/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.UnramifiedKummer
import CurvesJacobian.FunctionField.KummerPic
import CurvesJacobian.FunctionField.KummerInertia
import ContinuousKummerTheory.Kummer.Equiv
import WeilCurves.FunctionField.ZerosPoles

/-!
# `Pic(X)[n]` is the group of unramified `μₙ`-characters

Setting of `pi1` / continuous-kummer-theory (`D : GaloisData k t`, `F = Ω^H`, `char k = 0`), with
`k` **algebraically closed**, so that `F` is the function field of a (proper, smooth) curve `X`
over `k`. Let `n ≥ 1`.

* `CurvesJacobian.unramifiedChars D n ≤ H¹(Gal(Ω/F), μₙ)`: the classes whose restriction to `H`
  is trivial on the inertia group of every place `W ⊇ k` of `Ω` — the characters of
  `Gal(Ω/F) ≅ H` that factor through `Π_X = H ⧸ ⟨⟨inertia of all places⟩⟩` (pi1's Galois model of
  `π₁ᵉᵗ(X)`, SGA 1 V.8.2);
* `CurvesJacobian.picTorsionEquivUnramified D n : Pic(F)[n] ≃+ Additive (unramifiedChars D n)`.

This is Milne, *Abelian Varieties*, III.Lemma 9.2 (`Hom(π₁(V), ℤ/n) ≅ Pic(V)ₙ`) for curves, in
the Galois model: `[D] ↦ κ(f)` with `n D = div f` (CJ8a `picTorsionEquiv`), using Kummer theory
`Fˣ/Fˣⁿ ≃ H¹(Gal(Ω/F), μₙ)` (continuous-kummer-theory) and the unramifiedness criterion
`isUnramifiedKummer_iff`. Over an algebraically closed `k` the functions without zeros and poles
are constants, hence `n`-th powers.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

namespace CurvesJacobian

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]
  (n : ℕ) [NeZero n]

attribute [local instance] isFunctionField_F

/-- The unramified classes: trivial on the inertia groups of all places `W ⊇ k` of `Ω`. -/
def unramifiedChars : Subgroup (ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω)) where
  carrier := {χ | ∀ (W : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ W) (σ : D.H)
    (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W),
    ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n χ) = 1}
  one_mem' := by intro W hk σ hσ; simp
  mul_mem' := by
    intro a b ha hb W hk σ hσ
    rw [map_mul, map_mul, ha W hk σ hσ, hb W hk σ hσ, one_mul]
  inv_mem' := by
    intro a ha W hk σ hσ
    rw [map_inv, map_inv, ha W hk σ hσ, inv_one]

omit [IsSepClosed Ω] [NeZero n] in
/-- A divisor is in `n • Div` iff all its coefficients are divisible by `n`. -/
lemma mem_nsmulDivisors_div_iff (f : F D) :
    Divisor.div k f ∈ nsmulDivisors k (F D) n ↔ ∀ P : Place k (F D), (n : ℤ) ∣ P.ord f := by
  constructor
  · rintro ⟨E, hE⟩ P
    have := congrArg (fun G : Divisor k (F D) ↦ G P) hE
    simp only [nsmulAddMonoidHom_apply, Finsupp.smul_apply, nsmul_eq_mul,
      Divisor.div_apply] at this
    exact ⟨E P, this.symm⟩
  · intro h
    refine ⟨Finsupp.mapRange (fun z : ℤ ↦ z / n) (by simp) (Divisor.div k f), ?_⟩
    ext P
    simp only [nsmulAddMonoidHom_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      Divisor.div_apply, nsmul_eq_mul]
    exact Int.mul_ediv_cancel' (h P)

variable [IsAlgClosed k]

omit [IsSepClosed Ω] [NeZero n] in
/-- Over an algebraically closed field, a function without zeros and poles is an `n`-th power. -/
lemma mem_nsmul_range_of_div_eq_zero (hn : 0 < n) (u : Additive (F D)ˣ)
    (hu : divHom k (F D) u = 0) : u ∈ (nsmulAddMonoidHom (α := Additive (F D)ˣ) n).range := by
  set c : F D := ((Additive.toMul u : (F D)ˣ) : F D)
  have hc : Divisor.div k c = 0 := hu
  have halg : IsAlgebraic k c := by
    by_contra htr
    obtain ⟨P, hP⟩ := Place.exists_ord_neg (k := k) (K := F D) htr
    have := congrArg (fun G : Divisor k (F D) ↦ G P) hc
    simp only [Divisor.div_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_isAlgebraic (k := k) (Ω := F D) halg
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq d hn
  have he0 : algebraMap k (F D) e ≠ 0 := by
    intro h
    rw [map_eq_zero_iff _ (algebraMap k (F D)).injective] at h
    rw [h, zero_pow hn.ne'] at he
    rw [← he, map_zero] at hd
    exact (Additive.toMul u).ne_zero hd.symm
  refine ⟨Additive.ofMul (Units.mk0 _ he0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  simp only [nsmulAddMonoidHom_apply, toMul_nsmul, toMul_ofMul, Units.val_pow_eq_pow_val,
    Units.val_mk0]
  rw [← map_pow, he, hd]

variable {n}

omit [IsAlgClosed k] in
/-- Kummer classes `v` with `div v ∈ n • Div` are unramified. -/
lemma kummer_mem_unramifiedChars (v : (F D)ˣ)
    (hv : Additive.ofMul v ∈ kummerClasses k (F D) n) :
    kummer n (F D) Ω v ∈ unramifiedChars D n := by
  have h := (isUnramifiedKummer_iff D n v).2 ((mem_nsmulDivisors_div_iff D n _).1 hv)
  exact h

omit [IsAlgClosed k] in
/-- `f ↦ κ(f)`, from Kummer classes to unramified characters. -/
noncomputable def kummerToUnramified :
    kummerClasses k (F D) n →+ Additive (unramifiedChars D n) where
  toFun v := Additive.ofMul ⟨kummer n (F D) Ω (Additive.toMul v.1),
    kummer_mem_unramifiedChars D _ v.2⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp

omit [IsAlgClosed k] in
lemma kummerToUnramified_surjective :
    Function.Surjective (kummerToUnramified D (n := n)) := by
  intro χ
  obtain ⟨v, hv⟩ := kummer_surjective n (F D) Ω (Additive.toMul χ).1
  have hunr : IsUnramifiedKummer D n v := by
    intro W hk σ hσ
    rw [hv]
    exact (Additive.toMul χ).2 W hk σ hσ
  have hmem : Additive.ofMul v ∈ kummerClasses k (F D) n :=
    (mem_nsmulDivisors_div_iff D n _).2 ((isUnramifiedKummer_iff D n v).1 hunr)
  refine ⟨⟨Additive.ofMul v, hmem⟩, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hv

lemma ker_kummerToUnramified (hn : 0 < n) :
    (kummerToUnramified D (n := n)).ker =
      (kummerTrivial k (F D) n).comap (kummerClasses k (F D) n).subtype := by
  ext x
  rcases x with ⟨v, hv⟩
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.coe_subtype]
  constructor
  · intro h
    have h' : kummer n (F D) Ω (Additive.toMul v) = 1 := by
      have := congrArg (fun x ↦ ((Additive.toMul x : unramifiedChars D n) :
        ContH1 (Ω ≃ₐ[F D] Ω) (Mu n Ω))) h
      simpa [kummerToUnramified] using this
    have hmem : Additive.toMul v ∈ (kummer n (F D) Ω).ker := h'
    rw [ker_kummer] at hmem
    obtain ⟨w, hw⟩ := hmem
    refine AddSubgroup.mem_sup_right ⟨Additive.ofMul w, ?_⟩
    apply Additive.toMul.injective
    simpa using hw
  · intro h
    obtain ⟨c, hc, _, ⟨w, rfl⟩, hcw⟩ := AddSubgroup.mem_sup.1 h
    obtain ⟨w', hw'⟩ := mem_nsmul_range_of_div_eq_zero D n hn c hc
    have hv' : v = n • (w' + w) := by rw [← hcw, ← hw', smul_add]; rfl
    apply Additive.toMul.injective
    apply Subtype.ext
    change kummer n (F D) Ω (Additive.toMul v) = 1
    rw [hv', toMul_nsmul, ← MonoidHom.mem_ker, ker_kummer]
    exact ⟨_, rfl⟩

/-- **`Pic(X)[n] ≃ Hom(Π_X, μₙ)`** in the Galois model: the `n`-torsion of the divisor class group
of `F` is isomorphic to the group of Kummer classes unramified at all places. -/
noncomputable def picTorsionEquivUnramified (hn : 0 < n) :
    picTorsion k (F D) n ≃+ Additive (unramifiedChars D n) :=
  (picTorsionEquiv hn).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (ker_kummerToUnramified D hn).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (kummerToUnramified_surjective D)))

end CurvesJacobian
