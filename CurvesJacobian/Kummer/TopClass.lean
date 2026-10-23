/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.H2Map

/-!
# `M_X / n` and the natural identifications given by a top class ([Mzk19] Prop. 1.2)

[Mzk19] = *Absolute anabelian cuspidalizations of proper hyperbolic curves*
(`Absolute Anabelian Cuspidalizations.txt`): l.302–305 define `M_X := Hom(H²(Δ_X, Ẑ), Ẑ)`, and
Prop. 1.2 (l.355–371) gives (i) the tautological isomorphism `H²(Δ_X, M_X) ≅ Ẑ` and (ii) the
unique isomorphism `M_X ≅ Ẑ(1)` sending the image of `1` (the tautological class) to the first
Chern class of a line bundle of degree `1`. Here, modulo `n` and for any topological group
`G ≃ₜ* Π̂_{g,0}` (`g ≥ 1`), in pure group theory:

* `CurvesJacobian.TopClass.zmodHom`, `monoidHom_ext_zmod`: homomorphisms out of `ℤ/n`;
* `CurvesJacobian.TopClass.TrivZ G n`: `ℤ/n` (written multiplicatively) with trivial `G`-action;
  `CurvesJacobian.TopClass.MXmod G n := Hom(H²(G, ℤ/n), ℤ/n)`, i.e. `M_X / n` (since
  `H²(Δ_X, Ẑ) ≅ Ẑ`), again with trivial action (a type synonym, with `MXmod.toHom` the identity
  to `H²(G, ℤ/n) →* ℤ/n`); `evAt u : M_X/n →* ℤ/n` the evaluation at `u`;
* `CurvesJacobian.TopClass.IsTaut t`: `t ∈ H²(G, M_X/n)` is **the tautological class**: for every
  `u ∈ H²(G, ℤ/n)`, the evaluation `ev_u : M_X/n → ℤ/n` sends `t` to `u`;
  **`exists_unique_isTaut`**: it exists and is unique (the class corresponding to
  `1 ∈ Ẑ ≅ H²(Δ_X, M_X)` of [Mzk19] Prop. 1.2(i), modulo `n`);
* **`CurvesJacobian.TopClass.exists_unique_mulEquiv`**: for a finite group `A` of order `n` with
  trivial action and a class `c` generating `H²(G, A)`, there is a unique isomorphism
  `ι : M_X/n ≃* A` with `ι_*(t) = c` ([Mzk19] Prop. 1.2(ii) modulo `n`, with `c` the first Chern
  class of a degree-1 line bundle and `A = μ_n`; `Kummer/ChernNatural.lean`).

The proofs use an orientation `G ≃ₜ* Π̂_{g,0}` and the relator value `H²(G, M) ≅ M`, which is
natural in `M` (`h2EquivAny_h2Map`); the statements do not depend on it.
-/

open Pi1 Pi1.Profinite Pi1.SurfaceGroup

noncomputable section

namespace CurvesJacobian.TopClass

/-! ### Homomorphisms out of `ℤ/n` -/

section ZMod

variable {n : ℕ} {B : Type*} [CommGroup B]

/-- The homomorphism `ℤ/n → B`, `1 ↦ b`, for `bⁿ = 1`. -/
def zmodHom (b : B) (hb : b ^ n = 1) : Multiplicative (ZMod n) →* B :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift n ⟨zmultiplesHom (Additive B) (Additive.ofMul b), by
    change ((n : ℕ) : ℤ) • Additive.ofMul b = 0
    rw [natCast_zsmul, ← ofMul_pow, hb, ofMul_one]⟩)

lemma zmodHom_ofAdd_one (b : B) (hb : b ^ n = 1) :
    zmodHom b hb (Multiplicative.ofAdd 1) = b := by
  rw [zmodHom, AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd,
    show (1 : ZMod n) = ((1 : ℤ) : ZMod n) from Int.cast_one.symm, ZMod.lift_coe]
  simp

/-- Homomorphisms out of `ℤ/n` are determined by the image of `1`. -/
lemma monoidHom_ext_zmod {f f' : Multiplicative (ZMod n) →* B}
    (h : f (Multiplicative.ofAdd 1) = f' (Multiplicative.ofAdd 1)) : f = f' := by
  refine MonoidHom.ext fun x ↦ ?_
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
  have hx : x = Multiplicative.ofAdd (1 : ZMod n) ^ z := by
    rw [← ofAdd_zsmul, zsmul_one, hz]
    rfl
  rw [hx, map_zpow, map_zpow, h]

lemma ofAdd_val_pow (x : ZMod n) [NeZero n] :
    Multiplicative.ofAdd x = Multiplicative.ofAdd (1 : ZMod n) ^ x.val := by
  rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]

end ZMod

section Defs

variable (G : Type*) [Group G] [TopologicalSpace G] (n : ℕ)

/-- `ℤ/n` (written multiplicatively) with the trivial action of `G`. -/
def TrivZ (_G : Type*) (n : ℕ) : Type := Multiplicative (ZMod n)

instance : CommGroup (TrivZ G n) := inferInstanceAs (CommGroup (Multiplicative (ZMod n)))

instance [NeZero n] : Finite (TrivZ G n) := inferInstanceAs (Finite (Multiplicative (ZMod n)))

instance : MulDistribMulAction G (TrivZ G n) := trivialAction G _

/-- The generator `1 ∈ ℤ/n`. -/
def TrivZ.one : TrivZ G n := Multiplicative.ofAdd (1 : ZMod n)

/-- **`M_X / n := Hom(H²(G, ℤ/n), ℤ/n)`** ([Mzk19] l.302–305 modulo `n`). -/
def MXmod : Type _ := H2lc G (TrivZ G n) →* TrivZ G n

instance : CommGroup (MXmod G n) :=
  inferInstanceAs (CommGroup (H2lc G (TrivZ G n) →* TrivZ G n))

instance : MulDistribMulAction G (MXmod G n) := trivialAction G _

/-- `M_X/n` is `Hom(H²(G, ℤ/n), ℤ/n)` (the identity of the type synonym). -/
def MXmod.toHom : MXmod G n ≃* (H2lc G (TrivZ G n) →* TrivZ G n) := MulEquiv.refl _

variable {G n}

/-- The evaluation `ev_u : M_X/n → ℤ/n` at `u ∈ H²(G, ℤ/n)`. -/
def evAt (u : H2lc G (TrivZ G n)) : MXmod G n →* TrivZ G n where
  toFun φ := MXmod.toHom G n φ u
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma evAt_apply (u : H2lc G (TrivZ G n)) (φ : MXmod G n) :
    evAt u φ = MXmod.toHom G n φ u := rfl

variable (G n) in
/-- **The tautological class** `t ∈ H²(G, M_X/n)`: `ev_u` sends it to `u` for every
`u ∈ H²(G, ℤ/n)` ([Mzk19] Prop. 1.2(i): the class corresponding to `1 ∈ Ẑ ≅ H²(Δ_X, M_X)`). -/
def IsTaut (t : H2lc G (MXmod G n)) : Prop :=
  ∀ u : H2lc G (TrivZ G n), h2Map (evAt u) (fun _ _ ↦ rfl) t = u

end Defs

section Orientation

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ} [NeZero n] {g : ℕ}
  (hg : 0 < g) (e : G ≃ₜ* ProfiniteSurfaceGroup g 0)

/-- The relator-value isomorphism `H²(G, ℤ/n) ≅ ℤ/n` of an orientation `e`. -/
abbrev eZ : H2lc G (TrivZ G n) ≃* TrivZ G n :=
  h2EquivAny hg e fun _ _ ↦ rfl

include hg e in
lemma finite_h2 : Finite (H2lc G (TrivZ G n)) := Finite.of_equiv _ (eZ hg e).symm.toEquiv

include hg e in
lemma finite_mxmod : Finite (MXmod G n) := by
  haveI := finite_h2 (n := n) hg e
  exact Finite.of_injective
    (fun φ : MXmod G n ↦ (MXmod.toHom G n φ : H2lc G (TrivZ G n) → TrivZ G n))
    (DFunLike.coe_injective.comp (MXmod.toHom G n).injective)

/-- `φ₀ = eZ` as an element of `M_X/n`. -/
abbrev phi0 : MXmod G n := (MXmod.toHom G n).symm (eZ hg e).toMonoidHom

/-- Elements of `M_X/n` are determined by their value at `u₀ = eZ⁻¹(1)`. -/
lemma mxmod_ext {φ φ' : MXmod G n} (h : evAt ((eZ hg e).symm (TrivZ.one G n)) φ =
    evAt ((eZ hg e).symm (TrivZ.one G n)) φ') : φ = φ' := by
  apply (MXmod.toHom G n).injective
  have : (MXmod.toHom G n φ).comp (eZ hg e).symm.toMonoidHom =
      (MXmod.toHom G n φ').comp (eZ hg e).symm.toMonoidHom :=
    monoidHom_ext_zmod (n := n) h
  refine MonoidHom.ext fun x ↦ ?_
  have h2 := DFunLike.congr_fun this (eZ hg e x)
  simpa using h2

/-- Every element of `M_X/n` is a power of `φ₀`. -/
lemma eq_phi0_pow (φ : MXmod G n) :
    φ = phi0 hg e ^ (Multiplicative.toAdd
      (evAt ((eZ hg e).symm (TrivZ.one G n)) φ : Multiplicative (ZMod n))).val := by
  refine mxmod_ext hg e ?_
  rw [map_pow]
  change _ = (eZ hg e) ((eZ hg e).symm (TrivZ.one G n)) ^ _
  rw [MulEquiv.apply_symm_apply]
  exact ofAdd_val_pow _

/-- The class `t₀ = e_{M_X/n}⁻¹(φ₀)`. -/
def taut0 : H2lc G (MXmod G n) :=
  haveI := finite_mxmod (n := n) hg e
  (h2EquivAny hg e fun _ _ ↦ rfl).symm (phi0 hg e)

lemma eMX_isTaut {t : H2lc G (MXmod G n)} (ht : IsTaut G n t) :
    haveI := finite_mxmod (n := n) hg e
    h2EquivAny hg e (fun _ _ ↦ rfl) t = phi0 hg e := by
  haveI := finite_mxmod (n := n) hg e
  apply (MXmod.toHom G n).injective
  refine MonoidHom.ext fun u ↦ ?_
  have h := h2EquivAny_h2Map hg e (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (evAt u) t
  rw [ht u] at h
  exact h.symm

lemma isTaut_taut0 : IsTaut G n (taut0 hg e) := by
  haveI := finite_mxmod (n := n) hg e
  intro u
  apply (eZ hg e).injective
  have h := h2EquivAny_h2Map hg e (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (evAt u)
    (taut0 hg e)
  rw [h, taut0, MulEquiv.apply_symm_apply]
  rfl

end Orientation

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ} [NeZero n] {g : ℕ}

/-- **[Mzk19] Prop. 1.2(i) modulo `n`**: the tautological class of `H²(G, M_X/n)` exists and is
unique (`G ≃ₜ* Π̂_{g,0}`, `g ≥ 1`). -/
theorem exists_unique_isTaut (hg : 0 < g) (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0)) :
    ∃! t : H2lc G (MXmod G n), IsTaut G n t := by
  obtain ⟨e⟩ := he
  haveI := finite_mxmod (n := n) hg e
  refine ⟨taut0 hg e, isTaut_taut0 hg e, fun t ht ↦ ?_⟩
  apply (h2EquivAny hg e (fun _ _ ↦ rfl)).injective
  rw [eMX_isTaut hg e ht, eMX_isTaut hg e (isTaut_taut0 hg e)]

variable {A : Type*} [CommGroup A] [Finite A] [MulDistribMulAction G A]

/-- **[Mzk19] Prop. 1.2(ii) modulo `n`**: let `A` be a group of order `n` with trivial
`G`-action and `c` a generator of `H²(G, A)` (`G ≃ₜ* Π̂_{g,0}`, `g ≥ 1`). Then there is a unique
isomorphism `ι : M_X/n ≃* A` sending the tautological class to `c`. -/
theorem exists_unique_mulEquiv (hg : 0 < g) (he : Nonempty (G ≃ₜ* ProfiniteSurfaceGroup g 0))
    (htriv : ∀ (γ : G) (a : A), γ • a = a) (hA : Nat.card A = n) (c : H2lc G A)
    (hc : ∀ c' : H2lc G A, c' ∈ Subgroup.zpowers c) {t : H2lc G (MXmod G n)}
    (ht : IsTaut G n t) :
    ∃! ι : MXmod G n ≃* A,
      h2Map ι.toMonoidHom (fun γ φ ↦ by rw [htriv]; rfl) t = c := by
  obtain ⟨e⟩ := he
  haveI := finite_mxmod (n := n) hg e
  set eA := h2EquivAny hg e htriv
  set a := eA c
  -- `a` generates `A`, hence has order `n`
  have ha : ∀ x : A, x ∈ Subgroup.zpowers a := fun x ↦ by
    obtain ⟨k, hk⟩ := hc (eA.symm x)
    refine ⟨k, ?_⟩
    change a ^ k = x
    rw [← map_zpow, show c ^ k = eA.symm x from hk, MulEquiv.apply_symm_apply]
  have hord : orderOf a = n := by
    rw [← hA, ← Nat.card_zpowers, show Subgroup.zpowers a = ⊤ from
      eq_top_iff.2 fun x _ ↦ ha x, Subgroup.card_top]
  have han : a ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one a
  -- the key equivalence: `ι_* t = c ↔ ι φ₀ = a`
  have key : ∀ ι : MXmod G n →* A, h2Map ι (fun γ φ ↦ by rw [htriv]; rfl) t = c ↔
      ι (phi0 hg e) = a := fun ι ↦ by
    rw [← eA.injective.eq_iff, h2EquivAny_h2Map hg e (fun _ _ ↦ rfl) htriv ι t,
      eMX_isTaut hg e ht]
  -- the homomorphism
  set u₀ := (eZ hg e).symm (TrivZ.one G n)
  let ι₀ : MXmod G n →* A := (zmodHom (n := n) a han).comp (evAt u₀)
  have hι₀ : ι₀ (phi0 hg e) = a := by
    change zmodHom a han ((eZ hg e) u₀) = a
    rw [MulEquiv.apply_symm_apply]
    exact zmodHom_ofAdd_one a han
  have hpow : ∀ φ : MXmod G n,
      ι₀ φ = a ^ (Multiplicative.toAdd (evAt u₀ φ : Multiplicative (ZMod n))).val := fun φ ↦ by
    conv_lhs => rw [eq_phi0_pow hg e φ]
    rw [map_pow, hι₀]
  have hbij : Function.Bijective ι₀ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro φ hφ
      rw [hpow, ← orderOf_dvd_iff_pow_eq_one, hord] at hφ
      have hlt := ZMod.val_lt (Multiplicative.toAdd (evAt u₀ φ : Multiplicative (ZMod n)))
      have h0 : (Multiplicative.toAdd (evAt u₀ φ : Multiplicative (ZMod n))).val = 0 :=
        Nat.eq_zero_of_dvd_of_lt hφ hlt
      rw [eq_phi0_pow hg e φ, h0, pow_zero]
    · intro x
      obtain ⟨k, rfl⟩ := ha x
      exact ⟨phi0 hg e ^ k, by rw [map_zpow, hι₀]⟩
  refine ⟨MulEquiv.ofBijective ι₀ hbij, (key _).2 hι₀, fun ι hι ↦ ?_⟩
  have h1 := (key ι.toMonoidHom).1 hι
  refine MulEquiv.ext fun φ ↦ ?_
  change ι φ = ι₀ φ
  rw [eq_phi0_pow hg e φ, map_pow, map_pow, hι₀]
  exact congrArg (· ^ _) h1

end Main

end CurvesJacobian.TopClass
