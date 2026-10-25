/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.KummerAction
import CurvesJacobian.CuspChar.DetAlgebra

/-!
# The weight identity for `π₁ᵉᵗ(U)`: `det(Ψ^*)² = χ^{2g + 2r − 2}`

Setting of `CurvesJacobian/CuspChar/KummerAction.lean`: a semilinear automorphism `φ` of `Ω`
(acting on `μ_n` by `χ`, fixing the cusps) and the induced automorphism `Ψ` of `π₁ᵉᵗ(U)`. Let
`M = Hom_cont(π₁ᵉᵗ(U), ℤ/n)`, free of rank `2g + r − 1`, `n = l^k`. Then
(`CurvesJacobian.CuspChar.det_pull_sq`)

  `det(e0 ↦ e0 ∘ Ψ | M)² = χ^{2g + 2(r − 1)}`.

Proof: the kernel `A` of the residue map is `Pic(F)[n]` (`picEquivKer`), free of rank `2g`
(`#Pic(F)[n] = n^{2g}`), carrying the Weil pairing, perfect (nondegeneracy) and
`χ`-equivariant, so `det(Ψ^*|_A)² = χ^{2g}` (`det_sq_of_pairing`); on `M ⧸ A ≅ (ℤ/n)^{cusps}_0`
`Ψ^*` is `χ · id` (`resMap_pull`), so its determinant is `χ^{r − 1}`
(`det_mapQ_eq_pow_of_sub_mem`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Pi1.Orbifold
  KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer Module

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.CuspChar

section ZModLocal

/-- `ℤ/p^k` is a local ring. -/
theorem isLocalRing_zmod_pow (p k : ℕ) [hp : Fact p.Prime] (hk : 0 < k) :
    IsLocalRing (ZMod (p ^ k)) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Nontrivial (ZMod (p ^ k)) := ZMod.nontrivial_iff.2
    (Nat.one_lt_pow hk.ne' hp.out.one_lt).ne'
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  by_cases ha : p ∣ a.val
  · right
    have hc : Nat.Coprime (1 + (p ^ k - 1) * a.val) (p ^ k) := by
      refine Nat.Coprime.pow_right _ ?_
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
      intro h
      have h2 : p ∣ (p ^ k - 1) * a.val := Dvd.dvd.mul_left ha _
      exact hp.out.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left h2).1 h))
    have h1 : (1 - a : ZMod (p ^ k)) = ((1 + (p ^ k - 1) * a.val : ℕ) : ZMod (p ^ k)) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hp.out.pos),
        ZMod.natCast_self, ZMod.natCast_zmod_val]
      push_cast
      ring
    rw [h1, ZMod.isUnit_iff_coprime]
    exact hc
  · left
    have hc : Nat.Coprime a.val (p ^ k) := by
      refine Nat.Coprime.pow_right _ ?_
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
      exact ha
    rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
    exact hc

end ZModLocal

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [IsAlgClosed k] [CharZero k]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] [IsCurveOver k X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  (hH : D.H ≤ D.HL) {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U : X.Opens} [Nonempty U] (n : ℕ) [NeZero n] (hU : (U : Set X)ᶜ.Finite)

attribute [local instance] isFunctionField_F

section Weil

/-- The `n`-th power of a value of the Weil pairing on `Pic[n]` is `1`. -/
lemma weilPairing_pow_n (x y : picTorsion k (F D) n) : weilPairing n x y ^ n = 1 := by
  have h : ∀ m : ℕ, weilPairing n (m • x) y = weilPairing n x y ^ m := by
    intro m
    induction m with
    | zero => rw [zero_smul, weilPairing_zero_left, pow_zero]
    | succ m ih => rw [succ_nsmul, weilPairing_add_left, ih, pow_succ]
  rw [← h n]
  have : n • x = 0 := Subtype.ext x.2
  rw [this, weilPairing_zero_left]

/-- The Weil pairing as a root of unity in `Ω`. -/
def weilMu (x y : picTorsion k (F D) n) : Mu n Ω :=
  Mu.mk (Units.mk0 (algebraMap k Ω (weilPairing n x y))
    ((map_ne_zero _).2 (weilPairing_ne_zero x y))) (by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ← map_pow,
      weilPairing_pow_n, map_one])

lemma val_weilMu (x y : picTorsion k (F D) n) :
    ((Mu.val (weilMu D n x y) : Ωˣ) : Ω) = algebraMap k Ω (weilPairing n x y) :=
  rfl

/-- The Weil pairing with values in `ℤ/n`. -/
def wlog (x y : picTorsion k (F D) n) : ZMod n :=
  Multiplicative.toAdd (logMu n Ω (weilMu D n x y))

lemma weilMu_add_left (x x' y : picTorsion k (F D) n) :
    weilMu D n (x + x') y = weilMu D n x y * weilMu D n x' y := by
  apply Mu.ext; apply Units.ext
  simp [val_weilMu, weilPairing_add_left]

lemma weilMu_add_right (x y y' : picTorsion k (F D) n) :
    weilMu D n x (y + y') = weilMu D n x y * weilMu D n x y' := by
  apply Mu.ext; apply Units.ext
  simp [val_weilMu, weilPairing_add_right]

lemma wlog_add_left (x x' y : picTorsion k (F D) n) :
    wlog D n (x + x') y = wlog D n x y + wlog D n x' y := by
  simp [wlog, weilMu_add_left]

lemma wlog_add_right (x y y' : picTorsion k (F D) n) :
    wlog D n x (y + y') = wlog D n x y + wlog D n x y' := by
  simp [wlog, weilMu_add_right]

lemma wlog_zero_left (y : picTorsion k (F D) n) : wlog D n 0 y = 0 := by
  have h := wlog_add_left D n 0 0 y
  rw [add_zero] at h
  linear_combination -h

lemma wlog_zero_right (x : picTorsion k (F D) n) : wlog D n x 0 = 0 := by
  have h := wlog_add_right D n x 0 0
  rw [add_zero] at h
  linear_combination -h

lemma wlog_nsmul_left (m : ℕ) (x y : picTorsion k (F D) n) :
    wlog D n (m • x) y = m * wlog D n x y := by
  induction m with
  | zero => rw [zero_nsmul, wlog_zero_left, Nat.cast_zero, zero_mul]
  | succ m ih => rw [succ_nsmul, wlog_add_left, ih]; push_cast; ring

lemma wlog_nsmul_right (m : ℕ) (x y : picTorsion k (F D) n) :
    wlog D n x (m • y) = m * wlog D n x y := by
  induction m with
  | zero => rw [zero_nsmul, wlog_zero_right, Nat.cast_zero, zero_mul]
  | succ m ih => rw [succ_nsmul, wlog_add_right, ih]; push_cast; ring

include hH hk in
/-- **Nondegeneracy of the Weil pairing on `Pic(F)[n]`.** -/
lemma weilPairing_nondeg (x : picTorsion k (F D) n) (h : ∀ y, weilPairing n x y = 1) :
    x = 0 :=
  weilPairing_nondegenerate_of_algEquiv (functionFieldEquivF hH hk).symm
    (fun a ha ↦ GenericPoint.weilPairing_nondegenerate k X a ha) x h

include hH hk in
lemma eq_zero_of_wlog (x : picTorsion k (F D) n) (h : ∀ y, wlog D n x y = 0) : x = 0 := by
  refine weilPairing_nondeg D X eL hk hH n x fun y ↦ ?_
  have h1 := h y
  have h2 : weilMu D n x y = 1 :=
    (logMu n Ω).injective (by rw [map_one]; exact toAdd_eq_zero.1 h1)
  have h3 := congrArg (fun ζ : Mu n Ω ↦ ((Mu.val ζ : Ωˣ) : Ω)) h2
  simp only [val_weilMu, map_one, Units.val_one] at h3
  exact (algebraMap k Ω).injective (by rw [h3, map_one])

end Weil

section Det

variable (φ : Ω ≃+* Ω) (hφF : ∀ x : F D, φ (x : Ω) ∈ F D)
  (hφF' : ∀ x : F D, φ.symm (x : Ω) ∈ F D)
  (hφk : ∀ c : k, φ (algebraMap k Ω c) ∈ Set.range (algebraMap k Ω) ∧
    φ.symm (algebraMap k Ω c) ∈ Set.range (algebraMap k Ω))
  (Ψ : PiU D X eL U ≃ₜ*
    PiU D X eL U)
  (hΨ : ∀ σ, Ψ (qU D X eL hH σ) = qU D X eL hH (conjH D φ hφF' σ))
  (χ : (ZMod n)ˣ)
  (hχ : ∀ ζ : Mu n Ω, φ ((Mu.val ζ : Ωˣ) : Ω) = ((Mu.val ζ : Ωˣ) : Ω) ^ (χ : ZMod n).val)
  (hcusp : ∀ c : CuspPl D X eL hH U, ∀ x : F D, phiF D φ hφF hφF' x ∈ c.1.1 ↔ x ∈ c.1.1)

include hχ in
lemma wlog_phiInv (x y : picTorsion k (F D) n) :
    wlog D n x y = (χ : ZMod n) * wlog D n
      ⟨picMap (phiCi D φ hφF hφF' hφk) x, picMap_mem_picTorsion' _ x.2⟩
      ⟨picMap (phiCi D φ hφF hφF' hφk) y, picMap_mem_picTorsion' _ y.2⟩ := by
  refine logMu_of_val_eq n φ χ hχ ?_
  rw [val_weilMu, val_weilMu, weilPairing_picMap]
  apply φ.symm.injective
  rw [φ.symm_apply_apply, IsScalarTower.algebraMap_apply k (F D) Ω,
    IsScalarTower.algebraMap_apply k (F D) Ω, ← constRes_spec]
  rfl

/-- The module of characters. -/
abbrev Mch (U' : X.Opens) [Nonempty U'] :=
  charSpace n (⊤ : OpenSubgroup (PiU D X eL U'))

/-- The kernel of the residue map. -/
abbrev Aker (U' : X.Opens) [Nonempty U'] : Submodule (ZMod n) (Mch D X eL n U') :=
  LinearMap.ker (resMap D X eL hH n (U := U'))

omit [IsGalois (K₀ k t) Ω] in
lemma smul_eq_val_nsmul {V : Type*} [AddCommGroup V] [Module (ZMod n) V] (c : ZMod n) (v : V) :
    c • v = c.val • v := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  exact Nat.cast_smul_eq_nsmul (ZMod n) c.val v

section Abstract

variable {T A : Type*} [AddCommGroup T] [AddCommGroup A] [Module (ZMod n) A] (P : T ≃+ A)
  (w : T → T → ZMod n) (hl : ∀ x x' y, w (x + x') y = w x y + w x' y)
  (hr : ∀ x y y', w x (y + y') = w x y + w x y')
  (hsl : ∀ (m : ℕ) x y, w (m • x) y = m * w x y) (hsr : ∀ (m : ℕ) x y, w x (m • y) = m * w x y)

/-- The bilinear form `(a, b) ↦ w(P⁻¹ a, P⁻¹ b)` on `A`, for a biadditive `w` on `T` and
`P : T ≃+ A`. -/
def pairOfEquiv : A →ₗ[ZMod n] A →ₗ[ZMod n] ZMod n :=
  LinearMap.mk₂ (ZMod n) (fun a b ↦ w (P.symm a) (P.symm b))
    (fun a a' b ↦ by
      change w (P.symm (a + a')) (P.symm b) = w (P.symm a) (P.symm b) + w (P.symm a') (P.symm b)
      rw [map_add, hl])
    (fun c a b ↦ by
      change w (P.symm (c • a)) (P.symm b) = c • w (P.symm a) (P.symm b)
      rw [smul_eq_val_nsmul n c a, map_nsmul, hsl, ZMod.natCast_zmod_val, smul_eq_mul])
    (fun a b b' ↦ by
      change w (P.symm a) (P.symm (b + b')) = w (P.symm a) (P.symm b) + w (P.symm a) (P.symm b')
      rw [map_add, hr])
    (fun c a b ↦ by
      change w (P.symm a) (P.symm (c • b)) = c • w (P.symm a) (P.symm b)
      rw [smul_eq_val_nsmul n c b, map_nsmul, hsr, ZMod.natCast_zmod_val, smul_eq_mul])

lemma pairOfEquiv_apply (a b : A) :
    pairOfEquiv n P w hl hr hsl hsr a b = w (P.symm a) (P.symm b) :=
  rfl

/-- A nondegenerate `w` gives an injective pairing. -/
lemma pairOfEquiv_injective (hnd : ∀ x, (∀ y, w x y = 0) → x = 0) :
    Function.Injective (pairOfEquiv n P w hl hr hsl hsr) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h : ∀ y, w (P.symm a) y = 0 := fun y ↦ by
    have := LinearMap.congr_fun ha (P y)
    rwa [pairOfEquiv_apply, AddEquiv.symm_apply_apply, LinearMap.zero_apply] at this
  rw [← P.apply_symm_apply a, hnd _ h, map_zero]

/-- Equivariance of `pairOfEquiv` from equivariance of `w`. -/
lemma pairOfEquiv_pull (fA : A → A) (τ' : T → T) (c : ZMod n)
    (hfA : ∀ z, fA (P z) = c • P (τ' z)) (hτ : ∀ x y, w x y = c * w (τ' x) (τ' y)) (a b : A) :
    pairOfEquiv n P w hl hr hsl hsr (fA a) (fA b) = c * pairOfEquiv n P w hl hr hsl hsr a b := by
  obtain ⟨x, rfl⟩ := P.surjective a
  obtain ⟨y, rfl⟩ := P.surjective b
  rw [pairOfEquiv_apply, pairOfEquiv_apply, hfA, hfA, smul_eq_val_nsmul n c (P (τ' x)),
    smul_eq_val_nsmul n c (P (τ' y)), ← map_nsmul P c.val (τ' x), ← map_nsmul P c.val (τ' y),
    P.symm_apply_apply, P.symm_apply_apply, P.symm_apply_apply, P.symm_apply_apply, hsl, hsr,
    hτ x y, ZMod.natCast_zmod_val]

end Abstract

/-- An injective pairing on a finite free `ℤ/n`-module is perfect. -/
lemma bijective_of_injective_pairing {A : Type*} [AddCommGroup A] [Module (ZMod n) A]
    [Module.Free (ZMod n) A] [Module.Finite (ZMod n) A] (e : A →ₗ[ZMod n] A →ₗ[ZMod n] ZMod n)
    (he : Function.Injective e) : Function.Bijective e := by
  classical
  haveI : Finite A := Module.finite_of_finite (ZMod n)
  haveI : Finite (Module.Dual (ZMod n) A) := Module.finite_of_finite (ZMod n)
  refine he.bijective_of_nat_card_le ?_
  rw [Nat.card_congr (Module.Free.chooseBasis (ZMod n) A).toDualEquiv.toEquiv]

section Rank

variable {R M N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] [AddCommGroup N] [Module R N] (res : M →ₗ[R] N)
  [Module.Free R (LinearMap.range res)]

/-- The kernel of a map from a finite free module with free image is finite free. -/
lemma free_finite_ker :
    Module.Free R (LinearMap.ker res) ∧ Module.Finite R (LinearMap.ker res) := by
  haveI : Module.Free R (M ⧸ LinearMap.ker res) := Module.Free.of_equiv res.quotKerEquivRange.symm
  exact ⟨free_of_free_quotient _, finite_of_free_quotient _⟩

/-- `rank M = rank (ker res) + rank (im res)`. -/
lemma finrank_eq_ker_add_range :
    finrank R M = finrank R (LinearMap.ker res) + finrank R (LinearMap.range res) := by
  haveI : Module.Free R (M ⧸ LinearMap.ker res) := Module.Free.of_equiv res.quotKerEquivRange.symm
  obtain ⟨h1, h2⟩ := free_finite_ker res
  rw [finrank_eq_finrank_add_finrank_quotient (LinearMap.ker res),
    res.quotKerEquivRange.finrank_eq]

/-- **Determinant from a perfect pairing on the kernel**: if `f` acts on the image of `res` by
`c` and preserves a perfect pairing on `ker res` up to `c`, then
`det f ^ 2 = c ^ (rank (ker res) + 2 rank (im res))`. -/
theorem det_sq_of_ker_pairing (f : M →ₗ[R] M) (c : R) (hf : ∀ x, res (f x) = c • res x)
    (hA : ∀ a ∈ LinearMap.ker res, f a ∈ LinearMap.ker res)
    (e : LinearMap.ker res →ₗ[R] LinearMap.ker res →ₗ[R] R) (he : Function.Bijective e)
    (hfe : ∀ a b, e (f.restrict hA a) (f.restrict hA b) = c * e a b) :
    LinearMap.det f ^ 2 =
      c ^ (finrank R (LinearMap.ker res) + 2 * finrank R (LinearMap.range res)) := by
  haveI : Module.Free R (M ⧸ LinearMap.ker res) := Module.Free.of_equiv res.quotKerEquivRange.symm
  obtain ⟨h1, h2⟩ := free_finite_ker res
  have hdetA := det_sq_of_pairing e he (f.restrict hA) c hfe
  have hdetQ := det_mapQ_eq_pow_of_sub_mem (LinearMap.ker res) f (fun a ha ↦ hA a ha) c
    fun x ↦ by rw [LinearMap.mem_ker, map_sub, map_smul, hf, sub_self]
  rw [det_eq_det_restrict_mul_det_mapQ (LinearMap.ker res) f hA, mul_pow, hdetA, hdetQ, ← pow_mul,
    ← pow_add, res.quotKerEquivRange.finrank_eq, mul_comm _ 2]

end Rank

/-- A free finite module over `ℤ/n` has `n ^ rank` elements. -/
lemma natCard_free (V : Type*) [AddCommGroup V] [Module (ZMod n) V] [Nontrivial (ZMod n)]
    [Module.Free (ZMod n) V] [Module.Finite (ZMod n) V] :
    Nat.card V = n ^ finrank (ZMod n) V := by
  have b := Module.Free.chooseBasis (ZMod n) V
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

/-- The rank of a free finite `ℤ/n`-module (`n > 1`) in bijection with a set of `n ^ r`
elements is `r`. -/
lemma finrank_eq_of_natCard {V T : Type*} [AddCommGroup V] [Module (ZMod n) V]
    [Nontrivial (ZMod n)] [Module.Free (ZMod n) V] [Module.Finite (ZMod n) V] (P : T ≃ V)
    {r : ℕ} (h : Nat.card T = n ^ r) : finrank (ZMod n) V = r := by
  have hn1 : 1 < n := by
    have := (ZMod.nontrivial_iff (n := n)).1 inferInstance
    have := NeZero.ne n
    omega
  have h1 := natCard_free n V
  rw [← Nat.card_congr P, h] at h1
  exact (Nat.pow_right_injective hn1 h1).symm

/-- Restriction of a sum-zero family to the complement of `c₀`. -/
def sumZeroRestrict [Fintype (CuspPl D X eL hH U)] (c₀ : CuspPl D X eL hH U) :
    sumZero D X eL hH n (U := U) →ₗ[ZMod n] ({c // c ≠ c₀} → ZMod n) where
  toFun a c := a.1 c.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma sumZeroRestrict_bijective [Fintype (CuspPl D X eL hH U)] (c₀ : CuspPl D X eL hH U) :
    Function.Bijective (sumZeroRestrict D X eL hH n c₀) := by
  classical
  have hs : ∀ a : CuspPl D X eL hH U → ZMod n,
      ∑ c, a c = a c₀ + ∑ c : {c // c ≠ c₀}, a c := fun a ↦
    Fintype.sum_eq_add_sum_subtype_ne a c₀
  constructor
  · intro a b hab
    apply Subtype.ext
    funext c
    by_cases h : c = c₀
    · rw [h]
      have ha : ∑ c', a.1 c' = 0 := a.2
      have hb : ∑ c', b.1 c' = 0 := b.2
      rw [hs] at ha hb
      have : ∑ c' : {c' // c' ≠ c₀}, a.1 c'.1 = ∑ c' : {c' // c' ≠ c₀}, b.1 c'.1 :=
        Finset.sum_congr rfl fun c' _ ↦ congrFun hab c'
      linear_combination ha - hb - this
    · exact congrFun hab ⟨c, h⟩
  · intro b
    refine ⟨⟨fun c ↦ if h : c = c₀ then -∑ c' : {c // c ≠ c₀}, b c' else b ⟨c, h⟩, ?_⟩, ?_⟩
    · change ∑ c, _ = 0
      rw [hs, dif_pos rfl, neg_add_eq_zero]
      exact Finset.sum_congr rfl fun c _ ↦ by rw [dif_neg c.2]
    · funext c
      change (if h : c.1 = c₀ then _ else b ⟨c.1, h⟩) = b c
      rw [dif_neg c.2]

/-- The sum-zero submodule is free. -/
lemma free_sumZero [Fintype (CuspPl D X eL hH U)] :
    Module.Free (ZMod n) (sumZero D X eL hH n (U := U)) := by
  by_cases he : IsEmpty (CuspPl D X eL hH U)
  · haveI : Subsingleton (sumZero D X eL hH n (U := U)) :=
      ⟨fun a b ↦ Subtype.ext (funext fun c ↦ he.elim c)⟩
    exact Module.Free.of_subsingleton _ _
  obtain ⟨c₀⟩ := not_isEmpty_iff.1 he
  exact Module.Free.of_equiv
    (LinearEquiv.ofBijective _ (sumZeroRestrict_bijective D X eL hH n c₀)).symm

/-- The Weil pairing on the kernel of the residue map. -/
def pairA : Aker D X eL hH n U →ₗ[ZMod n] Aker D X eL hH n U →ₗ[ZMod n] ZMod n :=
  pairOfEquiv n (picEquivKer D X eL hk hH hτ n hU) (wlog D n) (wlog_add_left D n)
    (wlog_add_right D n) (wlog_nsmul_left D n) (wlog_nsmul_right D n)

/-- The Weil pairing on the kernel of the residue map is perfect. -/
lemma pairA_bijective [Module.Free (ZMod n) (Aker D X eL hH n U)]
    [Module.Finite (ZMod n) (Aker D X eL hH n U)] :
    Function.Bijective (pairA D X eL hk hH hτ n hU) :=
  bijective_of_injective_pairing n (pairA D X eL hk hH hτ n hU)
    (pairOfEquiv_injective n (picEquivKer D X eL hk hH hτ n hU) (wlog D n) (wlog_add_left D n)
      (wlog_add_right D n) (wlog_nsmul_left D n) (wlog_nsmul_right D n)
      fun x hx ↦ eq_zero_of_wlog D X eL hk hH n x hx)

include hk hτ hU hΨ hχ hcusp hφk in
/-- The pull-back `Ψ^*` preserves the kernel of the residue map. -/
lemma pull_mem_Aker (a : Mch D X eL n U) (ha : a ∈ Aker D X eL hH n U) :
    pullΨ D X eL n Ψ a ∈ Aker D X eL hH n U := by
  rw [LinearMap.mem_ker] at ha ⊢
  rw [resMap_pull D X eL hk hH hτ n hU φ hφF hφF' Ψ hΨ χ hχ hφk hcusp, ha, smul_zero]

include hΨ hχ hcusp in
lemma restrict_picEquivKer (z : picTorsion k (F D) n) :
    (pullΨ D X eL n Ψ).toLinearMap.restrict
        (pull_mem_Aker D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp)
        (picEquivKer D X eL hk hH hτ n hU z) =
      (χ : ZMod n) • picEquivKer D X eL hk hH hτ n hU
        ⟨picMap (phiCi D φ hφF hφF' hφk) z, picMap_mem_picTorsion' _ z.2⟩ := by
  apply Subtype.ext
  simp only [LinearMap.restrict_apply, LinearEquiv.coe_coe, Submodule.coe_smul, coe_picEquivKer]
  exact pull_picChar D X eL hk hH hτ n hU φ hφF hφF' Ψ hΨ χ hχ hφk z

include hΨ hχ hcusp in
/-- **The pull-back multiplies the Weil pairing by `χ`.** -/
lemma pairA_pull (a b : Aker D X eL hH n U) :
    pairA D X eL hk hH hτ n hU
        ((pullΨ D X eL n Ψ).toLinearMap.restrict
          (pull_mem_Aker D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp) a)
        ((pullΨ D X eL n Ψ).toLinearMap.restrict
          (pull_mem_Aker D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp) b) =
      (χ : ZMod n) * pairA D X eL hk hH hτ n hU a b := by
  let τ' : picTorsion k (F D) n → picTorsion k (F D) n := fun z ↦
    ⟨picMap (phiCi D φ hφF hφF' hφk) z, picMap_mem_picTorsion' _ z.2⟩
  have h := pairOfEquiv_pull n (picEquivKer D X eL hk hH hτ n hU) (wlog D n) (wlog_add_left D n)
    (wlog_add_right D n) (wlog_nsmul_left D n) (wlog_nsmul_right D n)
    ((pullΨ D X eL n Ψ).toLinearMap.restrict
      (pull_mem_Aker D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp)) τ'
    (χ : ZMod n) (restrict_picEquivKer D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp)
    (wlog_phiInv D n φ hφF hφF' hφk χ hχ) a b
  exact h

variable (hl : IsLocalRing (ZMod n))
  [Module.Free (ZMod n) (Mch D X eL n U)] [Module.Finite (ZMod n) (Mch D X eL n U)]
  (g r₀ : ℕ) (hMrank : finrank (ZMod n) (Mch D X eL n U) = 2 * g + r₀ - 1)
  (hcard : Nat.card (picTorsion k (F D) n) = n ^ (2 * g))

include hk hτ hU in
/-- The image of the residue map is free. -/
lemma free_range_resMap [Finite (CuspPl D X eL hH U)] :
    Module.Free (ZMod n) (LinearMap.range (resMap D X eL hH n (U := U))) :=
  haveI := Fintype.ofFinite (CuspPl D X eL hH U)
  haveI := free_sumZero D X eL hH n (U := U)
  Module.Free.of_equiv (LinearEquiv.ofEq _ _ (range_resMap D X eL hk hH hτ n hU)).symm

include hk hτ hU hl hcard in
/-- The kernel of the residue map has rank `2g`. -/
lemma finrank_Aker [Module.Free (ZMod n) (Aker D X eL hH n U)]
    [Module.Finite (ZMod n) (Aker D X eL hH n U)] :
    finrank (ZMod n) (Aker D X eL hH n U) = 2 * g :=
  haveI := hl
  finrank_eq_of_natCard n (picEquivKer D X eL hk hH hτ n hU).toEquiv hcard

include hk hτ hU hΨ hχ hcusp hφk hl hMrank hcard in
/-- **The weight identity for `π₁ᵉᵗ(U)`**: `det(Ψ^* | Hom_cont(π₁ᵉᵗ(U), ℤ/n))² =
χ^{2g + 2(r − 1)}`. -/
theorem det_pull_sq [Finite (CuspPl D X eL hH U)] :
    ((charDet (p := n) Ψ ⊤ (mapOpenSub_top' D X eL Ψ) : (ZMod n)ˣ) : ZMod n) ^ 2 =
      (χ : ZMod n) ^ (2 * g + 2 * (r₀ - 1)) := by
  haveI := hl
  haveI := Fintype.ofFinite (CuspPl D X eL hH U)
  haveI := free_range_resMap D X eL hk hH hτ n hU
  obtain ⟨h1, h2⟩ := free_finite_ker (resMap D X eL hH n (U := U))
  have hdet := det_sq_of_ker_pairing (resMap D X eL hH n (U := U)) (pullΨ D X eL n Ψ).toLinearMap
    (χ : ZMod n) (resMap_pull D X eL hk hH hτ n hU φ hφF hφF' Ψ hΨ χ hχ hφk hcusp)
    (pull_mem_Aker D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp)
    (pairA D X eL hk hH hτ n hU) (pairA_bijective D X eL hk hH hτ n hU)
    (pairA_pull D X eL hk hH hτ n hU φ hφF hφF' hφk Ψ hΨ χ hχ hcusp)
  have hrA := finrank_Aker D X eL hk hH hτ n hU hl g hcard
  have hrank := finrank_eq_ker_add_range (resMap D X eL hH n (U := U))
  simp only [hrA, hMrank] at hrank
  simp only [charDet, LinearEquiv.coe_det]
  refine hdet.trans ?_
  simp only [hrA]
  congr 1
  omega

include hk hτ hU hl hMrank hcard in
/-- **The number of cusps of `F` is the number `r₀` of punctures** (rank count:
`2g + r₀ - 1 = rank A + rank (M ⧸ A) = 2g + (#cusps - 1)`). -/
theorem card_cuspPl_eq [Fintype (CuspPl D X eL hH U)] (hr₀ : 1 ≤ r₀) (c₀ : CuspPl D X eL hH U) :
    Fintype.card (CuspPl D X eL hH U) = r₀ := by
  classical
  haveI := hl
  haveI := free_range_resMap D X eL hk hH hτ n hU
  obtain ⟨h1, h2⟩ := free_finite_ker (resMap D X eL hH n (U := U))
  have hrA := finrank_Aker D X eL hk hH hτ n hU hl g hcard
  have hrank := finrank_eq_ker_add_range (resMap D X eL hH n (U := U))
  have hsz : finrank (ZMod n) (LinearMap.range (resMap D X eL hH n (U := U))) =
      Fintype.card (CuspPl D X eL hH U) - 1 := by
    rw [(LinearEquiv.ofEq _ _ (range_resMap D X eL hk hH hτ n hU)).finrank_eq,
      (LinearEquiv.ofBijective _ (sumZeroRestrict_bijective D X eL hH n c₀)).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp only [hsz, hrA, hMrank] at hrank
  have hpos : 0 < Fintype.card (CuspPl D X eL hH U) := Fintype.card_pos_iff.2 ⟨c₀⟩
  omega

end Det

end CurvesJacobian.CuspChar
