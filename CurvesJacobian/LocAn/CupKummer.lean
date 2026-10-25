/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.ChernNatural
import CurvesJacobian.Kummer.DeltaAbKummer
import CurvesJacobian.LocAn.NormCocycle
import CurvesJacobian.LocAn.DeltaXEquiv
import Pi1.Surface.Cup

/-!
# The Chern class of the norm representative is a cup product ((P6), step 3 on `π₁ᵉᵗ(X)`)

MR5's model of a curve over an algebraically closed field (`D : GaloisData k t`, a scheme model
`(X, eL)`, `ρ = rhoX : H ↠ π₁ᵉᵗ(X)`, the first Chern class `chernClassDiv` of a representative
`IsChernRepDiv`, `Kummer/ChernDivisor.lean`).

* `ChernClass.chernClassOf_eq_cupClass` (group theory): if the Chern cocycle of an admissible
  locally constant choice `g` is the cup-product cocycle `(γ, δ) ↦ χ(γ)^{ψ(δ)}`, the Chern class
  is pi1's cup product `χ ∪ ψ`;
* `kch a : π₁ᵉᵗ(X) →* μ_n`, the Kummer character of `a ∈ Pic(F)[n]` (MR5's
  `picTorsionEquivPiChars` along `π₁ᵉᵗ(X) ≃ Π_X`), with `kch_rhoX`: `χ_a(ρ σ) = σ(β)/β` for every
  root `βⁿ = f` of a representative;
* **`chernClassDiv_eq_cupClass`**: for the norm representative `F = ∏_{i<n} ρ_i`,
  `ρ_i = ∏_{j<i} g_j` (`NormCocycle.normF`) of an `n`-periodic family `g_j` permuted by `H` through
  a character `ψ : π₁ᵉᵗ(X) → ℤ/n` (`τ g_j = g_{j + ψ(ρτ)}`) and a root `βⁿ = ρ_n` with
  `τ β = χ(ρτ) β`, the Chern class of `F` (for any divisor it represents) is `χ ∪ ψ`
  (McCallum–Sharifi's skeleton, arXiv math/0202161v3, Thm 2.4, in abelian form; JAC-plan
  "JAC agent 29").
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open WeilCurves.FunctionField CurvesJacobian.Kummer
open CurvesJacobian.LocAn.WeilCupTransport (mu_pow_n)

set_option linter.unusedSectionVars false

namespace CurvesJacobian.ChernClass

universe u

/-! ### Chern cocycle = cup cocycle -/

section Generic

variable {G Q Ω : Type*} [Group G] [Group Q] [Field Ω] [MulSemiringAction G Ω]
  {ρ : G →* Q} {n : ℕ} [NeZero n] {s : Q → G} (hs : ∀ γ, ρ (s γ) = γ)
  (hμ : ∀ (σ : G) (ζ : Ω), ζ ^ n = 1 → σ • ζ = ζ)
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (hstab : ∀ x : Ω, IsOpen (MulAction.stabilizer G x : Set G))
  (hq : ∀ S : Set Q, IsOpen (ρ ⁻¹' S) → IsOpen S)

attribute [local instance] Pi1.SurfaceGroup.trivialAction in
/-- **The Chern class is the cup product** if the Chern cocycle of a locally constant admissible
choice is the cup-product cocycle. -/
theorem chernClassOf_eq_cupClass {f : Ω} (hf : f ≠ 0) (hfix : IsFix ρ f) {g : Q → Ω}
    (hg : IsAdm ρ n s f g) (hglc : IsLocallyConstant g) (χ : Q →* Mu n Ω)
    (hχ : IsLocallyConstant χ) (ψ : Q →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ)
    (hval : ∀ γ δ, chernVal s g (γ, δ) =
      ((Mu.val (χ γ ^ (Multiplicative.toAdd (ψ δ)).val) : Ωˣ) : Ω)) :
    chernClassOf hs hμ hstab hq hf hfix hg hglc =
      cupClass (fun _ _ => rfl) (fun m => Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one]))
        χ hχ ψ hψ := by
  unfold chernClassOf cupClass
  congr 1
  refine Subtype.ext (funext fun x => Mu.ext (Units.ext ?_))
  obtain ⟨γ, δ⟩ := x
  exact hval γ δ

theorem isFix_prod {ι : Type*} (S : Finset ι) {x : ι → Ω} (hx : ∀ i ∈ S, IsFix ρ (x i)) :
    IsFix ρ (∏ i ∈ S, x i) := fun σ hσ => by
  rw [Finset.smul_prod']
  exact Finset.prod_congr rfl fun i hi => hx i hi σ hσ

end Generic

/-! ### The norm representative on MR5's model -/

section Curve

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {n : ℕ} [NeZero n]

attribute [local instance] isFunctionField_F instTrivMu

variable (hH) in
/-- **The Kummer character `χ_a : π₁ᵉᵗ(X) → μ_n`** of `a ∈ Pic(F)[n]` (MR5's
`picTorsionEquivPiChars` along `π₁ᵉᵗ(X) ≃ Π_X`). -/
noncomputable def kch (a : picTorsion k (F D) n) :
    π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Mu n Ω :=
  ((Additive.toMul (picTorsionEquivPiChars D n (NeZero.pos n) a) :
    ContinuousMonoidHom (PiX D) (Mu n Ω)) : PiX D →* Mu n Ω).comp
    (LocAn.DeltaXEquiv.pi1TopEquivPiX hH hk hτ).toMulEquiv.toMonoidHom

theorem continuous_kch (a : picTorsion k (F D) n) : Continuous (kch hH hk hτ a) :=
  (Additive.toMul (picTorsionEquivPiChars D n (NeZero.pos n) a)).continuous.comp
    (LocAn.DeltaXEquiv.pi1TopEquivPiX hH hk hτ).continuous

theorem isLocallyConstant_kch (a : picTorsion k (F D) n) : IsLocallyConstant (kch hH hk hτ a) :=
  (IsLocallyConstant.iff_continuous _).2 (continuous_kch hk hτ a)

theorem kch_rhoX (a : picTorsion k (F D) n) (σ : D.H) :
    kch hH hk hτ a (rhoX D eL hH σ) =
      (Additive.toMul (picTorsionEquivPiChars D n (NeZero.pos n) a)) (QuotientGroup.mk σ) := by
  change (Additive.toMul (picTorsionEquivPiChars D n (NeZero.pos n) a))
    (LocAn.DeltaXEquiv.pi1TopEquivPiX hH hk hτ (rhoX D eL hH σ)) = _
  rw [← LocAn.DeltaXEquiv.pi1TopEquivPiX_symm_mk (hH := hH) hk hτ,
    ContinuousMulEquiv.apply_symm_apply]

/-- **`χ_a(ρ σ) β = σ(β)`** for every root `βⁿ = f` of a representative `n E = div f` of `a`. -/
theorem kch_rhoX_mul (a : picTorsion k (F D) n) (r : TorsRep n (a : Pic k (F D))) {β : Ω}
    (hβ : β ^ n = algebraMap (F D) Ω r.f) (σ : D.H) :
    ((Mu.val (kch hH hk hτ a (rhoX D eL hH σ)) : Ωˣ) : Ω) * β = (σ : Ω ≃ₐ[K₀ k t] Ω) β := by
  rw [kch_rhoX]
  exact val_picTorsionEquivPiChars_mul D (NeZero.pos n) a r hβ σ

include hk hτ in
/-- Kummer roots of `n`-torsion classes lie in the function field of the universal cover. -/
theorem isFix_root (a : picTorsion k (F D) n) (r : TorsRep n (a : Pic k (F D))) {β : Ω}
    (hβ : β ^ n = algebraMap (F D) Ω r.f) : IsFix (rhoX D eL hH) β := fun σ hσ => by
  have h := kch_rhoX_mul (hH := hH) hk hτ a r hβ σ
  rw [MonoidHom.mem_ker.1 hσ, map_one] at h
  change (σ : Ω ≃ₐ[K₀ k t] Ω) β = β
  rw [← h]
  simp

open CurvesJacobian.LocAn.NormCocycle in
/-- **The Chern class of the norm representative is the cup product `χ ∪ ψ`** (McCallum–Sharifi's
skeleton in abelian form): `g : ℕ → Ω` is `n`-periodic, non-vanishing, in the function field of the
universal cover, permuted by `τ ∈ H` through `ψ` (`τ g_j = g_{j + ψ(ρτ)}`), and `βⁿ = ∏_{j<n} g_j`
with `τ β = χ(ρτ) β`. -/
theorem chernClassDiv_eq_cupClass {g : ℕ → Ω} (hg0 : ∀ j, g j ≠ 0) (hper : ∀ j, g (j + n) = g j)
    (hgfix : ∀ j, IsFix (rhoX D eL hH) (g j))
    (ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ)
    (hact : ∀ (σ : D.H) (j : ℕ),
      σ • g j = g (j + (Multiplicative.toAdd (ψ (rhoX D eL hH σ))).val))
    (χ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Mu n Ω) (hχ : IsLocallyConstant χ)
    {β : Ω} (hβ : β ^ n = LocAn.NormCocycle.rho g n) (hβfix : IsFix (rhoX D eL hH) β)
    (hβσ : ∀ σ : D.H, σ • β = ((Mu.val (χ (rhoX D eL hH σ)) : Ωˣ) : Ω) * β)
    {E : Divisor k (F D)} (hF : IsChernRepDiv D eL hH n E (LocAn.NormCocycle.normF n g)) :
    chernClassDiv hk hτ hF =
      cupClass (fun _ _ => rfl) (fun m => Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one]))
        χ hχ ψ hψ := by
  set ρ := rhoX D eL hH
  set m : D.H → ℕ := fun σ => (Multiplicative.toAdd (ψ (ρ σ))).val
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne n)] at hβ
    exact rho_ne_zero hg0 n hβ.symm
  have hm : ∀ σ σ' : D.H, m σ + m σ' = m (σ * σ') ∨ m σ + m σ' = m (σ * σ') + n := by
    intro σ σ'
    simp only [m, map_mul, toAdd_mul, ZMod.val_add]
    have h1 := ZMod.val_lt (Multiplicative.toAdd (ψ (ρ σ)))
    have h2 := ZMod.val_lt (Multiplicative.toAdd (ψ (ρ σ')))
    by_cases hlt : (Multiplicative.toAdd (ψ (ρ σ))).val +
        (Multiplicative.toAdd (ψ (ρ σ'))).val < n
    · left; rw [Nat.mod_eq_of_lt hlt]
    · right
      rw [Nat.mod_eq_sub_mod (not_lt.1 hlt), Nat.mod_eq_of_lt (by omega)]
      omega
  set Λ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) → Ω := fun γ =>
    β ^ (Multiplicative.toAdd (ψ γ)).val / LocAn.NormCocycle.rho g (Multiplicative.toAdd (ψ γ)).val
  have hΛ : ∀ σ, LocAn.NormCocycle.lam g m β σ = Λ (ρ σ) := fun σ => rfl
  have hsX : ∀ γ, ρ (sX hH hk hτ γ) = γ := rhoX_sX hH hk hτ
  have hadm : IsAdm ρ n (sX hH hk hτ) (LocAn.NormCocycle.normF n g) Λ := by
    refine ⟨fun γ => (hβfix.pow _).div (isFix_prod _ fun j _ => hgfix j),
      fun γ => div_ne_zero (pow_ne_zero _ hβ0) (rho_ne_zero hg0 _), fun γ => ?_⟩
    · have := smul_normF (m := m) hg0 (fun σ j => hact σ j) hper hβ (sX hH hk hτ γ)
      rw [hΛ, hsX] at this
      exact this
  have hlc : IsLocallyConstant Λ :=
    hψ.comp fun u =>
      β ^ (Multiplicative.toAdd u).val / LocAn.NormCocycle.rho g (Multiplicative.toAdd u).val
  rw [chernClassDiv, ← chernClassOf_eq_chernClass _ _ _ _ hF.toKummerInv hadm hlc]
  refine chernClassOf_eq_cupClass _ _ _ _ _ _ hadm hlc χ hχ ψ hψ fun γ δ => ?_
  have key := lam_cocycle_of (m := m) hg0 (fun σ j => hact σ j) hper hβ hβ0
    (c := fun σ => ((Mu.val (χ (ρ σ)) : Ωˣ) : Ω)) hβσ hm (sX hH hk hτ γ) (sX hH hk hτ δ)
  simp only [hΛ, map_mul, hsX] at key
  simp only [chernVal]
  rw [key]
  simp [m, hsX]

/-! ### Reduction to classes of exact order `n` ((P6) step S0) -/

theorem kch_add (a a' : picTorsion k (F D) n) :
    kch hH hk hτ (a + a') = kch hH hk hτ a * kch hH hk hτ a' := by
  ext γ
  simp only [kch, map_add, toMul_add, MonoidHom.comp_apply, MonoidHom.mul_apply]
  rfl

theorem kch_zero : kch hH hk hτ (0 : picTorsion k (F D) n) = 1 := by
  ext γ
  simp only [kch, map_zero, toMul_zero, MonoidHom.comp_apply, MonoidHom.one_apply]
  rfl

theorem kch_nsmul (a : picTorsion k (F D) n) (c : ℕ) :
    kch hH hk hτ (c • a) = kch hH hk hτ a ^ c := by
  induction c with
  | zero => rw [zero_smul, kch_zero, pow_zero]
  | succ c ih => rw [succ_nsmul, kch_add, ih, pow_succ]

/-- **Every locally constant character `π₁ᵉᵗ(X) → μ_n` is a Kummer character** (MR5's
`picTorsionEquivPiChars`). -/
theorem exists_kch_eq (χ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Mu n Ω)
    (hχ : IsLocallyConstant χ) : ∃ a : picTorsion k (F D) n, kch hH hk hτ a = χ := by
  set e := LocAn.DeltaXEquiv.pi1TopEquivPiX hH hk hτ
  let χ' : ContinuousMonoidHom (PiX D) (Mu n Ω) :=
    ⟨χ.comp e.symm.toMulEquiv.toMonoidHom, hχ.continuous.comp e.symm.continuous⟩
  refine ⟨(picTorsionEquivPiChars D n (NeZero.pos n)).symm (Additive.ofMul χ'),
    MonoidHom.ext fun γ => ?_⟩
  change (Additive.toMul ((picTorsionEquivPiChars D n (NeZero.pos n))
    ((picTorsionEquivPiChars D n (NeZero.pos n)).symm (Additive.ofMul χ')))) (e γ) = χ γ
  rw [AddEquiv.apply_symm_apply, toMul_ofMul]
  exact congrArg χ (e.symm_apply_apply γ)

theorem cupClass_pow_right {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M]
    [MulDistribMulAction G M] (htriv : ∀ (g : G) (m : M), g • m = m)
    (hM : ∀ m : M, m ^ n = 1) (χ : G →* M) (hχ : IsLocallyConstant χ)
    (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) (c : ℕ)
    (h : IsLocallyConstant (ψ ^ c)) :
    cupClass htriv hM χ hχ (ψ ^ c) h = cupClass htriv hM χ hχ ψ hψ ^ c := by
  induction c with
  | zero => simp only [pow_zero]; exact cupClass_one_right htriv hM χ hχ _
  | succ c ih =>
    have hc : IsLocallyConstant (ψ ^ c) := hψ.comp fun x => x ^ c
    simp only [pow_succ]
    rw [cupClass_mul_right htriv hM χ hχ _ _ hc hψ, ih hc]

/-- `x ^ a = x ^ b` for `a ≡ b mod n` if `x ^ n = 1`. -/
theorem zpow_eq_of_modEq {A : Type*} [Group A] {x : A} (hx : x ^ n = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD n]) : x ^ a = x ^ b := by
  obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.1 h
  have hb : b = a + n * q := by omega
  rw [hb, zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, mul_one]

include hk hτ in
theorem c1One_pow_n (hg : 0 < (curveGenus k X).toNat) : c1One hH hk hτ n hg ^ n = 1 := by
  rw [c1One, ← toMul_nsmul, ← map_nsmul, c1Div_nsmul]
  rfl

include hk hτ in
/-- **(P6) step S0**: the identity `χ_b ∪ ψ_a = c₁(pt)^m`, `ζ^m = e_n(a, b)`, for all `a` follows
from the case of `a` of exact order `n`: with a character `ψ₀` and `δ₀` with `ψ₀(δ₀) = 1`
(pi1's dual character of an oriented basis) and its class `a₀`, `a' = a + c a₀` has
`ψ_{a'}(δ₀) = 1` (hence order `n`) for `c = n + 1 − ψ_a(δ₀)`, and both sides are additive in `a`. -/
theorem cup_kummer_eq_c1_of_order (hg : 0 < (curveGenus k X).toNat) {ζk : k}
    (hζk : IsPrimitiveRoot ζk n) {ζ : Mu n Ω} (hζ : ((Mu.val ζ : Ωˣ) : Ω) = algebraMap k Ω ζk)
    (b : picTorsion k (F D) n)
    (hcore : ∀ (a : picTorsion k (F D) n)
      (ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Multiplicative (ZMod n))
      (hψ : IsLocallyConstant ψ), kch hH hk hτ a = (zmodPowHom (mu_pow_n ζ)).comp ψ →
      (∀ d : ℕ, 0 < d → d < n → d • a ≠ 0) → ∀ m : ℤ, weilPairing n a b = ζk ^ m →
      cupClass (fun _ _ => rfl) (fun x => mu_pow_n x) (kch hH hk hτ b)
        (isLocallyConstant_kch hk hτ b) ψ hψ = c1One hH hk hτ n hg ^ m)
    (a : picTorsion k (F D) n)
    (ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ) (haψ : kch hH hk hτ a = (zmodPowHom (mu_pow_n ζ)).comp ψ)
    (m : ℤ) (hm : weilPairing n a b = ζk ^ m) :
    cupClass (fun _ _ => rfl) (fun x => mu_pow_n x) (kch hH hk hτ b)
      (isLocallyConstant_kch hk hτ b) ψ hψ = c1One hH hk hτ n hg ^ m := by
  classical
  set zp := zmodPowHom (mu_pow_n ζ)
  obtain ⟨e0⟩ := nonempty_orientation hH hk hτ
  set i₀ : Fin (curveGenus k X).toNat := ⟨0, hg⟩
  set δ₀ := SurfaceGroup.genAOf e0 i₀
  set ψ₀ := SurfaceGroup.dualA e0 n i₀
  have hψ₀ : IsLocallyConstant ψ₀ := SurfaceGroup.isLocallyConstant_dualA e0 n i₀
  have hψ₀δ₀ : Multiplicative.toAdd (ψ₀ δ₀) = 1 := by simp [ψ₀, δ₀]
  obtain ⟨a₀, ha₀⟩ :=
    exists_kch_eq hk hτ (zp.comp ψ₀) (by rw [MonoidHom.coe_comp]; exact hψ₀.comp _)
  -- a class whose character takes the value `ζ` at `δ₀` has exact order `n`
  have hord : ∀ (x : picTorsion k (F D) n)
      (φ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Multiplicative (ZMod n)),
      kch hH hk hτ x = zp.comp φ → Multiplicative.toAdd (φ δ₀) = 1 →
      ∀ d : ℕ, 0 < d → d < n → d • x ≠ 0 := by
    intro x φ hx h1 d hd hdn h0
    have h2 := congrArg (fun y => kch hH hk hτ y δ₀) h0
    simp only [kch_nsmul, kch_zero, MonoidHom.one_apply, MonoidHom.pow_apply, hx,
      MonoidHom.comp_apply] at h2
    have h3 : zp (φ δ₀) = ζ := by
      change ζ ^ (Multiplicative.toAdd (φ δ₀)).val = ζ
      rw [h1, pow_zmod_val_one (mu_pow_n ζ)]
    rw [h3] at h2
    have h4 : ζk ^ d = 1 := by
      have := congrArg (fun y : Mu n Ω => ((Mu.val y : Ωˣ) : Ω)) h2
      simp only [map_pow, Units.val_pow_eq_pow_val, hζ, map_one, Units.val_one] at this
      exact (algebraMap k Ω).injective (by rw [map_pow, this, map_one])
    have := Nat.le_of_dvd hd (hζk.dvd_of_pow_eq_one d h4)
    omega
  -- the values of the Weil pairing are powers of `ζk`
  have hpow : ∀ x : picTorsion k (F D) n, ∃ m' : ℤ, weilPairing n x b = ζk ^ m' := fun x => by
    obtain ⟨i, -, hi⟩ := hζk.eq_pow_of_pow_eq_one (weilPairing_pow x b)
    exact ⟨i, by rw [zpow_natCast, hi]⟩
  set j := (Multiplicative.toAdd (ψ δ₀)).val
  have hj : j < n := ZMod.val_lt _
  set c := n + 1 - j
  set a' := a + c • a₀
  set ψ' := ψ * ψ₀ ^ c
  have hψc : IsLocallyConstant (ψ₀ ^ c) := hψ₀.comp fun x => x ^ c
  have hψ' : IsLocallyConstant ψ' := hψ.mul hψc
  have ha' : kch hH hk hτ a' = zp.comp ψ' := by
    rw [kch_add, kch_nsmul, haψ, ha₀]
    ext γ
    simp [ψ', map_mul, map_pow]
  have hψ'δ₀ : Multiplicative.toAdd (ψ' δ₀) = 1 := by
    simp only [ψ', MonoidHom.mul_apply, MonoidHom.pow_apply, toAdd_mul, toAdd_pow, hψ₀δ₀,
      nsmul_eq_mul, mul_one]
    rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd (ψ δ₀)), ← Nat.cast_add]
    have : j + c = n + 1 := by omega
    rw [this, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  obtain ⟨m', hm'⟩ := hpow a'
  obtain ⟨m₀, hm₀⟩ := hpow a₀
  have h1 := hcore a' ψ' hψ' ha' (hord a' ψ' ha' hψ'δ₀) m' hm'
  have h2 := hcore a₀ ψ₀ hψ₀ ha₀ (hord a₀ ψ₀ ha₀ hψ₀δ₀) m₀ hm₀
  have hsplit := cupClass_mul_right (fun _ _ => rfl) (fun x => mu_pow_n x) (kch hH hk hτ b)
    (isLocallyConstant_kch hk hτ b) ψ (ψ₀ ^ c) hψ hψc hψ'
  rw [cupClass_pow_right _ _ _ _ ψ₀ hψ₀ c hψc, h1, h2] at hsplit
  -- the exponents
  have hwe : weilPairing n a' b = weilPairing n a b * weilPairing n a₀ b ^ c := by
    rw [weilPairing_add_left]
    congr 1
    induction c with
    | zero => rw [zero_smul, weilPairing_zero_left, pow_zero]
    | succ c ih => rw [succ_nsmul, weilPairing_add_left, ih, pow_succ]
  have hne : ζk ≠ 0 := hζk.ne_zero (NeZero.ne n)
  rw [hm', hm, hm₀, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hne] at hwe
  have hmod : m ≡ m' - m₀ * c [ZMOD n] := by
    have h0 : ζk ^ (m' - (m + m₀ * c)) = 1 := by
      rw [zpow_sub₀ hne, hwe, div_self (zpow_ne_zero _ hne)]
    have h3 := (hζk.zpow_eq_one_iff_dvd _).1 h0
    exact Int.modEq_iff_dvd.2 (by convert h3 using 1; ring)
  have hc1 := c1One_pow_n hk hτ (hH := hH) (n := n) hg
  have hψeq := eq_mul_inv_of_mul_eq hsplit.symm
  rw [zpow_eq_of_modEq hc1 hmod, hψeq, zpow_sub, zpow_mul, zpow_natCast]

end Curve

end CurvesJacobian.ChernClass
