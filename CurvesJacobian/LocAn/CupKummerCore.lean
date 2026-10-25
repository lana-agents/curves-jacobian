/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.CupKummer
import CurvesJacobian.LocAn.CupKummerLoc
import CurvesJacobian.FunctionField.KummerCoverEval
import CurvesJacobian.Tsen.C1

/-!
# The Weil pairing is the cup product of Kummer characters ((P6) on `π₁ᵉᵗ(X)`)

MR5's model of a curve `X` over an algebraically closed field `k` of characteristic `0`
(`D`, `eL`, `hH`, `hk`, `hτ`, `Δ = π₁ᵉᵗ(X)`), `n ≥ 1`, `ζ` a primitive `n`-th root of unity, `χ_a`
the Kummer character of `a ∈ J[n]` (`kch`) and `ψ_a = log_ζ χ_a`:

  **`cup_kummer_eq_c1`**: `χ_b ∪ ψ_a = c₁(pt)^m` in `H²(Δ, μ_n)` whenever `ζ^m = e_n(a, b)`

(no sign; JAC-plan "JAC agent 29" and the review of 2026-10-24). Proof for `a` of exact order `n`
(`cup_kummer_eq_c1_core`): `L = F(α)`, `αⁿ = f_a`, is a cyclic unramified cover of degree `n`
(`FunctionField/KummerCover.lean`); Tsen gives `γ ∈ L` with `N γ = f_b` (`Tsen.exists_norm_eq`),
`div γ = C − σC + π^*D_b`; the norm representative `F = ∏_{i<n} ∏_{j<i} σ^j γ` represents
`E = −π_*C + (n(n−1)/2) D_b` (`CupKummerLoc.loc_of_mem_L`, `KummerCover.div_normF`) and its Chern
class is `χ_b ∪ ψ_a` (`chernClassDiv_eq_cupClass`), so
`χ_b ∪ ψ_a = c₁(pt)^{deg E} = c₁(pt)^{−deg C}`;
Weil reciprocity on `L` gives `e_n(a, b) = ζ^{−deg C}` (`KummerCover.evalDiv_div_evalDiv`). The
general case follows by `cup_kummer_eq_c1_of_order` (S0).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open WeilCurves.FunctionField CurvesJacobian.Kummer
open CurvesJacobian.LocAn.WeilCupTransport (mu_pow_n)

set_option linter.unusedSectionVars false

namespace CurvesJacobian.ChernClass

universe u

section Core

variable {k Ω : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} {hH : D.H ≤ D.HL}
  [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {n : ℕ} [NeZero n]

attribute [local instance] isFunctionField_F instTrivMu

/-- Two algebra maps out of `F(α)` agreeing at the generator are equal. -/
theorem algHom_ext_gen {F' E A : Type*} [Field F'] [Field E] [Algebra F' E] [Semiring A]
    [Algebra F' A] {α : E} {φ₁ φ₂ : IntermediateField.adjoin F' {α} →ₐ[F'] A}
    (h : φ₁ (IntermediateField.AdjoinSimple.gen F' α) =
      φ₂ (IntermediateField.AdjoinSimple.gen F' α)) : φ₁ = φ₂ :=
  IntermediateField.adjoin_algHom_ext F' fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h

/-- Elements of `F(α)` for `α` in the function field of the universal cover lie there too. -/
theorem isFix_of_mem_adjoin {α : Ω} (hα : IsFix (rhoX D eL hH) α)
    (x : IntermediateField.adjoin (F D) {α}) : IsFix (rhoX D eL hH) (x : Ω) := by
  intro σ hσ
  let ϕ : Ω →ₐ[F D] Ω :=
    { (σ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv.toRingHom with
      commutes' := fun y => fixes_of_mem_F σ.2 y }
  have h : ϕ.comp (IntermediateField.val _) = IntermediateField.val _ :=
    algHom_ext_gen (hα σ hσ)
  exact DFunLike.congr_fun h x

/-- `σ' ∈ H` acts on `F(α)` as `σ^{m'}` if it does so on `α`. -/
theorem smul_coe_sigma_pow {α : Ω}
    {σ : IntermediateField.adjoin (F D) {α} ≃ₐ[F D] IntermediateField.adjoin (F D) {α}}
    (σ' : D.H) {m' : ℕ} (hgα : (σ' : Ω ≃ₐ[K₀ k t] Ω) α =
      (((σ ^ m') (IntermediateField.AdjoinSimple.gen (F D) α) : _) : Ω))
    (j : ℕ) (γ : IntermediateField.adjoin (F D) {α}) :
    (σ' : Ω ≃ₐ[K₀ k t] Ω) (((σ ^ j) γ : _) : Ω) = (((σ ^ (j + m')) γ : _) : Ω) := by
  let ϕ : Ω →ₐ[F D] Ω :=
    { (σ' : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv.toRingHom with
      commutes' := fun y => fixes_of_mem_F σ'.2 y }
  have hext : ϕ.comp (IntermediateField.val _) =
      (IntermediateField.val _).comp ((σ ^ m').toAlgHom) := algHom_ext_gen hgα
  have h3 := DFunLike.congr_fun hext ((σ ^ j) γ)
  rw [add_comm, pow_add, AlgEquiv.mul_apply]
  exact h3

theorem val_zmodPowHom {ζk : k} {ζ : Mu n Ω} (hζ : ((Mu.val ζ : Ωˣ) : Ω) = algebraMap k Ω ζk)
    (u : Multiplicative (ZMod n)) :
    ((Mu.val (zmodPowHom (mu_pow_n ζ) u) : Ωˣ) : Ω) =
      algebraMap k Ω ζk ^ (Multiplicative.toAdd u).val := by
  change ((Mu.val (ζ ^ (Multiplicative.toAdd u).val) : Ωˣ) : Ω) = _
  rw [map_pow, Units.val_pow_eq_pow_val, hζ]

/-- A class whose multiple `d • a` vanishes has `d • D` principal for its representatives. -/
theorem hord_of_order {a : picTorsion k (F D) n} (hord : ∀ d : ℕ, 0 < d → d < n → d • a ≠ 0)
    (r : TorsRep n (a : Pic k (F D))) :
    ∀ d : ℕ, 0 < d → d < n → d ∣ n → ∀ h : F D, h ≠ 0 → Divisor.div k h ≠ d • r.D := by
  intro d hd hdn _ h hh heq
  refine hord d hd hdn (Subtype.ext ?_)
  rw [AddSubgroup.coe_nsmul, ← r.mk_eq, ← QuotientAddGroup.mk_nsmul, ← heq,
    AddSubgroup.coe_zero]
  exact (QuotientAddGroup.eq_zero_iff _).2 (div_mem_principal hh)

set_option maxHeartbeats 1000000 in
-- the proof assembles the Kummer cover, Tsen, Weil reciprocity and the Chern representative
include hk hτ in
/-- **(P6) for `a` of exact order `n`**: `χ_b ∪ ψ_a = c₁(pt)^m` if `ζ^m = e_n(a, b)`. -/
theorem cup_kummer_eq_c1_core (hg : 0 < (curveGenus k X).toNat) {ζk : k}
    (hζk : IsPrimitiveRoot ζk n) {ζ : Mu n Ω} (hζ : ((Mu.val ζ : Ωˣ) : Ω) = algebraMap k Ω ζk)
    (b a : picTorsion k (F D) n)
    (ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ) (haψ : kch hH hk hτ a = (zmodPowHom (mu_pow_n ζ)).comp ψ)
    (hord : ∀ d : ℕ, 0 < d → d < n → d • a ≠ 0) (m : ℤ) (hm : weilPairing n a b = ζk ^ m) :
    cupClass (fun _ _ => rfl) (fun x => mu_pow_n x) (kch hH hk hτ b)
      (isLocallyConstant_kch hk hτ b) ψ hψ = c1One hH hk hτ n hg ^ m := by
  classical
  -- representatives and the Kummer cover `L = F(α)`
  obtain ⟨rb⟩ := TorsRep.exists b.2
  obtain ⟨ra⟩ := TorsRep.exists a.2
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (F D) Ω ra.f) (NeZero.pos n)
  have hint : IsIntegral (F D) α :=
    IsIntegral.of_pow (NeZero.pos n) (hα ▸ isIntegral_algebraMap)
  set L := IntermediateField.adjoin (F D) {α}
  haveI : FiniteDimensional (F D) L := IntermediateField.adjoin.finiteDimensional hint
  haveI : Module.Free (F D) L := Module.Free.of_divisionRing _ _
  haveI : IsFunctionField k L := IsFunctionField.of_finite (K := F D)
  haveI : Algebra.IsIntegral (F D) L := Algebra.IsIntegral.of_finite (F D) L
  set αL : L := IntermediateField.AdjoinSimple.gen (F D) α
  have hαL : αL ^ n = algebraMap (F D) L ra.f := Subtype.ext (by
    change α ^ n = _
    rw [hα]
    rfl)
  have hgen : IntermediateField.adjoin (F D) {αL} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra _ _
      (IntermediateField.adjoin.powerBasis hint).adjoin_gen_eq_top
  have hfD : Divisor.div k ra.f = n • ra.D := ra.nsmul_eq.symm
  have hordD := hord_of_order hord ra
  set σ := KummerCover.sigma hζk ra.f_ne hfD hordD hαL hgen
  haveI : IsGalois (F D) L := KummerCover.isGalois hζk ra.f_ne hfD hordD hαL hgen
  -- the norm `γ` and the divisor `C`
  obtain ⟨γ, hγN⟩ := Tsen.exists_norm_eq k (K := F D) L rb.f
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hγN
    exact rb.f_ne hγN.symm
  obtain ⟨C, hC⟩ := KummerCover.exists_div_eq hζk ra.f_ne hfD hordD hαL hgen hγ0 (B := rb.D)
    (by rw [hγN]; exact rb.nsmul_eq.symm)
  -- S5: move `D_a` off `supp D_b ∪ π(supp C)` and apply Weil reciprocity on `L`
  obtain ⟨h, hh, hS⟩ := exists_add_div_avoid ra.D
    (rb.D.support ∪ C.support.image fun Q => Q.restrict (K := F D))
  have hDisj : ∀ P, (ra.move hh).D P = 0 ∨ rb.D P = 0 := fun P => by
    by_cases hP : P ∈ rb.D.support
    · exact Or.inl (hS P (Finset.mem_union_left _ hP))
    · exact Or.inr (Finsupp.notMem_support_iff.1 hP)
  have hDC : ∀ Q ∈ C.support, (ra.move hh).D (Q.restrict (K := F D)) = 0 := fun Q hQ =>
    hS _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ))
  have hS5 := KummerCover.evalDiv_div_evalDiv hζk (KummerCover.shift_hf0 ra.f_ne hh)
    (KummerCover.shift_hfD ra.f_ne hfD hh) (KummerCover.shift_hord hordD hh)
    (KummerCover.shift_hα hαL h) (KummerCover.shift_hgen hgen hh) rb.f_ne rb.nsmul_eq.symm hγN
    (by rw [KummerCover.sigma_shift hζk ra.f_ne hfD hordD hαL hgen hh]; exact hC) hDisj hDC
  have hwe : weilPairing n a b = ζk ^ (-C.deg) := by
    rw [weilPairing_eq a b (ra.move hh) rb hDisj]
    exact hS5
  have hmod : m ≡ -C.deg [ZMOD n] := by
    have h0 : ζk ^ (-C.deg - m) = 1 := by
      rw [zpow_sub₀ (hζk.ne_zero (NeZero.ne n)), ← hwe, hm,
        div_self (zpow_ne_zero _ (hζk.ne_zero (NeZero.ne n)))]
    exact Int.modEq_iff_dvd.2 ((hζk.zpow_eq_one_iff_dvd _).1 h0)
  -- S3: the family `g_j = σ^j γ` and the roots
  set g : ℕ → Ω := fun j => (((σ ^ j) γ : L) : Ω)
  have hg0 : ∀ j, g j ≠ 0 := fun j h0 =>
    hγ0 ((map_eq_zero_iff (σ ^ j) (σ ^ j).injective).1 (Subtype.ext h0))
  have hσn : σ ^ n = 1 :=
    (KummerCover.sigma_pow_eq_one_iff hζk ra.f_ne hfD hordD hαL hgen).2 dvd_rfl
  have hper : ∀ j, g (j + n) = g j := fun j => by
    simp only [g, pow_add, hσn, mul_one]
  have hLfix : ∀ x : L, IsFix (rhoX D eL hH) (x : Ω) :=
    isFix_of_mem_adjoin (isFix_root hk hτ a ra hα)
  have hgfix : ∀ j, IsFix (rhoX D eL hH) (g j) := fun j => hLfix _
  have hact : ∀ (σ' : D.H) (j : ℕ),
      σ' • g j = g (j + (Multiplicative.toAdd (ψ (rhoX D eL hH σ'))).val) := by
    intro σ' j
    refine smul_coe_sigma_pow σ' ?_ j γ
    rw [KummerCover.sigma_pow_apply hζk ra.f_ne hfD hordD hαL hgen,
      ← kch_rhoX_mul hk hτ a ra hα σ', haψ, MonoidHom.comp_apply, val_zmodPowHom hζ]
    rfl
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (F D) Ω rb.f) (NeZero.pos n)
  have hβρ : β ^ n = LocAn.NormCocycle.rho g n := by
    have e1 : (((∏ j ∈ Finset.range n, (σ ^ j) γ : L)) : Ω) = ∏ j ∈ Finset.range n, g j :=
      map_prod (IntermediateField.val L) (fun j => (σ ^ j) γ) _
    rw [LocAn.NormCocycle.rho, ← e1, ← KummerCover.norm_eq_prod hζk ra.f_ne hfD hordD hαL hgen,
      hγN, hβ]
    rfl
  have hβfix := isFix_root (hH := hH) hk hτ b rb hβ
  have hβσ : ∀ σ' : D.H, σ' • β = ((Mu.val (kch hH hk hτ b (rhoX D eL hH σ')) : Ωˣ) : Ω) * β :=
    fun σ' => (kch_rhoX_mul hk hτ b rb hβ σ').symm
  -- S4: the representative `F` of `E`
  set F' : L := ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, (σ ^ j) γ
  have hFeq : LocAn.NormCocycle.normF n g = (F' : Ω) := by
    change _ = IntermediateField.val L F'
    simp only [F', map_prod]
    rfl
  have hF'0 : F' ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ =>
      (map_ne_zero_iff _ (σ ^ j).injective).2 hγ0
  set E : Divisor k (F D) :=
    -(KummerCover.normDiv (F D) C) + (n * (n - 1) / 2 : ℕ) • rb.D
  have hdivF := KummerCover.div_normF hζk ra.f_ne hfD hordD hαL hgen hγ0 hC
  have hram : ∀ (Q : Place k L) (x : F D),
      Q.ord (algebraMap (F D) L x) = (Q.restrict (K := F D)).ord x := fun Q x => by
    rw [ord_algebraMap_eq_ramIndex_mul,
      KummerCover.ramIndex_eq_one hζk ra.f_ne hfD hordD hαL hgen, one_mul]
  have hcong : ∀ Q : Place k L, (n : ℤ) ∣ Q.ord F' - E (Q.restrict (K := F D)) := fun Q => by
    have h1 := DFunLike.congr_fun hdivF Q
    rw [Divisor.div_apply] at h1
    rw [h1, Finsupp.add_apply, conormOf_apply,
      KummerCover.ramIndex_eq_one hζk ra.f_ne hfD hordD hαL hgen, one_mul]
    change (n : ℤ) ∣ (n • C) Q + E (Q.restrict (K := F D)) - E (Q.restrict (K := F D))
    rw [add_sub_cancel_right, Finsupp.smul_apply, nsmul_eq_mul]
    exact dvd_mul_right _ _
  have hfree : ∀ (g' : L ≃ₐ[F D] L) (Q : Place k L), (∀ x, g' x ∈ Q.1 ↔ x ∈ Q.1) → g' = 1 := by
    intro g' Q hQ
    refine KummerCover.placeMap_injective hζk ra.f_ne hfD hordD hαL hgen Q ?_
    change KummerCover.placeMap g' Q = KummerCover.placeMap 1 Q
    rw [KummerCover.placeMap_one]
    refine Place.ext (ValuationSubring.ext _ _ fun x => ?_)
    rw [KummerCover.mem_placeMap]
    have := hQ (g'.symm x)
    rwa [AlgEquiv.apply_symm_apply, Iff.comm] at this
  have hloc := CupKummer.loc_of_mem_L (L := L) hF'0 hcong hram hfree
  set mm : D.H → ℕ := fun σ' => (Multiplicative.toAdd (ψ (rhoX D eL hH σ'))).val
  have hF : IsChernRepDiv D eL hH n E (LocAn.NormCocycle.normF n g) :=
    { ne := by
        rw [hFeq]
        exact fun h0 => hF'0 (Subtype.ext h0)
      fix := by
        rw [hFeq]
        exact hLfix F'
      inv := fun σ' => ⟨LocAn.NormCocycle.lam g mm β σ',
        (hβfix.pow _).div (isFix_prod _ fun j _ => hgfix j),
        LocAn.NormCocycle.smul_normF hg0 (fun σ'' j => hact σ'' j) hper hβρ σ'⟩
      loc := by
        rw [hFeq]
        exact hloc }
  have hmain := chernClassDiv_eq_cupClass hk hτ hg0 hper hgfix ψ hψ hact (kch hH hk hτ b)
    (isLocallyConstant_kch hk hτ b) hβρ hβfix hβσ hF
  have hc := (c1Div_eq hk hτ hg hF).symm.trans (c1Div_eq_deg_smul_c1One hk hτ hg E)
  apply_fun Additive.toMul at hc
  rw [toMul_ofMul, toMul_zsmul, toMul_ofMul] at hc
  have hdegE : E.deg = -C.deg := by
    rw [Divisor.deg_add, Divisor.deg_neg, Divisor.deg_nsmul,
      KummerCover.deg_normDiv, deg_eq_zero_of_nsmul_eq_div (NeZero.ne n) rb.nsmul_eq, mul_zero,
      add_zero]
  rw [← hmain, hc, hdegE]
  exact zpow_eq_of_modEq (c1One_pow_n hk hτ (hH := hH) (n := n) hg) hmod.symm

include hk hτ in
/-- **(P6) on MR5's model** (`Δ = π₁ᵉᵗ(X)`): for `a, b ∈ J[n]`, a primitive `ζ` and
`ψ_a = log_ζ χ_a`, `χ_b ∪ ψ_a = c₁(pt)^m` whenever `ζ^m = e_n(a, b)` (no sign). -/
theorem cup_kummer_eq_c1 (hg : 0 < (curveGenus k X).toNat) {ζk : k}
    (hζk : IsPrimitiveRoot ζk n) {ζ : Mu n Ω} (hζ : ((Mu.val ζ : Ωˣ) : Ω) = algebraMap k Ω ζk)
    (b a : picTorsion k (F D) n)
    (ψ : π₁ᵉᵗ(specPoint D.L Ω ≫ genericL D X eL ⊤) →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ) (haψ : kch hH hk hτ a = (zmodPowHom (mu_pow_n ζ)).comp ψ)
    (m : ℤ) (hm : weilPairing n a b = ζk ^ m) :
    cupClass (fun _ _ => rfl) (fun x => mu_pow_n x) (kch hH hk hτ b)
      (isLocallyConstant_kch hk hτ b) ψ hψ = c1One hH hk hτ n hg ^ m :=
  cup_kummer_eq_c1_of_order hk hτ hg hζk hζ b
    (fun a' ψ' hψ' ha' hord' m' hm' =>
      cup_kummer_eq_c1_core hk hτ hg hζk hζ b a' ψ' hψ' ha' hord' m' hm') a ψ hψ haψ m hm

end Core

end CurvesJacobian.ChernClass
