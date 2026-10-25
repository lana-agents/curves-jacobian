/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.ThetaPullback
import CurvesJacobian.LocAn.ResDeltaGeneric
import CurvesJacobian.LocAn.CupKummerCore
import CurvesJacobian.Galois.PicTorsionCount

/-!
# (P6) on a Galois model from the core identity on MR5's model (assembly W2, `s = 1`)

Let `D` be a Galois model whose base change `baseChange D` is modelled by a curve `X` over `k̄`
(`eL`, `hH`, `hk`, `hτ` as in `ResDeltaGeneric`), `e = deltaXEquivPi1 : π₁ᵉᵗ(X) ≃ₜ* Δ_X`.

* `val_kch_eq_kCharAb`: MR5's Kummer character `kch a` of `a ∈ J(k̄)[n]` is `kCharAb a` along
  `e` (both are `σ(β)/β` for a lift `σ ∈ H_{k̄}`);
* `chiDelta_comp_eq_kch`: `χ_δ ∘ e = kch (a δ)` (`weilPairing_aMap`);
* `mapEquiv_cupClass`: the cup product on `Δ_X` corresponds to pi1's cup product on `π₁ᵉᵗ(X)`;
* **`weilCupG_of_core`**: `WeilCupG D n hW` with `s = 1` follows from the core identity
  `kch b ∪ ψ = c₁(pt)^m`, `e_n(a, b) = ζ^m`, `kch a = ζ^ψ`, on MR5's model.
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open WeilCurves.FunctionField CurvesJacobian.ChernClass CurvesJacobian.Kummer
open CurvesJacobian.LocAn.WeilForm CurvesJacobian.LocAn.DeltaXEquiv CurvesJacobian.LocAn.SemiAb
open CurvesJacobian.LocAn.ArithChern

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.JacInput

universe u

attribute [local instance 2000] Kummer.group_piX
attribute [local instance] isFunctionField_F instTrivMu

/-! ### The genus is invariant under isomorphisms of function fields -/

section Genus

variable {κ K K' : Type*} [Field κ] [IsAlgClosed κ] [CharZero κ] [Field K] [Field K']
  [Algebra κ K] [Algebra κ K'] [IsFunctionField κ K] [IsFunctionField κ K'] (e : K ≃ₐ[κ] K')

theorem divisorEquivOfAlgEquiv_placeMap (A : Divisor κ K) (P : Place κ K) :
    CurvesJacobian.divisorEquivOfAlgEquiv e A (CurvesJacobian.placeMap e P) = A P := by
  change A ((CurvesJacobian.placeEquivOfAlgEquiv e).symm
    (CurvesJacobian.placeEquivOfAlgEquiv e P)) = A P
  rw [Equiv.symm_apply_apply]

theorem deg_divisorEquivOfAlgEquiv (A : Divisor κ K) :
    (CurvesJacobian.divisorEquivOfAlgEquiv e A).deg = A.deg := by
  induction A using Finsupp.induction_linear with
  | zero => rw [map_zero, Divisor.deg_zero, Divisor.deg_zero]
  | add A B hA hB => rw [map_add, Divisor.deg_add, Divisor.deg_add, hA, hB]
  | single P m =>
    have h : CurvesJacobian.divisorEquivOfAlgEquiv e (Finsupp.single P m) =
        Finsupp.single (CurvesJacobian.placeMap e P) m :=
      Finsupp.equivMapDomain_single _ _ _
    rw [h, Divisor.deg_single, Divisor.deg_single, Place.deg_eq_one, Place.deg_eq_one]

theorem L_divisorEquivOfAlgEquiv (A : Divisor κ K) :
    Divisor.L (CurvesJacobian.divisorEquivOfAlgEquiv e A) =
      (Divisor.L A).map e.toLinearEquiv.toLinearMap := by
  ext y
  rw [Submodule.mem_map_equiv, Divisor.mem_L, Divisor.mem_L]
  change _ ↔ e.symm y = 0 ∨ ∀ P : Place κ K, -A P ≤ P.ord (e.symm y)
  rw [map_eq_zero_iff _ e.symm.injective]
  refine or_congr Iff.rfl ⟨fun h P => ?_, fun h Q => ?_⟩
  · have h1 := h (CurvesJacobian.placeMap e P)
    rw [divisorEquivOfAlgEquiv_placeMap, ← AlgEquiv.apply_symm_apply e y,
      CurvesJacobian.ord_placeMap] at h1
    exact h1
  · obtain ⟨P, rfl⟩ := (CurvesJacobian.placeEquivOfAlgEquiv e).surjective Q
    change -(CurvesJacobian.divisorEquivOfAlgEquiv e A) (CurvesJacobian.placeMap e P) ≤
      (CurvesJacobian.placeMap e P).ord y
    rw [divisorEquivOfAlgEquiv_placeMap, ← AlgEquiv.apply_symm_apply e y,
      CurvesJacobian.ord_placeMap]
    exact h P

theorem ell_divisorEquivOfAlgEquiv (A : Divisor κ K) :
    Divisor.ell (CurvesJacobian.divisorEquivOfAlgEquiv e A) = Divisor.ell A := by
  unfold Divisor.ell
  rw [L_divisorEquivOfAlgEquiv]
  exact LinearEquiv.finrank_map_eq _ _

include e in
/-- **The genus is invariant under `κ`-isomorphisms of function fields.** -/
theorem genus_eq_of_algEquiv : genus κ K' = genus κ K := by
  unfold genus Divisor.riemannConst
  congr 2
  rw [← (CurvesJacobian.divisorEquivOfAlgEquiv e).surjective.range_comp]
  congr 1
  funext A
  simp only [Function.comp_apply, deg_divisorEquivOfAlgEquiv, ell_divisorEquivOfAlgEquiv]

end Genus

section Core

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [Fact (Function.Surjective (piJ1ToGk D))]
  {X : Scheme.{u}} [X.Over (Spec (.of (kbar k Ω)))] [IsCurveOver (kbar k Ω) X] [IsIntegral X]
  [Nonempty (⊤ : X.Opens)]
  {eL : X.functionField ≃+* (baseChange D).L} (hH : (baseChange D).H ≤ (baseChange D).HL)
  (hk : ∀ c : kbar k Ω, ((eL (algebraMap (kbar k Ω) X.functionField c) :
    (baseChange D).L) : Ω) = algebraMap (kbar k Ω) Ω c)
  {τ : X.functionField} (hτ : ((eL τ : (baseChange D).L) : Ω) = t)
  {n : ℕ} [NeZero n]
  (hW : Function.Bijective (weilDual (κ := kbar k Ω) (K := F (Kummer.baseChange D)) (n := n)))

/-- **MR5's Kummer character is `kCharAb` along `π₁ᵉᵗ(X) ≃ Δ_X`.** -/
theorem val_kch_eq_kCharAb (a : JT D n)
    (γ : π₁ᵉᵗ(specPoint (baseChange D).L Ω ≫ genericL (baseChange D) X eL ⊤)) :
    ((Mu.val (kch hH hk hτ a γ) : Ωˣ) : Ω) =
      (((kCharAb a (deltaAbMk D (deltaXEquivPi1 hH hk hτ γ)) : (kbar k Ω)ˣ) : kbar k Ω) : Ω) := by
  obtain ⟨σ, rfl⟩ : ∃ σ, rhoX (baseChange D) eL hH σ = γ :=
    ⟨sX hH hk hτ γ, rhoX_sX hH hk hτ γ⟩
  rw [kch_rhoX, val_picTorsionEquivPiChars, deltaXEquivPi1_rhoX]
  change _ = (((kCharAb a (deltaTildeToAb (bcToDeltaTilde D σ)) : (kbar k Ω)ˣ) :
    kbar k Ω) : Ω)
  rw [kCharAb_deltaTildeToAb, coe_kChar]

/-- **`χ_δ ∘ e = kch (a δ)`.** -/
theorem chiDelta_comp_eq_kch (δ : DeltaX D) :
    (chiDelta hW δ).comp (deltaXEquivPi1 hH hk hτ).toMulEquiv.toMonoidHom =
      kch hH hk hτ (aMap hW (deltaAbMk D δ)) := by
  refine MonoidHom.ext fun γ => Mu.ext (Units.ext ?_)
  rw [val_kch_eq_kCharAb hH hk hτ]
  change ((weilPairing n (aMap hW (deltaAbMk D δ))
    (aMap hW (deltaAbMk D (deltaXEquivPi1 hH hk hτ γ))) : kbar k Ω) : Ω) = _
  rw [weilPairing_aMap]

/-- **The cup product on `Δ_X` is pi1's cup product on `π₁ᵉᵗ(X)`** along `e`. -/
theorem mapEquiv_cupClass (χ : DeltaX D →* Mu n Ω) (hχ : IsLocallyConstant χ)
    (ψ : DeltaX D →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    ContH2.mapEquiv (deltaXEquivPi1 hH hk hτ).toMulEquiv (deltaXEquivPi1 hH hk hτ).continuous
        (deltaXEquivPi1 hH hk hτ).symm.continuous (deltaXEquivPi1_smul hH hk hτ)
        (cupClass χ hχ ψ hψ) =
      h2lcToContH2 (Pi1.Profinite.cupClass (fun _ _ => rfl)
        (fun x => WeilCupTransport.mu_pow_n x)
        (χ.comp (deltaXEquivPi1 hH hk hτ).toMulEquiv.toMonoidHom)
        (hχ.comp_continuous (deltaXEquivPi1 hH hk hτ).continuous)
        (ψ.comp (deltaXEquivPi1 hH hk hτ).toMulEquiv.toMonoidHom)
        (hψ.comp_continuous (deltaXEquivPi1 hH hk hτ).continuous)) :=
  rfl

include hH hk in
/-- **`g(F k̄) = g(X)`** for the model `X` of `baseChange D` (`eL : K(X) ≅ L = F k̄`). -/
theorem genus_F_baseChange_eq :
    genus (kbar k Ω) (F (baseChange D)) = curveGenus (kbar k Ω) X := by
  have hLF : (baseChange D).L = F (baseChange D) := le_antisymm
    (fun z hz => ChernClass.mem_F_of_mem_L hH ⟨z, hz⟩)
    (fun z hz => ChernClass.mem_L_of_mem_F ⟨z, hz⟩)
  let φ : X.functionField ≃+* F (baseChange D) :=
    eL.trans (IntermediateField.equivOfEq hLF).toRingEquiv
  let e : X.functionField ≃ₐ[kbar k Ω] F (baseChange D) :=
    AlgEquiv.ofRingEquiv (f := φ) fun c => Subtype.ext (hk c)
  exact genus_eq_of_algEquiv e

include hH hk in
theorem pos_curveGenus_of_one_le (h : 1 ≤ genus (kbar k Ω) (F (baseChange D))) :
    0 < (curveGenus (kbar k Ω) X).toNat := by
  rw [← genus_F_baseChange_eq hH hk]
  omega

set_option maxHeartbeats 2000000 in
-- unifying the transport along `π₁ᵉᵗ(X) ≃ Δ_X` with MR5's classes is slow
include hH hk hτ in
/-- **(P6) on `D` from the core identity on MR5's model** (`s = 1`). The genus hypothesis
`hgX` compares the genus of `F k̄` with that of the model `X` (`X.functionField ≅ F k̄`). -/
theorem weilCupG_of_core [Finite (JT D n)]
    (hgX : 1 ≤ genus (kbar k Ω) (F (baseChange D)) → 0 < (curveGenus (kbar k Ω) X).toNat)
    (hcore : ∀ (hg : 0 < (curveGenus (kbar k Ω) X).toNat) {ζk : kbar k Ω}
      (_ : IsPrimitiveRoot ζk n) {ζ : Mu n Ω}
      (_ : ((Mu.val ζ : Ωˣ) : Ω) = algebraMap (kbar k Ω) Ω ζk) (b a : JT D n)
      (ψ : π₁ᵉᵗ(specPoint (baseChange D).L Ω ≫ genericL (baseChange D) X eL ⊤) →*
        Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ),
      kch hH hk hτ a = (zmodPowHom (WeilCupTransport.mu_pow_n ζ)).comp ψ →
      ∀ m : ℤ, weilPairing n a b = ζk ^ m →
      Pi1.Profinite.cupClass (fun _ _ => rfl) (fun x => WeilCupTransport.mu_pow_n x)
        (kch hH hk hτ b) (isLocallyConstant_kch hk hτ b) ψ hψ = c1One hH hk hτ n hg ^ m) :
    WeilCupG D n hW := by
  intro hgen
  have hg := hgX hgen
  refine ⟨1, Or.inl rfl, fun E f hf _ δ ψ hψ => ?_⟩
  set e := deltaXEquivPi1 hH hk hτ
  obtain ⟨ζk, hζk⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (kbar k Ω) n
  set ζ : Mu n Ω := ofKbar (k := k) n hζk.pow_eq_one
  have hζ : ((Mu.val ζ : Ωˣ) : Ω) = algebraMap (kbar k Ω) Ω ζk := rfl
  set zp := zmodPowHom (WeilCupTransport.mu_pow_n ζ)
  set ψ' := ψ.comp e.toMulEquiv.toMonoidHom
  have hψ' : IsLocallyConstant ψ' := hψ.comp_continuous e.continuous
  obtain ⟨a', ha'⟩ := exists_kch_eq hk hτ (zp.comp ψ') (by
    rw [MonoidHom.coe_comp]; exact hψ'.comp _)
  set b := aMap hW (deltaAbMk D δ)
  obtain ⟨i, -, hi⟩ := hζk.eq_pow_of_pow_eq_one (weilPairing_pow a' b)
  have h1 := hcore hg hζk hζ b a' ψ' hψ' ha' i (by rw [zpow_natCast, hi])
  -- the exponent: `e_n(a', b) = χ_{a'}(δ) = ζ^{ψ(δ)}`
  set j := (Multiplicative.toAdd (ψ δ)).val
  have hval : weilPairing n a' b = ζk ^ j := by
    apply Subtype.ext
    have h2 := val_kch_eq_kCharAb hH hk hτ a' (e.symm δ)
    rw [ha', ContinuousMulEquiv.apply_symm_apply] at h2
    rw [weilPairing_aMap, ← h2]
    change ((Mu.val (ζ ^ (Multiplicative.toAdd (ψ (e (e.symm δ)))).val) : Ωˣ) : Ω) = _
    rw [ContinuousMulEquiv.apply_symm_apply, map_pow, Units.val_pow_eq_pow_val, hζ]
    rfl
  have hne : ζk ≠ 0 := hζk.ne_zero (NeZero.ne n)
  have hmod : (i : ℤ) ≡ (j : ℤ) [ZMOD n] := by
    have h0 : ζk ^ ((i : ℤ) - j) = 1 := by
      rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hi, hval, div_self (pow_ne_zero _ hne)]
    have h3 := (hζk.zpow_eq_one_iff_dvd _).1 h0
    rw [Int.modEq_iff_dvd, ← neg_sub, dvd_neg]
    exact h3
  have hc1 := c1One_pow_n hk hτ (hH := hH) (n := n) hg
  -- transport along `e`
  apply (ContH2.mapEquiv e.toMulEquiv e.continuous e.symm.continuous
    (deltaXEquivPi1_smul hH hk hτ)).injective
  have hcup : Pi1.Profinite.cupClass (fun _ _ => rfl) (fun x => WeilCupTransport.mu_pow_n x)
        ((chiDelta hW δ).comp e.toMulEquiv.toMonoidHom)
        ((isLocallyConstant_chiDelta hW δ).comp_continuous e.continuous) ψ' hψ' =
      Pi1.Profinite.cupClass (fun _ _ => rfl) (fun x => WeilCupTransport.mu_pow_n x)
        (kch hH hk hτ b) (isLocallyConstant_kch hk hτ b) ψ' hψ' :=
    Pi1.Profinite.cupClass_congr _ _ _ _ _ _ (chiDelta_comp_eq_kch hH hk hτ hW δ) rfl
  rw [map_zpow, map_zpow, mapEquiv_resDeltaG hH hk hτ hg hf, mapEquiv_cupClass hH hk hτ, hcup, h1,
    zpow_eq_of_modEq hc1 hmod, map_zpow, ← zpow_mul, ← zpow_mul]
  congr 1
  ring

include hH hk hτ in
/-- **(P6) on any Galois model whose base change is modelled by a curve** (`s = 1`): the core
identity is `cup_kummer_eq_c1`. -/
theorem weilCupG_of_model [Finite (JT D n)] : WeilCupG D n hW :=
  weilCupG_of_core hH hk hτ hW (pos_curveGenus_of_one_le hH hk)
    fun hg _ hζk _ hζ b a ψ hψ haψ m hm => cup_kummer_eq_c1 hk hτ hg hζk hζ b a ψ hψ haψ m hm

end Core

/-! ### The Galois model of a curve -/

section Curve

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-- **(P6) for a curve** (`WeilCup`): `weilCupG_of_model` for the model `X_{k̄}` of
`barData k hτ = baseChange (curveGaloisData k hτ)`. -/
theorem weilCup_curve (n : ℕ) [NeZero n] : WeilCup hτ n := by
  unfold WeilCup
  exact weilCupG_of_model (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) _

end Curve

end CurvesJacobian.LocAn.JacInput
