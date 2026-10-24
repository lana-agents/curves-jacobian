/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.LocAn.SemiAb
import CurvesJacobian.LocAn.ThetaClass
import CurvesJacobian.Kummer.PrincipalEta
import CurvesJacobian.Kummer.JacobianBridge

/-!
# The Weil form on `Δ_X^{ab}` and the theta class on `Δ_X^{ab} ⋊ G_k` (JAC D-d, C2)

For a curve `X` over a field `k` of characteristic `0` (Galois model `D₀ = curveGaloisData k hτ`,
`J(k̄)[n] = Pic(F k̄)[n]`), the Kummer characters `χ_x : Δ_X^{ab} → μ_n` (`Kummer.kCharAb`) and
the perfect Weil pairing `e_n` on `J(k̄)[n]` (`Kummer.weilDual_bijective_baseChange`) identify
`Δ_X^{ab}/n` with `J(k̄)[n]`:

  `a : Δ_X^{ab} → J(k̄)[n]`,  `e_n(x, a δ) = χ_x(δ)` for all `x ∈ J(k̄)[n]` (`weilPairing_aMap`).

The **Weil form** on `Δ_X^{ab}` is `e(δ, δ') = e_n(a δ, a δ') ∈ μ_n` (`weilForm`). It is
bilinear (`weilForm_mul_left`, `weilForm_mul_right`), alternating (`weilForm_self`),
`G_k`-equivariant (**`weilForm_smul`**, from the Galois equivariance of `χ` and of `e_n`) and
locally constant (`isLocallyConstant_weilForm`).

On `E = Δ_X^{ab} ⋊ G_k` (`SemiAb.EAb`) the form `b = e^s` (`s ∈ ℤ`) on the `Δ^{ab}`-components
satisfies the hypotheses of `ThetaClass`, which gives **`thetaE hτ n s ∈ H²(E, μ_n)`**, the
theta class `θ_{e^s}` (for odd `n = 2m + 1`, `e^{±1} = halfForm (e^{±2})` has commutator pairing
`e^{±2}`, the commutator pairing of `c(L)` for `L = (1, φ_Θ)^* 𝒫`; `JAC-plan.md`, D-d.0).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField AlgebraicGeometry Belyi CategoryTheory
open CurvesJacobian.Cusp
open CurvesJacobian.Kummer CurvesJacobian.LocAn.SemiAb

set_option linter.unusedSectionVars false

namespace CurvesJacobian.LocAn.WeilForm

universe u

/-! ### Locally constant characters -/

section LC

variable {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]

/-- A homomorphism with open kernel is locally constant. -/
theorem isLocallyConstant_of_isOpen_ker (f : A →* B) (hf : IsOpen (f.ker : Set A)) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq _]
  intro x
  have h : (fun y => x⁻¹ * y) ⁻¹' (f.ker : Set A) ∈ nhds x := by
    refine (hf.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
    simp
  filter_upwards [h] with y hy
  have hy' : f (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at hy'
  exact hy'.symm

end LC

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] isFunctionField_F

/-- `Π_{J¹} → G_k` is surjective for the Galois model of a curve. -/
instance fact_surjective_curve :
    Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
  fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)

variable {k}

/-- `J(k̄)[n] = Pic(F k̄)[n]` for the Galois model of `X`. -/
abbrev JT (n : ℕ) : Type u :=
  picTorsion (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ))) n

variable (n : ℕ) [NeZero n]

/-- The Weil duality `J(k̄)[n] ≃ Hom(J(k̄)[n], k̄ˣ)`. -/
noncomputable def weilEquiv :
    JT hτ n ≃ (Multiplicative (JT hτ n) →* (kbar k (FFClosure X))ˣ) :=
  Equiv.ofBijective _ (weilDual_bijective_baseChange k hτ (n := n))

/-- **`a : Δ_X^{ab} → J(k̄)[n]`**, characterised by `e_n(x, a δ) = χ_x(δ)`. -/
noncomputable def aMap (δ : DeltaAb (curveGaloisData k hτ)) : JT hτ n :=
  (weilEquiv hτ n).symm (kDual (curveGaloisData k hτ) n δ)

theorem weilDual_aMap (δ : DeltaAb (curveGaloisData k hτ)) :
    weilDual (aMap hτ n δ) = kDual (curveGaloisData k hτ) n δ :=
  (weilEquiv hτ n).apply_symm_apply _

/-- **`e_n(x, a δ) = χ_x(δ)`.** -/
theorem weilPairing_aMap (x : JT hτ n) (δ : DeltaAb (curveGaloisData k hτ)) :
    weilPairing n x (aMap hτ n δ) = (kCharAb x δ : kbar k (FFClosure X)) := by
  have h := congrArg (fun χ => ((χ (Multiplicative.ofAdd x) : (kbar k (FFClosure X))ˣ) :
    kbar k (FFClosure X))) (weilDual_aMap hτ n δ)
  simpa [weilDual, weilChar] using h

theorem weilDual_injective' : Function.Injective (weilDual (κ := kbar k (FFClosure X))
    (K := F (Kummer.baseChange (curveGaloisData k hτ))) (n := n)) :=
  (weilDual_bijective_baseChange k hτ).1

/-- `b` is determined by the pairings `e_n(x, b)`. -/
theorem eq_of_weilPairing_eq {b b' : JT hτ n} (h : ∀ x, weilPairing n x b = weilPairing n x b') :
    b = b' := by
  apply weilDual_injective' hτ n
  refine MonoidHom.ext fun x => Units.ext ?_
  exact h (Multiplicative.toAdd x)

theorem aMap_mul (δ δ' : DeltaAb (curveGaloisData k hτ)) :
    aMap hτ n (δ * δ') = aMap hτ n δ + aMap hτ n δ' := by
  refine eq_of_weilPairing_eq hτ n fun x => ?_
  rw [weilPairing_add_right, weilPairing_aMap, weilPairing_aMap, weilPairing_aMap, map_mul,
    Units.val_mul]

/-! ### The Weil form -/

/-- **The Weil form** `e(δ, δ') = e_n(a δ, a δ') ∈ μ_n` on `Δ_X^{ab}`. -/
noncomputable def weilForm (δ δ' : DeltaAb (curveGaloisData k hτ)) : Mu n (FFClosure X) :=
  ofKbar n (weilPairing_pow (aMap hτ n δ) (aMap hτ n δ'))

theorem val_weilForm (δ δ' : DeltaAb (curveGaloisData k hτ)) :
    ((Mu.val (weilForm hτ n δ δ') : (FFClosure X)ˣ) : FFClosure X) =
      ((weilPairing n (aMap hτ n δ) (aMap hτ n δ') : kbar k (FFClosure X)) : FFClosure X) := rfl

theorem weilForm_ext {ζ ζ' : Mu n (FFClosure X)}
    (h : ((Mu.val ζ : (FFClosure X)ˣ) : FFClosure X) = ((Mu.val ζ' : (FFClosure X)ˣ) :
      FFClosure X)) : ζ = ζ' :=
  Mu.ext (Units.ext h)

theorem weilForm_mul_left (δ₁ δ₂ δ' : DeltaAb (curveGaloisData k hτ)) :
    weilForm hτ n (δ₁ * δ₂) δ' = weilForm hτ n δ₁ δ' * weilForm hτ n δ₂ δ' := by
  apply weilForm_ext
  simp only [map_mul, Units.val_mul, val_weilForm, aMap_mul, weilPairing_add_left,
    IntermediateField.coe_mul]

theorem weilForm_mul_right (δ δ₁ δ₂ : DeltaAb (curveGaloisData k hτ)) :
    weilForm hτ n δ (δ₁ * δ₂) = weilForm hτ n δ δ₁ * weilForm hτ n δ δ₂ := by
  apply weilForm_ext
  simp only [map_mul, Units.val_mul, val_weilForm, aMap_mul, weilPairing_add_right,
    IntermediateField.coe_mul]

/-- **The Weil form is alternating.** -/
theorem weilForm_self (δ : DeltaAb (curveGaloisData k hτ)) : weilForm hτ n δ δ = 1 := by
  apply weilForm_ext
  rw [val_weilForm, weilPairing_self_baseChange k hτ]
  rfl

/-- `a(g δ) = h · a(δ)` for `h ∈ H` over `g ∈ G_k`. -/
theorem aMap_smul (h : (curveGaloisData k hτ).H) (δ : DeltaAb (curveGaloisData k hτ)) :
    aMap hτ n (hToGk _ h • δ) =
      ⟨picAct _ h (aMap hτ n δ), picAct_mem_picTorsion _ h (aMap hτ n δ).2⟩ := by
  refine eq_of_weilPairing_eq hτ n fun x => ?_
  set x' : JT hτ n := ⟨picAct _ h⁻¹ x, picAct_mem_picTorsion _ h⁻¹ x.2⟩
  have hx : x = ⟨picAct _ h x', picAct_mem_picTorsion _ h x'.2⟩ :=
    Subtype.ext (picAct_picAct_inv h x).symm
  apply Subtype.ext
  rw [weilPairing_aMap, hx, weilPairing_picAct, kCharAb_smul, weilPairing_aMap]

/-- **`G_k`-equivariance of the Weil form**: `g · e(δ, δ') = e(g δ, g δ')`. -/
theorem weilForm_smul (g : Gk k (FFClosure X)) (δ δ' : DeltaAb (curveGaloisData k hτ)) :
    g • weilForm hτ n δ δ' = weilForm hτ n (g • δ) (g • δ') := by
  obtain ⟨h, rfl⟩ := hToGk_surjective_of_fact (D := curveGaloisData k hτ) g
  apply weilForm_ext
  rw [hToGk_smul_mu, val_weilForm, val_weilForm, aMap_smul, aMap_smul, weilPairing_picAct]
  rfl

/-! ### Local constancy -/

theorem isOpen_ker_kCharAb (x : JT hτ n) :
    IsOpen ((kCharAb x).ker : Set (DeltaAb (curveGaloisData k hτ))) := by
  have hq : Topology.IsQuotientMap (deltaTildeToAb (D := curveGaloisData k hτ)) :=
    IsClosedMap.isQuotientMap (continuous_deltaTildeToAb.isClosedMap)
      continuous_deltaTildeToAb deltaTildeToAb_surjective
  rw [← hq.isOpen_preimage]
  have h : (deltaTildeToAb (D := curveGaloisData k hτ)) ⁻¹' ((kCharAb x).ker : Set _) =
      ((kChar x).ker : Set _) := by
    ext s
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, kCharAb_deltaTildeToAb]
  rw [h]
  exact isOpen_ker_kChar x

theorem isLocallyConstant_aMap : IsLocallyConstant (aMap hτ n) := by
  rw [IsLocallyConstant.iff_eventually_eq _]
  intro δ
  have h : ∀ x : JT hτ n, ∀ᶠ y in nhds δ, kCharAb x y = kCharAb x δ := fun x =>
    ((IsLocallyConstant.iff_eventually_eq _).1
      (isLocallyConstant_of_isOpen_ker (kCharAb x) (isOpen_ker_kCharAb hτ n x))) δ
  filter_upwards [Filter.eventually_all.2 h] with y hy
  unfold aMap
  congr 1
  exact MonoidHom.ext fun x => hy (Multiplicative.toAdd x)

theorem isLocallyConstant_weilForm :
    IsLocallyConstant fun p : DeltaAb (curveGaloisData k hτ) × DeltaAb (curveGaloisData k hτ) =>
      weilForm hτ n p.1 p.2 :=
  ((isLocallyConstant_aMap hτ n).comp_continuous continuous_fst).comp₂
    ((isLocallyConstant_aMap hτ n).comp_continuous continuous_snd) fun a b =>
      (ofKbar n (weilPairing_pow a b) : Mu n (FFClosure X))

/-! ### The theta class on `E = Δ_X^{ab} ⋊ G_k` -/

/-- **`b = e^s` on the `Δ_X^{ab}`-components of `E`.** -/
noncomputable def bE (s : ℤ) (e e' : EAb (curveGaloisData k hτ)) : Mu n (FFClosure X) :=
  weilForm hτ n e.left e'.left ^ s

theorem left_mul_of_right_eq_one {D : Pi1.Orbifold.GaloisData k (coordT τ)}
    [Fact (Function.Surjective (piJ1ToGk D))] (a b : EAb D) (ha : a.right = 1) :
    (a * b).left = a.left * b.left := by
  rw [SemidirectProduct.mul_left, ha, map_one, MulAut.one_apply]

theorem isBilin_bE (s : ℤ) : ThetaClass.IsBilin (piE (curveGaloisData k hτ)) (bE hτ n s) where
  mul_left t t' s' ht _ _ := by
    rw [bE, bE, bE, left_mul_of_right_eq_one _ _ ht, weilForm_mul_left, mul_zpow]
  mul_right t s₁ s₂ _ hs _ := by
    rw [bE, bE, bE, left_mul_of_right_eq_one _ _ hs, weilForm_mul_right, mul_zpow]

/-- The `Δ^{ab}`-component of a conjugate of an element of `Δ^{ab}`. -/
theorem left_conj {D : Pi1.Orbifold.GaloisData k (coordT τ)}
    [Fact (Function.Surjective (piJ1ToGk D))] (e t : EAb D) (ht : t.right = 1) :
    (e * t * e⁻¹).left = e.right • t.left := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    ht, mul_one, actAb_apply, smul_inv', smul_smul, mul_inv_cancel, one_smul]
  rw [mul_comm e.left, mul_assoc, mul_inv_cancel, mul_one]

theorem isEquivar_bE (s : ℤ) : ThetaClass.IsEquivar (piE (curveGaloisData k hτ)) (bE hτ n s) :=
  fun e t t' ht ht' => by
    rw [bE, bE, left_conj e t ht, left_conj e t' ht', eAb_smul_mu, smul_zpow', weilForm_smul]
    rfl

theorem isLocallyConstant_bE (s : ℤ) :
    IsLocallyConstant fun p : EAb (curveGaloisData k hτ) × EAb (curveGaloisData k hτ) =>
      bE hτ n s p.1 p.2 :=
  ((isLocallyConstant_weilForm hτ n).comp_continuous
    ((SemidirectProduct.continuous_left.comp continuous_fst).prodMk
      (SemidirectProduct.continuous_left.comp continuous_snd))).comp fun ζ => ζ ^ s

/-- **The theta class `θ_{e^s} ∈ H²(Δ_X^{ab} ⋊ G_k, μ_n)`** of the Weil form. -/
noncomputable def thetaE (s : ℤ) :
    ContH2 (EAb (curveGaloisData k hτ)) (Mu n (FFClosure X)) :=
  ThetaClass.thetaClass (continuous_piE _) (continuous_epsE _) (piE_epsE _) (piE_comm _)
    (isBilin_bE hτ n s) (isEquivar_bE hτ n s) (isLocallyConstant_bE hτ n s)

/-- For `n = 2m + 1`, `e^s = (e^{2s})^{m+1}` (`halfForm`, the form in which MR7's
`TPrime.tprime_of_star_P6` takes (★)). -/
theorem bE_eq_pow {m : ℕ} (hn : n = 2 * m + 1) (s : ℤ) (e e' : EAb (curveGaloisData k hτ)) :
    bE hτ n s e e' = bE hτ n (2 * s) e e' ^ (m + 1) := by
  simp only [bE]
  rw [← zpow_natCast, ← zpow_mul]
  have hζ : weilForm hτ n e.left e'.left ^ (n : ℤ) = 1 := by
    rw [zpow_natCast]
    exact Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])
  have h : 2 * s * ((m + 1 : ℕ) : ℤ) = s + s * (n : ℤ) := by
    rw [hn]
    push_cast
    ring
  rw [h, zpow_add, zpow_mul', hζ, one_zpow, mul_one]

/-- **`θ_{e^s} = θ_{halfForm (e^{2s})}`** for `n = 2m + 1`: `thetaE` in the form of MR7's
`TPrime.tprime_of_star_P6` (hypotheses `hstar_i` with `e_i = e^{2s}`). -/
theorem thetaE_eq_halfForm {m : ℕ} (hn : n = 2 * m + 1) (s : ℤ) :
    thetaE hτ n s = ThetaClass.thetaClass (continuous_piE _) (continuous_epsE _) (piE_epsE _)
      (piE_comm _) ((isBilin_bE hτ n (2 * s)).pow (m + 1))
      ((isEquivar_bE hτ n (2 * s)).pow (m + 1))
      ((isLocallyConstant_bE hτ n (2 * s)).comp fun x => x ^ (m + 1)) := by
  have h : bE hτ n s = fun e e' => bE hτ n (2 * s) e e' ^ (m + 1) :=
    funext fun e => funext fun e' => bE_eq_pow hτ n hn s e e'
  unfold thetaE
  congr 1

end CurvesJacobian.LocAn.WeilForm
