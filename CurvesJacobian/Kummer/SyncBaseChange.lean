/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.SyncZHat
import CurvesJacobian.Kummer.BaseChangeFunctionField
import CurvesJacobian.Cusp.GenusBaseChange

/-!
# Synchronization of geometric cyclotomes for `X_{k̄}` of a curve `X` over `k`

[AbsTopIII] Prop. 1.4 (`Topics in Absolute Anabelian Geometry III.txt` l.1752–1806) is stated
for `X` over a field `k` of characteristic `0` and concerns the geometric groups
`Δ_U = π₁ᵉᵗ(U_{k̄})`, `Δ_X = π₁ᵉᵗ(X_{k̄})`. The results of `Kummer/CuspCentralCurve.lean`,
`Kummer/CuspInertiaZHat.lean`, `Kummer/ChernNatural.lean`, `Kummer/NatIsoCompat.lean` and
`Kummer/SyncZHat.lean` are proved for a generic Galois model `(D, eL)` of a curve over an
algebraically closed field. Here they are instantiated for `X_{k̄} = X ×_k k̄`
(`baseChangeKbar k X`, `k̄ = kbar k Ω` the algebraic closure of `k` in `Ω = K(X)^alg`) with the
Galois model `barData k hτ = baseChange (curveGaloisData k hτ)` (the model of `X_{k̄}` inside the
Galois model of `X`, `F (barData) = F k̄`, `Gal(Ω/F k̄) = ker(Π_X ↠ G_k)` at the generic point):

* `barData_H_eq`, `barData_H_le`, `barData_L_eq`: `H = H_L` for `barData`;
* **`barEquivL : K(X_{k̄}) ≃+* L`** (from `ffEquiv`), `barEquivL_algebraMap`, `barEquivL_tau`:
  the hypotheses `hk`, `hτ` of the generic results; `genus_bar_pos`: `g(X_{k̄}) = g(X)`;
* `DeltaBar k hτ U = π₁ᵉᵗ(U_{k̄})` at the generic geometric point, `DeltaBarX k hτ = Δ_X`;
* **`nonempty_orientation_bar`**: `Δ_X ≃ₜ* Π̂_{g,0}`, `g = g(X)`;
* **`exists_cuspCentral_equiv_bar`**, **`cuspCentral_exact_bar`**: Prop. 1.4(i)–(ii), the group
  theory of `1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` for `X_{k̄}`;
* **`cuspInertiaZHatEquivBar : I_x ≃ₜ* Ẑ(1)`** (Prop. 1.4(i));
* `c1OneBar n`: `c₁ mod n` of a degree-`1` line bundle on `X_{k̄}`; **`natIsoBar n : M_X/n ≃* μ_n`**
  ([Mzk19] Prop. 1.2(ii) mod `n`) with `natIsoBar_spec`, `natIsoBar_unique`,
  `natIsoBar_transition`; **`natIsoHatBar : M_X ≃* Ẑ(1)`** (the limit);
* **`syncEquivBar : I_x ≃* M_X`**, and **`IsCuspPushout.mk_eq_natIso_bar`**,
  **`IsCuspPushout.mk_eq_tautX_bar`**: [AbsTopIII] Prop. 1.4(ii) for `X_{k̄}`;
* `pointData_bar`: every place of `F k̄` gives a point `x`, `U = X_{k̄} ∖ {x}`, a place `W₀` of `Ω`
  over `x` and a uniformiser, as the results above require.

The genus hypothesis is `0 < g(X)` throughout (`hg`).
-/

open CategoryTheory AlgebraicGeometry Belyi AlgebraicGeometry.FiniteEtale AffOrbicurve Topology
open Pi1.Orbifold Pi1 CurvesJacobian.Cusp KummerTheory KummerTheory.Curve Pi1.Profinite
open Pi1.SurfaceGroup WeilCurves.FunctionField CurvesJacobian.ChernClass CurvesJacobian.TopClass
open CurvesJacobian.CuspCentral

universe u

noncomputable section

namespace CurvesJacobian.Kummer

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

/-! ### The Galois model of `X_{k̄}` and the hypotheses of the generic results -/

/-- **The Galois model of `X_{k̄}`**: the base change to `k̄` of the Galois model of `X`. -/
abbrev barData : GaloisData (kbar k (FFClosure X)) (coordT τ) :=
  Kummer.baseChange (curveGaloisData k hτ)

lemma barData_H_eq : (barData k hτ).H = (barData k hτ).HL := by
  ext σ
  rw [mem_baseChange_H]
  change _ ↔ σ ∈ (Kummer.baseChange (curveGaloisData k hτ)).HL
  unfold Kummer.baseChange
  exact Iff.rfl

lemma barData_H_le : (barData k hτ).H ≤ (barData k hτ).HL := (barData_H_eq k hτ).le

lemma barData_L_eq : (barData k hτ).L = F (barData k hτ) := by
  change IntermediateField.fixedField (barData k hτ).HL =
    IntermediateField.fixedField (barData k hτ).H
  rw [barData_H_eq]

/-- **`K(X_{k̄}) ≃ L`** for the Galois model `barData` (`ffEquiv`). -/
def barEquivL : (baseChangeKbar k X).functionField ≃+* (barData k hτ).L :=
  (ffEquiv k hτ).symm.toRingEquiv.trans
    (IntermediateField.equivOfEq (barData_L_eq k hτ).symm).toRingEquiv

lemma coe_barEquivL (z : (baseChangeKbar k X).functionField) :
    ((barEquivL k hτ z : (barData k hτ).L) : FFClosure X) =
      (((ffEquiv k hτ).symm z : F (barData k hτ)) : FFClosure X) := rfl

/-- The hypothesis `hk` of the generic results for `barEquivL`. -/
lemma barEquivL_algebraMap (c : kbar k (FFClosure X)) :
    ((barEquivL k hτ (algebraMap (kbar k (FFClosure X)) (baseChangeKbar k X).functionField c) :
      (barData k hτ).L) : FFClosure X) = algebraMap (kbar k (FFClosure X)) (FFClosure X) c := by
  rw [coe_barEquivL, AlgEquiv.commutes]
  rfl

/-- The hypothesis `hτ` of the generic results for `barEquivL`: the coordinate is the pull-back
of `τ` to `X_{k̄}`. -/
lemma barEquivL_tau :
    ((barEquivL k hτ (ffMap k X τ) : (barData k hτ).L) : FFClosure X) = coordT τ :=
  coe_ffEquiv_symm_ffMap k hτ τ

instance nonempty_top_baseChangeKbar : Nonempty (⊤ : (baseChangeKbar k X).Opens) :=
  ⟨⟨genericPoint _, trivial⟩⟩

variable {k} in
/-- `g(X_{k̄}) = g(X)`. -/
lemma genus_bar_pos (hg : 0 < (curveGenus k X).toNat) :
    0 < (curveGenus (kbar k (FFClosure X)) (baseChangeKbar k X)).toNat := by
  rwa [Cusp.curveGenus_baseChange k (kbar k (FFClosure X)) X]

/-! ### The geometric fundamental groups -/

/-- **`Δ_U = π₁ᵉᵗ(U_{k̄})`**, `U` an open of `X_{k̄}`, at the geometric generic point. -/
abbrev DeltaBar (U : (baseChangeKbar k X).Opens) [Nonempty U] :=
  π₁ᵉᵗ(specPoint (barData k hτ).L (FFClosure X) ≫
    genericL (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U)

/-- **`Δ_X = π₁ᵉᵗ(X_{k̄})`** at the geometric generic point. -/
abbrev DeltaBarX := DeltaBar k hτ ⊤

/-- **`Δ_X ≃ₜ* Π̂_{g,0}`**, `g = g(X)` (an orientation exists). -/
theorem nonempty_orientation_bar :
    Nonempty (DeltaBarX k hτ ≃ₜ* ProfiniteSurfaceGroup (curveGenus k X).toNat 0) := by
  rw [← Cusp.curveGenus_baseChange k (kbar k (FFClosure X)) X]
  exact nonempty_orientation (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)

/-! ### Points -/

/-- **Points of `X_{k̄}`** in the form the results below use: for every place `P` of `F k̄` there
are a point `x` of `X_{k̄}`, `U = X_{k̄} ∖ {x}`, a place `W₀` of `Ω` over `P` centred on `x`, and a
uniformiser `π` of `P`. -/
theorem pointData_bar (P : Place (kbar k (FFClosure X)) (F (barData k hτ))) {R : Prop}
    (hR : ∀ (x : baseChangeKbar k X) (U : (baseChangeKbar k X).Opens) [Nonempty U]
      (W₀ : ValuationSubring (FFClosure X)) (π : (F (barData k hτ))ˣ),
      (U : Set (baseChangeKbar k X))ᶜ = {x} →
      IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀ →
      ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀ →
      (∀ y : F (barData k hτ), ((y : F (barData k hτ)) : FFClosure X) ∈ W₀ ↔ y ∈ P.1) →
      W₀.valuation ((π : F (barData k hτ)) : FFClosure X) < 1 →
      (∀ f ∈ F (barData k hτ), W₀.valuation f < 1 →
        W₀.valuation f ≤ W₀.valuation ((π : F (barData k hτ)) : FFClosure X)) → R) :
    R :=
  pointData (barEquivL_algebraMap k hτ) P hR

variable {k hτ} {U : (baseChangeKbar k X).Opens} [Nonempty U] {x : baseChangeKbar k X}
  {W₀ : ValuationSubring (FFClosure X)} {π : (F (barData k hτ))ˣ}

/-! ### [AbsTopIII] Prop. 1.4 for `X_{k̄}` -/

/-- **[AbsTopIII] Prop. 1.4 for `X_{k̄}`, group theory**: `Δ_{U_x} ≅ Π̂_{g,1}`, `Δ_X ≅ Π̂_{g,0}`
compatibly with `I_x ↦ ⟨c⟩‾`, the filling map, its kernel and the cuspidally central quotient
(`CuspCentral.exists_cuspCentral_equiv`). -/
theorem exists_cuspCentral_equiv_bar (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀) :
    ∃ (Θ : DeltaBar k hτ U ≃ₜ*
        ProfiniteSurfaceGroup (curveGenus (kbar k (FFClosure X)) (baseChangeKbar k X)).toNat 1)
      (Θ₀ : DeltaBarX k hτ ≃ₜ*
        ProfiniteSurfaceGroup (curveGenus (kbar k (FFClosure X)) (baseChangeKbar k X)).toNat 0),
      (cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) U
          W₀).map Θ.toMulEquiv.toMonoidHom = inertia 0 ∧
      (∀ γ, Θ₀ (fundamentalGroupMap ((baseChangeKbar k X).homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
          γ) = fillHat _ (Θ γ)) ∧
      (fundamentalGroupMap ((baseChangeKbar k X).homOfLE (le_top : U ≤ ⊤))
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
          le_top)).toMonoidHom.ker.map Θ.toMulEquiv.toMonoidHom = cuspKernel _ ∧
      (⁅(fundamentalGroupMap ((baseChangeKbar k X).homOfLE (le_top : U ≤ ⊤))
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
          le_top)).toMonoidHom.ker, ⊤⁆ : Subgroup (DeltaBar k hτ U)).topologicalClosure.map
            Θ.toMulEquiv.toMonoidHom = ccnKernel _ :=
  CuspCentral.exists_cuspCentral_equiv _ _ (barData_H_le k hτ) (barEquivL_algebraMap k hτ)
    (barEquivL_tau k hτ) U hUx hW₀ hW₀U

/-- **[AbsTopIII] Prop. 1.4(ii) for `X_{k̄}`, the exact sequence**
`1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` (`CuspCentral.cuspCentral_exact_curve`). -/
theorem cuspCentral_exact_bar (hg : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀) :
    let f := fundamentalGroupMap ((baseChangeKbar k X).homOfLE (le_top : U ≤ ⊤))
      (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
    let N' : Subgroup (DeltaBar k hτ U) := (⁅f.toMonoidHom.ker, ⊤⁆ : Subgroup _).topologicalClosure
    (cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) U W₀ ⊓
        N' = ⊥) ∧
      cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) U W₀ ≤
        f.toMonoidHom.ker ∧
      f.toMonoidHom.ker ≤
        cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) U
          W₀ ⊔ N' ∧ Function.Surjective f :=
  CuspCentral.cuspCentral_exact_curve _ _ (barData_H_le k hτ) (barEquivL_algebraMap k hτ)
    (barEquivL_tau k hτ) (genus_bar_pos hg) U hUx hW₀ hW₀U

/-- **[AbsTopIII] Prop. 1.4(i) for `X_{k̄}`: `I_x ≃ₜ* Ẑ(1)`** via the tame character of a
uniformiser (`CuspCentral.cuspInertiaZHatEquiv`). -/
def cuspInertiaZHatEquivBar (hg : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀)
    (hπW : W₀.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), W₀.valuation f < 1 →
      W₀.valuation f ≤ W₀.valuation ((π : F (barData k hτ)) : FFClosure X)) :
    cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) U W₀ ≃ₜ*
      ZHatOne (F (barData k hτ)) (FFClosure X) :=
  CuspCentral.cuspInertiaZHatEquiv (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)
    (genus_bar_pos hg) U hUx hW₀ hW₀U hπW hπ

/-! ### [Mzk19] Prop. 1.2(ii) for `X_{k̄}` -/

attribute [local instance] instTrivMu

variable (hτ) in
/-- `c₁ mod n` of a line bundle of degree `1` on `X_{k̄}` (`ChernClass.c1One`). -/
def c1OneBar (n : ℕ) [NeZero n] (hg : 0 < (curveGenus k X).toNat) :
    H2lc (DeltaBarX k hτ) (Mu n (FFClosure X)) :=
  c1One (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) n
    (genus_bar_pos hg)

variable (hτ) in
/-- The tautological class of `H²(Δ_X, M_X/n)` for `X_{k̄}` ([Mzk19] Prop. 1.2(i) mod `n`). -/
def tautBar (n : ℕ) [NeZero n] (hg : 0 < (curveGenus k X).toNat) :
    H2lc (DeltaBarX k hτ) (MXmod (DeltaBarX k hτ) n) :=
  tautX (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) n
    (genus_bar_pos hg)

variable (hτ) in
/-- **The natural isomorphism `M_X/n ≃* μ_n` for `X_{k̄}`** ([Mzk19] Prop. 1.2(ii) mod `n`). -/
def natIsoBar (n : ℕ) [NeZero n] (hg : 0 < (curveGenus k X).toNat) :
    MXmod (DeltaBarX k hτ) n ≃* Mu n (FFClosure X) :=
  natIso (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) n
    (genus_bar_pos hg)

/-- `natIsoBar` sends the tautological class to `c₁` of a degree-`1` line bundle. -/
theorem natIsoBar_spec (n : ℕ) [NeZero n] (hg : 0 < (curveGenus k X).toNat) :
    h2Map (natIsoBar hτ n hg).toMonoidHom (fun _ _ ↦ rfl) (tautBar hτ n hg) = c1OneBar hτ n hg :=
  natIso_spec _ _ _

/-- `natIsoBar` is the only isomorphism with `natIsoBar_spec`. -/
theorem natIsoBar_unique (n : ℕ) [NeZero n] (hg : 0 < (curveGenus k X).toNat)
    (ι : MXmod (DeltaBarX k hτ) n ≃* Mu n (FFClosure X))
    (hι : h2Map ι.toMonoidHom (fun _ _ ↦ rfl) (tautBar hτ n hg) = c1OneBar hτ n hg) :
    ι = natIsoBar hτ n hg :=
  natIso_unique _ _ _ ι hι

/-- `c₁ mod n` of a degree-`1` line bundle generates `H²(Δ_X, μ_n)`. -/
theorem c1OneBar_generates (n : ℕ) [NeZero n] (hg : 0 < (curveGenus k X).toNat)
    (c : H2lc (DeltaBarX k hτ) (Mu n (FFClosure X))) :
    c ∈ Subgroup.zpowers (c1OneBar hτ n hg) :=
  c1One_generates _ _ _ c

/-- **The `natIsoBar` are compatible in `n`**. -/
theorem natIsoBar_transition (n m : ℕ) [NeZero n] [NeZero m] (hg : 0 < (curveGenus k X).toNat) :
    (Mu.transition (dvd_mul_right n m)).comp (natIsoBar hτ (n * m) hg).toMonoidHom =
      (natIsoBar hτ n hg).toMonoidHom.comp
        (mxTransition (genus_bar_pos hg) (nonempty_orientation (barData_H_le k hτ)
          (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ))) :=
  natIso_transition _ _ _

variable (hτ) in
/-- **The natural isomorphism `M_X ≃* Ẑ(1)` for `X_{k̄}`** ([Mzk19] Prop. 1.2(ii)). -/
def natIsoHatBar (hg : 0 < (curveGenus k X).toNat) :
    MXHat (DeltaBarX k hτ) (F (barData k hτ)) ≃* ZHatOne (F (barData k hτ)) (FFClosure X) :=
  natIsoHat (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)
    (genus_bar_pos hg)

/-! ### [AbsTopIII] Prop. 1.4(ii) for `X_{k̄}` -/

/-- **The synchronization `I_x ≃* M_X` for `X_{k̄}`** ([AbsTopIII] Prop. 1.4(ii)):
`I_x ≅ Ẑ(1) ≅ M_X` (`ChernClass.syncEquiv`). -/
def syncEquivBar (hg : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀)
    (hπW : W₀.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), W₀.valuation f < 1 →
      W₀.valuation f ≤ W₀.valuation ((π : F (barData k hτ)) : FFClosure X)) :
    cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) U W₀ ≃*
      MXHat (DeltaBarX k hτ) (F (barData k hτ)) :=
  syncEquiv (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) U
    (genus_bar_pos hg) hUx hW₀ hW₀U hπW hπ

/-- **[AbsTopIII] Prop. 1.4(ii) for `X_{k̄}`, modulo `n`**: every pushout of
`1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` along the natural `I_x ≅ Ẑ(1) ↠ μ_n` has class
`natIsoBar_*(taut)` (`ChernClass.IsCuspPushout.mk_eq_natIso`). -/
theorem IsCuspPushout.mk_eq_natIso_bar (hg : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀)
    (hπW : W₀.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), W₀.valuation f < 1 →
      W₀.valuation f ≤ W₀.valuation ((π : F (barData k hτ)) : FFClosure X))
    (n : ℕ) [NeZero n] {Φ : TrivCocycle (DeltaBarX k hτ) (Mu n (FFClosure X))}
    {Ψ : DeltaBar k hτ U →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout (barData_H_le k hτ) U
      (chiN (barData_H_le k hτ) (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ) n U
        (genus_bar_pos hg) hUx hW₀ hW₀U hπW hπ) Φ Ψ) :
    QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ) =
      h2Map (natIsoBar hτ n hg).toMonoidHom (fun _ _ ↦ rfl) (tautBar hτ n hg) :=
  ChernClass.IsCuspPushout.mk_eq_natIso _ _ _ hUx hW₀ hW₀U hπW hπ hΦ h

/-- **[AbsTopIII] Prop. 1.4(ii) for `X_{k̄}`, tautological form**: every pushout of
`1 → I_x → Δ^{c-cn}_{U_x} → Δ_X → 1` along `I_x ≅ M_X ↠ M_X/n` (`syncEquivBar`) has the
tautological class (`ChernClass.IsCuspPushout.mk_eq_tautX`). -/
theorem IsCuspPushout.mk_eq_tautX_bar (hg : 0 < (curveGenus k X).toNat)
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U W₀)
    (hπW : W₀.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), W₀.valuation f < 1 →
      W₀.valuation f ≤ W₀.valuation ((π : F (barData k hτ)) : FFClosure X))
    (n : ℕ) [NeZero n] {Φ : TrivCocycle (DeltaBarX k hτ) (MXmod (DeltaBarX k hτ) n)}
    {Ψ : DeltaBar k hτ U →* Twist Φ} (hΦ : IsLocallyConstant Φ.1)
    (h : IsCuspPushout (barData_H_le k hτ) U
      (fun σ ↦ MXHat.proj (kIdx (barData k hτ) n)
        (syncEquivBar hg hUx hW₀ hW₀U hπW hπ σ)) Φ Ψ) :
    QuotientGroup.mk (toCocyclesX (fun _ _ ↦ rfl) hΦ) = tautBar hτ n hg :=
  ChernClass.IsCuspPushout.mk_eq_tautX _ _ _ hUx hW₀ hW₀U hπW hπ n hΦ h

end CurvesJacobian.Kummer
