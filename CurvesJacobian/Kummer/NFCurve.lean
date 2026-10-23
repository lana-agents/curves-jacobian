/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.NFCharacterization
import CurvesJacobian.Kummer.KummerFaithful

/-!
# [AbsTopIII] Prop. 1.8(i), "if", for a curve over a Kummer-faithful field

`NFModel.exists_eq_kummerMapZHat_of_restrictClosed` (`Kummer/NFCharacterization.lean`) proves
[AbsTopIII] Prop. 1.8(i), "if" (T3 l.2061–2106), in the Galois model `D` of `U`, with the
hypotheses `IsKummerFaithfulJac D` (Kummer-faithfulness for the Jacobian, used through
Prop. 1.6(iii)), "`k` is algebraically closed in `F`" and `H_L = H`. For the Galois model
`curveGaloisData k hτ` of a curve `X` over `k` with a `k`-point, these are discharged here:

* `IsKummerFaithfulJac` from `IsKummerFaithful k` ([AbsTopIII] Def. 1.5 for the Jacobian,
  `isKummerFaithfulJac_of_isKummerFaithful`);
* `k` algebraically closed in `F ≅ K(X)` (`mem_range_of_isAlgebraic_F`);
* `H_L = H` by definition of `curveGaloisData`.

The `𝔾_m`-form `IsTorallyKummerFaithful k` of continuous-kummer-theory stays a separate
hypothesis: [AbsTopIII] Def. 1.5 implies it (tori are semi-abelian), but Mathlib has no `𝔾_m` as a
group scheme, so `IsKummerFaithful k → IsTorallyKummerFaithful k` is not available.

* **`CurvesJacobian.Kummer.NFModel.exists_eq_kummerMapZHat_of_restrictClosed_curve`**.
-/

open CategoryTheory AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve IsLocalRing
open CurvesJacobian.Cusp

universe u

namespace CurvesJacobian.Kummer

namespace NFModel

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)] [IsAlgClosed (FFClosure X)]

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(i), "if", for an NF-curve `X` over a Kummer-faithful field `k`** of
characteristic `0` with `X(k) ≠ ∅` (Galois model `curveGaloisData k hτ`, `U` the open defined by
`t = τ`): if `η ∈ P_U` restricts trivially to an NF-point `x₁` and nontrivially to a closed point
`x₂` (`[k_{x_i} : k] < ∞`), then `η` is the Kummer class of a nonconstant NF-rational function. -/
theorem exists_eq_kummerMapZHat_of_restrictClosed_curve
    (N : NFModel (curveGaloisData k hτ))
    (htf : IsTorallyKummerFaithful k) (hk : IsKummerFaithful k)
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (hη : η ∈ PU (curveGaloisData k hτ))
    (A₁ : ValuationSubring (FFClosure X)) (hk₁ : ∀ c : k, algebraMap k (FFClosure X) c ∈ A₁)
    [Algebra k (ResidueField A₁)]
    (hkres₁ : ∀ c : k, residue A₁ ⟨algebraMap k (FFClosure X) c, hk₁ c⟩ =
      algebraMap k (ResidueField A₁) c)
    [Algebra.IsIntegral k (ResidueField A₁)]
    [FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A₁ hk₁ hkres₁)]
    (ht₁ : coordT τ ∈ A₁) (hA₁ : N.IsNFPoint A₁)
    (A₂ : ValuationSubring (FFClosure X)) (hk₂ : ∀ c : k, algebraMap k (FFClosure X) c ∈ A₂)
    [Algebra k (ResidueField A₂)]
    (hkres₂ : ∀ c : k, residue A₂ ⟨algebraMap k (FFClosure X) c, hk₂ c⟩ =
      algebraMap k (ResidueField A₂) c)
    [Algebra.IsIntegral k (ResidueField A₂)]
    [FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A₂ hk₂ hkres₂)]
    (ht₂ : coordT τ ∈ A₂)
    (h₁ : restrictClosed (curveGaloisData k hτ) A₁ hk₁ hkres₁ rfl ht₁ η = 1)
    (h₂ : restrictClosed (curveGaloisData k hτ) A₂ hk₂ hkres₂ rfl ht₂ η ≠ 1) :
    ∃ w : units (curveGaloisData k hτ), η = kummerMapZHat (curveGaloisData k hτ) w ∧
      w ∉ Set.range (constUnit (curveGaloisData k hτ)) ∧
      N.IsNFFunction ((w : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) :=
  N.exists_eq_kummerMapZHat_of_restrictClosed htf
    (isKummerFaithfulJac_of_isKummerFaithful k hτ hk σ hσ) (mem_range_of_isAlgebraic_F k hτ) rfl
    η hη A₁ hk₁ hkres₁ ht₁ hA₁ A₂ hk₂ hkres₂ ht₂ h₁ h₂

end NFModel

end CurvesJacobian.Kummer
