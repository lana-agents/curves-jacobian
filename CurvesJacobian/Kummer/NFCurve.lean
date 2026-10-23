/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.NFCharacterization
import CurvesJacobian.Kummer.KummerFaithful
import CurvesJacobian.Kummer.TorallyFromKF

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

* the `𝔾_m`-form `IsTorallyKummerFaithful k` of continuous-kummer-theory from
  `IsKummerFaithful k` ([AbsTopIII] Rem. 1.5.3(ii), `IsKummerFaithful.isTorallyKummerFaithful`,
  `Kummer/TorallyFromKF.lean`).

* **`CurvesJacobian.Kummer.NFModel.exists_eq_kummerMapZHat_of_restrictClosed_curve`**;
* the other directions need only `IsTorallyKummerFaithful k` (unconditional for number fields and
  finite extensions of `ℚ_p`): **`NFModel.exists_restrictClosed_of_isNF_curve`** (Prop. 1.8(i),
  "only if"), **`NFModel.eq_toKummerCompletion_of_restrictClosed_eq_curve`** (Prop. 1.8(ii),
  "if") and **`NFModel.exists_restrictClosed_eq_of_isNFConstant_curve`** (Prop. 1.8(ii),
  "only if").
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
    (hk : IsKummerFaithful k)
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
  N.exists_eq_kummerMapZHat_of_restrictClosed hk.isTorallyKummerFaithful
    (isKummerFaithfulJac_of_isKummerFaithful k hτ hk σ hσ) (mem_range_of_isAlgebraic_F k hτ) rfl
    η hη A₁ hk₁ hkres₁ ht₁ hA₁ A₂ hk₂ hkres₂ ht₂ h₁ h₂

/-- **[AbsTopIII] Prop. 1.8(i), "only if", for a curve** over a torally Kummer-faithful field `k`
(e.g. a number field, `NumberField.isTorallyKummerFaithful`, or a finite extension of `ℚ_p`,
`isTorallyKummerFaithful_of_isNonarchimedeanLocalField`): for a nonconstant NF-rational unit `f`
there are `M ≥ 1` and NF-points `x₁, x₂ ∈ U(k_x)` (`[k_{x_i} : k] < ∞`) with `κ_U(f^M)|x₁ = 0`
and `κ_U(f^M)|x₂ ≠ 0`. -/
theorem exists_restrictClosed_of_isNF_curve (N : NFModel (curveGaloisData k hτ))
    (htf : IsTorallyKummerFaithful k) (f : units (curveGaloisData k hτ))
    (hf : Transcendental k ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (hNF : N.IsNFFunction ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ))) :
    ∃ M : ℕ, 0 < M ∧
      (∃ (A : ValuationSubring (FFClosure X)) (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
        (ht : coordT τ ∈ A), N.IsNFPoint A ∧
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed (curveGaloisData k hτ) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk) rfl ht
            (kummerMapZHat (curveGaloisData k hτ) (f ^ M)) = 1) ∧
      (∃ (A : ValuationSubring (FFClosure X)) (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
        (ht : coordT τ ∈ A), N.IsNFPoint A ∧
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed (curveGaloisData k hτ) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk) rfl ht
            (kummerMapZHat (curveGaloisData k hτ) (f ^ M)) ≠ 1) :=
  N.exists_restrictClosed_of_isNF htf rfl f hf hNF

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(ii), "if", for a curve** over a torally Kummer-faithful field: if
`κ_U(f)|_x = c|_{G_{k_x}}` for an NF-rational unit `f`, an NF-point `x` (`[k_x : k] < ∞`) and
`c ∈ (kˣ)^∧`, then `c` is the Kummer class of an NF-constant. -/
theorem eq_toKummerCompletion_of_restrictClosed_eq_curve (N : NFModel (curveGaloisData k hτ))
    (htf : IsTorallyKummerFaithful k) (f : units (curveGaloisData k hτ))
    (hNF : N.IsNFFunction ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (A : ValuationSubring (FFClosure X)) (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
    [Algebra k (ResidueField A)]
    (hkres : ∀ c : k, residue A ⟨algebraMap k (FFClosure X) c, hk c⟩ =
      algebraMap k (ResidueField A) c)
    [Algebra.IsIntegral k (ResidueField A)]
    [FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A hk hkres)]
    (ht : coordT τ ∈ A) (hA : N.IsNFPoint A) (c : KummerCompletion k)
    (h : restrictClosed (curveGaloisData k hτ) A hk hkres rfl ht
        (kummerMapZHat (curveGaloisData k hτ) f) =
      restrictClosed (curveGaloisData k hτ) A hk hkres rfl ht
        (constMapZHat (curveGaloisData k hτ) c)) :
    ∃ b : kˣ, c = toKummerCompletion k b ∧ IsNFConstant (FFClosure X) (b : k) ∧
      constMapZHat (curveGaloisData k hτ) c =
        kummerMapZHat (curveGaloisData k hτ) (constUnit (curveGaloisData k hτ) b) :=
  N.eq_toKummerCompletion_of_restrictClosed_eq htf rfl f hNF A hk hkres ht hA c h

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(ii), "only if", for a curve** over a torally Kummer-faithful field:
if there is a nonconstant NF-rational unit `f₀`, then for every NF-constant `b ∈ kˣ` there are a
nonconstant NF-rational unit `f` and an NF-point `x ∈ U(k_x)`, `[k_x : k] < ∞`, with
`κ_U(f)|_x = κ(b)|_{G_{k_x}}`. -/
theorem exists_restrictClosed_eq_of_isNFConstant_curve (N : NFModel (curveGaloisData k hτ))
    (htf : IsTorallyKummerFaithful k) (f₀ : units (curveGaloisData k hτ))
    (hf₀ : Transcendental k ((f₀ : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (hNF₀ : N.IsNFFunction ((f₀ : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (b : kˣ) (hb : IsNFConstant (FFClosure X) (b : k)) :
    ∃ f : units (curveGaloisData k hτ),
      Transcendental k ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
      N.IsNFFunction ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
      ∃ (A : ValuationSubring (FFClosure X)) (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
        (ht : coordT τ ∈ A), N.IsNFPoint A ∧
        letI := Decomposition.residueAlgebra A hk
        ∃ (_ : Algebra.IsIntegral k (ResidueField A))
          (_ : FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A hk
            (Decomposition.residue_algebraMap_residueAlgebra A hk))),
          restrictClosed (curveGaloisData k hτ) A hk
              (Decomposition.residue_algebraMap_residueAlgebra A hk) rfl ht
              (kummerMapZHat (curveGaloisData k hτ) f) =
            restrictClosed (curveGaloisData k hτ) A hk
              (Decomposition.residue_algebraMap_residueAlgebra A hk) rfl ht
              (constMapZHat (curveGaloisData k hτ) (toKummerCompletion k b)) :=
  N.exists_restrictClosed_eq_of_isNFConstant htf rfl f₀ hf₀ hNF₀ b hb

end NFModel

end CurvesJacobian.Kummer
