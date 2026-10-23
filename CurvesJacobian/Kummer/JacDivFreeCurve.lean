/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianDivExt
import CurvesJacobian.Kummer.KummerCurve
import CurvesJacobian.Kummer.PrincipalDescent
import CurvesJacobian.Kummer.NFCurve

/-!
# Curve forms of [AbsTopIII] Prop. 1.6(ii), (iii) and Prop. 1.8(i) "if" under `JacDivFree`

The curve theorems `ker_res_curve`, `PU_eq_curve` (`Kummer/KummerCurve.lean`),
`eta_eq_one_iff_curve` (`Kummer/PrincipalEta.lean`), `eta_eq_one_iff_principal_curve`,
`tD_conj_identity_iff_principal_curve` (`Kummer/PrincipalDescent.lean`) and
`NFModel.exists_eq_kummerMapZHat_of_restrictClosed_curve` (`Kummer/NFCurve.lean`) assume that `k`
is Kummer-faithful ([AbsTopIII] Def. 1.5), but only use `⋂_{N ≥ 1} N · J(k) = 0` for the Jacobian
`J` of the curve ([AbsTopIII] Rem. 1.5.4(i) reduces this to a finite extension of `ℚ_p`). Here they
are restated with the hypothesis `JacDivFree X σ hσ L` (`⋂_N N · J(L) = 0`) for an arbitrary field
extension `L / k` (`Kummer/JacobianDivExt.lean`); with `L` a finite extension of `ℚ_p` containing
`k` this is the reduction of Rem. 1.5.4(i).
-/

open CategoryTheory AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve IsLocalRing
open WeilCurves.FunctionField CurvesJacobian.Cusp

universe u

namespace CurvesJacobian.Kummer

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (L : Type u) [Field L] [Algebra k L]

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve, exactness**: `ker(res) = (kˣ)^∧`, for `X(k) ≠ ∅`
and `⋂_N N · J(L) = 0` for some extension `L / k`. -/
theorem ker_res_curve_of_jacDivFree (hL : JacDivFree X σ hσ L) :
    (res (curveGaloisData k hτ)).ker = (constMapZHat (curveGaloisData k hτ)).range :=
  ker_res (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ L hL)
    (mem_range_of_isAlgebraic_F k hτ)

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve, the image**: `P_U = κ(Γ(U, 𝒪^×)) · (kˣ)^∧`, for
`X(k) ≠ ∅` and `⋂_N N · J(L) = 0` for some extension `L / k`. -/
theorem PU_eq_curve_of_jacDivFree (hL : JacDivFree X σ hσ L) :
    PU (curveGaloisData k hτ) = (kummerMapZHat (curveGaloisData k hτ)).range ⊔
      (constMapZHat (curveGaloisData k hτ)).range :=
  PU_eq (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ L hL)
    (mem_range_of_isAlgebraic_F k hτ)

attribute [local instance] isFunctionField_F

/-- **[AbsTopIII] Prop. 1.6(ii)** for a curve with a `k`-point, under `⋂_N N · J(L) = 0`: a
degree-`0` divisor supported on `k`-rational points is principal on `X_{k̄}` iff `η_D = 0`. -/
theorem eta_eq_one_iff_curve_of_jacDivFree (hL : JacDivFree X σ hσ L)
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ (QuotientAddGroup.mk (ratDiv f) :
      Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) = 0 :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  eta_eq_one_iff (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ L hL)
    (fun N hN y hy => by
      obtain ⟨w, hw⟩ := exists_nsmul_eq_jacPsi k hτ σ hσ hN.ne' ⟨y, hy⟩
      exact ⟨w, congrArg Subtype.val hw⟩)
    (fun N _ => weilDual_bijective_baseChange k hτ)
    (fun N _ => finite_picTorsion_baseChange k hτ) f hf

/-- **[AbsTopIII] Prop. 1.6(ii)** for a curve with a `k`-point, under `⋂_N N · J(L) = 0`: a
degree-`0` divisor supported on `k`-rational points is principal on `X` iff `η_D = 0`. -/
theorem eta_eq_one_iff_principal_curve_of_jacDivFree (hL : JacDivFree X σ hσ L)
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  (eta_eq_one_iff_curve_of_jacDivFree k hτ σ hσ L hL f hf).trans (mk_ratDiv_eq_zero_iff f)

/-- **[AbsTopIII] Prop. 1.6(ii)** as stated in the paper (T3 l.1993–2000), under
`⋂_N N · J(L) = 0`: `t_D` is `Δ_X`-conjugate to the identity section iff `D` is principal. -/
theorem tD_conj_identity_iff_principal_curve_of_jacDivFree (hL : JacDivFree X σ hσ L)
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (x₀ : RatPoint (curveGaloisData k hτ)) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    (∃ q : DeltaAb (curveGaloisData k hτ), ∀ g : Gk k (FFClosure X),
      (etaCocycle f x₀ : Gk k (FFClosure X) → DeltaAb (curveGaloisData k hτ)) g = q / (g • q)) ↔
      ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  (eta_eq_one_iff_exists_conj f hf x₀).symm.trans
    (eta_eq_one_iff_principal_curve_of_jacDivFree k hτ σ hσ L hL f hf)

namespace NFModel

variable [CharZero (FFClosure X)] [IsAlgClosed (FFClosure X)]

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(i), "if", for an NF-curve** over a torally Kummer-faithful field `k`
with `X(k) ≠ ∅` and `⋂_N N · J(L) = 0` for some extension `L / k`. -/
theorem exists_eq_kummerMapZHat_of_restrictClosed_curve_of_jacDivFree
    (N : NFModel (curveGaloisData k hτ)) (htf : IsTorallyKummerFaithful k)
    (hL : JacDivFree X σ hσ L)
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
    (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ L hL)
    (mem_range_of_isAlgebraic_F k hτ) rfl
    η hη A₁ hk₁ hkres₁ ht₁ hA₁ A₂ hk₂ hkres₂ ht₂ h₁ h₂

end NFModel

end CurvesJacobian.Kummer
