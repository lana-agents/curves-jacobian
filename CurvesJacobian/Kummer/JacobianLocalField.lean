/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacDivFreeCurve
import CurvesJacobian.PointTopology.Group
import CurvesJacobian.PointTopology.NumberFieldLocal

/-!
# `⋂_N N · J(k) = 0` for number fields and `p`-adic fields (MR5 Task B, debt D-KF discharged)

[AbsTopIII] Rem. 1.5.4(i) (`Topics in Absolute Anabelian Geometry III.txt` l.1909–1919): for an
abelian variety `A` over a finite extension `K` of `ℚ_p`, `⋂_N N · A(K) = 0`, and number fields
reduce to this case. For the Jacobian `J = jacK` of a curve `X` with a rational point:

* **`jacDivFree_of_properSpace`**: `JacDivFree X σ hσ L` (`⋂_N N · J(L) = 0`) for every field
  extension `L / k` carrying a proper ultrametric norm (e.g. a finite extension of `ℚ_p`), from
  `PointTopology.GroupScheme.eq_one_of_forall_pow_eq` (`J(L)` is a profinite group) and
  `J_k(L) ≅ J(L)` (`jacKPointsMulEquiv`);
* **`jacDivFree_padic`**: `JacDivFree X σ hσ k` for `k` a finite extension of `ℚ_p` given as
  `[Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]` (`k ↪ L` with `L` a proper normed field,
  `Padic.exists_localField_of_finiteDimensional`); `isKummerFaithfulJac_curveGaloisData_padic`;
* **`jacDivFree_numberField`**: `JacDivFree X σ hσ k` for a number field `k`
  (`k ↪ L` with `L / ℚ_2` finite, `NumberField.exists_localField`, and `JacDivFree.of_ext`);
* the curve forms of [AbsTopIII] Prop. 1.6(ii), (iii) and Prop. 1.8(i) "if" over number fields
  without further hypotheses: `ker_res_curve_numberField`, `PU_eq_curve_numberField`,
  `eta_eq_one_iff_curve_numberField`, `eta_eq_one_iff_principal_curve_numberField`,
  `tD_conj_identity_iff_principal_curve_numberField`,
  `NFModel.exists_eq_kummerMapZHat_of_restrictClosed_curve_numberField`, and the same forms of
  Prop. 1.6(ii), (iii) over finite extensions of `ℚ_p` (`*_padic`).
-/

open CategoryTheory AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve IsLocalRing
open WeilCurves.FunctionField CurvesJacobian.Cusp

universe u

namespace CurvesJacobian.Kummer

section Jac

variable {k : Type u} [Field k] [PerfectField k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsCurveOver k X] (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

open MonObj in
/-- **`⋂_N N · J(L) = 0` for `L` a proper ultrametric normed field** (e.g. a finite extension of
`ℚ_p`) containing `k`. -/
theorem jacDivFree_of_properSpace (L : Type u) [NormedField L] [IsUltrametricDist L]
    [ProperSpace L] [Algebra k L] : JacDivFree X σ hσ L := by
  intro z hz hdiv
  let φ := (jacKPointsMulEquiv X σ hσ (AlgebraicClosure k) L).symm
  haveI : IsProper (jacK X σ hσ (AlgebraicClosure k)).hom :=
    (inferInstance : IsAbelianVariety (jacK X σ hσ (AlgebraicClosure k))).isProper
  have h1 := PointTopology.GroupScheme.eq_one_of_forall_pow_eq
    (jacK X σ hσ (AlgebraicClosure k)) (Belyi.specAlgebraMap (k₀ := k) L)
    (φ (Multiplicative.ofAdd ⟨z, hz⟩)) fun N hN ↦ by
      obtain ⟨y, hy, hyz⟩ := hdiv N hN
      refine ⟨φ (Multiplicative.ofAdd ⟨y, hy⟩), ?_⟩
      rw [← map_pow, ← ofAdd_nsmul]
      congr 2
      exact Subtype.ext hyz
  have h3 : (Multiplicative.ofAdd (⟨z, hz⟩ : jacPoints X σ hσ L)) = 1 :=
    φ.injective (h1.trans (map_one φ).symm)
  exact congrArg Subtype.val (Multiplicative.ofAdd.injective h3 :
    (⟨z, hz⟩ : jacPoints X σ hσ L) = 0)

/-- **`⋂_N N · J(k) = 0` over a finite extension `k` of `ℚ_p`** ([AbsTopIII] Rem. 1.5.4(i) for
the Jacobian; discharges debt D-KF over `p`-adic fields). -/
theorem jacDivFree_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k] :
    JacDivFree X σ hσ k := by
  obtain ⟨L, _, _, _, ⟨f⟩⟩ := Padic.exists_localField_of_finiteDimensional p k
  letI : Algebra k L := f.toAlgebra
  exact JacDivFree.of_ext L (jacDivFree_of_properSpace X σ hσ L)

/-- **`⋂_N N · J(k) = 0` over a number field `k`** ([AbsTopIII] Rem. 1.5.4(i) for the Jacobian). -/
theorem jacDivFree_numberField [NumberField k] : JacDivFree X σ hσ k := by
  obtain ⟨L, _, _, _, ⟨f⟩⟩ := NumberField.exists_localField k
  letI : Algebra k L := f.toAlgebra
  exact JacDivFree.of_ext L (jacDivFree_of_properSpace X σ hσ L)

end Jac

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

include σ hσ

/-- **Kummer-faithfulness of the Jacobian (MR5 J1) over a number field.** -/
theorem isKummerFaithfulJac_curveGaloisData_numberField [NumberField k] :
    IsKummerFaithfulJac (curveGaloisData k hτ) :=
  isKummerFaithfulJac_curveGaloisData k hτ σ hσ (jacDivFree_numberField X σ hσ)

/-- **Kummer-faithfulness of the Jacobian (MR5 J1) over a finite extension of `ℚ_p`.** -/
theorem isKummerFaithfulJac_curveGaloisData_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] : IsKummerFaithfulJac (curveGaloisData k hτ) :=
  isKummerFaithfulJac_curveGaloisData k hτ σ hσ (jacDivFree_padic X σ hσ p)

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve over a number field, exactness**:
`ker(res) = (kˣ)^∧` (`X(k) ≠ ∅`). -/
theorem ker_res_curve_numberField [NumberField k] :
    (res (curveGaloisData k hτ)).ker = (constMapZHat (curveGaloisData k hτ)).range :=
  ker_res_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_numberField X σ hσ)

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve over a number field, the image**:
`P_U = κ(Γ(U, 𝒪^×)) · (kˣ)^∧` (`X(k) ≠ ∅`). -/
theorem PU_eq_curve_numberField [NumberField k] :
    PU (curveGaloisData k hτ) = (kummerMapZHat (curveGaloisData k hτ)).range ⊔
      (constMapZHat (curveGaloisData k hτ)).range :=
  PU_eq_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_numberField X σ hσ)

attribute [local instance] isFunctionField_F

/-- **[AbsTopIII] Prop. 1.6(ii)** for a curve with a `k`-point over a number field: a degree-`0`
divisor supported on `k`-rational points is principal on `X_{k̄}` iff `η_D = 0`. -/
theorem eta_eq_one_iff_curve_numberField [NumberField k]
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ (QuotientAddGroup.mk (ratDiv f) :
      Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) = 0 :=
  eta_eq_one_iff_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_numberField X σ hσ) f hf

/-- **[AbsTopIII] Prop. 1.6(ii)** for a curve with a `k`-point over a number field: a degree-`0`
divisor supported on `k`-rational points is principal on `X` iff `η_D = 0`. -/
theorem eta_eq_one_iff_principal_curve_numberField [NumberField k]
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  eta_eq_one_iff_principal_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_numberField X σ hσ) f hf

/-- **[AbsTopIII] Prop. 1.6(ii)** as stated in the paper (T3 l.1993–2000), over a number field:
`t_D` is `Δ_X`-conjugate to the identity section iff `D` is principal. -/
theorem tD_conj_identity_iff_principal_curve_numberField [NumberField k]
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (x₀ : RatPoint (curveGaloisData k hτ)) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    (∃ q : DeltaAb (curveGaloisData k hτ), ∀ g : Gk k (FFClosure X),
      (etaCocycle f x₀ : Gk k (FFClosure X) → DeltaAb (curveGaloisData k hτ)) g = q / (g • q)) ↔
      ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  tD_conj_identity_iff_principal_curve_of_jacDivFree k hτ σ hσ k
    (jacDivFree_numberField X σ hσ) f hf x₀

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve over a finite extension of `ℚ_p`, exactness**:
`ker(res) = (kˣ)^∧` (`X(k) ≠ ∅`). -/
theorem ker_res_curve_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] :
    (res (curveGaloisData k hτ)).ker = (constMapZHat (curveGaloisData k hτ)).range :=
  ker_res_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_padic X σ hσ p)

/-- **[AbsTopIII] Prop. 1.6(iii) for a curve over a finite extension of `ℚ_p`, the image**:
`P_U = κ(Γ(U, 𝒪^×)) · (kˣ)^∧` (`X(k) ≠ ∅`). -/
theorem PU_eq_curve_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] :
    PU (curveGaloisData k hτ) = (kummerMapZHat (curveGaloisData k hτ)).range ⊔
      (constMapZHat (curveGaloisData k hτ)).range :=
  PU_eq_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_padic X σ hσ p)

/-- **[AbsTopIII] Prop. 1.6(ii)** for a curve with a `k`-point over a finite extension of `ℚ_p`:
a degree-`0` divisor supported on `k`-rational points is principal on `X_{k̄}` iff `η_D = 0`. -/
theorem eta_eq_one_iff_curve_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k]
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ (QuotientAddGroup.mk (ratDiv f) :
      Pic (kbar k (FFClosure X)) (F (Kummer.baseChange (curveGaloisData k hτ)))) = 0 :=
  eta_eq_one_iff_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_padic X σ hσ p) f hf

/-- **[AbsTopIII] Prop. 1.6(ii)** for a curve with a `k`-point over a finite extension of `ℚ_p`:
a degree-`0` divisor supported on `k`-rational points is principal on `X` iff `η_D = 0`. -/
theorem eta_eq_one_iff_principal_curve_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k]
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  eta_eq_one_iff_principal_curve_of_jacDivFree k hτ σ hσ k (jacDivFree_padic X σ hσ p) f hf

/-- **[AbsTopIII] Prop. 1.6(ii)** as stated in the paper (T3 l.1993–2000), over a finite
extension of `ℚ_p`: `t_D` is `Δ_X`-conjugate to the identity section iff `D` is principal. -/
theorem tD_conj_identity_iff_principal_curve_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k]
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0)
    (x₀ : RatPoint (curveGaloisData k hτ)) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    (∃ q : DeltaAb (curveGaloisData k hτ), ∀ g : Gk k (FFClosure X),
      (etaCocycle f x₀ : Gk k (FFClosure X) → DeltaAb (curveGaloisData k hτ)) g = q / (g • q)) ↔
      ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  tD_conj_identity_iff_principal_curve_of_jacDivFree k hτ σ hσ k
    (jacDivFree_padic X σ hσ p) f hf x₀

namespace NFModel

variable [CharZero (FFClosure X)] [IsAlgClosed (FFClosure X)]

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop. 1.8(i), "if", for an NF-curve over a number field** with `X(k) ≠ ∅`:
if `η ∈ P_U` restricts trivially to an NF-point `x₁` and nontrivially to a closed point `x₂`,
then `η` is the Kummer class of a nonconstant NF-rational function. -/
theorem exists_eq_kummerMapZHat_of_restrictClosed_curve_numberField [NumberField k]
    (N : NFModel (curveGaloisData k hτ))
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
  exists_eq_kummerMapZHat_of_restrictClosed_curve_of_jacDivFree k hτ σ hσ k N
    (NumberField.isTorallyKummerFaithful k) (jacDivFree_numberField X σ hσ)
    η hη A₁ hk₁ hkres₁ ht₁ hA₁ A₂ hk₂ hkres₂ ht₂ h₁ h₂

end NFModel

end CurvesJacobian.Kummer
