/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.JacobianBridge

/-!
# `⋂_N N · J(k) = 0` descends from an extension field (MR5 Task B, step B0)

[AbsTopIII] Rem. 1.5.4(i) (`Topics in Absolute Anabelian Geometry III.txt` l.1909–1919) reduces
Kummer-faithfulness to the case of a finite extension of `ℚ_p`. For the Jacobian of a curve `X`
over `k` (the only abelian variety used in [AbsTopIII] Prop. 1.6(iii), see `Kummer/PicAction.lean`)
the reduction is elementary: `J(k) ↪ J(L)` for every field extension `L / k`
(`picRes_injective`), and an element of `⋂_N N · J(k)` maps into `⋂_N N · J(L)`.

* `CurvesJacobian.Kummer.JacDivFree X σ hσ K`: `⋂_{N ≥ 1} N · J(K) = 0` for the `K`-points
  `J(K) = Pic⁰_{X/k,σ}(K)` (`jacPoints`);
* **`JacDivFree.of_ext`**: `JacDivFree` for some extension `L` of `k` implies it for `k`;
* **`isKummerFaithfulJac_curveGaloisData_of_ext`**: hence `IsKummerFaithfulJac` for the Galois
  model of `X` (MR5 J1), e.g. with `L` a finite extension of `ℚ_p` containing a number field `k`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi KummerTheory Curve AffOrbicurve
open WeilCurves.FunctionField CurvesJacobian.Cusp

universe u

namespace CurvesJacobian.Kummer

section Ext

variable {k : Type u} [Field k] [PerfectField k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsCurveOver k X] (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- **`⋂_{N ≥ 1} N · J(K) = 0`** for the group `J(K) = Pic⁰_{X/k,σ}(K)` of `K`-points of the
Jacobian of `X` (`K` a field extension of `k`). -/
def JacDivFree (K : Type u) [Field K] [Algebra k K] : Prop :=
  ∀ z ∈ jacPoints X σ hσ K, (∀ N : ℕ, 0 < N → ∃ y ∈ jacPoints X σ hσ K, N • y = z) → z = 0

variable {X σ hσ}

/-- **`⋂_N N · J(k) = 0` descends from any extension field** (`J(k) ↪ J(L)`). -/
theorem JacDivFree.of_ext (L : Type u) [Field L] [Algebra k L] (hL : JacDivFree X σ hσ L) :
    JacDivFree X σ hσ k := by
  intro z hz hdiv
  apply picRes_injective X σ hσ k L
  rw [map_zero]
  refine hL _ (picRes_mem_jacPoints X σ hσ k L hz) fun N hN ↦ ?_
  obtain ⟨y, hy, hyz⟩ := hdiv N hN
  exact ⟨_, picRes_mem_jacPoints X σ hσ k L hy, by rw [← map_nsmul, hyz]⟩

end Ext

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  (σ : Spec (CommRingCat.of k) ⟶ X)
  (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- **Kummer-faithfulness of the Jacobian (MR5 J1) from an extension field**: if
`⋂_N N · J(L) = 0` for some field extension `L / k`, then `IsKummerFaithfulJac` holds for the
Galois model of `X`. -/
theorem isKummerFaithfulJac_curveGaloisData_of_ext (L : Type u) [Field L] [Algebra k L]
    (hL : JacDivFree X σ hσ L) : IsKummerFaithfulJac (curveGaloisData k hτ) :=
  isKummerFaithfulJac_curveGaloisData k hτ σ hσ (JacDivFree.of_ext L hL)

end CurvesJacobian.Kummer
