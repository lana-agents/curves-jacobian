/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.LocAn

/-!
# Assembly of the existence half of the rel-isom-DGC (MR7 stage S8, skeleton)

MR8 and iut use the existence half of [LocAn] Theorem A for hyperbolic curves over number fields,
`Belyi.Anabelian.RelIsomDGC.Exists K`, as the explicit hypothesis `hDGC`. The uniqueness half is a
theorem for affine curves (`CurvesJacobian.LocAn.innerRigid`). This file states **how the
existence half follows from the stages of the MR7 plan** (Route T: [TopSurr] Thm 4.12 with the
Chern-class step T′). Every stage that is not yet formalised enters as one explicit theorem
argument with a precise statement. Each such argument is a **recorded debt** in `MR7-plan.md`
("S8 skeleton"). No argument is a structure, and none is assumed globally.

## The debts

1. **`ExistsProperMLF p`** (stages S4–S7 and T6/T7, [TopSurr] Thm 4.12 proof l.2231–2317 together
   with [LocAn] §§7–14 for proper curves): for every finite extension `L` of `ℚ_p`, every
   isomorphism over `G_L` between the `π₁ᵉᵗ` of two *proper* hyperbolic curves over `L` is
   induced by an `L`-isomorphism (`RelIsomDGC.ExistsProper L`). In the plan this splits further:
   * S4 = T′, the ample Chern class (group side done: `EigenH2`, `DiffMap`, `TransportH2`;
     geometric inputs D-d go to the Jacobian track);
   * S5 = T2, degree-0 Chern classes (Néron/semi-abelian model of `J`, D-a; base field, D-b);
   * S6 = [LocAn] Prop. 7.4 and §8;
   * S7 = [LocAn] §§9–10, Cor. 10.5;
   * T6/T7 = [LocAn] §§12–14 for proper curves (preservation of `L`-points and of relations,
     Thm 14.1).

   The intermediate statements are about `p`-adic fields `L` with imperfect residue field (the
   completions at generic points of the special fibre of a model, [LocAn] l.3530 `(∗)_{L-pt}`)
   and about `H²(Π_X, ℚ_p(1))`. They can only be stated once semistable models over `O_K` and the
   arithmetic Chern class exist, so they are not separate Lean arguments yet.
2. **`AffineReduction p`** (stage S8/T8 and glue G: cusp preservation [AbsTopI] Lemma 4.5(iv),(v)
   with MR3 weights, filling of cusps, the cover argument preceding [LocAn] Thm 14.1, and uniqueness
   on covers): over finite extensions of `ℚ_p`, the proper case implies the general case.
3. **`DescentNF`** (stage S1, [LocAn] Cor. 15.5, l.4320–4370): for a number field `K` embedded in
   a finite extension `L` of `ℚ_p`, existence over `L` implies existence over `K`. The proof
   needs three things:
   * `Π_{U_L} ≅ Π_U ×_{G_K} G_L`, i.e. invariance of `Δ_U` under `K̄ ⊆ L̄` (D-c, PI1TOP track);
   * finiteness of `Isom(X_{K̄}, Y_{K̄})` and its invariance under extension of algebraically
     closed fields;
   * Galois descent from a finite Galois `K'/K`, which uses uniqueness over the number field `K'`
     (for affine curves this is `innerRigid`).

## Main results

* `Belyi.Anabelian.RelIsomDGC.ExistsProper`: the existence half for proper hyperbolic curves;
* `CurvesJacobian.LocAn.ForallMLF p P`: `P L` for every finite extension `L` of `ℚ_p`;
* `CurvesJacobian.LocAn.ExistsProperMLF`, `CurvesJacobian.LocAn.AffineReduction`,
  `CurvesJacobian.LocAn.DescentNF`: the debt statements;
* `CurvesJacobian.LocAn.exists_padicField_of_numberField`: a number field embeds into a finite
  extension of `ℚ_p` (in its own universe);
* **`CurvesJacobian.LocAn.relIsomDGC_exists_mlf`**: debts 1 and 2 give `RelIsomDGC.Exists L` for
  every finite extension `L` of `ℚ_p`;
* **`CurvesJacobian.LocAn.relIsomDGC_exists_numberField`**: debts 1, 2 and 3 give
  `RelIsomDGC.Exists K` for every number field `K`, which is the form of MR8's `hDGC`.
-/

universe u

open AlgebraicGeometry CategoryTheory Belyi.Anabelian
open scoped TensorProduct

noncomputable section

namespace Belyi.Anabelian

open HypCurve in
/-- **Existence half of the rel-isom-DGC for proper hyperbolic curves** over `k`: the statement of
`RelIsomDGC.Exists k` for curves `C₁, C₂` without cusps (`U = X̄`). By `2g − 2 + r > 0` these are
the proper curves of genus `≥ 2`. This is the case [TopSurr] Thm 4.12 reduces to (proof,
l.2234–2236: "and X₁, X₂ are proper of genus g"). -/
def RelIsomDGC.ExistsProper (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
    haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
    ∀ (C₁ C₂ : HypCurve k), (C₁.U : Set C₁.Xbar)ᶜ = ∅ → (C₂.U : Set C₂.Xbar)ᶜ = ∅ →
    ∀ (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)),
    IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) → ∃ f : KIso C₁ C₂, InducedBy ξ₁ ξ₂ f φ

/-- The existence half implies its restriction to proper curves. -/
theorem RelIsomDGC.Exists.existsProper {k : Type u} [Field k] [CharZero k]
    (h : RelIsomDGC.Exists k) : RelIsomDGC.ExistsProper k :=
  fun Ω _ _ _ C₁ C₂ _ _ ξ₁ ξ₂ φ hφ ↦ h Ω C₁ C₂ ξ₁ ξ₂ φ hφ

end Belyi.Anabelian

namespace CurvesJacobian.LocAn

/-- A finite extension of `ℚ_p` has characteristic zero. -/
theorem charZero_of_padic (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] [Algebra ℚ_[p] L] :
    CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective

/-- `P L` holds for every finite extension `L` of `ℚ_p` (in the universe `u`). -/
def ForallMLF (p : ℕ) [Fact p.Prime] (P : ∀ (L : Type u) [Field L] [CharZero L], Prop) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L],
    @P L _ (charZero_of_padic p L)

/-- **Debt S4–S7 + T6/T7** (recorded in `MR7-plan.md`, "S8 skeleton"): [TopSurr] Thm 4.12 for
proper hyperbolic curves over every finite extension `L` of `ℚ_p`, existence half. -/
def ExistsProperMLF (p : ℕ) [Fact p.Prime] : Prop :=
  ForallMLF.{u} p fun L _ _ ↦ RelIsomDGC.ExistsProper L

/-- **Debt S8/T8 + G** (recorded in `MR7-plan.md`, "S8 skeleton"): over finite extensions of
`ℚ_p`, the existence half for proper curves implies it for all hyperbolic curves. The proof uses
cusp preservation ([AbsTopI] Lemma 4.5(iv),(v), MR3 weights), filling the cusps, and the cover
argument preceding [LocAn] Thm 14.1. -/
def AffineReduction (p : ℕ) [Fact p.Prime] : Prop :=
  ExistsProperMLF.{u} p → ForallMLF.{u} p fun L _ _ ↦ RelIsomDGC.Exists L

/-- **Debt S1** (recorded in `MR7-plan.md`, "S8 skeleton"; [LocAn] Cor. 15.5, l.4338–4370): for a
number field `K` and a finite extension `L` of `ℚ_p` containing `K`, the existence half over `L`
implies it over `K`. -/
def DescentNF (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [Algebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra K L],
    @RelIsomDGC.Exists L _ (charZero_of_padic p L) → RelIsomDGC.Exists K

/-- **A number field embeds into a finite extension of `ℚ_p`** (the residue field of a maximal
ideal of `ℚ_p ⊗_ℚ K`), in the universe of `K`. -/
theorem exists_padicField_of_numberField (p : ℕ) [Fact p.Prime] (K : Type u) [Field K]
    [NumberField K] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra ℚ_[p] L) (_ : FiniteDimensional ℚ_[p] L),
      Nonempty (K →+* L) := by
  haveI : Nontrivial (ℚ_[p] ⊗[ℚ] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain ℚ ℚ_[p] K
      (algebraMap ℚ ℚ_[p]).injective (algebraMap ℚ K).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℚ_[p] ⊗[ℚ] K)
  letI : Field ((ℚ_[p] ⊗[ℚ] K) ⧸ m) := Ideal.Quotient.field m
  exact ⟨(ℚ_[p] ⊗[ℚ] K) ⧸ m, inferInstance, inferInstance, inferInstance,
    ⟨(Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom⟩⟩

/-- **Existence half over finite extensions of `ℚ_p`**, from the debts S4–S7 + T6/T7
(`ExistsProperMLF`) and S8/T8 (`AffineReduction`). -/
theorem relIsomDGC_exists_mlf (p : ℕ) [Fact p.Prime] (hCore : ExistsProperMLF.{u} p)
    (hAff : AffineReduction.{u} p) (L : Type u) [Field L] [Algebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] : @RelIsomDGC.Exists L _ (charZero_of_padic p L) :=
  hAff hCore L

/-- **Existence half over number fields** (the form of MR8's `hDGC`), from the debts S4–S7 +
T6/T7 (`ExistsProperMLF`), S8/T8 (`AffineReduction`) and S1 (`DescentNF`) for one prime `p`. -/
theorem relIsomDGC_exists_numberField (p : ℕ) [Fact p.Prime] (hCore : ExistsProperMLF.{u} p)
    (hAff : AffineReduction.{u} p) (hDesc : DescentNF.{u} p) (K : Type u) [Field K]
    [NumberField K] : RelIsomDGC.Exists K := by
  obtain ⟨L, _, _, _, ⟨ι⟩⟩ := exists_padicField_of_numberField p K
  letI : Algebra K L := ι.toAlgebra
  exact hDesc K L (relIsomDGC_exists_mlf p hCore hAff L)

end CurvesJacobian.LocAn
