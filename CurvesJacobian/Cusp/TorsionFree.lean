/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithmeticExt
import Pi1.Profinite.TorsionFree

/-!
# `Δ_U` is torsion-free (MR8.3, task 2 (i))

For an affine hyperbolic curve `U` over a number field (`CurvesJacobian.Cusp.arithmeticExt`),
the geometric fundamental group `Δ_U ≅ Π̂_{g,r}` (`r ≥ 1`) is a free profinite group, hence
torsion-free (pi1 `Pi1.Profinite.FreeHat.eq_one_of_isOfFinOrder`). Consequently every subgroup
of `Δ_U` lies in a normal open torsion-free subgroup of `Δ_U` (namely `Δ_U`), the side condition
of the de-cuspidalisation step `•` of [AbsTopI] Definition 4.2 (iii)(c)
(`Topics in Absolute Anabelian Geometry I.txt` l.3011–3014) for the trivial chain object
`Π₀ = Π_U`; cf. [AbsTopI] Lemma 4.1 (i) (l.2744: the cusp decomposition group "is a torsion-free,
commensurably terminal infinite subgroup of Δ") and (iv) (l.2749).

* `CurvesJacobian.Cusp.eq_one_of_isOfFinOrder_surfaceCompletion`: `Π̂_{g,r}` (universe `u`) is
  torsion-free for `r ≥ 1`;
* `CurvesJacobian.Cusp.Delta_eq_one_of_isOfFinOrder`: `Δ_U` is torsion-free;
* `Belyi.Anabelian.ChainObj.inTorsionFreeNormalOpen_of`: for a chain object with torsion-free
  `Δ_j`, every `C ≤ Δ_j` satisfies `InTorsionFreeNormalOpen`;
* `CurvesJacobian.Cusp.arithmeticExt_inTorsionFreeNormalOpen`: hence for `Π₀ = Π_U`.
-/

open CategoryTheory AlgebraicGeometry Belyi Belyi.Anabelian Pi1.Profinite
  ProfiniteGrp.ProfiniteCompletion

universe u

noncomputable section

namespace Belyi.Anabelian.ChainObj

variable {E : CuspidalExt.{u}}

/-- If `Δ_j` is torsion-free, every subgroup `C ≤ Δ_j` lies in a normal open torsion-free
subgroup of `Δ_j` (namely `Δ_j`). -/
theorem inTorsionFreeNormalOpen_of (A : ChainObj E)
    (htf : ∀ δ ∈ A.Delta, IsOfFinOrder δ → δ = 1) {C : Subgroup A.grp} (hC : C ≤ A.Delta) :
    A.InTorsionFreeNormalOpen C := by
  refine ⟨A.Delta, le_rfl, hC, fun d _ n hn ↦ (A.Delta.mul_mem (A.Delta.mul_mem ‹_› hn)
    (A.Delta.inv_mem ‹_›)), ?_, htf⟩
  rw [Subgroup.subgroupOf_self]
  exact isOpen_univ

end Belyi.Anabelian.ChainObj

namespace CurvesJacobian.Cusp

/-- **`Π̂_{g,r}` is torsion-free for `r ≥ 1`** (universe `u` version of
`Pi1.SurfaceGroup.eq_one_of_isOfFinOrder`). -/
theorem eq_one_of_isOfFinOrder_surfaceCompletion {g r : ℕ} (hr : 0 < r)
    {z : completion (GrpCat.of (ULift.{u} (Pi1.SurfaceGroup g r)))} (hz : IsOfFinOrder z) :
    z = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  let e := (surfaceCompletionEquivFreeHat.{u} g r).toMulEquiv
  have h := FreeHat.eq_one_of_isOfFinOrder _
    ((e.injective.isOfFinOrder_iff (f := e.toMonoidHom)).2 hz)
  exact e.injective (h.trans (map_one e).symm)

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **`Δ_U` is torsion-free.** -/
theorem Delta_eq_one_of_isOfFinOrder {δ : (projGk Ω C hc).toMonoidHom.ker}
    (hδ : IsOfFinOrder δ) : δ = 1 := by
  obtain ⟨e⟩ := nonempty_kerProjGk_equiv Ω C hc
  have hr : 0 < Nat.card ((baseChangeOpen K Ω C.U : Set (baseChange K Ω C.Xbar))ᶜ : Set _) :=
    haveI := (compl_finite_baseChangeOpen K Ω C.nonempty).to_subtype
    Nat.card_pos_iff.2 ⟨(compl_nonempty_baseChangeOpen K Ω hc).to_subtype, inferInstance⟩
  have h := eq_one_of_isOfFinOrder_surfaceCompletion hr
    ((e.toMulEquiv.injective.isOfFinOrder_iff (f := e.toMulEquiv.toMonoidHom)).2 hδ)
  exact e.injective (h.trans (map_one e).symm)

/-- **The `•` side condition for `Π₀ = Π_U`**: every subgroup of `Δ_U` lies in a normal open
torsion-free subgroup of `Δ_U`. -/
theorem arithmeticExt_inTorsionFreeNormalOpen {I : Subgroup (arithmeticExt Ω C hc).Pi}
    (hI : I ≤ (ChainObj.base (arithmeticExt Ω C hc)).Delta) :
    (ChainObj.base (arithmeticExt Ω C hc)).InTorsionFreeNormalOpen I := by
  refine ChainObj.inTorsionFreeNormalOpen_of _ (fun δ hδ hfin ↦ ?_) hI
  have := Delta_eq_one_of_isOfFinOrder Ω C hc (δ := ⟨δ, hδ⟩)
    ((Subgroup.subtype_injective _).isOfFinOrder_iff (f := Subgroup.subtype _) |>.1 hfin)
  exact congrArg Subtype.val this

end CurvesJacobian.Cusp
