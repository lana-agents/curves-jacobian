/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithmeticExt
import CurvesJacobian.Cusp.CoverOpen
import Belyi.Anabelian.ChainOpen

/-!
# Operations of type `⋏` on the arithmetic fundamental group (MR8.3, chain functor)

[AbsTopI] Definition 4.2 (iii)(a) (`Topics in Absolute Anabelian Geometry I.txt` l.3005–3006):
an elementary operation `Π_j ⇝ Π_{j+1}` of type `⋏` is an open immersion `Π_{j+1} ↪ Π_j`
compatible with the rigidifying homomorphisms; by [AbsTopI] Remark 4.2.1 (l.3083–3092) a finite
étale covering of curves gives one.

* `Belyi.Anabelian.ElemOp.ofOpenSubgroup E H`: the operation `Π ⇝ H` of type `⋏` from the
  trivial chain object to the chain object `ChainObj.ofOpenSubgroup E H` of an open subgroup.
* `CurvesJacobian.Cusp.coverChainObj`: for `C : HypCurve K` (number field `K`) with a cusp and a
  connected finite étale `f : V ⟶ U = Spec Γ(X̄, U)` with a geometric point `η` over the base point
  of `Π_U`, the chain object of the open subgroup `π₁ᵉᵗ(V) ⊆ Π_U` (`coverSubgroup`);
  `coverChainObjEquiv : π₁ᵉᵗ(V, η) ≃ₜ*` its group, and `coverElemOp : Π_U ⇝ π₁ᵉᵗ(V)`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian
open scoped TensorProduct

universe u

noncomputable section

namespace Belyi.Anabelian.ElemOp

variable (E : CuspidalExt.{u}) (H : OpenSubgroup E.Pi)

/-- **The operation of type `⋏` of an open subgroup** `H ⊆ Π`: the inclusion
`H ↪ Π`, from the trivial chain object `Π₀ = Π` to `ChainObj.ofOpenSubgroup E H`. -/
def ofOpenSubgroup : ElemOp (ChainObj.base E) (ChainObj.ofOpenSubgroup E H) :=
  .cover ⟨(H : Subgroup E.Pi).subtype, continuous_subtype_val⟩ Subtype.val_injective
    (by
      change IsOpen (Set.range (Subtype.val : ↥(H : Subgroup E.Pi) → E.Pi))
      rw [Subtype.range_coe]
      exact H.isOpen)
    ⟨H, le_rfl, le_top, fun _ _ ↦ rfl⟩

lemma kind_ofOpenSubgroup : (ofOpenSubgroup E H).kind = .cover := rfl

end Belyi.Anabelian.ElemOp

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [CharZero K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
  {V : Scheme.{u}} (f : V ⟶ Spec Γ(C.Xbar, C.U)) [IsFiniteEtale f] [ConnectedSpace V]
  (η : Spec (.of Ω) ⟶ V) (h : η ≫ f = basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U))

/-- **The chain object of a connected finite étale cover** `f : V ⟶ U`: the open subgroup
`π₁ᵉᵗ(V) ⊆ Π_U` (the stabiliser of `η` in the fibre of `V`), as an object of `Chain(Π_U)`. -/
def coverChainObj [IsSlimGk K Ω] : ChainObj (arithmeticExt Ω C hc) :=
  ChainObj.ofOpenSubgroup (arithmeticExt Ω C hc) (coverSubgroup f η h)

/-- The group of `coverChainObj` is `π₁ᵉᵗ(V, η)` (via the map induced by `f`,
`AlgebraicGeometry.FiniteEtale.coe_coverEquiv_apply`). -/
def coverChainObjEquiv [IsSlimGk K Ω] : π₁ᵉᵗ(η) ≃ₜ* (coverChainObj Ω C hc f η h).grp :=
  coverEquiv f η h

/-- **The operation `Π_U ⇝ π₁ᵉᵗ(V)` of type `⋏`** of a connected finite étale cover `V → U`
([AbsTopI] Definition 4.2 (iii)(a), Remark 4.2.1). -/
def coverElemOp [IsSlimGk K Ω] :
    ElemOp (ChainObj.base (arithmeticExt Ω C hc)) (coverChainObj Ω C hc f η h) :=
  ElemOp.ofOpenSubgroup (arithmeticExt Ω C hc) (coverSubgroup f η h)

end CurvesJacobian.Cusp
