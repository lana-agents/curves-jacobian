/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.FillStep
import Belyi.Anabelian.BelyiChain

/-!
# Runs of `•`: the `Π`-chain `Π_U ⇝ Π_{U₁} ⇝ … ⇝ Π_{U_r}` of a sequence of fillings

[AbsTopII] Example 3.6 (ii) and Corollary 3.7 (a) (`Topics in Absolute Anabelian Geometry
II.txt` l.4669–4680, l.4743–4753) use runs `•, …, •` of operations filling in one closed point at a
time. For a hyperbolic curve `C = (X̄, U)` over a number field and opens
`U = U₀ ⊆ U₁ ⊆ … ⊆ U_r` with `U_{i+1} = U_i ∪ {xᵢ}` (`xᵢ` a `K`-rational point, as the
operations of type `•` require), all hyperbolic with a cusp,
`CurvesJacobian.Cusp.fillChain` is the `Π`-chain (of the arithmetic cuspidal extension `Π_U ↠ G_K`)
with objects `fillChainObj U_i` and operations `fillStepElemOp` (all of type `•`,
`fillChain_isDecuspRun`).

## Main results

* `fillMap_bijective_of_eq`, `fillEquivOfEq`: `Π_U → Π_{U'}` is an isomorphism if `U' = U`;
* **`fillChain`**, `fillChain_len`, `fillChain_isDecuspRun`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

set_option backward.isDefEq.respectTransparency false in
omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `Π_U → Π_{U'}` is bijective if `U' = U`. -/
lemma fillMap_bijective_of_eq {U' : C.Xbar.Opens} (h : C.U ≤ U') (he : U' = C.U) :
    Function.Bijective (fillMap Ω C hc h) := by
  subst he
  have e : (resAlg K h).toRingHom = RingHom.id _ := by
    ext a
    change Scheme.Hom.appLE (𝟙 C.Xbar) C.U C.U h a = a
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rw [Category.id_comp, show (CategoryTheory.homOfLE h).op = 𝟙 (Opposite.op C.U) from rfl]
    exact (congrArg (fun f ↦ (ConcreteCategory.hom f) a)
      (C.Xbar.presheaf.map_id (Opposite.op C.U))).trans rfl
  have : IsIso (Spec.map (CommRingCat.ofHom (resAlg K h).toRingHom)) := by
    rw [e, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  exact fundamentalGroupMap_bijective_of_isIso _ _

/-- The isomorphism `Π_U ≃ₜ* Π_{U'}` for `U' = U` (at the base points `basePoint`, `fillPoint`). -/
def fillEquivOfEq {U' : C.Xbar.Opens} (h : C.U ≤ U') (he : U' = C.U) :
    π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec K Ω Γ(C.Xbar, C.U)) ≃ₜ*
      π₁ᵉᵗ(fillPoint Ω C hc h ≫ baseChangeSpec K Ω Γ(C.Xbar, U')) :=
  ContinuousMulEquiv.mk' ((fillMap Ω C hc h).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (fillMap_bijective_of_eq Ω C hc h he)))
    (fun a b ↦ map_mul (fillMap Ω C hc h) a b)

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
lemma fillEquivOfEq_apply {U' : C.Xbar.Opens} (h : C.U ≤ U') (he : U' = C.U) (γ) :
    fillEquivOfEq Ω C hc h he γ = fillMap Ω C hc h γ :=
  rfl

variable (r : ℕ) (U : Fin (r + 1) → C.Xbar.Opens) (hU0 : U 0 = C.U) (hle : ∀ i, C.U ≤ U i)
  (hmono : ∀ i : Fin r, U i.castSucc ≤ U i.succ) (hcU : ∀ i, (U i : Set C.Xbar)ᶜ.Nonempty)
  (hyp : ∀ i, haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar (U i))
  (x : Fin r → C.Xbar) (hxU : ∀ i, x i ∈ U i.succ) (hxU' : ∀ i, x i ∉ U i.castSucc)
  (hx : ∀ i, (U i.succ : Set C.Xbar) \ U i.castSucc ⊆ {x i})
  (hxr : ∀ i, IsIso ((C.Xbar ↘ Spec (.of K)).residueFieldMap (x i)))

/-- **The run of `•`'s of a sequence of fillings** `U = U₀ ⊆ U₁ ⊆ … ⊆ U_r`,
`U_{i+1} = U_i ∪ {xᵢ}`, `xᵢ` rational ([AbsTopII] Example 3.6 (ii)): the `Π`-chain of `Π_U ↠ G_K`
with objects `Π_{U_i}` (`fillChainObj`) and operations `Π_{U_i} ↠ Π_{U_{i+1}}` of type `•`
(`fillStepElemOp`). -/
def fillChain : PiChain (arithmeticExt Ω C hc) where
  len := r
  obj i := fillChainObj Ω C hc (hle i) (hcU i) (hyp i)
  obj_zero := ⟨(fillEquivOfEq Ω C hc (hle 0) hU0).symm, ⊤, le_rfl, le_rfl, fun γ _ ↦
    (fillEquivOfEq Ω C hc (hle 0) hU0).symm_apply_apply γ⟩
  op j := fillStepElemOp Ω C hc (hle j.castSucc) (hmono j) (hcU j.castSucc) (hcU j.succ)
    (hyp j.castSucc) (hyp j.succ) (hxU j) (hxU' j) (hx j) (hxr j)

lemma fillChain_len : (fillChain Ω C hc r U hU0 hle hmono hcU hyp x hxU hxU' hx hxr).len = r := rfl

/-- All operations of `fillChain` are of type `•`. -/
lemma fillChain_isDecuspRun :
    (fillChain Ω C hc r U hU0 hle hmono hcU hyp x hxU hxU' hx hxr).IsDecuspRun 0 r
      (by rw [fillChain_len, zero_add]) :=
  fun _ _ ↦ rfl

end CurvesJacobian.Cusp
