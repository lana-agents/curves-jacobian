/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CoverCusps
import CurvesJacobian.Cusp.ChainPushOps
import CurvesJacobian.Cusp.FillChain

/-!
# The Belyi chain of an affine hyperbolic curve over a number field (MR8.5)

[AbsTopII] Example 3.6 (ii) (`Topics in Absolute Anabelian Geometry II.txt` l.4655–4680) and
Corollary 3.7 (a) (l.4743–4753): for `X` of strictly Belyi type, the `Π`-chain
`X ⇝ V ⇝ Q ⇝ Q_l ⇝ … ⇝ P ⇝ W ⇝ W_n ⇝ … ⇝ U ⇝ … ⇝ V ⇝ X* = X` of type
`⋏, ⋎, •, …, •, ⋏, •, …, •, ⋎` with a terminal isomorphism to the trivial chain.

**Scope.** Following the MR8 decision (IUT only needs affine hyperbolic curves: the
once-punctured elliptic curve and its quotients), all curves are *affine* hyperbolic curves, i.e.
`HypCurve`s with at least one cusp; every `•` fills one rational point of a curve which keeps a
cusp.

`BelyiData CX` (over a number field `M ⊇ K`, `CX` over `K`) consists of
* hyperbolic curves `CQ = (Q̄, Q)` and `CW = (V̄, W)` over `M` with a cusp;
* runs of fillings `Q = UQ₀ ⊆ … ⊆ UQ_l = P` in `Q̄` and `W = UW₀ ⊆ … ⊆ UW_r = V` in `V̄`, one
  `M`-rational point at a time ([AbsTopII] Example 3.6, l.4634–4635, l.4667–4668), all
  hyperbolic with a cusp (the hypotheses of `fillChain`);
* finite étale maps `FV : V ⟶ U_X` (over `Spec M ⟶ Spec K`), `FQ : V ⟶ Q` and `β : W ⟶ P`
  (over `Spec M`), on the affine schemes `Spec Γ(·)`.

(For a Belyi map `β` and `P = ℙ¹ ∖ {0, 1, ∞}`, this is [AbsTopII] Example 3.6; the existence of
such data is [AbsTopII] Example 3.6 (i), MR8.4, belyi `exists_belyi_open_le_finSub`; for curves of
strictly Belyi type it is `CurvesJacobian.Cusp.exists_belyiData`.)

## Main definitions

* `BelyiData.path D : OpPath (base E) _` (`E = arithmeticExt Ω CX hcX`) — the Belyi path
  `o₁ = ⋏ (Π_V ↪ Π_X)`, `o₂ = ⋎ (Π_V ↪ Π_Q)`, the run of `•`'s of `Q ⊆ … ⊆ P` pushed to `E`,
  `o₃ = ⋏ (Π_W ↪ Π_P)`, the run of `•`'s of `W ⊆ … ⊆ V` pushed to `E`, `o₄ = ⋎ (Π_V ↪ Π_X)`;
  the cuspidal decomposition groups are matched by `CurvesJacobian.Cusp.CoverCusps`
  (`cuspMatchQ`, `cuspMatchW`);
* `BelyiData.isBelyiType`: its `Π`-chain is of type `⋏, ⋎, •^l, ⋏, •^r, ⋎`;
* `BelyiData.terminalIso`: a terminal isomorphism to the trivial chain;
* **`BelyiData.belyiCandidate_mem`**: the resulting candidates `Π_{UW_{r-m}} ↠ Π_V ↪ Π_X` lie in
  `belyiCusp E` ([AbsTopII] Corollary 3.7 (a)).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve Pi1.Profinite

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CurvesJacobian.Cusp

section Galois

variable (M Ω : Type u) [Field M] [Field Ω] [Algebra M Ω] [IsSepClosed Ω]

/-- `G_M → G_M` induced by the identity of `Spec M` is the identity. -/
lemma galoisMap_self (y : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M Ω)))) :
    galoisMap M M Ω y = y := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap M M)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have h1 := DFunLike.congr_fun (fundamentalGroupMap_congr e (specMap_algebraMap_tower M M Ω)
    (Category.comp_id _)) y
  exact h1.trans (DFunLike.congr_fun (fundamentalGroupMap_id (Category.comp_id _)) y)

end Galois

section FillG

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) {U₁ : C.Xbar.Opens} (h₁ : C.U ≤ U₁)
  (hc₁ : (U₁ : Set C.Xbar)ᶜ.Nonempty)
  (hyp₁ : haveI := IsCurveOver.isIntegral K C.Xbar
    2 < 2 * Anabelian.curveGenus K C.Xbar + cuspDegree K C.Xbar U₁)

/-- The element of `G_K` by which `fillTransport` conjugates the projections. -/
def fillG : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  fiberIsoMap (Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.Xbar, U₁))))
    (basePoint_spec₂ Ω (fillCurve C h₁ hyp₁) hc₁) (fillPoint_spec₂ Ω C hc h₁)
    (fiberIsoMap (baseChangeSpec K Ω Γ(C.Xbar, U₁)) rfl rfl (fillAlpha Ω C hc h₁ hc₁ hyp₁))

omit [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `projGkFill ∘ fillTransport = conj ∘ projGk`. -/
lemma projGkFill_fillTransport (y) :
    projGkFill Ω C hc h₁ (fillTransport Ω C hc h₁ hc₁ hyp₁ y) =
      fillG Ω C hc h₁ hc₁ hyp₁ * projGk Ω (fillCurve C h₁ hyp₁) hc₁ y *
        (fillG Ω C hc h₁ hc₁ hyp₁)⁻¹ :=
  (fundamentalGroupMap_autContinuousMulEquivOfIso _ (basePoint_spec₂ Ω (fillCurve C h₁ hyp₁) hc₁)
    (fillPoint_spec₂ Ω C hc h₁) _ y).trans (autContinuousMulEquivOfIso_self _ _)

end FillG

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M]

/-- **Belyi data** for an affine hyperbolic curve `CX` over `K` ([AbsTopII] Example 3.6): curves
`CQ = (Q̄, Q)`, `CW = (V̄, W)` over a number field `M ⊇ K` with runs of fillings
`Q ⊆ … ⊆ P` and `W ⊆ … ⊆ V` (one rational point at a time, all hyperbolic with a cusp) and
finite étale maps `V ⟶ U_X`, `V ⟶ Q`, `β : W ⟶ P`. -/
structure BelyiData (CX : HypCurve K) where
  /-- The curve `(Q̄, Q)`. -/
  CQ : HypCurve M
  hcQ : (CQ.U : Set CQ.Xbar)ᶜ.Nonempty
  /-- The number of fillings `Q ⇝ P`. -/
  l : ℕ
  UQ : Fin (l + 1) → CQ.Xbar.Opens
  hUQ0 : UQ 0 = CQ.U
  hleQ : ∀ i, CQ.U ≤ UQ i
  hmonoQ : ∀ i : Fin l, UQ i.castSucc ≤ UQ i.succ
  hcUQ : ∀ i, (UQ i : Set CQ.Xbar)ᶜ.Nonempty
  hypQ : ∀ i, haveI := IsCurveOver.isIntegral M CQ.Xbar
    2 < 2 * Anabelian.curveGenus M CQ.Xbar + cuspDegree M CQ.Xbar (UQ i)
  xQ : Fin l → CQ.Xbar
  hxUQ : ∀ i, xQ i ∈ UQ i.succ
  hxUQ' : ∀ i, xQ i ∉ UQ i.castSucc
  hxQ : ∀ i, (UQ i.succ : Set CQ.Xbar) \ UQ i.castSucc ⊆ {xQ i}
  /-- The filled points are `M`-rational (operations of type `•` fill rational cusps). -/
  ratQ : ∀ i, IsIso ((CQ.Xbar ↘ Spec (.of M)).residueFieldMap (xQ i))
  /-- The curve `(V̄, W)`. -/
  CW : HypCurve M
  hcW : (CW.U : Set CW.Xbar)ᶜ.Nonempty
  /-- The number of fillings `W ⇝ V`. -/
  r : ℕ
  UW : Fin (r + 1) → CW.Xbar.Opens
  hUW0 : UW 0 = CW.U
  hleW : ∀ i, CW.U ≤ UW i
  hmonoW : ∀ i : Fin r, UW i.castSucc ≤ UW i.succ
  hcUW : ∀ i, (UW i : Set CW.Xbar)ᶜ.Nonempty
  hypW : ∀ i, haveI := IsCurveOver.isIntegral M CW.Xbar
    2 < 2 * Anabelian.curveGenus M CW.Xbar + cuspDegree M CW.Xbar (UW i)
  xW : Fin r → CW.Xbar
  hxUW : ∀ i, xW i ∈ UW i.succ
  hxUW' : ∀ i, xW i ∉ UW i.castSucc
  hxW : ∀ i, (UW i.succ : Set CW.Xbar) \ UW i.castSucc ⊆ {xW i}
  ratW : ∀ i, IsIso ((CW.Xbar ↘ Spec (.of M)).residueFieldMap (xW i))
  /-- `V ⟶ U_X`. -/
  FV : Spec Γ(CW.Xbar, UW (Fin.last r)) ⟶ Spec Γ(CX.Xbar, CX.U)
  [finFV : IsFiniteEtale FV]
  hFV : FV ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CW.Xbar, UW (Fin.last r)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K M))
  /-- `V ⟶ Q`. -/
  FQ : Spec Γ(CW.Xbar, UW (Fin.last r)) ⟶ Spec Γ(CQ.Xbar, CQ.U)
  [finFQ : IsFiniteEtale FQ]
  hFQ : FQ ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(CQ.Xbar, CQ.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CW.Xbar, UW (Fin.last r)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M M))
  /-- The Belyi map `β : W ⟶ P`. -/
  β : Spec Γ(CW.Xbar, CW.U) ⟶ Spec Γ(CQ.Xbar, UQ (Fin.last l))
  [finβ : IsFiniteEtale β]
  hβ : β ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(CQ.Xbar, UQ (Fin.last l)))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CW.Xbar, CW.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M M))

attribute [instance] BelyiData.finFV BelyiData.finFQ BelyiData.finβ

namespace BelyiData

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [Algebra M Ω] [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]
  {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (D : BelyiData (M := M) CX)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-! ### The curves `V` and `P` -/

/-- The curve `(V̄, V)`. -/
abbrev CV : HypCurve M := fillCurve D.CW (D.hleW (Fin.last D.r)) (D.hypW (Fin.last D.r))

lemma hcV : ((D.CV).U : Set (D.CV).Xbar)ᶜ.Nonempty := D.hcUW (Fin.last D.r)

/-- The curve `(Q̄, P)`. -/
abbrev CP : HypCurve M := fillCurve D.CQ (D.hleQ (Fin.last D.l)) (D.hypQ (Fin.last D.l))

lemma hcP : ((D.CP).U : Set (D.CP).Xbar)ᶜ.Nonempty := D.hcUQ (Fin.last D.l)

/-! ### The maps of fundamental groups -/

/-- `φ₁ : Π_V ↪ Π_X`. -/
abbrev φ₁ : (arithmeticExt Ω D.CV D.hcV).Pi →ₜ* (arithmeticExt Ω CX hcX).Pi :=
  coverPiHom Ω CX hcX D.CV D.hcV D.FV

/-- `j₂ : Π_V ↪ Π_Q`. -/
abbrev j₂ : (arithmeticExt Ω D.CV D.hcV).Pi →ₜ* (arithmeticExt Ω D.CQ D.hcQ).Pi :=
  coverPiHom Ω D.CQ D.hcQ D.CV D.hcV D.FQ

/-- `Π_W ↪ Π_P` (at the base point of `P`). -/
abbrev jβ : (arithmeticExt Ω D.CW D.hcW).Pi →ₜ* (arithmeticExt Ω D.CP D.hcP).Pi :=
  coverPiHom Ω D.CP D.hcP D.CW D.hcW D.β

/-- The change of base point of `P` to the base point of the run of fillings of `Q`. -/
abbrev TP := fillTransport Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l)) (D.hcUQ (Fin.last D.l))
  (D.hypQ (Fin.last D.l))

/-- The change of base point of `V` to the base point of the run of fillings of `W`. -/
abbrev TV := fillTransport Ω D.CW D.hcW (D.hleW (Fin.last D.r)) (D.hcUW (Fin.last D.r))
  (D.hypW (Fin.last D.r))

/-- `φ₃ : Π_W ↪ Π_P` (at the base point of the run of fillings of `Q`). -/
abbrev φ₃ := (ContinuousMonoidHom.toContinuousMonoidHom (D.TP Ω)).comp (D.jβ Ω)

/-- `φ₄ : Π_V ↪ Π_X` (from the base point of the run of fillings of `W`). -/
abbrev φ₄ := (D.φ₁ Ω hcX).comp (ContinuousMonoidHom.toContinuousMonoidHom (D.TV Ω).symm)

lemma φ₁_injective : Function.Injective (D.φ₁ Ω hcX) := coverPiHom_injective _ _ _ _ _ _

lemma isOpen_range_φ₁ : IsOpen (Set.range (D.φ₁ Ω hcX)) := isOpen_range_coverPiHom _ _ _ _ _ _

lemma φ₃_injective : Function.Injective (D.φ₃ Ω) :=
  (D.TP Ω).injective.comp (coverPiHom_injective _ _ _ _ _ _)

lemma isOpen_range_φ₃ : IsOpen (Set.range (D.φ₃ Ω)) := by
  rw [ContinuousMonoidHom.coe_comp, Set.range_comp]
  exact (D.TP Ω).toHomeomorph.isOpenMap _ (isOpen_range_coverPiHom _ _ _ _ _ _)

lemma φ₄_injective : Function.Injective (D.φ₄ Ω hcX) :=
  (D.φ₁_injective Ω hcX).comp (D.TV Ω).symm.injective

lemma isOpen_range_φ₄ : IsOpen (Set.range (D.φ₄ Ω hcX)) := by
  change IsOpen (Set.range (D.φ₁ Ω hcX ∘ (D.TV Ω).symm))
  rw [(D.TV Ω).symm.surjective.range_comp]
  exact D.isOpen_range_φ₁ Ω hcX

/-! ### The Galois groups -/

local notation "GM" => π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M Ω)))
local notation "GK" => π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω)))

/-- `G_M ↪ G_K` for `V ⟶ U_X`. -/
abbrev ιV : GM →ₜ* GK := coverι Ω CX hcX D.CV D.hcV D.FV D.hFV

/-- The conjugating element of `V ⟶ U_X`. -/
def gV : GK := coverG Ω CX hcX D.CV D.hcV D.FV D.hFV

lemma ιV_apply (y : GM) : D.ιV Ω hcX y = D.gV Ω hcX * galoisMap K M Ω y * (D.gV Ω hcX)⁻¹ :=
  autContinuousMulEquivOfIso_self _ _

/-- The conjugating element of `V ⟶ Q`. -/
def gQ : GM := coverG Ω D.CQ D.hcQ D.CV D.hcV D.FQ D.hFQ

lemma coverιQ_apply (y : GM) :
    coverι Ω D.CQ D.hcQ D.CV D.hcV D.FQ D.hFQ y = D.gQ Ω * y * (D.gQ Ω)⁻¹ := by
  change autContinuousMulEquivOfIso (D.gQ Ω) (galoisMap M M Ω y) = _
  rw [autContinuousMulEquivOfIso_self, galoisMap_self]

/-- `ι_Q : G_M → G_K` for the run of fillings of `Q`: `ι_V ∘ conj(g_Q⁻¹)`. -/
def ιQ : GM →ₜ* GK :=
  (D.ιV Ω hcX).comp (ContinuousMonoidHom.toContinuousMonoidHom
    (autContinuousMulEquivOfIso ((D.gQ Ω)⁻¹ : GM)))

lemma ιQ_apply (y : GM) :
    D.ιQ Ω hcX y = D.ιV Ω hcX ((D.gQ Ω)⁻¹ * y * (D.gQ Ω)⁻¹⁻¹) :=
  congrArg (D.ιV Ω hcX) (autContinuousMulEquivOfIso_self _ _)

lemma ιQ_injective : Function.Injective (D.ιQ Ω hcX) :=
  (coverι_injective Ω CX hcX D.CV D.hcV D.FV D.hFV).comp
    (autContinuousMulEquivOfIso ((D.gQ Ω)⁻¹ : GM)).injective

lemma isOpen_range_ιQ : IsOpen (Set.range (D.ιQ Ω hcX)) := by
  change IsOpen (Set.range (D.ιV Ω hcX ∘ autContinuousMulEquivOfIso ((D.gQ Ω)⁻¹ : GM)))
  rw [(autContinuousMulEquivOfIso _).surjective.range_comp]
  exact isOpen_range_coverι Ω CX hcX D.CV D.hcV D.FV D.hFV

/-- `A₁ = Π_V` (after `⋏`). -/
abbrev A₁ : ChainObj (arithmeticExt Ω CX hcX) :=
  (ChainObj.base (arithmeticExt Ω CX hcX)).coverObj (D.φ₁ Ω hcX) (D.φ₁_injective Ω hcX)
    (D.isOpen_range_φ₁ Ω hcX)

lemma hcompQ (x : (arithmeticExt Ω D.CV D.hcV).Pi) :
    D.ιQ Ω hcX ((arithmeticExt Ω D.CQ D.hcQ).pr (D.j₂ Ω x)) = (D.A₁ Ω hcX).toG x := by
  change _ = (arithmeticExt Ω CX hcX).pr (D.φ₁ Ω hcX x)
  rw [pr_coverPiHom Ω D.CQ D.hcQ D.CV D.hcV D.FQ D.hFQ,
    pr_coverPiHom Ω CX hcX D.CV D.hcV D.FV D.hFV, ιQ_apply, coverιQ_apply]
  congr 1
  simp only [mul_assoc, inv_inv, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- The conjugating element of `fillTransport` for `P`. -/
def g₁ : GM := fillG Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l)) (D.hcUQ (Fin.last D.l))
  (D.hypQ (Fin.last D.l))

/-- The conjugating element of `β`. -/
def gβ : GM := coverG Ω D.CP D.hcP D.CW D.hcW D.β D.hβ

lemma coverιβ_apply (y : GM) :
    coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ y = D.gβ Ω * y * (D.gβ Ω)⁻¹ := by
  change autContinuousMulEquivOfIso (D.gβ Ω) (galoisMap M M Ω y) = _
  rw [autContinuousMulEquivOfIso_self, galoisMap_self]

/-- `ι_W : G_M → G_K` for the run of fillings of `W`. -/
def ιW : GM →ₜ* GK :=
  (D.ιQ Ω hcX).comp ((ContinuousMonoidHom.toContinuousMonoidHom
    (autContinuousMulEquivOfIso (D.g₁ Ω))).comp (coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ))

/-- `ι_W` is `ι_V` up to conjugation by `w = g_Q⁻¹ g₁ g_β`. -/
lemma ιW_apply (y : GM) : D.ιW Ω hcX y =
    D.ιV Ω hcX ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * y * ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω)⁻¹) := by
  have e : (D.gQ Ω)⁻¹ * (D.g₁ Ω * (D.gβ Ω * y * (D.gβ Ω)⁻¹) * (D.g₁ Ω)⁻¹) * (D.gQ Ω)⁻¹⁻¹ =
      (D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * y * ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω)⁻¹ := by
    group
  have e0 : D.ιW Ω hcX y = D.ιQ Ω hcX (D.g₁ Ω * (D.gβ Ω * y * (D.gβ Ω)⁻¹) * (D.g₁ Ω)⁻¹) := by
    change D.ιQ Ω hcX (autContinuousMulEquivOfIso (D.g₁ Ω)
      (coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ y)) = _
    rw [autContinuousMulEquivOfIso_self, coverιβ_apply]
  exact e0.trans ((D.ιQ_apply Ω hcX _).trans (congrArg (D.ιV Ω hcX) e))

lemma ιW_injective : Function.Injective (D.ιW Ω hcX) :=
  (D.ιQ_injective Ω hcX).comp ((autContinuousMulEquivOfIso (D.g₁ Ω)).injective.comp
    (coverι_injective Ω D.CP D.hcP D.CW D.hcW D.β D.hβ))

lemma isOpen_range_ιW : IsOpen (Set.range (D.ιW Ω hcX)) := by
  let f : GM →ₜ* GM := (ContinuousMonoidHom.toContinuousMonoidHom
    (autContinuousMulEquivOfIso (D.g₁ Ω))).comp (coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ)
  have hf : IsOpen (Set.range f) := by
    change IsOpen (Set.range (autContinuousMulEquivOfIso (D.g₁ Ω) ∘
      coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ))
    rw [Set.range_comp]
    exact (autContinuousMulEquivOfIso (D.g₁ Ω)).toHomeomorph.isOpenMap _
      (isOpen_range_coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ)
  have h := isOpen_map_of_isOpen_range (D.ιQ Ω hcX) (D.isOpen_range_ιQ Ω hcX)
    (ChainObj.isOpen_coe_range f hf)
  have e : Set.range (D.ιW Ω hcX) =
      (((f : GM →* GM).range.map (D.ιQ Ω hcX : GM →* GK) : Subgroup GK) : Set GK) := by
    ext z
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨f y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  rw [e]
  exact h

/-! ### The chain objects and operations -/

/-- The run of fillings `Q ⊆ … ⊆ P`. -/
abbrev cQ : PiChain (arithmeticExt Ω D.CQ D.hcQ) :=
  fillChain Ω D.CQ D.hcQ D.l D.UQ D.hUQ0 D.hleQ D.hmonoQ D.hcUQ D.hypQ D.xQ D.hxUQ D.hxUQ' D.hxQ
    D.ratQ

/-- The run of fillings `W ⊆ … ⊆ V`. -/
abbrev cW : PiChain (arithmeticExt Ω D.CW D.hcW) :=
  fillChain Ω D.CW D.hcW D.r D.UW D.hUW0 D.hleW D.hmonoW D.hcUW D.hypW D.xW D.hxUW D.hxUW' D.hxW
    D.ratW

lemma j₂_injective : Function.Injective (D.j₂ Ω) := coverPiHom_injective _ _ _ _ _ _

lemma isOpen_range_j₂ : IsOpen (Set.range (D.j₂ Ω)) := isOpen_range_coverPiHom _ _ _ _ _ _

/-- **Matching of the cusps of `Q` with those of `X`** (through `V`). -/
theorem cuspMatchQ : (D.A₁ Ω hcX).CuspMatch (E' := arithmeticExt Ω D.CQ D.hcQ) (D.j₂ Ω) := by
  refine ChainObj.cuspMatch_of_commensurable (arithCusps Ω D.CV D.hcV) (fun J hJ ↦ ?_)
    fun I' hI' ↦ ?_
  · obtain ⟨I, hI, hle, hidx⟩ := exists_arithCusps_map_coverPiHom Ω CX hcX D.CV D.hcV D.FV hJ
    refine ⟨I, hI, ?_⟩
    rw [ChainObj.image_coverObj, ChainObj.image_base]
    exact Subgroup.commensurable_comap_of_map_le (D.φ₁_injective Ω hcX) hle hidx
  · obtain ⟨J, hJ, hle, hidx⟩ := exists_arithCusps_coverHom_le Ω D.CQ D.hcQ D.CV D.hcV D.FQ hI'
    exact ⟨J, hJ, Subgroup.commensurable_of_le hle hidx⟩

/-- `A₃ = Π_P` (the end of the pushed run of fillings of `Q`). -/
abbrev A₃ : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₁ Ω hcX).push (D.j₂ Ω) (D.isOpen_range_j₂ Ω) (D.ιQ Ω hcX) (D.ιQ_injective Ω hcX)
    (D.isOpen_range_ιQ Ω hcX) (D.hcompQ Ω hcX) ((D.cQ Ω).obj ⟨(D.cQ Ω).len, Nat.lt_succ_self _⟩)

lemma hcompW (x : (arithmeticExt Ω D.CW D.hcW).Pi) :
    D.ιW Ω hcX ((arithmeticExt Ω D.CW D.hcW).pr x) = (D.A₃ Ω hcX).toG (D.φ₃ Ω x) := by
  change D.ιQ Ω hcX (autContinuousMulEquivOfIso (D.g₁ Ω)
    (coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ (projGk Ω D.CW D.hcW x))) =
      D.ιQ Ω hcX (projGkFill Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l)) (D.TP Ω (D.jβ Ω x)))
  have hP : projGk Ω D.CP D.hcP (D.jβ Ω x) =
      coverι Ω D.CP D.hcP D.CW D.hcW D.β D.hβ (projGk Ω D.CW D.hcW x) :=
    pr_coverPiHom Ω D.CP D.hcP D.CW D.hcW D.β D.hβ x
  rw [projGkFill_fillTransport, autContinuousMulEquivOfIso_self]
  change _ = D.ιQ Ω hcX (D.g₁ Ω * projGk Ω D.CP D.hcP (D.jβ Ω x) * (D.g₁ Ω)⁻¹)
  rw [hP]

/-- `Π_P ⇝ Π_W` target before pushing. -/
abbrev A₄ : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₃ Ω hcX).coverObj (D.φ₃ Ω) (D.φ₃_injective Ω) (D.isOpen_range_φ₃ Ω)

set_option quotPrecheck false in
local notation "Φ₁" => (BelyiData.φ₁ Ω hcX D :
  (arithmeticExt Ω (BelyiData.CV D) (BelyiData.hcV D)).Pi →* (arithmeticExt Ω CX hcX).Pi)
set_option quotPrecheck false in
local notation "J₂" => (BelyiData.j₂ Ω D :
  (arithmeticExt Ω (BelyiData.CV D) (BelyiData.hcV D)).Pi →* (arithmeticExt Ω D.CQ D.hcQ).Pi)
set_option quotPrecheck false in
local notation "Φ₃" => (BelyiData.φ₃ Ω D : (arithmeticExt Ω D.CW D.hcW).Pi →*
  π₁ᵉᵗ(fillPoint Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l)) ≫
    baseChangeSpec M Ω Γ(D.CQ.Xbar, D.UQ (Fin.last D.l))))

set_option maxHeartbeats 1600000 in
-- the cusp bookkeeping unfolds the pushed chain objects of two runs of fillings
/-- **Matching of the cusps of `W` with those of `X`** (through `P`, `Q`, `V`). -/
theorem cuspMatchW : (D.A₄ Ω hcX).CuspMatch (E' := arithmeticExt Ω D.CW D.hcW)
    (ContinuousMonoidHom.id _) := by
  refine ChainObj.cuspMatch_of_commensurable (arithCusps Ω D.CW D.hcW) (fun J hJ ↦ ?_)
    fun I' hI' ↦ ⟨I', hI', ?_⟩
  · obtain ⟨IP, hIP, hle1, hidx1⟩ := exists_arithCusps_map_coverPiHom Ω D.CP D.hcP D.CW D.hcW D.β hJ
    haveI := nonempty_fillOpen Ω D.CQ (D.hleQ (Fin.last D.l))
    obtain ⟨IQ, hIQ, hIQe⟩ := exists_mem_arithCusps_map_fillMap Ω D.CQ D.hcQ
      (D.hleQ (Fin.last D.l)) (D.hcUQ (Fin.last D.l)) (D.hypQ (Fin.last D.l))
      (fillAlpha Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l)) (D.hcUQ (Fin.last D.l))
        (D.hypQ (Fin.last D.l))) hIP
    obtain ⟨JV, hJV, hle2, hidx2⟩ :=
      exists_arithCusps_coverHom_le Ω D.CQ D.hcQ D.CV D.hcV D.FQ hIQ
    obtain ⟨I, hI, hle3, hidx3⟩ := exists_arithCusps_map_coverPiHom Ω CX hcX D.CV D.hcV D.FV hJV
    refine ⟨I, hI, ?_⟩
    have h1 : (D.A₁ Ω hcX).image I = I.comap Φ₁ :=
      ChainObj.image_coverObj_base (D.φ₁ Ω hcX) (D.φ₁_injective Ω hcX)
        (D.isOpen_range_φ₁ Ω hcX) I
    have hA : (D.A₃ Ω hcX).image I = ((D.cQ Ω).obj ⟨(D.cQ Ω).len, Nat.lt_succ_self _⟩).image
        (((D.A₁ Ω hcX).image I).map J₂) :=
      ChainObj.image_push (D.A₁ Ω hcX) (D.j₂ Ω) (D.isOpen_range_j₂ Ω) (D.ιQ Ω hcX)
        (D.ιQ_injective Ω hcX) (D.isOpen_range_ιQ Ω hcX) (D.hcompQ Ω hcX)
        ((D.cQ Ω).obj ⟨(D.cQ Ω).len, Nat.lt_succ_self _⟩) I
    have hB := image_fillChainObj Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l)) (D.hcUQ (Fin.last D.l))
      (D.hypQ (Fin.last D.l)) (((D.A₁ Ω hcX).image I).map J₂)
    have h2 : (D.A₃ Ω hcX).image I = ((I.comap Φ₁).map J₂).map
        (fillMap Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l))).toMonoidHom := by
      rw [hA, ← h1]
      exact hB
    have hC := ChainObj.image_coverObj (D.A₃ Ω hcX) (D.φ₃ Ω) (D.φ₃_injective Ω)
      (D.isOpen_range_φ₃ Ω) I
    rw [hC, h2]
    have c1 := Subgroup.commensurable_comap_of_map_le (D.φ₁_injective Ω hcX) hle3 hidx3
    have c2 := Subgroup.commensurable_of_le hle2 hidx2
    have c3 : ((I.comap Φ₁).map J₂).Commensurable IQ :=
      (Subgroup.Commensurable.map' J₂ c1).symm.trans c2
    have c4 : (((I.comap Φ₁).map J₂).map
        (fillMap Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l))).toMonoidHom).Commensurable
          (IP.map (D.TP Ω).toMulEquiv.toMonoidHom) :=
      (Subgroup.Commensurable.map'
        (fillMap Ω D.CQ D.hcQ (D.hleQ (Fin.last D.l))).toMonoidHom c3).trans
          (Subgroup.commensurable_of_eq hIQe)
    have c5 := Subgroup.Commensurable.comap' Φ₃ c4
    have e6 : (IP.map (D.TP Ω).toMulEquiv.toMonoidHom).comap Φ₃ =
        IP.comap (D.jβ Ω :
          (arithmeticExt Ω D.CW D.hcW).Pi →* (arithmeticExt Ω D.CP D.hcP).Pi) := by
      ext y
      simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv]
      change (D.TP Ω).toMulEquiv.symm (D.TP Ω (D.jβ Ω y)) ∈ IP ↔ _
      rw [show (D.TP Ω).toMulEquiv.symm (D.TP Ω (D.jβ Ω y)) = D.jβ Ω y from
        (D.TP Ω).symm_apply_apply _]
      exact Iff.rfl
    exact (Subgroup.commensurable_comap_of_map_le (coverPiHom_injective _ _ _ _ _ _) hle1
      hidx1).trans (c5.trans (Subgroup.commensurable_of_eq e6)).symm
  · have e : I'.map ((ContinuousMonoidHom.id (arithmeticExt Ω D.CW D.hcW).Pi : _ →ₜ* _) :
        _ →* _) = I' := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨y, hy, rfl⟩
    exact (congrArg (fun T ↦ T.Commensurable I') e).mpr (.refl I')

/-- `ρ` of the first object of a run of fillings is bijective (`U₀ = U`). -/
lemma rhoTop_bijective_cQ :
    Function.Bijective (((D.cQ Ω).obj ⟨0, Nat.succ_pos _⟩).rhoTop fun _ ↦ trivial) :=
  fillMap_bijective_of_eq Ω D.CQ D.hcQ (D.hleQ 0) D.hUQ0

lemma rhoTop_bijective_cW :
    Function.Bijective (((D.cW Ω).obj ⟨0, Nat.succ_pos _⟩).rhoTop fun _ ↦ trivial) :=
  fillMap_bijective_of_eq Ω D.CW D.hcW (D.hleW 0) D.hUW0

/-- `o₁ : Π_X ⇝ Π_V` of type `⋏`. -/
abbrev o₁ := ElemOp.ofCover (ChainObj.base (arithmeticExt Ω CX hcX)) (D.φ₁ Ω hcX)
  (D.φ₁_injective Ω hcX)
  (D.isOpen_range_φ₁ Ω hcX)

/-- `o₂ : Π_V ⇝ Π_Q` of type `⋎`. -/
abbrev o₂ := ElemOp.toPush (D.A₁ Ω hcX) (D.j₂ Ω) (D.isOpen_range_j₂ Ω) (D.ιQ Ω hcX)
  (D.ιQ_injective Ω hcX) (D.isOpen_range_ιQ Ω hcX) (D.hcompQ Ω hcX)
  ((D.cQ Ω).obj ⟨0, Nat.succ_pos _⟩) (fun _ ↦ trivial) (D.j₂_injective Ω)
  (D.rhoTop_bijective_cQ Ω).1

/-- The run `Π_Q ⇝ … ⇝ Π_P` of `•`'s. -/
abbrev r₁ := OpPath.pushRun (D.A₁ Ω hcX) (D.j₂ Ω) (D.isOpen_range_j₂ Ω) (D.ιQ Ω hcX)
  (D.ιQ_injective Ω hcX) (D.isOpen_range_ιQ Ω hcX) (D.hcompQ Ω hcX) (D.cuspMatchQ Ω hcX) (D.cQ Ω)

/-- `o₃ : Π_P ⇝ Π_W` of type `⋏`. -/
abbrev o₃ := ElemOp.coverPush (D.A₃ Ω hcX) (D.φ₃ Ω) (D.φ₃_injective Ω) (D.isOpen_range_φ₃ Ω)
  (D.ιW Ω hcX) (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX)
  ((D.cW Ω).obj ⟨0, Nat.succ_pos _⟩) (fun _ ↦ trivial) (D.rhoTop_bijective_cW Ω)

/-- The run `Π_W ⇝ … ⇝ Π_V` of `•`'s. -/
abbrev r₂ := OpPath.pushRun (D.A₄ Ω hcX) (ContinuousMonoidHom.id _)
  (ElemOp.isOpen_range_id (E' := arithmeticExt Ω D.CW D.hcW)) (D.ιW Ω hcX)
  (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX) (D.cuspMatchW Ω hcX) (D.cW Ω)

/-- `A₅ = Π_V` at the end of the pushed run of fillings of `W`. -/
abbrev A₅ : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₄ Ω hcX).push (E' := arithmeticExt Ω D.CW D.hcW) (ContinuousMonoidHom.id _)
    (ElemOp.isOpen_range_id (E' := arithmeticExt Ω D.CW D.hcW)) (D.ιW Ω hcX)
    (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX)
    ((D.cW Ω).obj ⟨(D.cW Ω).len, Nat.lt_succ_self _⟩)

/-- The conjugating element of `fillTransport` for `V`. -/
def g₂ : GM := fillG Ω D.CW D.hcW (D.hleW (Fin.last D.r)) (D.hcUW (Fin.last D.r))
  (D.hypW (Fin.last D.r))

/-- The element `ι_V(w)` conjugating the last projection. -/
def g₀ : GK := D.ιV Ω hcX ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * D.g₂ Ω)

/-- The projection `Π_X → G_K` of the last object: `conj(g₀) ∘ pr`. -/
def toG' : (arithmeticExt Ω CX hcX).Pi →ₜ* (arithmeticExt Ω CX hcX).G :=
  (ContinuousMonoidHom.toContinuousMonoidHom (autContinuousMulEquivOfIso (D.g₀ Ω hcX))).comp
    (projGk Ω CX hcX)

lemma toG'_apply (x : (arithmeticExt Ω CX hcX).Pi) : D.toG' Ω hcX x =
    D.g₀ Ω hcX * projGk Ω CX hcX x * (D.g₀ Ω hcX)⁻¹ :=
  autContinuousMulEquivOfIso_self _ _

lemma htoG (x : (D.A₅ Ω hcX).grp) : D.toG' Ω hcX (D.φ₄ Ω hcX x) = (D.A₅ Ω hcX).toG x := by
  obtain ⟨y, rfl⟩ := (D.TV Ω).surjective x
  have hV : projGk Ω CX hcX (D.φ₁ Ω hcX y) = D.ιV Ω hcX (projGk Ω D.CV D.hcV y) :=
    pr_coverPiHom Ω CX hcX D.CV D.hcV D.FV D.hFV y
  have e1 : D.toG' Ω hcX (D.φ₄ Ω hcX (D.TV Ω y)) =
      D.g₀ Ω hcX * D.ιV Ω hcX (projGk Ω D.CV D.hcV y) * (D.g₀ Ω hcX)⁻¹ :=
    (D.toG'_apply Ω hcX _).trans (congrArg (fun t ↦ D.g₀ Ω hcX * t * (D.g₀ Ω hcX)⁻¹)
      ((congrArg (fun t ↦ projGk Ω CX hcX (D.φ₁ Ω hcX t))
        ((D.TV Ω).symm_apply_apply y)).trans hV))
  have e2 : ∀ p : GM, D.g₀ Ω hcX * D.ιV Ω hcX p * (D.g₀ Ω hcX)⁻¹ =
      D.ιV Ω hcX ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * D.g₂ Ω * p *
        ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * D.g₂ Ω)⁻¹) := fun p ↦ by
    rw [g₀]
    simp only [map_mul, map_inv]
  have e3 : ∀ p : GM, (D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * D.g₂ Ω * p *
        ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * D.g₂ Ω)⁻¹ =
      (D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω * (D.g₂ Ω * p * (D.g₂ Ω)⁻¹) *
        ((D.gQ Ω)⁻¹ * D.g₁ Ω * D.gβ Ω)⁻¹ := fun p ↦ by
    group
  have e4 := (projGkFill_fillTransport Ω D.CW D.hcW (D.hleW (Fin.last D.r))
    (D.hcUW (Fin.last D.r)) (D.hypW (Fin.last D.r)) y).symm
  exact e1.trans ((e2 _).trans ((congrArg (D.ιV Ω hcX) (e3 _)).trans
    ((D.ιW_apply Ω hcX _).symm.trans (congrArg (D.ιW Ω hcX) e4))))

lemma ker_toG' :
    ((D.toG' Ω hcX : (arithmeticExt Ω CX hcX).Pi →* (arithmeticExt Ω CX hcX).G)).ker =
      ((arithmeticExt Ω CX hcX).pr :
        (arithmeticExt Ω CX hcX).Pi →* (arithmeticExt Ω CX hcX).G).ker := by
  ext x
  simp only [MonoidHom.mem_ker]
  change autContinuousMulEquivOfIso (D.g₀ Ω hcX) (projGk Ω CX hcX x) = 1 ↔ projGk Ω CX hcX x = 1
  exact map_eq_one_iff _ (autContinuousMulEquivOfIso (D.g₀ Ω hcX)).injective

lemma isOpen_range_toG' : IsOpen (Set.range (D.toG' Ω hcX)) := by
  change IsOpen (Set.range (autContinuousMulEquivOfIso (D.g₀ Ω hcX) ∘ projGk Ω CX hcX))
  rw [Set.range_comp, (projGk_surjective Ω CX hcX).range_eq, Set.image_univ,
    (autContinuousMulEquivOfIso _).surjective.range_eq]
  exact isOpen_univ

lemma isSlim_ker_toG' :
    IsSlim ((D.toG' Ω hcX : (arithmeticExt Ω CX hcX).Pi →* (arithmeticExt Ω CX hcX).G)).ker := by
  rw [ker_toG']
  exact (arithmeticExt Ω CX hcX).slim_delta

lemma ker_toG'_ne_bot :
    ((D.toG' Ω hcX : (arithmeticExt Ω CX hcX).Pi →* (arithmeticExt Ω CX hcX).G)).ker ≠ ⊥ := by
  rw [ker_toG']
  exact (arithmeticExt Ω CX hcX).nontrivial_delta

/-- `g₀` as an element of `G_K`. -/
def g₀G : (arithmeticExt Ω CX hcX).G := D.g₀ Ω hcX

lemma pr_eq_conj_toG' (x : (arithmeticExt Ω CX hcX).Pi) :
    (arithmeticExt Ω CX hcX).pr x = (D.g₀G Ω hcX)⁻¹ * D.toG' Ω hcX x * (D.g₀G Ω hcX)⁻¹⁻¹ := by
  have hk : projGk Ω CX hcX x = (D.g₀ Ω hcX)⁻¹ * (D.g₀ Ω hcX * projGk Ω CX hcX x *
      (D.g₀ Ω hcX)⁻¹) * (D.g₀ Ω hcX)⁻¹⁻¹ := by
    group
  exact hk.trans (congrArg (fun t ↦ (D.g₀G Ω hcX)⁻¹ * t * (D.g₀G Ω hcX)⁻¹⁻¹)
    (D.toG'_apply Ω hcX x)).symm

/-- `o₄ : Π_V ⇝ Π_X` of type `⋎`. -/
abbrev o₄ := ElemOp.ofQuot (D.A₅ Ω hcX) (D.φ₄ Ω hcX) (D.isOpen_range_φ₄ Ω hcX) (D.toG' Ω hcX)
  (D.htoG Ω hcX) (D.isOpen_range_toG' Ω hcX) (D.isSlim_ker_toG' Ω hcX) (D.ker_toG'_ne_bot Ω hcX)
  (D.φ₄_injective Ω hcX)

/-- **The Belyi path** `Π_X ⇝ Π_V ⇝ Π_Q ⇝ … ⇝ Π_P ⇝ Π_W ⇝ … ⇝ Π_V ⇝ Π_X`. -/
def path := OpPath.belyiPath (D.o₁ Ω hcX) (D.o₂ Ω hcX) (D.r₁ Ω hcX) (D.o₃ Ω hcX) (D.r₂ Ω hcX)
  (D.o₄ Ω hcX)

/-- **The Belyi chain is of type `⋏, ⋎, •^l, ⋏, •^r, ⋎`.** -/
theorem isBelyiType : (D.path Ω hcX).toPiChain.IsBelyiType D.l D.r := by
  have h := OpPath.isBelyiType_belyiPath (D.o₁ Ω hcX) (D.o₂ Ω hcX) (D.r₁ Ω hcX) (D.o₃ Ω hcX)
    (D.r₂ Ω hcX) (D.o₄ Ω hcX) rfl rfl
    (fun j hj ↦ (OpPath.kind_opN_pushRun _ _ _ _ _ _ _ _ _ j
      (by rwa [OpPath.length_pushRun] at hj) hj).trans rfl) rfl
    (fun j hj ↦ (OpPath.kind_opN_pushRun _ _ _ _ _ _ _ _ _ j
      (by rwa [OpPath.length_pushRun] at hj) hj).trans rfl) rfl
  rwa [OpPath.length_pushRun, OpPath.length_pushRun] at h

/-- **A terminal isomorphism of the Belyi chain to the trivial chain.** -/
def terminalIso :
    (D.path Ω hcX).toPiChain.TerminalIso (PiChain.trivial (arithmeticExt Ω CX hcX)) :=
  OpPath.terminalIso (D.path Ω hcX) (ContinuousMulEquiv.refl _) (D.g₀G Ω hcX)⁻¹
    (D.pr_eq_conj_toG' Ω hcX)

/-- **[AbsTopII] Corollary 3.7 (a), membership**: the candidates `Π_{UW_{r-m}} ↠ Π_V ↪ Π_X`
produced by the Belyi chain lie in `belyiCusp (arithmeticExt Ω CX hcX)`. -/
theorem belyiCandidate_mem (m : ℕ) (hm : m ≤ D.r) :
    PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm ∈
      belyiCusp (arithmeticExt Ω CX hcX) :=
  ⟨_, _, _, D.isBelyiType Ω hcX, D.terminalIso Ω hcX, m, hm, rfl⟩

end BelyiData

end CurvesJacobian.Cusp
