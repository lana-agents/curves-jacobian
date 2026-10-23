/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiArithChain
import CurvesJacobian.Cusp.OpPathRun
import Belyi.Anabelian.EllipticChain

/-!
# The elliptic chain of an affine hyperbolic curve over a number field (MR8)

[AbsTopII] Example 3.2 (ii) (`Topics in Absolute Anabelian Geometry II.txt` l.4381–4400) and
Corollary 3.3 (iii)(a) (l.4481–4491): the `Π`-chain
`X ⇝ V ⇝ D ⇝ U ⇝ U_n ⇝ … ⇝ U_1 = D ⇝ V ⇝ X* = X` of type `⋏, ⋎, ⋏, •, …, •, ⋏, ⋎` with a
terminal isomorphism to the trivial chain. This is the geometric counterpart of the
group-theoretic `Belyi.Anabelian.PiChain.ellipticCandidate`, parallel to the Belyi chain of
`CurvesJacobian.Cusp.BelyiArithChain` (all curves are affine hyperbolic curves).

`EllipticData CX` (over a number field `M ⊇ K`, `CX` over `K`) consists of
* hyperbolic curves `CQ = (Q̄, D)`, `CW = (W̄, U)` and `CV = (V̄, V)` over `M` with a cusp;
* a run of fillings `U = UW₀ ⊆ … ⊆ UW_n = D'` in `W̄`, one `M`-rational point at a time, all
  hyperbolic with a cusp (the hypotheses of `fillChain`);
* finite étale maps `FV : V ⟶ U_X` (over `Spec M ⟶ Spec K`), `FQ : V ⟶ D`, `β : U ⟶ D` (the
  `[N]` of Ex 3.2) and `FD : V ⟶ D'` (over `Spec M`), on the affine schemes `Spec Γ(·)`.

## Main definitions

* `Belyi.Anabelian.OpPath.ellipticPath`, `OpPath.isEllipticType_ellipticPath`: paths of type
  `⋏, ⋎, ⋏, •^n, ⋏, ⋎`;
* `EllipticData.path D`: `o₁ = ⋏ (Π_V ↪ Π_X)`, `o₂ = ⋎ (Π_V ↪ Π_D)`, `o₃ = ⋏ (Π_U ↪ Π_D)`, the
  run of `•`'s of `U ⊆ … ⊆ D'` pushed to `Π_X`, `o₅ = ⋏ (Π_V ↪ Π_{D'})`, `o₆ = ⋎ (Π_V ↪ Π_X)`;
* `EllipticData.isEllipticType`, `EllipticData.terminalIso`;
* **`EllipticData.ellipticCandidate_mem`**: the resulting candidate lies in `ellipticCusp`;
* **`EllipticData.ellipticCandidate_spec`**: it is `Π_U ↠ Π_{D'} ↩ Π_V ↪ Π_X`, with the map
  induced by `U ⊆ D'` (`stepHom`), by `FD` (`φ₅`) and by `FV` (`φ₁`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve Pi1.Profinite

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Belyi.Anabelian

namespace ElemOp

variable {E : CuspidalExt.{u}}

/-- `coverHom` along equalities of objects and a heterogeneous equality of operations. -/
lemma coverHom_heq₂ {A B A' B' : ChainObj E} (o : ElemOp A B) (o' : ElemOp A' B') (hA : A = A')
    (hB : B = B') (h : HEq o o') (k : o.kind = .cover) (k' : o'.kind = .cover) (x : B.grp) :
    ChainObj.equivOfEq hA (o.coverHom k x) = o'.coverHom k' (ChainObj.equivOfEq hB x) := by
  subst hA hB
  obtain rfl := eq_of_heq h
  rfl

end ElemOp

namespace OpPath

variable {E : CuspidalExt.{u}}

/-- **The elliptic path** `⋏, ⋎, ⋏, (run), ⋏, ⋎` ([AbsTopII] Example 3.2 (ii)). -/
def ellipticPath {A₁ A₂ A₃ A₄ A₅ A₆ : ChainObj E} (o₁ : ElemOp (ChainObj.base E) A₁)
    (o₂ : ElemOp A₁ A₂) (o₃ : ElemOp A₂ A₃) (r : OpPath A₃ A₄) (o₅ : ElemOp A₄ A₅)
    (o₆ : ElemOp A₅ A₆) : OpPath (ChainObj.base E) A₆ :=
  cons o₁ (cons o₂ (cons o₃ (r.append (cons o₅ (single o₆)))))

variable {A₁ A₂ A₃ A₄ A₅ A₆ : ChainObj E} (o₁ : ElemOp (ChainObj.base E) A₁)
  (o₂ : ElemOp A₁ A₂) (o₃ : ElemOp A₂ A₃) (r : OpPath A₃ A₄) (o₅ : ElemOp A₄ A₅)
  (o₆ : ElemOp A₅ A₆)

lemma length_ellipticPath : (ellipticPath o₁ o₂ o₃ r o₅ o₆).length = r.length + 5 := by
  simp only [ellipticPath, length, length_append, length_single]

/-- The `Π`-chain of an elliptic path is of elliptic type. -/
theorem isEllipticType_ellipticPath (h₁ : o₁.kind = .cover) (h₂ : o₂.kind = .quot)
    (h₃ : o₃.kind = .cover) (hr : ∀ j (h : j < r.length), (r.opN j h).kind = .decusp)
    (h₅ : o₅.kind = .cover) (h₆ : o₆.kind = .quot) :
    (ellipticPath o₁ o₂ o₃ r o₅ o₆).toPiChain.IsEllipticType r.length := by
  have hlen := length_ellipticPath o₁ o₂ o₃ r o₅ o₆
  have hlen' : (ellipticPath o₁ o₂ o₃ r o₅ o₆).toPiChain.len = r.length + 5 := hlen
  have k3 : ∀ n (hn : n + 3 < (ellipticPath o₁ o₂ o₃ r o₅ o₆).toPiChain.len)
      (hn' : n < (r.append (cons o₅ (single o₆))).length),
      ((ellipticPath o₁ o₂ o₃ r o₅ o₆).toPiChain.opN (n + 3) hn).kind =
        ((r.append (cons o₅ (single o₆))).opN n hn').kind :=
    fun _ _ _ ↦ rfl
  have hTlen : (r.append (cons o₅ (single o₆))).length = r.length + 2 := by
    simp only [length, length_append, length_single]
  refine ⟨hlen, h₁, h₂, h₃, fun s hs ↦ ?_, ?_, ?_⟩
  · rw [PiChain.kind_opN_congr _ (show 3 + s = s + 3 by omega) _ (by omega),
      k3 s _ (by omega)]
    exact (kind_opN_append_left _ _ s hs _).trans (hr s hs)
  · rw [k3 _ _ (by omega)]
    exact (kind_opN_append_right' r _ 0 r.length (by omega)
      (by simp only [length]; omega) _).trans h₅
  · rw [PiChain.kind_opN_congr _ (show r.length + 4 = (r.length + 1) + 3 by omega) _ (by omega),
      k3 _ _ (by omega)]
    exact (kind_opN_append_right' r _ 1 (r.length + 1) (by omega)
      (by simp only [length, length_single]; omega) _).trans
      ((kind_opN_cons o₅ (single o₆) 0 1 rfl (by rw [length_single]; omega) _).trans h₆)

/-- The objects of the run of an elliptic path. -/
theorem objN_ellipticPath (k : ℕ) (hk : k ≤ r.length) :
    (ellipticPath o₁ o₂ o₃ r o₅ o₆).objN (3 + k) = r.objN k := by
  rw [show 3 + k = k + 1 + 1 + 1 by omega]
  change (r.append (cons o₅ (single o₆))).objN k = _
  exact objN_append_left r _ k hk

/-- The operations of the run of an elliptic path. -/
theorem opN_ellipticPath_heq (k : ℕ) (hk : k < r.length)
    (h' : 3 + k < (ellipticPath o₁ o₂ o₃ r o₅ o₆).length) :
    HEq ((ellipticPath o₁ o₂ o₃ r o₅ o₆).opN (3 + k) h') (r.opN k hk) := by
  have e : 3 + k = k + 1 + 1 + 1 := by omega
  refine (opN_congr_heq _ e h' (by rw [← e]; exact h')).trans ?_
  change HEq ((r.append (cons o₅ (single o₆))).opN k _) _
  exact opN_append_left_heq r _ k hk _

/-- The third to last object of an elliptic path (`Π_D`). -/
theorem objN_ellipticPath_D : (ellipticPath o₁ o₂ o₃ r o₅ o₆).objN (r.length + 3) = A₄ := by
  rw [show r.length + 3 = 3 + r.length by omega,
    objN_ellipticPath o₁ o₂ o₃ r o₅ o₆ r.length le_rfl]
  exact objN_length r

/-- The second to last object of an elliptic path (`Π_V`). -/
theorem objN_ellipticPath_V : (ellipticPath o₁ o₂ o₃ r o₅ o₆).objN (r.length + 4) = A₅ := by
  rw [show r.length + 4 = (r.length + 1) + 1 + 1 + 1 by omega]
  change (r.append (cons o₅ (single o₆))).objN (r.length + 1) = _
  rw [objN_append_right]
  rfl

/-- The operation `⋏` before the last of an elliptic path. -/
theorem opN_ellipticPath_D_heq (h' : r.length + 3 < (ellipticPath o₁ o₂ o₃ r o₅ o₆).length) :
    HEq ((ellipticPath o₁ o₂ o₃ r o₅ o₆).opN (r.length + 3) h') o₅ := by
  have e : r.length + 3 = (r.length + 0) + 1 + 1 + 1 := by omega
  refine (opN_congr_heq _ e h' (by rw [← e]; exact h')).trans ?_
  change HEq ((r.append (cons o₅ (single o₆))).opN (r.length + 0) _) _
  exact opN_append_right_heq r _ 0 (by simp only [length]; omega) _

/-- The last operation of an elliptic path. -/
theorem opN_ellipticPath_V_heq (h' : r.length + 4 < (ellipticPath o₁ o₂ o₃ r o₅ o₆).length) :
    HEq ((ellipticPath o₁ o₂ o₃ r o₅ o₆).opN (r.length + 4) h') o₆ := by
  have e : r.length + 4 = (r.length + 1) + 1 + 1 + 1 := by omega
  refine (opN_congr_heq _ e h' (by rw [← e]; exact h')).trans ?_
  change HEq ((r.append (cons o₅ (single o₆))).opN (r.length + 1) _) _
  exact (opN_append_right_heq r _ 1 (by simp only [length, length_single]; omega) _).trans
    HEq.rfl

end OpPath

end Belyi.Anabelian

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M]

/-- **Elliptic data** for an affine hyperbolic curve `CX` over `K` ([AbsTopII] Example 3.2 (ii)):
curves `CQ = (Q̄, D)`, `CW = (W̄, U)`, `CV = (V̄, V)` over a number field `M ⊇ K`, a run of
fillings `U ⊆ … ⊆ D'` in `W̄` (one rational point at a time, all hyperbolic with a cusp) and
finite étale maps `V ⟶ U_X`, `V ⟶ D`, `β : U ⟶ D`, `V ⟶ D'`. -/
structure EllipticData (CX : HypCurve K) where
  /-- The curve `(Q̄, D)`. -/
  CQ : HypCurve M
  hcQ : (CQ.U : Set CQ.Xbar)ᶜ.Nonempty
  /-- The curve `(W̄, U)`. -/
  CW : HypCurve M
  hcW : (CW.U : Set CW.Xbar)ᶜ.Nonempty
  /-- The number of fillings `U ⇝ D'`. -/
  n : ℕ
  UW : Fin (n + 1) → CW.Xbar.Opens
  hUW0 : UW 0 = CW.U
  hleW : ∀ i, CW.U ≤ UW i
  hmonoW : ∀ i : Fin n, UW i.castSucc ≤ UW i.succ
  hcUW : ∀ i, (UW i : Set CW.Xbar)ᶜ.Nonempty
  hypW : ∀ i, haveI := IsCurveOver.isIntegral M CW.Xbar
    2 < 2 * Anabelian.curveGenus M CW.Xbar + cuspDegree M CW.Xbar (UW i)
  xW : Fin n → CW.Xbar
  hxUW : ∀ i, xW i ∈ UW i.succ
  hxUW' : ∀ i, xW i ∉ UW i.castSucc
  hxW : ∀ i, (UW i.succ : Set CW.Xbar) \ UW i.castSucc ⊆ {xW i}
  /-- The filled points are `M`-rational (operations of type `•` fill rational cusps). -/
  ratW : ∀ i, IsIso ((CW.Xbar ↘ Spec (.of M)).residueFieldMap (xW i))
  /-- The curve `(V̄, V)`. -/
  CV : HypCurve M
  hcV : (CV.U : Set CV.Xbar)ᶜ.Nonempty
  /-- `V ⟶ U_X`. -/
  FV : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CX.Xbar, CX.U)
  [finFV : IsFiniteEtale FV]
  hFV : FV ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K M))
  /-- `V ⟶ D`. -/
  FQ : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CQ.Xbar, CQ.U)
  [finFQ : IsFiniteEtale FQ]
  hFQ : FQ ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(CQ.Xbar, CQ.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M M))
  /-- `β : U ⟶ D` (the `[N]` of [AbsTopII] Example 3.2). -/
  β : Spec Γ(CW.Xbar, CW.U) ⟶ Spec Γ(CQ.Xbar, CQ.U)
  [finβ : IsFiniteEtale β]
  hβ : β ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(CQ.Xbar, CQ.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CW.Xbar, CW.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M M))
  /-- `V ⟶ D'`. -/
  FD : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CW.Xbar, UW (Fin.last n))
  [finFD : IsFiniteEtale FD]
  hFD : FD ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(CW.Xbar, UW (Fin.last n)))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M M))

attribute [instance] EllipticData.finFV EllipticData.finFQ EllipticData.finβ EllipticData.finFD

namespace EllipticData

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [Algebra M Ω] [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]
  {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (D : EllipticData (M := M) CX)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-! ### The curve `D'` and the maps of fundamental groups -/

/-- The curve `(W̄, D')`. -/
abbrev CDp : HypCurve M := fillCurve D.CW (D.hleW (Fin.last D.n)) (D.hypW (Fin.last D.n))

lemma hcDp : ((D.CDp).U : Set (D.CDp).Xbar)ᶜ.Nonempty := D.hcUW (Fin.last D.n)

/-- `φ₁ : Π_V ↪ Π_X`. -/
abbrev φ₁ : (arithmeticExt Ω D.CV D.hcV).Pi →ₜ* (arithmeticExt Ω CX hcX).Pi :=
  coverPiHom Ω CX hcX D.CV D.hcV D.FV

/-- `j₂ : Π_V ↪ Π_D`. -/
abbrev j₂ : (arithmeticExt Ω D.CV D.hcV).Pi →ₜ* (arithmeticExt Ω D.CQ D.hcQ).Pi :=
  coverPiHom Ω D.CQ D.hcQ D.CV D.hcV D.FQ

/-- `jβ : Π_U ↪ Π_D`. -/
abbrev jβ : (arithmeticExt Ω D.CW D.hcW).Pi →ₜ* (arithmeticExt Ω D.CQ D.hcQ).Pi :=
  coverPiHom Ω D.CQ D.hcQ D.CW D.hcW D.β

/-- `Π_V ↪ Π_{D'}` (at the base point of `D'`). -/
abbrev jD : (arithmeticExt Ω D.CV D.hcV).Pi →ₜ* (arithmeticExt Ω D.CDp D.hcDp).Pi :=
  coverPiHom Ω D.CDp D.hcDp D.CV D.hcV D.FD

/-- The change of base point of `D'` to the base point of the run of fillings of `U`. -/
abbrev TW := fillTransport Ω D.CW D.hcW (D.hleW (Fin.last D.n)) (D.hcUW (Fin.last D.n))
  (D.hypW (Fin.last D.n))

/-- `φ₅ : Π_V ↪ Π_{D'}` (at the base point of the run of fillings of `U`). -/
abbrev φ₅ := (ContinuousMonoidHom.toContinuousMonoidHom (D.TW Ω)).comp (D.jD Ω)

lemma φ₁_injective : Function.Injective (D.φ₁ Ω hcX) := coverPiHom_injective _ _ _ _ _ _

lemma isOpen_range_φ₁ : IsOpen (Set.range (D.φ₁ Ω hcX)) := isOpen_range_coverPiHom _ _ _ _ _ _

lemma j₂_injective : Function.Injective (D.j₂ Ω) := coverPiHom_injective _ _ _ _ _ _

lemma isOpen_range_j₂ : IsOpen (Set.range (D.j₂ Ω)) := isOpen_range_coverPiHom _ _ _ _ _ _

lemma jβ_injective : Function.Injective (D.jβ Ω) := coverPiHom_injective _ _ _ _ _ _

lemma isOpen_range_jβ : IsOpen (Set.range (D.jβ Ω)) := isOpen_range_coverPiHom _ _ _ _ _ _

lemma φ₅_injective : Function.Injective (D.φ₅ Ω) :=
  (D.TW Ω).injective.comp (coverPiHom_injective _ _ _ _ _ _)

lemma isOpen_range_φ₅ : IsOpen (Set.range (D.φ₅ Ω)) := by
  rw [ContinuousMonoidHom.coe_comp, Set.range_comp]
  exact (D.TW Ω).toHomeomorph.isOpenMap _ (isOpen_range_coverPiHom _ _ _ _ _ _)

/-! ### The Galois groups -/

local notation "GM" => π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap M Ω)))
local notation "GK" => π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω)))

/-- `G_M ↪ G_K` for `V ⟶ U_X`. -/
abbrev ιV : GM →ₜ* GK := coverι Ω CX hcX D.CV D.hcV D.FV D.hFV

/-- The conjugating element of `V ⟶ U_X`. -/
def gV : GK := coverG Ω CX hcX D.CV D.hcV D.FV D.hFV

lemma ιV_apply (y : GM) : D.ιV Ω hcX y = D.gV Ω hcX * galoisMap K M Ω y * (D.gV Ω hcX)⁻¹ :=
  autContinuousMulEquivOfIso_self _ _

/-- The conjugating element of `V ⟶ D`. -/
def gQ : GM := coverG Ω D.CQ D.hcQ D.CV D.hcV D.FQ D.hFQ

lemma coverιQ_apply (y : GM) :
    coverι Ω D.CQ D.hcQ D.CV D.hcV D.FQ D.hFQ y = D.gQ Ω * y * (D.gQ Ω)⁻¹ := by
  change autContinuousMulEquivOfIso (D.gQ Ω) (galoisMap M M Ω y) = _
  rw [autContinuousMulEquivOfIso_self, galoisMap_self]

/-- `ι_Q : G_M → G_K` for `D`: `ι_V ∘ conj(g_Q⁻¹)`. -/
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

/-- The conjugating element of `β`. -/
def gβ : GM := coverG Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ

lemma coverιβ_apply (y : GM) :
    coverι Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ y = D.gβ Ω * y * (D.gβ Ω)⁻¹ := by
  change autContinuousMulEquivOfIso (D.gβ Ω) (galoisMap M M Ω y) = _
  rw [autContinuousMulEquivOfIso_self, galoisMap_self]

/-- `ι_W : G_M → G_K` for the run of fillings of `U`: `ι_Q ∘ ι_β`. -/
def ιW : GM →ₜ* GK := (D.ιQ Ω hcX).comp (coverι Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ)

/-- `ι_W` is `ι_V` up to conjugation by `g_Q⁻¹ g_β`. -/
lemma ιW_apply (y : GM) : D.ιW Ω hcX y =
    D.ιV Ω hcX ((D.gQ Ω)⁻¹ * D.gβ Ω * y * ((D.gQ Ω)⁻¹ * D.gβ Ω)⁻¹) := by
  have e : (D.gQ Ω)⁻¹ * (D.gβ Ω * y * (D.gβ Ω)⁻¹) * (D.gQ Ω)⁻¹⁻¹ =
      (D.gQ Ω)⁻¹ * D.gβ Ω * y * ((D.gQ Ω)⁻¹ * D.gβ Ω)⁻¹ := by
    group
  have e0 : D.ιW Ω hcX y = D.ιQ Ω hcX (D.gβ Ω * y * (D.gβ Ω)⁻¹) := by
    change D.ιQ Ω hcX (coverι Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ y) = _
    rw [coverιβ_apply]
  exact e0.trans ((D.ιQ_apply Ω hcX _).trans (congrArg (D.ιV Ω hcX) e))

lemma ιW_injective : Function.Injective (D.ιW Ω hcX) :=
  (D.ιQ_injective Ω hcX).comp (coverι_injective Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ)

lemma isOpen_range_ιW : IsOpen (Set.range (D.ιW Ω hcX)) := by
  let f : GM →ₜ* GM := coverι Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ
  have hf : IsOpen (Set.range f) := isOpen_range_coverι Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ
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

/-- The run of fillings `U ⊆ … ⊆ D'`. -/
abbrev cW : PiChain (arithmeticExt Ω D.CW D.hcW) :=
  fillChain Ω D.CW D.hcW D.n D.UW D.hUW0 D.hleW D.hmonoW D.hcUW D.hypW D.xW D.hxUW D.hxUW' D.hxW
    D.ratW

/-- `A₃ = Π_D` (the trivial object of `D`, pushed to `X`). -/
abbrev A₃ : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₁ Ω hcX).push (D.j₂ Ω) (D.isOpen_range_j₂ Ω) (D.ιQ Ω hcX) (D.ιQ_injective Ω hcX)
    (D.isOpen_range_ιQ Ω hcX) (D.hcompQ Ω hcX) (ChainObj.base (arithmeticExt Ω D.CQ D.hcQ))

lemma hcompW (x : (arithmeticExt Ω D.CW D.hcW).Pi) :
    D.ιW Ω hcX ((arithmeticExt Ω D.CW D.hcW).pr x) = (D.A₃ Ω hcX).toG (D.jβ Ω x) :=
  congrArg (D.ιQ Ω hcX) (pr_coverPiHom Ω D.CQ D.hcQ D.CW D.hcW D.β D.hβ x).symm

/-- `A₄ = Π_U`, the target of `⋏ : Π_D ⇝ Π_U` before pushing. -/
abbrev A₄ : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₃ Ω hcX).coverObj (D.jβ Ω) (D.jβ_injective Ω) (D.isOpen_range_jβ Ω)

/-- **Matching of the cusps of `D` with those of `X`** (through `V`). -/
theorem cuspMatchQ : (D.A₁ Ω hcX).CuspMatch (E' := arithmeticExt Ω D.CQ D.hcQ) (D.j₂ Ω) := by
  refine ChainObj.cuspMatch_of_commensurable (arithCusps Ω D.CV D.hcV) (fun J hJ ↦ ?_)
    fun I' hI' ↦ ?_
  · obtain ⟨I, hI, hle, hidx⟩ := exists_arithCusps_map_coverPiHom Ω CX hcX D.CV D.hcV D.FV hJ
    refine ⟨I, hI, ?_⟩
    rw [ChainObj.image_coverObj, ChainObj.image_base]
    exact Subgroup.commensurable_comap_of_map_le (D.φ₁_injective Ω hcX) hle hidx
  · obtain ⟨J, hJ, hle, hidx⟩ := exists_arithCusps_coverHom_le Ω D.CQ D.hcQ D.CV D.hcV D.FQ hI'
    exact ⟨J, hJ, Subgroup.commensurable_of_le hle hidx⟩

set_option quotPrecheck false in
local notation "Φ₁" => (EllipticData.φ₁ Ω hcX D :
  (arithmeticExt Ω (EllipticData.CV D) (EllipticData.hcV D)).Pi →* (arithmeticExt Ω CX hcX).Pi)
set_option quotPrecheck false in
local notation "J₂" => (EllipticData.j₂ Ω D :
  (arithmeticExt Ω (EllipticData.CV D) (EllipticData.hcV D)).Pi →*
    (arithmeticExt Ω D.CQ D.hcQ).Pi)
set_option quotPrecheck false in
local notation "Jβ" => (EllipticData.jβ Ω D :
  (arithmeticExt Ω D.CW D.hcW).Pi →* (arithmeticExt Ω D.CQ D.hcQ).Pi)

/-- **Matching of the cusps of `U` with those of `X`** (through `D`, `V`). -/
theorem cuspMatchW : (D.A₄ Ω hcX).CuspMatch (E' := arithmeticExt Ω D.CW D.hcW)
    (ContinuousMonoidHom.id _) := by
  refine ChainObj.cuspMatch_of_commensurable (arithCusps Ω D.CW D.hcW) (fun J hJ ↦ ?_)
    fun I' hI' ↦ ⟨I', hI', ?_⟩
  · obtain ⟨IQ, hIQ, hle1, hidx1⟩ :=
      exists_arithCusps_map_coverPiHom Ω D.CQ D.hcQ D.CW D.hcW D.β hJ
    obtain ⟨JV, hJV, hle2, hidx2⟩ :=
      exists_arithCusps_coverHom_le Ω D.CQ D.hcQ D.CV D.hcV D.FQ hIQ
    obtain ⟨I, hI, hle3, hidx3⟩ := exists_arithCusps_map_coverPiHom Ω CX hcX D.CV D.hcV D.FV hJV
    refine ⟨I, hI, ?_⟩
    have h1 : (D.A₁ Ω hcX).image I = I.comap Φ₁ :=
      ChainObj.image_coverObj_base (D.φ₁ Ω hcX) (D.φ₁_injective Ω hcX)
        (D.isOpen_range_φ₁ Ω hcX) I
    have hA : (D.A₃ Ω hcX).image I = (ChainObj.base (arithmeticExt Ω D.CQ D.hcQ)).image
        (((D.A₁ Ω hcX).image I).map J₂) :=
      ChainObj.image_push (D.A₁ Ω hcX) (D.j₂ Ω) (D.isOpen_range_j₂ Ω) (D.ιQ Ω hcX)
        (D.ιQ_injective Ω hcX) (D.isOpen_range_ιQ Ω hcX) (D.hcompQ Ω hcX)
        (ChainObj.base (arithmeticExt Ω D.CQ D.hcQ)) I
    have h2 : (D.A₃ Ω hcX).image I = (I.comap Φ₁).map J₂ := by
      rw [hA, ChainObj.image_base, h1]
    have hC := ChainObj.image_coverObj (D.A₃ Ω hcX) (D.jβ Ω) (D.jβ_injective Ω)
      (D.isOpen_range_jβ Ω) I
    rw [hC, h2]
    have c1 := Subgroup.commensurable_comap_of_map_le (D.φ₁_injective Ω hcX) hle3 hidx3
    have c2 := Subgroup.commensurable_of_le hle2 hidx2
    have c3 : ((I.comap Φ₁).map J₂).Commensurable IQ :=
      (Subgroup.Commensurable.map' J₂ c1).symm.trans c2
    have c5 := Subgroup.Commensurable.comap' Jβ c3
    exact (Subgroup.commensurable_comap_of_map_le (coverPiHom_injective _ _ _ _ _ _) hle1
      hidx1).trans c5.symm
  · have e : I'.map ((ContinuousMonoidHom.id (arithmeticExt Ω D.CW D.hcW).Pi : _ →ₜ* _) :
        _ →* _) = I' := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨y, hy, rfl⟩
    exact (congrArg (fun T ↦ T.Commensurable I') e).mpr (.refl I')

lemma rhoTop_injective_base :
    Function.Injective ((ChainObj.base (arithmeticExt Ω D.CQ D.hcQ)).rhoTop fun _ ↦ trivial) :=
  fun _ _ h ↦ h

/-- `ρ` of the first object of the run of fillings is bijective (`UW₀ = U`). -/
lemma rhoTop_bijective_cW :
    Function.Bijective (((D.cW Ω).obj ⟨0, Nat.succ_pos _⟩).rhoTop fun _ ↦ trivial) :=
  fillMap_bijective_of_eq Ω D.CW D.hcW (D.hleW 0) D.hUW0

/-- `o₁ : Π_X ⇝ Π_V` of type `⋏`. -/
abbrev o₁ := ElemOp.ofCover (ChainObj.base (arithmeticExt Ω CX hcX)) (D.φ₁ Ω hcX)
  (D.φ₁_injective Ω hcX) (D.isOpen_range_φ₁ Ω hcX)

/-- `o₂ : Π_V ⇝ Π_D` of type `⋎`. -/
abbrev o₂ := ElemOp.toPush (D.A₁ Ω hcX) (D.j₂ Ω) (D.isOpen_range_j₂ Ω) (D.ιQ Ω hcX)
  (D.ιQ_injective Ω hcX) (D.isOpen_range_ιQ Ω hcX) (D.hcompQ Ω hcX)
  (ChainObj.base (arithmeticExt Ω D.CQ D.hcQ)) (fun _ ↦ trivial) (D.j₂_injective Ω)
  (D.rhoTop_injective_base Ω)

/-- `o₃ : Π_D ⇝ Π_U` of type `⋏`. -/
abbrev o₃ := ElemOp.coverPush (D.A₃ Ω hcX) (D.jβ Ω) (D.jβ_injective Ω) (D.isOpen_range_jβ Ω)
  (D.ιW Ω hcX) (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX)
  ((D.cW Ω).obj ⟨0, Nat.succ_pos _⟩) (fun _ ↦ trivial) (D.rhoTop_bijective_cW Ω)

/-- The run `Π_U ⇝ … ⇝ Π_{D'}` of `•`'s. -/
abbrev rW := OpPath.pushRun (D.A₄ Ω hcX) (ContinuousMonoidHom.id _)
  (ElemOp.isOpen_range_id (E' := arithmeticExt Ω D.CW D.hcW)) (D.ιW Ω hcX)
  (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX) (D.cuspMatchW Ω hcX) (D.cW Ω)

/-- The pushed objects of the run of fillings of `U`. -/
abbrev Fobj (i : Fin (D.n + 1)) : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₄ Ω hcX).push (E' := arithmeticExt Ω D.CW D.hcW) (ContinuousMonoidHom.id _)
    (ElemOp.isOpen_range_id (E' := arithmeticExt Ω D.CW D.hcW)) (D.ιW Ω hcX)
    (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX) ((D.cW Ω).obj i)

/-- `A₅ = Π_{D'}` at the end of the pushed run of fillings of `U`. -/
abbrev A₅ : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₄ Ω hcX).push (E' := arithmeticExt Ω D.CW D.hcW) (ContinuousMonoidHom.id _)
    (ElemOp.isOpen_range_id (E' := arithmeticExt Ω D.CW D.hcW)) (D.ιW Ω hcX)
    (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX)
    ((D.cW Ω).obj ⟨(D.cW Ω).len, Nat.lt_succ_self _⟩)

/-- `o₅ : Π_{D'} ⇝ Π_V` of type `⋏`. -/
abbrev o₅ := ElemOp.ofCover (D.A₅ Ω hcX) (D.φ₅ Ω) (D.φ₅_injective Ω) (D.isOpen_range_φ₅ Ω)

/-- `A₆ = Π_V` (after `⋏`). -/
abbrev A₆ : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₅ Ω hcX).coverObj (D.φ₅ Ω) (D.φ₅_injective Ω) (D.isOpen_range_φ₅ Ω)

/-- The conjugating element of `V ⟶ D'`. -/
def gD : GM := coverG Ω D.CDp D.hcDp D.CV D.hcV D.FD D.hFD

lemma coverιD_apply (y : GM) :
    coverι Ω D.CDp D.hcDp D.CV D.hcV D.FD D.hFD y = D.gD Ω * y * (D.gD Ω)⁻¹ := by
  change autContinuousMulEquivOfIso (D.gD Ω) (galoisMap M M Ω y) = _
  rw [autContinuousMulEquivOfIso_self, galoisMap_self]

/-- The conjugating element of `fillTransport` for `D'`. -/
def g₂ : GM := fillG Ω D.CW D.hcW (D.hleW (Fin.last D.n)) (D.hcUW (Fin.last D.n))
  (D.hypW (Fin.last D.n))

/-- The element `ι_V(w)` conjugating the last projection. -/
def g₀ : GK := D.ιV Ω hcX ((D.gQ Ω)⁻¹ * D.gβ Ω * D.g₂ Ω * D.gD Ω)

/-- The projection `Π_X → G_K` of the last object: `conj(g₀) ∘ pr`. -/
def toG' : (arithmeticExt Ω CX hcX).Pi →ₜ* (arithmeticExt Ω CX hcX).G :=
  (ContinuousMonoidHom.toContinuousMonoidHom (autContinuousMulEquivOfIso (D.g₀ Ω hcX))).comp
    (projGk Ω CX hcX)

lemma toG'_apply (x : (arithmeticExt Ω CX hcX).Pi) : D.toG' Ω hcX x =
    D.g₀ Ω hcX * projGk Ω CX hcX x * (D.g₀ Ω hcX)⁻¹ :=
  autContinuousMulEquivOfIso_self _ _

lemma htoG (x : (D.A₆ Ω hcX).grp) : D.toG' Ω hcX (D.φ₁ Ω hcX x) = (D.A₆ Ω hcX).toG x := by
  have e1 : D.toG' Ω hcX (D.φ₁ Ω hcX x) =
      D.g₀ Ω hcX * D.ιV Ω hcX (projGk Ω D.CV D.hcV x) * (D.g₀ Ω hcX)⁻¹ :=
    (D.toG'_apply Ω hcX _).trans (congrArg (fun t ↦ D.g₀ Ω hcX * t * (D.g₀ Ω hcX)⁻¹)
      (pr_coverPiHom Ω CX hcX D.CV D.hcV D.FV D.hFV x))
  have e2 : ∀ p : GM, D.g₀ Ω hcX * D.ιV Ω hcX p * (D.g₀ Ω hcX)⁻¹ =
      D.ιV Ω hcX ((D.gQ Ω)⁻¹ * D.gβ Ω * D.g₂ Ω * D.gD Ω * p *
        ((D.gQ Ω)⁻¹ * D.gβ Ω * D.g₂ Ω * D.gD Ω)⁻¹) := fun p ↦ by
    rw [g₀]
    simp only [map_mul, map_inv]
  have e3 : ∀ p : GM, (D.gQ Ω)⁻¹ * D.gβ Ω * D.g₂ Ω * D.gD Ω * p *
        ((D.gQ Ω)⁻¹ * D.gβ Ω * D.g₂ Ω * D.gD Ω)⁻¹ =
      (D.gQ Ω)⁻¹ * D.gβ Ω * (D.g₂ Ω * (D.gD Ω * p * (D.gD Ω)⁻¹) * (D.g₂ Ω)⁻¹) *
        ((D.gQ Ω)⁻¹ * D.gβ Ω)⁻¹ := fun p ↦ by
    group
  have hD : projGk Ω D.CDp D.hcDp (D.jD Ω x) = D.gD Ω * projGk Ω D.CV D.hcV x * (D.gD Ω)⁻¹ :=
    (pr_coverPiHom Ω D.CDp D.hcDp D.CV D.hcV D.FD D.hFD x).trans (D.coverιD_apply Ω _)
  have e4 : projGkFill Ω D.CW D.hcW (D.hleW (Fin.last D.n)) (D.TW Ω (D.jD Ω x)) =
      D.g₂ Ω * (D.gD Ω * projGk Ω D.CV D.hcV x * (D.gD Ω)⁻¹) * (D.g₂ Ω)⁻¹ :=
    (projGkFill_fillTransport Ω D.CW D.hcW (D.hleW (Fin.last D.n)) (D.hcUW (Fin.last D.n))
      (D.hypW (Fin.last D.n)) (D.jD Ω x)).trans
      (congrArg (fun t ↦ D.g₂ Ω * t * (D.g₂ Ω)⁻¹) hD)
  have e5 : (D.A₆ Ω hcX).toG x = D.ιW Ω hcX
      (projGkFill Ω D.CW D.hcW (D.hleW (Fin.last D.n)) (D.TW Ω (D.jD Ω x))) := rfl
  exact e1.trans ((e2 _).trans ((congrArg (D.ιV Ω hcX) (e3 _)).trans
    ((D.ιW_apply Ω hcX _).symm.trans ((congrArg (D.ιW Ω hcX) e4).symm.trans e5.symm))))

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

/-- `o₆ : Π_V ⇝ Π_X` of type `⋎`. -/
abbrev o₆ := ElemOp.ofQuot (D.A₆ Ω hcX) (D.φ₁ Ω hcX) (D.isOpen_range_φ₁ Ω hcX) (D.toG' Ω hcX)
  (D.htoG Ω hcX) (D.isOpen_range_toG' Ω hcX) (D.isSlim_ker_toG' Ω hcX) (D.ker_toG'_ne_bot Ω hcX)
  (D.φ₁_injective Ω hcX)

/-- **The elliptic path** `Π_X ⇝ Π_V ⇝ Π_D ⇝ Π_U ⇝ … ⇝ Π_{D'} ⇝ Π_V ⇝ Π_X`. -/
def path := OpPath.ellipticPath (D.o₁ Ω hcX) (D.o₂ Ω hcX) (D.o₃ Ω hcX) (D.rW Ω hcX) (D.o₅ Ω hcX)
  (D.o₆ Ω hcX)

/-- **The elliptic chain is of type `⋏, ⋎, ⋏, •^n, ⋏, ⋎`.** -/
theorem isEllipticType : (D.path Ω hcX).toPiChain.IsEllipticType D.n := by
  have h := OpPath.isEllipticType_ellipticPath (D.o₁ Ω hcX) (D.o₂ Ω hcX) (D.o₃ Ω hcX)
    (D.rW Ω hcX) (D.o₅ Ω hcX) (D.o₆ Ω hcX) rfl rfl rfl
    (fun j hj ↦ (OpPath.kind_opN_pushRun _ _ _ _ _ _ _ _ _ j
      (by rwa [OpPath.length_pushRun] at hj) hj).trans rfl) rfl rfl
  rwa [OpPath.length_pushRun] at h

/-- **A terminal isomorphism of the elliptic chain to the trivial chain.** -/
def terminalIso :
    (D.path Ω hcX).toPiChain.TerminalIso (PiChain.trivial (arithmeticExt Ω CX hcX)) :=
  OpPath.terminalIso (D.path Ω hcX) (ContinuousMulEquiv.refl _) (D.g₀G Ω hcX)⁻¹
    (D.pr_eq_conj_toG' Ω hcX)

/-- **[AbsTopII] Corollary 3.3 (iii)(a), membership**: the candidate `Π_U ↠ Π_{D'} ↩ Π_V ↪ Π_X`
produced by the elliptic chain lies in `ellipticCusp (arithmeticExt Ω CX hcX)`. -/
theorem ellipticCandidate_mem :
    PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX) ∈
      ellipticCusp (arithmeticExt Ω CX hcX) :=
  ⟨_, _, D.isEllipticType Ω hcX, D.terminalIso Ω hcX, rfl⟩

/-! ### The specification of the candidate -/

lemma monoW : Monotone D.UW := Fin.monotone_iff_le_succ.2 D.hmonoW

/-- **`Π_{U_i} → Π_{U_j}`** for `i ≤ j` along the run of fillings `U ⊆ … ⊆ D'` (at the base
points `fillPoint`), induced by `Spec Γ(U_i) ⟶ Spec Γ(U_j)`. -/
def stepHom (i j : Fin (D.n + 1)) (hij : i ≤ j) :
    π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫ baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)) →ₜ*
      π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW j) ≫ baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW j)) :=
  fillStepMap Ω D.CW D.hcW (D.hleW i) (D.monoW hij)

lemma stepHom_self (i : Fin (D.n + 1)) (y) : D.stepHom Ω i i le_rfl y = y := by
  obtain ⟨γ, rfl⟩ := fillMap_surjective Ω D.CW D.hcW (D.hleW i) (D.hcUW i) y
  exact fillStepMap_fillMap Ω D.CW D.hcW (D.hleW i) (D.monoW le_rfl) γ

lemma stepHom_comp (i j k : Fin (D.n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (y) :
    D.stepHom Ω j k hjk (D.stepHom Ω i j hij y) = D.stepHom Ω i k (hij.trans hjk) y := by
  obtain ⟨γ, rfl⟩ := fillMap_surjective Ω D.CW D.hcW (D.hleW i) (D.hcUW i) y
  have e1 := fillStepMap_fillMap Ω D.CW D.hcW (D.hleW i) (D.monoW hij) γ
  have e2 := fillStepMap_fillMap Ω D.CW D.hcW (D.hleW j) (D.monoW hjk) γ
  have e3 := fillStepMap_fillMap Ω D.CW D.hcW (D.hleW i) (D.monoW (hij.trans hjk)) γ
  exact (congrArg (D.stepHom Ω j k hjk) e1).trans (e2.trans e3.symm)

lemma length_rW : (D.rW Ω hcX).length = D.n := OpPath.length_pushRun _ _ _ _ _ _ _ _ _

lemma length_path : (D.path Ω hcX).length = D.n + 5 := (D.isEllipticType Ω hcX).len_eq

/-- The objects of the run of the elliptic path. -/
lemma objN_path (s : ℕ) (hs : s ≤ D.n) :
    (D.path Ω hcX).objN (3 + s) = D.Fobj Ω hcX ⟨s, by omega⟩ := by
  rw [path, OpPath.objN_ellipticPath _ _ _ _ _ _ s (by rw [D.length_rW Ω hcX]; exact hs)]
  exact OpPath.objN_ofSeq _ _ _ _ (by change _ ≤ D.n; omega)

/-- The operations of the run of the elliptic path. -/
lemma opN_path_heq (s : ℕ) (hs : s < D.n) (h' : 3 + s < (D.path Ω hcX).length) :
    HEq ((D.path Ω hcX).opN (3 + s) h')
      ((D.rW Ω hcX).opN s (by rw [D.length_rW Ω hcX]; exact hs)) :=
  OpPath.opN_ellipticPath_heq _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 1600000 in
-- the operations of the pushed run are compared with `fillStepMap` by unfolding
/-- **The run homomorphism of the elliptic chain is `stepHom`.** -/
lemma runHom_path : ∀ (s : ℕ) (hs : s ≤ D.n)
    (h : 3 + s ≤ (D.path Ω hcX).toPiChain.len)
    (hrun : (D.path Ω hcX).toPiChain.IsDecuspRun 3 s h) (x),
    ChainObj.equivOfEq (D.objN_path Ω hcX s hs)
        ((D.path Ω hcX).toPiChain.runHom 3 s h hrun x) =
      D.stepHom Ω ⟨0, Nat.succ_pos _⟩ ⟨s, by omega⟩ (Fin.mk_le_mk.2 (by omega))
        (ChainObj.equivOfEq (D.objN_path Ω hcX 0 (Nat.zero_le _)) x)
  | 0, _, _, _, x => (D.stepHom_self Ω _ _).symm
  | s + 1, hs, h, hrun, x => by
    have ih := runHom_path s (by omega) (by omega) (fun t ht ↦ hrun t (by omega)) x
    have hop := (D.opN_path_heq Ω hcX s (by omega) (by
      change _ < (D.path Ω hcX).toPiChain.len; omega)).trans
      (OpPath.opN_ofSeq_heq _ _ _ s (by change _ < D.n; omega) _)
    have h1 := ElemOp.decuspHom_heq _ _ (D.objN_path Ω hcX s (by omega))
      (D.objN_path Ω hcX (s + 1) hs) hop (hrun s (by omega)) rfl
      ((D.path Ω hcX).toPiChain.runHom 3 s (by omega) (fun t ht ↦ hrun t (by omega)) x)
    exact h1.trans ((congrArg (D.stepHom Ω ⟨s, by omega⟩ ⟨s + 1, by omega⟩
      (Fin.mk_le_mk.2 (by omega))) ih).trans (D.stepHom_comp Ω _ _ _ _ _ _))

set_option maxHeartbeats 1600000 in
-- the objects of the elliptic path are identified with the pushed objects by unfolding
/-- **[AbsTopII] Corollary 3.3 (iii)(a)**: the cuspidalisation candidate of the elliptic chain is,
up to isomorphism, `Π_U ↠ Π_{D'} ↩ Π_V ↪ Π_X`: the map induced by the inclusion `U ⊆ D'`
(`stepHom`), the map induced by `FD : V ⟶ D'` (`φ₅`, at the base point of the run of fillings) and
the map induced by `FV : V ⟶ U_X` (`φ₁`). -/
theorem ellipticCandidate_spec :
    ∃ (eU : (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).PiU ≃ₜ*
        π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW ⟨0, Nat.succ_pos _⟩) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW ⟨0, Nat.succ_pos _⟩)))
      (eD : (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).PiD ≃ₜ*
        π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.n)) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.n))))
      (eV : (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).PiV ≃ₜ*
        (arithmeticExt Ω D.CV D.hcV).Pi),
      (∀ x, eD ((PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).surj
          x) = D.stepHom Ω ⟨0, Nat.succ_pos _⟩ (Fin.last D.n) (Fin.mk_le_mk.2 (Nat.zero_le _))
            (eU x)) ∧
        (∀ y, eD ((PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).incl
          y) = D.φ₅ Ω (eV y)) ∧
        ∀ y, (PiChain.ellipticCandidate (D.isEllipticType Ω hcX) (D.terminalIso Ω hcX)).emb y =
          D.φ₁ Ω hcX (eV y) := by
  have hlen5 : D.n + 3 = (D.rW Ω hcX).length + 3 := by rw [D.length_rW Ω hcX]
  have hlen6 : D.n + 4 = (D.rW Ω hcX).length + 4 := by rw [D.length_rW Ω hcX]
  have hD : (D.path Ω hcX).objN (D.n + 3) = D.A₅ Ω hcX := by
    rw [hlen5, path]
    exact OpPath.objN_ellipticPath_D _ _ _ _ _ _
  have hV : (D.path Ω hcX).objN (D.n + 4) = D.A₆ Ω hcX := by
    rw [hlen6, path]
    exact OpPath.objN_ellipticPath_V _ _ _ _ _ _
  refine ⟨ChainObj.equivOfEq (D.objN_path Ω hcX 0 (Nat.zero_le _)), ChainObj.equivOfEq hD,
    ChainObj.equivOfEq hV, fun x ↦ ?_, fun y ↦ ?_, fun y ↦ ?_⟩
  · have key := D.runHom_path Ω hcX D.n le_rfl (by
      change _ ≤ (D.path Ω hcX).length; rw [D.length_path Ω hcX]; omega)
      ((D.isEllipticType Ω hcX).isDecuspRun) x
    exact (congrArg (ChainObj.equivOfEq hD) (PiChain.objCongr_eq_equivOfEq _ _ _ _ _)).trans
      ((ChainObj.equivOfEq_trans _ _ _).trans key)
  · have hlen : D.n + 3 < (D.path Ω hcX).length := by
      rw [D.length_path Ω hcX]; omega
    have hop : HEq ((D.path Ω hcX).opN (D.n + 3) hlen) (D.o₅ Ω hcX) := by
      refine (OpPath.opN_congr_heq _ hlen5 hlen (by rw [← hlen5]; exact hlen)).trans ?_
      exact OpPath.opN_ellipticPath_D_heq _ _ _ _ _ _ _
    exact ElemOp.coverHom_heq₂ _ _ hD hV hop (D.isEllipticType Ω hcX).2.2.2.2.2.1 rfl y
  · have hlen : D.n + 4 < (D.path Ω hcX).length := by
      rw [D.length_path Ω hcX]; omega
    have hop : HEq ((D.path Ω hcX).opN (D.n + 4) hlen) (D.o₆ Ω hcX) := by
      refine (OpPath.opN_congr_heq _ hlen6 hlen (by rw [← hlen6]; exact hlen)).trans ?_
      exact OpPath.opN_ellipticPath_V_heq _ _ _ _ _ _ _
    have hidx : D.n + 4 + 1 = (D.path Ω hcX).length := by
      rw [D.length_path Ω hcX]
    have hA7 := (congrArg (fun k ↦ (D.path Ω hcX).objN k) hidx).trans
      (OpPath.objN_length (D.path Ω hcX))
    have h1 := ElemOp.quotHom_heq _ _ hV hA7 hop (D.isEllipticType Ω hcX).2.2.2.2.2.2 rfl y
    exact (congrArg (ChainObj.equivOfEq (OpPath.objN_length (D.path Ω hcX)))
      (PiChain.objCongr_eq_equivOfEq _ _ _ _ _)).trans ((ChainObj.equivOfEq_trans _ _ _).trans h1)

end EllipticData

end CurvesJacobian.Cusp
