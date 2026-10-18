/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiArithChain
import CurvesJacobian.Cusp.OpPathRun

/-!
# The cuspidalisation candidates of the Belyi chain (MR8.5, [AbsTopII] Corollary 3.7 (a))

[AbsTopII] Corollary 3.7 (a) (`Topics in Absolute Anabelian Geometry II.txt` l.4743–4753): the
surjection `Π_U ↠ Π_V` (`U ⊆ V` open) is recovered as the composite of the last `•`'s of the
Belyi chain, and `Π_V ↪ Π_X` as its last operation `⋎` followed by the terminal isomorphism.

For Belyi data `D` (`CurvesJacobian.Cusp.BelyiData`) and `m ≤ r`,
**`BelyiData.belyiCandidate_spec`**: the candidate
`PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm ∈ belyiCusp Π_X`
(`BelyiData.belyiCandidate_mem`) is isomorphic to
`Π_{U} ↠ Π_V ↪ Π_X` with `U = UW_{r-m} ⊆ V = UW_r`: `Π_U ↠ Π_V` is the map
`π₁ᵉᵗ(Spec Γ(U)) → π₁ᵉᵗ(Spec Γ(V))` induced by the inclusion (`stepHom`, i.e. `fillStepMap`, at
the base points of the run of fillings) and `Π_V ↪ Π_X` is induced by the finite étale
`FV : V ⟶ U_X` (`φ₄`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M]

namespace BelyiData

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [Algebra M Ω] [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]
  {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (D : BelyiData (M := M) CX)

attribute [local instance] isAlgClosure_of_isAlgebraic

lemma monoW : Monotone D.UW := Fin.monotone_iff_le_succ.2 D.hmonoW

/-- **`Π_{U_i} → Π_{U_j}`** for `i ≤ j` along the run of fillings `W ⊆ … ⊆ V` (at the base
points `fillPoint`), induced by `Spec Γ(U_i) ⟶ Spec Γ(U_j)`. -/
def stepHom (i j : Fin (D.r + 1)) (hij : i ≤ j) :
    π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫ baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)) →ₜ*
      π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW j) ≫ baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW j)) :=
  fillStepMap Ω D.CW D.hcW (D.hleW i) (D.monoW hij)

lemma stepHom_self (i : Fin (D.r + 1)) (y) : D.stepHom Ω i i le_rfl y = y := by
  obtain ⟨γ, rfl⟩ := fillMap_surjective Ω D.CW D.hcW (D.hleW i) (D.hcUW i) y
  exact fillStepMap_fillMap Ω D.CW D.hcW (D.hleW i) (D.monoW le_rfl) γ

lemma stepHom_comp (i j k : Fin (D.r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (y) :
    D.stepHom Ω j k hjk (D.stepHom Ω i j hij y) = D.stepHom Ω i k (hij.trans hjk) y := by
  obtain ⟨γ, rfl⟩ := fillMap_surjective Ω D.CW D.hcW (D.hleW i) (D.hcUW i) y
  have e1 := fillStepMap_fillMap Ω D.CW D.hcW (D.hleW i) (D.monoW hij) γ
  have e2 := fillStepMap_fillMap Ω D.CW D.hcW (D.hleW j) (D.monoW hjk) γ
  have e3 := fillStepMap_fillMap Ω D.CW D.hcW (D.hleW i) (D.monoW (hij.trans hjk)) γ
  exact (congrArg (D.stepHom Ω j k hjk) e1).trans (e2.trans e3.symm)

/-- The pushed objects of the run of fillings of `W`. -/
abbrev Fobj (i : Fin (D.r + 1)) : ChainObj (arithmeticExt Ω CX hcX) :=
  (D.A₄ Ω hcX).push (E' := arithmeticExt Ω D.CW D.hcW) (ContinuousMonoidHom.id _)
    (ElemOp.isOpen_range_id (E' := arithmeticExt Ω D.CW D.hcW)) (D.ιW Ω hcX)
    (D.ιW_injective Ω hcX) (D.isOpen_range_ιW Ω hcX) (D.hcompW Ω hcX) ((D.cW Ω).obj i)

lemma stepHom_congr (i j j' : Fin (D.r + 1)) (hij : i ≤ j) (hj : j = j') (y) :
    ChainObj.equivOfEq (congrArg (D.Fobj Ω hcX) hj) (D.stepHom Ω i j hij y) =
      D.stepHom Ω i j' (hj ▸ hij) y := by
  subst hj
  rfl

lemma length_r₁ : (D.r₁ Ω hcX).length = D.l := OpPath.length_pushRun _ _ _ _ _ _ _ _ _

lemma length_r₂ : (D.r₂ Ω hcX).length = D.r := OpPath.length_pushRun _ _ _ _ _ _ _ _ _

lemma length_path : (D.path Ω hcX).length = D.l + D.r + 4 := (D.isBelyiType Ω hcX).len_eq

/-- The objects of the second run of the Belyi path. -/
lemma objN_path (m : ℕ) (hm : m ≤ D.r) (s : ℕ) (hs : s ≤ m) :
    (D.path Ω hcX).objN (D.l + 3 + (D.r - m) + s) =
      D.Fobj Ω hcX ⟨D.r - m + s, by omega⟩ := by
  have e : D.l + 3 + (D.r - m) + s = (D.r₁ Ω hcX).length + 3 + (D.r - m + s) := by
    rw [D.length_r₁ Ω hcX]
    omega
  rw [e, path, OpPath.objN_belyiPath _ _ _ _ _ _ _ (by rw [D.length_r₂ Ω hcX]; omega)]
  exact OpPath.objN_ofSeq _ _ _ _ (by change _ ≤ D.r; omega)

/-- The operations of the second run of the Belyi path. -/
lemma opN_path_heq (m : ℕ) (hm : m ≤ D.r) (s : ℕ) (hs : s < m)
    (h' : D.l + 3 + (D.r - m) + s < (D.path Ω hcX).length) :
    HEq ((D.path Ω hcX).opN (D.l + 3 + (D.r - m) + s) h')
      ((D.r₂ Ω hcX).opN (D.r - m + s) (by rw [D.length_r₂ Ω hcX]; omega)) := by
  have e : D.l + 3 + (D.r - m) + s = (D.r₁ Ω hcX).length + 3 + (D.r - m + s) := by
    rw [D.length_r₁ Ω hcX]
    omega
  refine (OpPath.opN_congr_heq _ e h' (by rw [← e]; exact h')).trans ?_
  exact OpPath.opN_belyiPath_heq _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 1600000 in
-- the operations of the pushed run are compared with `fillStepMap` by unfolding
/-- **The run homomorphism of the Belyi chain is `stepHom`.** -/
lemma runHom_path (m : ℕ) (hm : m ≤ D.r) : ∀ (s : ℕ) (hs : s ≤ m)
    (h : D.l + 3 + (D.r - m) + s ≤ (D.path Ω hcX).toPiChain.len)
    (hrun : (D.path Ω hcX).toPiChain.IsDecuspRun (D.l + 3 + (D.r - m)) s h) (x),
    ChainObj.equivOfEq (D.objN_path Ω hcX m hm s hs)
        ((D.path Ω hcX).toPiChain.runHom (D.l + 3 + (D.r - m)) s h hrun x) =
      D.stepHom Ω ⟨D.r - m, by omega⟩ ⟨D.r - m + s, by omega⟩
        (Fin.mk_le_mk.2 (by omega))
        (ChainObj.equivOfEq (D.objN_path Ω hcX m hm 0 (Nat.zero_le _)) x)
  | 0, _, _, _, x => (D.stepHom_self Ω _ _).symm
  | s + 1, hs, h, hrun, x => by
    have ih := runHom_path m hm s (by omega) (by omega) (fun t ht ↦ hrun t (by omega)) x
    have hop := (D.opN_path_heq Ω hcX m hm s (by omega) (by
      change _ < (D.path Ω hcX).toPiChain.len; omega)).trans
      (OpPath.opN_ofSeq_heq _ _ _ (D.r - m + s) (by change _ < D.r; omega) _)
    have h1 := ElemOp.decuspHom_heq _ _ (D.objN_path Ω hcX m hm s (by omega))
      (D.objN_path Ω hcX m hm (s + 1) hs) hop (hrun s (by omega)) rfl
      ((D.path Ω hcX).toPiChain.runHom (D.l + 3 + (D.r - m)) s (by omega)
        (fun t ht ↦ hrun t (by omega)) x)
    exact h1.trans ((congrArg (D.stepHom Ω ⟨D.r - m + s, by omega⟩ ⟨D.r - m + s + 1, by omega⟩
      (Fin.mk_le_mk.2 (by omega))) ih).trans (D.stepHom_comp Ω _ _ _ _ _ _))

set_option maxHeartbeats 1600000 in
-- the objects of the Belyi path are identified with the pushed objects by unfolding
/-- **[AbsTopII] Corollary 3.7 (a)**: the cuspidalisation candidate of the Belyi chain for
`m ≤ r` is, up to isomorphism, `Π_U ↠ Π_V ↪ Π_X` for `U = UW_{r-m} ⊆ V`: the map induced by
the inclusion `U ⊆ V` (`stepHom`) followed by the map induced by `FV : V ⟶ U_X` (`φ₄`). -/
theorem belyiCandidate_spec (m : ℕ) (hm : m ≤ D.r) :
    ∃ (eU : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiU ≃ₜ*
        π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW ⟨D.r - m, by omega⟩) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW ⟨D.r - m, by omega⟩)))
      (eV : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiV ≃ₜ*
        π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
          baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r)))),
      (∀ x, eV ((PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).surj
          x) = D.stepHom Ω ⟨D.r - m, by omega⟩ (Fin.last D.r) (Fin.le_last _) (eU x)) ∧
        ∀ y, (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).emb y =
          D.φ₄ Ω hcX (eV y) := by
  have hV : (D.path Ω hcX).objN (D.l + D.r + 3) = D.A₅ Ω hcX := by
    rw [show D.l + D.r + 3 = (D.r₁ Ω hcX).length + (D.r₂ Ω hcX).length + 3 by
      rw [D.length_r₁ Ω hcX, D.length_r₂ Ω hcX], path]
    exact OpPath.objN_belyiPath_last _ _ _ _ _ _
  refine ⟨ChainObj.equivOfEq (D.objN_path Ω hcX m hm 0 (Nat.zero_le _)),
    ChainObj.equivOfEq hV, fun x ↦ ?_, fun y ↦ ?_⟩
  · have hlast : (⟨D.r - m + m, by omega⟩ : Fin (D.r + 1)) = Fin.last D.r := Fin.ext (by
      simp only [Fin.val_last]; omega)
    have key := D.runHom_path Ω hcX m hm m le_rfl (by
      change _ ≤ (D.path Ω hcX).length; rw [D.length_path Ω hcX]; omega)
      ((D.isBelyiType Ω hcX).isDecuspRun m hm) x
    have k2 := (congrArg (ChainObj.equivOfEq (congrArg (D.Fobj Ω hcX) hlast)) key).trans
      (D.stepHom_congr Ω hcX _ _ _ _ hlast _)
    exact (congrArg (ChainObj.equivOfEq hV) (PiChain.objCongr_eq_equivOfEq _ _ _ _ _)).trans
      (((ChainObj.equivOfEq_trans _ _ _).trans (ChainObj.equivOfEq_trans _ _ _).symm).trans k2)
  · have hlen : D.l + D.r + 3 < (D.path Ω hcX).length := by
      rw [D.length_path Ω hcX]; omega
    have hop : HEq ((D.path Ω hcX).opN (D.l + D.r + 3) hlen) (D.o₄ Ω hcX) := by
      have e : D.l + D.r + 3 = (D.r₁ Ω hcX).length + (D.r₂ Ω hcX).length + 3 := by
        rw [D.length_r₁ Ω hcX, D.length_r₂ Ω hcX]
      refine (OpPath.opN_congr_heq _ e hlen (by rw [← e]; exact hlen)).trans ?_
      exact OpPath.opN_belyiPath_last_heq _ _ _ _ _ _ _
    have hidx : D.l + D.r + 3 + 1 = (D.path Ω hcX).length := by
      rw [D.length_path Ω hcX]
    have hA6 := (congrArg (fun n ↦ (D.path Ω hcX).objN n) hidx).trans
      (OpPath.objN_length (D.path Ω hcX))
    have h1 := ElemOp.quotHom_heq _ _ hV hA6 hop (D.isBelyiType Ω hcX).2.2.2.2.2.2 rfl y
    exact (congrArg (ChainObj.equivOfEq (OpPath.objN_length (D.path Ω hcX)))
      (PiChain.objCongr_eq_equivOfEq _ _ _ _ _)).trans ((ChainObj.equivOfEq_trans _ _ _).trans h1)

end BelyiData

end CurvesJacobian.Cusp
