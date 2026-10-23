/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelCuspIndep
import Belyi.Anabelian.EllipticChain

/-!
# The run of an elliptic-type chain is a filling of curves (MR8.7, round 29)

[AbsTopII] Corollary 3.3 (iii)(a) (`Topics in Absolute Anabelian Geometry II.txt` l.4481–4491):
an elliptic-type `Π`-chain (type-chain `⋏, ⋎, ⋏, •^n, ⋏, ⋎`, belyi
`Belyi.Anabelian.PiChain.IsEllipticType`) with a terminal isomorphism to the trivial chain
produces `Π_U ↠ Π_D ↩ Π_V ↪ Π` (`PiChain.ellipticCandidate`). For the arithmetic fundamental
group `Π_X ↠ G_K` of an affine hyperbolic curve over a number field we show, assuming the
rel-isom-DGC over number fields (`hDGC`):

* `PiChain.IsEllipticType.hasInfCusp_D`: the object `Π_D = Π_{n+3}` at the end of the run of `•`'s
  has an infinite cusp image (for `n ≥ 1` from the model independence of cusps,
  `modelCuspIndep₂`, and `ElemOp.hasInfCusp_target_of_cover₂`: otherwise the last `•` would fill
  all cusps of a model and `Π_V ⊆ Π_D` would be an open subgroup of `Δ_X` that is `Δ` of a proper
  curve); hence every object has one (`PiChain.IsEllipticType.hasInfCusp`);
* **`PiChain.IsEllipticType.exists_candidate_fill_toG`**: if `Δ` of `Π_U = Π_3` is torsion-free
  (a group-theoretic condition; it holds for the chains of [AbsTopII] Ex 3.2, where `U` is a
  curve), there are a full geometric model `(Y, ι : Π_Y ≅ Π_U)`, a filling `U_Y ⊆ U'` and
  `ε : Π_{(X̄_Y, U')} ≅ Π_D` such that `Π_U ↠ Π_D` is `ε ∘ fillPiHom ∘ ι⁻¹`, with `ε` over
  `res : G_M → G_K` up to conjugation.

(Without the torsion-freeness of `Δ_U` the middle objects may be orbicurve groups, which have no
geometric models in this framework.)
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace Belyi.Anabelian

variable {E : CuspidalExt.{u}}

/-- The operation homomorphism of a `⋏` is compatible with the rigidifying homomorphisms. -/
theorem ElemOp.compat_coverHom {A B : ChainObj E} :
    ∀ (o : ElemOp A B) (h : o.kind = .cover), ChainObj.Compat B A (o.coverHom h)
  | .cover _ _ _ compat, _ => compat
  | .quot .., h => absurd h (by simp [ElemOp.kind])
  | .decusp .., h => absurd h (by simp [ElemOp.kind])
  | .deorb .., h => absurd h (by simp [ElemOp.kind])

namespace PiChain

variable {c : PiChain E} {n : ℕ}

/-- **The embedding `Π_V ↪ Π` of an elliptic-type chain lies over `G` up to conjugation.** -/
theorem exists_pr_ellipticEmb (hc : c.IsEllipticType n)
    (t : c.TerminalIso (PiChain.trivial E)) :
    ∃ g : E.G, ∀ y, E.pr (PiChain.ellipticEmb hc t y) =
      g * (c.objN (n + 4) (by have := hc.len_eq; omega)).toG y * g⁻¹ := by
  have hlen := hc.len_eq
  obtain ⟨g, hg⟩ := t.over
  refine ⟨g, fun y ↦ ?_⟩
  have h1 := ChainObj.toG_apply_of_compat (ElemOp.compat_quotHom
    (c.opN (n + 4) (by omega)) hc.2.2.2.2.2.2) y
  have h2 := ChainObj.toG_apply_of_compat (c.compat_objCongr (a := n + 4 + 1) (b := c.len)
    (by omega) (by omega) le_rfl) ((c.opN (n + 4) (by omega)).quotHom hc.2.2.2.2.2.2 y)
  have h3 := hg (c.objCongr (a := n + 4 + 1) (b := c.len) (by omega) (by omega) le_rfl
    ((c.opN (n + 4) (by omega)).quotHom hc.2.2.2.2.2.2 y))
  exact h3.trans (congrArg (fun z ↦ g * z * g⁻¹) (h2.trans h1))

/-- **An elliptic-type chain has no operation of type `⊚`.** -/
theorem IsEllipticType.kind_ne_deorb (hc : c.IsEllipticType n) (j : ℕ) (hj : j < c.len) :
    (c.opN j hj).kind ≠ .deorb := by
  obtain ⟨hlen, h0, h1, h2, h3, h4, h5⟩ := hc
  have hd : (OpKind.decusp) ≠ .deorb := by decide
  have hcv : (OpKind.cover) ≠ .deorb := by decide
  have hq : (OpKind.quot) ≠ .deorb := by decide
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact h0 ▸ hcv
    · exact h1 ▸ hq
    · exact h2 ▸ hcv
  rcases Nat.lt_or_ge j (n + 3) with hjn | hjn
  · rw [c.kind_opN_congr (b := 3 + (j - 3)) (by omega) hj (by omega), h3 (j - 3) (by omega)]
    exact hd
  rcases (by omega : j = n + 3 ∨ j = n + 4) with rfl | rfl
  · exact h4 ▸ hcv
  · exact h5 ▸ hq

/-- The operation homomorphism `Π_V ↪ Π_D` of an elliptic-type chain is compatible with the
rigidifying homomorphisms. -/
theorem compat_ellipticIncl (hc : c.IsEllipticType n) :
    ChainObj.Compat _ _ (PiChain.ellipticIncl hc) :=
  ElemOp.compat_coverHom _ _

end PiChain

end Belyi.Anabelian

namespace CurvesJacobian.Cusp

open Belyi.Anabelian.ChainObj

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The point `Spec Ω ⟶ Spec K`. -/
local notation "sK" => Spec.map (CommRingCat.ofHom (algebraMap K Ω))

variable {c : PiChain (arithmeticExt Ω CX hcX)} {n : ℕ}

/-- **`Π_D` of an elliptic-type chain with `n = 0` has an infinite cusp image**: it is linked to
`Π₀ ≅ Π_X` by `⋏, ⋎, ⋏`. -/
theorem _root_.Belyi.Anabelian.PiChain.IsEllipticType.hasInfCusp_D_zero
    (hc : c.IsEllipticType 0) : (c.objN (0 + 3) (by have := hc.len_eq; omega)).HasInfCusp := by
  have hlen := hc.len_eq
  have h0 := c.hasInfCusp_obj_zero₂ (Nat.zero_le _)
  have h1 := (c.opN 0 (by omega)).hasInfCusp_target (Or.inl hc.2.1) h0
  have h2 := (c.opN 1 (by omega)).hasInfCusp_target (Or.inr hc.2.2.1) h1
  exact (c.opN 2 (by omega)).hasInfCusp_target (Or.inl hc.2.2.2.1) h2

/-- **`Π_D = Π_{n+3}` of an elliptic-type chain with a terminal isomorphism has an infinite cusp
image** (assuming the rel-isom-DGC over number fields). -/
theorem _root_.Belyi.Anabelian.PiChain.IsEllipticType.hasInfCusp_D (hc : c.IsEllipticType n)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k) :
    (c.objN (n + 3) (by have := hc.len_eq; omega)).HasInfCusp := by
  have hlen := hc.len_eq
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hc.hasInfCusp_D_zero
  have hkind : (c.opN (n + 2) (by omega)).kind = .decusp := by
    rw [c.kind_opN_congr (b := 3 + (n - 1)) (by omega) _ (by omega)]
    exact hc.2.2.2.2.1 (n - 1) (by omega)
  have hle : ∀ j (hj : j ≤ n + 2), (c.objN j (by omega)).HasInfCusp :=
    c.hasInfCusp_le_of_decusp₂ (n + 2) (by omega) hkind
      (fun j' _ ↦ hc.kind_ne_deorb j' (by omega))
  obtain ⟨D₀⟩ := c.nonempty_geomModel_le₂ hDGC (n + 2) (by omega)
    (fun j _ ↦ hc.kind_ne_deorb j (by omega)) hle
  have hCS := c.cuspSurj_le₂ (modelCuspIndep₂ Ω CX hcX hDGC) hDGC (n + 2) (by omega)
    (fun i _ ↦ hc.kind_ne_deorb i (by omega)) hle
  exact (c.opN (n + 2) (by omega)).hasInfCusp_target_of_cover₂ hkind D₀ hDGC hCS
    (PiChain.ellipticIncl hc) (ElemOp.coverHom_injective _ _) (ElemOp.isOpen_range_coverHom _ _)
    (PiChain.compat_ellipticIncl hc) (PiChain.ellipticEmb hc t)
    (PiChain.ellipticEmb_injective hc t) (PiChain.isOpen_range_ellipticEmb hc t)
    (PiChain.exists_pr_ellipticEmb hc t)

/-- **Every object of an elliptic-type chain with a terminal isomorphism has an infinite cusp
image.** -/
theorem _root_.Belyi.Anabelian.PiChain.IsEllipticType.hasInfCusp (hc : c.IsEllipticType n)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (j : ℕ) (hj : j ≤ c.len) : (c.objN j hj).HasInfCusp := by
  have hlen := hc.len_eq
  have hD := hc.hasInfCusp_D t hDGC
  have down : ∀ m k (hk : k ≤ c.len), k + m = n + 3 → (c.objN k hk).HasInfCusp := by
    intro m
    induction m with
    | zero =>
      intro k hk hkm
      exact (c.objN_congr_iff ChainObj.HasInfCusp (by omega) _ _).2 hD
    | succ m ih =>
      intro k hk hkm
      exact (c.opN k (by omega)).hasInfCusp_source (hc.kind_ne_deorb k (by omega))
        (ih (k + 1) (by omega) (by omega))
  have h4 : (c.objN (n + 4) (by omega)).HasInfCusp :=
    (c.opN (n + 3) (by omega)).hasInfCusp_target (Or.inl hc.2.2.2.2.2.1)
      (down 0 (n + 3) (by omega) (by omega))
  rcases Nat.lt_or_ge j (n + 4) with hj4 | hj4
  · exact down (n + 3 - j) j hj (by omega)
  rcases (by omega : j = n + 4 ∨ j = n + 4 + 1) with rfl | rfl
  · exact h4
  · exact (c.opN (n + 4) (by omega)).hasInfCusp_target (Or.inr hc.2.2.2.2.2.2) h4

set_option maxHeartbeats 800000 in
-- the existential statement with the chain indices is slow to elaborate
/-- **The candidate of an elliptic-type chain: the run is a filling of curves.** If `Δ` of
`Π_U = Π_3` is torsion-free, there are a full geometric model `(Y, ι : Π_Y ≅ Π_U)`, a filling
`U_Y ⊆ U'` and `ε : Π_{(X̄_Y, U')} ≅ Π_D` such that `Π_U ↠ Π_D` is `ε ∘ fillPiHom ∘ ι⁻¹`. -/
theorem _root_.Belyi.Anabelian.PiChain.IsEllipticType.exists_candidate_fill
    (hc : c.IsEllipticType n) (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (htf : IsTorsionFreeSubgroup (c.objN 3 (by have := hc.len_eq; omega)).Delta) :
    ∃ D : GeomModel Ω CX hcX (c.objN 3 (by have := hc.len_eq; omega)),
      Function.Surjective D.ι ∧
      ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
        (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
          2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
        (ε : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
          baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* (PiChain.ellipticCandidate hc t).PiD),
        ∀ σ, (PiChain.ellipticCandidate hc t).surj (D.ι σ) =
          ε (fillPiHom Ω D.Y D.hY h hc' hyp σ) := by
  have hlen := hc.len_eq
  obtain ⟨D₀⟩ := c.nonempty_geomModel_le₂ hDGC 3 (by omega)
    (fun j _ ↦ hc.kind_ne_deorb j (by omega)) (fun j _ ↦ hc.hasInfCusp t hDGC j _)
  obtain ⟨D, hD⟩ := D₀.exists_full hDGC htf
  have hinf : ∀ s (hs : s < n), (c.objN (3 + s + 1) (by omega)).HasInfCusp :=
    fun s _ ↦ hc.hasInfCusp t hDGC _ _
  obtain ⟨U', h, hc', hyp, ι', hrel⟩ := c.exists_run_fill hDGC 3 (by omega) D hD n (by omega)
    hc.isDecuspRun hinf
  have hF := isConjInduced_fillPiHom Ω D.Y D.hY h hc' hyp
  obtain ⟨u, hu⟩ := IsConjInduced.exists_conj_eq hrel hF
  refine ⟨D, hD, U', h, hc', hyp, ((conjCMEquiv u).trans ι').trans
    (c.objCongr (a := 3 + n) (b := n + 3) (by omega) (by omega) (by omega)), fun σ ↦ ?_⟩
  have e : ι' (u * fillPiHom Ω D.Y D.hY h hc' hyp σ * u⁻¹) =
      c.runHom 3 n (by omega) hc.isDecuspRun (D.ι σ) :=
    (congrArg ι' (hu σ)).symm.trans (ι'.apply_symm_apply _)
  exact congrArg (c.objCongr (a := 3 + n) (b := n + 3) (by omega) (by omega) (by omega)) e.symm

set_option maxHeartbeats 800000 in
-- the existential statement with the chain indices is slow to elaborate
/-- **`exists_candidate_fill` with the projection to `G_K`**: moreover `ε : Π_{(X̄_Y, U')} ≅ Π_D`
lies over `res : G_M → G_K` up to conjugation. -/
theorem _root_.Belyi.Anabelian.PiChain.IsEllipticType.exists_candidate_fill_toG
    (hc : c.IsEllipticType n) (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (htf : IsTorsionFreeSubgroup (c.objN 3 (by have := hc.len_eq; omega)).Delta) :
    ∃ D : GeomModel Ω CX hcX (c.objN 3 (by have := hc.len_eq; omega)),
      Function.Surjective D.ι ∧
      ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
        (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
          2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
        (ε : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
          baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* (PiChain.ellipticCandidate hc t).PiD),
        (∀ σ, (PiChain.ellipticCandidate hc t).surj (D.ι σ) =
          ε (fillPiHom Ω D.Y D.hY h hc' hyp σ)) ∧
        ∃ g₀ : π₁ᵉᵗ(sK), ∀ τ, toGk (c.objN (n + 3) (by have := hc.len_eq; omega)) (ε τ) =
          g₀ * resGal K Ω D.M (projGk Ω (fillCurve D.Y h hyp) hc' τ) * g₀⁻¹ := by
  have hlen := hc.len_eq
  obtain ⟨D, hD, U', h, hc', hyp, ε, hε⟩ := hc.exists_candidate_fill t hDGC htf
  refine ⟨D, hD, U', h, hc', hyp, ε, hε, ?_⟩
  have hf : ChainObj.Compat (c.objN 3 (by omega)) (c.objN (n + 3) (by omega))
      (PiChain.ellipticCandidate hc t).surj :=
    (c.compat_runHom 3 n (by omega) hc.isDecuspRun).comp
      (c.compat_objCongr (a := 3 + n) (b := n + 3) (by omega) (by omega) (by omega))
  have hrel : IsConjInduced (Spec.map (CommRingCat.ofHom (resAlg D.M h).toRingHom))
      (fun σ ↦ ε.symm ((PiChain.ellipticCandidate hc t).surj (D.ι σ))) :=
    (isConjInduced_fillPiHom Ω D.Y D.hY h hc' hyp).congr_fun fun σ ↦
      (congrArg ε.symm (hε σ)).trans (ε.symm_apply_apply _)
  exact D.exists_toGk_ofFill _ hf h hc' hyp ε hrel

end CurvesJacobian.Cusp
