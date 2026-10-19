/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiArithSpec
import CurvesJacobian.Cusp.ModelChain

/-!
# `Π_V` of a geometric Belyi chain has an infinite cusp image (MR8, round 26, step (4))

For Belyi data `D` (`CurvesJacobian.Cusp.BelyiData`) the second to last object `Π_V` of the
Belyi chain `D.path` has a cuspidal decomposition group of `Π_X` with infinite image
(`BelyiData.hasInfCusp_V`), and so has the corresponding object of every transport of the chain
along an isomorphism of cuspidal extensions `Π_X ≅ Π'` (`BelyiData.hasInfCusp_V_transport`; the
hypothesis `hV` of `PiChain.IsBelyiType.nonempty_geomModel`, `exists_candidate_fill` for the
transported chain, as needed for [AbsTopII] Cor 3.8, existence).

Proof: `Q ⊆ ℙ¹ ∖ {0, 1, ∞}` has at least three geometric cusps (`BelyiData.h3Q`), so its cuspidal
inertia groups are nontrivial (`arithCusps_ne_bot`) and infinite (`Δ_Q` is torsion-free); the
preimage under `Π_V ↪ Π_Q` of one of them is an infinite cuspidal inertia group `J` of `Π_V`
(`exists_arithCusps_coverHom_le`), `J` is the image under `Π_W ↠ Π_V` of a cuspidal inertia group
`I'` of `Π_W` (`exists_map_eq_of_conjInduced_fill`), and `I'` is commensurable with the image in
`Π_W` of a cuspidal inertia group `I` of `Π_X` (`BelyiData.cuspMatchW`); so `ρ_V(I) ∼ J` is
infinite.

* `CurvesJacobian.Cusp.exists_mem_arithCusps`: every curve with a cusp has a cuspidal inertia
  group;
* `CurvesJacobian.Cusp.not_commensurable_bot_of_mem_arithCusps`: with at least two geometric cusps,
  cuspidal inertia groups are infinite;
* `Belyi.Anabelian.ChainObj.hasInfCusp_transport`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory
open Pi1.Orbifold AffOrbicurve

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Belyi.Anabelian.ChainObj

variable {E E' : CuspidalExt.{u}}

/-- **Transport preserves infinite cusp images.** -/
theorem hasInfCusp_transport (Φ : E.Iso E') {A : ChainObj E} (hA : A.HasInfCusp) :
    (A.transport Φ).HasInfCusp := by
  obtain ⟨I, hI, h⟩ := hA
  exact ⟨I.map Φ.pi.toMulEquiv.toMonoidHom, (Φ.cusps_map I).1 hI, by rwa [transport_image]⟩

end Belyi.Anabelian.ChainObj

namespace CurvesJacobian.Cusp

section Cusps

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (C : HypCurve K)
  (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **A curve with a cusp has a cuspidal inertia group.** -/
theorem exists_mem_arithCusps : ∃ I, I ∈ arithCusps Ω C hc := by
  obtain ⟨y, hy⟩ := compl_nonempty_baseChangeOpen (k := K) (Ω := Ω) hc
  haveI : Nonempty (⊤ : (geomCurve Ω C).Opens) := ⟨⟨y, trivial⟩⟩
  obtain ⟨W₀, -, hW₀V, hW₀U⟩ := exists_isCentredOn_not_isCentredOn (geomData Ω C)
    (geomCurve Ω C) (curveEquivL Ω (transcendental_geomCoord Ω C))
    (curveEquivL_algebraMap Ω (transcendental_geomCoord Ω C)) (V := ⊤)
    (compl_finite_baseChangeOpen K Ω C.nonempty) trivial hy
  exact ⟨_, mem_arithCusps Ω C hc hW₀V.1 hW₀U⟩

/-- **Cuspidal inertia groups are infinite** if `U_Ω` has at least two cusps (they are nontrivial,
`arithCusps_ne_bot`, and `Δ_U` is torsion-free). -/
theorem not_commensurable_bot_of_mem_arithCusps
    (h2 : 1 < Nat.card ((geomOpen Ω C : Set (geomCurve Ω C))ᶜ : Set (geomCurve Ω C)))
    {I} (hI : I ∈ arithCusps Ω C hc) : ¬ I.Commensurable ⊥ := by
  intro hfin
  apply arithCusps_ne_bot Ω C hc h2 hI
  haveI : Finite I := (Subgroup.finite_of_commensurable_bot hfin).to_subtype
  refine eq_bot_iff.2 fun x hx ↦ Subgroup.mem_bot.2 ?_
  have h1 := Delta_eq_one_of_isOfFinOrder Ω C hc (δ := ⟨x, arithCusps_le Ω C hc hI hx⟩)
    (((Subgroup.subtype_injective _).isOfFinOrder_iff
      (f := ((projGk Ω C hc).toMonoidHom.ker).subtype)).1
      (I.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨x, hx⟩ : I))))
  exact congrArg Subtype.val h1

end Cusps

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M]

namespace BelyiData

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [Algebra M Ω] [IsScalarTower K M Ω] [Algebra.IsAlgebraic M Ω]
  {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (D : BelyiData (M := M) CX)

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsScalarTower K M Ω] in
/-- **`Π_V` has an infinite cuspidal inertia group** (coming from a cusp of `Q`). -/
theorem exists_arithCusps_V_infinite :
    ∃ J ∈ arithCusps Ω D.CV D.hcV, ¬ J.Commensurable ⊥ := by
  obtain ⟨I, hI⟩ := exists_mem_arithCusps Ω D.CQ D.hcQ
  have h2 : 1 < Nat.card ((geomOpen Ω D.CQ : Set (geomCurve Ω D.CQ))ᶜ :
      Set (geomCurve Ω D.CQ)) := by
    have hc := card_compl_eq_cuspDegree_of_isCurveOver (k := M) Ω D.CQ.U D.CQ.nonempty
    exact lt_of_lt_of_le (by omega : 1 < 3) (D.h3Q.trans hc.symm.le)
  have hIinf := not_commensurable_bot_of_mem_arithCusps Ω D.CQ D.hcQ h2 hI
  obtain ⟨J, hJ, hJI, hfin⟩ := exists_arithCusps_coverHom_le Ω D.CQ D.hcQ D.CV D.hcV D.FQ hI
  refine ⟨J, hJ, fun hJfin ↦ hIinf ?_⟩
  have hcomm : (J.map (coverPiHom Ω D.CQ D.hcQ D.CV D.hcV D.FQ).toMonoidHom).Commensurable I :=
    ⟨hfin, by rw [Subgroup.relIndex_eq_one.2 hJI]; exact one_ne_zero⟩
  exact hcomm.symm.trans ((map_commensurable_bot_iff _
    (coverPiHom_injective Ω D.CQ D.hcQ D.CV D.hcV D.FQ)).2 hJfin)

/-- **The object `Π_V` of the pushed run of fillings of `W` has an infinite cusp image.** -/
theorem hasInfCusp_Fobj_last : (D.Fobj Ω hcX (Fin.last D.r)).HasInfCusp := by
  obtain ⟨J, hJ, hJinf⟩ := D.exists_arithCusps_V_infinite Ω
  haveI : Nonempty (baseChangeOpen M Ω (D.UW (Fin.last D.r))) :=
    (nonempty_baseChangeOpen M Ω (D.CW.nonempty.mono (D.hleW _))).to_subtype
  obtain ⟨I', hI', hI'J⟩ := exists_map_eq_of_conjInduced_fill Ω D.CW D.hcW (D.hleW _)
    (D.hcUW _) (D.hypW _) _ (isConjInduced_fillPiHom Ω D.CW D.hcW (D.hleW _) (D.hcUW _)
      (D.hypW _)) hJ
  obtain ⟨I, hI, hII'⟩ := D.cuspMatchW Ω hcX I' hI'
  refine ⟨I, hI, fun hfin ↦ hJinf ?_⟩
  -- `ρ_V(I) ∼ fillMap(I') = T(J)`
  rw [ChainObj.image_push] at hfin
  have h1 : ((D.cW Ω).obj (Fin.last D.r)).image I' =
      I'.map (fillMap Ω D.CW D.hcW (D.hleW (Fin.last D.r))).toMonoidHom :=
    image_fillChainObj Ω D.CW D.hcW (D.hleW _) (D.hcUW _) (D.hypW _) I'
  have h2 : I'.map (fillMap Ω D.CW D.hcW (D.hleW (Fin.last D.r))).toMonoidHom =
      J.map (D.TV Ω).toMulEquiv.toMonoidHom := by
    rw [← hI'J, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun σ ↦
      (fillTransport_fillPiHom Ω D.CW D.hcW (D.hleW _) (D.hcUW _) (D.hypW _) σ).symm
  have h3 := ((D.cW Ω).obj (Fin.last D.r)).image_commensurable hII'
  rw [h1, h2] at h3
  exact (map_commensurable_bot_iff _ (D.TV Ω).injective).1 (h3.symm.trans hfin)

/-- **`Π_V = Π_{l+r+3}` of the Belyi chain has an infinite cusp image.** -/
theorem hasInfCusp_V : ((D.path Ω hcX).toPiChain.objN (D.l + D.r + 3)
    (by have := (D.isBelyiType Ω hcX).len_eq; omega)).HasInfCusp := by
  have e := D.objN_path Ω hcX 0 (Nat.zero_le _) 0 le_rfl
  have e' : D.Fobj Ω hcX ⟨D.r - 0 + 0, by omega⟩ = D.Fobj Ω hcX (Fin.last D.r) :=
    congrArg (D.Fobj Ω hcX) (Fin.ext (by simp))
  have h := D.hasInfCusp_Fobj_last Ω hcX
  rw [← e', ← e] at h
  have hlen := (D.isBelyiType Ω hcX).len_eq
  exact ((D.path Ω hcX).toPiChain.objN_congr_iff ChainObj.HasInfCusp
    (a := D.l + 3 + (D.r - 0) + 0) (by omega) (by omega) _).1 h

/-- **The transported object `Π_V` has an infinite cusp image** (the hypothesis `hV` for the
transport of the Belyi chain along `Φ : Π_X ≅ Π'`). -/
theorem hasInfCusp_V_transport {E' : CuspidalExt.{u + 1}}
    (Φ : (arithmeticExt Ω CX hcX).Iso E') :
    ChainObj.HasInfCusp (((D.path Ω hcX).toPiChain.transport Φ).objN (D.l + D.r + 3)
      (by have := (D.isBelyiType Ω hcX).len_eq; change _ ≤ (D.path Ω hcX).toPiChain.len; omega)) :=
  ChainObj.hasInfCusp_transport Φ (D.hasInfCusp_V Ω hcX)

end BelyiData

end CurvesJacobian.Cusp
