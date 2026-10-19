/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelCover

/-!
# Cuspidal decomposition groups of chain objects and the cusps of a geometric model (MR8.5)

A geometric model `D` of a chain object `A` (`CurvesJacobian.Cusp.GeomModel`) carries the cusp
compatibility invariant `GeomModel.cusp`: for a cuspidal inertia group `I` of `Π_X`, the preimage
`ι⁻¹(ρ_A(I))` is finite or commensurable with a cuspidal inertia group of `Π_Y`. Here:

* `Subgroup.commensurable_comap_iff`, `Subgroup.comap_commensurator`: for a homomorphism
  `f : G → H` with image of finite index, `f⁻¹` preserves and reflects
  commensurability and commutes with commensurators.
* `GeomModel.comap_toG_ker`: `ι⁻¹(Δ_A) = Δ_Y`.
* **`GeomModel.comap_mem_arithCusps_of_isCuspidal`**: for a cuspidal decomposition group `C` in
  `Δ_A` ([AbsTopI] Def 4.2 (iii), (3Π)) lying in a torsion-free subgroup (the situation of an
  operation of type `•`), `ι⁻¹(C)` is a cuspidal inertia group of `Π_Y`: it is
  `Comm(ι⁻¹ρ_A(I)) ∩ Δ_Y = Comm(J) ∩ Δ_Y = J` ([AbsTopI] Lemma 4.1 (i), commensurable
  terminality); the finite case is excluded by torsion-freeness.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory
open scoped Pointwise

universe u

noncomputable section

section GroupTheory

variable {G H : Type*} [Group G] [Group H]

/-- A subgroup of finite index has finite relative index in every subgroup. -/
lemma Subgroup.relIndex_ne_zero_of_index_ne_zero {R : Subgroup H} (hR : R.index ≠ 0)
    (K : Subgroup H) : R.relIndex K ≠ 0 := fun h0 ↦
  hR (by rw [← Subgroup.relIndex_top_right]; exact Subgroup.relIndex_eq_zero_of_le_right le_top h0)

/-- `X ∩ R` is commensurable with `X` for `R` of finite index. -/
lemma Subgroup.commensurable_inf_of_index_ne_zero {R : Subgroup H} (hR : R.index ≠ 0)
    (X : Subgroup H) : (R ⊓ X).Commensurable X :=
  ⟨by rw [Subgroup.inf_relIndex_right]; exact Subgroup.relIndex_ne_zero_of_index_ne_zero hR X,
    by rw [Subgroup.relIndex_eq_one.2 inf_le_right]; exact one_ne_zero⟩

/-- **Preimages under a homomorphism with image of finite index preserve and reflect
commensurability.** -/
theorem Subgroup.commensurable_comap_iff {f : G →* H} (hR : f.range.index ≠ 0) {X Y : Subgroup H} :
    (X.comap f).Commensurable (Y.comap f) ↔ X.Commensurable Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comap' f⟩
  have h' := h.map' f
  rw [Subgroup.map_comap_eq, Subgroup.map_comap_eq] at h'
  exact (Subgroup.commensurable_inf_of_index_ne_zero hR X).symm.trans
    (h'.trans (Subgroup.commensurable_inf_of_index_ne_zero hR Y))

omit [Group H] in
lemma Subgroup.conjAct_smul_comap {H : Type*} [Group H] (f : G →* H) (X : Subgroup H) (g : G) :
    ConjAct.toConjAct g • X.comap f = (ConjAct.toConjAct (f g) • X).comap f := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_comap, Subgroup.mem_comap,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, ConjAct.toConjAct_smul]
  simp only [map_mul, map_inv]

/-- **Commensurators commute with preimages** under a homomorphism with image of finite
index. -/
theorem Subgroup.comap_commensurator {f : G →* H} (hR : f.range.index ≠ 0) (X : Subgroup H) :
    (Subgroup.Commensurable.commensurator X).comap f =
      Subgroup.Commensurable.commensurator (X.comap f) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.Commensurable.commensurator_mem_iff,
    Subgroup.Commensurable.commensurator_mem_iff, Subgroup.conjAct_smul_comap,
    Subgroup.commensurable_comap_iff hR]

end GroupTheory

namespace CurvesJacobian.Cusp.GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The image of `ι` has finite index. -/
lemma index_range_ne_zero : (D.ι : D.Pi →* A.grp).range.index ≠ 0 := by
  haveI := finiteIndex_of_isOpen (G := A.grp) (O := (D.ι : D.Pi →* A.grp).range)
    (by rw [MonoidHom.coe_range]; exact D.isOpen_range)
  exact Subgroup.FiniteIndex.index_ne_zero

/-- **`ι⁻¹(Δ_A) = Δ_Y`.** -/
lemma comap_Delta : A.Delta.comap (D.ι : D.Pi →* A.grp) = (projGk Ω D.Y D.hY).toMonoidHom.ker := by
  ext σ
  rw [Subgroup.mem_comap, MonoidHom.mem_ker]
  change toGk A (D.ι σ) = 1 ↔ _
  rw [toG_ι, conj_eq_one_iff, map_eq_one_iff _ (resGal_injective (K := K) (Ω := Ω) D.M)]
  rfl

/-- **The preimage under `ι` of a cuspidal decomposition group `C` in `Δ_A` lying in a
torsion-free subgroup is a cuspidal inertia group of `Π_Y`** (cusp compatibility of the model,
[AbsTopI] Lemma 4.1 (i)). -/
theorem comap_mem_arithCusps_of_isCuspidal {C : Subgroup A.grp} (hC : A.IsCuspidal C)
    (tf : A.InTorsionFreeNormalOpen C) :
    C.comap (D.ι : D.Pi →* A.grp) ∈ arithCusps Ω D.Y D.hY := by
  obtain ⟨I, hI, hne, rfl⟩ := hC
  have hR := D.index_range_ne_zero
  rw [Subgroup.comap_inf, Subgroup.comap_commensurator hR, comap_Delta]
  rcases D.cusp I hI with hb | ⟨J, hJ, hJc⟩
  · exfalso
    refine hne ?_
    have hb' : (A.image I).Commensurable ⊥ := by
      rw [← Subgroup.commensurable_comap_iff hR, MonoidHom.comap_bot,
        (MonoidHom.ker_eq_bot_iff (D.ι : D.Pi →* A.grp)).2 D.inj]
      exact hb
    have hfin := Subgroup.finite_of_commensurable_bot hb'
    obtain ⟨N, -, hCN, -, -, htf⟩ := tf
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    refine htf x (hCN ⟨ChainObj.le_commensurator_self' _ hx,
      A.image_le_Delta ((arithmeticExt Ω CX hcX).cusps_le I hI) hx⟩) ?_
    haveI : Finite (A.image I) := hfin.to_subtype
    have := isOfFinOrder_of_finite (⟨x, hx⟩ : A.image I)
    exact (A.image I).subtype.isOfFinOrder this
  · rw [Subgroup.Commensurable.eq hJc, commensurator_inf_of_mem_arithCusps Ω D.Y D.hY hJ]
    exact hJ

end CurvesJacobian.Cusp.GeomModel
