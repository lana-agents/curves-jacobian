/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Galois.ChartOfOpen
import Belyi.Anabelian.LocAn
import Belyi.Dimension

/-!
# Runs of fillings `W = U₀ ⊆ U₁ ⊆ ⋯ ⊆ U_r = U`

For opens `W ⊆ U_mid ⊆ U` of a scheme with `U ∖ W` finite and consisting of closed points,
`CurvesJacobian.Cusp.exists_fillSeq` produces a run of opens `W = U₀ ⊆ U₁ ⊆ ⋯ ⊆ U_r = U`
adding one point `x_i` at a time and passing through `U_j = U_mid`; this is the shape of the
fields `UW, hUW0, hleW, hmonoW, xW, hxUW, hxUW', hxW` of `CurvesJacobian.Cusp.BelyiData`.

We also record three facts on curves over a perfect field:

* `CurvesJacobian.Cusp.isClosed_singleton_of_not_mem`: a point outside a nonempty open is closed;
* `CurvesJacobian.Cusp.cuspDegree_anti`: the cusp degree is antitone in the open;
* `CurvesJacobian.Cusp.isAffineOpen_of_isCurveOver`: a nonempty open with nonempty finite
  complement is affine.
-/

open AlgebraicGeometry Belyi Belyi.Anabelian

universe u

namespace CurvesJacobian.Cusp

section Topology

variable {X : Scheme.{u}}

/-- Adding to an open `W ⊆ U` a set `S ⊆ U ∖ W` gives an open, if `U ∖ W` is a finite set of
closed points: `W ∪ S = U ∖ ((U ∖ W) ∖ S)`. -/
theorem isOpen_union_of_subset_diff (W U : X.Opens) (hWU : W ≤ U) {S : Set X}
    (hS : S ⊆ (U : Set X) \ W) (hfin : ((U : Set X) \ W).Finite)
    (hcl : ∀ x ∈ (U : Set X) \ W, IsClosed ({x} : Set X)) : IsOpen ((W : Set X) ∪ S) := by
  have heq : (W : Set X) ∪ S = (U : Set X) \ (((U : Set X) \ W) \ S) := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact ⟨SetLike.coe_subset_coe.2 hWU hy, fun h ↦ h.1.2 hy⟩
      · exact ⟨(hS hy).1, fun h ↦ h.2 hy⟩
    · rintro ⟨hyU, hy⟩
      by_contra h
      simp only [Set.mem_union, not_or] at h
      exact hy ⟨⟨hyU, h.1⟩, h.2⟩
  rw [heq]
  refine U.isOpen.sdiff ?_
  have hF : (((U : Set X) \ W) \ S).Finite := hfin.subset Set.sdiff_subset
  have := hF.isClosed_biUnion (f := fun x ↦ ({x} : Set X)) fun x hx ↦ hcl x hx.1
  rwa [Set.biUnion_of_singleton] at this

/-- **Runs of fillings along an enumeration.** If `e : Fin r → X` enumerates `U ∖ W` without
repetition (a finite set of closed points), the opens `U_i = W ∪ {e m | m < i}` form a run
`W = U₀ ⊆ ⋯ ⊆ U_r = U` with `U_{i+1} ∖ U_i = {e i}`. -/
theorem exists_fillSeq_of_enum (W U : X.Opens) (hWU : W ≤ U) (hfin : ((U : Set X) \ W).Finite)
    (hcl : ∀ x ∈ (U : Set X) \ W, IsClosed ({x} : Set X)) {r : ℕ} (e : Fin r → X)
    (he : Function.Injective e) (hrange : Set.range e = (U : Set X) \ W) :
    ∃ UW : Fin (r + 1) → X.Opens,
      (∀ i, (UW i : Set X) = (W : Set X) ∪ e '' {m | (m : ℕ) < i}) ∧
      UW 0 = W ∧ UW (Fin.last r) = U ∧
      (∀ i, W ≤ UW i) ∧ (∀ i, UW i ≤ U) ∧ (∀ i : Fin r, UW i.castSucc ≤ UW i.succ) ∧
      (∀ i, e i ∈ UW i.succ) ∧ (∀ i, e i ∉ UW i.castSucc) ∧
      (∀ i, (UW i.succ : Set X) \ UW i.castSucc ⊆ {e i}) := by
  have hS : ∀ i : ℕ, e '' {m | (m : ℕ) < i} ⊆ (U : Set X) \ W := fun _ ↦
    (Set.image_subset_range _ _).trans hrange.subset
  let UW : Fin (r + 1) → X.Opens := fun i ↦
    ⟨(W : Set X) ∪ e '' {m | (m : ℕ) < i},
      isOpen_union_of_subset_diff W U hWU (hS i) hfin hcl⟩
  have hUW : ∀ i, (UW i : Set X) = (W : Set X) ∪ e '' {m | (m : ℕ) < i} := fun _ ↦ rfl
  have hmem : ∀ i y, y ∈ UW i ↔ y ∈ (W : Set X) ∪ e '' {m | (m : ℕ) < i} := fun _ _ ↦ Iff.rfl
  have hei : ∀ i, e i ∈ (U : Set X) \ W := fun i ↦ hrange ▸ Set.mem_range_self i
  refine ⟨UW, hUW, ?_, ?_, fun _ ↦ SetLike.coe_subset_coe.1 Set.subset_union_left,
    fun i ↦ SetLike.coe_subset_coe.1
      (Set.union_subset (SetLike.coe_subset_coe.2 hWU) ((hS i).trans Set.sdiff_subset)),
    fun i ↦ SetLike.coe_subset_coe.1 (Set.union_subset_union_right _
      (Set.image_mono fun m (hm : (m : ℕ) < i.castSucc) ↦
        show (m : ℕ) < i.succ by simp only [Fin.val_castSucc, Fin.val_succ] at hm ⊢; omega)),
    fun i ↦ (hmem _ _).2 (Or.inr ⟨i, by simp, rfl⟩), fun i h ↦ ?_, fun i y hy ↦ ?_⟩
  · apply TopologicalSpace.Opens.ext
    rw [hUW]
    simp
  · apply TopologicalSpace.Opens.ext
    rw [hUW]
    have : {m : Fin r | (m : ℕ) < (Fin.last r : ℕ)} = Set.univ :=
      Set.eq_univ_of_forall fun m ↦ m.2
    rw [this, Set.image_univ, hrange]
    exact Set.union_sdiff_cancel (SetLike.coe_subset_coe.2 hWU)
  · rcases (hmem _ _).1 h with h | ⟨m, hm, hme⟩
    · exact (hei i).2 h
    · obtain rfl := he hme
      simp at hm
  · obtain ⟨hy1, hy2⟩ := hy
    rcases (hmem _ _).1 hy1 with hy1 | ⟨m, hm, rfl⟩
    · exact absurd ((hmem _ _).2 (Or.inl hy1)) hy2
    · rcases eq_or_ne m i with rfl | hmi
      · rfl
      · refine absurd ((hmem _ _).2 (Or.inr ⟨m, ?_, rfl⟩)) hy2
        have := Fin.val_ne_of_ne hmi
        simp only [Set.mem_setOf_eq, Fin.val_succ] at hm
        simp only [Set.mem_setOf_eq, Fin.val_castSucc]
        omega

/-- **Runs of fillings through an intermediate open.** For opens `W ⊆ U_mid ⊆ U` with `U ∖ W`
a finite set of closed points there is a run `W = U₀ ⊆ U₁ ⊆ ⋯ ⊆ U_r = U` with
`U_{i+1} ∖ U_i = {x_i}`, `x_i ∉ U_i`, and `U_j = U_mid` for some `j ≤ r`. -/
theorem exists_fillSeq (W Umid U : X.Opens) (hWm : W ≤ Umid) (hmU : Umid ≤ U)
    (hfin : ((U : Set X) \ W).Finite) (hcl : ∀ x ∈ (U : Set X) \ W, IsClosed ({x} : Set X)) :
    ∃ (r j : ℕ) (hj : j ≤ r) (UW : Fin (r + 1) → X.Opens) (x : Fin r → X),
      UW 0 = W ∧ UW (Fin.last r) = U ∧ UW ⟨j, Nat.lt_succ_of_le hj⟩ = Umid ∧
      (∀ i, W ≤ UW i) ∧ (∀ i, UW i ≤ U) ∧ (∀ i : Fin r, UW i.castSucc ≤ UW i.succ) ∧
      (∀ i, x i ∈ UW i.succ) ∧ (∀ i, x i ∉ UW i.castSucc) ∧
      (∀ i, (UW i.succ : Set X) \ UW i.castSucc ⊆ {x i}) := by
  classical
  have hWm' : (W : Set X) ⊆ Umid := SetLike.coe_subset_coe.2 hWm
  have hmU' : (Umid : Set X) ⊆ U := SetLike.coe_subset_coe.2 hmU
  have hA : ((Umid : Set X) \ W).Finite := hfin.subset (Set.sdiff_subset_sdiff_left hmU')
  have hB : ((U : Set X) \ Umid).Finite := hfin.subset (Set.sdiff_subset_sdiff_right hWm')
  set a := hA.toFinset.card
  set b := hB.toFinset.card
  let f : Fin a → X := fun i ↦ (hA.toFinset.equivFin.symm i : X)
  let g : Fin b → X := fun i ↦ (hB.toFinset.equivFin.symm i : X)
  have hf : ∀ i, f i ∈ (Umid : Set X) \ W := fun i ↦
    hA.mem_toFinset.1 (hA.toFinset.equivFin.symm i).2
  have hg : ∀ i, g i ∈ (U : Set X) \ Umid := fun i ↦
    hB.mem_toFinset.1 (hB.toFinset.equivFin.symm i).2
  have hfi : Function.Injective f := fun i j h ↦
    hA.toFinset.equivFin.symm.injective (Subtype.ext h)
  have hgi : Function.Injective g := fun i j h ↦
    hB.toFinset.equivFin.symm.injective (Subtype.ext h)
  let e : Fin (a + b) → X := Fin.append f g
  have he : Function.Injective e :=
    Fin.append_injective_iff.2 ⟨hfi, hgi, fun i j h ↦ (hg j).2 (h ▸ (hf i).1)⟩
  have hrange : Set.range e = (U : Set X) \ W := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      induction m using Fin.addCases with
      | left i => simpa [e] using ⟨hmU' (hf i).1, (hf i).2⟩
      | right i => simpa [e] using ⟨(hg i).1, fun h ↦ (hg i).2 (hWm' h)⟩
    · intro hy
      by_cases hym : y ∈ (Umid : Set X)
      · refine ⟨Fin.castAdd b (hA.toFinset.equivFin ⟨y, hA.mem_toFinset.2 ⟨hym, hy.2⟩⟩), ?_⟩
        simp [e, f]
      · refine ⟨Fin.natAdd a (hB.toFinset.equivFin ⟨y, hB.mem_toFinset.2 ⟨hy.1, hym⟩⟩), ?_⟩
        simp [e, g]
  obtain ⟨UW, hUW, h0, hlast, hle, hleU, hmono, hx1, hx2, hx3⟩ :=
    exists_fillSeq_of_enum W U (hWm.trans hmU) hfin hcl e he hrange
  refine ⟨a + b, a, Nat.le_add_right a b, UW, e, h0, hlast, ?_, hle, hleU, hmono, hx1, hx2,
    hx3⟩
  apply TopologicalSpace.Opens.ext
  rw [hUW]
  have himg : e '' {m | (m : ℕ) < ((⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩ :
      Fin (a + b + 1)) : ℕ)} = (Umid : Set X) \ W := by
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      induction m using Fin.addCases with
      | left i => simpa [e] using hf i
      | right i => simp at hm
    · intro hy
      exact ⟨Fin.castAdd b (hA.toFinset.equivFin ⟨y, hA.mem_toFinset.2 hy⟩), by simp,
        by simp [e, f]⟩
  rw [himg]
  exact Set.union_sdiff_cancel hWm'

end Topology

section Curve

variable {k : Type u} [Field k]

/-- **A point outside a nonempty open of a curve is closed** (it is not the generic point, and
the stalks of a curve over a perfect field have dimension `≤ 1`). -/
theorem isClosed_singleton_of_not_mem [PerfectField k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsCurveOver k X] (U : X.Opens) (hU : (U : Set X).Nonempty)
    {x : X} (hx : x ∉ U) : IsClosed ({x} : Set X) := by
  haveI := IsCurveOver.isIntegral k X
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  exact isClosed_singleton_of_ne_genericPoint (krullDimLE_one_stalk_of_isCurveOver k X)
    fun h ↦ hx (h ▸ hgen)

/-- **The cusp degree is antitone in the open**: `U ⊆ U'` (with `X ∖ U` finite) gives
`Σ_{c ∉ U'} [κ(c) : k] ≤ Σ_{c ∉ U} [κ(c) : k]`. -/
theorem cuspDegree_anti {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {U U' : X.Opens} (h : U ≤ U') (hfin : (U : Set X)ᶜ.Finite) :
    Anabelian.cuspDegree k X U' ≤ Anabelian.cuspDegree k X U := by
  have hsub : (U' : Set X)ᶜ ⊆ (U : Set X)ᶜ :=
    Set.compl_subset_compl.2 (SetLike.coe_subset_coe.2 h)
  have hfin' : (U' : Set X)ᶜ.Finite := hfin.subset hsub
  unfold Anabelian.cuspDegree
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Finset.sum_le_sum_of_subset (Set.Finite.toFinset_subset_toFinset.2 hsub)

/-- **A nonempty open of a curve with nonempty finite complement is affine** (it is a chart
`π⁻¹ D₊(X₁)` of a rational function with poles exactly at the complement,
`CurvesJacobian.exists_chartOne_eq`). -/
theorem isAffineOpen_of_isCurveOver [PerfectField k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsCurveOver k X] (U : X.Opens) (hU : (U : Set X).Nonempty)
    (hfin : (U : Set X)ᶜ.Finite) (hc : (U : Set X)ᶜ.Nonempty) : IsAffineOpen U := by
  haveI := IsCurveOver.isIntegral k X
  haveI : Nonempty U := hU.to_subtype
  have hne : U ≠ ⊤ := fun h ↦ by
    obtain ⟨x, hx⟩ := hc
    exact hx (h ▸ trivial)
  obtain ⟨τ, hτ, hU'⟩ := exists_chartOne_eq k U hfin hne
  rw [hU']
  exact isAffineOpen_chartOne hτ

end Curve

end CurvesJacobian.Cusp
