/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Pi1.Mathlib.CategoryTheory.Galois.EssImage
import Pi1.Surface.Commensurator

/-!
# Conjugacy of subgroups of a profinite group from fixed points on finite quotients

Let `G` be a profinite group and `A, B ⊆ G` subgroups with `A` closed. If every open subgroup
`V ⊇ A` contains a conjugate of `B`, then `B` lies in a conjugate of `A`
(`CurvesJacobian.Cusp.exists_conj_mem_of_forall_isOpen`): for each open normal `N` the set of
`g` with `g B g⁻¹ ⊆ N A` is closed and nonempty, these sets are directed, so by compactness some
`g` lies in all of them, and `⋂_N N A = A` for closed `A`.

For a Galois category with fibre functor `F` this reads
(`CurvesJacobian.Cusp.exists_conj_mem_of_fixedPoints`): if, for every object `X`, a fixed point
of `A ⊆ Aut F` on `F X` forces a fixed point of `B` on `F X`, then `B` lies in a conjugate of `A`
(every open subgroup of `Aut F` is the stabiliser of a point,
`CategoryTheory.PreGaloisCategory.exists_obj_stabilizer_eq`).

This is the group-theoretic half of the identification of Galois inertia groups with the closures
of topological loops around punctures: a loop around a puncture fixes a point of the fibre of a
cover as soon as the Galois inertia group does (an unramified point over the puncture lifts the
loop), hence the closure of the loop lies in a conjugate of the inertia group. Since inertia
groups are abelian and the cuspidal inertia groups `Iⱼ` of `Π̂_{g,r+2}` are commensurably
terminal (pi1's `Pi1.SurfaceGroup.commensurator_inertia`), an abelian subgroup containing `Iⱼ` is
`Iⱼ` (`CurvesJacobian.Cusp.eq_inertia_of_inertia_le`).
-/

open CategoryTheory PreGaloisCategory
open scoped Pointwise

namespace CurvesJacobian.Cusp

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- An element outside a closed subgroup `A` of a profinite group lies outside `N ⊔ A` for some
open normal subgroup `N`. -/
lemma exists_openNormalSubgroup_notMem_sup {A : Subgroup G} (hA : IsClosed (A : Set G)) {x : G}
    (hx : x ∉ A) : ∃ N : OpenNormalSubgroup G, x ∉ (N : Subgroup G) ⊔ A := by
  let U : Set G := (x • (A : Set G))ᶜ
  have hUo : IsOpen U := ((Homeomorph.mulLeft x).isClosedMap _ hA).isOpen_compl
  have h1U : (1 : G) ∈ U := by
    refine Set.mem_compl fun ⟨l, hl, (hxl : x * l = 1)⟩ ↦ ?_
    rw [← inv_eq_iff_mul_eq_one] at hxl
    exact hx (inv_mem_iff.mp (hxl ▸ hl))
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  refine ⟨N, fun hx' ↦ ?_⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
  rw [← eq_mul_inv_iff_mul_eq] at hyz
  exact hN (hyz ▸ hy) (mem_leftCoset x (inv_mem_iff.mpr hz))

/-- **Conjugacy from open subgroups.** In a profinite group, if every open subgroup `V ⊇ A`
contains a conjugate `g B g⁻¹` of `B` (`A` closed), then some conjugate of `B` lies in `A`. -/
theorem exists_conj_mem_of_forall_isOpen {A B : Subgroup G} (hA : IsClosed (A : Set G))
    (h : ∀ V : Subgroup G, IsOpen (V : Set G) → A ≤ V → ∃ g : G, ∀ b ∈ B, g * b * g⁻¹ ∈ V) :
    ∃ g : G, ∀ b ∈ B, g * b * g⁻¹ ∈ A := by
  let T : OpenNormalSubgroup G → Set G := fun N ↦
    {g | ∀ b ∈ B, g * b * g⁻¹ ∈ (N : Subgroup G) ⊔ A}
  have hTo (N : OpenNormalSubgroup G) : IsOpen (((N : Subgroup G) ⊔ A : Subgroup G) : Set G) :=
    Subgroup.isOpen_mono le_sup_left N.isOpen'
  have hTc (N : OpenNormalSubgroup G) : IsClosed (T N) := by
    have : T N = ⋂ b ∈ B, (fun g ↦ g * b * g⁻¹) ⁻¹'
        (((N : Subgroup G) ⊔ A : Subgroup G) : Set G) := by
      ext g
      simp [T]
    rw [this]
    exact isClosed_biInter fun b _ ↦ (Subgroup.isClosed_of_isOpen _ (hTo N)).preimage
      (by fun_prop)
  have hTn (N : OpenNormalSubgroup G) : (T N).Nonempty := by
    obtain ⟨g, hg⟩ := h _ (hTo N) le_sup_right
    exact ⟨g, hg⟩
  have hTd : Directed (· ⊇ ·) T := by
    intro N₁ N₂
    refine ⟨N₁ ⊓ N₂, fun g hg b hb ↦ ?_, fun g hg b hb ↦ ?_⟩
    · exact sup_le_sup_right (fun x hx ↦ (inf_le_left : N₁ ⊓ N₂ ≤ N₁) hx) A (hg b hb)
    · exact sup_le_sup_right (fun x hx ↦ (inf_le_right : N₁ ⊓ N₂ ≤ N₂) hx) A (hg b hb)
  haveI : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := (inferInstance : (⊤ : Subgroup G).Normal) }⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hTd hTn
    (fun N ↦ (hTc N).isCompact) hTc
  refine ⟨g, fun b hb ↦ ?_⟩
  by_contra hbA
  obtain ⟨N, hN⟩ := exists_openNormalSubgroup_notMem_sup hA hbA
  exact hN (Set.mem_iInter.1 hg N b hb)

end Group

section Galois

universe u₁ u₂ w

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

/-- **Conjugacy from fixed points.** Let `A, B ⊆ Aut F` be subgroups, `A` closed. If for every
object `X` a fixed point of `A` on `F X` forces a fixed point of `B` on `F X`, then some conjugate
of `B` lies in `A`. -/
theorem exists_conj_mem_of_fixedPoints {A B : Subgroup (Aut F)} (hA : IsClosed (A : Set (Aut F)))
    (h : ∀ (X : C) (x : F.obj X), (∀ σ ∈ A, σ • x = x) → ∃ y : F.obj X, ∀ τ ∈ B, τ • y = y) :
    ∃ g : Aut F, ∀ b ∈ B, g * b * g⁻¹ ∈ A := by
  refine exists_conj_mem_of_forall_isOpen hA fun V hV hAV ↦ ?_
  obtain ⟨X, a, hstab, htrans⟩ := exists_obj_stabilizer_eq F V hV
  obtain ⟨y, hy⟩ := h X a fun σ hσ ↦ (hstab σ).2 (hAV hσ)
  obtain ⟨σ, rfl⟩ := htrans y
  refine ⟨σ⁻¹, fun b hb ↦ (hstab _).1 ?_⟩
  change (σ⁻¹ * b * σ⁻¹⁻¹) • a = a
  rw [inv_inv, mul_smul, mul_smul]
  change σ⁻¹ • b • (σ.hom.app X a) = a
  rw [hy b hb]
  change σ⁻¹ • σ • a = a
  rw [inv_smul_smul]

end Galois

section Surface

open Pi1.SurfaceGroup

/-- **An abelian subgroup containing a cuspidal inertia group is that inertia group.** For a
cusp `j` of `Π̂_{g,r+2}` and a commutative subgroup `A ⊇ Iⱼ`: every `a ∈ A` centralises `Iⱼ`, so
`A` lies in the commensurator of `Iⱼ`, which is `Iⱼ` (`Pi1.SurfaceGroup.commensurator_inertia`). -/
theorem eq_inertia_of_inertia_le {g r : ℕ} (j : Fin (r + 2))
    {A : Subgroup (Pi1.ProfiniteSurfaceGroup g (r + 2))} (hle : inertia j ≤ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = inertia j := by
  refine le_antisymm (fun a ha ↦ ?_) hle
  rw [← commensurator_inertia (g := g) j, Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct a • inertia (g := g) j = inertia j := by
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hcomm a ha y (hle hy), mul_assoc,
        mul_inv_cancel, mul_one]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hcomm a ha x (hle hx), mul_assoc,
        mul_inv_cancel, mul_one]
  rw [this]

end Surface

end CurvesJacobian.Cusp
