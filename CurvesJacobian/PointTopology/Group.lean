/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.PointTopology.Local
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.GroupTheory.OrderOfElement

/-!
# `⋂_N N · A(L) = 0` for proper commutative group schemes over local fields

Let `L` be a proper ultrametric normed field (e.g. a finite extension of `ℚ_p`), `S` an affine
scheme, `s₀ : Spec L ⟶ S`, and `A` a commutative group scheme over `S` which is proper (e.g. an
abelian variety). The group `A(L) = Hom_S(Spec L, A)` with the topology of `L`-points
(`PointTopology/Basic.lean`) is a compact Hausdorff topological group in which every neighbourhood
of `1` contains a clopen neighbourhood (`Proper.lean`, `Local.lean`), i.e. a profinite group.
Every open subgroup has finite index `M`, and `x = y^M` lies in it; hence:

* **`eq_one_of_forall_pow_eq_of_clopen`** (abstract form): in a compact Hausdorff commutative
  topological group with a basis of clopen neighbourhoods of `1`, the only element with `N`-th
  roots for all `N ≥ 1` is `1`;
* **`GroupScheme.eq_one_of_forall_pow_eq`**: `⋂_{N ≥ 1} A(L)^N = 1`.

This is the statement "`⋂_N N · A(K) = 0`" of [AbsTopIII] Rem. 1.5.4(i)
(`Topics in Absolute Anabelian Geometry III.txt` l.1909–1919) for abelian varieties over finite
extensions `K` of `ℚ_p`; the paper deduces it from the structure of `A(K)` as an extension of a
finitely generated `ℤ`-module by a compact `p`-adic Lie group. Here only compactness and total
disconnectedness of `A(K)` are used (no `p`-adic logarithm).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Topology Filter Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

noncomputable section

namespace CurvesJacobian.PointTopology

/-- **Profinite commutative groups have no nontrivial infinitely divisible elements.** -/
theorem eq_one_of_forall_pow_eq_of_clopen {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (hcl : ∀ W ∈ 𝓝 (1 : G), ∃ K : Set G, IsClopen K ∧ (1 : G) ∈ K ∧ K ⊆ W) {z : G}
    (hz : ∀ N : ℕ, 0 < N → ∃ y, y ^ N = z) : z = 1 := by
  by_contra hne
  obtain ⟨K, hK, h1K, hKW⟩ := hcl {z}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hK h1K
  haveI : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨y, hy⟩ := hz H.toSubgroup.index (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
  have hzH : z ∈ (H : Set G) := hy ▸ H.toSubgroup.pow_index_mem y
  exact hKW (hH hzH) rfl

section Points

variable {S : Scheme.{u}} (A : Over S) {L : Type u} [NormedField L]
  (s₀ : Spec (CommRingCat.of L) ⟶ S)

/-- The underlying `L`-point of `x ∈ A(L)`. -/
def toPt (x : Over.mk s₀ ⟶ A) : Spec (CommRingCat.of L) ⟶ A.left := x.left

/-- The topology on `A(L) = Hom_S(Spec L, A)` induced from the `L`-points of `A`. -/
abbrev pointsTopology : TopologicalSpace (Over.mk s₀ ⟶ A) :=
  TopologicalSpace.induced (toPt A s₀) inferInstance

lemma range_toPt : Set.range (toPt A s₀) =
    {x : Spec (CommRingCat.of L) ⟶ A.left | x ≫ A.hom = s₀} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Over.w y
  · intro hx
    exact ⟨Over.homMk x hx, rfl⟩

variable [GrpObj A]

lemma toPt_mul (x y : Over.mk s₀ ⟶ A) :
    toPt A s₀ (x * y) = pullback.lift (toPt A s₀ x) (toPt A s₀ y) (x.w.trans y.w.symm) ≫
      μ[A].left := by
  rw [toPt, Hom.mul_def, Over.comp_left, Over.lift_left]
  rfl

lemma toPt_inv (x : Over.mk s₀ ⟶ A) : toPt A s₀ x⁻¹ = toPt A s₀ x ≫ ι[A].left := by
  rw [toPt, Hom.inv_def, Over.comp_left]
  rfl

end Points

section GroupScheme

variable {S : Scheme.{u}} [IsAffine S] (A : Over S) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] {L : Type u} [NormedField L] [IsUltrametricDist L] [ProperSpace L]
  (s₀ : Spec (CommRingCat.of L) ⟶ S)

variable {A}

omit [IsAffine S] [GrpObj A] [IsCommMonObj A] [IsUltrametricDist L] [ProperSpace L] in
lemma valuativeCriterion_of_isProper : ValuativeCriterion A.hom := by
  have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) A.hom := by
    rw [← IsProper.eq_valuativeCriterion]
    infer_instance
  exact h.1.1.1

variable (A)

/-- **`⋂_{N ≥ 1} A(L)^N = 1`** for a proper commutative group scheme `A` over an affine scheme
`S`, with `L` a proper ultrametric normed field and `Spec L ⟶ S`. -/
theorem GroupScheme.eq_one_of_forall_pow_eq (x : Over.mk s₀ ⟶ A)
    (hx : ∀ N : ℕ, 0 < N → ∃ y, y ^ N = x) : x = 1 := by
  letI : TopologicalSpace (Over.mk s₀ ⟶ A) := pointsTopology A s₀
  letI : CommGroup (Over.mk s₀ ⟶ A) := Hom.commGroup
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  haveI : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have hVC := valuativeCriterion_of_isProper (A := A)
  have hind : Topology.IsInducing (toPt A s₀) := ⟨rfl⟩
  have hcont : Continuous (toPt A s₀) := hind.continuous
  -- the map to the fibre `A(L)_{s₀}` is continuous and injective
  have hT2fib := t2Space_fiber (ValuativeCriterion.uniqueness hVC) s₀
  haveI : T2Space (Over.mk s₀ ⟶ A) := by
    let F : (Over.mk s₀ ⟶ A) → {x : Spec (CommRingCat.of L) ⟶ A.left // x ≫ A.hom = s₀} :=
      fun x ↦ ⟨toPt A s₀ x, Over.w x⟩
    have hF : Function.Injective F := fun x y h ↦ by
      ext1
      exact congrArg Subtype.val h
    exact T2Space.of_injective_continuous hF (hcont.subtype_mk _)
  haveI : CompactSpace (Over.mk s₀ ⟶ A) := by
    refine ⟨?_⟩
    rw [hind.isCompact_iff, Set.image_univ, range_toPt]
    exact isCompact_fiber (ValuativeCriterion.existence hVC) s₀
  haveI : IsTopologicalGroup (Over.mk s₀ ⟶ A) := by
    refine { continuous_mul := ?_, continuous_inv := ?_ }
    · refine continuous_induced_rng.mpr ?_
      have hpair : Continuous fun p : (Over.mk s₀ ⟶ A) × (Over.mk s₀ ⟶ A) ↦
          (⟨(toPt A s₀ p.1, toPt A s₀ p.2), p.1.w.trans p.2.w.symm⟩ :
            {q : (Spec (CommRingCat.of L) ⟶ A.left) × (Spec (CommRingCat.of L) ⟶ A.left) //
              q.1 ≫ A.hom = q.2 ≫ A.hom}) :=
        ((hcont.comp continuous_fst).prodMk (hcont.comp continuous_snd)).subtype_mk _
      have := (continuous_comp (L := L) μ[A].left).comp
        ((continuous_pullbackLift A.hom A.hom).comp hpair)
      convert this using 1
      funext p
      exact toPt_mul A s₀ p.1 p.2
    · refine continuous_induced_rng.mpr ?_
      convert (continuous_comp (L := L) ι[A].left).comp hcont using 1
      funext x
      exact toPt_inv A s₀ x
  refine eq_one_of_forall_pow_eq_of_clopen (fun W hW ↦ ?_) hx
  rw [hind.nhds_eq_comap] at hW
  obtain ⟨W', hW', hW'W⟩ := hW
  obtain ⟨K, hKo, h1K, hKW', hKc⟩ := exists_isOpen_isCompact s₀ hW' (f := A.hom)
  refine ⟨toPt A s₀ ⁻¹' K, ⟨?_, hKo.preimage hcont⟩, h1K,
    fun x hx ↦ hW'W (hKW' hx)⟩
  refine IsCompact.isClosed ?_
  rw [hind.isCompact_iff, Set.image_preimage_eq_inter_range, range_toPt]
  exact hKc

end GroupScheme

end CurvesJacobian.PointTopology
