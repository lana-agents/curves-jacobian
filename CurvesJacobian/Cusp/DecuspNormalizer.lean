/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelStep

/-!
# The stabiliser of the torsion-free subgroup of a `•` operation (MR8.5, option (A4))

[AbsTopI] Definition 4.2 (iii)(c) and Lemma 4.1 (v) (`Topics in Absolute Anabelian Geometry
I.txt` l.2765–2770, proof l.2810–2818): the cuspidal decomposition group `C` of an operation of
type `•` lies in a torsion-free subgroup `J ⊆ Δ_A` which is open and normal **in `Δ_A`**
(`Belyi.Anabelian.ChainObj.InTorsionFreeNormalOpen`). Its stabiliser under conjugation by `A`
(the normaliser `N_A(J)`) is an open subgroup of `A` containing `Δ_A`
(`Belyi.Anabelian.ChainObj.isOpen_normalizer_of_isOpen_subgroupOf`,
`Belyi.Anabelian.ChainObj.Delta_le_normalizer`): this is the open subgroup `A' ⊆ A` in which the
geometric model of the `•` step is normal (lead decision for (A4)).

Proof of openness: `J = Δ ∩ W` for an open `W ⊆ A`; an open normal `T ⊆ W` normalises `J`, since
for `t ∈ T`, `j ∈ J` the commutator `j⁻¹ t j t⁻¹` lies in `T ∩ Δ ⊆ J`.
-/

open Pi1.Profinite

universe u

namespace Belyi.Anabelian

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The normaliser of a subgroup `J ⊆ Δ` which is open and normal in a normal subgroup `Δ` is
open.** -/
theorem isOpen_normalizer_of_isOpen_subgroupOf {Δ J : Subgroup G} [Δ.Normal] (hJΔ : J ≤ Δ)
    (hJ : IsOpen ((J.subgroupOf Δ : Subgroup Δ) : Set Δ)) :
    IsOpen (Subgroup.normalizer (J : Set G) : Set G) := by
  obtain ⟨W, hW, hWJ⟩ := isOpen_induced_iff.1 hJ
  have h1 : (1 : G) ∈ W := by
    have : (1 : Δ) ∈ ((J.subgroupOf Δ : Subgroup Δ) : Set Δ) := one_mem _
    rw [← hWJ] at this
    exact this
  obtain ⟨T₀, hT⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  let T : Subgroup G := T₀.toSubgroup
  haveI : T.Normal := T₀.isNormal'
  have hTo : IsOpen (T : Set G) := T₀.isOpen'
  have hTW : (T : Set G) ⊆ W := hT
  have hTΔ : ∀ x ∈ T, x ∈ Δ → x ∈ J := fun x hxT hxΔ ↦ by
    have : (⟨x, hxΔ⟩ : Δ) ∈ ((J.subgroupOf Δ : Subgroup Δ) : Set Δ) := by
      rw [← hWJ]
      exact hTW hxT
    exact this
  have key : ∀ t ∈ T, ∀ j ∈ J, t * j * t⁻¹ ∈ J := fun t ht j hj ↦ by
    have hc : j⁻¹ * (t * j * t⁻¹) ∈ J := by
      refine hTΔ _ ?_ ?_
      · have : j⁻¹ * t * j ∈ T := by
          simpa [mul_assoc] using (inferInstance : T.Normal).conj_mem t ht j⁻¹
        simpa [mul_assoc] using T.mul_mem this (T.inv_mem ht)
      · exact Δ.mul_mem (Δ.inv_mem (hJΔ hj)) ((inferInstance : Δ.Normal).conj_mem _ (hJΔ hj) t)
    simpa [mul_assoc] using J.mul_mem hj hc
  refine Subgroup.isOpen_mono (H₁ := T) (fun t ht ↦ ?_) hTo
  refine Subgroup.mem_set_normalizer_iff.2 fun j ↦ ⟨key t ht j, fun hj ↦ ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hj
  simpa [mul_assoc] using this

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- A subgroup normal in `Δ` is normalised by `Δ`. -/
theorem le_normalizer_of_forall_conj_mem {Δ J : Subgroup G}
    (hJ : ∀ d ∈ Δ, ∀ n ∈ J, d * n * d⁻¹ ∈ J) : Δ ≤ Subgroup.normalizer (J : Set G) := by
  intro d hd
  refine Subgroup.mem_set_normalizer_iff.2 fun n ↦ ⟨hJ d hd n, fun h ↦ ?_⟩
  have := hJ d⁻¹ (Δ.inv_mem hd) _ h
  simpa [mul_assoc] using this

end Group

namespace ChainObj

variable {E : CuspidalExt.{u}} (A : ChainObj E)

/-- **The stabiliser `N_A(J)` of the torsion-free subgroup of a `•` operation is open.** -/
theorem isOpen_normalizer_of_inTorsionFreeNormalOpen {N : Subgroup A.grp} (hNΔ : N ≤ A.Delta)
    (hN : IsOpen ((N.subgroupOf A.Delta : Subgroup A.Delta) : Set A.Delta)) :
    IsOpen (Subgroup.normalizer (N : Set A.grp) : Set A.grp) :=
  haveI : A.Delta.Normal := MonoidHom.normal_ker _
  isOpen_normalizer_of_isOpen_subgroupOf hNΔ hN

/-- **`Δ_A ⊆ N_A(J)`.** -/
theorem Delta_le_normalizer {N : Subgroup A.grp}
    (hN : ∀ d ∈ A.Delta, ∀ n ∈ N, d * n * d⁻¹ ∈ N) :
    A.Delta ≤ Subgroup.normalizer (N : Set A.grp) :=
  le_normalizer_of_forall_conj_mem hN

/-- **The data of `InTorsionFreeNormalOpen C`, with the open stabiliser `A' = N_A(J) ⊇ Δ_A`.** -/
theorem InTorsionFreeNormalOpen.exists_normalizer {C : Subgroup A.grp}
    (h : A.InTorsionFreeNormalOpen C) :
    ∃ N : Subgroup A.grp, N ≤ A.Delta ∧ C ≤ N ∧ (∀ n ∈ N, IsOfFinOrder n → n = 1) ∧
      IsOpen (Subgroup.normalizer (N : Set A.grp) : Set A.grp) ∧
      A.Delta ≤ Subgroup.normalizer (N : Set A.grp) := by
  obtain ⟨N, hNΔ, hCN, hconj, hopen, htf⟩ := h
  exact ⟨N, hNΔ, hCN, htf, A.isOpen_normalizer_of_inTorsionFreeNormalOpen hNΔ hopen,
    A.Delta_le_normalizer hconj⟩

end ChainObj

end Belyi.Anabelian
