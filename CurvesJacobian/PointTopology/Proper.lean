/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.PointTopology.Germ
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Compactness and Hausdorffness of `X(L)` for proper `X`

Let `L` be a proper normed field (e.g. a finite extension of `ℚ_p`), `f : X ⟶ S` a morphism of
schemes and `s₀ : Spec L ⟶ S`. Write `X(L)_{s₀} = {x : Spec L ⟶ X | x ≫ f = s₀}`. Using the
ultrapower description of limits (`Germ.lean`) and the valuative criteria:

* **`isCompact_fiber`**: if `f` satisfies the existence part of the valuative criterion (e.g.
  `f` proper) and `X` is quasi-compact and quasi-separated, `X(L)_{s₀}` is compact;
* **`eq_of_tendsto_fiber`**, **`t2Space_fiber`**: if `f` satisfies the uniqueness part (e.g.
  `f` separated), `S` is affine and `X` quasi-separated, limits of ultrafilters in `X(L)` are
  unique, and `X(L)_{s₀}` is Hausdorff.

This is the input "`A(K)` is a compact `p`-adic Lie group" of [AbsTopIII] Rem. 1.5.4(i)
(`Topics in Absolute Anabelian Geometry III.txt` l.1909–1919) in the form needed for
`⋂_N N · A(K) = 0` (`PointTopology/Group.lean`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Topology Filter Limits

noncomputable section

namespace CurvesJacobian.PointTopology

variable {X Y S : Scheme.{u}} {I : Type u} {𝒰 : Ultrafilter I}
  {L : Type u} [NormedField L]

/-- In a quasi-compact scheme, eventually all members of a family of field-valued points lie in
one affine open. -/
lemma exists_affine_eventually [CompactSpace X] {K : Type u} [Field K]
    (y : I → (Spec (CommRingCat.of K) ⟶ X)) (𝒰 : Ultrafilter I) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ᶠ i in (𝒰 : Filter I), ⊤ ≤ y i ⁻¹ᵁ U := by
  have hcov : ∀ p : X, ∃ U : X.Opens, IsAffineOpen U ∧ p ∈ U := fun p ↦ by
    obtain ⟨U, hU, hpU, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show p ∈ (⊤ : X.Opens) from trivial)
    exact ⟨U, hU, hpU⟩
  choose U hU hpU using hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun p ↦ (U p : Set X))
    (fun p ↦ (U p).isOpen) fun p _ ↦ Set.mem_iUnion.mpr ⟨p, hpU p⟩
  have hmem : (⋃ p ∈ (t : Set X), {i | y i (pt K) ∈ U p}) ∈ 𝒰 :=
    Filter.univ_mem' fun i ↦ by simpa using ht (Set.mem_univ (y i (pt K)))
  obtain ⟨p, -, hp⟩ := (Ultrafilter.finite_biUnion_mem_iff t.finite_toSet).mp hmem
  exact ⟨U p, hU p, Filter.mem_of_superset (Ultrafilter.mem_coe.mpr hp)
    fun i hi ↦ lands_of_mem _ _ hi⟩

lemma IsGermPt.congr {y y' : I → (Spec (CommRingCat.of L) ⟶ X)}
    {ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X} (hξ : IsGermPt 𝒰 y ξ)
    (h : ∀ᶠ i in (𝒰 : Filter I), y i = y' i) : IsGermPt 𝒰 y' ξ where
  eventually_lands hU hξU := ((hξ.eventually_lands hU hξU).and h).mono fun i ⟨hi, e⟩ ↦ e ▸ hi
  ev_eq hU hξU a := by
    rw [hξ.ev_eq hU hξU]
    exact Filter.Germ.coe_eq.mpr (h.mono fun i e ↦ by simp only [e])

/-- The constant map `L → V`. -/
def constV (𝒰 : Ultrafilter I) (L : Type u) [NormedField L] : L →+* finiteGerms 𝒰 L :=
  (constHom 𝒰 L).codRestrict _ fun c ↦ const_mem_finiteGerms 𝒰 L c

lemma constV_ιV : CommRingCat.ofHom (constV 𝒰 L) ≫ ιV 𝒰 L = CommRingCat.ofHom (constHom 𝒰 L) :=
  rfl

lemma constV_stV [ProperSpace L] : CommRingCat.ofHom (constV 𝒰 L) ≫ stV 𝒰 L = 𝟙 _ := by
  ext c
  exact stdPart_const 𝒰 L c

/-- Morphisms `Spec V ⟶ S` to an affine scheme are determined on `Spec L^𝒰`. -/
lemma eq_of_specMap_ιV_comp [IsAffine S] {g g' : Spec (CommRingCat.of (finiteGerms 𝒰 L)) ⟶ S}
    (h : Spec.map (ιV 𝒰 L) ≫ g = Spec.map (ιV 𝒰 L) ≫ g') : g = g' := by
  have h1 : ⊤ ≤ g ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  have h2 : ⊤ ≤ g' ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  refine ext_of_ev (isAffineOpen_top S) h1 h2 fun a ↦ Subtype.ext ?_
  have e1 := ev_specMap_comp g (ιV 𝒰 L) h1 a
  have e2 := ev_specMap_comp g' (ιV 𝒰 L) h2 a
  simp only [h] at e1
  exact e1.symm.trans e2

/-- The germ point of a family in `X(L)_{s₀}` lies over `s₀`. -/
lemma IsGermPt.comp_eq [QuasiSeparatedSpace S] {f : X ⟶ S} {s₀ : Spec (CommRingCat.of L) ⟶ S}
    {y : I → (Spec (CommRingCat.of L) ⟶ X)} {ξ : Spec (CommRingCat.of (UPow 𝒰 L)) ⟶ X}
    (hξ : IsGermPt 𝒰 y ξ) (hy : ∀ᶠ i in (𝒰 : Filter I), y i ≫ f = s₀) :
    ξ ≫ f = Spec.map (CommRingCat.ofHom (constHom 𝒰 L)) ≫ s₀ :=
  ((hξ.comp f).congr hy).unique (isGermPt_const s₀)

/-! ### Compactness -/

/-- **`X(L)_{s₀}` is compact** for `f` satisfying the existence part of the valuative criterion
(e.g. `f` proper) and `X` quasi-compact and quasi-separated. -/
theorem isCompact_fiber [ProperSpace L] [CompactSpace X] [QuasiSeparatedSpace X]
    [QuasiSeparatedSpace S]
    {f : X ⟶ S} (hf : ValuativeCriterion.Existence f) (s₀ : Spec (CommRingCat.of L) ⟶ S) :
    IsCompact {x : Spec (CommRingCat.of L) ⟶ X | x ≫ f = s₀} := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒱 h𝒱
  obtain ⟨U₀, hU₀, hy⟩ := exists_affine_eventually (fun x ↦ x) 𝒱
  obtain ⟨ξ, hξ, -⟩ := exists_isGermPt (𝒰 := 𝒱) (fun x ↦ x) hU₀ hy
  have hfib : ∀ᶠ x in (𝒱 : Filter _), x ≫ f = s₀ := h𝒱 (Filter.mem_principal_self _)
  have hsq := hξ.comp_eq hfib
  let sq : ValuativeCommSq f :=
    { R := finiteGerms 𝒱 L
      K := UPow 𝒱 L
      i₁ := ξ
      i₂ := Spec.map (CommRingCat.ofHom (constV 𝒱 L)) ≫ s₀
      commSq := ⟨by rw [hsq, ← Category.assoc, ← Spec.map_comp]; rfl⟩ }
  obtain ⟨l⟩ := (hf sq).exists_lift
  refine ⟨Spec.map (stV 𝒱 L) ≫ l.l, ?_, tendsto_of_lift hξ l.l l.fac_left⟩
  change (Spec.map (stV 𝒱 L) ≫ l.l) ≫ f = s₀
  rw [Category.assoc, l.fac_right]
  change Spec.map (stV 𝒱 L) ≫ Spec.map (CommRingCat.ofHom (constV 𝒱 L)) ≫ s₀ = s₀
  rw [← Category.assoc, ← Spec.map_comp, constV_stV, Spec.map_id, Category.id_comp]

/-! ### Uniqueness of limits -/

/-- **Limits in `X(L)` are unique** for `f` satisfying the uniqueness part of the valuative
criterion (e.g. `f` separated), `S` affine and `X` quasi-separated. -/
theorem eq_of_tendsto_fiber [ProperSpace L] [QuasiSeparatedSpace X] [IsAffine S] {f : X ⟶ S}
    (hf : ValuativeCriterion.Uniqueness f)
    (𝒱 : Ultrafilter (Spec (CommRingCat.of L) ⟶ X))
    {x x' : Spec (CommRingCat.of L) ⟶ X} (hx : Tendsto (fun z ↦ z) 𝒱 (𝓝 x))
    (hx' : Tendsto (fun z ↦ z) 𝒱 (𝓝 x')) : x = x' := by
  obtain ⟨U₀, hU₀, -, hxU⟩ := exists_affine_lands x (U := ⊤) (fun _ _ ↦ trivial)
  have hy : ∀ᶠ z in (𝒱 : Filter (Spec (CommRingCat.of L) ⟶ X)), ⊤ ≤ z ⁻¹ᵁ U₀ :=
    ((tendsto_iff.mp hx) U₀ 0 Set.univ isOpen_univ hxU trivial).mono fun _ ⟨h, _⟩ ↦ h
  obtain ⟨ξ, hξ, -⟩ := exists_isGermPt (𝒰 := 𝒱) (fun z ↦ z) hU₀ hy
  obtain ⟨ℓ, hℓ, hℓx⟩ := exists_lift_of_tendsto hξ hx
  obtain ⟨ℓ', hℓ', hℓx'⟩ := exists_lift_of_tendsto hξ hx'
  have hb : ℓ' ≫ f = ℓ ≫ f := eq_of_specMap_ιV_comp (by
    rw [← Category.assoc, ← Category.assoc, hℓ, hℓ'])
  let sq : ValuativeCommSq f :=
    { R := finiteGerms 𝒱 L
      K := UPow 𝒱 L
      i₁ := ξ
      i₂ := ℓ ≫ f
      commSq := ⟨by rw [← Category.assoc]; exact congrArg (· ≫ f) hℓ.symm⟩ }
  have := hf sq
  have e : ℓ = ℓ' := congrArg CommSq.LiftStruct.l
    (Subsingleton.elim (α := sq.commSq.LiftStruct) ⟨ℓ, hℓ, rfl⟩ ⟨ℓ', hℓ', hb⟩)
  rw [← hℓx, ← hℓx', e]

/-- **`X(L)_{s₀}` is Hausdorff** (`f` separated, `S` affine, `X` quasi-separated). -/
theorem t2Space_fiber [ProperSpace L] [QuasiSeparatedSpace X] [IsAffine S] {f : X ⟶ S}
    (hf : ValuativeCriterion.Uniqueness f) (s₀ : Spec (CommRingCat.of L) ⟶ S) :
    T2Space {x : Spec (CommRingCat.of L) ⟶ X // x ≫ f = s₀} := by
  rw [t2_iff_ultrafilter]
  intro x x' 𝒱 hx hx'
  have h1 : Tendsto (fun z ↦ z) (𝒱.map Subtype.val : Filter _) (𝓝 x.1) := by
    rw [Ultrafilter.coe_map]
    exact tendsto_map'_iff.mpr ((continuous_subtype_val.tendsto x).comp hx)
  have h2 : Tendsto (fun z ↦ z) (𝒱.map Subtype.val : Filter _) (𝓝 x'.1) := by
    rw [Ultrafilter.coe_map]
    exact tendsto_map'_iff.mpr ((continuous_subtype_val.tendsto x').comp hx')
  exact Subtype.ext (eq_of_tendsto_fiber hf (𝒱.map Subtype.val) h1 h2)

end CurvesJacobian.PointTopology
