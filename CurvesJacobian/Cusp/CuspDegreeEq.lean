/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspCount

/-!
# The number of geometric cusps equals the number of cusps after base change

Let `k ⊆ Ω` be fields of characteristic zero with `Ω` algebraically closed, `X` a scheme locally
of finite type over `k`, and `U ⊆ X` an open with finite complement whose base change
`U_Ω ⊆ X_Ω` also has finite complement. Then

  `Σ_{c ∉ U} [κ(c) : k] = #(X_Ω ∖ U_Ω)`

(`CurvesJacobian.Cusp.cuspDegree_eq_card_compl`, `CurvesJacobian.Cusp.card_compl_eq_cuspDegree`).

The inequality `≤` is `CurvesJacobian.Cusp.cuspDegree_le_card_compl`. For the converse we show that
`(c, σ) ↦ geomPoint c σ` is onto `X_Ω ∖ U_Ω`:

* a point of a finite closed subset of a Jacobson space is closed
  (`CurvesJacobian.Cusp.isClosed_singleton_of_mem_finite`), so every `y ∈ X_Ω ∖ U_Ω` is a closed
  point, hence an `Ω`-rational point `Spec Ω ⟶ X_Ω` (Mathlib's `pointOfClosedPoint`), which is
  `geomPoint c σ` for `c = fst y` and the induced `k`-embedding `σ : κ(c) → Ω`
  (`CurvesJacobian.Cusp.exists_geomPoint_eq`);
* every `c ∉ U` is a closed point of `X`, so `κ(c)` is finite over `k`
  (`CurvesJacobian.Cusp.finite_residueField`) and `#Hom_k(κ(c), Ω) = [κ(c) : k]`.

For a curve `X` over `k` and a nonempty open `U` both finiteness hypotheses are automatic
(`CurvesJacobian.Cusp.card_compl_eq_cuspDegree_of_isCurveOver`).
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi Belyi.Anabelian Module

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- In a Jacobson space, every point of a finite closed subset is a closed point. -/
lemma isClosed_singleton_of_mem_finite {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    {Z : Set T} (hZ : IsClosed Z) (hfin : Z.Finite) {y : T} (hy : y ∈ Z) : IsClosed {y} := by
  have hsub : closure {y} ⊆ Z := closure_minimal (Set.singleton_subset_iff.mpr hy) hZ
  have hcl : IsClosed (closure {y} ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closure {y} ∩ closedPoints T)]
    exact ((hfin.subset hsub).subset Set.inter_subset_left).isClosed_biUnion fun x hx ↦ hx.2
  have h := closure_inter_closedPoints (X := T) (isClosed_closure (s := {y}))
  rw [hcl.closure_eq] at h
  have hy' : y ∈ closure {y} ∩ closedPoints T := by
    rw [h]; exact subset_closure (Set.mem_singleton y)
  exact hy'.2

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The residue field of a closed point of a scheme locally of finite type over `k` is finite
over `k`. -/
lemma finite_residueField [LocallyOfFiniteType (X ↘ Spec (.of k))] {c : X} (hc : IsClosed {c}) :
    letI := Anabelian.residueFieldAlgebra k X c
    Module.Finite k (X.residueField c) := by
  letI := Anabelian.residueFieldAlgebra k X c
  have := isClosed_singleton_iff_isClosedImmersion.mp hc
  have h := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField c ≫ (X ↘ Spec (.of k)))).mpr inferInstance
  rw [fromSpecResidueField_comp_structure, IsFinite.SpecMap_iff] at h
  exact RingHom.finite_algebraMap.mp h

/-- **Every closed point of `X_Ω` is a `geomPoint`.** -/
lemma exists_geomPoint_eq [IsAlgClosed Ω]
    [LocallyOfFiniteType (pullback.snd (X ↘ Spec (.of k)) (specAlgebraMap k Ω))]
    (y : baseChange k Ω X) (hy : IsClosed {y}) :
    ∃ (c : X) (σ : ResEmb k Ω X c), geomPoint k Ω c σ (IsLocalRing.closedPoint Ω) = y := by
  let f : Spec (.of Ω) ⟶ baseChange k Ω X := pointOfClosedPoint (pullback.snd _ _) y hy
  have hf : f ≫ pullback.snd _ _ = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hfy : f (IsLocalRing.closedPoint Ω) = y := pointOfClosedPoint_apply _ _ _ _
  let g : Spec (.of Ω) ⟶ X := f ≫ pullback.fst _ _
  have hg0 := (Scheme.SpecToEquivOfField Ω X).symm_apply_apply g
  generalize Scheme.SpecToEquivOfField Ω X g = p at hg0
  obtain ⟨c, τ⟩ := p
  have hg : Spec.map τ ≫ X.fromSpecResidueField c = g := hg0
  letI := Anabelian.residueFieldAlgebra k X c
  have h1 : g ≫ (X ↘ Spec (.of k)) = specAlgebraMap k Ω := by
    simp only [g, Category.assoc, pullback.condition, reassoc_of% hf]
  rw [← hg, Category.assoc, fromSpecResidueField_comp_structure, ← Spec.map_comp,
    specAlgebraMap] at h1
  have hcomm : τ.hom.comp (algebraMap k (X.residueField c)) = algebraMap k Ω :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  let σ : ResEmb k Ω X c := ⟨τ.hom, fun r ↦ RingHom.congr_fun hcomm r⟩
  have hgeom : geomPoint k Ω c σ = f := by
    apply pullback.hom_ext
    · rw [geomPoint_fst]
      exact hg
    · rw [geomPoint_snd, hf]
  exact ⟨c, σ, by rw [hgeom, hfy]⟩

/-- **`Σ_{c ∉ U} [κ(c) : k] = #(X_Ω ∖ U_Ω)`.** -/
theorem cuspDegree_eq_card_compl [CharZero k] [IsAlgClosed Ω]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite)
    (hfin' : ((baseChangeOpen k Ω U : (baseChange k Ω X).Opens) : Set (baseChange k Ω X))ᶜ.Finite) :
    Anabelian.cuspDegree k X U =
      Nat.card ((baseChangeOpen k Ω U : Set (baseChange k Ω X))ᶜ : Set _) := by
  classical
  haveI := hfin'.to_subtype
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  haveI : JacobsonSpace (baseChange k Ω X) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (X ↘ Spec (.of k)) (specAlgebraMap k Ω))
  let S := hfin.toFinset
  let F : (Σ c : S, ResEmb k Ω X c.1) →
      ((baseChangeOpen k Ω U : Set (baseChange k Ω X))ᶜ : Set _) := fun cσ ↦
    ⟨geomPoint k Ω cσ.1.1 cσ.2 (IsLocalRing.closedPoint Ω), by
      have h := hfin.mem_toFinset.mp cσ.1.2
      change geomPoint k Ω cσ.1.1 cσ.2 (IsLocalRing.closedPoint Ω) ∉
        pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω) ⁻¹ᵁ U
      rw [Scheme.Hom.mem_preimage, fst_geomPoint_apply]
      exact h⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨c₁, h₁⟩, σ₁⟩ ⟨⟨c₂, h₂⟩, σ₂⟩ h
    have := geomPoint_injective k Ω (X := X) (a₁ := ⟨c₁, σ₁⟩) (a₂ := ⟨c₂, σ₂⟩)
      (congrArg Subtype.val h)
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj this
    cases eq_of_heq h'
    rfl
  have hFs : Function.Surjective F := by
    rintro ⟨y, hy⟩
    have hyc : IsClosed {y} :=
      isClosed_singleton_of_mem_finite (baseChangeOpen k Ω U).isOpen.isClosed_compl hfin' hy
    obtain ⟨c, σ, rfl⟩ := exists_geomPoint_eq k Ω y hyc
    have hc : c ∈ S := by
      rw [Set.Finite.mem_toFinset]
      intro hcU
      apply hy
      change _ ∈ pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω) ⁻¹ᵁ U
      rw [Scheme.Hom.mem_preimage, fst_geomPoint_apply]
      exact hcU
    exact ⟨⟨⟨c, hc⟩, σ⟩, rfl⟩
  haveI : Finite (Σ c : S, ResEmb k Ω X c.1) := Finite.of_injective F hF
  haveI : ∀ c : S, Finite (ResEmb k Ω X c.1) := fun c ↦
    Finite.of_injective (fun σ : ResEmb k Ω X c.1 ↦ (⟨c, σ⟩ : Σ c : S, ResEmb k Ω X c.1))
      (fun _ _ h ↦ by simpa using h)
  have hdeg : ∀ c ∈ S, Anabelian.pointDegree k X c = Nat.card (ResEmb k Ω X c) := by
    intro c hc
    have hcl : IsClosed {c} :=
      isClosed_singleton_of_mem_finite U.isOpen.isClosed_compl hfin (hfin.mem_toFinset.mp hc)
    letI := Anabelian.residueFieldAlgebra k X c
    haveI := finite_residueField k hcl
    haveI : Algebra.IsSeparable k (X.residueField c) := inferInstance
    rw [Anabelian.pointDegree, ← AlgHom.card k (X.residueField c) Ω, Fintype.card_eq_nat_card]
  rw [Anabelian.cuspDegree, finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ∑ c ∈ S, Anabelian.pointDegree k X c = ∑ c ∈ S, Nat.card (ResEmb k Ω X c) :=
        Finset.sum_congr rfl hdeg
    _ = ∑ c : S, Nat.card (ResEmb k Ω X c.1) := (Finset.sum_coe_sort S _).symm
    _ = Nat.card (Σ c : S, ResEmb k Ω X c.1) := Nat.card_sigma.symm
    _ = _ := Nat.card_congr (Equiv.ofBijective F ⟨hF, hFs⟩)

/-- **`#(X_Ω ∖ U_Ω) = Σ_{c ∉ U} [κ(c) : k]`.** -/
theorem card_compl_eq_cuspDegree [CharZero k] [IsAlgClosed Ω]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite)
    (hfin' : ((baseChangeOpen k Ω U : (baseChange k Ω X).Opens) : Set (baseChange k Ω X))ᶜ.Finite) :
    Nat.card ((baseChangeOpen k Ω U : Set (baseChange k Ω X))ᶜ : Set _) =
      Anabelian.cuspDegree k X U :=
  (cuspDegree_eq_card_compl k Ω U hfin hfin').symm

/-- **For a curve `X` over `k` and a nonempty open `U`: `#(X_Ω ∖ U_Ω) = Σ_{c ∉ U} [κ(c) : k]`.** -/
theorem card_compl_eq_cuspDegree_of_isCurveOver [CharZero k] [IsAlgClosed Ω] [IsCurveOver k X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Nat.card ((baseChangeOpen k Ω U : Set (baseChange k Ω X))ᶜ : Set _) =
      Anabelian.cuspDegree k X U :=
  card_compl_eq_cuspDegree k Ω U (Anabelian.finite_compl_of_isCurveOver (k := k) X U hU)
    (compl_finite_baseChangeOpen k Ω hU)

end CurvesJacobian.Cusp
