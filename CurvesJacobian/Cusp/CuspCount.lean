/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BaseChange
import Belyi.Anabelian.LocAn

/-!
# Geometric points over a closed point after base change to an algebraic closure

Let `k ⊆ Ω` be fields of characteristic zero with `Ω` algebraically closed, and `X` a scheme over
`k` with `X_Ω → Spec Ω` locally of finite type. For a point `c` of `X`, every `k`-embedding
`σ : κ(c) → Ω` gives an `Ω`-rational point `Spec Ω ⟶ X_Ω` (`CurvesJacobian.Cusp.geomPoint`)
lying over `c`, and distinct embeddings give distinct points
(`CurvesJacobian.Cusp.geomPoint_injective`: two sections `Spec Ω ⟶ X_Ω` through the same point
agree, Mathlib's `ext_of_apply_closedPoint_eq`, and `Spec κ(c) ⟶ X` is a monomorphism).
Consequently (`CurvesJacobian.Cusp.cuspDegree_le_card_compl`): for an open `U ⊆ X` with finite
complement,

  `Σ_{c ∉ U} [κ(c) : k] ≤ #(X_Ω ∖ U_Ω)`,

i.e. the number of geometric cusps of a hyperbolic curve over `k` (`Belyi.Anabelian.cuspDegree`)
is at most the number of cusps of its base change to `Ω`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi Belyi.Anabelian Module

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- `Spec κ(c) ⟶ X ⟶ Spec k` is `Spec` of the `k`-algebra structure of `κ(c)`. -/
lemma fromSpecResidueField_comp_structure (c : X) :
    X.fromSpecResidueField c ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom
        (letI := Anabelian.residueFieldAlgebra k X c; algebraMap k (X.residueField c))) := by
  have hs : (X ↘ Spec (.of k)) = X.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  rw [hs, Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  rfl

variable (X) in
/-- The `k`-embeddings `κ(c) → Ω`. -/
abbrev ResEmb (c : X) : Type u :=
  @AlgHom k (X.residueField c) Ω _ _ _ (Anabelian.residueFieldAlgebra k X c) _

/-- The underlying ring homomorphism of a `k`-embedding `κ(c) → Ω`. -/
abbrev ResEmb.ring {c : X} (σ : ResEmb k Ω X c) : X.residueField c →+* Ω :=
  letI := Anabelian.residueFieldAlgebra k X c; σ.toRingHom

lemma ResEmb.ring_injective {c : X} : Function.Injective (ResEmb.ring k Ω (c := c)) := by
  letI := Anabelian.residueFieldAlgebra k X c
  exact AlgHom.coe_ringHom_injective

/-- The `Ω`-point of `X_Ω` over `c : X` given by a `k`-embedding `σ : κ(c) → Ω`. -/
def geomPoint (c : X) (σ : ResEmb k Ω X c) : Spec (.of Ω) ⟶ baseChange k Ω X :=
  pullback.lift (Spec.map (CommRingCat.ofHom (ResEmb.ring k Ω σ)) ≫ X.fromSpecResidueField c)
    (𝟙 _) (by
    letI := Anabelian.residueFieldAlgebra k X c
    rw [Category.assoc, fromSpecResidueField_comp_structure, ← Spec.map_comp,
      Category.id_comp, specAlgebraMap]
    congr 1
    ext a
    exact σ.commutes a)

lemma geomPoint_snd (c : X) (σ : ResEmb k Ω X c) :
    geomPoint k Ω c σ ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

lemma geomPoint_fst (c : X) (σ : ResEmb k Ω X c) :
    geomPoint k Ω c σ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (ResEmb.ring k Ω σ)) ≫ X.fromSpecResidueField c :=
  pullback.lift_fst _ _ _

lemma fst_geomPoint_apply (c : X) (σ : ResEmb k Ω X c) :
    pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω)
      (geomPoint k Ω c σ (IsLocalRing.closedPoint Ω)) = c := by
  rw [← Scheme.Hom.comp_apply, geomPoint_fst, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]

/-- **Distinct embeddings give distinct geometric points.** -/
lemma geomPoint_injective [IsAlgClosed Ω]
    [LocallyOfFiniteType (pullback.snd (X ↘ Spec (.of k)) (specAlgebraMap k Ω))] :
    Function.Injective (fun cσ : Σ c : X, ResEmb k Ω X c ↦
      geomPoint k Ω cσ.1 cσ.2 (IsLocalRing.closedPoint Ω)) := by
  rintro ⟨c₁, σ₁⟩ ⟨c₂, σ₂⟩ h
  have heq : geomPoint k Ω c₁ σ₁ = geomPoint k Ω c₂ σ₂ :=
    ext_of_apply_closedPoint_eq (pullback.snd _ _) (geomPoint_snd k Ω c₁ σ₁)
      (geomPoint_snd k Ω c₂ σ₂) h
  have h2 := congrArg (· ≫ pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω)) heq
  simp only [geomPoint_fst] at h2
  have h3 : (Scheme.SpecToEquivOfField Ω X).symm ⟨c₁, CommRingCat.ofHom (ResEmb.ring k Ω σ₁)⟩ =
      (Scheme.SpecToEquivOfField Ω X).symm ⟨c₂, CommRingCat.ofHom (ResEmb.ring k Ω σ₂)⟩ := h2
  have h4 := (Scheme.SpecToEquivOfField Ω X).symm.injective h3
  obtain ⟨rfl, h5⟩ := Sigma.mk.inj h4
  have h6 : (ResEmb.ring k Ω σ₁) = (ResEmb.ring k Ω σ₂) :=
    congrArg CommRingCat.Hom.hom (eq_of_heq h5)
  have h7 : σ₁ = σ₂ := ResEmb.ring_injective k Ω h6
  subst h7
  rfl

/-- `[κ(c) : k] ≤ #Hom_k(κ(c), Ω)` (equality for finite `κ(c)/k`; `0` otherwise). -/
lemma pointDegree_le_card [CharZero k] [IsAlgClosed Ω] (c : X) :
    Anabelian.pointDegree k X c ≤ Nat.card (ResEmb k Ω X c) := by
  letI := Anabelian.residueFieldAlgebra k X c
  rw [Anabelian.pointDegree]
  by_cases hfin : FiniteDimensional k (X.residueField c)
  · haveI : Algebra.IsSeparable k (X.residueField c) := inferInstance
    rw [← AlgHom.card k (X.residueField c) Ω, Fintype.card_eq_nat_card]
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _

/-- **`Σ_{c ∉ U} [κ(c) : k] ≤ #(X_Ω ∖ U_Ω)`.** -/
theorem cuspDegree_le_card_compl [CharZero k] [IsAlgClosed Ω]
    [LocallyOfFiniteType (pullback.snd (X ↘ Spec (.of k)) (specAlgebraMap k Ω))]
    (U : X.Opens) (hfin : (U : Set X)ᶜ.Finite)
    (hfin' : ((baseChangeOpen k Ω U : (baseChange k Ω X).Opens) : Set (baseChange k Ω X))ᶜ.Finite) :
    Anabelian.cuspDegree k X U ≤
      Nat.card ((baseChangeOpen k Ω U : Set (baseChange k Ω X))ᶜ : Set _) := by
  classical
  haveI := hfin'.to_subtype
  set S := hfin.toFinset
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
  haveI : Finite (Σ c : S, ResEmb k Ω X c.1) := Finite.of_injective F hF
  haveI : ∀ c : S, Finite (ResEmb k Ω X c.1) := fun c ↦
    Finite.of_injective (fun σ : ResEmb k Ω X c.1 ↦ (⟨c, σ⟩ : Σ c : S, ResEmb k Ω X c.1))
      (fun _ _ h ↦ by simpa using h)
  rw [Anabelian.cuspDegree, finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ∑ c ∈ S, Anabelian.pointDegree k X c ≤ ∑ c ∈ S, Nat.card (ResEmb k Ω X c) :=
        Finset.sum_le_sum fun c _ ↦ pointDegree_le_card k Ω c
    _ = ∑ c : S, Nat.card (ResEmb k Ω X c.1) := (Finset.sum_coe_sort S _).symm
    _ = Nat.card (Σ c : S, ResEmb k Ω X c.1) := Nat.card_sigma.symm
    _ ≤ _ := Nat.card_le_card_of_injective F hF

end CurvesJacobian.Cusp
