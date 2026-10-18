/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Scheme.TensorDomainConstantField
import CurvesJacobian.Scheme.ConstantField

/-!
# Geometric integrality from the constant field (characteristic zero)

**Theorem** (`CurvesJacobian.geometricallyIntegral_of_isAlgClosedIn`). Let `K` be a field of
characteristic zero and `X` an integral scheme over `Spec K` such that `K` is algebraically
closed in the function field `K(X)` (with belyi's `K`-algebra structure on `K(X)`). Then
`X ↘ Spec K` is geometrically integral. This is a converse of
`CurvesJacobian.mem_range_algebraMap_of_isAlgebraic`. No finiteness hypothesis on `X` is needed.

**Proof sketch.** Fix a field `F / K` and put `X_F = X ×_K F`, with `W_F ⊆ X_F` the preimage of
an open `W ⊆ X`.
1. For a nonempty affine open `W`, `W_F ≅ Spec (F ⊗[K] Γ(X, W))`, and `F ⊗[K] Γ(X, W)` is a
   domain by `CurvesJacobian.isDomain_tensorProduct_of_injective`, applied to the injective germ
   map `Γ(X, W) → K(X)`. So `W_F` is integral.
2. The `W_F` cover `X_F`, and `X_F → X` is surjective (`Spec F → Spec K` is), so `W_F ≠ ∅`
   when `W ≠ ∅`.
3. `X_F` is reduced, since each stalk is a stalk of some integral `W_F`.
4. `X_F` is irreducible. Given nonempty opens `u ∋ p`, `v ∋ q` with `p ∈ W₁_F` and `q ∈ W₂_F`,
   choose a nonempty affine `W₃ ⊆ W₁ ∩ W₂` (`X` is irreducible). Then irreducibility of `W₁_F`,
   `W₂_F` and `W₃_F` gives `W₃_F ∩ u ≠ ∅`, `W₃_F ∩ v ≠ ∅` and finally `u ∩ v ≠ ∅`.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi
open scoped TensorProduct

universe u

namespace CurvesJacobian

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

variable (K X) in
/-- The preimage `W_F` of an open `W ⊆ X` in the base change `X_F = X ×_K F`. -/
noncomputable abbrev baseChangePreimage (F : Type u) [Field F] [Algebra K F] (W : X.Opens) :
    (pullback (X ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K F)))).Opens :=
  (pullback.fst (X ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K F)))) ⁻¹ᵁ W

/-- The preimage of a nonempty affine open `W` in `X_F` is integral: it is
`Spec (F ⊗[K] Γ(X, W))`, and `F ⊗[K] Γ(X, W)` is a domain since `Γ(X, W) ↪ K(X)`. -/
private lemma isIntegral_baseChangePreimage [CharZero K] [IsIntegral X]
    (hK : ∀ x : X.functionField, IsAlgebraic K x → x ∈ (algebraMap K X.functionField).range)
    (F : Type u) [Field F] [Algebra K F] {W : X.Opens} (hW : IsAffineOpen W) [Nonempty W] :
    IsIntegral (baseChangePreimage K X F W).toScheme := by
  letI := sectionsAlgebra K X W
  let γ : Γ(X, W) →ₐ[K] X.functionField :=
    { (X.germToFunctionField W).hom with
      commutes' := fun c ↦ (algebraMap_functionField_eq_germ K X W c).symm }
  haveI : IsDomain (F ⊗[K] Γ(X, W)) :=
    isDomain_tensorProduct_of_injective hK F γ (X.germToFunctionField_injective W)
  let f := X ↘ Spec (.of K)
  let g := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have h₂ : hW.isoSpec.inv ≫ W.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, W))) := by
    rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    exact fromSpec_comp_structure K X hW
  let m := pullback.map g (hW.isoSpec.inv ≫ W.ι ≫ f) g (W.ι ≫ f) (𝟙 _) hW.isoSpec.inv (𝟙 _)
    (by simp) (by simp)
  haveI : IsIso m := by
    simp only [m]
    infer_instance
  let e : Spec (.of (F ⊗[K] Γ(X, W))) ≅ (baseChangePreimage K X F W).toScheme :=
    (pullbackSpecIso K F Γ(X, W)).symm ≪≫ pullback.congrHom rfl h₂.symm ≪≫ asIso m ≪≫
      pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso f g W.ι).symm ≪≫
      pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict _ W
  exact IsIntegral.of_isIso e.hom

/-- **Geometric integrality from the constant field.** Let `K` be a field of characteristic zero
and `X` an integral scheme over `Spec K` such that `K` is algebraically closed in the function
field `K(X)`. Then `X ⟶ Spec K` is geometrically integral. -/
theorem geometricallyIntegral_of_isAlgClosedIn [CharZero K] [IsIntegral X]
    (hK : ∀ x : X.functionField, IsAlgebraic K x → x ∈ (algebraMap K X.functionField).range) :
    GeometricallyIntegral (X ↘ Spec (.of K)) := by
  haveI : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IsIntegral ·) :=
    ⟨fun e _ ↦ IsIntegral.of_isIso e.hom⟩
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro F _ _
  let f := X ↘ Spec (.of K)
  let g := Spec.map (CommRingCat.ofHom (algebraMap K F))
  let pre := baseChangePreimage K X F
  let P : Scheme.{u} := pullback f g
  haveI : Surjective g := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y⟩ : Nonempty (Spec (.of F)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩
  have hsurj : Function.Surjective (pullback.fst f g) := (pullback.fst f g).surjective
  -- the preimages of affine opens cover `X_F`
  have hcov : ∀ p : P, ∃ W : X.Opens, IsAffineOpen W ∧ p ∈ pre W := by
    intro p
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pullback.fst f g p)) isOpen_univ
    exact ⟨W, hW, hx⟩
  have hne : ∀ W : X.Opens, (W : Set X).Nonempty → ((pre W : Set P)).Nonempty := by
    rintro W ⟨x, hx⟩
    obtain ⟨p, rfl⟩ := hsurj x
    exact ⟨p, hx⟩
  have hint : ∀ W : X.Opens, IsAffineOpen W → (W : Set X).Nonempty →
      IsIntegral (pre W).toScheme := by
    rintro W hW ⟨x, hx⟩
    haveI : Nonempty W := ⟨⟨x, hx⟩⟩
    exact isIntegral_baseChangePreimage hK F hW
  have hirr : ∀ W : X.Opens, IsAffineOpen W → (W : Set X).Nonempty →
      IsPreirreducible (pre W : Set P) := by
    intro W hW hWne
    haveI := hint W hW hWne
    have := (IrreducibleSpace.isIrreducible_univ (pre W).toScheme).image (pre W).ι
      (pre W).ι.continuous.continuousOn
    rw [Set.image_univ, Scheme.Opens.range_ι] at this
    exact this.isPreirreducible
  haveI : IrreducibleSpace P := by
    refine { isPreirreducible_univ := ?_, toNonempty := ?_ }
    · rintro u v hu hv ⟨p, -, hp⟩ ⟨q, -, hq⟩
      obtain ⟨W₁, hW₁, hp₁⟩ := hcov p
      obtain ⟨W₂, hW₂, hq₂⟩ := hcov q
      obtain ⟨x, hx₁, hx₂⟩ : ((W₁ : Set X) ∩ W₂).Nonempty :=
        nonempty_preirreducible_inter W₁.2 W₂.2 ⟨_, hp₁⟩ ⟨_, hq₂⟩
      obtain ⟨_, ⟨W₃, hW₃, rfl⟩, hx₃, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((W₁ ⊓ W₂ : X.Opens) : Set X) from ⟨hx₁, hx₂⟩) (W₁ ⊓ W₂).2
      have hne₃ : (W₃ : Set X).Nonempty := ⟨x, hx₃⟩
      have hsub₁ : (pre W₃ : Set P) ⊆ pre W₁ := fun y hy ↦ (hsub hy).1
      have hsub₂ : (pre W₃ : Set P) ⊆ pre W₂ := fun y hy ↦ (hsub hy).2
      obtain ⟨r, hr⟩ := hne W₃ hne₃
      have h₁ : ((pre W₃ : Set P) ∩ u).Nonempty := by
        obtain ⟨y, -, hyu, hy₃⟩ := hirr W₁ hW₁ ⟨_, hp₁⟩ u (pre W₃) hu (pre W₃).2
          ⟨p, hp₁, hp⟩ ⟨r, hsub₁ hr, hr⟩
        exact ⟨y, hy₃, hyu⟩
      have h₂ : ((pre W₃ : Set P) ∩ v).Nonempty := by
        obtain ⟨y, -, hyv, hy₃⟩ := hirr W₂ hW₂ ⟨_, hq₂⟩ v (pre W₃) hv (pre W₃).2
          ⟨q, hq₂, hq⟩ ⟨r, hsub₂ hr, hr⟩
        exact ⟨y, hy₃, hyv⟩
      obtain ⟨y, -, hyu, hyv⟩ := hirr W₃ hW₃ hne₃ u v hu hv h₁ h₂
      exact ⟨y, trivial, hyu, hyv⟩
    · obtain ⟨x⟩ : Nonempty X := inferInstance
      obtain ⟨p, -⟩ := hsurj x
      exact ⟨p⟩
  haveI : IsReduced P := by
    have (p : P) : _root_.IsReduced (P.presheaf.stalk p) := by
      obtain ⟨W, hW, hp⟩ := hcov p
      haveI := hint W hW ⟨_, hp⟩
      exact isReduced_of_injective _
        (asIso ((pre W).ι.stalkMap ⟨p, hp⟩)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end CurvesJacobian
