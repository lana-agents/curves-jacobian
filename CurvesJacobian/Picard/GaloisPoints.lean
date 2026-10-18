/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Jacobian

/-!
# Galois descent of points, and the Galois action on `Pic_{C/k,σ}`

Let `Ω / K` be a Galois extension of fields (possibly infinite).

* `CurvesJacobian.eq_of_specMapAlg_comp_eq`: a morphism `Spec K ⟶ X` is determined by its
  composite with `Spec Ω ⟶ Spec K`.
* **`CurvesJacobian.exists_specMapAlg_comp_eq`** (Galois descent of points of schemes): a
  morphism `a : Spec Ω ⟶ X` with `Spec(τ) ≫ a = a` for all `τ ∈ Gal(Ω/K)` factors through
  `Spec Ω ⟶ Spec K`. Indeed `a` is a point `x ∈ X` with an embedding `κ(x) ⟶ Ω`, whose image is
  fixed by `Gal(Ω/K)`, hence lies in `K` (`InfiniteGalois.mem_range_algebraMap_iff_fixed`).

For a scheme `C` over a field `k` with a rational point `σ`, and fields `k ⊆ K ⊆ Ω`:

* `CurvesJacobian.picRes`: the restriction `Pic_{C/k,σ}(K) ⟶ Pic_{C/k,σ}(Ω)` (pullback along
  `C_Ω ⟶ C_K`);
* `CurvesJacobian.picGal τ`: the action of `τ ∈ Aut(Ω/K)` on `Pic_{C/k,σ}(Ω)`, by functoriality of
  the Picard functor along the `k`-morphism `Spec(τ)`;
* `CurvesJacobian.picGal_picRes`: restrictions are Galois invariant, so `picRes` lands in the
  invariants `picInv` (`CurvesJacobian.picRes_mem_picInv`).

For a curve, `jacPoints C σ hσ K = Pic⁰_{C/k,σ}(K)` is the group of `K`-points of the Jacobian
(over a separably closed perfect `k` these are the `K`-points of the scheme `Jacobian C σ hσ`,
`jacobianRepresentableBy`), and `picRes` restricts to `J(K) ⟶ J(Ω)`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Belyi

section Points

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- The morphism `Spec Ω ⟶ Spec K` of a field extension. -/
abbrev specMapAlg : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ω))

variable {K Ω}

/-- The automorphism `Spec(τ)` of `Spec Ω` for `τ ∈ Aut(Ω/K)`. -/
abbrev specAut (τ : Ω ≃ₐ[K] Ω) : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω) :=
  Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))

@[reassoc (attr := simp)]
lemma specAut_comp_specMapAlg (τ : Ω ≃ₐ[K] Ω) : specAut τ ≫ specMapAlg K Ω = specMapAlg K Ω := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact τ.commutes r

/-- A morphism `Spec K ⟶ X` is determined by its composite with `Spec Ω ⟶ Spec K`. -/
lemma eq_of_specMapAlg_comp_eq {X : Scheme.{u}} {b b' : Spec (CommRingCat.of K) ⟶ X}
    (h : specMapAlg K Ω ≫ b = specMapAlg K Ω ≫ b') : b = b' := by
  obtain ⟨⟨x, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  obtain ⟨⟨x', ψ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := (Scheme.SpecToEquivOfField Ω X).symm.injective
    (a₁ := ⟨x, ψ ≫ CommRingCat.ofHom (algebraMap K Ω)⟩)
    (a₂ := ⟨x', ψ' ≫ CommRingCat.ofHom (algebraMap K Ω)⟩) h
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp h'
  dsimp only at e he
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
  have hψ : ψ = ψ' := by
    ext r
    exact (algebraMap K Ω).injective (congrArg (fun f ↦ f.hom r) he)
  rw [hψ]

variable [IsGalois K Ω]

/-- **Galois descent of points of schemes**: a `Gal(Ω/K)`-invariant morphism `Spec Ω ⟶ X`
factors through `Spec Ω ⟶ Spec K`. -/
theorem exists_specMapAlg_comp_eq {X : Scheme.{u}} (a : Spec (CommRingCat.of Ω) ⟶ X)
    (ha : ∀ τ : Ω ≃ₐ[K] Ω, specAut τ ≫ a = a) :
    ∃ b : Spec (CommRingCat.of K) ⟶ X, specMapAlg K Ω ≫ b = a := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective a
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha ⊢
  have hfix : ∀ (τ : Ω ≃ₐ[K] Ω) (r : X.residueField x), τ (φ r) = φ r := by
    intro τ r
    have h := ha τ
    rw [← Category.assoc, ← Spec.map_comp] at h
    have h' := (Scheme.SpecToEquivOfField Ω X).symm.injective
      (a₁ := ⟨x, φ ≫ CommRingCat.ofHom (τ : Ω →+* Ω)⟩) (a₂ := ⟨x, φ⟩) h
    obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp h'
    simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
    exact congrArg (fun f ↦ f.hom r) he
  have hmem : ∀ r, φ r ∈ (algebraMap K Ω).fieldRange := fun r ↦
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (φ r)).mpr fun τ ↦ hfix τ r
  let ψ : X.residueField x ⟶ CommRingCat.of K := CommRingCat.ofHom
    ((algebraMap K Ω).rangeRestrictFieldEquiv.symm.toRingHom.comp
      (φ.hom.codRestrict (algebraMap K Ω).fieldRange hmem))
  have hψ : ψ ≫ CommRingCat.ofHom (algebraMap K Ω) = φ := by
    ext r
    exact (algebraMap K Ω).rangeRestrictFieldEquiv_apply_symm_apply _
  refine ⟨Spec.map ψ ≫ X.fromSpecResidueField x, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hψ]

end Points

section Pic

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (K Ω : Type u) [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω]

@[reassoc (attr := simp)]
lemma specMapAlg_comp_specAlgebraMap :
    specMapAlg K Ω ≫ specAlgebraMap (k₀ := k) K = specAlgebraMap (k₀ := k) Ω := by
  rw [specAlgebraMap, specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

variable {K Ω} in
@[reassoc (attr := simp)]
lemma specAut_comp_specAlgebraMap (τ : Ω ≃ₐ[K] Ω) :
    specAut τ ≫ specAlgebraMap (k₀ := k) Ω = specAlgebraMap (k₀ := k) Ω := by
  rw [← specMapAlg_comp_specAlgebraMap K Ω, specAut_comp_specMapAlg_assoc]

/-- The rigidified Picard group `Pic_{C/k,σ}(K)` of `C_K`. -/
abbrev picPt (K : Type u) [Field K] [Algebra k K] :
    AddSubgroup (pullback (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) K)).Pic :=
  picSigmaGrp (C ↘ Spec (CommRingCat.of k)) σ hσ (specAlgebraMap (k₀ := k) K)

/-- **The restriction `Pic_{C/k,σ}(K) ⟶ Pic_{C/k,σ}(Ω)`** for `k ⊆ K ⊆ Ω`. -/
def picRes : picPt C σ hσ K →+ picPt C σ hσ Ω :=
  picSigmaMap _ σ hσ (specMapAlg K Ω) _ _ (specMapAlg_comp_specAlgebraMap K Ω)

variable {K Ω} in
/-- **The Galois action** of `τ ∈ Aut(Ω/K)` on `Pic_{C/k,σ}(Ω)`: pullback along the
`k`-automorphism `Spec(τ)` of `Spec Ω`. -/
def picGal (τ : Ω ≃ₐ[K] Ω) : picPt C σ hσ Ω →+ picPt C σ hσ Ω :=
  picSigmaMap _ σ hσ (specAut τ) _ _ (specAut_comp_specAlgebraMap τ)

variable {K Ω} in
/-- **Restrictions are Galois invariant.** -/
lemma picGal_picRes (τ : Ω ≃ₐ[K] Ω) (x : picPt C σ hσ K) :
    picGal C σ hσ τ (picRes C σ hσ K Ω x) = picRes C σ hσ K Ω x := by
  apply Subtype.ext
  simp only [picGal, picRes, coe_picSigmaMap]
  rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, ← bcMap_comp _ _ _ _ _ _ _ _
    (by rw [specAut_comp_specMapAlg, specMapAlg_comp_specAlgebraMap])]
  congr 2
  exact bcMap_congr _ (specAut_comp_specMapAlg τ) _ _ _ _

/-- The `Aut(Ω/K)`-invariants of `Pic_{C/k,σ}(Ω)`. -/
def picInv : AddSubgroup (picPt C σ hσ Ω) where
  carrier := {x | ∀ τ : Ω ≃ₐ[K] Ω, picGal C σ hσ τ x = x}
  zero_mem' τ := map_zero _
  add_mem' {a b} ha hb τ := by rw [map_add, ha τ, hb τ]
  neg_mem' {a} ha τ := by rw [map_neg, ha τ]

lemma picRes_mem_picInv (x : picPt C σ hσ K) : picRes C σ hσ K Ω x ∈ picInv C σ hσ K Ω :=
  fun τ ↦ picGal_picRes C σ hσ τ x

end Pic

section Jacobian

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (K Ω : Type u) [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω]

/-- **The `K`-points of the Jacobian**: `J(K) = Pic⁰_{C/k,σ}(K)` (the degree is computed with
the chosen finite morphism `curveToP1 k C`). -/
abbrev jacPoints (K : Type u) [Field K] [Algebra k K] : AddSubgroup (picPt C σ hσ K) :=
  picZeroGrp (curveToP1 k C) σ hσ (specAlgebraMap (k₀ := k) K)

/-- The restriction maps `J(K)` into `J(Ω)`. -/
lemma picRes_mem_jacPoints {x : picPt C σ hσ K} (hx : x ∈ jacPoints C σ hσ K) :
    picRes C σ hσ K Ω x ∈ jacPoints C σ hσ Ω := by
  exact picDeg_map_over C σ hσ (curveToP1 k C) 0
    (Over.homMk (specMapAlg K Ω) (specMapAlg_comp_specAlgebraMap K Ω) :
      Over.mk (specAlgebraMap (k₀ := k) Ω) ⟶ Over.mk (specAlgebraMap (k₀ := k) K)) x hx

end Jacobian

end CurvesJacobian
