/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.FundamentalGroup.HomotopyExact
import Pi1.FundamentalGroup.BaseChangeInjective
import Pi1.Profinite.Slim
import LocalClassFieldTheory.NumberField.GaloisSlim

/-!
# The arithmetic fundamental group `Π_X ↠ G_k` of an affine `k`-scheme (MR8.3 (b))

For a field `k`, a separable closure `Ω` of `k` and an affine `k`-scheme `X = Spec R` with `X` and
`X_Ω = Spec (Ω ⊗[k] R)` connected, and an `Ω`-rational point `x` of `X_Ω`:

* `CurvesJacobian.Cusp.geomFundamentalGroupEquivKer`: **`Δ_X ≃ₜ* ker(Π_X ↠ G_k)`**, the left half
  and the middle of the homotopy exact sequence `1 → π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X) → Gal(Ω/k) → 1`
  (pi1 `fundamentalGroupMap_baseChange_injective` and `ker_toGaloisGroup_eq_range`; a continuous
  bijection of compact Hausdorff groups is a homeomorphism);
* `CurvesJacobian.Cusp.isSlim_galoisGroup_numberField`: **`G_K = Gal(Ω/K)` is slim** for a number
  field `K` ([AbsTopI] Theorem 1.7 (iii); local-class-field-theory
  `NumberField.eq_one_of_forall_mem_commute`).

([AbsTopI] = `Topics in Absolute Anabelian Geometry I.txt`; Example 4.8 (ii), l.3570: "`G_k` is
slim" for sub-`p`-adic `k`, the input of Definition 4.6 (ii).)
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Pi1.Profinite
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-- **The absolute Galois group of a number field is slim**: an element of `Gal(Ω/K)` commuting
with an open subgroup is trivial. -/
theorem isSlim_galoisGroup_numberField (K Ω : Type*) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] : IsSlim (Ω ≃ₐ[K] Ω) := fun U _ hz ↦
  NumberField.eq_one_of_forall_mem_commute K Ω U.isOpen fun τ hτ ↦ (hz τ hτ).symm

variable {k Ω R : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] [IsGalois k Ω]
  [CommRing R] [Algebra k R] [ConnectedSpace (Spec (.of R))]
  [ConnectedSpace (Spec (.of (Ω ⊗[k] R)))]
  (x : Spec (.of Ω) ⟶ Spec (.of (Ω ⊗[k] R)))
  (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[k] R))) =
    Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)))
  (h : (x ≫ baseChangeSpec k Ω R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
    Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

include hx in
lemma mem_ker_toGaloisGroup (δ : π₁ᵉᵗ(x)) :
    fundamentalGroupMap (baseChangeSpec k Ω R) rfl δ ∈
      (toGaloisGroup (Spec.map (CommRingCat.ofHom (algebraMap k R))) h).ker := by
  rw [ker_toGaloisGroup_eq_range x hx h]
  exact ⟨δ, rfl⟩

/-- `π₁ᵉᵗ(X_Ω) → ker(Π_X → G_k)`. -/
def toKerToGaloisGroup :
    π₁ᵉᵗ(x) →* (toGaloisGroup (Spec.map (CommRingCat.ofHom (algebraMap k R))) h).ker where
  toFun δ := ⟨fundamentalGroupMap (baseChangeSpec k Ω R) rfl δ, mem_ker_toGaloisGroup x hx h δ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

lemma continuous_toKerToGaloisGroup : Continuous (toKerToGaloisGroup x hx h) :=
  ((fundamentalGroupMap (baseChangeSpec k Ω R) rfl).continuous).subtype_mk _

/-- `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X)` is injective with image `ker(Π_X → G_k)`. -/
lemma bijective_toKerToGaloisGroup : Function.Bijective (toKerToGaloisGroup x hx h) := by
  refine ⟨fun a b hab ↦ fundamentalGroupMap_baseChange_injective x (congrArg Subtype.val hab),
    fun ⟨γ, hγ⟩ ↦ ?_⟩
  rw [ker_toGaloisGroup_eq_range x hx h] at hγ
  obtain ⟨δ, rfl⟩ := hγ
  exact ⟨δ, rfl⟩

/-- **`Δ_X ≃ₜ* ker(Π_X ↠ G_k)`** for an affine `k`-scheme `X = Spec R`: the geometric fundamental
group `π₁ᵉᵗ(X_Ω, x)` is identified, as a topological group, with the kernel of
`π₁ᵉᵗ(X, x) → Gal(Ω/k)` (SGA 1 IX.6.1). -/
def geomFundamentalGroupEquivKer :
    π₁ᵉᵗ(x) ≃ₜ* (toGaloisGroup (Spec.map (CommRingCat.ofHom (algebraMap k R))) h).ker :=
  let e := MulEquiv.ofBijective _ (bijective_toKerToGaloisGroup x hx h)
  { e with
    continuous_toFun := continuous_toKerToGaloisGroup x hx h
    continuous_invFun := ((continuous_toKerToGaloisGroup x hx h).homeoOfEquivCompactToT2
      (f := e.toEquiv)).symm.continuous }

@[simp]
lemma geomFundamentalGroupEquivKer_apply (δ : π₁ᵉᵗ(x)) :
    (geomFundamentalGroupEquivKer x hx h δ : π₁ᵉᵗ(x ≫ baseChangeSpec k Ω R)) =
      fundamentalGroupMap (baseChangeSpec k Ω R) rfl δ := rfl

end CurvesJacobian.Cusp
