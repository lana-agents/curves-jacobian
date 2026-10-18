/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ArithmeticPi1
import CurvesJacobian.Galois.MaxSpecBaseChange
import CurvesJacobian.Galois.CurveCharts
import CurvesJacobian.Scheme.ConstantField
import Belyi.Curve.BaseChange
import Belyi.Anabelian.BelyiInput

/-!
# Base change of an affine open of a curve to a separable closure (MR8.3 (b))

Let `X` be a curve over a field `k`, `Ω ⊇ k` a field, `X_Ω = X ×_k Ω` (a curve over `Ω`, belyi
`isCurveOver_pullback`) and `U ⊆ X` an affine open. With `R = Γ(X, U)`:

* `CurvesJacobian.Cusp.baseChangeOpen U : X_Ω.Opens`, the preimage `U_Ω` of `U`;
* `CurvesJacobian.Cusp.specTensorIsoBaseChangeOpen`: `Spec (Ω ⊗[k] R) ≅ U_Ω`;
* `Spec R` and `Spec (Ω ⊗[k] R)` are connected (for `U` nonempty), `U_Ω` has finite complement,
  nonempty if `U ≠ X`; `Spec (Ω ⊗[k] R)` has an `Ω`-rational point when `Ω` is algebraically
  closed (`exists_rationalPoint`).

These are the inputs of the homotopy exact sequence of `CurvesJacobian.Cusp.ArithmeticPi1` for
the open `U` of a hyperbolic curve.
-/

open CategoryTheory Limits AlgebraicGeometry Belyi
open scoped TensorProduct

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (X) in
/-- The base change `X_Ω = X ×_{Spec k} Spec Ω`. -/
abbrev baseChange : Scheme.{u} := pullback (X ↘ Spec (.of k)) (specAlgebraMap k Ω)

/-- The preimage `U_Ω ⊆ X_Ω` of an open `U ⊆ X`. -/
abbrev baseChangeOpen (U : X.Opens) : (baseChange k Ω X).Opens :=
  (pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω)) ⁻¹ᵁ U

/-- The structure morphism of an affine open `U`: `Spec Γ(X, U) ⟶ Spec k` is `Spec` of the
`k`-algebra structure of `Γ(X, U)`. -/
lemma isoSpec_inv_ι_structure {U : X.Opens} (hU : IsAffineOpen U) :
    hU.isoSpec.inv ≫ U.ι ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
  rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  exact fromSpec_comp_structure k X hU

/-- Replacing `Spec Γ(X, U)` by `U` in the base change. -/
abbrev pullbackMapIsoSpec {U : X.Opens} (hU : IsAffineOpen U) :
    pullback (specAlgebraMap k Ω) (hU.isoSpec.inv ≫ U.ι ≫ (X ↘ Spec (.of k))) ⟶
      pullback (specAlgebraMap k Ω) (U.ι ≫ (X ↘ Spec (.of k))) :=
  pullback.map (specAlgebraMap k Ω) (hU.isoSpec.inv ≫ U.ι ≫ (X ↘ Spec (.of k)))
    (specAlgebraMap k Ω) (U.ι ≫ (X ↘ Spec (.of k))) (𝟙 _) hU.isoSpec.inv (𝟙 _)
    (by simp) (by simp)

lemma isIso_pullbackMapIsoSpec {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (pullbackMapIsoSpec k Ω hU) := by
  unfold pullbackMapIsoSpec
  infer_instance

/-- **`Spec (Ω ⊗[k] Γ(X, U)) ≅ U_Ω`** for an affine open `U ⊆ X`. -/
def specTensorIsoBaseChangeOpen {U : X.Opens} (hU : IsAffineOpen U) :
    Spec (.of (Ω ⊗[k] Γ(X, U))) ≅ (baseChangeOpen k Ω U).toScheme :=
  (pullbackSpecIso k Ω Γ(X, U)).symm ≪≫
    pullback.congrHom rfl (isoSpec_inv_ι_structure k hU).symm ≪≫
    @asIso _ _ _ _ (pullbackMapIsoSpec k Ω hU) (isIso_pullbackMapIsoSpec k Ω hU) ≪≫
    pullbackSymmetry _ _ ≪≫
    (pullbackRightPullbackFstIso (X ↘ Spec (.of k)) (specAlgebraMap k Ω) U.ι).symm ≪≫
    pullbackSymmetry _ _ ≪≫
    pullbackRestrictIsoRestrict _ U

/-- The `k`-algebra `Γ(X, U)` of an affine open of a `k`-scheme locally of finite type is of
finite type. -/
lemma finiteType_sections [LocallyOfFiniteType (X ↘ Spec (.of k))] {U : X.Opens}
    (hU : IsAffineOpen U) : Algebra.FiniteType k Γ(X, U) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) := by
    rw [← isoSpec_inv_ι_structure k hU]
    infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
  exact this

/-- `Spec Γ(X, U)` is integral for a nonempty affine open `U` of an integral scheme. -/
lemma isIntegral_spec_sections [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsIntegral (Spec Γ(X, U)) := by
  haveI : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom (Classical.arbitrary U)⟩
  exact isIntegral_of_isOpenImmersion hU.fromSpec

/-- `Spec Ω ⟶ Spec k` is surjective. -/
lemma surjective_specAlgebraMap : Surjective (specAlgebraMap k Ω) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨y⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

/-- `U_Ω` is nonempty if `U` is. -/
lemma nonempty_baseChangeOpen {U : X.Opens} (hU : (U : Set X).Nonempty) :
    ((baseChangeOpen k Ω U : (baseChange k Ω X).Opens) : Set (baseChange k Ω X)).Nonempty := by
  haveI := surjective_specAlgebraMap k Ω
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, rfl⟩ := (pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω)).surjective x
  exact ⟨y, hx⟩

/-- The complement of `U_Ω` is nonempty if that of `U` is. -/
lemma compl_nonempty_baseChangeOpen {U : X.Opens} (hU : (U : Set X)ᶜ.Nonempty) :
    ((baseChangeOpen k Ω U : (baseChange k Ω X).Opens) : Set (baseChange k Ω X))ᶜ.Nonempty := by
  haveI := surjective_specAlgebraMap k Ω
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, rfl⟩ := (pullback.fst (X ↘ Spec (.of k)) (specAlgebraMap k Ω)).surjective x
  exact ⟨y, hx⟩

/-- The complement of `U_Ω` is finite, for a nonempty open `U` of a curve over a perfect `Ω`. -/
lemma compl_finite_baseChangeOpen [IsCurveOver k X] [PerfectField Ω] {U : X.Opens}
    (hU : (U : Set X).Nonempty) :
    ((baseChangeOpen k Ω U : (baseChange k Ω X).Opens) : Set (baseChange k Ω X))ᶜ.Finite :=
  Anabelian.finite_compl_of_isCurveOver (k := Ω) (baseChange k Ω X) _
    (nonempty_baseChangeOpen k Ω hU)

/-- `Spec (Ω ⊗[k] Γ(X, U))` is integral, for a nonempty affine open `U` of a curve. -/
lemma isIntegral_spec_tensor [IsCurveOver k X] {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) : IsIntegral (Spec (.of (Ω ⊗[k] Γ(X, U)))) := by
  haveI := IsCurveOver.isIntegral Ω (baseChange k Ω X)
  obtain ⟨y, hy⟩ := nonempty_baseChangeOpen k Ω hne
  haveI : Nonempty (Spec (.of (Ω ⊗[k] Γ(X, U)))) :=
    ⟨(specTensorIsoBaseChangeOpen k Ω hU).inv ⟨y, hy⟩⟩
  exact isIntegral_of_isOpenImmersion
    ((specTensorIsoBaseChangeOpen k Ω hU).hom ≫ (baseChangeOpen k Ω U).ι)

/-- **An `Ω`-rational point of `U_Ω = Spec (Ω ⊗[k] Γ(X, U))`** (`Ω` algebraically closed): a
point `x` over `Spec Ω` (`hx`) lying over `Spec Ω ⟶ Spec k` (`h`). -/
lemma exists_rationalPoint [IsAlgClosed Ω] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    {U : X.Opens} (hU : IsAffineOpen U) [Nontrivial (Ω ⊗[k] Γ(X, U))] :
    ∃ x : Spec (.of Ω) ⟶ Spec (.of (Ω ⊗[k] Γ(X, U))),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[k] Γ(X, U)))) =
        Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) ∧
      (x ≫ FiniteEtale.baseChangeSpec k Ω Γ(X, U)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  haveI := finiteType_sections k hU
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Ω ⊗[k] Γ(X, U))
  let φ : Ω ⊗[k] Γ(X, U) →ₐ[Ω] Ω := maximalSpectrumEquivAlgHom Ω _ ⟨M, hM⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    simp
  · rw [Category.assoc, FiniteEtale.baseChangeSpec, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
    rw [Algebra.TensorProduct.includeRight_apply, ← mul_one (algebraMap k Γ(X, U) c),
      ← Algebra.smul_def, TensorProduct.tmul_smul, ← Algebra.TensorProduct.one_def,
      LinearMapClass.map_smul_of_tower, map_one, Algebra.smul_def, mul_one]

end CurvesJacobian.Cusp
