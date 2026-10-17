/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicSpecEquiv
import CurvesJacobian.Picard.Pullback
import FormalSchemes.QcohAffineLocalization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Sections of invertible sheaves over affine opens

Let `X` be a scheme, `U ⊆ X` an affine open and `M` a quasi-coherent `𝒪_X`-module. For
`f ∈ Γ(X, U)`, the restriction `Γ(M, U) → Γ(M, D(f))` is a localization away from `f`
(`Scheme.Modules.isLocalizedModule_resBasicOpen`, from formal-schemes'
`exists_pow_smul_eq_res`/`exists_pow_smul_eq_zero`; Stacks, Lemma 26.7.4, Tag 01IA, and
Lemma 26.5.4, Tag 01HV).

For an invertible sheaf `L`, the `f ∈ Γ(X, U)` such that `L` has a basis on `D(f)` coming from a
section over `U` generate the unit ideal (`Scheme.Modules.span_trivSet_eq_top`), so:

* `Scheme.Modules.finite_sections`, `Scheme.Modules.projective_sections`: `Γ(L, U)` is a finite
  projective `Γ(X, U)`-module (locally free of rank one; Stacks, Lemma 10.78.2, Tag 00NX, via
  `Module.FinitePresentation.of_localizationSpan'` and `Module.flat_of_isLocalized_span`).
-/

open CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}

/-- `Γ(M, D(f))` as a `Γ(X, U)`-module, through the restriction `Γ(X, U) → Γ(X, D(f))`. -/
scoped instance moduleBasicOpen (f : Γ(X, U)) : Module Γ(X, U) Γ(M, X.basicOpen f) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

scoped instance isScalarTower_basicOpen (f : Γ(X, U)) :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
  IsScalarTower.of_compHom _ _ _

lemma smul_basicOpen_def (f : Γ(X, U)) (r : Γ(X, U)) (x : Γ(M, X.basicOpen f)) :
    r • x = X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • x := rfl

/-- The restriction `Γ(M, U) → Γ(M, D(f))`, as a `Γ(X, U)`-linear map. -/
def resBasicOpen (f : Γ(X, U)) : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' := map_add _
  map_smul' r m := M.map_smul (homOfLE (X.basicOpen_le f)) r m

lemma resBasicOpen_apply (f : Γ(X, U)) (m : Γ(M, U)) :
    M.resBasicOpen f m = M.presheaf.map (homOfLE (X.basicOpen_le f)).op m := rfl

lemma isUnit_res_basicOpen (f : Γ(X, U)) :
    IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
  X.toRingedSpace.isUnit_res_basicOpen f

/-- For quasi-coherent `M` and affine `U`, `Γ(M, U) → Γ(M, D(f))` is a localization away from
`f` (Stacks, Lemma 26.7.4, Tag 01IA). -/
theorem isLocalizedModule_resBasicOpen [M.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (M.resBasicOpen f) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    obtain ⟨v, hv⟩ := (isUnit_res_basicOpen f).pow n
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun y ↦ ((v⁻¹ : (Γ(X, X.basicOpen f))ˣ) : Γ(X, X.basicOpen f)) • y, fun y ↦ ?_, fun y ↦ ?_⟩
    · simp only [Module.algebraMap_end_apply]
      rw [smul_basicOpen_def, map_pow, ← hv, smul_smul, Units.inv_mul, one_smul]
    · simp only [Module.algebraMap_end_apply]
      rw [smul_basicOpen_def, map_pow, ← hv, smul_smul, Units.mul_inv, one_smul]
  surj y := by
    obtain ⟨m, k, h⟩ := exists_pow_smul_eq_res hU M f y
    exact ⟨⟨m, ⟨f ^ k, k, rfl⟩⟩, h⟩
  exists_of_eq {m₁ m₂} h := by
    have h' : M.presheaf.map (homOfLE (X.basicOpen_le f)).op (m₁ - m₂) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero hU M f (m₁ - m₂) h'
    refine ⟨⟨f ^ k, k, rfl⟩, ?_⟩
    change f ^ k • m₁ = f ^ k • m₂
    rw [← sub_eq_zero, ← smul_sub, hk]

/-! ### Bases -/

variable {M}

lemma isBasisOn_unit_smul {V : X.Opens} {e : Γ(M, V)} (he : M.IsBasisOn V e) {u : Γ(X, V)}
    (hu : IsUnit u) : M.IsBasisOn V (u • e) := by
  intro W hW
  set u' : X.ringCatSheaf.obj.obj (op W) := X.ringCatSheaf.obj.map (homOfLE hW).op u
  have hres : IsUnit u' := hu.map (X.presheaf.map (homOfLE hW).op).hom
  have : (fun r : X.ringCatSheaf.obj.obj (op W) ↦
      r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj M) hW (u • e)) =
      (fun r : X.ringCatSheaf.obj.obj (op W) ↦
        r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj M) hW e) ∘
        (fun r ↦ r * u') := by
    funext r
    simp only [Function.comp_apply]
    exact (congrArg (r • ·) (Scheme.PresheafOfModules.res_smul _ hW u e)).trans
      (smul_smul _ _ _)
  rw [this]
  refine (he hW).comp ?_
  obtain ⟨w, hw⟩ := hres
  rw [← hw]
  exact (Units.mulRight w).bijective

/-- The bijection `Γ(X, V) ≃ Γ(M, V)`, `r ↦ r • e`, given by a basis `e` on `V`. -/
def IsBasisOn.equiv {V : X.Opens} {e : Γ(M, V)} (he : M.IsBasisOn V e) :
    Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, V) Γ(M, V) e) <| by
    have h := he (le_refl V)
    have e' : (fun r : X.ringCatSheaf.obj.obj (op V) ↦
        r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj M) (le_refl V) e) =
        LinearMap.toSpanSingleton Γ(X, V) Γ(M, V) e := by
      funext r
      rw [Scheme.PresheafOfModules.res_self]
      rfl
    rw [e'] at h
    exact h

variable (M) in
/-- The `f ∈ Γ(X, U)` such that `M` has a basis on `D(f)` which is the restriction of a section
over `U`. -/
def trivSet (U : X.Opens) : Set Γ(X, U) :=
  {f | ∃ m : Γ(M, U), M.IsBasisOn (X.basicOpen f) (M.resBasicOpen f m)}

/-- For an invertible sheaf and an affine open `U`, the `f` with `L|_{D(f)}` trivialised by a
section over `U` generate the unit ideal of `Γ(X, U)`. -/
theorem span_trivSet_eq_top (L : X.Modules) [L.IsInvertible] (hU : IsAffineOpen U) :
    Ideal.span (L.trivSet U) = ⊤ := by
  rw [← hU.self_le_iSup_basicOpen_iff]
  intro x hxU
  obtain ⟨W, e, hxW, he⟩ := IsInvertible.exists_basis (L := L) x
  obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ hxU
  have he' : L.IsBasisOn (X.basicOpen f) (L.presheaf.map (homOfLE hfW).op e) :=
    Scheme.PresheafOfModules.IsBasisOn.restrict he hfW
  obtain ⟨m, k, hm⟩ := exists_pow_smul_eq_res hU L f (L.presheaf.map (homOfLE hfW).op e)
  have hmf : f ∈ L.trivSet U := by
    refine ⟨m, ?_⟩
    rw [resBasicOpen_apply, ← hm]
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ k)) := by
      rw [map_pow]
      exact (isUnit_res_basicOpen f).pow k
    exact isBasisOn_unit_smul he' hu
  exact Opens.mem_iSup.mpr ⟨⟨f, hmf⟩, hxf⟩

section Projective

variable (L : X.Modules) [L.IsInvertible] (hU : IsAffineOpen U)

include hU in
lemma finitePresentation_and_flat_sections :
    Module.FinitePresentation Γ(X, U) Γ(L, U) ∧ Module.Flat Γ(X, U) Γ(L, U) := by
  haveI := isQuasicoherent_of_isInvertible L
  set s := L.trivSet U
  have hs := span_trivSet_eq_top L hU
  haveI : ∀ g : s, IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) := fun g ↦
    hU.isLocalization_basicOpen g.1
  haveI : ∀ g : s, IsLocalizedModule.Away g.1 (L.resBasicOpen g.1) := fun g ↦
    L.isLocalizedModule_resBasicOpen hU g.1
  have hfree : ∀ g : s, Γ(X, X.basicOpen g.1) ≃ₗ[Γ(X, X.basicOpen g.1)]
      Γ(L, X.basicOpen g.1) := fun g ↦ (g.2.choose_spec).equiv
  constructor
  · refine Module.FinitePresentation.of_localizationSpan' (M := Γ(L, U)) s hs
      (Rₚ := fun g : s ↦ Γ(X, X.basicOpen g.1)) (fun g ↦ L.resBasicOpen g.1) fun g ↦ ?_
    exact Module.FinitePresentation.of_equiv (hfree g)
  · refine Module.flat_of_isLocalized_span (R := Γ(X, U)) Γ(X, U) Γ(L, U) s hs
      (fun g : s ↦ Γ(L, X.basicOpen g.1)) (fun g ↦ L.resBasicOpen g.1) fun g ↦ ?_
    haveI : Module.Flat Γ(X, U) Γ(X, X.basicOpen g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.of_linearEquiv ((hfree g).restrictScalars Γ(X, U)).symm

include hU in
/-- Sections of an invertible sheaf over an affine open form a finite `Γ(X, U)`-module. -/
theorem finite_sections : Module.Finite Γ(X, U) Γ(L, U) :=
  haveI := (finitePresentation_and_flat_sections L hU).1
  inferInstance

include hU in
/-- Sections of an invertible sheaf over an affine open form a projective `Γ(X, U)`-module. -/
theorem projective_sections : Module.Projective Γ(X, U) Γ(L, U) :=
  haveI := (finitePresentation_and_flat_sections L hU).1
  haveI := (finitePresentation_and_flat_sections L hU).2
  Module.Flat.projective_of_finitePresentation

end Projective

end AlgebraicGeometry.Scheme.Modules
