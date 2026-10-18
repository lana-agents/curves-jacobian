/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.EulerCharAdd
import CurvesJacobian.Picard.TwistCech

/-!
# Twisting by a rational point raises the Euler characteristic by one

For a line bundle `M` on a curve `Y` over a field (charts `U`, `V`) and the divisor `D` of a
rational point `σ ∈ U ∩ V`, the short exact sequence `0 → M → M(D) → M(D)|_σ → 0` gives
`χ(M(D)) = χ(M) + 1`, with `χ = h⁰ − h¹` of the chart Čech complexes. This is the computation
`deg 𝒪(x) = 1` behind the degree `χ = d + 1 − g` of Stacks, Lemma 44.6.7 (Tag 0BA0).

* `TwoCech.chi_of_removePoint`: the linear algebra. For maps `α, β, γ` of two-set Čech data
  `D' → D` and `ε : R → E` with `E` one-dimensional, `im α = ker (ε ∘ f)`,
  `im β = ker (ε ∘ g)`, `im γ = ker ε`, `ε ∘ f`, `ε ∘ g` surjective and `α, β, γ` injective,
  the Euler characteristics satisfy `χ(D) = χ(D') + 1`. The third complex of the short exact
  sequence is `E × E → E`, `(a, b) ↦ a - b`, of Euler characteristic `1`
  (`CurvesJacobian.TwoTerm.chi_add`).
* `CurvesJacobian.surjective_pullbackRes`: evaluation of sections of an invertible sheaf over
  an affine open at a section `σ` landing in it is surjective.
* `CurvesJacobian.Cech.chi_twist`: `χ(P) = χ(M) + 1` for `P ≅ M ⊗ 𝒪(D)`, `D` the divisor of a
  section `σ` landing in `U ∩ V`, over the spectrum of a field.
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry Function
open AlgebraicGeometry.Scheme.Modules LinearMap Module

universe u

noncomputable section

namespace TwoCech

variable {F : Type*} [Field F]
variable {P Q R P' Q' R' E : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q] [Module F Q]
  [AddCommGroup R] [Module F R] [AddCommGroup P'] [Module F P'] [AddCommGroup Q'] [Module F Q']
  [AddCommGroup R'] [Module F R'] [AddCommGroup E] [Module F E]
  {f : P →ₗ[F] R} {g : Q →ₗ[F] R} {f' : P' →ₗ[F] R'} {g' : Q' →ₗ[F] R'}
  {α : P' →ₗ[F] P} {β : Q' →ₗ[F] Q} {γ : R' →ₗ[F] R} {ε : R →ₗ[F] E}

/-- The two-term complex `E × E → E`, `(a, b) ↦ a - b`, has Euler characteristic `1` when
`E` is one-dimensional. -/
lemma finrank_H0_id_id (hE : finrank F E = 1) :
    finrank F (H0 (LinearMap.id : E →ₗ[F] E) LinearMap.id) = 1 := by
  rw [← hE]
  refine (LinearEquiv.finrank_eq ?_)
  refine
    { toFun := fun x ↦ x.1.1
      invFun := fun e ↦ ⟨(e, e), mem_H0.mpr rfl⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun x ↦ Subtype.ext (Prod.ext rfl (mem_H0.mp x.2))
      right_inv := fun _ ↦ rfl }

lemma subsingleton_H1_id_id :
    Subsingleton (H1 (LinearMap.id : E →ₗ[F] E) LinearMap.id) := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  exact fun e ↦ ⟨(e, 0), by simp [d_apply]⟩

/-- **Removing a point lowers the Euler characteristic by one**: `χ(D) = χ(D') + 1` for the
exact sequence `0 → D' → D → (E × E → E) → 0` of two-set Čech data. -/
theorem chi_of_removePoint (hf : f ∘ₗ α = γ ∘ₗ f') (hg : g ∘ₗ β = γ ∘ₗ g')
    (hαi : Injective α) (hβi : Injective β) (hγi : Injective γ)
    (hα : range α = ker (ε ∘ₗ f)) (hβ : range β = ker (ε ∘ₗ g)) (hγ : range γ = ker ε)
    (hεf : Surjective (ε ∘ₗ f)) (hεg : Surjective (ε ∘ₗ g)) (hE : finrank F E = 1)
    [FiniteDimensional F (H0 f g)] [FiniteDimensional F (H1 f g)]
    [FiniteDimensional F (H0 f' g')] [FiniteDimensional F (H1 f' g')] :
    (finrank F (H0 f g) : ℤ) - finrank F (H1 f g) =
      ((finrank F (H0 f' g') : ℤ) - finrank F (H1 f' g')) + 1 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE
  haveI : FiniteDimensional F (H0 (LinearMap.id : E →ₗ[F] E) LinearMap.id) :=
    Module.finite_of_finrank_eq_succ (finrank_H0_id_id hE)
  haveI : Subsingleton (H1 (LinearMap.id : E →ₗ[F] E) LinearMap.id) := subsingleton_H1_id_id
  haveI : FiniteDimensional F (H1 (LinearMap.id : E →ₗ[F] E) LinearMap.id) :=
    Module.Finite.of_surjective (0 : E →ₗ[F] _) fun x ↦ ⟨0, Subsingleton.elim _ _⟩
  have hexα : Exact α (ε ∘ₗ f) := LinearMap.exact_iff.mpr hα.symm
  have hexβ : Exact β (ε ∘ₗ g) := LinearMap.exact_iff.mpr hβ.symm
  have hexγ : Exact γ ε := LinearMap.exact_iff.mpr hγ.symm
  have hεs : Surjective ε := fun e ↦ by
    obtain ⟨p, hp⟩ := hεf e
    exact ⟨f p, hp⟩
  have h₁ : γ ∘ₗ d f' g' = d f g ∘ₗ α.prodMap β := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, d_apply, LinearMap.prodMap_apply, map_sub]
    rw [← LinearMap.comp_apply f, hf, ← LinearMap.comp_apply g, hg]
    rfl
  have h₂ : ε ∘ₗ d f g = d LinearMap.id LinearMap.id ∘ₗ (ε ∘ₗ f).prodMap (ε ∘ₗ g) := by
    refine LinearMap.ext fun x ↦ ?_
    simp [d_apply]
  have key := CurvesJacobian.TwoTerm.chi_add (d₁ := d f' g') (d₂ := d f g)
    (d₃ := d (LinearMap.id : E →ₗ[F] E) LinearMap.id)
    (exact_prodMap α β (ε ∘ₗ f) (ε ∘ₗ g) hexα hexβ)
    (fun x y h ↦ Prod.ext (hαi (congrArg Prod.fst h)) (hβi (congrArg Prod.snd h)))
    (prodMap_surjective _ _ hεf hεg) hexγ hγi hεs h₁ h₂
  change (finrank F (H0 f g) : ℤ) - finrank F (H1 f g) =
    ((finrank F (H0 f' g') : ℤ) - finrank F (H1 f' g')) +
      ((finrank F (H0 (LinearMap.id : E →ₗ[F] E) LinearMap.id) : ℤ) -
        finrank F (H1 (LinearMap.id : E →ₗ[F] E) LinearMap.id)) at key
  rw [key, finrank_H0_id_id hE,
    Module.finrank_zero_of_subsingleton (M := H1 (LinearMap.id : E →ₗ[F] E) LinearMap.id)]
  norm_num

end TwoCech

namespace CurvesJacobian

/-- Evaluating sections of an invertible sheaf over an affine open `Z` at a section `σ`
landing in `Z` is surjective, when `Γ(Y, Z) → Γ(S)` is (base change). -/
lemma surjective_pullbackRes {S Y : Scheme.{u}} (σ : S ⟶ Y) [IsAffine S] (P : Y.Modules)
    [P.IsInvertible] {Z : Y.Opens} (hZa : IsAffineOpen Z) (hZ : ⊤ ≤ σ ⁻¹ᵁ Z)
    (hsurj : Surjective (σ.appLE Z ⊤ hZ)) : Surjective (pullbackRes σ P hZ) := by
  letI := (σ.appLE Z ⊤ hZ).hom.toAlgebra
  letI : Module Γ(Y, Z) Γ((Scheme.Modules.pullback σ).obj P, ⊤) :=
    Module.compHom _ (algebraMap Γ(Y, Z) Γ(S, ⊤))
  haveI : IsScalarTower Γ(Y, Z) Γ(S, ⊤) Γ((Scheme.Modules.pullback σ).obj P, ⊤) :=
    IsScalarTower.of_compHom _ _ _
  have hbc := isBaseChange_pullbackRes σ P hZ hZa (isAffineOpen_top S)
  exact (IsBaseChange.surjective_and_ker_eq hbc hsurj).1

/-- An invertible sheaf on the spectrum of a field has a nonzero global section. -/
lemma exists_ne_zero_sections_of_isField {S : Scheme.{u}} [IsAffine S] (hF : IsField Γ(S, ⊤))
    (L : S.Modules) [L.IsInvertible] : ∃ w : Γ(L, ⊤), w ≠ 0 := by
  letI := hF.toField
  haveI := invertible_sections L (isAffineOpen_top S)
  have h1 : Module.finrank Γ(S, ⊤) Γ(L, ⊤) = 1 := finrank_eq_one_of_invertible
  haveI := Module.nontrivial_of_finrank_eq_succ h1
  exact exists_ne 0

end CurvesJacobian

namespace CurvesJacobian.Cech

section ChiTwist

variable {S Y : Scheme.{u}} [Y.Over S] [IsAffine S] (σ : S ⟶ Y) (hσ : σ ≫ (Y ↘ S) = 𝟙 S)

include hσ in
/-- **Twisting by the divisor of a rational point raises `χ` by one**: for `Γ(S)` a field,
`σ : S → Y` a section landing in `U ∩ V`, `D` the divisor of `σ` and `P ≅ M ⊗ 𝒪(D)`,
`h⁰(P) − h¹(P) = h⁰(M) − h¹(M) + 1` for the Čech complexes of the charts `U`, `V`. -/
theorem chi_twist (hF : IsField Γ(S, ⊤)) {U V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) (hσW : ⊤ ≤ σ ⁻¹ᵁ (U ⊓ V))
    {T : Scheme.{u}} {fD : Y ⟶ T} (D : RelEffCartier fD) [QuasiCompact σ] (hD : D.ideal = σ.ker)
    (M P : Y.Modules) [M.IsInvertible] [P.IsInvertible] (e : P ≅ M ⊗ D.lineBundle)
    [Module.Finite Γ(S, ⊤) (cechModH0 S P U V)] [Module.Finite Γ(S, ⊤) (cechModH1 S P U V)]
    [Module.Finite Γ(S, ⊤) (cechModH0 S M U V)] [Module.Finite Γ(S, ⊤) (cechModH1 S M U V)] :
    (finrank Γ(S, ⊤) (cechModH0 S P U V) : ℤ) - finrank Γ(S, ⊤) (cechModH1 S P U V) =
      ((finrank Γ(S, ⊤) (cechModH0 S M U V) : ℤ) - finrank Γ(S, ⊤) (cechModH1 S M U V)) + 1 := by
  letI := hF.toField
  have hσU : ⊤ ≤ σ ⁻¹ᵁ U := hσW.trans (σ.preimage_mono inf_le_left)
  have hσV : ⊤ ≤ σ ⁻¹ᵁ V := hσW.trans (σ.preimage_mono inf_le_right)
  -- transport from `P` to `M ⊗ 𝒪(D)`
  have hf := sectionsIso_res (S := S) e (inf_le_left : U ⊓ V ≤ U)
  have hg := sectionsIso_res (S := S) e (inf_le_right : U ⊓ V ≤ V)
  let e0 := TwoCech.equivH0 _ _ _ hf hg
  let e1 := TwoCech.equivH1 _ _ _ hf hg
  haveI : Module.Finite Γ(S, ⊤) (cechModH0 S (M ⊗ D.lineBundle) U V) := Module.Finite.equiv e0
  haveI : Module.Finite Γ(S, ⊤) (cechModH1 S (M ⊗ D.lineBundle) U V) := Module.Finite.equiv e1
  rw [e0.finrank_eq, e1.finrank_eq]
  -- the image of twisting by the canonical section is the kernel of evaluation at `σ`
  have hrange : ∀ {Z : Y.Opens} (hZa : IsAffineOpen Z) (hZ : ⊤ ≤ σ ⁻¹ᵁ Z)
      (y : Γ(M ⊗ D.lineBundle, Z)),
      y ∈ LinearMap.range (twistLin (S := S) M D.lineBundle D.canonicalSection Z) ↔
        pullbackRes σ (M ⊗ D.lineBundle) hZ y = 0 := fun {Z} hZa hZ y ↦ by
    rw [mem_range_twistLin_iff M D.lineBundle D.canonicalSection hZa,
      D.contentIdeal_canonicalSection ⟨Z, hZa⟩, hD, Scheme.Hom.ker_apply,
      ker_app_eq_ker_appLE σ hZ,
      pullbackRes_eq_zero_iff σ _ hZa hZ (surjective_appLE σ hσ hZ)]
  have hinj : ∀ {Z : Y.Opens} (hZa : IsAffineOpen Z),
      Injective (twistLin (S := S) M D.lineBundle D.canonicalSection Z) := fun hZa ↦
    injective_twistLin M _ _ hZa (D.injective_smul_canonicalSection _)
  -- evaluation at `σ` on `U ∩ V`, as a map to a quotient
  let NW : Submodule Γ(Y, U ⊓ V) Γ(M ⊗ D.lineBundle, U ⊓ V) :=
    RingHom.ker (σ.appLE (U ⊓ V) ⊤ hσW).hom • ⊤
  let ε := (NW.restrictScalars Γ(S, ⊤)).mkQ
  have hε : ∀ y, ε y = 0 ↔ pullbackRes σ (M ⊗ D.lineBundle) hσW y = 0 := fun y ↦ by
    rw [pullbackRes_eq_zero_iff σ _ hUV hσW (surjective_appLE σ hσ hσW)]
    exact (Submodule.Quotient.mk_eq_zero _).trans (Submodule.restrictScalars_mem _ _ _)
  have hres : ∀ {Z : Y.Opens} (h : U ⊓ V ≤ Z) (hZ : ⊤ ≤ σ ⁻¹ᵁ Z) (y : Γ(M ⊗ D.lineBundle, Z)),
      pullbackRes σ (M ⊗ D.lineBundle) hσW ((M ⊗ D.lineBundle).presheaf.map (homOfLE h).op y) =
        pullbackRes σ (M ⊗ D.lineBundle) hZ y := fun {Z} h hZ y ↦ by
    have hid : (homOfLE (le_rfl : (⊤ : S.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := rfl
    simp only [pullbackRes_res σ (M ⊗ D.lineBundle) hZ h le_rfl hσW y, hid,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hα : LinearMap.range (twistLin (S := S) M D.lineBundle D.canonicalSection U) =
      LinearMap.ker (ε ∘ₗ resModLin S (M ⊗ D.lineBundle) (inf_le_left : U ⊓ V ≤ U)) := by
    ext y
    rw [hrange hU hσU, LinearMap.mem_ker, LinearMap.comp_apply, hε]
    exact (hres inf_le_left hσU y).symm ▸ Iff.rfl
  have hβ : LinearMap.range (twistLin (S := S) M D.lineBundle D.canonicalSection V) =
      LinearMap.ker (ε ∘ₗ resModLin S (M ⊗ D.lineBundle) (inf_le_right : U ⊓ V ≤ V)) := by
    ext y
    rw [hrange hV hσV, LinearMap.mem_ker, LinearMap.comp_apply, hε]
    exact (hres inf_le_right hσV y).symm ▸ Iff.rfl
  have hγ : LinearMap.range (twistLin (S := S) M D.lineBundle D.canonicalSection (U ⊓ V)) =
      LinearMap.ker ε := by
    ext y
    rw [hrange hUV hσW, LinearMap.mem_ker, hε]
  -- surjectivity of evaluation from `U` and from `V`
  have hsurjZ : ∀ {Z : Y.Opens} (hZa : IsAffineOpen Z) (h : U ⊓ V ≤ Z) (hZ : ⊤ ≤ σ ⁻¹ᵁ Z),
      Surjective (ε ∘ₗ resModLin S (M ⊗ D.lineBundle) h) := fun {Z} hZa h hZ c ↦ by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨x, hx⟩ := surjective_pullbackRes σ (M ⊗ D.lineBundle) hZa hZ
      (surjective_appLE σ hσ hZ) (pullbackRes σ (M ⊗ D.lineBundle) hσW y)
    refine ⟨x, ?_⟩
    rw [LinearMap.comp_apply, ← sub_eq_zero]
    change ε _ - ε y = 0
    rw [← map_sub, hε, map_sub, resModLin_apply, hres h hZ, hx, sub_self]
  -- `E` is one-dimensional
  have hE1 : finrank Γ(S, ⊤) (Γ(M ⊗ D.lineBundle, U ⊓ V) ⧸ NW.restrictScalars Γ(S, ⊤)) = 1 := by
    obtain ⟨w, hw⟩ := exists_ne_zero_sections_of_isField hF
      ((Scheme.Modules.pullback σ).obj (M ⊗ D.lineBundle))
    obtain ⟨y, rfl⟩ := surjective_pullbackRes σ (M ⊗ D.lineBundle) hUV hσW
      (surjective_appLE σ hσ hσW) w
    have hy : ε y ≠ 0 := fun h0 ↦ hw ((hε y).mp h0)
    refine (finrank_eq_one_iff_of_nonzero' _ hy).mpr fun w' ↦ ?_
    obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    obtain ⟨μ, hμ⟩ := exists_eq_smul_of_ne_zero hF _ hw (pullbackRes σ _ hσW x₂)
    refine ⟨μ, ?_⟩
    change μ • Submodule.Quotient.mk y = Submodule.Quotient.mk x₂
    rw [← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
    refine (hε _).mpr ?_
    rw [map_sub, smul_sections_def, pullbackRes_smul, appLE_algebraMap σ hσ hσW, hμ, sub_self]
  have hfU := twistLin_comp_res (S := S) M D.lineBundle D.canonicalSection
    (inf_le_left : U ⊓ V ≤ U)
  have hgV := twistLin_comp_res (S := S) M D.lineBundle D.canonicalSection
    (inf_le_right : U ⊓ V ≤ V)
  exact TwoCech.chi_of_removePoint hfU hgV (hinj hU) (hinj hV) (hinj hUV) hα hβ hγ
    (hsurjZ hU inf_le_left hσU) (hsurjZ hV inf_le_right hσV) hE1

end ChiTwist

end CurvesJacobian.Cech
