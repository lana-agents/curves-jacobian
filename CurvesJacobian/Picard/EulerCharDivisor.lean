/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.EulerCharTwist
import CurvesJacobian.Picard.ZeroSchemeDegree
import CurvesJacobian.Picard.CechGlobal
import Mathlib.AlgebraicGeometry.Artinian

/-!
# Twisting by an effective divisor: `χ(M(D)) = χ(M) + h⁰(𝒪_D)`

Let `Y` be a scheme over the spectrum `S` of a field, covered by affine opens `U`, `V` with
affine intersection `U ∩ V = D(τ) ⊆ U`, and `D ⊂ Y` a relative effective Cartier divisor whose
underlying scheme is locally Artinian (e.g. finite over `S`). For `M` invertible, the short exact
sequence `0 → M → M(D) → M(D)|_D → 0` gives `χ(M(D)) = χ(M) + h⁰(D, M(D)|_D)` for the chart Čech
complexes (`CurvesJacobian.Cech.chi_twist_divisor`). The third complex is the Čech complex of
`M(D)|_D` for the covering `(D ∩ U, D ∩ V)` of `D`: its `H⁰` is `Γ(D, M(D)|_D)` (sheaf axiom) and
its `H¹` vanishes since restriction `Γ(D ∩ U) → Γ(D ∩ U ∩ V)` is a localization of an Artinian
ring, hence surjective (`IsArtinianRing.localization_surjective`, module version
`CurvesJacobian.surjective_of_isLocalizedModule_of_isArtinianRing`).

This is the degree computation `deg 𝒪(D) = deg D` behind the additivity of the degree
`χ = d + 1 − g` in Stacks, Lemma 44.6.7 (Tag 0BA0).

* `TwoCech.chi_of_shortExact`: `χ(D) = χ(D') + χ(D'')` for a short exact sequence of two-set
  Čech data over a field (from `CurvesJacobian.TwoTerm.chi_add`).
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry Function
open AlgebraicGeometry.Scheme.Modules LinearMap Module

universe u

noncomputable section

namespace TwoCech

variable {F : Type*} [Field F]
variable {P Q R P' Q' R' P'' Q'' R'' : Type*} [AddCommGroup P] [Module F P] [AddCommGroup Q]
  [Module F Q] [AddCommGroup R] [Module F R] [AddCommGroup P'] [Module F P'] [AddCommGroup Q']
  [Module F Q'] [AddCommGroup R'] [Module F R'] [AddCommGroup P''] [Module F P'']
  [AddCommGroup Q''] [Module F Q''] [AddCommGroup R''] [Module F R'']
  {f : P →ₗ[F] R} {g : Q →ₗ[F] R} {f' : P' →ₗ[F] R'} {g' : Q' →ₗ[F] R'}
  {f'' : P'' →ₗ[F] R''} {g'' : Q'' →ₗ[F] R''}
  {α₁ : P' →ₗ[F] P} {β₁ : Q' →ₗ[F] Q} {γ₁ : R' →ₗ[F] R}
  {α₂ : P →ₗ[F] P''} {β₂ : Q →ₗ[F] Q''} {γ₂ : R →ₗ[F] R''}

/-- **Additivity of `χ` for short exact sequences of two-set Čech data** over a field. -/
theorem chi_of_shortExact (hf₁ : f ∘ₗ α₁ = γ₁ ∘ₗ f') (hg₁ : g ∘ₗ β₁ = γ₁ ∘ₗ g')
    (hf₂ : f'' ∘ₗ α₂ = γ₂ ∘ₗ f) (hg₂ : g'' ∘ₗ β₂ = γ₂ ∘ₗ g)
    (hα : Exact α₁ α₂) (hβ : Exact β₁ β₂) (hγ : Exact γ₁ γ₂)
    (hα₁ : Injective α₁) (hβ₁ : Injective β₁) (hγ₁ : Injective γ₁)
    (hα₂ : Surjective α₂) (hβ₂ : Surjective β₂) (hγ₂ : Surjective γ₂)
    [FiniteDimensional F (H0 f g)] [FiniteDimensional F (H1 f g)]
    [FiniteDimensional F (H0 f' g')] [FiniteDimensional F (H1 f' g')]
    [FiniteDimensional F (H0 f'' g'')] [FiniteDimensional F (H1 f'' g'')] :
    (finrank F (H0 f g) : ℤ) - finrank F (H1 f g) =
      ((finrank F (H0 f' g') : ℤ) - finrank F (H1 f' g')) +
        ((finrank F (H0 f'' g'') : ℤ) - finrank F (H1 f'' g'')) := by
  have h₁ : γ₁ ∘ₗ d f' g' = d f g ∘ₗ α₁.prodMap β₁ := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, d_apply, LinearMap.prodMap_apply, map_sub]
    rw [← LinearMap.comp_apply f, hf₁, ← LinearMap.comp_apply g, hg₁]
    rfl
  have h₂ : γ₂ ∘ₗ d f g = d f'' g'' ∘ₗ α₂.prodMap β₂ := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, d_apply, LinearMap.prodMap_apply, map_sub]
    rw [← LinearMap.comp_apply f'', hf₂, ← LinearMap.comp_apply g'', hg₂]
    rfl
  exact CurvesJacobian.TwoTerm.chi_add (d₁ := d f' g') (d₂ := d f g) (d₃ := d f'' g'')
    (exact_prodMap α₁ β₁ α₂ β₂ hα hβ)
    (fun x y h ↦ Prod.ext (hα₁ (congrArg Prod.fst h)) (hβ₁ (congrArg Prod.snd h)))
    (prodMap_surjective _ _ hα₂ hβ₂) hγ hγ₁ hγ₂ h₁ h₂

/-- `H¹ = 0` when the first restriction map is surjective. -/
lemma subsingleton_H1_of_surjective (hf : Surjective f) : Subsingleton (H1 f g) := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  intro r
  obtain ⟨p, rfl⟩ := hf r
  exact ⟨(p, 0), by simp [d_apply]⟩

end TwoCech

namespace CurvesJacobian

/-- Localization of a module over an Artinian ring at one element is surjective. -/
theorem surjective_of_isLocalizedModule_of_isArtinianRing {R M M' : Type*} [CommRing R]
    [IsArtinianRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (r : R)
    (φ : M →ₗ[R] M') [IsLocalizedModule (Submonoid.powers r) φ] : Surjective φ := by
  intro x
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers r) φ x
  obtain ⟨n, c, hc⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
  refine ⟨c • m, ?_⟩
  change φ (c • m) = IsLocalizedModule.mk' φ m s
  symm
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← LinearMap.map_smul, ← sub_eq_zero,
    ← LinearMap.map_sub]
  have hu := IsLocalizedModule.map_units φ ⟨(s : R) ^ n, pow_mem s.2 n⟩
  rw [Module.End.isUnit_iff] at hu
  apply hu.1
  rw [LinearMap.map_zero]
  change ((s : R) ^ n) • φ (m - (s : R) • c • m) = 0
  rw [← LinearMap.map_smul, smul_sub, smul_smul, smul_smul, ← pow_succ]
  have : (s : R) ^ (n + 1) * c = (s : R) ^ n := by
    simpa [smul_eq_mul] using hc
  rw [this, sub_self, LinearMap.map_zero]

/-- Restriction of a quasi-coherent sheaf from an affine open `U` with Artinian ring of sections
to a basic open of `U` is surjective. -/
theorem surjective_res_of_isArtinianRing {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U W : X.Opens} (hU : IsAffineOpen U) [IsArtinianRing Γ(X, U)] (t : Γ(X, U))
    (hW : X.basicOpen t = W) (hle : W ≤ U) : Surjective (F.presheaf.map (homOfLE hle).op) := by
  subst hW
  haveI := F.isLocalizedModule_resBasicOpen hU t
  exact surjective_of_isLocalizedModule_of_isArtinianRing t (F.resBasicOpen t)

end CurvesJacobian

namespace CurvesJacobian.Cech

open Scheme

section Divisor

variable {S Y : Scheme.{u}} [Y.Over S] [IsAffine S] {T : Scheme.{u}} {fD : Y ⟶ T}
  (D : RelEffCartier fD)

attribute [local instance] subschemeOver

omit [IsAffine S] in
/-- Evaluation `Γ(N, W) → Γ(N|_D, D ∩ W)` on an affine `W` is surjective with kernel
`I_D(W) · Γ(N, W)`. -/
theorem thetaSec_surjective_ker_ideal (N : Y.Modules) [N.IsInvertible] {W : Y.Opens}
    (hW : IsAffineOpen W) {W' : D.ideal.subscheme.Opens} (hW' : W' = D.ideal.subschemeι ⁻¹ᵁ W) :
    Surjective (thetaSec S N D.ideal hW'.le) ∧ ∀ m, thetaSec S N D.ideal hW'.le m = 0 ↔
      m ∈ D.ideal.ideal ⟨W, hW⟩ • (⊤ : Submodule Γ(Y, W) Γ(N, W)) := by
  subst hW'
  set I := D.ideal
  letI := (I.subschemeι.appLE W (I.subschemeι ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  letI : Module Γ(Y, W) Γ((Scheme.Modules.pullback I.subschemeι).obj N, I.subschemeι ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap Γ(Y, W) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W))
  haveI : IsScalarTower Γ(Y, W) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W)
      Γ((Scheme.Modules.pullback I.subschemeι).obj N, I.subschemeι ⁻¹ᵁ W) :=
    IsScalarTower.of_compHom _ _ _
  have hb := isBaseChange_pullbackRes I.subschemeι N le_rfl hW (hW.preimage I.subschemeι)
  have happ : algebraMap Γ(Y, W) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W) =
      (I.subschemeι.app W).hom := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  have hS : Surjective (algebraMap Γ(Y, W) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W)) := by
    rw [happ]
    exact I.subschemeι_app_surjective ⟨W, hW⟩
  have hker : RingHom.ker (algebraMap Γ(Y, W) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W)) =
      I.ideal ⟨W, hW⟩ := by
    rw [happ]
    exact I.ker_subschemeι_app ⟨W, hW⟩
  obtain ⟨hsurj, hk⟩ := IsBaseChange.surjective_and_ker_eq hb hS
  rw [hker] at hk
  exact ⟨hsurj, fun m ↦ (SetLike.ext_iff.mp hk m)⟩

variable [IsLocallyArtinian D.ideal.subscheme]

set_option hygiene false in
local notation "ιD" => (RelEffCartier.ideal D).subschemeι
set_option hygiene false in
local notation "ZD" => (RelEffCartier.ideal D).subscheme
set_option hygiene false in
local notation "ND" => (M ⊗ RelEffCartier.lineBundle D)
set_option hygiene false in
local notation "NZ" =>
  (Scheme.Modules.pullback (RelEffCartier.ideal D).subschemeι).obj (M ⊗ RelEffCartier.lineBundle D)

omit [IsAffine S] in
/-- **Twisting by an effective divisor** (Stacks, Lemma 44.6.7, Tag 0BA0, degree computation):
for `Γ(S)` a field, a covering `Y = U ∪ V` by affine opens with `U ∩ V = D(τ) ⊆ U`, and a
relative effective Cartier divisor `D` with locally Artinian underlying scheme,
`h⁰(M(D)) − h¹(M(D)) = h⁰(M) − h¹(M) + dim Γ(D, M(D)|_D)`. -/
theorem chi_twist_divisor (hF : IsField Γ(S, ⊤)) {U V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) (hcov : U ⊔ V = ⊤) (τ : Γ(Y, U))
    (hτ : Y.basicOpen τ = U ⊓ V) (M : Y.Modules) [M.IsInvertible]
    [Module.Finite Γ(S, ⊤) (cechModH0 S (M ⊗ D.lineBundle) U V)]
    [Module.Finite Γ(S, ⊤) (cechModH1 S (M ⊗ D.lineBundle) U V)]
    [Module.Finite Γ(S, ⊤) (cechModH0 S M U V)] [Module.Finite Γ(S, ⊤) (cechModH1 S M U V)]
    [Module.Finite Γ(S, ⊤)
      Γ((Scheme.Modules.pullback D.ideal.subschemeι).obj (M ⊗ D.lineBundle), ⊤)] :
    (finrank Γ(S, ⊤) (cechModH0 S (M ⊗ D.lineBundle) U V) : ℤ) -
        finrank Γ(S, ⊤) (cechModH1 S (M ⊗ D.lineBundle) U V) =
      ((finrank Γ(S, ⊤) (cechModH0 S M U V) : ℤ) - finrank Γ(S, ⊤) (cechModH1 S M U V)) +
        finrank Γ(S, ⊤)
          Γ((Scheme.Modules.pullback D.ideal.subschemeι).obj (M ⊗ D.lineBundle), ⊤) := by
  letI := hF.toField
  have hU' : IsAffineOpen (ιD ⁻¹ᵁ U) := hU.preimage ιD
  have hcov' : ιD ⁻¹ᵁ U ⊔ ιD ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcov, Scheme.Hom.preimage_top]
  -- the rows `0 → Γ(M, W) → Γ(M(D), W) → Γ(M(D)|_D, D ∩ W) → 0`
  have hrow : ∀ {W : Y.Opens} (hW : IsAffineOpen W) {W' : (ZD).Opens} (hW' : W' = ιD ⁻¹ᵁ W),
      Exact (twistLin (S := S) M D.lineBundle D.canonicalSection W)
        (thetaSec S ND D.ideal hW'.le) := fun {W} hW {W'} hW' y ↦ by
    rw [(thetaSec_surjective_ker_ideal D ND hW hW').2 y, Set.mem_range,
      ← LinearMap.mem_range, mem_range_twistLin_iff M D.lineBundle D.canonicalSection hW,
      D.contentIdeal_canonicalSection ⟨W, hW⟩]
  have hinj : ∀ {W : Y.Opens} (hW : IsAffineOpen W),
      Injective (twistLin (S := S) M D.lineBundle D.canonicalSection W) := fun hW ↦
    injective_twistLin M _ _ hW (D.injective_smul_canonicalSection _)
  have hsurj : ∀ {W : Y.Opens} (hW : IsAffineOpen W) {W' : (ZD).Opens} (hW' : W' = ιD ⁻¹ᵁ W),
      Surjective (thetaSec S ND D.ideal hW'.le) := fun hW _ hW' ↦
    (thetaSec_surjective_ker_ideal D ND hW hW').1
  have hθ : ∀ {W₁ W₂ : Y.Opens} (h : W₂ ≤ W₁) {W₁' W₂' : (ZD).Opens} (e₁ : W₁' = ιD ⁻¹ᵁ W₁)
      (e₂ : W₂' = ιD ⁻¹ᵁ W₂) (h' : W₂' ≤ W₁'),
      resModLin S NZ h' ∘ₗ thetaSec S ND D.ideal e₁.le =
        thetaSec S ND D.ideal e₂.le ∘ₗ resModLin S ND h :=
    fun {W₁ W₂} h {W₁' W₂'} e₁ e₂ h' ↦ by
    refine LinearMap.ext fun m ↦ ?_
    change _ = pullbackRes ιD ND e₂.le ((ND).presheaf.map (homOfLE h).op m)
    rw [pullbackRes_res ιD ND e₁.le h h' e₂.le]
    rfl
  -- the third complex: the Čech complex of `M(D)|_D` for `(D ∩ U, D ∩ V)`
  have hres : Surjective (resModLin S NZ (inf_le_left : ιD ⁻¹ᵁ U ⊓ ιD ⁻¹ᵁ V ≤ ιD ⁻¹ᵁ U)) := by
    haveI := isQuasicoherent_of_isInvertible NZ
    haveI : IsArtinianRing Γ(ZD, ιD ⁻¹ᵁ U) :=
      IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨ιD ⁻¹ᵁ U, hU'⟩
    have hbo : (ZD).basicOpen ((ιD).app U τ) = ιD ⁻¹ᵁ U ⊓ ιD ⁻¹ᵁ V := by
      rw [← Scheme.preimage_basicOpen, hτ]
      rfl
    exact surjective_res_of_isArtinianRing NZ hU' ((ιD).app U τ) hbo inf_le_left
  haveI : Subsingleton (cechModH1 S NZ (ιD ⁻¹ᵁ U) (ιD ⁻¹ᵁ V)) :=
    TwoCech.subsingleton_H1_of_surjective hres
  let e0 := globalSectionsEquivH0 S NZ hcov'
  haveI : Module.Finite Γ(S, ⊤) (cechModH0 S NZ (ιD ⁻¹ᵁ U) (ιD ⁻¹ᵁ V)) := Module.Finite.equiv e0
  haveI : Module.Finite Γ(S, ⊤) (cechModH1 S NZ (ιD ⁻¹ᵁ U) (ιD ⁻¹ᵁ V)) :=
    Module.Finite.of_surjective (0 : Γ(S, ⊤) →ₗ[Γ(S, ⊤)] _) fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  have key := TwoCech.chi_of_shortExact
    (twistLin_comp_res (S := S) M D.lineBundle D.canonicalSection (inf_le_left : U ⊓ V ≤ U))
    (twistLin_comp_res (S := S) M D.lineBundle D.canonicalSection (inf_le_right : U ⊓ V ≤ V))
    (hθ (inf_le_left : U ⊓ V ≤ U) (W₁' := ιD ⁻¹ᵁ U) (W₂' := ιD ⁻¹ᵁ U ⊓ ιD ⁻¹ᵁ V) rfl rfl
      inf_le_left)
    (hθ (inf_le_right : U ⊓ V ≤ V) (W₁' := ιD ⁻¹ᵁ V) (W₂' := ιD ⁻¹ᵁ U ⊓ ιD ⁻¹ᵁ V) rfl rfl
      inf_le_right)
    (hrow hU rfl) (hrow hV rfl) (hrow hUV (W' := ιD ⁻¹ᵁ U ⊓ ιD ⁻¹ᵁ V) rfl)
    (hinj hU) (hinj hV) (hinj hUV) (hsurj hU rfl) (hsurj hV rfl)
    (hsurj hUV (W' := ιD ⁻¹ᵁ U ⊓ ιD ⁻¹ᵁ V) rfl)
  rw [key, ← e0.finrank_eq,
    Module.finrank_zero_of_subsingleton (M := cechModH1 S NZ (ιD ⁻¹ᵁ U) (ιD ⁻¹ᵁ V))]
  push_cast
  ring

end Divisor

end CurvesJacobian.Cech
