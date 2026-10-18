/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ZeroSchemeAlgebra
import CurvesJacobian.Picard.CurveGenus
import CurvesJacobian.Picard.RelEffCartierFinite
import CurvesJacobian.Picard.FinrankFibre
import CurvesJacobian.Picard.QcohBaseChange
import CurvesJacobian.Picard.PerfectOpen

/-!
# The degree of the zero scheme of a section (Stacks, Lemma 44.6.4, Tag 0B9X)

In the proof of Stacks, Lemma 44.6.4 (Tag 0B9X), a line bundle `L` on `X_T = C ×_k T` in the
`F`-subfunctor gives a section `s` whose zero scheme `Z` is a relative effective Cartier divisor
of degree `g`. This file proves the degree statement, relatively over an affine base and
without passing to fibres:

* `CurvesJacobian.invertible_sections`: sections of an invertible sheaf over an affine open
  form an invertible module;
* `CurvesJacobian.sectionsEquivCechH0`: the sheaf axiom for a covering by two opens;
* `CurvesJacobian.quotH0ToCechH1_bijective` (step 1): for `0 → 𝒪 →(s) L → Q → 0` on the charts
  `U, V`, if `s` is regular on `U ∩ V`, `Ȟ¹(L) = 0` and `Ȟ⁰(L) = Γ(S) · s`, then the connecting
  map `Ȟ⁰(Q) → Ȟ¹(𝒪)` is bijective;
* `CurvesJacobian.zeroSchemeSectionsEquiv` (step 3): if the ideal of `Z ⊂ Y` on `U`, `V`, `U ∩ V`
  is the content ideal of `s`, then `Γ(Z, ι^*L) ≅ Ȟ⁰(Q) ≅ Ȟ¹(𝒪_Y)`;
* `CurvesJacobian.rankAtStalk_sections_pullback` (step 4): `Γ(Z, ι^*L)` and `Γ(Z, 𝒪_Z)` have the
  same rank over `Γ(S)` when `Z → S` is finite flat;
* `CurvesJacobian.rankAtStalk_cechH1_curve` (step 2) and the main result
  `CurvesJacobian.degree_zeroScheme_eq_curveGenus`: `deg(Z/T) = g(C)` at every point of `T`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite Function
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

section Invertible

variable {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] {U : X.Opens}

/-- **Sections of an invertible sheaf over an affine open form an invertible module.** -/
theorem invertible_sections (hU : IsAffineOpen U) : Module.Invertible Γ(X, U) Γ(L, U) := by
  haveI := isQuasicoherent_of_isInvertible L
  haveI := finite_sections L hU
  haveI := projective_sections L hU
  refine PerfectOpen.invertible_of_rankAtStalk fun q ↦ ?_
  obtain ⟨f, hf, hfq⟩ : ∃ f ∈ L.trivSet U, f ∉ q.asIdeal := by
    by_contra! H
    exact q.isPrime.ne_top (top_le_iff.mp
      ((span_trivSet_eq_top L hU).symm.le.trans (Ideal.span_le.mpr H)))
  obtain ⟨m, hm⟩ := hf
  haveI := hU.isLocalization_basicOpen f
  haveI := L.isLocalizedModule_resBasicOpen hU f
  have hb : IsBaseChange Γ(X, X.basicOpen f) (L.resBasicOpen f) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers f) _ _
  have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen f))) := by
    rw [PrimeSpectrum.localization_away_comap_range Γ(X, X.basicOpen f) f]
    exact hfq
  obtain ⟨q', rfl⟩ := hq
  haveI : Nontrivial Γ(X, X.basicOpen f) := q'.nontrivial
  haveI : Module.Free Γ(X, X.basicOpen f) Γ(L, X.basicOpen f) := Module.Free.of_equiv hm.equiv
  rw [← Module.rankAtStalk_isBaseChange hb, Module.rankAtStalk_eq_finrank_of_free,
    ← hm.equiv.finrank_eq, Module.finrank_self]
  rfl

end Invertible

section Rank

variable {S Y : Scheme.{u}} [Y.Over S] [IsAffine S] (L : Y.Modules) [L.IsInvertible]
  (I : Y.IdealSheafData)

lemma appLE_top_eq_appTop {X Z : Scheme.{u}} (f : X ⟶ Z) :
    f.appLE ⊤ ⊤ le_top = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

lemma rankAtStalk_algebra_congr {A B : Type u} [CommRing A] [CommRing B] {φ ψ : A →+* B}
    (h : φ = ψ) (p : PrimeSpectrum A) :
    @Module.rankAtStalk A B _ _ φ.toAlgebra.toModule p =
      @Module.rankAtStalk A B _ _ ψ.toAlgebra.toModule p := by
  subst h; rfl

variable [IsFinite (I.subschemeι ≫ (Y ↘ S))] [Flat (I.subschemeι ≫ (Y ↘ S))]

/-- **Step 4 of Stacks, Lemma 44.6.4 (Tag 0B9X)**: for `Z = V(I)` finite flat over the affine
`S`, `Γ(Z, ι^*L)` has the same rank as `Γ(Z, 𝒪_Z)` at every prime of `Γ(S)`. -/
theorem rankAtStalk_sections_pullback (p : PrimeSpectrum Γ(S, ⊤)) :
    letI := ((I.subschemeι ≫ (Y ↘ S)).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) :=
      Module.compHom _ (algebraMap Γ(S, ⊤) Γ(I.subscheme, ⊤))
    Module.rankAtStalk Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) p =
      Module.rankAtStalk Γ(I.subscheme, ⊤) p := by
  letI := ((I.subschemeι ≫ (Y ↘ S)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) :=
    Module.compHom _ (algebraMap Γ(S, ⊤) Γ(I.subscheme, ⊤))
  haveI : IsScalarTower Γ(S, ⊤) Γ(I.subscheme, ⊤)
      Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) := IsScalarTower.of_compHom _ _ _
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ (Y ↘ S))
  haveI := invertible_sections ((Scheme.Modules.pullback I.subschemeι).obj L)
    (isAffineOpen_top I.subscheme)
  haveI : Module.Finite Γ(S, ⊤) Γ(I.subscheme, ⊤) := by
    have := Scheme.Hom.finite_appTop (I.subschemeι ≫ (Y ↘ S))
    rw [← appLE_top_eq_appTop] at this
    exact this
  haveI : Module.Flat Γ(S, ⊤) Γ(I.subscheme, ⊤) :=
    HasRingHomProperty.appLE (P := @Flat) (I.subschemeι ≫ (Y ↘ S)) ‹_›
      ⟨⊤, isAffineOpen_top S⟩ ⟨⊤, isAffineOpen_top _⟩ le_top
  exact rankAtStalk_eq_of_invertible p

/-- The degree of `Z → S` at `t` is the rank of `Γ(Z, 𝒪_Z)` over `Γ(S)`. -/
theorem finrank_eq_rankAtStalk_sections (t : S) :
    letI := ((I.subschemeι ≫ (Y ↘ S)).appLE ⊤ ⊤ le_top).hom.toAlgebra
    (I.subschemeι ≫ (Y ↘ S)).finrank t =
      Module.rankAtStalk Γ(I.subscheme, ⊤) ((isAffineOpen_top S).primeIdealOf ⟨t, trivial⟩) := by
  refine (Scheme.Hom.finrank_eq_rankAtStalk _ (isAffineOpen_top S) t trivial).trans ?_
  exact rankAtStalk_algebra_congr (congrArg CommRingCat.Hom.hom
    (appLE_top_eq_appTop (I.subschemeι ≫ (Y ↘ S))).symm) _

end Rank

open Cech

section Glue

variable {S Y : Scheme.{u}} [Y.Over S] (M : Y.Modules) (U V : Y.Opens)

omit [Y.Over S] in
lemma presheaf_map_map_apply {W₁ W₂ W₃ : Y.Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂)
    (x : Γ(M, W₁)) : M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of global sections to the two-set Čech `H⁰`. -/
def toCechH0 : Γ(M, ⊤) →ₗ[Γ(S, ⊤)] cechModH0 S M U V :=
  LinearMap.codRestrict _ ((resModLin S M (le_top : U ≤ ⊤)).prod
    (resModLin S M (le_top : V ≤ ⊤))) fun x ↦ by
    rw [TwoCech.mem_H0]
    change M.presheaf.map (homOfLE inf_le_left).op (M.presheaf.map (homOfLE le_top).op x) =
      M.presheaf.map (homOfLE inf_le_right).op (M.presheaf.map (homOfLE le_top).op x)
    rw [presheaf_map_map_apply, presheaf_map_map_apply]

lemma toCechH0_apply (x : Γ(M, ⊤)) :
    (toCechH0 (S := S) M U V x : Γ(M, U) × Γ(M, V)) =
      (M.presheaf.map (homOfLE le_top).op x, M.presheaf.map (homOfLE le_top).op x) := rfl

/-- **Sheaf axiom for two opens**: if `U ∪ V = Y`, global sections are the Čech `H⁰`. -/
theorem toCechH0_bijective (h : U ⊔ V = ⊤) : Bijective (toCechH0 (S := S) M U V) := by
  let F : TopCat.Sheaf Ab.{u} Y := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg (fun y : cechModH0 S M U V ↦ (y : Γ(M, U) × Γ(M, V)).1) hx
    have h2 := congrArg (fun y : cechModH0 S M U V ↦ (y : Γ(M, U) × Γ(M, V)).2) hx
    simp only [toCechH0_apply, ZeroMemClass.coe_zero, Prod.fst_zero, Prod.snd_zero] at h1 h2
    refine sheaf_eq_of_locally_eq F x 0 fun y _ ↦ ?_
    have hy : y ∈ U ⊔ V := h ▸ trivial
    rcases Opens.mem_sup.mp hy with hyU | hyV
    · exact ⟨U, le_top, hyU, by rw [map_zero]; exact h1⟩
    · exact ⟨V, le_top, hyV, by rw [map_zero]; exact h2⟩
  · rintro ⟨⟨a, b⟩, hab⟩
    rw [TwoCech.mem_H0] at hab
    simp only [resModLin_apply] at hab
    let W : Bool → Y.Opens := fun i ↦ cond i U V
    let sf : ∀ i, ToType (F.1.obj (op (W i))) := fun i ↦
      Bool.rec (motive := fun i ↦ ToType (F.1.obj (op (cond i U V)))) b a i
    have hcompat : TopCat.Presheaf.IsCompatible F.1 W sf := by
      intro i j
      cases i <;> cases j
      · exact congrArg (fun φ : (V ⊓ V ⟶ V) ↦ F.1.map φ.op b) (Subsingleton.elim _ _)
      · have := congrArg (M.presheaf.map (homOfLE (inf_comm V U).le).op) hab
        rw [presheaf_map_map_apply, presheaf_map_map_apply] at this
        exact this.symm
      · exact hab
      · exact congrArg (fun φ : (U ⊓ U ⟶ U) ↦ F.1.map φ.op a) (Subsingleton.elim _ _)
    obtain ⟨x, hx, -⟩ := F.existsUnique_gluing' W ⊤ (fun _ ↦ homOfLE le_top)
      (by rw [iSup_bool_eq]; exact h.ge) sf hcompat
    refine ⟨x, Subtype.ext (Prod.ext (hx true) (hx false))⟩

/-- Global sections over `U ∪ V = Y` as the two-set Čech `H⁰`. -/
def sectionsEquivCechH0 (h : U ⊔ V = ⊤) : Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] cechModH0 S M U V :=
  LinearEquiv.ofBijective _ (toCechH0_bijective M U V h)

end Glue


section ZeroScheme

variable (S : Scheme.{u}) {Y : Scheme.{u}} [Y.Over S] (L : Y.Modules) (s : Γ(L, ⊤))

/-- The restriction `s|_W`. -/
abbrev secRes (W : Y.Opens) : Γ(L, W) := L.presheaf.map (homOfLE le_top).op s

/-- Multiplication by `s|_W`: `Γ(Y, W) → Γ(L, W)`, `r ↦ r s|_W`. -/
def mulSec (W : Y.Opens) : Γ(Y, W) →ₗ[Γ(S, ⊤)] Γ(L, W) where
  toFun r := r • secRes L s W
  map_add' r r' := add_smul r r' _
  map_smul' a r := by
    rw [RingHom.id_apply, smul_sections_def, Algebra.smul_def, mul_smul]

lemma mulSec_apply (W : Y.Opens) (r : Γ(Y, W)) : mulSec S L s W r = r • secRes L s W :=
  rfl

lemma resModLin_comp_mulSec {W W' : Y.Opens} (h : W' ≤ W) :
    resModLin S L h ∘ₗ mulSec S L s W = mulSec S L s W' ∘ₗ resLin S Y h := by
  ext r
  simp only [LinearMap.comp_apply, mulSec_apply, resModLin_apply, resLin_apply]
  rw [Scheme.Modules.map_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The quotient `Q_W = Γ(L, W) / Γ(Y, W) s|_W`. -/
abbrev QSec (W : Y.Opens) : Type u := Γ(L, W) ⧸ LinearMap.range (mulSec S L s W)

/-- Restriction maps of the quotients `Q_W`. -/
def quotRes {W W' : Y.Opens} (h : W' ≤ W) : QSec S L s W →ₗ[Γ(S, ⊤)] QSec S L s W' :=
  Submodule.mapQ _ _ (resModLin S L h) (by
    rintro _ ⟨r, rfl⟩
    exact ⟨resLin S Y h r, (LinearMap.congr_fun (resModLin_comp_mulSec S L s h) r).symm⟩)

lemma quotRes_comp_mkQ {W W' : Y.Opens} (h : W' ≤ W) :
    quotRes S L s h ∘ₗ (LinearMap.range (mulSec S L s W)).mkQ =
      (LinearMap.range (mulSec S L s W')).mkQ ∘ₗ resModLin S L h :=
  rfl

variable (U V : Y.Opens)

/-- The Čech `H⁰` of the quotients `Q_W` for the covering `(U, V)`. -/
abbrev quotH0 : Submodule Γ(S, ⊤) (QSec S L s U × QSec S L s V) :=
  TwoCech.H0 (quotRes S L s (inf_le_left : U ⊓ V ≤ U)) (quotRes S L s inf_le_right)

/-- **The connecting map** `Ȟ⁰(Q) → Ȟ¹(𝒪_Y)` of `0 → 𝒪_Y → L → Q → 0` (multiplication by
`s`), for the covering `(U, V)`. -/
def quotH0ToCechH1 (hreg : Injective (mulSec S L s (U ⊓ V))) :
    quotH0 S L s U V →ₗ[Γ(S, ⊤)] Cech.cechH1 S Y U V :=
  TwoCech.δ (mulSec S L s U) (mulSec S L s V) (mulSec S L s (U ⊓ V))
    (LinearMap.range (mulSec S L s U)).mkQ (LinearMap.range (mulSec S L s V)).mkQ
    (LinearMap.range (mulSec S L s (U ⊓ V))).mkQ
    (resModLin_comp_mulSec S L s inf_le_left) (resModLin_comp_mulSec S L s inf_le_right)
    (quotRes_comp_mkQ S L s inf_le_left) (quotRes_comp_mkQ S L s inf_le_right)
    (LinearMap.exact_map_mkQ_range _) (LinearMap.exact_map_mkQ_range _)
    (LinearMap.exact_map_mkQ_range _) (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _)
    hreg

/-- **Step 1 of Stacks, Lemma 44.6.4 (Tag 0B9X)**: if `s` is regular on `U ∩ V`, the Čech `H¹`
of `L` vanishes and the Čech `H⁰` of `L` is generated by `s` over `Γ(S)`, the connecting map
`Ȟ⁰(Q) → Ȟ¹(𝒪_Y)` is bijective. -/
theorem quotH0ToCechH1_bijective (hreg : Injective (mulSec S L s (U ⊓ V)))
    (hH1 : Subsingleton (cechModH1 S L U V))
    (hH0 : ∀ x : cechModH0 S L U V, ∃ a : Γ(S, ⊤),
      (x : Γ(L, U) × Γ(L, V)) = a • (secRes L s U, secRes L s V)) :
    Bijective (quotH0ToCechH1 S L s U V hreg) := by
  refine TwoCech.δ_bijective _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x ↦ ?_) hH1
  obtain ⟨a, ha⟩ := hH0 x
  have h1 : ((1 : Γ(Y, U)), (1 : Γ(Y, V))) ∈
      TwoCech.H0 (resLin S Y (inf_le_left : U ⊓ V ≤ U)) (resLin S Y inf_le_right) := by
    rw [TwoCech.mem_H0, resLin_apply, resLin_apply, map_one, map_one]
  refine ⟨a • ⟨_, h1⟩, Subtype.ext ?_⟩
  rw [_root_.map_smul, Submodule.coe_smul, TwoCech.mapH0_apply, ha]
  simp [mulSec_apply]

end ZeroScheme

section Subscheme

variable (S : Scheme.{u}) {Y : Scheme.{u}} [Y.Over S] (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
  (I : Y.IdealSheafData)

/-- The closed subscheme `Z = V(I)` as a scheme over `S`. -/
abbrev subschemeOver : I.subscheme.Over S := ⟨I.subschemeι ≫ (Y ↘ S)⟩

attribute [local instance] subschemeOver

/-- `θ : Γ(L, W) → Γ(ι^*L, W')` (`W' = ι⁻¹W`), as a `Γ(S)`-linear map. -/
def thetaSec {W : Y.Opens} {W' : I.subscheme.Opens} (hW' : W' ≤ I.subschemeι ⁻¹ᵁ W) :
    Γ(L, W) →ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback I.subschemeι).obj L, W') where
  toFun := pullbackRes I.subschemeι L hW'
  map_add' := map_add _
  map_smul' a m := by
    rw [RingHom.id_apply, smul_sections_def, pullbackRes_smul, smul_sections_def]
    congr 1
    rw [algebraMap_sections, algebraMap_sections, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE]
    rfl

omit [L.IsInvertible] in
lemma thetaSec_apply {W : Y.Opens} {W' : I.subscheme.Opens} (hW' : W' ≤ I.subschemeι ⁻¹ᵁ W)
    (m : Γ(L, W)) : thetaSec S L I hW' m = pullbackRes I.subschemeι L hW' m := rfl

/-- On an affine `W` where the ideal of `Z` is the content ideal of `s|_W`, `θ` is surjective
with kernel `Γ(Y, W) s|_W`. -/
theorem thetaSec_surjective_ker {W : Y.Opens} (hW : IsAffineOpen W)
    (hI : I.ideal ⟨W, hW⟩ = LinearMap.range (Module.Dual.eval Γ(Y, W) Γ(L, W) (secRes L s W)))
    {W' : I.subscheme.Opens} (hW' : W' = I.subschemeι ⁻¹ᵁ W) :
    Surjective (thetaSec S L I hW'.le) ∧
      LinearMap.ker (thetaSec S L I hW'.le) = LinearMap.range (mulSec S L s W) := by
  subst hW'
  letI := (I.subschemeι.appLE W (I.subschemeι ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  letI : Module Γ(Y, W) Γ((Scheme.Modules.pullback I.subschemeι).obj L, I.subschemeι ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap Γ(Y, W) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W))
  haveI : IsScalarTower Γ(Y, W) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W)
      Γ((Scheme.Modules.pullback I.subschemeι).obj L, I.subschemeι ⁻¹ᵁ W) :=
    IsScalarTower.of_compHom _ _ _
  have hb := isBaseChange_pullbackRes I.subschemeι L le_rfl hW (hW.preimage I.subschemeι)
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
  haveI := invertible_sections L hW
  rw [hker, hI, Invertible.range_eval_smul_top] at hk
  refine ⟨hsurj, ?_⟩
  ext m
  have := SetLike.ext_iff.mp hk m
  rw [Submodule.mem_span_singleton] at this
  exact this


/-- `Q_W ≅ Γ(ι^*L, ι⁻¹W)` on an affine `W` where the ideal of `Z` is the content ideal
of `s|_W`. -/
def quotSecEquiv {W : Y.Opens} (hW : IsAffineOpen W)
    (hI : I.ideal ⟨W, hW⟩ = LinearMap.range (Module.Dual.eval Γ(Y, W) Γ(L, W) (secRes L s W)))
    (W' : I.subscheme.Opens) (hW' : W' = I.subschemeι ⁻¹ᵁ W) :
    QSec S L s W ≃ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback I.subschemeι).obj L, W') :=
  (Submodule.quotEquivOfEq _ _ (thetaSec_surjective_ker S L s I hW hI hW').2.symm).trans
    ((thetaSec S L I hW'.le).quotKerEquivOfSurjective (thetaSec_surjective_ker S L s I hW hI hW').1)

lemma quotSecEquiv_mk {W : Y.Opens} (hW : IsAffineOpen W)
    (hI : I.ideal ⟨W, hW⟩ = LinearMap.range (Module.Dual.eval Γ(Y, W) Γ(L, W) (secRes L s W)))
    (W' : I.subscheme.Opens) (hW' : W' = I.subschemeι ⁻¹ᵁ W) (m : Γ(L, W)) :
    quotSecEquiv S L s I hW hI W' hW' (Submodule.Quotient.mk m) =
      pullbackRes I.subschemeι L hW'.le m := rfl

lemma quotSecEquiv_res {W₁ W₂ : Y.Opens} (h₁ : IsAffineOpen W₁) (h₂ : IsAffineOpen W₂)
    (h : W₂ ≤ W₁)
    (hI₁ : I.ideal ⟨W₁, h₁⟩ = LinearMap.range (Module.Dual.eval _ _ (secRes L s W₁)))
    (hI₂ : I.ideal ⟨W₂, h₂⟩ = LinearMap.range (Module.Dual.eval _ _ (secRes L s W₂)))
    (W₁' W₂' : I.subscheme.Opens) (e₁ : W₁' = I.subschemeι ⁻¹ᵁ W₁)
    (e₂ : W₂' = I.subschemeι ⁻¹ᵁ W₂) (h' : W₂' ≤ W₁') :
    resModLin S ((Scheme.Modules.pullback I.subschemeι).obj L) h' ∘ₗ
        (quotSecEquiv S L s I h₁ hI₁ W₁' e₁).toLinearMap =
      (quotSecEquiv S L s I h₂ hI₂ W₂' e₂).toLinearMap ∘ₗ quotRes S L s h := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with | H m => ?_
  change _ = pullbackRes I.subschemeι L e₂.le (L.presheaf.map (homOfLE h).op m)
  rw [pullbackRes_res I.subschemeι L e₁.le h h' e₂.le]
  rfl

variable (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
  (hIU : I.ideal ⟨U, hU⟩ = LinearMap.range (Module.Dual.eval _ _ (secRes L s U)))
  (hIV : I.ideal ⟨V, hV⟩ = LinearMap.range (Module.Dual.eval _ _ (secRes L s V)))
  (hIUV : I.ideal ⟨U ⊓ V, hUV⟩ = LinearMap.range (Module.Dual.eval _ _ (secRes L s (U ⊓ V))))

/-- **Step 3 of Stacks, Lemma 44.6.4 (Tag 0B9X)**: `Ȟ⁰(Q) ≅ Γ(Z, ι^*L)`. -/
def quotH0Equiv (hcov : U ⊔ V = ⊤) :
    quotH0 S L s U V ≃ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) :=
  (TwoCech.equivH0 (quotSecEquiv S L s I hU hIU _ rfl) (quotSecEquiv S L s I hV hIV _ rfl)
    (quotSecEquiv S L s I hUV hIUV (I.subschemeι ⁻¹ᵁ U ⊓ I.subschemeι ⁻¹ᵁ V) rfl)
    (quotSecEquiv_res S L s I hU hUV inf_le_left hIU hIUV _
      (I.subschemeι ⁻¹ᵁ U ⊓ I.subschemeι ⁻¹ᵁ V) rfl rfl inf_le_left)
    (quotSecEquiv_res S L s I hV hUV inf_le_right hIV hIUV _
      (I.subschemeι ⁻¹ᵁ U ⊓ I.subschemeι ⁻¹ᵁ V) rfl rfl inf_le_right)).trans
    (sectionsEquivCechH0 _ (I.subschemeι ⁻¹ᵁ U) (I.subschemeι ⁻¹ᵁ V)
      (by rw [← Scheme.Hom.preimage_sup, hcov, Scheme.Hom.preimage_top])).symm

/-- **`Γ(Z, ι^*L) ≅ Ȟ¹(𝒪_Y)`** (Stacks, Lemma 44.6.4, Tag 0B9X, steps 1 and 3). -/
def zeroSchemeSectionsEquiv (hcov : U ⊔ V = ⊤) (hreg : Injective (mulSec S L s (U ⊓ V)))
    (hH1 : Subsingleton (cechModH1 S L U V))
    (hH0 : ∀ x : cechModH0 S L U V, ∃ a : Γ(S, ⊤),
      (x : Γ(L, U) × Γ(L, V)) = a • (secRes L s U, secRes L s V)) :
    Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤) ≃ₗ[Γ(S, ⊤)] Cech.cechH1 S Y U V :=
  (quotH0Equiv S L s I U V (hU := hU) (hV := hV) (hUV := hUV) (hIU := hIU) (hIV := hIV)
    (hIUV := hIUV) (hcov := hcov)).symm.trans
    (LinearEquiv.ofBijective _ (quotH0ToCechH1_bijective S L s U V hreg hH1 hH0))

end Subscheme


section Curve

open Belyi

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)
  [IsFinite π] {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Spec (CommRingCat.of k))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) g

attribute [local instance] subschemeOver

/-- The preimage `U_i` in `C ×_k T` of the standard chart `D₊(x_i)` of `ℙ¹_k`. -/
abbrev zsChart (i : Fin 2) : (pullback (C ↘ Spec (CommRingCat.of k)) g).Opens :=
  (pullback.fst (C ↘ Spec (CommRingCat.of k)) g ≫ π) ⁻¹ᵁ ProjectiveLine.U k i

/-- **Step 2 of Stacks, Lemma 44.6.4 (Tag 0B9X)**: the Čech `H¹(𝒪)` of `C ×_k T` for the
chart covering is free of rank `g(C)` over `Γ(T)`. -/
theorem rankAtStalk_cechH1_curve (p : PrimeSpectrum Γ(T, ⊤)) :
    haveI := IsCurveOver.isIntegral k C
    (Module.rankAtStalk (Cech.cechH1 T (XT) (zsChart π g 0) (zsChart π g 1)) p : ℤ) =
      curveGenus k C := by
  haveI := IsCurveOver.isIntegral k C
  letI : T.Over Sk := ⟨g⟩
  have hU := (ProjectiveLine.isAffineOpen_U k 0).preimage π
  have hV := (ProjectiveLine.isAffineOpen_U k 1).preimage π
  have hUV := (ProjectiveLine.isAffineOpen_U_inf k).preimage π
  have hcov : π ⁻¹ᵁ ProjectiveLine.U k 0 ⊔ π ⁻¹ᵁ ProjectiveLine.U k 1 = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ProjectiveLine.U_sup, Scheme.Hom.preimage_top]
  haveI : Module.Free Γ(Sk, ⊤)
      (Cech.cechH1 Sk C (π ⁻¹ᵁ ProjectiveLine.U k 0) (π ⁻¹ᵁ ProjectiveLine.U k 1)) := by
    letI := (isField_ΓSpec (k := k)).toField
    exact Module.Free.of_divisionRing _ _
  haveI : Nontrivial Γ(T, ⊤) := p.nontrivial
  have e := cechH1BaseChange (S := Sk) (T := T) _ _ hU hV hUV
  have h1 := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id,
    Module.finrank_baseChange] at h1
  rw [← finrank_cechH1_eq_curveGenus k C hU hV hcov, ← h1]
  rfl

/-- **The degree of the zero scheme of a section** (Stacks, Lemma 44.6.4, Tag 0B9X): let `C` be
a curve over a perfect field `k` with a finite `π : C → ℙ¹_k`, `T` an affine `k`-scheme, `L` an
invertible sheaf on `X_T = C ×_k T` and `s ∈ Γ(X_T, L)`. Let `U₀`, `U₁` be the preimages of the
standard charts of `ℙ¹`. Assume that `s` is a nonzerodivisor on `U₀ ∩ U₁`, that the Čech `H¹` of
`L` for `(U₀, U₁)` vanishes and its Čech `H⁰` is `Γ(T) · s`, and let `Z ⊂ X_T` be a relative
effective Cartier divisor whose ideal on `U₀`, `U₁`, `U₀ ∩ U₁` is the content ideal of `s`
(`{φ(s) : φ ∈ Γ(L, W)ᵛ}`). Then `Z → T` has degree `g(C)` everywhere. -/
theorem degree_zeroScheme_eq_curveGenus (L : (XT).Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (Z : RelEffCartier (pullback.snd (C ↘ Sk) g))
    (hreg : Injective fun r : Γ(XT, zsChart π g 0 ⊓ zsChart π g 1) ↦
      r • secRes L s (zsChart π g 0 ⊓ zsChart π g 1))
    (hH1 : Subsingleton (cechModH1 T L (zsChart π g 0) (zsChart π g 1)))
    (hH0 : ∀ x : cechModH0 T L (zsChart π g 0) (zsChart π g 1), ∃ a : Γ(T, ⊤),
      (x : Γ(L, zsChart π g 0) × Γ(L, zsChart π g 1)) =
        a • (secRes L s (zsChart π g 0), secRes L s (zsChart π g 1)))
    (hZ : ∀ (W : (XT).Opens) (hW : IsAffineOpen W), W = (zsChart π g 0) ∨ W = (zsChart π g 1) ∨
      W = (zsChart π g 0) ⊓ (zsChart π g 1) →
      Z.ideal.ideal ⟨W, hW⟩ = LinearMap.range (Module.Dual.eval Γ(XT, W) Γ(L, W) (secRes L s W)))
    (t : T) :
    haveI := IsCurveOver.isIntegral k C
    (Z.degree t : ℤ) = curveGenus k C := by
  haveI := IsCurveOver.isIntegral k C
  letI : T.Over Sk := ⟨g⟩
  haveI : IsFinite (Z.ideal.subschemeι ≫ ((XT) ↘ T)) := Z.isFinite C g
  haveI : Flat (Z.ideal.subschemeι ≫ ((XT) ↘ T)) := Z.flat
  have hU : IsAffineOpen (zsChart π g 0) := isAffineOpen_chart (T₀ := T) π 0
  have hV : IsAffineOpen (zsChart π g 1) := isAffineOpen_chart (T₀ := T) π 1
  have hUV : IsAffineOpen ((zsChart π g 0) ⊓ (zsChart π g 1)) :=
    isAffineOpen_chart_inf (T₀ := T) π
  have hcov : (zsChart π g 0) ⊔ (zsChart π g 1) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ProjectiveLine.U_sup, Scheme.Hom.preimage_top]
  let e := zeroSchemeSectionsEquiv T L s Z.ideal (zsChart π g 0) (zsChart π g 1) (hU := hU)
    (hV := hV) (hUV := hUV) (hIU := hZ _ hU (Or.inl rfl)) (hIV := hZ _ hV (Or.inr (Or.inl rfl)))
    (hIUV := hZ _ hUV (Or.inr (Or.inr rfl))) (hcov := hcov) (hreg := hreg) (hH1 := hH1)
    (hH0 := hH0)
  have h1 := finrank_eq_rankAtStalk_sections (S := T) Z.ideal t
  have h2 := rankAtStalk_sections_pullback (S := T) L Z.ideal
    ((isAffineOpen_top T).primeIdealOf ⟨t, trivial⟩)
  have h3 := congrFun (Module.rankAtStalk_eq_of_equiv e)
    ((isAffineOpen_top T).primeIdealOf ⟨t, trivial⟩)
  have h4 := rankAtStalk_cechH1_curve π g ((isAffineOpen_top T).primeIdealOf ⟨t, trivial⟩)
  change ((Z.ideal.subschemeι ≫ ((XT) ↘ T)).finrank t : ℤ) = _
  rw [h1, ← h2]
  exact (congrArg ((↑) : ℕ → ℤ) h3).trans h4

end Curve

end CurvesJacobian
