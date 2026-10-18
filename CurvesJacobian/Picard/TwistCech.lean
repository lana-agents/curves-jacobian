/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TensorSections
import CurvesJacobian.Picard.TwistCechAlgebra
import CurvesJacobian.Picard.PicFOpen
import CurvesJacobian.Picard.ZeroScheme

/-!
# Twisting the Čech complex of a line bundle by a section

Let `Y` be a scheme over `S`, `M`, `N` invertible sheaves on `Y` and `s ∈ Γ(N, Y)`. The maps
`Γ(M, W) → Γ(M ⊗ N, W)`, `m ↦ m ⊗ s|_W` (`CurvesJacobian.Cech.twistLin`) commute with the
restrictions, so they give a map of two-set Čech complexes. Over an affine `W`, by
`Scheme.Modules.bijective_tensorSections`, it is injective if `s|_W` is a nonzerodivisor and
its image is `c(s|_W) · Γ(M ⊗ N, W)` (`c` = content ideal).

* `RelEffCartier.injective_smul_canonicalSection`: the canonical section of `𝒪(D)` of a
  relative effective Cartier divisor is a nonzerodivisor on every open.
* `CurvesJacobian.Cech.removePoint`: **removing a rational point** (proof of Stacks,
  Lemma 44.6.5, Tag 0B9Y). Let `S` be the spectrum of a field, `σ : S → Y` a section landing in
  the affine opens `U`, `V`, `U ∩ V`, and `D` the divisor of `σ` (ideal `ker σ`). If
  `P ≅ M ⊗ 𝒪(D)` has Čech `H¹ = 0` and some `h ∈ H⁰(P)` does not vanish at `σ`, then `M` has
  Čech `H¹ = 0` and `h⁰(M) = h⁰(P) - 1` (from `0 → M → M(D) → M(D)|_σ → 0`).
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry Function
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.RelEffCartier

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : RelEffCartier f)

/-- The content ideal of the canonical section of `𝒪(D)` on an affine open is the ideal of
`D`. -/
lemma contentIdeal_canonicalSection (W : X.affineOpens) :
    CurvesJacobian.contentIdeal (R := Γ(X, W.1))
      (D.lineBundle.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op D.canonicalSection) =
        D.ideal.ideal W := by
  rw [← Scheme.Modules.zeroIdeal_ideal, D.zeroIdeal_canonicalSection]

/-- **The canonical section of `𝒪(D)` is a nonzerodivisor on every open.** -/
theorem injective_smul_canonicalSection (W : X.Opens) :
    Injective fun r : Γ(X, W) ↦
      r • D.lineBundle.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op D.canonicalSection := by
  suffices key : ∀ r : Γ(X, W),
      r • D.lineBundle.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op D.canonicalSection = 0 →
        r = 0 by
    intro r r' hrr
    rw [← sub_eq_zero]
    exact key _ (by rw [sub_smul]; exact sub_eq_zero.mpr hrr)
  intro r hr
  refine CurvesJacobian.sheaf_eq_of_locally_eq X.sheaf r 0 fun x hxW ↦ ?_
  obtain ⟨V, g, -, hxV, hVW, hgI, hg, -, -⟩ := exists_affine_principal_principal
    D.locally_principal D.locally_principal x W hxW
  refine ⟨V.1, hVW, hxV, ?_⟩
  have hc := D.contentIdeal_canonicalSection V
  rw [hgI] at hc
  obtain ⟨μ, hμ⟩ : g ∈ CurvesJacobian.contentIdeal (R := Γ(X, V.1))
      (D.lineBundle.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op D.canonicalSection) := by
    rw [hc]; exact Ideal.mem_span_singleton_self g
  have h0 : X.presheaf.map (homOfLE hVW).op r •
      D.lineBundle.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op D.canonicalSection = 0 := by
    have := congrArg (D.lineBundle.presheaf.map (homOfLE hVW).op) hr
    rw [Scheme.Modules.map_smul, map_zero] at this
    rw [← this]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have h1 : X.presheaf.map (homOfLE hVW).op r * g = 0 := by
    rw [← hμ]
    change _ * μ _ = 0
    rw [← smul_eq_mul, ← LinearMap.map_smul, h0, map_zero]
  change X.presheaf.map (homOfLE hVW).op r = X.presheaf.map (homOfLE hVW).op 0
  rw [map_zero]
  refine hg ?_
  change g * _ = g * 0
  rw [mul_comm, h1, mul_zero]

end AlgebraicGeometry.RelEffCartier

namespace CurvesJacobian

section EvalPoint

variable {S Y : Scheme.{u}} (σ : S ⟶ Y)

/-- The kernel of evaluation at a point `σ` landing in the affine open `Z`:
`ker(Γ(P, Z) → Γ(σ^*P, S)) = ker(σ^♯) · Γ(P, Z)` (base change of sections of invertible sheaves,
`isBaseChange_pullbackRes`). -/
lemma pullbackRes_eq_zero_iff [IsAffine S] (P : Y.Modules) [P.IsInvertible] {Z : Y.Opens}
    (hZa : IsAffineOpen Z) (hZ : ⊤ ≤ σ ⁻¹ᵁ Z) (hsurj : Surjective (σ.appLE Z ⊤ hZ))
    (m : Γ(P, Z)) :
    pullbackRes σ P hZ m = 0 ↔
      m ∈ RingHom.ker (σ.appLE Z ⊤ hZ).hom • (⊤ : Submodule Γ(Y, Z) Γ(P, Z)) := by
  letI := (σ.appLE Z ⊤ hZ).hom.toAlgebra
  letI : Module Γ(Y, Z) Γ((Scheme.Modules.pullback σ).obj P, ⊤) :=
    Module.compHom _ (algebraMap Γ(Y, Z) Γ(S, ⊤))
  haveI : IsScalarTower Γ(Y, Z) Γ(S, ⊤) Γ((Scheme.Modules.pullback σ).obj P, ⊤) :=
    IsScalarTower.of_compHom _ _ _
  have hbc := isBaseChange_pullbackRes σ P hZ hZa (isAffineOpen_top S)
  have := (IsBaseChange.surjective_and_ker_eq hbc hsurj).2
  rw [show RingHom.ker (σ.appLE Z ⊤ hZ).hom = RingHom.ker (algebraMap Γ(Y, Z) Γ(S, ⊤)) from rfl,
    ← this]
  exact Iff.rfl

/-- An invertible module over a field has dimension `1`. -/
lemma finrank_eq_one_of_invertible {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
    [Module.Invertible F E] : Module.finrank F E = 1 := by
  have h := (Module.Invertible.linearEquiv F E).finrank_eq
  rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq, Module.finrank_self] at h
  exact Nat.eq_one_of_mul_eq_one_right h

/-- Sections over `S` of an invertible sheaf on the spectrum `S` of a field form a vector space
of dimension one. -/
lemma exists_eq_smul_of_ne_zero [IsAffine S] (hF : IsField Γ(S, ⊤)) (L : S.Modules)
    [L.IsInvertible] {e₁ : Γ(L, ⊤)} (h : e₁ ≠ 0) (e₂ : Γ(L, ⊤)) :
    ∃ μ : Γ(S, ⊤), e₂ = μ • e₁ := by
  letI := hF.toField
  haveI := invertible_sections L (isAffineOpen_top S)
  have h1 : Module.finrank Γ(S, ⊤) Γ(L, ⊤) = 1 := finrank_eq_one_of_invertible
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' e₁ h).mp h1 e₂
  exact ⟨c, hc.symm⟩

end EvalPoint

end CurvesJacobian

namespace CurvesJacobian.Cech

variable {S Y : Scheme.{u}} [Y.Over S] (M N : Y.Modules) (s : Γ(N, ⊤))

/-- `Γ(M, W) → Γ(M ⊗ N, W)`, `m ↦ m ⊗ s|_W`, as a `Γ(S, ⊤)`-linear map. -/
def twistLin (W : Y.Opens) : Γ(M, W) →ₗ[Γ(S, ⊤)] Γ(M ⊗ N, W) where
  toFun m := tmulSection m (N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s)
  map_add' a b := tmulSection_add_left a b _
  map_smul' r m := by
    rw [smul_sections_def, smul_sections_def, RingHom.id_apply]
    exact tmulSection_smul_left _ m _

lemma twistLin_apply (W : Y.Opens) (m : Γ(M, W)) :
    twistLin (S := S) M N s W m =
      tmulSection m (N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) := rfl

lemma twistLin_comp_res {W W' : Y.Opens} (h : W' ≤ W) :
    resModLin S (M ⊗ N) h ∘ₗ twistLin M N s W = twistLin M N s W' ∘ₗ resModLin S M h := by
  refine LinearMap.ext fun m ↦ ?_
  change (M ⊗ N).presheaf.map (homOfLE h).op (tmulSection m _) = tmulSection _ _
  rw [tmulSection_res]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

variable [M.IsInvertible] [N.IsInvertible] {W : Y.Opens}

omit [M.IsInvertible] [N.IsInvertible] in
lemma twistLin_eq (m : Γ(M, W)) :
    twistLin (S := S) M N s W m = tensorSections M N W
      (tmulRight (R := Γ(Y, W)) (N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) m) := rfl

/-- The twisting map is injective if `s|_W` is a nonzerodivisor. -/
theorem injective_twistLin (hW : IsAffineOpen W)
    (hs : Injective fun r : Γ(Y, W) ↦ r • N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) :
    Injective (twistLin (S := S) M N s W) := by
  haveI := projective_sections M hW
  have h1 := injective_tmulRight (R := Γ(Y, W)) (M := Γ(M, W)) hs
  exact (bijective_tensorSections hW).1.comp h1

/-- The image of the twisting map is `c(s|_W) · Γ(M ⊗ N, W)`. -/
theorem mem_range_twistLin_iff (hW : IsAffineOpen W) (y : Γ(M ⊗ N, W)) :
    y ∈ LinearMap.range (twistLin (S := S) M N s W) ↔
      y ∈ contentIdeal (R := Γ(Y, W)) (N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) •
        (⊤ : Submodule Γ(Y, W) Γ(M ⊗ N, W)) := by
  haveI := invertible_sections N hW
  set t := N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s
  set e := tensorSectionsEquiv (A := M) (B := N) hW
  have hr := range_tmulRight (R := Γ(Y, W)) (M := Γ(M, W)) t
  constructor
  · rintro ⟨m, rfl⟩
    rw [twistLin_eq M N s]
    have hm : tmulRight (R := Γ(Y, W)) t m ∈ LinearMap.range (tmulRight (R := Γ(Y, W)) t) :=
      ⟨m, rfl⟩
    rw [hr] at hm
    have := Submodule.mem_map_of_mem (f := e.toLinearMap) hm
    rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
  · intro hy
    have hy' : e.symm y ∈ contentIdeal (R := Γ(Y, W)) t • (⊤ : Submodule Γ(Y, W) _) := by
      have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hy
      rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
    rw [← hr] at hy'
    obtain ⟨m, hm⟩ := hy'
    refine ⟨m, ?_⟩
    rw [twistLin_eq M N s]
    change e _ = y
    rw [hm, LinearEquiv.apply_symm_apply]

section Eval

variable {S Y : Scheme.{u}} [Y.Over S] (σ : S ⟶ Y) (hσ : σ ≫ (Y ↘ S) = 𝟙 S)

include hσ in
lemma appLE_algebraMap {Z : Y.Opens} (hZ : ⊤ ≤ σ ⁻¹ᵁ Z) (a : Γ(S, ⊤)) :
    σ.appLE Z ⊤ hZ (algebraMap Γ(S, ⊤) Γ(Y, Z) a) = a := by
  rw [algebraMap_sections, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq hσ]
  simp [Scheme.Hom.appLE]

include hσ in
lemma surjective_appLE {Z : Y.Opens} (hZ : ⊤ ≤ σ ⁻¹ᵁ Z) : Surjective (σ.appLE Z ⊤ hZ) :=
  fun a ↦ ⟨_, appLE_algebraMap σ hσ hZ a⟩

omit [Y.Over S] in
lemma ker_app_eq_ker_appLE {Z : Y.Opens} (hZ : ⊤ ≤ σ ⁻¹ᵁ Z) :
    RingHom.ker (σ.app Z).hom = RingHom.ker (σ.appLE Z ⊤ hZ).hom := by
  have hiso : IsIso (S.presheaf.map (homOfLE hZ).op) := by
    have : IsIso (homOfLE hZ).op :=
      ⟨⟨(homOfLE (le_top : σ ⁻¹ᵁ Z ≤ ⊤)).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    infer_instance
  ext r
  rw [RingHom.mem_ker, RingHom.mem_ker, Scheme.Hom.appLE, CommRingCat.hom_comp,
    RingHom.comp_apply]
  exact ⟨fun h ↦ by rw [h, map_zero], fun h ↦
    (ConcreteCategory.bijective_of_isIso (S.presheaf.map (homOfLE hZ).op)).1
      (h.trans (map_zero _).symm)⟩

end Eval

section RemovePoint

variable {S Y : Scheme.{u}} [Y.Over S] [IsAffine S] (σ : S ⟶ Y) (hσ : σ ≫ (Y ↘ S) = 𝟙 S)

include hσ in
/-- **Removing a rational point** (proof of Stacks, Lemma 44.6.5, Tag 0B9Y). Let `Γ(S)` be a
field, `σ : S → Y` a section landing in `U ∩ V`, and `D` the divisor of `σ`. If
`P ≅ M ⊗ 𝒪(D)` has Čech `H¹ = 0` for `(U, V)` and some `h ∈ H⁰(P)` does not vanish at `σ`,
then `H¹(M) = 0` and `h⁰(M) + 1 = h⁰(P)`. -/
theorem removePoint (hF : IsField Γ(S, ⊤)) {U V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V)) (hσW : ⊤ ≤ σ ⁻¹ᵁ (U ⊓ V))
    {T : Scheme.{u}} {fD : Y ⟶ T} (D : RelEffCartier fD) [QuasiCompact σ] (hD : D.ideal = σ.ker)
    (M P : Y.Modules) [M.IsInvertible] [P.IsInvertible] (e : P ≅ M ⊗ D.lineBundle)
    (h1 : Subsingleton (cechModH1 S P U V)) [Module.Finite Γ(S, ⊤) (cechModH0 S P U V)]
    {h : Γ(P, U) × Γ(P, V)} (hh : h ∈ cechModH0 S P U V)
    (hh0 : P.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op h.1 ∉
      RingHom.ker (σ.appLE (U ⊓ V) ⊤ hσW).hom • (⊤ : Submodule Γ(Y, U ⊓ V) Γ(P, U ⊓ V))) :
    Subsingleton (cechModH1 S M U V) ∧
      Module.finrank Γ(S, ⊤) (cechModH0 S M U V) + 1 =
        Module.finrank Γ(S, ⊤) (cechModH0 S P U V) := by
  letI := hF.toField
  have hσU : ⊤ ≤ σ ⁻¹ᵁ U := hσW.trans (σ.preimage_mono inf_le_left)
  have hσV : ⊤ ≤ σ ⁻¹ᵁ V := hσW.trans (σ.preimage_mono inf_le_right)
  -- transport from `P` to `M ⊗ 𝒪(D)`
  have hf := sectionsIso_res (S := S) e (inf_le_left : U ⊓ V ≤ U)
  have hg := sectionsIso_res (S := S) e (inf_le_right : U ⊓ V ≤ V)
  let e0 := TwoCech.equivH0 _ _ _ hf hg
  let e1 := TwoCech.equivH1 _ _ _ hf hg
  haveI : Module.Finite Γ(S, ⊤) (cechModH0 S (M ⊗ D.lineBundle) U V) := Module.Finite.equiv e0
  have h1Q : Subsingleton (cechModH1 S (M ⊗ D.lineBundle) U V) :=
    e1.toEquiv.subsingleton_congr.mp h1
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
  have hγ : ∀ c, ε (twistLin (S := S) M D.lineBundle D.canonicalSection (U ⊓ V) c) = 0 :=
    fun c ↦ (hε _).mpr ((hrange hUV hσW _).mp ⟨c, rfl⟩)
  have hE : ∀ e₁ e₂ : (Γ(M ⊗ D.lineBundle, U ⊓ V) ⧸ NW.restrictScalars Γ(S, ⊤)), e₁ ≠ 0 →
      ∃ μ : Γ(S, ⊤), e₂ = μ • e₁ := by
    intro e₁ e₂ he₁
    obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective _ e₁
    obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective _ e₂
    have hx₁ : pullbackRes σ (M ⊗ D.lineBundle) hσW x₁ ≠ 0 := fun h0 ↦ he₁ ((hε x₁).mpr h0)
    obtain ⟨μ, hμ⟩ := exists_eq_smul_of_ne_zero hF _ hx₁ (pullbackRes σ _ hσW x₂)
    refine ⟨μ, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
    refine (hε _).mpr ?_
    rw [map_sub, smul_sections_def, pullbackRes_smul, appLE_algebraMap σ hσ hσW, hμ, sub_self]
  -- the element `h`, transported to `M ⊗ 𝒪(D)`
  let h' : Γ(M ⊗ D.lineBundle, U) × Γ(M ⊗ D.lineBundle, V) :=
    (sectionsIso (S := S) e U h.1, sectionsIso (S := S) e V h.2)
  have hh' : h' ∈ cechModH0 S (M ⊗ D.lineBundle) U V := (e0 ⟨h, hh⟩).2
  have hh0' : ε (resModLin S (M ⊗ D.lineBundle) (inf_le_left : U ⊓ V ≤ U) h'.1) ≠ 0 := by
    intro h0
    have h0' := (pullbackRes_eq_zero_iff σ _ hUV hσW (surjective_appLE σ hσ hσW) _).mp
      ((hε _).mp h0)
    apply hh0
    have hres' : resModLin S (M ⊗ D.lineBundle) (inf_le_left : U ⊓ V ≤ U) h'.1 =
        appLinearEquiv e (U ⊓ V) (P.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op h.1) :=
      LinearMap.congr_fun hf h.1
    rw [hres'] at h0'
    have := Submodule.mem_map_of_mem (f := (appLinearEquiv e (U ⊓ V)).symm.toLinearMap) h0'
    rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
  have hfU := twistLin_comp_res (S := S) M D.lineBundle D.canonicalSection
    (inf_le_left : U ⊓ V ≤ U)
  have hgV := twistLin_comp_res (S := S) M D.lineBundle D.canonicalSection
    (inf_le_right : U ⊓ V ≤ V)
  refine ⟨TwoCech.subsingleton_H1_of_removePoint hfU hgV hα hβ hγ (hinj hUV)
    (fun e₁ e₂ he₁ ↦ hE e₁ e₂ he₁) hh' hh0' h1Q, ?_⟩
  rw [e0.finrank_eq]
  exact TwoCech.finrank_H0_of_removePoint hfU hgV (hinj hU) (hinj hV) hα hβ (hinj hUV)
    hE hh' hh0'

end RemovePoint

end CurvesJacobian.Cech
