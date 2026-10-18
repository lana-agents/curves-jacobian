/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.CurvePerfect
import CurvesJacobian.Picard.PerfectOpen
import CurvesJacobian.Picard.QcohBaseChange
import CurvesJacobian.Picard.PicSigma

/-!
# Openness of the `F`-condition for line bundles on curves (Stacks, Lemma 44.6.2, Tag 0B9V)

* `Cech.isFPoint_congr`: the `F`-condition (`Cech.IsFPoint`: Čech `H¹ = 0`, Čech `H⁰` invertible)
  only depends on the isomorphism class of the module;
* `Cech.isFPoint_pullback_iso`: it is invariant under isomorphisms of schemes;
* `CurvesJacobian.exists_goodLocus`: for `L` invertible on `X_T = C ×_k T`, `T` affine (no
  Noetherian hypothesis), there is an open `U ⊆ Spec Γ(T)` such that for every affine
  `T`-scheme `T'` the `F`-condition holds for `L_{T'}` iff `Spec Γ(T') → Spec Γ(T)` lands in `U`
  (Stacks, Lemma 44.6.2, Tag 0B9V, via Lemmas 36.32.3 = Tag 0B9S and 36.31.3 = Tag 0BDK, on
  affine test schemes).
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

/-- A base change along a bijective ring map is bijective. -/
lemma IsBaseChange.bijective_of_bijective {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f)
    (hRS : Function.Bijective (algebraMap R S)) : Function.Bijective f := by
  let e : S ≃ₐ[R] R := (AlgEquiv.ofBijective (Algebra.ofId R S) hRS).symm
  let E : S ⊗[R] M ≃ₗ[R] M :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ TensorProduct.lid R M
  have hmk : ∀ m, E (1 ⊗ₜ m) = m := fun m ↦ by
    simp [E, map_one]
  have hf : ∀ m, f m = h.equiv (1 ⊗ₜ m) := fun m ↦ by rw [h.equiv_tmul, one_smul]
  have hb : Function.Bijective (fun m : M ↦ (1 : S) ⊗ₜ[R] m) := by
    have : (fun m : M ↦ (1 : S) ⊗ₜ[R] m) = E.symm := funext fun m ↦ by
      rw [LinearEquiv.eq_symm_apply, hmk]
    rw [this]
    exact E.symm.bijective
  rw [show ⇑f = h.equiv ∘ (fun m : M ↦ (1 : S) ⊗ₜ[R] m) from funext hf]
  exact h.equiv.bijective.comp hb

namespace Cech

variable {S Y : Scheme.{u}} [Y.Over S]

/-- Sections of isomorphic modules, as `Γ(S)`-linear isomorphisms. -/
def sectionsIso {L M : Y.Modules} (e : L ≅ M) (W : Y.Opens) : Γ(L, W) ≃ₗ[Γ(S, ⊤)] Γ(M, W) where
  toFun := e.hom.app W
  invFun := e.inv.app W
  left_inv x := by
    change (e.hom.app W ≫ e.inv.app W) x = x
    rw [← Hom.comp_app, e.hom_inv_id]
    rfl
  right_inv x := by
    change (e.inv.app W ≫ e.hom.app W) x = x
    rw [← Hom.comp_app, e.inv_hom_id]
    rfl
  map_add' := map_add _
  map_smul' r x := by
    rw [smul_sections_def, smul_sections_def, RingHom.id_apply, Hom.app_smul]

lemma sectionsIso_res {L M : Y.Modules} (e : L ≅ M) {W W' : Y.Opens} (h : W' ≤ W) :
    resModLin S M h ∘ₗ (sectionsIso e W).toLinearMap =
      (sectionsIso e W').toLinearMap ∘ₗ resModLin S L h := by
  refine LinearMap.ext fun x ↦ ?_
  change M.presheaf.map (homOfLE h).op (e.hom.app W x) = e.hom.app W' (L.presheaf.map _ x)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← mapPresheaf_app,
    ← mapPresheaf_app, ← NatTrans.naturality]

variable (S) in
/-- **The `F`-condition only depends on the isomorphism class.** -/
lemma isFPoint_congr {L M : Y.Modules} (e : L ≅ M) (U V : Y.Opens) :
    IsFPoint S L U V ↔ IsFPoint S M U V := by
  have hf := sectionsIso_res (S := S) e (inf_le_left : U ⊓ V ≤ U)
  have hg := sectionsIso_res (S := S) e (inf_le_right : U ⊓ V ≤ V)
  rw [isFPoint_iff, isFPoint_iff]
  exact and_congr (TwoCech.equivH1 _ _ _ hf hg).toEquiv.subsingleton_congr
    ⟨fun h ↦ .congr (TwoCech.equivH0 _ _ _ hf hg),
      fun h ↦ .congr (TwoCech.equivH0 _ _ _ hf hg).symm⟩

section Iso

variable {S Y Y' : Scheme.{u}} [Y.Over S] [Y'.Over S] (e : Y' ⟶ Y) [IsIso e]
  (he : e ≫ (Y ↘ S) = Y' ↘ S) (L : Y.Modules) [L.IsInvertible]

omit [IsIso e] in
include he in
lemma appLE_structure_iso (W : Y.Opens) (W' : Y'.Opens) (hW : W' ≤ e ⁻¹ᵁ W) (r : Γ(S, ⊤)) :
    e.appLE W W' hW ((Y ↘ S).appLE ⊤ W (by simp) r) = (Y' ↘ S).appLE ⊤ W' (by simp) r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ : Y' ⟶ S ↦ φ.appLE ⊤ W' (by simp) r) he

omit [Y.Over S] [Y'.Over S] in
lemma bijective_pullbackRes_iso (W : Y.Opens) (hW : IsAffineOpen W) (W' : Y'.Opens)
    (hW' : W' = e ⁻¹ᵁ W) : Function.Bijective (pullbackRes e L hW'.le) := by
  subst hW'
  have hW'a : IsAffineOpen (e ⁻¹ᵁ W) := hW.preimage e
  letI := (e.appLE W (e ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  letI : Module Γ(Y, W) Γ((Scheme.Modules.pullback e).obj L, e ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap Γ(Y, W) Γ(Y', e ⁻¹ᵁ W))
  haveI : IsScalarTower Γ(Y, W) Γ(Y', e ⁻¹ᵁ W) Γ((Scheme.Modules.pullback e).obj L, e ⁻¹ᵁ W) :=
    IsScalarTower.of_compHom _ _ _
  have hb := isBaseChange_pullbackRes e L le_rfl hW hW'a
  have hbij : Function.Bijective (algebraMap Γ(Y, W) Γ(Y', e ⁻¹ᵁ W)) := by
    change Function.Bijective (e.appLE W (e ⁻¹ᵁ W) le_rfl).hom
    rw [← Scheme.Hom.app_eq_appLE]
    exact ConcreteCategory.bijective_of_isIso (e.app W)
  exact IsBaseChange.bijective_of_bijective hb hbij

include he in
/-- **Sections of the pullback along an isomorphism**: `Γ(e^*L, e⁻¹W) ≃ Γ(L, W)` (`W` affine),
`Γ(S)`-linearly, via `θ = pullbackRes`. -/
def pullbackIsoSections (W : Y.Opens) (hW : IsAffineOpen W) (W' : Y'.Opens)
    (hW' : W' = e ⁻¹ᵁ W) : Γ(L, W) ≃ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback e).obj L, W') :=
  LinearEquiv.ofBijective
    { toFun := pullbackRes e L hW'.le
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change pullbackRes e L hW'.le ((Y ↘ S).appLE ⊤ W (by simp) r • m) =
          (Y' ↘ S).appLE ⊤ W' (by simp) r • pullbackRes e L hW'.le m
        rw [pullbackRes_smul, appLE_structure_iso e he W W' hW'.le r] }
    (bijective_pullbackRes_iso e L W hW W' hW')

include he in
lemma pullbackIsoSections_apply (W : Y.Opens) (hW : IsAffineOpen W) (W' : Y'.Opens)
    (hW' : W' = e ⁻¹ᵁ W) (m : Γ(L, W)) :
    pullbackIsoSections e he L W hW W' hW' m = pullbackRes e L hW'.le m := rfl

include he in
lemma pullbackIsoSections_res {W₁ W₂ : Y.Opens} (h₁ : IsAffineOpen W₁) (h₂ : IsAffineOpen W₂)
    (h : W₂ ≤ W₁) {W₁' W₂' : Y'.Opens} (e₁ : W₁' = e ⁻¹ᵁ W₁) (e₂ : W₂' = e ⁻¹ᵁ W₂)
    (h' : W₂' ≤ W₁') :
    resModLin S ((Scheme.Modules.pullback e).obj L) h' ∘ₗ
        (pullbackIsoSections e he L W₁ h₁ W₁' e₁).toLinearMap =
      (pullbackIsoSections e he L W₂ h₂ W₂' e₂).toLinearMap ∘ₗ resModLin S L h := by
  refine LinearMap.ext fun m ↦ ?_
  change _ = pullbackRes e L e₂.le (L.presheaf.map (homOfLE h).op m)
  rw [pullbackRes_res e L e₁.le h h' e₂.le]
  rfl

include he in
/-- **The `F`-condition is invariant under isomorphisms of schemes.** -/
lemma isFPoint_pullback_iso {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) {U' V' : Y'.Opens} (eU : U' = e ⁻¹ᵁ U) (eV : V' = e ⁻¹ᵁ V) :
    IsFPoint S ((Scheme.Modules.pullback e).obj L) U' V' ↔ IsFPoint S L U V := by
  have eUV : U' ⊓ V' = e ⁻¹ᵁ (U ⊓ V) := by subst eU eV; rfl
  have hf := pullbackIsoSections_res e he L hU hUV inf_le_left eU eUV inf_le_left
  have hg := pullbackIsoSections_res e he L hV hUV inf_le_right eV eUV inf_le_right
  rw [isFPoint_iff, isFPoint_iff]
  symm
  exact and_congr (TwoCech.equivH1 _ _ _ hf hg).toEquiv.subsingleton_congr
    ⟨fun h ↦ .congr (TwoCech.equivH0 _ _ _ hf hg), fun h ↦
      .congr (TwoCech.equivH0 _ _ _ hf hg).symm⟩

end Iso

end Cech

section Curve

open Cech Belyi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]
  (π : C ⟶ ProjectiveLine.scheme k) [PerfectField k] [IsCurveOver k C] [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T ↘ Sk)

/-- **Openness of the `F`-condition on affine test schemes** (Stacks, Lemma 44.6.2, Tag 0B9V,
via Lemmas 36.32.3 = Tag 0B9S and 36.31.3 = Tag 0BDK): for `L` invertible on `X_T`, `T` affine
over `k` (no Noetherian hypothesis), there is an open `U ⊆ Spec Γ(T)` such that for every affine
`T`-scheme `T'`, `L_{T'}` satisfies the `F`-condition (Čech `H¹ = 0`, Čech `H⁰` invertible, for
the chart covering) iff all points of `Spec Γ(T')` map into `U`. -/
theorem exists_goodLocus (L : (XT).Modules) [L.IsInvertible] :
    ∃ U : Set (PrimeSpectrum Γ(T, ⊤)), IsOpen U ∧
      ∀ (T' : Scheme.{u}) [T'.Over T] [IsAffine T'],
        IsFPoint T' (lineBundleBaseChange (S := T) (T := T') L)
          (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
            (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0))
          (pullback.fst ((XT) ↘ T) (T' ↘ T) ⁻¹ᵁ
            (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1)) ↔
        ∀ q : PrimeSpectrum Γ(T', ⊤),
          PrimeSpectrum.comap (algebraMap Γ(T, ⊤) Γ(T', ⊤)) q ∈ U := by
  obtain ⟨K₀, K₁, δ, h₁, h₂, h₃, h₄, H⟩ := exists_finite_projective_cech' (T := T) π L
  refine ⟨PerfectOpen.goodLocus δ, PerfectOpen.isOpen_goodLocus δ, fun T' _ _ ↦ ?_⟩
  obtain ⟨⟨e₀⟩, ⟨e₁⟩⟩ := H T'
  rw [← PerfectOpen.good_iff, isFPoint_iff]
  refine and_congr ?_ ⟨fun h ↦ .congr e₀.symm, fun h ↦ .congr e₀⟩
  rw [← e₁.toEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff,
    LinearMap.range_eq_top]

/-- The `F`-condition for an invertible sheaf on `C ×_k T'` (`g' : T' ⟶ Spec k`, `T'` affine),
for the covering by the preimages of the two charts of `ℙ¹` under `π`. -/
def FCond {T' : Scheme.{u}} (g' : T' ⟶ Sk) (M : (pullback (C ↘ Sk) g').Modules) : Prop :=
  IsFPoint T' M ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
    ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)

omit [IsAffine T] [PerfectField k] [IsCurveOver k C] [IsFinite π] in
lemma fCond_congr {T' : Scheme.{u}} (g' : T' ⟶ Sk) {M M' : (pullback (C ↘ Sk) g').Modules}
    (e : M ≅ M') : FCond π g' M ↔ FCond π g' M' :=
  isFPoint_congr T' e _ _

/-- **Openness of the `F`-condition** (Stacks, Lemma 44.6.2, Tag 0B9V, on affine test schemes):
for `L` invertible on `C ×_k T` (`T` affine, `g : T ⟶ Spec k`) there is an open `U ⊆ T` such that
for every affine `T''` and `h : T'' ⟶ T` the pullback of `L` to `C ×_k T''` satisfies the
`F`-condition iff `h` factors through `U`. -/
theorem exists_opens_fCond {T : Scheme.{u}} [T.Over Sk] [IsAffine T]
    (L : (pullback (C ↘ Sk) (T ↘ Sk)).Modules) [L.IsInvertible] :
    ∃ U : T.Opens, ∀ (T'' : Scheme.{u}) [IsAffine T''] (h : T'' ⟶ T),
      FCond π (h ≫ (T ↘ Sk))
        ((Scheme.Modules.pullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)).obj L) ↔
        Set.range h ⊆ U := by
  obtain ⟨Ua, hUa, hU⟩ := exists_goodLocus (T := T) π L
  refine ⟨T.isoSpec.hom ⁻¹ᵁ ⟨Ua, hUa⟩, fun T'' _ h ↦ ?_⟩
  letI : T''.Over T := ⟨h⟩
  have key := hU T''
  -- the comparison isomorphism `C ×_k T'' ≅ (C ×_k T) ×_T T''`
  have H : IsPullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)
      (pullback.snd (C ↘ Sk) (h ≫ (T ↘ Sk)))
      (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) :=
    HilbPoint.isPullback_baseChangeMap (C ↘ Sk)
      (Over.homMk h rfl : Over.mk (h ≫ (T ↘ Sk)) ⟶ Over.mk (T ↘ Sk))
  let e := H.isoPullback.hom
  have he₁ : e ≫ pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) =
      bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl :=
    H.isoPullback_hom_fst
  have he₂ : e ≫ pullback.snd (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) =
      pullback.snd (C ↘ Sk) (h ≫ (T ↘ Sk)) :=
    H.isoPullback_hom_snd
  have hpX : bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl ≫ pullback.fst (C ↘ Sk) (T ↘ Sk) =
      pullback.fst (C ↘ Sk) (h ≫ (T ↘ Sk)) := bcMap_fst _ _ _ _ _
  -- the module isomorphism `e^* (p^* L) ≅ bcMap^* L`
  let iso : (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback
      (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T))).obj L) ≅
      (Scheme.Modules.pullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)).obj L :=
    (Scheme.Modules.pullbackComp e _).app L ≪≫ eqToIso (by rw [he₁])
  have hcharts : ∀ i : Fin 2, (pullback.fst (C ↘ Sk) (h ≫ (T ↘ Sk)) ≫ π) ⁻¹ᵁ ProjectiveLine.U k i =
      e ⁻¹ᵁ (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) ⁻¹ᵁ
        (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k i)) := fun i ↦ by
    rw [← hpX, ← he₁]
    rfl
  have hZU := fun i : Fin 2 ↦ isAffineOpen_preimage_fst (S := T) (T := T'')
    (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k i) (isAffineOpen_chart π i) _ rfl
  have hZUV := isAffineOpen_preimage_fst (S := T) (T := T'')
    (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1) (isAffineOpen_chart_inf π) _ rfl
  rw [← fCond_congr π (h ≫ (T ↘ Sk)) iso, FCond,
    isFPoint_pullback_iso (S := T'') e he₂ _ (hZU 0) (hZU 1) hZUV (hcharts 0) (hcharts 1), key]
  -- points
  have hnat := Scheme.isoSpec_hom_naturality h
  have halg : ∀ x, (Spec.map h.appTop) x =
      PrimeSpectrum.comap (algebraMap Γ(T, ⊤) Γ(T'', ⊤)) x := fun x ↦ by
    change PrimeSpectrum.comap h.appTop.hom x = _
    congr 2
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  constructor
  · rintro hq _ ⟨t, rfl⟩
    have := hq (T''.isoSpec.hom t)
    change T.isoSpec.hom (h t) ∈ Ua
    rw [← Scheme.Hom.comp_apply, ← hnat, Scheme.Hom.comp_apply, halg]
    exact this
  · intro hr q
    obtain ⟨t, rfl⟩ : ∃ t, T''.isoSpec.hom t = q :=
      ⟨T''.isoSpec.inv q, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
    have := hr ⟨t, rfl⟩
    change T.isoSpec.hom (h t) ∈ Ua at this
    rw [← Scheme.Hom.comp_apply, ← hnat, Scheme.Hom.comp_apply, halg] at this
    exact this

end Curve

end CurvesJacobian
