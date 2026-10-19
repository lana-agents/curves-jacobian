/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BaseChangePi
import CurvesJacobian.Cusp.Cor37b
import CurvesJacobian.Cusp.GaloisOfNormal
import CurvesJacobian.Cusp.ModelCover

/-!
# The base change of a Galois cover to a normal extension is Galois (MR8.5)

Let `CX = (X̄, X)` be an affine hyperbolic curve over a number field `K`, `C = (V̄, V)` a
hyperbolic curve over a number field `M ⊇ K` and `FV : V ⟶ X` a finite étale **Galois** cover
over `Spec M ⟶ Spec K` (`GaloisBelyiInput`). For a finite extension `M'/M` which is **normal over
`K`** (stable under `Gal(Ω/K)`) and a cartesian square `V' = V ×_M M'`
(`aV : Spec Γ(V') ⟶ Spec Γ(V)` over `Spec M' ⟶ Spec M`), the composite `V' ⟶ V ⟶ X` is again a
Galois cover (`CurvesJacobian.Cusp.isGalois_coverObj_comp_of_normal`).

Proof (at the level of images of `π₁ᵉᵗ`): with `q_V : Π_V ↠ G_M`, `q_X : Π_X ↠ G_K` and the
injection `res : G_M ↪ G_K`, the image of `Π_{V'}` in `Π_V` is `q_V⁻¹(G_{M'})`
(`range_fundamentalGroupMap_of_isPullback`), hence its image in `Π_X` is
`im(Π_V) ∩ q_X⁻¹(res(G_{M'}))` (`res` is injective and `q_X ∘ FV = res ∘ q_V`). Both are normal:
`im(Π_V)` since `FV` is Galois, `res(G_{M'}) = G_{M'} ⊆ G_K` since `M'/K` is normal
(`CurvesJacobian.Cusp.normal_range_resGal_of_stable`). A connected cover with normal image of
`π₁ᵉᵗ` is Galois (`isGalois_coverObj_of_normal_range`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

/-! ### Group theory -/

/-- In a commutative square `q_X ∘ f = r ∘ q_C` with `r` injective, if `im f` and `r(S)` are
normal, then so is `f(q_C⁻¹(S))` (it is `im f ∩ q_X⁻¹(r(S))`). -/
lemma normal_map_comap_of_comm₂ {P X GM GK : Type*} [Group P] [Group X] [Group GM] [Group GK]
    (f : P →* X) (qC : P →* GM) (qX : X →* GK) (r : GM →* GK) (hr : Function.Injective r)
    (hcomm : ∀ p, qX (f p) = r (qC p)) (hN : f.range.Normal) (S : Subgroup GM)
    (hS : (S.map r).Normal) : ((S.comap qC).map f).Normal := by
  have e : (S.comap qC).map f = f.range ⊓ (S.map r).comap qX := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, rfl⟩, ⟨qC p, hp, (hcomm p).symm⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨s, hs, hsx⟩⟩
      have hps : qC p = s := hr (by rw [hsx, hcomm])
      exact ⟨p, show qC p ∈ S from hps ▸ hs, rfl⟩
  rw [e]
  haveI := hS.comap qX
  infer_instance

/-! ### `G_{M'} ⊴ G_K` for `M'/K` normal -/

section Res

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [IsGalois K Ω] (M' : Type u) [Field M'] [Algebra K M'] [Algebra M' Ω] [IsScalarTower K M' Ω]
  [IsGalois M' Ω]

/-- **`G_{M'} ⊴ G_K` for `M'/K` normal**: if `Gal(Ω/K)` maps `M' ⊆ Ω` into itself, the image of
`res : G_{M'} → G_K` is normal. -/
theorem normal_range_resGal_of_stable
    (hM' : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x : M', ∃ y : M', σ (algebraMap M' Ω x) = algebraMap M' Ω y) :
    (resGal K Ω M').toMonoidHom.range.Normal := by
  refine ⟨fun γ hγ δ ↦ ?_⟩
  rw [mem_range_resGal_iff] at hγ ⊢
  intro x
  obtain ⟨y, hy⟩ := hM' ((mulEquivAutFiber K Ω).symm δ)⁻¹ x
  have hd : (mulEquivAutFiber K Ω).symm δ (((mulEquivAutFiber K Ω).symm δ)⁻¹
      (algebraMap M' Ω x)) = algebraMap M' Ω x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rw [map_mul, map_mul, map_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy, hγ y, ← hy, hd]

end Res

/-! ### The cover `V' ⟶ V ⟶ X` -/

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω]
  {M' : Type u} [Field M'] [NumberField M'] [Algebra M M'] [Algebra M' Ω] [IsScalarTower M M' Ω]
  [Algebra K M'] [IsScalarTower K M M'] [IsScalarTower K M' Ω] [Algebra.IsAlgebraic M' Ω]

attribute [local instance] isAlgClosure_of_isAlgebraic

omit [NumberField K] [Algebra K M'] [IsScalarTower K M M'] in
/-- A base change of `Spec M' ⟶ Spec M` is finite étale. -/
lemma isFiniteEtale_of_isPullback_sKU {C : HypCurve M} {C' : HypCurve M'}
    {aV : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U)}
    (hsq : IsPullback aV (sKU C') (sKU C) (specAlgebraMap M M')) : IsFiniteEtale aV :=
  haveI : IsFiniteEtale (specAlgebraMap M M') := isFiniteEtale_specAlgebraMap (M := M) (M' := M')
  MorphismProperty.of_isPullback (P := @IsFiniteEtale) hsq.flip inferInstance

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] [Algebra.IsAlgebraic M Ω]
  [Algebra.IsAlgebraic M' Ω] in
/-- Image of `π₁ᵉᵗ` of a composite. -/
lemma range_fundamentalGroupMap_comp₂ [IsSepClosed Ω] {Y X W : Scheme.{u}} (f : Y ⟶ X)
    (g : X ⟶ W) (x₀ : Spec (.of Ω) ⟶ Y) :
    (fundamentalGroupMap (f ≫ g) (Category.assoc x₀ f g).symm).toMonoidHom.range =
      (fundamentalGroupMap f (rfl : x₀ ≫ f = x₀ ≫ f)).toMonoidHom.range.map
        (fundamentalGroupMap g (rfl : (x₀ ≫ f) ≫ g = (x₀ ≫ f) ≫ g)).toMonoidHom := by
  rw [fundamentalGroupMap_comp f g rfl rfl]
  exact MonoidHom.range_comp _ _

omit [CharZero Ω] [Algebra.IsAlgebraic M Ω] in
/-- **The image of `π₁ᵉᵗ(V') → π₁ᵉᵗ(X)` is normal** (at any geometric point of `V'` over
`Spec Ω ⟶ Spec M'`), for `V' = V ×_M M'`, `V → X` Galois and `M'/K` normal. -/
theorem normal_range_fundamentalGroupMap_comp_of_normal (CX : HypCurve K)
    (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (FV : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(CX.Xbar, CX.U)) [IsFiniteEtale FV]
    (hFV : FV ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M)))
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj FV))
    (hM' : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x : M', ∃ y : M', σ (algebraMap M' Ω x) = algebraMap M' Ω y)
    (C' : HypCurve M')
    (aV : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U))
    (hsq : IsPullback aV (sKU C') (sKU C) (specAlgebraMap M M'))
    (η : Spec (.of Ω) ⟶ Spec Γ(C'.Xbar, C'.U))
    (hη : η ≫ sKU C' = Spec.map (CommRingCat.ofHom (algebraMap M' Ω))) :
    (fundamentalGroupMap (aV ≫ FV) (Category.assoc η aV FV).symm).toMonoidHom.range.Normal := by
  haveI := isIntegral_specSections CX hcX
  haveI := isIntegral_specSections C hc
  haveI : IsFiniteEtale (specAlgebraMap M M') := isFiniteEtale_specAlgebraMap (M := M) (M' := M')
  haveI : IsFiniteEtale aV := isFiniteEtale_of_isPullback_sKU hsq
  haveI := hgal
  -- the geometric points
  have hv : (η ≫ aV) ≫ sKU C = Spec.map (CommRingCat.ofHom (algebraMap M Ω)) := by
    rw [Category.assoc, hsq.w, ← Category.assoc, hη]
    exact specMap_algebraMap_tower M M' Ω
  have hv' : (η ≫ sKU C') ≫ specAlgebraMap M M' =
      Spec.map (CommRingCat.ofHom (algebraMap M Ω)) := by
    rw [hη]
    exact specMap_algebraMap_tower M M' Ω
  have hw : ((η ≫ aV) ≫ FV) ≫ sKU CX = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [Category.assoc, hFV, ← Category.assoc, hv]
    exact specMap_algebraMap_tower K M Ω
  -- `im π₁ᵉᵗ(V') = q_V⁻¹(G_{M'})` in `π₁ᵉᵗ(V)`
  have key := range_fundamentalGroupMap_of_isPullback hsq.flip hv
    (fundamentalGroupMap_structure_surjective Ω C hc hv) (rfl : η ≫ aV = _) hv'
  -- `im π₁ᵉᵗ(V' → X) = FV(im π₁ᵉᵗ(V'))`
  have hcomp := range_fundamentalGroupMap_comp₂ Ω aV FV η
  -- `q_X ∘ FV = res ∘ q_V`
  have hcomm : ∀ p, fundamentalGroupMap (sKU CX) hw (fundamentalGroupMap FV rfl p) =
      resGal K Ω M (fundamentalGroupMap (sKU C) hv p) := fun p ↦ by
    have h1 : (η ≫ aV) ≫ FV ≫ sKU CX = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [← Category.assoc]; exact hw
    have h2 : (η ≫ aV) ≫ sKU C ≫ sKM K M = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [← Category.assoc, hv]; exact sM_sKM M
    have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp FV (sKU CX) rfl hw h1) p
    have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp (sKU C) (sKM K M) hv (sM_sKM M) h2) p
    rw [fundamentalGroupMap_congr hFV h1 h2] at c1
    exact c1.symm.trans c2
  -- `res(G_{M'}) = G_{M'} ⊴ G_K`
  have hS : ((fundamentalGroupMap (specAlgebraMap M M') hv').toMonoidHom.range.map
      (resGal K Ω M).toMonoidHom).Normal := by
    have e1 : (fundamentalGroupMap (specAlgebraMap M M') hv').toMonoidHom.range =
        (galoisMap M M' Ω).toMonoidHom.range :=
      range_fundamentalGroupMap_congr_pt Ω (specAlgebraMap M M') hη hv'
        (specMap_algebraMap_tower M M' Ω)
    have e : (fundamentalGroupMap (specAlgebraMap M M') hv').toMonoidHom.range.map
        (resGal K Ω M).toMonoidHom = (resGal K Ω M').toMonoidHom.range := by
      rw [e1]
      ext γ
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨s, (resGal_galoisMap M M' s).symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨_, ⟨s, rfl⟩, resGal_galoisMap M M' s⟩
    rw [e]
    exact normal_range_resGal_of_stable M' hM'
  rw [hcomp, key]
  exact normal_map_comap_of_comm₂ _ _ _ _ (resGal_injective M) hcomm
    (normal_range_fundamentalGroupMap FV rfl) _ hS

omit [CharZero Ω] [Algebra.IsAlgebraic M Ω] in
/-- **The base change `V' = V ×_M M' ⟶ V ⟶ X` of a Galois cover to a finite extension `M'/M`
normal over `K` is Galois.** -/
theorem isGalois_coverObj_comp_of_normal (CX : HypCurve K)
    (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (FV : Spec Γ(C.Xbar, C.U) ⟶ Spec Γ(CX.Xbar, CX.U)) [IsFiniteEtale FV]
    (hFV : FV ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, C.U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M)))
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj FV))
    (hM' : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x : M', ∃ y : M', σ (algebraMap M' Ω x) = algebraMap M' Ω y)
    (C' : HypCurve M') (hc' : (C'.U : Set C'.Xbar)ᶜ.Nonempty)
    (aV : Spec Γ(C'.Xbar, C'.U) ⟶ Spec Γ(C.Xbar, C.U))
    (hsq : IsPullback aV (sKU C') (sKU C) (specAlgebraMap M M')) :
    haveI := isIntegral_specSections CX hcX
    haveI := isFiniteEtale_of_isPullback_sKU hsq
    IsGalois (coverObj (aV ≫ FV)) := by
  haveI := isIntegral_specSections CX hcX
  haveI := isIntegral_specSections C' hc'
  haveI := isFiniteEtale_of_isPullback_sKU hsq
  exact isGalois_coverObj_of_normal_range
    (basePoint Ω C' hc' ≫ baseChangeSpec M' Ω Γ(C'.Xbar, C'.U)) (Category.assoc _ aV FV).symm
    (normal_range_fundamentalGroupMap_comp_of_normal Ω CX hcX C hc FV hFV hgal hM' C' aV hsq
      _ (basePoint_spec₂ Ω C' hc'))

end CurvesJacobian.Cusp
