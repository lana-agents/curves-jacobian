/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelEnlargeExt
import CurvesJacobian.Cusp.ConjInducedCusps
import CurvesJacobian.Cusp.ChainPush

/-!
# Enlarging a geometric model: the projection to `G_K` (MR8 option (Q), step (Q-c))

In the setting of `CurvesJacobian.Cusp.ModelEnlargeExt` (a geometric model `D` of `A`, the
punctured line `L`, the cover `V = Spec R_{h'} ⟶ Spec Γ(L)`, `E₁ = π₁ᵉᵗ(W) ≤ Π_L` and the
surjection `Φ : E₁ ↠ P'`):

* `AlgebraicGeometry.FiniteEtale.exists_conj_fundamentalGroupMap_of_conjInduced`: if
  `φ : π₁ᵉᵗ(X, x) → π₁ᵉᵗ(Y, y)` is induced by `F : X ⟶ Y` lying over `S`, then
  `π₁ᵉᵗ(Y → S) ∘ φ = conj c ∘ π₁ᵉᵗ(X → S)` for some `c` (the scheme-level form of
  `CurvesJacobian.Cusp.exists_resGal_projGk_conj_of_conjInduced`);
* `GeomModel.enlCover_comp_sKU`: `V ⟶ Spec Γ(L) ⟶ Spec K` equals `V ⟶ Spec Γ(U_Y) ⟶ Spec M ⟶
  Spec K`, and `GeomModel.exists_resGal_projGk_enlPsi₀`:
  `res ∘ pr_Y ∘ ψ₀ = conj c ∘ pr_L ∘ π₁ᵉᵗ(V ⟶ L)`;
* **`GeomModel.exists_toGk_enlPhi`**: `toG_A ∘ Φ = conj c ∘ pr_L` on `E₁` (both are homomorphisms
  `E₁ → G_K` agreeing up to conjugation on the open `ker p₁`, and `G_K` is slim);
* `GeomModel.enlPhi_mem_Delta_iff`: `Φ e ∈ Δ_A ↔ e ∈ ker pr_L`;
* `GeomModel.exists_toGk_enlPhi_enlZ0`: the model form `toG_A ∘ Φ ∘ (Π_{Z₀} ≃ E₁) =
  conj g₀' ∘ res ∘ pr_{Z₀}`, and `GeomModel.mem_ker_projGk_enlZ0_iff`:
  `γ ∈ ker pr_{Z₀} ↔ Φ γ ∈ Δ_A`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory Polynomial

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteEtale

variable {X Y S : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- **Maps induced by a morphism over `S` lie over `π₁ᵉᵗ(S)` up to conjugation**: if `φ` is
induced by `F : X ⟶ Y` and `F ≫ pY = pX`, then `π₁ᵉᵗ(pY) ∘ φ = conj c ∘ π₁ᵉᵗ(pX)`. -/
theorem exists_conj_fundamentalGroupMap_of_conjInduced {F : X ⟶ Y} {pX : X ⟶ S} {pY : Y ⟶ S}
    (hF : F ≫ pY = pX) {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y} {s : Spec (.of Ω) ⟶ S}
    (hx : x ≫ pX = s) (hy : y ≫ pY = s) {φ : π₁ᵉᵗ(x) → π₁ᵉᵗ(y)} (H : IsConjInduced F φ) :
    ∃ c : π₁ᵉᵗ(s), ∀ σ,
      fundamentalGroupMap pY hy (φ σ) = c * fundamentalGroupMap pX hx σ * c⁻¹ := by
  obtain ⟨γ, hγ⟩ := H
  have hxF' : x ≫ F ≫ pY = s := by rw [hF]; exact hx
  have hxF : (x ≫ F) ≫ pY = s := (Category.assoc _ _ _).trans hxF'
  refine ⟨fiberIsoMap pY hxF hy γ, fun σ ↦ ?_⟩
  have c3 := fundamentalGroupMap_autContinuousMulEquivOfIso pY hxF hy γ
    (fundamentalGroupMap F rfl σ)
  have c4 := DFunLike.congr_fun (fundamentalGroupMap_comp F pY rfl hxF hxF') σ
  have c5 := DFunLike.congr_fun (fundamentalGroupMap_congr hF hxF' hx) σ
  calc fundamentalGroupMap pY hy (φ σ)
      = fundamentalGroupMap pY hy (autContinuousMulEquivOfIso γ (fundamentalGroupMap F rfl σ)) :=
        congrArg _ (hγ σ)
    _ = autContinuousMulEquivOfIso (fiberIsoMap pY hxF hy γ) (fundamentalGroupMap pX hx σ) :=
        c3.trans (congrArg _ (c4.symm.trans c5))
    _ = _ := Aut_conjAut_eq _ _

end AlgebraicGeometry.FiniteEtale

namespace CurvesJacobian.Cusp.GeomModel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty} {A : ChainObj (arithmeticExt Ω CX hcX)}
  (D : GeomModel Ω CX hcX A) (hDGC : RelIsomDGC.Exists D.M) {P' : Subgroup D.Nrm}
  (hrel : D.ιNHom.range.relIndex P' ≠ 0)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- The point `Spec Ω ⟶ Spec K`. -/
local notation "sK" => Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-! ### `ψ₀` over `G_K` -/

/-- **`V ⟶ Spec Γ(L) ⟶ Spec K` equals `V ⟶ Spec Γ(U_Y) ⟶ Spec M ⟶ Spec K`** (`t` is a
`K`-linear coordinate, the `K`-structure of `Γ(U_Y)` is through `M`). -/
theorem enlCover_comp_sKU :
    D.enlCover hDGC hrel ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U))) =
      D.enlJ hDGC hrel ≫ Spec.map (CommRingCat.ofHom (algebraMap D.M Γ(D.Y.Xbar, D.Y.U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K D.M)) := by
  have key : (Localization.awayMap (lineHom K (D.enlT hDGC hrel))
      (quotLinePoly K (D.enlH hDGC hrel))).comp
        (algebraMap K (Localization.Away (quotLinePoly K (D.enlH hDGC hrel)))) =
      (algebraMap Γ(D.Y.Xbar, D.Y.U) (D.enlRing hDGC hrel)).comp
        ((algebraMap D.M Γ(D.Y.Xbar, D.Y.U)).comp (algebraMap K D.M)) := by
    ext c
    change Localization.awayMap (lineHom K (D.enlT hDGC hrel)) (quotLinePoly K (D.enlH hDGC hrel))
        (algebraMap K[X] _ (algebraMap K K[X] c)) = _
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    change algebraMap Γ(D.Y.Xbar, D.Y.U) (D.enlRing hDGC hrel)
      (aeval (D.enlT hDGC hrel) (algebraMap K K[X] c)) = _
    rw [Polynomial.algebraMap_eq, aeval_C]
    rfl
  rw [enlCover, quotLineCover_eq, Category.assoc, lineCurveIso_hom_structure, enlJ,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, key]

/-- **`ψ₀` lies over `G_K` up to conjugation**:
`res(pr_Y(ψ₀ τ)) = c · pr_L(π₁ᵉᵗ(V ⟶ L) τ) · c⁻¹`. -/
theorem exists_resGal_projGk_enlPsi₀ :
    ∃ c : π₁ᵉᵗ(sK), ∀ τ : π₁ᵉᵗ(D.enlPt hDGC hrel),
      resGal K Ω D.M (projGk Ω D.Y D.hY (D.enlPsi₀ hDGC hrel τ)) =
        c * projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)
          (fundamentalGroupMap (D.enlCover hDGC hrel) (D.enlPt_spec hDGC hrel) τ) * c⁻¹ := by
  have hy := basePoint_spec_tower₁ Ω D.hY (K := K)
  have hx : D.enlPt hDGC hrel ≫ D.enlCover hDGC hrel ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U))) = sK := by
    rw [← Category.assoc, enlPt_spec]
    exact basePoint_spec₂ Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)
  obtain ⟨c, hc⟩ := exists_conj_fundamentalGroupMap_of_conjInduced
    (D.enlCover_comp_sKU hDGC hrel).symm hx hy (D.isConjInduced_enlPsi₀ hDGC hrel)
  refine ⟨c, fun τ ↦ ?_⟩
  have c1 := DFunLike.congr_fun (fundamentalGroupMap_comp
    (Spec.map (CommRingCat.ofHom (algebraMap D.M Γ(D.Y.Xbar, D.Y.U))))
    (Spec.map (CommRingCat.ofHom (algebraMap K D.M))) (basePoint_spec₂ Ω D.Y D.hY)
    (sM_sKM (K := K) (Ω := Ω) D.M) hy) (D.enlPsi₀ hDGC hrel τ)
  have c2 := DFunLike.congr_fun (fundamentalGroupMap_comp (D.enlCover hDGC hrel)
    (Spec.map (CommRingCat.ofHom
      (algebraMap K Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U))))
    (D.enlPt_spec hDGC hrel) (basePoint_spec₂ Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)) hx) τ
  calc resGal K Ω D.M (projGk Ω D.Y D.hY (D.enlPsi₀ hDGC hrel τ))
      = _ := c1.symm
    _ = _ := hc τ
    _ = _ := congrArg (fun z ↦ c * z * c⁻¹) c2

/-! ### `Φ` over `G_K` -/

variable (hPP' : D.ιNHom.range ≤ P')

/-- **`toG_A ∘ Φ = conj c ∘ pr_L` on `E₁`**: both are homomorphisms `E₁ → G_K`; on the open
`ker p₁ = π₁ᵉᵗ(V)` they agree up to conjugation (`toG_ι`, `exists_resGal_projGk_enlPsi₀`), hence
everywhere since `G_K` is slim. -/
theorem exists_toGk_enlPhi : ∃ c : π₁ᵉᵗ(sK), ∀ e : D.enlE₁ hDGC hrel,
    toGk A ((D.enlPhi hDGC hrel hPP' e : D.Nrm) : A.grp) =
      c * projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)
        (e : π₁ᵉᵗ(D.enlEta hDGC hrel)) * c⁻¹ := by
  obtain ⟨c, hc⟩ := D.exists_resGal_projGk_enlPsi₀ hDGC hrel
  let a : D.enlE₁ hDGC hrel →* π₁ᵉᵗ(sK) := (toGk A).comp (D.Nrm.subtype.comp
    (P'.subtype.comp (D.enlPhi hDGC hrel hPP').toMonoidHom))
  let b : D.enlE₁ hDGC hrel →* π₁ᵉᵗ(sK) :=
    (projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)).toMonoidHom.comp
      (D.enlE₁ hDGC hrel).subtype
  have hker : ∀ x ∈ (D.enlP₁ hDGC hrel).ker,
      a x = (D.g₀ * c) * b x * (D.g₀ * c)⁻¹ := by
    intro x hx
    have h1 := hc (D.enlKerToV hDGC hrel ⟨x, hx⟩)
    rw [fundamentalGroupMap_enlKerToV] at h1
    change toGk A ((D.enlPhi hDGC hrel hPP' (⟨x, hx⟩ : (D.enlP₁ hDGC hrel).ker) : D.Nrm) :
      A.grp) = _
    change _ = (D.g₀ * c) * projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)
      (x : π₁ᵉᵗ(D.enlEta hDGC hrel)) * (D.g₀ * c)⁻¹
    rw [coe_enlPhi_ker, toG_ι, h1]
    group
  have hopen : IsOpen (((coverSubgroup (D.enlCover hDGC hrel) (D.enlPt hDGC hrel)
      (D.enlPt_spec hDGC hrel) : Subgroup π₁ᵉᵗ(D.enlEta hDGC hrel)).map
        (projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)).toMonoidHom :
          Subgroup π₁ᵉᵗ(sK)) : Set π₁ᵉᵗ(sK)) := by
    refine isOpen_map_of_isOpen_range (projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)) ?_
      (coverSubgroup (D.enlCover hDGC hrel) (D.enlPt hDGC hrel) (D.enlPt_spec hDGC hrel)).isOpen
    rw [(projGk_surjective Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)).range_eq]
    exact isOpen_univ
  refine ⟨D.g₀ * c, fun e ↦ ?_⟩
  change a e = (D.g₀ * c) * b e * (D.g₀ * c)⁻¹
  have hz : ((D.g₀ * c) * b e)⁻¹ * a e * (D.g₀ * c) = 1 := by
    refine isSlim_Gk (K := K) Ω ⟨_, hopen⟩ _ ?_
    rintro _ ⟨m, hm, rfl⟩
    have hmE : m ∈ D.enlE₁ hDGC hrel :=
      coverSubgroup_le_quot (ρ := D.enlCoverAut hDGC hrel) (D.enlPt_spec hDGC hrel) hm
    have hmK : (⟨m, hmE⟩ : D.enlE₁ hDGC hrel) ∈ (D.enlP₁ hDGC hrel).ker := by
      rw [ker_enlP₁]
      exact Subgroup.mem_subgroupOf.2 hm
    have h1 := hker _ ((MonoidHom.normal_ker _).conj_mem _ hmK e)
    simp only [map_mul, map_inv] at h1
    rw [hker _ hmK] at h1
    change _ * b ⟨m, hmE⟩ = b ⟨m, hmE⟩ * _
    calc ((D.g₀ * c) * b e)⁻¹ * a e * (D.g₀ * c) * b ⟨m, hmE⟩
        = ((D.g₀ * c) * b e)⁻¹ * (a e * ((D.g₀ * c) * b ⟨m, hmE⟩ * (D.g₀ * c)⁻¹) * (a e)⁻¹) *
            a e * (D.g₀ * c) := by group
      _ = ((D.g₀ * c) * b e)⁻¹ * ((D.g₀ * c) * (b e * b ⟨m, hmE⟩ * (b e)⁻¹) * (D.g₀ * c)⁻¹) *
            a e * (D.g₀ * c) := by rw [h1]
      _ = b ⟨m, hmE⟩ * (((D.g₀ * c) * b e)⁻¹ * a e * (D.g₀ * c)) := by group
  calc a e = ((D.g₀ * c) * b e) * (((D.g₀ * c) * b e)⁻¹ * a e * (D.g₀ * c)) *
        (D.g₀ * c)⁻¹ := by group
    _ = _ := by rw [hz]; group

/-- **`Φ e ∈ Δ_A ↔ pr_L e = 1`.** -/
theorem enlPhi_mem_Delta_iff (e : D.enlE₁ hDGC hrel) :
    ((D.enlPhi hDGC hrel hPP' e : D.Nrm) : A.grp) ∈ A.Delta ↔
      (e : π₁ᵉᵗ(D.enlEta hDGC hrel)) ∈
        (projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)).toMonoidHom.ker := by
  obtain ⟨c, hc⟩ := D.exists_toGk_enlPhi hDGC hrel hPP'
  rw [MonoidHom.mem_ker]
  change toGk A _ = 1 ↔ _
  rw [hc, conj_eq_one_iff]
  rfl

/-- `Spec Γ(Z₀) ≅ W ⟶ Spec Γ(L)` lies over `Spec M₀ ⟶ Spec K` (`coverIso_spec`). -/
lemma coverIso_spec_enlZ0 :
    (coverIso (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) (D.enlWHom hDGC hrel)).hom ≫
    D.enlWHom hDGC hrel ≫ Spec.map (CommRingCat.ofHom
          (algebraMap K Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap (D.enlM₀ hDGC hrel)
        Γ((D.enlZ0 hDGC hrel).Xbar, (D.enlZ0 hDGC hrel).U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (D.enlM₀ hDGC hrel))) :=
  coverIso_spec (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel) (D.enlWHom hDGC hrel)

/-- `Spec Γ(Z₀) ≅ W ⟶ Spec Γ(L)` lies over `Spec M₀ ⟶ Spec K`. -/
lemma lineQuotCurveIso_spec_enlZ0 :
    (lineQuotCurveIso K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
      (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel)
      (D.enlRho_fix hDGC hrel) (D.transcendental_enlT hDGC hrel)).hom ≫ D.enlWHom hDGC hrel ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U))) =
      Spec.map (CommRingCat.ofHom (algebraMap (D.enlM₀ hDGC hrel)
        Γ((D.enlZ0 hDGC hrel).Xbar, (D.enlZ0 hDGC hrel).U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (D.enlM₀ hDGC hrel))) :=
  D.coverIso_spec_enlZ0 hDGC hrel

omit [NumberField K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] [CharZero Ω] in
/-- `Spec K ⟶ Spec K` is the identity. -/
lemma specMap_algebraMap_self_enl : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- **`Π_{Z₀} ≃ E₁ ⊆ Π_L` lies over `res : G_{M₀} → G_K` up to conjugation** (K0). -/
theorem exists_projGk_enlZ0PiEquiv :
    letI := D.enlAlgebraM₀ hDGC hrel
    haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
    haveI := D.isScalarTower_enlAlgebraM₀ hDGC hrel
    ∃ c : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))), ∀ γ,
      projGk Ω (D.enlL hDGC hrel) (D.enlL_cusp hDGC hrel)
        ((D.enlZ0PiEquiv hDGC hrel γ : D.enlE₁ hDGC hrel) : π₁ᵉᵗ(D.enlEta hDGC hrel)) =
        c * resGal K Ω (D.enlM₀ hDGC hrel)
          (projGk Ω (D.enlZ0 hDGC hrel) (D.enlZ0_cusp hDGC hrel) γ) * c⁻¹ := by
  letI := D.enlAlgebraM₀ hDGC hrel
  haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
  haveI := D.isScalarTower_enlAlgebraM₀ hDGC hrel
  have hF : ((lineQuotCurveIso K (D.enlT hDGC hrel) (D.enlH hDGC hrel) (D.enlH_ne_zero hDGC hrel)
      (D.finite_enlT hDGC hrel) (D.enlH_etale hDGC hrel) (D.enlRho hDGC hrel)
      (D.enlRho_fix hDGC hrel) (D.transcendental_enlT hDGC hrel)).hom ≫ D.enlWHom hDGC hrel) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K Γ((D.enlL hDGC hrel).Xbar, (D.enlL hDGC hrel).U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K K)) =
      Spec.map (CommRingCat.ofHom (algebraMap (D.enlM₀ hDGC hrel)
        Γ((D.enlZ0 hDGC hrel).Xbar, (D.enlZ0 hDGC hrel).U))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (D.enlM₀ hDGC hrel))) :=
    (congrArg (fun g ↦ _ ≫ _ ≫ g) specMap_algebraMap_self_enl).trans
      ((congrArg (fun g ↦ _ ≫ g) (Category.comp_id _)).trans
        ((Category.assoc _ _ _).trans (D.lineQuotCurveIso_spec_enlZ0 hDGC hrel)))
  obtain ⟨c, hc⟩ := exists_resGal_projGk_conj_of_conjInduced Ω (K := K)
    (D.enlZ0_cusp hDGC hrel) (D.enlL_cusp hDGC hrel) _ hF
    (D.isConjInduced_enlZ0PiEquiv hDGC hrel)
  exact ⟨c, fun γ ↦ (resGal_self _).symm.trans (hc γ)⟩

/-- **The model form of `toG` for `Z₀`**: `toG_A ∘ Φ ∘ (Π_{Z₀} ≃ E₁) = conj g₀' ∘ res ∘ pr_{Z₀}`. -/
theorem exists_toGk_enlPhi_enlZ0 :
    letI := D.enlAlgebraM₀ hDGC hrel
    haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
    haveI := D.isScalarTower_enlAlgebraM₀ hDGC hrel
    ∃ g₀' : π₁ᵉᵗ(sK), ∀ γ,
      toGk A ((D.enlPhi hDGC hrel hPP' (D.enlZ0PiEquiv hDGC hrel γ) : D.Nrm) : A.grp) =
        g₀' * resGal K Ω (D.enlM₀ hDGC hrel)
          (projGk Ω (D.enlZ0 hDGC hrel) (D.enlZ0_cusp hDGC hrel) γ) * g₀'⁻¹ := by
  letI := D.enlAlgebraM₀ hDGC hrel
  haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
  haveI := D.isScalarTower_enlAlgebraM₀ hDGC hrel
  obtain ⟨c', hc'⟩ := D.exists_toGk_enlPhi hDGC hrel hPP'
  obtain ⟨c, hc⟩ := D.exists_projGk_enlZ0PiEquiv hDGC hrel
  refine ⟨c' * c, fun γ ↦ ?_⟩
  rw [hc', hc]
  group

/-- **`γ ∈ ker pr_{Z₀} ↔ Φ γ ∈ Δ_A`** (`res` is injective). -/
theorem mem_ker_projGk_enlZ0_iff :
    letI := D.enlAlgebraM₀ hDGC hrel
    haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
    ∀ γ, γ ∈ (projGk Ω (D.enlZ0 hDGC hrel) (D.enlZ0_cusp hDGC hrel)).toMonoidHom.ker ↔
      ((D.enlPhi hDGC hrel hPP' (D.enlZ0PiEquiv hDGC hrel γ) : D.Nrm) : A.grp) ∈ A.Delta := by
  letI := D.enlAlgebraM₀ hDGC hrel
  haveI := D.isAlgebraic_enlAlgebraM₀ hDGC hrel
  haveI := D.isScalarTower_enlAlgebraM₀ hDGC hrel
  haveI : FiniteDimensional K (D.enlM₀ hDGC hrel) :=
    Module.Finite.of_restrictScalars_finite ℚ K (D.enlM₀ hDGC hrel)
  intro γ
  obtain ⟨g, hg⟩ := D.exists_toGk_enlPhi_enlZ0 hDGC hrel hPP'
  rw [MonoidHom.mem_ker]
  change _ ↔ toGk A _ = 1
  rw [hg, conj_eq_one_iff]
  exact (map_eq_one_iff _ (resGal_injective (K := K) (Ω := Ω) (D.enlM₀ hDGC hrel))).symm

end CurvesJacobian.Cusp.GeomModel
