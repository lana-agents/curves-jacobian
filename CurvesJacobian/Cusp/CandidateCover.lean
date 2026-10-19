/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.ModelRun
import CurvesJacobian.Cusp.FieldTwistDGC
import CurvesJacobian.Cusp.CoverRangeOpen
import CurvesJacobian.Cusp.CoverCuspComap

/-!
# Belyi candidates with an infinite cusp image are geometric (MR8, round 27, step (3b))

For a Belyi-type chain `c` of `Π_X ↠ G_K` with a terminal isomorphism `t` to the trivial chain,
whose object `Π_V` has an infinite cusp image (`hV`), and `m ≤ r`, the candidate
`Π_U ↠ Π_V ↪ Π_X` (`PiChain.belyiCandidate hc t m hm`) is geometric
(**`PiChain.IsBelyiType.exists_cover_fill`**): there are a hyperbolic curve `Y = (X̄_Y, U_Y)` over a
number field `M ⊇ K` with `ι : Π_Y ≅ Π_U`, a filling `U_Y ⊆ U'` with `ε : Π_{(X̄_Y, U')} ≅ Π_V` such
that `Π_U ↠ Π_V` is `ε ∘ fillPiHom ∘ ι⁻¹`, and a **finite étale `q : Spec Γ(U') ⟶ Spec Γ(X)`**
inducing (up to a change of base point) the embedding `Π_V ↪ Π_X` composed with `ε`. This is the
converse of [AbsTopII] Cor 3.7 (a) (`Topics in Absolute Anabelian Geometry II.txt` l.4743–4753)
modulo `hV`; the only DGC input is `hDGC`.

Proof: `exists_candidate_fill_toG` gives `Y ⊆ Y'` and `ε`; the open subgroup `range(emb) ⊆ Π_X`
is the image of `π₁ᵉᵗ` of a connected finite étale cover `p : V ⟶ X`
(`exists_isFiniteEtale_range_eq_of_open`), a hyperbolic curve `V'` over its constant field `k'`
(`coverCurve`) with `Π_{V'} ≅ range(emb)` over `res : G_{k'} → G_K` up to conjugation
(`toG_coverCurvePiEquiv`); `Π_{Y'} ≅ Π_V ≅ range(emb) ≅ Π_{V'}` lies over `res` on both sides
(`PiChain.exists_pr_belyiEmb`), so the rel-isom-DGC across fields
(`exists_isConjInduced_of_relIsomDGC_field`) gives a semilinear `F : Spec Γ(U') ≅ Spec Γ(V')`
inducing it, and `q := F ≫ (Spec Γ(V') ≅ V) ≫ p`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Belyi.Anabelian
  Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {CX : HypCurve K}
  {hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty}

attribute [local instance] isAlgClosure_of_isAlgebraic


omit [NumberField K] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] in
/-- `Spec α` over `Spec K` for a `K`-isomorphism `α : M₂ ≃ₐ[K] M₁`. -/
lemma specRingEquiv₂_comp_specAlgebraMap {M₁ M₂ : Type u} [Field M₁] [Field M₂] [Algebra K M₁]
    [Algebra K M₂] (α : M₂ ≃ₐ[K] M₁) :
    specRingEquiv₂ α.toRingEquiv ≫ Spec.map (CommRingCat.ofHom (algebraMap K M₂)) =
      Spec.map (CommRingCat.ofHom (algebraMap K M₁)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact α.commutes x

/-- **A cover realising an open embedding** (the geometric step of (3b)): let `C₁` be a hyperbolic
curve over a number field `M₁ ⊇ K` and `f : Π_{C₁} → Π_X` a continuous injective homomorphism
lying over `res : G_{M₁} → G_K` up to conjugation, whose image is the image of `π₁ᵉᵗ` of a
connected finite étale `p : V ⟶ X` at a point `ζ`. Then `f` is induced, up to a change of base
point, by a finite étale `q : Spec Γ(C₁.U) ⟶ Spec Γ(X)` (DGC across fields, `hDGC`). -/
theorem exists_isConjInduced_cover_of_range {M₁ : Type u} [Field M₁] [NumberField M₁]
    [Algebra K M₁] [Algebra M₁ Ω] [IsScalarTower K M₁ Ω] [FiniteDimensional K M₁]
    [Algebra.IsAlgebraic M₁ Ω] (C₁ : HypCurve M₁) (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
    (hDGC : RelIsomDGC M₁)
    (f : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) →ₜ*
      π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))
    (hf : Function.Injective f) {Yc : Scheme.{u}} (p : Yc ⟶ Spec Γ(CX.Xbar, CX.U))
    [IsFiniteEtale p] [ConnectedSpace Yc] (ζ : Spec (.of Ω) ⟶ Yc)
    (hζ : ζ ≫ p = basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))
    (hrange : (fundamentalGroupMap p hζ).toMonoidHom.range = f.toMonoidHom.range)
    (g : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (hg : ∀ τ, projGk Ω CX hcX (f τ) = g * resGal K Ω M₁ (projGk Ω C₁ hc₁ τ) * g⁻¹) :
    ∃ (q : Spec Γ(C₁.Xbar, C₁.U) ⟶ Spec Γ(CX.Xbar, CX.U)) (_ : IsFiniteEtale q),
      IsConjInduced q f ∧
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
          Spec.map (CommRingCat.ofHom (algebraMap M₁ Γ(C₁.Xbar, C₁.U))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap K M₁)) := by
  haveI := isIntegral_specSections CX hcX
  letI := coverAlgebra Ω CX hcX p ζ
  haveI := isScalarTower_coverAlgebra Ω CX hcX p ζ hζ
  haveI := isAlgebraic_coverAlgebra Ω CX hcX p ζ hζ
  haveI : FiniteDimensional K (coverField CX hcX p) :=
    Module.Finite.of_restrictScalars_finite ℚ K (coverField CX hcX p)
  have hmem : ∀ v, f v ∈ (coverSubgroup p ζ hζ : Subgroup _) := fun v ↦ by
    rw [← range_fundamentalGroupMap_eq_coverSubgroup, hrange]
    exact ⟨v, rfl⟩
  let w₀ : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) →ₜ*
      (coverChainObj Ω CX hcX p ζ hζ).grp :=
    ⟨⟨⟨fun v ↦ ⟨f v, hmem v⟩, Subtype.ext (map_one f)⟩,
      fun a b ↦ Subtype.ext (map_mul f a b)⟩, Continuous.subtype_mk f.continuous _⟩
  have hw₀ : Function.Bijective w₀ := by
    refine ⟨fun a b hab ↦ hf (congrArg Subtype.val hab), fun z ↦ ?_⟩
    let z' : ↥(coverSubgroup p ζ hζ : Subgroup π₁ᵉᵗ(basePoint Ω CX hcX ≫
      baseChangeSpec K Ω Γ(CX.Xbar, CX.U))) := z
    have hz : z'.1 ∈ f.toMonoidHom.range := by
      rw [← hrange, range_fundamentalGroupMap_eq_coverSubgroup]
      exact z'.2
    obtain ⟨v, hv⟩ := hz
    exact ⟨v, Subtype.ext hv⟩
  have hφe : ∀ τ, coverPiIncl Ω CX hcX p ζ hζ (coverCurvePiEquiv Ω CX hcX p ζ hζ
      ((continuousMulEquivOfBijective w₀ hw₀).trans
        (coverCurvePiEquiv Ω CX hcX p ζ hζ).symm τ)) = f τ := fun τ ↦
    (congrArg (coverPiIncl Ω CX hcX p ζ hζ)
      ((coverCurvePiEquiv Ω CX hcX p ζ hζ).apply_symm_apply _)).trans rfl
  have htoG := toG_coverCurvePiEquiv Ω CX hcX p ζ hζ
  generalize coverConj Ω CX hcX p ζ hζ (coverCurve CX hcX p) (coverCurve_cusp CX hcX p)
    (coverIso CX hcX p) (coverIso_spec CX hcX p) = cc at htoG
  have hφ : ∀ τ, resGal K Ω (coverField CX hcX p)
      (projGk Ω (coverCurve CX hcX p) (coverCurve_cusp CX hcX p)
        (((continuousMulEquivOfBijective w₀ hw₀).trans
          (coverCurvePiEquiv Ω CX hcX p ζ hζ).symm) τ)) =
      (cc⁻¹ * g) * resGal K Ω M₁ (projGk Ω C₁ hc₁ τ) * (cc⁻¹ * g)⁻¹ := fun τ ↦ by
    have h1 : projGk Ω CX hcX (f τ) = cc * resGal K Ω (coverField CX hcX p)
        (projGk Ω (coverCurve CX hcX p) (coverCurve_cusp CX hcX p)
          (((continuousMulEquivOfBijective w₀ hw₀).trans
            (coverCurvePiEquiv Ω CX hcX p ζ hζ).symm) τ)) * cc⁻¹ := by
      rw [← hφe]
      exact htoG _
    have h3 := h1.symm.trans (hg τ)
    calc _ = cc⁻¹ * (cc * resGal K Ω (coverField CX hcX p)
          (projGk Ω (coverCurve CX hcX p) (coverCurve_cusp CX hcX p)
            (((continuousMulEquivOfBijective w₀ hw₀).trans
              (coverCurvePiEquiv Ω CX hcX p ζ hζ).symm) τ)) * cc⁻¹) * cc := by group
      _ = _ := by rw [h3]; group
  obtain ⟨α, F, hFα, HF⟩ := exists_isConjInduced_of_relIsomDGC_field hDGC
    ((continuousMulEquivOfBijective w₀ hw₀).trans (coverCurvePiEquiv Ω CX hcX p ζ hζ).symm)
    (cc⁻¹ * g) hφ
  haveI : IsFiniteEtale F.hom := MorphismProperty.of_isIso @IsFiniteEtale F.hom
  haveI : IsFiniteEtale (coverIso CX hcX p).hom :=
    MorphismProperty.of_isIso @IsFiniteEtale (coverIso CX hcX p).hom
  haveI : IsFiniteEtale ((coverIso CX hcX p).hom ≫ p) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  refine ⟨F.hom ≫ (coverIso CX hcX p).hom ≫ p,
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance, ?_⟩
  have Hc := isConjInduced_coverPiEquiv Ω CX hcX (coverCurve CX hcX p) (coverCurve_cusp CX hcX p)
    p ζ hζ (coverIso CX hcX p)
  refine ⟨(HF.comp Hc).congr_fun fun τ ↦ (hφe τ).symm, ?_⟩
  have e1 := coverIso_spec CX hcX p
  calc (F.hom ≫ (coverIso CX hcX p).hom ≫ p) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
      F.hom ≫ (coverIso CX hcX p).hom ≫ p ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) := by
        simp only [Category.assoc]
    _ = (F.hom ≫ sKU (coverCurve CX hcX p)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (coverField CX hcX p))) := by
        rw [e1, Category.assoc]
    _ = _ := by
        rw [hFα, Category.assoc, specRingEquiv₂_comp_specAlgebraMap]

/-- `exists_isConjInduced_cover_of_range` for a composite `emb ∘ ε` with `ε` an isomorphism. -/
theorem exists_isConjInduced_cover_of_range' {M₁ : Type u} [Field M₁] [NumberField M₁]
    [Algebra K M₁] [Algebra M₁ Ω] [IsScalarTower K M₁ Ω] [FiniteDimensional K M₁]
    [Algebra.IsAlgebraic M₁ Ω] (C₁ : HypCurve M₁) (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
    (hDGC : RelIsomDGC M₁) {P : Type*} [Group P] [TopologicalSpace P]
    (ε : π₁ᵉᵗ(basePoint Ω C₁ hc₁ ≫ baseChangeSpec M₁ Ω Γ(C₁.Xbar, C₁.U)) ≃ₜ* P)
    (emb : P →ₜ* π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))
    (hemb : Function.Injective emb) {Yc : Scheme.{u}} (p : Yc ⟶ Spec Γ(CX.Xbar, CX.U))
    [IsFiniteEtale p] [ConnectedSpace Yc] (ζ : Spec (.of Ω) ⟶ Yc)
    (hζ : ζ ≫ p = basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))
    (hrange : (fundamentalGroupMap p hζ).toMonoidHom.range = emb.toMonoidHom.range)
    (g : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (hg : ∀ τ, projGk Ω CX hcX (emb (ε τ)) = g * resGal K Ω M₁ (projGk Ω C₁ hc₁ τ) * g⁻¹) :
    ∃ (q : Spec Γ(C₁.Xbar, C₁.U) ⟶ Spec Γ(CX.Xbar, CX.U)) (_ : IsFiniteEtale q),
      IsConjInduced q (fun τ ↦ emb (ε τ)) ∧
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
          Spec.map (CommRingCat.ofHom (algebraMap M₁ Γ(C₁.Xbar, C₁.U))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap K M₁)) := by
  have hR : (fundamentalGroupMap p hζ).toMonoidHom.range =
      (emb.comp (ContinuousMonoidHom.toContinuousMonoidHom ε)).toMonoidHom.range := by
    rw [hrange]
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨ε.symm v, congrArg emb (ε.apply_symm_apply v)⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨ε τ, rfl⟩
  exact exists_isConjInduced_cover_of_range C₁ hc₁ hDGC
    (emb.comp (ContinuousMonoidHom.toContinuousMonoidHom ε)) (hemb.comp ε.injective) p ζ hζ hR g hg

variable {c : PiChain (arithmeticExt Ω CX hcX)} {l r : ℕ}

set_option maxHeartbeats 400000 in
-- the existential statement with the chain indices is slow to elaborate
/-- **[AbsTopII] Cor 3.7 (a), converse: candidates with an infinite cusp image are geometric**
(MR8 round 27, step (3b)). For a Belyi-type chain with a terminal isomorphism to the trivial
chain whose object `Π_V` has an infinite cusp image, and `m ≤ r`, the candidate
`Π_U ↠ Π_V ↪ Π_X` is `Π_Y ↠ Π_{Y'} ↪ Π_X` for a filling `Y = (X̄_Y, U_Y) ⊆ Y' = (X̄_Y, U')` of
one curve over a number field and a finite étale `q : Spec Γ(U') ⟶ Spec Γ(X)`. -/
theorem _root_.Belyi.Anabelian.PiChain.IsBelyiType.exists_cover_fill (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial _))
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC k)
    (hV : (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp) (m : ℕ) (hm : m ≤ r) :
    ∃ D : GeomModel Ω CX hcX (c.objN (l + 3 + (r - m)) (by have := hc.len_eq; omega)),
      Function.Surjective D.ι ∧
      ∃ (U' : D.Y.Xbar.Opens) (h : D.Y.U ≤ U') (hc' : (U' : Set D.Y.Xbar)ᶜ.Nonempty)
        (hyp : haveI := IsCurveOver.isIntegral D.M D.Y.Xbar
          2 < 2 * Anabelian.curveGenus D.M D.Y.Xbar + cuspDegree D.M D.Y.Xbar U')
        (ε : π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
          baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) ≃ₜ* (PiChain.belyiCandidate hc t m hm).PiV),
        (∀ σ, (PiChain.belyiCandidate hc t m hm).surj (D.ι σ) =
          ε (fillPiHom Ω D.Y D.hY h hc' hyp σ)) ∧
        ∃ (q : Spec Γ(D.Y.Xbar, U') ⟶ Spec Γ(CX.Xbar, CX.U)) (_ : IsFiniteEtale q),
          IsConjInduced q (fun τ ↦ (PiChain.belyiCandidate hc t m hm).emb (ε τ) :
            π₁ᵉᵗ(basePoint Ω (fillCurve D.Y h hyp) hc' ≫
              baseChangeSpec D.M Ω Γ(D.Y.Xbar, U')) →
              π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))) ∧
          q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
            Spec.map (CommRingCat.ofHom (algebraMap D.M Γ(D.Y.Xbar, U'))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap K D.M)) := by
  have hlen := hc.len_eq
  have h1 := hc.exists_candidate_fill_toG t hDGC hV m hm
  obtain ⟨D, hD, U', h, hc', hyp, ε, hε, g₀, hG⟩ := h1
  refine ⟨D, hD, U', h, hc', hyp, ε, hε, ?_⟩
  have hpr := PiChain.exists_pr_belyiEmb hc t
  obtain ⟨g, hg⟩ := hpr
  haveI := isIntegral_specSections CX hcX
  have hO : IsOpen ((PiChain.belyiCandidate hc t m hm).emb.toMonoidHom.range :
      Set (arithmeticExt Ω CX hcX).Pi) :=
    (PiChain.belyiCandidate hc t m hm).isOpen_range_emb
  obtain ⟨Yc, p, hp, ζ, hζ, hconn, hrange⟩ := exists_isFiniteEtale_range_eq_of_open
    (basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) ⟨_, hO⟩
  obtain ⟨g', hg'⟩ : ∃ g' : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))),
      ∀ y, (arithmeticExt Ω CX hcX).pr (PiChain.belyiEmb hc t y) =
        g' * toGk (c.objN (l + r + 3) (by omega)) y * g'⁻¹ := ⟨g, hg⟩
  have hf : ∀ τ, projGk Ω CX hcX ((PiChain.belyiCandidate hc t m hm).emb (ε τ)) = (g' * g₀) *
      resGal K Ω D.M (projGk Ω (fillCurve D.Y h hyp) hc' τ) * (g' * g₀)⁻¹ := fun τ ↦ by
    have e1 := hg' (ε τ)
    have e3 := congrArg (fun z ↦ g' * z * g'⁻¹) (hG τ)
    exact (e1.trans e3).trans (by group)
  have hrange' : (fundamentalGroupMap p hζ).toMonoidHom.range =
      (PiChain.belyiCandidate hc t m hm).emb.toMonoidHom.range := hrange
  have key := exists_isConjInduced_cover_of_range' (P := (PiChain.belyiCandidate hc t m hm).PiV)
    (fillCurve D.Y h hyp) hc' (hDGC D.M) ε
    (PiChain.belyiCandidate hc t m hm).emb (PiChain.belyiCandidate hc t m hm).emb_injective
    p ζ hζ hrange' _ hf
  exact key

end CurvesJacobian.Cusp
