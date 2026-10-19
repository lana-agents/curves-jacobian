/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BelyiArithSpec
import CurvesJacobian.Cusp.FillSeq
import CurvesJacobian.Cusp.HypBaseChange
import CurvesJacobian.Cusp.P1Curve
import CurvesJacobian.Cusp.RationalBaseChange
import Belyi.Anabelian.BelyiInputNumberField

/-!
# Existence of Belyi data for curves of strictly Belyi type (MR8.5)

[AbsTopII] Definition 3.5 (`Topics in Absolute Anabelian Geometry II.txt` l.4615–4617): "We shall
say that `X` is of *strictly Belyi type* if it is defined over a number field and isogenous [cf.
§0] to a hyperbolic curve of genus zero." Example 3.6 (ii) (l.4655–4680) then uses finite étale
coverings `V → X`, `V → Q` with an open immersion `Q → P` into a copy `P` of the projective line
minus three points, a nonempty open `U ⊆ V` descending to the given `U_X ⊆ X`, and a Belyi map
`β : W → P` with `W ⊆ U` (Example 3.6 (i), l.4628–4636).

`StrictlyBelyiInput CX M` is the input of Example 3.6 (ii) for an affine hyperbolic curve
`CX = (X̄, X)` over a number field `K`: over a number field `M ⊇ K`, a hyperbolic curve `V` with a
cusp, finite étale `V ⟶ X` (over `Spec M ⟶ Spec K`) and finite étale `V ⟶ Q` onto an open
`Q ⊆ ℙ¹_M ∖ {0, 1, ∞}`. (This is Definition 3.5 after replacing the number field by a finite
extension over which the genus-zero curve becomes an open of `ℙ¹` and three of its cusps become
`0, 1, ∞`.)

**Main theorem** (`CurvesJacobian.Cusp.exists_belyiData`): for every nonempty open `U_X ⊆ X`
there are a finite extension `M'` of `M` inside `Ω`, Belyi data `D : BelyiData CX` over `M'`
and an index `j ≤ D.r` such that the `j`-th open of the run of fillings `W ⊆ … ⊆ V_{M'}` is
`U = V_{M'} ×_X U_X` (`D.UW j = V_{M'} ∩ FV⁻¹(U_X)`). With `belyiCandidate_spec` (`m = r - j`)
the corresponding candidate of the Belyi chain is `Π_U ↠ Π_V ↪ Π_X` ([AbsTopII] Cor 3.7 (a);
`CurvesJacobian.Cusp.exists_belyiCandidate`).

**Normal field** (`CurvesJacobian.Cusp.exists_belyiData_normal`,
`CurvesJacobian.Cusp.exists_belyiCandidate_normal`): `M'` can be taken stable under `Gal(Ω/K)` (the
normal closure over `K` of the Belyi field, `CurvesJacobian.Cusp.normalFinSub`, via
`CurvesJacobian.Cusp.exists_belyi_open_le_finSub_ge_up`), with `D.FV = (V_{M'} ⟶ V) ≫ FV` for a
cartesian square `V_{M'} = V ×_M M'`; then `V_{M'} ⟶ X` is Galois when `V ⟶ X` is
(`CurvesJacobian.Cusp.isGalois_coverObj_comp_of_normal`).

Construction: `U₀ = V ×_X U_X ⊆ V`; belyi's `exists_belyi_open_le_finSub` gives a finite extension
`M'` and a finite `f : V̄_{M'} ⟶ ℙ¹_{M'}` with `W = f⁻¹(ℙ¹ ∖ {0, 1, ∞}) ⊆ (U₀)_{M'}` and
`f|_W` finite étale; `CW = (V̄_{M'}, W)`, `CQ = (ℙ¹_{M'}, Q_{M'})`, runs of fillings
`W ⊆ … ⊆ (U₀)_{M'} ⊆ … ⊆ V_{M'}` and `Q_{M'} ⊆ … ⊆ ℙ¹ ∖ {0, 1, ∞}` (`exists_fillSeq`), the maps
`V_{M'} ⟶ V ⟶ X`, `V_{M'} ⟶ Q_{M'}` (base change of `V ⟶ Q`) and `β = f|_W`.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian IntermediateField

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CurvesJacobian.Cusp

/-! ### The normal closure of a finite subextension -/

section NormalClosure

variable (K : Type u) [Field K] {M : Type u} [Field M] [Algebra K M] {Ω : Type u} [Field Ω]
  [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω]

/-- The normal closure over `K` of a finite subextension `L` of `Ω / M`, as an intermediate field
of `Ω / K`. -/
def normalClosureField (L : FinSub M Ω) : IntermediateField K Ω :=
  normalClosure K (L.1.restrictScalars K) Ω

lemma restrictScalars_le_normalClosureField (L : FinSub M Ω) :
    L.1.restrictScalars K ≤ normalClosureField K L :=
  IntermediateField.le_normalClosure _

lemma algebraMap_mem_normalClosureField (L : FinSub M Ω) (m : M) :
    algebraMap M Ω m ∈ normalClosureField K L :=
  restrictScalars_le_normalClosureField K L (L.1.algebraMap_mem m)

lemma finiteDimensional_normalClosureField [FiniteDimensional K M] (L : FinSub M Ω) :
    FiniteDimensional K (normalClosureField K L) := by
  haveI := L.2
  haveI : FiniteDimensional K L.1 := Module.Finite.trans M L.1
  haveI : FiniteDimensional K (L.1.restrictScalars K) := this
  exact normalClosure.is_finiteDimensional K _ Ω

/-- **The normal closure** over `K` of a finite subextension `L` of `Ω / M` (with `M / K`
finite), as a finite subextension of `Ω / M`. -/
def normalFinSub [FiniteDimensional K M] (L : FinSub M Ω) : FinSub M Ω :=
  ⟨(normalClosureField K L).toSubfield.toIntermediateField
      (algebraMap_mem_normalClosureField K L), by
    haveI := finiteDimensional_normalClosureField K L
    haveI : FiniteDimensional K ((normalClosureField K L).toSubfield.toIntermediateField
      (K := M) (algebraMap_mem_normalClosureField K L)) := this
    exact Module.Finite.of_restrictScalars_finite K M _⟩

lemma mem_normalFinSub [FiniteDimensional K M] (L : FinSub M Ω) (x : Ω) :
    x ∈ (normalFinSub K L).1 ↔ x ∈ normalClosureField K L := Iff.rfl

lemma le_normalFinSub [FiniteDimensional K M] (L : FinSub M Ω) : L ≤ normalFinSub K L :=
  fun _ hx ↦ restrictScalars_le_normalClosureField K L hx

lemma normalClosureField_stable (L : FinSub M Ω) (σ : Ω ≃ₐ[K] Ω) {x : Ω}
    (hx : x ∈ normalClosureField K L) : σ x ∈ normalClosureField K L := by
  have hle : normalClosureField K L ≤ (normalClosureField K L).map σ.symm.toAlgHom := by
    refine (normalClosure_le_iff).2 fun f y hy ↦ ?_
    obtain ⟨a, rfl⟩ := hy
    refine ⟨σ (f a), ?_, by simp⟩
    exact AlgHom.fieldRange_le_normalClosure (σ.toAlgHom.comp f) ⟨a, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hle hx
  have : σ x = y := by rw [← hxy]; simp
  rw [this]; exact hy

/-- **The normal closure is `Gal(Ω/K)`-stable.** -/
lemma normalFinSub_stable [FiniteDimensional K M] (L : FinSub M Ω) :
    ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ (normalFinSub K L).1, σ x ∈ (normalFinSub K L).1 :=
  fun σ _ hx ↦ normalClosureField_stable K L σ hx

end NormalClosure

/-! ### The Belyi input over a finite extension of prescribed shape -/

section BelyiUp

/-- `Belyi.Anabelian.exists_baseChange_model_ge` with the subextension of the shape `R L₀`, for
an inflationary `R` (move the model along the transition morphism `X_{R K} ⟶ X_K`). -/
theorem exists_baseChange_model_up {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X]
    [QuasiSeparatedSpace X] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [LocallyOfFinitePresentation g]
    (φ : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f ⟶ Z)
    (hφ : φ ≫ g = pullback.snd _ f ≫ f) (K₀ : FinSub k Ω) (R : FinSub k Ω → FinSub k Ω)
    (hR : ∀ L, L ≤ R L) :
    ∃ (K : (FinSub k Ω)ᵒᵖ) (ψ : (baseChangeDiagram (Ω := Ω) f).obj K ⟶ Z), K₀ ≤ K.unop ∧
      (∃ L₀, K.unop = R L₀) ∧ (baseChangeCone (Ω := Ω) f).π.app K ≫ ψ = φ ∧
      ψ ≫ g = (baseChangeDiagramπ (Ω := Ω) f).app K ≫ f := by
  obtain ⟨K, ψ, hK₀, h1, h2⟩ := exists_baseChange_model_ge f g φ hφ K₀
  let h : Opposite.op (R K.unop) ⟶ K := (homOfLE (hR K.unop)).op
  refine ⟨Opposite.op (R K.unop), (baseChangeDiagram (Ω := Ω) f).map h ≫ ψ, hK₀.trans (hR _),
    ⟨K.unop, rfl⟩, ?_, ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ψ) ((baseChangeCone (Ω := Ω) f).w h))).trans h1
  · rw [Category.assoc, h2, ← Category.assoc, (baseChangeDiagramπ (Ω := Ω) f).naturality h]
    simp only [Functor.const_obj_map]
    exact congrArg (· ≫ f) (Category.comp_id _)

variable (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
  [IsAlgClosed Ω] [CharZero F] [Algebra.IsAlgebraic ℚ F]

/-- **`Belyi.Anabelian.exists_belyi_open_le_finSub_ge` with the finite subextension of the shape
`R L₀`** for an inflationary `R : FinSub F Ω → FinSub F Ω` (e.g. the normal closure over a
subfield, `normalFinSub`). [AbsTopII] Example 3.6 (i), with the field as large as the cusps
require. Let `X₀` be a curve over a field `F` algebraic over `ℚ`,
`U₀ ⊆ X₀` a nonempty open subscheme, `Ω` an algebraic closure of `F` and `P` any rule assigning
a finite subextension of `Ω / F` to a subset of `X₀`. Then there are a finite set `S₀ ⊆ X₀`, a
finite subextension `K ⊇ P S₀` and a finite morphism `f : X_K ⟶ ℙ¹_K` over `K` such that
`W = f⁻¹(ℙ¹_K ∖ {0, 1, ∞})` is a nonempty open subscheme of `U_K`, `f|_W` is finite étale, and
every point of `X_K` outside `W` lies over `S₀`. (With `P S₀` a field over which the points over
`S₀` become rational this is [AbsTopII] Example 3.6 (i), l.4634–4635: "by replacing `k′` by some
finite extension of `k′`, … the cusps of `W` are all defined over `k′`".) -/
theorem exists_belyi_open_le_finSub_ge_up (X₀ : Scheme.{u}) [X₀.Over (Spec (.of F))]
    [IsCurveOver F X₀] (U₀ : X₀.Opens) (hU₀ : (U₀ : Set X₀).Nonempty)
    (P : Set X₀ → FinSub F Ω) (R : FinSub F Ω → FinSub F Ω) (hR : ∀ L, L ≤ R L) :
    ∃ (S₀ : Set X₀) (K : FinSub F Ω)
      (f : pullback (specAlgebraMap F K.1) (X₀ ↘ Spec (.of F)) ⟶ P1 K.1),
      S₀.Finite ∧ P S₀ ≤ K ∧
      f ≫ (P1 K.1 ↘ Spec (.of K.1)) = pullback.fst _ _ ∧ IsFinite f ∧
      f ⁻¹ᵁ puncturedLine K.1 ≤ pullback.snd (specAlgebraMap F K.1) (X₀ ↘ Spec (.of F)) ⁻¹ᵁ U₀ ∧
      (SetLike.coe (f ⁻¹ᵁ puncturedLine K.1)).Nonempty ∧
      IsFinite (f ∣_ puncturedLine K.1) ∧ Etale (f ∣_ puncturedLine K.1) ∧
      (∀ x, x ∉ f ⁻¹ᵁ puncturedLine K.1 →
        pullback.snd (specAlgebraMap F K.1) (X₀ ↘ Spec (.of F)) x ∈ S₀) ∧ ∃ L₀, K = R L₀ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  set p₀ := X₀ ↘ Spec (.of F) with hp₀
  haveI : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  haveI : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated p₀
  -- The curve `X_Ω = Spec Ω ×_F X₀` over `Spec Ω`.
  letI : (pullback (specAlgebraMap F Ω) p₀).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
  haveI : IsCurveOver Ω (pullback (specAlgebraMap F Ω) p₀) :=
    IsCurveOver.of_iso (pullbackSymmetry p₀ (specAlgebraMap F Ω))
      (pullbackSymmetry_hom_comp_fst _ _)
  have hUΩ : (SetLike.coe (pullback.snd (specAlgebraMap F Ω) p₀ ⁻¹ᵁ U₀)).Nonempty := by
    obtain ⟨x, hx⟩ := hU₀
    obtain ⟨y, rfl⟩ := (pullback.snd (specAlgebraMap F Ω) p₀).surjective x
    exact ⟨y, hx⟩
  -- The Belyi map over `Ω`.
  obtain ⟨fΩ, hBel, hover, hWU, hWne, -, hWet⟩ :=
    exists_belyi_open_le Ω (pullback (specAlgebraMap F Ω) p₀) _ hUΩ
  haveI := hBel.isFinite
  -- The image `S₀ ⊆ X₀` of the complement of `W_Ω`.
  set S₀ : Set X₀ := ⇑(pullback.snd (specAlgebraMap F Ω) p₀) ''
    (SetLike.coe (fΩ ⁻¹ᵁ puncturedLine Ω))ᶜ with hS₀
  have hS₀fin : S₀.Finite :=
    (finite_compl_of_isCurveOver (k := Ω) _ (fΩ ⁻¹ᵁ puncturedLine Ω) hWne).image _
  -- Spread out `X_Ω ⟶ ℙ¹_Ω ⟶ ℙ¹_F` to a finite subextension `K`.
  have hφ : (fΩ ≫ P1.mapOfAlgebra F Ω) ≫ (P1 F ↘ Spec (.of F)) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) p₀ ≫ p₀ := by
    rw [Category.assoc, P1.mapOfAlgebra_comp_structMap, ← Category.assoc, hover]
    exact pullback.condition
  obtain ⟨K', ψ, hK₀, hKR, hψ, hψover⟩ := exists_baseChange_model_up (Ω := Ω) p₀
    (P1 F ↘ Spec (.of F)) (fΩ ≫ P1.mapOfAlgebra F Ω) hφ (P S₀) R hR
  set K := K'.unop with hK
  let πX : pullback (specAlgebraMap F Ω) p₀ ⟶ pullback (specAlgebraMap F K.1) p₀ :=
    (baseChangeCone (Ω := Ω) p₀).π.app K'
  have hπfst : πX ≫ pullback.fst _ _ = pullback.fst _ _ ≫ specAlgebraMap K.1 Ω :=
    pullback.lift_fst _ _ _
  have hπsnd : πX ≫ pullback.snd _ _ = pullback.snd _ _ := baseChangeCone_π_app_snd p₀ K'
  let ψ' : pullback (specAlgebraMap F K.1) p₀ ⟶ P1 F := ψ
  have hψ' : πX ≫ ψ' = fΩ ≫ P1.mapOfAlgebra F Ω := hψ
  have hcomm : ψ' ≫ (P1 F ↘ Spec (.of F)) = pullback.fst _ _ ≫ specAlgebraMap F K.1 :=
    hψover.trans pullback.condition.symm
  -- The descended map `f_K : X_K ⟶ ℙ¹_K`.
  let fK : pullback (specAlgebraMap F K.1) p₀ ⟶ P1 K.1 :=
    pullback.lift ψ' (pullback.fst _ _) hcomm ≫ inv (P1.toPullback F K.1)
  have hfKmap : fK ≫ P1.mapOfAlgebra F K.1 = ψ' := by
    rw [← P1.toPullback_fst, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hfKstr : fK ≫ (P1 K.1 ↘ Spec (.of K.1)) = pullback.fst _ _ := by
    rw [← P1.toPullback_snd F K.1, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  -- The cartesian square `X_Ω = X_K ×_{ℙ¹_K} ℙ¹_Ω`.
  have hP1 := P1.isPullback_mapOfAlgebra K.1 Ω
  have houter : IsPullback (pullback.fst (specAlgebraMap F Ω) p₀) πX (specAlgebraMap K.1 Ω)
      (pullback.fst (specAlgebraMap F K.1) p₀) := by
    refine IsPullback.of_bot ?_ hπfst.symm (IsPullback.of_hasPullback (specAlgebraMap F K.1) p₀)
    rw [hπsnd, specAlgebraMap_comp_specAlgebraMap]
    exact IsPullback.of_hasPullback _ _
  have hw : fΩ ≫ P1.mapOfAlgebra K.1 Ω = πX ≫ fK := by
    rw [← cancel_mono (P1.toPullback F K.1)]
    apply pullback.hom_ext
    · simp only [Category.assoc, P1.toPullback_fst]
      rw [P1.mapOfAlgebra_comp_mapOfAlgebra, hfKmap, hψ']
    · simp only [Category.assoc, P1.toPullback_snd]
      rw [hfKstr, hπfst, hP1.w, ← Category.assoc, hover]
      rfl
  have hS0 : IsPullback fΩ πX (P1.mapOfAlgebra K.1 Ω) fK := by
    refine IsPullback.of_right ?_ hw hP1.flip
    rw [hover, hfKstr]
    exact houter
  haveI : Surjective (P1.mapOfAlgebra K.1 Ω) :=
    MorphismProperty.of_isPullback (P := @Surjective) hP1.flip inferInstance
  haveI : Flat (P1.mapOfAlgebra K.1 Ω) :=
    MorphismProperty.of_isPullback (P := @Flat) hP1.flip inferInstance
  haveI : QuasiCompact (P1.mapOfAlgebra K.1 Ω) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hP1.flip inferInstance
  haveI : Surjective πX := MorphismProperty.of_isPullback (P := @Surjective) houter
    inferInstance
  -- Finiteness descends.
  letI : (pullback (specAlgebraMap F K.1) p₀).Over (Spec (.of K.1)) := ⟨pullback.fst _ _⟩
  haveI : fK.IsOver (Spec (.of K.1)) := ⟨hfKstr⟩
  haveI : IsProper (pullback (specAlgebraMap F K.1) p₀ ↘ Spec (.of K.1)) :=
    MorphismProperty.pullback_fst (P := @IsProper) _ _ inferInstance
  haveI : IsProper fK := isProper_of_isOver fK (S := Spec (.of K.1))
  haveI : IsFinite fK := isFinite_of_isPullback_of_faithfullyFlat hS0
  -- The punctured lines correspond.
  have hpre : P1.mapOfAlgebra K.1 Ω ⁻¹ᵁ puncturedLine K.1 = puncturedLine Ω := by
    rw [← opensRange_puncturedι, ← opensRange_puncturedι]
    exact mapOfAlgebra_preimage_opensRange_puncturedι K.1 Ω
  have hpt : ∀ y, P1.mapOfAlgebra K.1 Ω (fΩ y) = fK (πX y) := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
  refine ⟨S₀, K, fK, hS₀fin, hK₀, hfKstr, inferInstance, fun x hx ↦ ?_, ?_, inferInstance, ?_,
    fun x hx ↦ ?_, hKR⟩
  · obtain ⟨y, rfl⟩ := πX.surjective x
    have hy : y ∈ fΩ ⁻¹ᵁ puncturedLine Ω := by
      rw [← hpre]
      simpa [Scheme.Hom.mem_preimage, hpt] using hx
    have := hWU hy
    simp only [Scheme.Hom.mem_preimage] at this ⊢
    rwa [← Scheme.Hom.comp_apply, hπsnd]
  · obtain ⟨y, hy⟩ := hWne
    refine ⟨πX y, ?_⟩
    have hy' : y ∈ fΩ ⁻¹ᵁ (P1.mapOfAlgebra K.1 Ω ⁻¹ᵁ puncturedLine K.1) := by
      rw [hpre]; exact hy
    simp only [Scheme.Hom.mem_preimage, SetLike.mem_coe] at hy' ⊢
    rwa [← hpt]
  · refine of_morphismRestrict_of_isPullback @Etale hS0 (puncturedLine K.1) ?_
    rw [hpre]
    exact hWet
  · obtain ⟨y, rfl⟩ := πX.surjective x
    refine ⟨y, fun hy ↦ hx ?_, ?_⟩
    · have hy' : y ∈ fΩ ⁻¹ᵁ (P1.mapOfAlgebra K.1 Ω ⁻¹ᵁ puncturedLine K.1) := by
        rw [hpre]; exact hy
      simp only [Scheme.Hom.mem_preimage] at hy' ⊢
      rwa [← hpt]
    · rw [← Scheme.Hom.comp_apply, hπsnd]

end BelyiUp

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M]

/-- **Input of [AbsTopII] Example 3.6 (ii)** (Definition 3.5, *strictly Belyi type*, normalised)
for an affine hyperbolic curve `CX` over `K`: over a number field `M ⊇ K`, a hyperbolic curve
`CV = (V̄, V)` with a cusp, a finite étale `FV : V ⟶ X` over `Spec M ⟶ Spec K` and a finite étale
`FQ : V ⟶ Q` over `M` onto an open `Q ⊆ ℙ¹_M ∖ {0, 1, ∞}`. -/
structure StrictlyBelyiInput (CX : HypCurve K) (M : Type u) [Field M] [NumberField M]
    [Algebra K M] where
  /-- The curve `(V̄, V)`. -/
  CV : HypCurve M
  hcV : (CV.U : Set CV.Xbar)ᶜ.Nonempty
  /-- `V ⟶ X`. -/
  FV : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(CX.Xbar, CX.U)
  [finFV : IsFiniteEtale FV]
  hFV : FV ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K M))
  /-- The genus-zero curve `Q ⊆ ℙ¹ ∖ {0, 1, ∞}`. -/
  Q : (P1 M).Opens
  hQ : Q ≤ puncturedLine M
  hQne : (Q : Set (P1 M)).Nonempty
  /-- `V ⟶ Q`. -/
  FQ : Spec Γ(CV.Xbar, CV.U) ⟶ Spec Γ(P1 M, Q)
  [finFQ : IsFiniteEtale FQ]
  hFQ : FQ ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(P1 M, Q))) =
    Spec.map (CommRingCat.ofHom (algebraMap M Γ(CV.Xbar, CV.U)))

attribute [instance] StrictlyBelyiInput.finFV StrictlyBelyiInput.finFQ

section FinSub

variable (Ω : Type u) [Field Ω] [Algebra M Ω]

instance numberField_finSub' (M' : FinSub M Ω) : NumberField M'.1 :=
  haveI := M'.2
  haveI : CharZero M'.1 := charZero_of_injective_algebraMap (algebraMap M M'.1).injective
  { to_finiteDimensional := Module.Finite.trans M M'.1 }

end FinSub

/-! ### Topological lemmas -/

section Topology

variable {X : Scheme.{u}}

/-- Nonemptiness of the complement passes to smaller opens. -/
lemma compl_nonempty_of_le {U U' : X.Opens} (h : U ≤ U') (hc : (U' : Set X)ᶜ.Nonempty) :
    (U : Set X)ᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := hc
  exact ⟨x, fun hx' ↦ hx (h hx')⟩

/-- Finiteness of the complement passes to larger opens. -/
lemma compl_finite_of_le {U U' : X.Opens} (h : U ≤ U') (hf : (U : Set X)ᶜ.Finite) :
    (U' : Set X)ᶜ.Finite :=
  hf.subset fun _ hx hx' ↦ hx (h hx')

/-- A finite étale morphism to a connected scheme from a nonempty scheme is surjective. -/
lemma surjective_of_isFiniteEtale {Y : Scheme.{u}} (g : Y ⟶ X) [IsFiniteEtale g]
    [ConnectedSpace X] [Nonempty Y] : Function.Surjective g := by
  have ho : IsOpen (Set.range g) := g.isOpenMap.isOpen_range
  have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
  exact Set.range_eq_univ.mp (IsClopen.eq_univ ⟨hc, ho⟩ (Set.range_nonempty g))

end Topology

/-! ### Hyperbolicity along runs of fillings -/

section Hyp

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- If `2 < 2g + r(U)` and `U' ⊆ U` has finite complement, then `2 < 2g + r(U')`. -/
lemma hyp_of_le {U U' : X.Opens} (h : U' ≤ U) (hf : (U' : Set X)ᶜ.Finite) {g : ℕ}
    (hyp : 2 < 2 * g + Anabelian.cuspDegree k X U) :
    2 < 2 * g + Anabelian.cuspDegree k X U' :=
  lt_of_lt_of_le hyp (Nat.add_le_add_left (cuspDegree_anti h hf) _)

end Hyp

/-! ### The construction -/

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic M Ω] {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)
  (S : StrictlyBelyiInput CX M)

namespace StrictlyBelyiInput

omit [NumberField K] in
lemma isAffineOpen_V : IsAffineOpen S.CV.U := isAffineOpen_U S.CV S.hcV

/-- `U₀ = V ×_X U_X` as an open of `V̄`. -/
def U₀ (UX : CX.Xbar.Opens) : S.CV.Xbar.Opens :=
  (S.isAffineOpen_V).fromSpec ''ᵁ (S.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX))

lemma U₀_le (UX : CX.Xbar.Opens) : S.U₀ hcX UX ≤ S.CV.U := by
  rintro _ ⟨x, -, rfl⟩
  change _ ∈ (S.CV.U : Set S.CV.Xbar)
  rw [← (S.isAffineOpen_V).range_fromSpec]
  exact ⟨x, rfl⟩

lemma U₀_nonempty (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ((S.U₀ hcX UX : S.CV.Xbar.Opens) : Set S.CV.Xbar).Nonempty := by
  haveI := isIntegral_specSections CX hcX
  haveI := isIntegral_specSections S.CV S.hcV
  obtain ⟨x, hx⟩ := hUXne
  have hx' : x ∈ Set.range (isAffineOpen_U CX hcX).fromSpec := by
    rw [IsAffineOpen.range_fromSpec]; exact hUX hx
  obtain ⟨t, rfl⟩ := hx'
  obtain ⟨s, rfl⟩ := surjective_of_isFiniteEtale S.FV t
  exact ⟨_, ⟨s, hx, rfl⟩⟩

end StrictlyBelyiInput

/-- `Spec.map (algebraMap R R) = 𝟙`. -/
lemma specMap_algebraMap_self (R : Type u) [CommRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- `Spec` of `g.appLE` is compatible with the structure maps of schemes over `Spec R`. -/
lemma specMap_appLE_algebraMap {X Y : Scheme.{u}} (g : X ⟶ Y) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [g.IsOver (Spec (.of R))] (U : Y.Opens)
    (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U) :
    Spec.map (g.appLE U V h) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (FiniteEtale.appLE_comp_algebraMap g R U V h)

/-- The complement of an open with positive cusp degree is nonempty. -/
lemma compl_nonempty_of_cuspDegree_pos {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {U : X.Opens} (h : 0 < Anabelian.cuspDegree k X U) :
    (U : Set X)ᶜ.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  rw [Anabelian.cuspDegree, he, finsum_mem_empty] at h
  exact lt_irrefl 0 h

include S in
/-- **Existence of Belyi data over a field normal over `K`** ([AbsTopII] Example 3.6,
Corollary 3.7 (a)): for an affine hyperbolic curve `CX` over a number field `K` of strictly Belyi
type (`S`) and a nonempty open `U_X ⊆ X`, there are a finite extension `M'` of `M` in `Ω`, Belyi
data `D` over `M'` and `j ≤ r` such that the `j`-th open of the run of fillings `W ⊆ … ⊆ V` is
`V ×_X U_X`; moreover `M'` is stable under `Gal(Ω/K)` (the normal closure of the Belyi field,
`normalFinSub`), and `D.FV : V_{M'} ⟶ X` is `V_{M'} ⟶ V ⟶ X` for a cartesian square
`V_{M'} = V ×_M M'`. -/
theorem exists_belyiData_normal (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ∃ (M' : FinSub M Ω) (D : BelyiData (M := M'.1) CX) (j : ℕ) (hj : j ≤ D.r)
      (hVa : IsAffineOpen (D.UW (Fin.last D.r))),
      D.UW ⟨j, Nat.lt_succ_of_le hj⟩ =
        hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)) ∧
      (∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ M'.1, σ x ∈ M'.1) ∧
      ∃ aV : Spec Γ(D.CV.Xbar, D.CV.U) ⟶ Spec Γ(S.CV.Xbar, S.CV.U),
        IsPullback aV (Spec.map (CommRingCat.ofHom (algebraMap M'.1 Γ(D.CV.Xbar, D.CV.U))))
          (Spec.map (CommRingCat.ofHom (algebraMap M Γ(S.CV.Xbar, S.CV.U))))
          (specAlgebraMap M M'.1) ∧ D.FV = aV ≫ S.FV := by
  classical
  -- the field over which the cusps to be filled become rational ([AbsTopII] Example 3.6,
  -- l.4634–4635, l.4667–4668): the cusps of `Q` lie over `ℙ¹_M ∖ Q`, those of `W` over `S₀`
  let PQ : FinSub M Ω := ratFinSub M Ω ((S.Q : Set (P1 M))ᶜ)
  let P : Set S.CV.Xbar → FinSub M Ω := fun T ↦
    haveI := (ratFinSub M Ω T).2
    haveI := PQ.2
    ⟨(ratFinSub M Ω T).1 ⊔ PQ.1, IntermediateField.finiteDimensional_sup _ _⟩
  obtain ⟨S₀, M', f, hS₀fin, hPM', hfo, -, hWU, hWne, hfinP, hetP, hS₀, L₀, hL₀⟩ :=
    exists_belyi_open_le_finSub_ge_up M Ω S.CV.Xbar (S.U₀ hcX UX) (S.U₀_nonempty hcX UX hUX hUXne)
      P (normalFinSub K) (le_normalFinSub K)
  -- `M'` is the normal closure of `L₀` over `K`
  have hM'st : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ M'.1, σ x ∈ M'.1 := by
    rw [hL₀]
    exact normalFinSub_stable K L₀
  have hPM : (P S₀).1 ≤ M'.1 := hPM'
  haveI := M'.2
  -- the curve `V̄_L` and its opens
  set Xw := bcX M M'.1 S.CV.Xbar with hXw
  set π := bcπ M M'.1 S.CV.Xbar with hπ
  have hπs : Function.Surjective π := surjective_bcπ M M'.1 S.CV.Xbar
  set W : Xw.Opens := f ⁻¹ᵁ puncturedLine M'.1 with hWdef
  set Vb : Xw.Opens := π ⁻¹ᵁ S.CV.U with hVb
  set Ub : Xw.Opens := π ⁻¹ᵁ S.U₀ hcX UX with hUb
  have hWUb : W ≤ Ub := hWU
  have hUbVb : Ub ≤ Vb := fun x hx ↦ S.U₀_le hcX UX hx
  have hWfin : (W : Set Xw)ᶜ.Finite := finite_compl_of_isCurveOver (k := M'.1) Xw W hWne
  have hcVb : (Vb : Set Xw)ᶜ.Nonempty := by
    obtain ⟨c, hc⟩ := S.hcV
    obtain ⟨x, rfl⟩ := hπs c
    exact ⟨x, hc⟩
  haveI := IsCurveOver.isIntegral M S.CV.Xbar
  haveI := IsCurveOver.isIntegral M'.1 Xw
  have hypVb : 2 < 2 * Anabelian.curveGenus M'.1 Xw + Anabelian.cuspDegree M'.1 Xw Vb :=
    lt_of_lt_of_le S.CV.hyperbolic (Nat.add_le_add (Nat.mul_le_mul_left 2
      (curveGenus_le_bc M M'.1 S.CV.Xbar)) (cuspDegree_le_bc M M'.1 S.CV.Xbar S.CV.U S.CV.nonempty))
  have hypW : ∀ U' : Xw.Opens, W ≤ U' → U' ≤ Vb →
      2 < 2 * Anabelian.curveGenus M'.1 Xw + Anabelian.cuspDegree M'.1 Xw U' := fun U' h₁ h₂ ↦
    hyp_of_le h₂ (compl_finite_of_le h₁ hWfin) hypVb
  -- the run of fillings `W ⊆ … ⊆ U_b ⊆ … ⊆ V_b`
  obtain ⟨r, j, hj, UW, xW, hW0, hWlast, hWmid, hleW, hleWV, hmonoW, hxW1, hxW2, hxW3⟩ :=
    exists_fillSeq W Ub Vb hWUb hUbVb (hWfin.subset fun _ hx ↦ hx.2)
      (fun _ hx ↦ isClosed_singleton_of_not_mem (k := M'.1) Xw W hWne hx.2)
  -- the filled points of `V̄_{M'}` are `M'`-rational
  haveI : IsFinite (specAlgebraMap M M'.1) := by
    rw [specAlgebraMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI : IsFinite π := MorphismProperty.pullback_snd (P := @IsFinite) _ _ inferInstance
  have hratW : ∀ i, IsIso ((Xw ↘ Spec (.of M'.1)).residueFieldMap (xW i)) := by
    intro i
    have hxWW : xW i ∉ W := fun h ↦ hxW2 i (hleW i.castSucc h)
    have hcl : IsClosed {xW i} := isClosed_singleton_of_not_mem (k := M'.1) Xw W hWne hxWW
    letI := Anabelian.residueFieldAlgebra M'.1 Xw (xW i)
    haveI := finite_residueField M'.1 hcl
    refine isIso_residueFieldMap_bcX M M'.1 Ω (xW i) inferInstance fun σ a ↦ ?_
    have hclπ : IsClosed {π (xW i)} := by
      have := π.isClosedMap _ hcl
      rwa [Set.image_singleton] at this
    have hmem := mem_ratFinSub M Ω hS₀fin (hS₀ _ hxWW) hclπ σ a
    exact ⟨⟨σ a, hPM (le_sup_left (a := (ratFinSub M Ω S₀).1) hmem)⟩, rfl⟩
  let CW : HypCurve M'.1 :=
    { Xbar := Xw, U := W, nonempty := hWne, cusps_finite := hWfin
      hyperbolic := hypW W le_rfl (hWUb.trans hUbVb) }
  -- the line `ℙ¹_L` and its opens
  set Pm := P1.mapOfAlgebra M M'.1 with hPm
  have hPsq := P1.isPullback_mapOfAlgebra M M'.1
  haveI : Surjective Pm := MorphismProperty.of_isPullback (P := @Surjective) hPsq.flip
    inferInstance
  set Q' : (P1 M'.1).Opens := Pm ⁻¹ᵁ S.Q with hQ'
  have hpre : Pm ⁻¹ᵁ puncturedLine M = puncturedLine M'.1 := by
    rw [← opensRange_puncturedι, ← opensRange_puncturedι]
    exact mapOfAlgebra_preimage_opensRange_puncturedι M M'.1
  have hQ'P : Q' ≤ puncturedLine M'.1 := by
    rw [← hpre]; exact fun x hx ↦ S.hQ hx
  have hQ'ne : (Q' : Set (P1 M'.1)).Nonempty := by
    obtain ⟨q, hq⟩ := S.hQne
    obtain ⟨x, rfl⟩ := Pm.surjective q
    exact ⟨x, hq⟩
  have hQ'fin : (Q' : Set (P1 M'.1))ᶜ.Finite :=
    finite_compl_of_isCurveOver (k := M'.1) (P1 M'.1) Q' hQ'ne
  have h3 := three_le_cuspDegree_puncturedLine M'.1
  have hcP : (puncturedLine M'.1 : Set (P1 M'.1))ᶜ.Nonempty :=
    compl_nonempty_of_cuspDegree_pos (k := M'.1) (by omega)
  have hypQ : ∀ U' : (P1 M'.1).Opens, Q' ≤ U' → U' ≤ puncturedLine M'.1 →
      2 < 2 * Anabelian.curveGenus M'.1 (P1 M'.1) + Anabelian.cuspDegree M'.1 (P1 M'.1) U' :=
    fun U' h₁ h₂ ↦ hyp_of_le (k := M'.1) h₂ (compl_finite_of_le h₁ hQ'fin) (by omega)
  obtain ⟨l, j', hj', UQ, xQ, hQ0, hQlast, -, hleQ, hleQP, hmonoQ, hxQ1, hxQ2, hxQ3⟩ :=
    exists_fillSeq Q' (puncturedLine M'.1) (puncturedLine M'.1) hQ'P le_rfl
      (hQ'fin.subset fun _ hx ↦ hx.2)
      (fun _ hx ↦ isClosed_singleton_of_not_mem (k := M'.1) (P1 M'.1) Q' hQ'ne hx.2)
  -- the filled points of `ℙ¹_{M'}` are `M'`-rational
  have hQrat : ∀ y ∈ (S.Q : Set (P1 M))ᶜ, ∀ (σ : ResEmb M Ω (P1 M) y) a,
      σ a ∈ Set.range (algebraMap M'.1 Ω) := fun y hy σ a ↦ by
    have hmem := mem_ratFinSub M Ω (finite_compl_of_isCurveOver (k := M) (P1 M) S.Q S.hQne) hy
      (isClosed_singleton_of_not_mem (k := M) (P1 M) S.Q S.hQne hy) σ a
    exact ⟨⟨σ a, hPM (le_sup_right (b := PQ.1) hmem)⟩, rfl⟩
  have hratQ : ∀ i, IsIso ((P1 M'.1 ↘ Spec (.of M'.1)).residueFieldMap (xQ i)) := by
    intro i
    have hxQQ : xQ i ∉ Q' := fun h ↦ hxQ2 i (hleQ i.castSucc h)
    have hcl : IsClosed {xQ i} :=
      isClosed_singleton_of_not_mem (k := M'.1) (P1 M'.1) Q' hQ'ne hxQQ
    let e := hPsq.flip.isoPullback
    have he1 : e.hom ≫ pullback.fst _ _ = (P1 M'.1 ↘ Spec (.of M'.1)) :=
      hPsq.flip.isoPullback_hom_fst
    have he2 : e.hom ≫ pullback.snd _ _ = Pm := hPsq.flip.isoPullback_hom_snd
    have hcl' : IsClosed {e.hom (xQ i)} := by
      have := (Scheme.homeoOfIso e).isClosedMap _ hcl
      rwa [Set.image_singleton] at this
    letI := Anabelian.residueFieldAlgebra M'.1 (bcX M M'.1 (P1 M)) (e.hom (xQ i))
    haveI := finite_residueField M'.1 hcl'
    have hy : bcπ M M'.1 (P1 M) (e.hom (xQ i)) ∈ (S.Q : Set (P1 M))ᶜ := by
      change (e.hom ≫ pullback.snd _ _) (xQ i) ∉ (S.Q : Set (P1 M))
      rw [he2]
      exact hxQQ
    haveI key : IsIso ((pullback.fst (specAlgebraMap M M'.1) (P1 M ↘ Spec (.of M))).residueFieldMap
        (e.hom (xQ i))) :=
      isIso_residueFieldMap_bcX M M'.1 Ω (X := P1 M) _ inferInstance (hQrat _ hy)
    rw [← he1, Scheme.residueFieldMap_comp]
    infer_instance
  let CQ : HypCurve M'.1 :=
    { Xbar := P1 M'.1, U := Q', nonempty := hQ'ne, cusps_finite := hQ'fin
      hyperbolic := hypQ Q' le_rfl hQ'P }
  -- the maps
  have hsqV := isPullback_bcπ M M'.1 S.CV.Xbar
  have hQaff : IsAffineOpen S.Q :=
    isAffineOpen_of_isCurveOver (k := M) (P1 M) S.Q S.hQne
      (finite_compl_of_isCurveOver (k := M) (P1 M) S.Q S.hQne)
      (compl_nonempty_of_le S.hQ (compl_nonempty_of_cuspDegree_pos (k := M)
        (by have := three_le_cuspDegree_puncturedLine M; omega)))
  have hsqVΓ := isPullback_specΓ π hsqV hWlast S.isAffineOpen_V
  have hsqQΓ := isPullback_specΓ Pm hPsq (V := Q') rfl hQaff
  set aV := Spec.map (π.appLE S.CV.U (UW (Fin.last r)) hWlast.le) with haV
  set aQ := Spec.map (Pm.appLE S.Q Q' le_rfl) with haQ
  haveI : IsFiniteEtale aV := isFiniteEtale_specΓ π hsqV hWlast S.isAffineOpen_V
  have hwV : (aV ≫ S.FQ) ≫ Spec.map (CommRingCat.ofHom (algebraMap M Γ(P1 M, S.Q))) =
      Spec.map (CommRingCat.ofHom (algebraMap M'.1 Γ(Xw, UW (Fin.last r)))) ≫
        specAlgebraMap M M'.1 := by
    rw [Category.assoc, S.hFQ]; exact hsqVΓ.w
  let FQ' := hsqQΓ.lift (aV ≫ S.FQ) _ hwV
  have htop : IsPullback aV FQ' S.FQ aQ := by
    refine IsPullback.of_bot ?_ (hsqQΓ.lift_fst _ _ hwV).symm hsqQΓ
    convert hsqVΓ using 1
    · exact hsqQΓ.lift_snd _ _ hwV
    · exact S.hFQ
  haveI : IsFiniteEtale FQ' := MorphismProperty.of_isPullback (P := @IsFiniteEtale) htop
    inferInstance
  have hβeq : W = f ⁻¹ᵁ UQ (Fin.last l) := by rw [hQlast]
  have hβle : W ≤ f ⁻¹ᵁ UQ (Fin.last l) := hβeq.le
  have hPaff : IsAffineOpen (UQ (Fin.last l)) := by
    rw [hQlast]
    exact isAffineOpen_of_isCurveOver (k := M'.1) (P1 M'.1) _ (hQ'ne.mono hQ'P)
      (compl_finite_of_le hQ'P hQ'fin) hcP
  have hWaff : IsAffineOpen W :=
    isAffineOpen_of_isCurveOver (k := M'.1) Xw W hWne hWfin
      (compl_nonempty_of_le (hWUb.trans hUbVb) hcVb)
  haveI : IsFinite (f ∣_ UQ (Fin.last l)) := by rw [hQlast]; exact hfinP
  haveI : Etale (f ∣_ UQ (Fin.last l)) := by rw [hQlast]; exact hetP
  haveI : IsFiniteEtale (Spec.map (f.appLE (UQ (Fin.last l)) W hβle)) :=
    isFiniteEtale_specMap_appLE f _ W hβeq hPaff hWaff
  haveI : f.IsOver (Spec (.of M'.1)) := ⟨hfo⟩
  let D : BelyiData (M := M'.1) CX :=
    { CQ := CQ, hcQ := compl_nonempty_of_le hQ'P hcP, l := l, UQ := UQ, hUQ0 := hQ0
      hleQ := hleQ, hmonoQ := hmonoQ
      hcUQ := fun i ↦ compl_nonempty_of_le (hleQP i) hcP
      hypQ := fun i ↦ hypQ _ (hleQ i) (hleQP i)
      xQ := xQ, hxUQ := hxQ1, hxUQ' := hxQ2, hxQ := hxQ3, ratQ := hratQ
      h3Q := (three_le_cuspDegree_puncturedLine M'.1).trans (cuspDegree_anti hQ'P hQ'fin)
      CW := CW, hcW := compl_nonempty_of_le (hWUb.trans hUbVb) hcVb, r := r, UW := UW
      hUW0 := hW0, hleW := hleW, hmonoW := hmonoW
      hcUW := fun i ↦ compl_nonempty_of_le (hleWV i) hcVb
      hypW := fun i ↦ hypW _ (hleW i) (hleWV i)
      xW := xW, hxUW := hxW1, hxUW' := hxW2, hxW := hxW3, ratW := hratW
      FV := aV ≫ S.FV
      hFV := by
        rw [Category.assoc, S.hFV, ← Category.assoc, hsqVΓ.w, Category.assoc]
        exact congrArg _ (specAlgebraMap_comp_specAlgebraMap K M M'.1)
      FQ := FQ'
      hFQ := (hsqQΓ.lift_snd _ _ hwV).trans
        (by rw [specMap_algebraMap_self, Category.comp_id])
      β := Spec.map (f.appLE (UQ (Fin.last l)) W hβle)
      hβ := by
        rw [specMap_appLE_algebraMap f M'.1 _ W hβle, specMap_algebraMap_self, Category.comp_id] }
  have hVa : IsAffineOpen (D.UW (Fin.last D.r)) := by
    change IsAffineOpen (UW (Fin.last r))
    rw [hWlast]
    exact isAffineOpen_of_isPullback π hsqV rfl S.isAffineOpen_V
  refine ⟨M', D, j, hj, hVa, ?_, hM'st, aV, hsqVΓ, rfl⟩
  change UW _ = hVa.fromSpec ''ᵁ ((aV ≫ S.FV) ⁻¹ᵁ _)
  rw [hWmid]
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec π S.isAffineOpen_V hVa hWlast.le
  have e : ∀ t, S.isAffineOpen_V.fromSpec (aV t) = π (hVa.fromSpec t) := fun t ↦ by
    change (aV ≫ S.isAffineOpen_V.fromSpec) t = (hVa.fromSpec ≫ π) t
    rw [hcomm]
  have hrV : ∀ s, S.isAffineOpen_V.fromSpec s ∈ (S.CV.U : Set S.CV.Xbar) := fun s ↦
    S.isAffineOpen_V.range_fromSpec ▸ Set.mem_range_self s
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hxV : x ∈ (UW (Fin.last r) : Set Xw) := by
      rw [hWlast]
      change π x ∈ (S.CV.U : Set S.CV.Xbar)
      rw [← hsx]
      exact hrV s
    have hxV' : x ∈ Set.range hVa.fromSpec := by
      rw [hVa.range_fromSpec]; exact hxV
    obtain ⟨t, rfl⟩ := hxV'
    refine ⟨t, ?_, rfl⟩
    have ht : S.isAffineOpen_V.fromSpec (aV t) = S.isAffineOpen_V.fromSpec s :=
      (e t).trans hsx.symm
    have h2 : aV t = s := S.isAffineOpen_V.fromSpec.isOpenEmbedding.injective ht
    have h3 : (aV ≫ S.FV) t = S.FV s := by
      change S.FV (aV t) = S.FV s
      rw [h2]
    change (aV ≫ S.FV) t ∈ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX : Set _)
    rw [h3]
    exact hs
  · rintro ⟨t, ht, rfl⟩
    exact ⟨aV t, ht, e t⟩

include S in
/-- **Existence of Belyi data** ([AbsTopII] Example 3.6, Corollary 3.7 (a)): for an affine
hyperbolic curve `CX` over a number field `K` of strictly Belyi type (`S`) and a nonempty open
`U_X ⊆ X`, there are a finite extension `M'` of `M` in `Ω`, Belyi data `D` over `M'` and `j ≤ r`
such that the `j`-th open of the run of fillings `W ⊆ … ⊆ V` is `V ×_X U_X`, i.e. the preimage of
`U_X` under `V ≅ Spec Γ(V) ⟶ Spec Γ(X) ≅ X` (`FV`). -/
theorem exists_belyiData (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ∃ (M' : FinSub M Ω) (D : BelyiData (M := M'.1) CX) (j : ℕ) (hj : j ≤ D.r)
      (hVa : IsAffineOpen (D.UW (Fin.last D.r))),
      D.UW ⟨j, Nat.lt_succ_of_le hj⟩ =
        hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)) := by
  obtain ⟨M', D, j, hj, hVa, h, -, -⟩ := exists_belyiData_normal Ω hcX S UX hUX hUXne
  exact ⟨M', D, j, hj, hVa, h⟩

/-! ### [AbsTopII] Corollary 3.7 (a) -/

section Cor37a

variable [Algebra.IsAlgebraic K Ω] [CharZero Ω]

instance isAlgebraic_finSub (M' : FinSub M Ω) : Algebra.IsAlgebraic M'.1 Ω :=
  Algebra.IsAlgebraic.tower_top (K := M) (L := M'.1) (A := Ω)

instance isScalarTower_finSub (M' : FinSub M Ω) : IsScalarTower K M'.1 Ω :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (IsScalarTower.algebraMap_apply K M Ω x).trans
    (by rw [IsScalarTower.algebraMap_apply K M M'.1 x]; rfl)

attribute [local instance] isAlgClosure_of_isAlgebraic

set_option maxHeartbeats 1000000 in
-- matching the existential of `exists_belyiData` (Belyi data over `M'.1`) is slow
include S in
/-- **[AbsTopII] Corollary 3.7 (a) over a field normal over `K`**: `exists_belyiCandidate` with
`M'` stable under `Gal(Ω/K)` and `D.FV = (V_{M'} ⟶ V) ≫ S.FV` for a cartesian square
`V_{M'} = V ×_M M'` (`exists_belyiData_normal`). -/
theorem exists_belyiCandidate_normal (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ∃ (M' : FinSub M Ω) (D : BelyiData (M := M'.1) CX) (m : ℕ) (hm : m ≤ D.r)
      (hVa : IsAffineOpen (D.UW (Fin.last D.r))),
      D.UW ⟨D.r - m, by omega⟩ =
        hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)) ∧
      PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm ∈
        belyiCusp (arithmeticExt Ω CX hcX) ∧
      (∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ M'.1, σ x ∈ M'.1) ∧
      (∃ aV : Spec Γ(D.CV.Xbar, D.CV.U) ⟶ Spec Γ(S.CV.Xbar, S.CV.U),
        IsPullback aV (Spec.map (CommRingCat.ofHom (algebraMap M'.1 Γ(D.CV.Xbar, D.CV.U))))
          (Spec.map (CommRingCat.ofHom (algebraMap M Γ(S.CV.Xbar, S.CV.U))))
          (specAlgebraMap M M'.1) ∧ D.FV = aV ≫ S.FV) ∧
      ∃ (eU : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiU ≃ₜ*
          π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW ⟨D.r - m, by omega⟩) ≫
            baseChangeSpec M'.1 Ω Γ(D.CW.Xbar, D.UW ⟨D.r - m, by omega⟩)))
        (eV : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiV ≃ₜ*
          π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
            baseChangeSpec M'.1 Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r)))),
        (∀ x, eV ((PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).surj
            x) = D.stepHom Ω ⟨D.r - m, by omega⟩ (Fin.last D.r) (Fin.le_last _) (eU x)) ∧
          ∀ y, (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).emb y =
            D.φ₄ Ω hcX (eV y) := by
  have hex := exists_belyiData_normal Ω hcX S UX hUX hUXne
  obtain ⟨M', D, j, hj, hVa, h, hst, hsq⟩ := hex
  refine ⟨M', D, D.r - j, Nat.sub_le _ _, hVa, ?_, ?_, hst, hsq, ?_⟩
  rotate_left
  · exact D.belyiCandidate_mem Ω hcX _ _
  · exact D.belyiCandidate_spec Ω hcX _ _
  have he : (⟨D.r - (D.r - j), by omega⟩ : Fin (D.r + 1)) = ⟨j, Nat.lt_succ_of_le hj⟩ :=
    Fin.ext (by simp only; omega)
  rw [he]
  exact h

set_option maxHeartbeats 1000000 in
-- matching the existential of `exists_belyiData` (Belyi data over `M'.1`) is slow
include S in
/-- **[AbsTopII] Corollary 3.7 (a)** for an affine hyperbolic curve `CX` of strictly Belyi type
over a number field: for every nonempty open `U_X ⊆ X` there is a Belyi chain (Belyi data `D`
over a finite extension `M'`) and `m ≤ r` such that, for `U = UW_{r-m} = V ×_X U_X`, the
candidate of the chain lies in `belyiCusp Π_X` and is `Π_U ↠ Π_V ↪ Π_X`. -/
theorem exists_belyiCandidate (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
    (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ∃ (M' : FinSub M Ω) (D : BelyiData (M := M'.1) CX) (m : ℕ) (hm : m ≤ D.r)
      (hVa : IsAffineOpen (D.UW (Fin.last D.r))),
      D.UW ⟨D.r - m, by omega⟩ =
        hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)) ∧
      PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm ∈
        belyiCusp (arithmeticExt Ω CX hcX) ∧
      ∃ (eU : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiU ≃ₜ*
          π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW ⟨D.r - m, by omega⟩) ≫
            baseChangeSpec M'.1 Ω Γ(D.CW.Xbar, D.UW ⟨D.r - m, by omega⟩)))
        (eV : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiV ≃ₜ*
          π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
            baseChangeSpec M'.1 Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r)))),
        (∀ x, eV ((PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).surj
            x) = D.stepHom Ω ⟨D.r - m, by omega⟩ (Fin.last D.r) (Fin.le_last _) (eU x)) ∧
          ∀ y, (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).emb y =
            D.φ₄ Ω hcX (eV y) := by
  obtain ⟨M', D, m, hm, hVa, h1, h2, -, -, h3⟩ :=
    exists_belyiCandidate_normal Ω hcX S UX hUX hUXne
  exact ⟨M', D, m, hm, hVa, h1, h2, h3⟩

end Cor37a

end CurvesJacobian.Cusp
