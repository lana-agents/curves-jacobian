/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.EulerChar
import CurvesJacobian.Picard.PicFSub
import CurvesJacobian.Picard.PicFRep

/-!
# The degree decomposition `Pic_{C/k,σ} = ∐_d Pic^d_{C/k,σ}` (Stacks, Lemma 44.6.7, Tag 0BA0)

Stacks, Lemma 44.6.7 (Tag 0BA0), first step of the proof: `Pic^d_{X/k}` is the open and closed
subscheme where the Euler characteristic of the universal line bundle is `d + 1 − g`, using the
local constancy of `χ` (Stacks, Lemma 36.32.2, Tag 0B9T; here `exists_isLocallyConstant_chi`).

* `CurvesJacobian.chiCurve`: `χ = h⁰ − h¹` of the chart Čech complex of `M` on `C ×_k T'`.
* `CurvesJacobian.exists_isLocallyConstant_chiCurve`: for `L` invertible on `C ×_k T`, `T`
  affine, there is a locally constant `χ : T → ℤ` with `χ(L_{T''}) = χ(h t)` for every affine
  `T''` with `Γ(T'')` a field, `h : T'' ⟶ T` and `t ∈ T''`.
* `CurvesJacobian.picDeg d`: the subfunctor `Pic^d ⊆ Pic_{C/k,σ}` of points all of whose field
  valued points have `χ = d + 1 − g` (Stacks' definition of `Pic^d`).
* `CurvesJacobian.isLocalPredicate_picDeg`, `CurvesJacobian.picDeg_open`: `Pic^d` is a
  Zariski-local, open subfunctor (tested on affine schemes);
* **`CurvesJacobian.exists_degree_decomposition`**: for every scheme `T` and `x ∈ Pic_{C/k,σ}(T)`
  there are opens `U_d ⊆ T` (`d ∈ ℤ`), pairwise disjoint and covering `T`, such that the
  pullback of `x` along `h : T' ⟶ T` lies in `Pic^d` iff `h` factors through `U_d`. Applied to
  the representing scheme of `Pic_{C/k,σ}` (`isRepresentable_picSigmaSch`) and its universal
  point, this is the decomposition `Pic_{C/k,σ} = ∐_d Pic^d_{C/k,σ}` into open and closed
  subschemes.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace CurvesJacobian

section Points

/-- An affine scheme whose ring of global sections is a field has exactly one point. -/
lemma subsingleton_of_isField {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤)) :
    Subsingleton T := by
  letI := hF.toField
  refine ⟨fun a b ↦ ?_⟩
  have h : ∀ c : T, T.isoSpec.inv (T.isoSpec.hom c) = c := fun c ↦ by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [← h a, ← h b, Subsingleton.elim (α := PrimeSpectrum Γ(T, ⊤)) (T.isoSpec.hom a)
    (T.isoSpec.hom b)]

lemma nonempty_of_isField {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤)) :
    Nonempty T := by
  letI := hF.toField
  exact ⟨T.isoSpec.inv (default : PrimeSpectrum Γ(T, ⊤))⟩

lemma isField_residueField {T : Scheme.{u}} (t : T) :
    IsField Γ(Spec (T.residueField t), ⊤) :=
  MulEquiv.isField (Field.toIsField (T.residueField t))
    (Scheme.ΓSpecIso (T.residueField t)).commRingCatIsoToRingEquiv.toMulEquiv

end Points

namespace Cech

section Iso

variable {S Y Y' : Scheme.{u}} [Y.Over S] [Y'.Over S] (e : Y' ⟶ Y) [IsIso e]
  (he : e ≫ (Y ↘ S) = Y' ↘ S) (L : Y.Modules) [L.IsInvertible]

include he in
/-- The dimensions of Čech `H⁰` and `H¹` are invariant under isomorphisms of schemes. -/
lemma finrank_pullback_iso {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) {U' V' : Y'.Opens} (eU : U' = e ⁻¹ᵁ U) (eV : V' = e ⁻¹ᵁ V) :
    Module.finrank Γ(S, ⊤) (cechModH0 S ((Scheme.Modules.pullback e).obj L) U' V') =
        Module.finrank Γ(S, ⊤) (cechModH0 S L U V) ∧
      Module.finrank Γ(S, ⊤) (cechModH1 S ((Scheme.Modules.pullback e).obj L) U' V') =
        Module.finrank Γ(S, ⊤) (cechModH1 S L U V) := by
  have eUV : U' ⊓ V' = e ⁻¹ᵁ (U ⊓ V) := by subst eU eV; rfl
  have hf := pullbackIsoSections_res e he L hU hUV inf_le_left eU eUV inf_le_left
  have hg := pullbackIsoSections_res e he L hV hUV inf_le_right eV eUV inf_le_right
  exact ⟨(TwoCech.equivH0 _ _ _ hf hg).finrank_eq.symm,
    (TwoCech.equivH1 _ _ _ hf hg).finrank_eq.symm⟩

end Iso

/-- The dimensions of Čech `H⁰` and `H¹` only depend on the isomorphism class of the module. -/
lemma finrank_congr {S Y : Scheme.{u}} [Y.Over S] {L M : Y.Modules} (e : L ≅ M)
    (U V : Y.Opens) :
    Module.finrank Γ(S, ⊤) (cechModH0 S L U V) = Module.finrank Γ(S, ⊤) (cechModH0 S M U V) ∧
      Module.finrank Γ(S, ⊤) (cechModH1 S L U V) =
        Module.finrank Γ(S, ⊤) (cechModH1 S M U V) := by
  have hf := sectionsIso_res (S := S) e (inf_le_left : U ⊓ V ≤ U)
  have hg := sectionsIso_res (S := S) e (inf_le_right : U ⊓ V ≤ V)
  exact ⟨(TwoCech.equivH0 _ _ _ hf hg).finrank_eq, (TwoCech.equivH1 _ _ _ hf hg).finrank_eq⟩

end Cech

open Cech Belyi Scheme.OpenSubfunctor

section Chi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k)

local notation "Sk" => Spec (CommRingCat.of k)

/-- The Euler characteristic `h⁰ − h¹` of the chart Čech complex of `M` on `C ×_k T'`
(`g' : T' ⟶ Spec k`), for the covering by the preimages of the two charts of `ℙ¹` under `π`. -/
def chiCurve {T' : Scheme.{u}} (g' : T' ⟶ Sk) (M : (pullback (C ↘ Sk) g').Modules) : ℤ :=
  (Module.finrank Γ(T', ⊤) (cechModH0 T' M
      ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
      ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)) : ℤ) -
    Module.finrank Γ(T', ⊤) (cechModH1 T' M
      ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
      ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1))

lemma chiCurve_congr {T' : Scheme.{u}} (g' : T' ⟶ Sk) {M M' : (pullback (C ↘ Sk) g').Modules}
    (e : M ≅ M') : chiCurve π g' M = chiCurve π g' M' := by
  obtain ⟨h0, h1⟩ := finrank_congr (S := T') e
    ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0)
    ((pullback.fst (C ↘ Sk) g' ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1)
  rw [chiCurve, chiCurve, h0, h1]

variable [PerfectField k] [IsCurveOver k C] [IsFinite π]

/-- **Local constancy of the Euler characteristic** (Stacks, Lemma 36.32.2, Tag 0B9T), in the
form used for `Pic^d`: for `L` invertible on `C ×_k T` (`T` affine over `k`) there is a locally
constant `χ : T → ℤ` such that `χ(L_{T''}) = χ(h t)` for every affine `T''` whose ring of global
sections is a field, every `h : T'' ⟶ T` and every `t ∈ T''`. -/
theorem exists_isLocallyConstant_chiCurve {T : Scheme.{u}} [T.Over Sk] [IsAffine T]
    (L : (pullback (C ↘ Sk) (T ↘ Sk)).Modules) [L.IsInvertible] :
    ∃ χ : T → ℤ, IsLocallyConstant χ ∧
      ∀ (T'' : Scheme.{u}) [IsAffine T''] (_ : IsField Γ(T'', ⊤)) (h : T'' ⟶ T) (t : T''),
        chiCurve π (h ≫ (T ↘ Sk))
          ((Scheme.Modules.pullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)).obj L) =
          χ (h t) := by
  obtain ⟨χa, hχa, H⟩ := exists_isLocallyConstant_chi (T := T) π L
  refine ⟨χa ∘ T.isoSpec.hom, hχa.comp_continuous T.isoSpec.hom.continuous,
    fun T'' _ hF h t ↦ ?_⟩
  letI : T''.Over T := ⟨h⟩
  have key := H T'' hF (T''.isoSpec.hom t)
  -- the comparison isomorphism `C ×_k T'' ≅ (C ×_k T) ×_T T''`
  have HP : IsPullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)
      (pullback.snd (C ↘ Sk) (h ≫ (T ↘ Sk)))
      (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) :=
    HilbPoint.isPullback_baseChangeMap (C ↘ Sk)
      (Over.homMk h rfl : Over.mk (h ≫ (T ↘ Sk)) ⟶ Over.mk (T ↘ Sk))
  let e := HP.isoPullback.hom
  have he₁ : e ≫ pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) =
      bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl :=
    HP.isoPullback_hom_fst
  have he₂ : e ≫ pullback.snd (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) =
      pullback.snd (C ↘ Sk) (h ≫ (T ↘ Sk)) :=
    HP.isoPullback_hom_snd
  have hpX : bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl ≫ pullback.fst (C ↘ Sk) (T ↘ Sk) =
      pullback.fst (C ↘ Sk) (h ≫ (T ↘ Sk)) := bcMap_fst _ _ _ _ _
  let iso : (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback
      (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T))).obj L) ≅
      (Scheme.Modules.pullback (bcMap (C ↘ Sk) h (T ↘ Sk) (h ≫ (T ↘ Sk)) rfl)).obj L :=
    (Scheme.Modules.pullbackComp e _).app L ≪≫ eqToIso (by rw [he₁])
  have hcharts : ∀ i : Fin 2,
      (pullback.fst (C ↘ Sk) (h ≫ (T ↘ Sk)) ≫ π) ⁻¹ᵁ ProjectiveLine.U k i =
      e ⁻¹ᵁ (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T) ⁻¹ᵁ
        (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k i)) := fun i ↦ by
    rw [← hpX, ← he₁]
    rfl
  have hZU := fun i : Fin 2 ↦ isAffineOpen_preimage_fst (S := T) (T := T'')
    (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k i) (isAffineOpen_chart π i) _ rfl
  have hZUV := isAffineOpen_preimage_fst (S := T) (T := T'')
    (curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      curveChartMap (T₀ := T) π ⁻¹ᵁ ProjectiveLine.U k 1) (isAffineOpen_chart_inf π) _ rfl
  obtain ⟨h0, h1⟩ := finrank_pullback_iso (S := T'') e he₂ ((Scheme.Modules.pullback
    (pullback.fst (pullback (C ↘ Sk) (T ↘ Sk) ↘ T) (T'' ↘ T))).obj L) (hZU 0) (hZU 1) hZUV
    (hcharts 0) (hcharts 1)
  rw [← chiCurve_congr π (h ≫ (T ↘ Sk)) iso, chiCurve, h0, h1, key]
  -- points
  have hnat := Scheme.isoSpec_hom_naturality h
  have halg : ∀ x, (Spec.map h.appTop) x =
      PrimeSpectrum.comap (algebraMap Γ(T, ⊤) Γ(T'', ⊤)) x := fun x ↦ by
    change PrimeSpectrum.comap h.appTop.hom x = _
    congr 2
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  change _ = χa (T.isoSpec.hom (h t))
  rw [← Scheme.Hom.comp_apply, ← hnat, Scheme.Hom.comp_apply, halg]

end Chi

section Degree

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  [PerfectField k] [IsCurveOver k C]
  (σ : Spec (CommRingCat.of k) ⟶ C) (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 _)
  (π : C ⟶ ProjectiveLine.scheme k)

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- The Euler characteristic of a point of `Pic_{C/k,σ}`, on its representative. -/
def chiPoint {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) : ℤ :=
  chiCurve π x.1 (Scheme.Pic.rep (x.2 : picSigmaGrp (C ↘ Sk) σ hσ x.1).1)

/-- **The subfunctor `Pic^d ⊆ Pic_{C/k,σ}`** (Stacks, Lemma 44.6.7, Tag 0BA0): `x ∈ Pic^d(T)` iff
for every field valued point `h : T' ⟶ T` (`T'` affine with `Γ(T')` a field) the Euler
characteristic of the pullback of `x` is `d + 1 − g`. -/
def picDeg (d : ℤ) (T : Scheme.{u}) (x : (sigmaG G).obj (op T)) : Prop :=
  ∀ (T' : Scheme.{u}) [IsAffine T'], IsField Γ(T', ⊤) → ∀ h : T' ⟶ T,
    chiPoint σ hσ π ((sigmaG G).map h.op x) = d + 1 - genusNat k C

omit [PerfectField k] [IsCurveOver k C] in
lemma chiPoint_map {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ Sk)
    (y : picSigmaGrp (C ↘ Sk) σ hσ g) :
    chiPoint σ hσ π ((sigmaG G).map h.op ⟨g, y⟩) =
      chiCurve π (h ≫ g) ((Scheme.Modules.pullback (bcMap (C ↘ Sk) h g (h ≫ g) rfl)).obj
        (Scheme.Pic.rep y.1)) := by
  change chiCurve π (h ≫ g) (Scheme.Pic.rep (Scheme.Pic.map (bcMap (C ↘ Sk) h g (h ≫ g) rfl)
    y.1)) = _
  exact chiCurve_congr π _ (Scheme.Pic.rep_mk _).some

variable [IsFinite π]

/-- The Euler characteristic of a point of `Pic_{C/k,σ}` over an affine scheme, as a locally
constant function. -/
theorem exists_isLocallyConstant_chiPoint {T : Scheme.{u}} [IsAffine T]
    (x : (sigmaG G).obj (op T)) :
    ∃ χ : T → ℤ, IsLocallyConstant χ ∧
      ∀ (T'' : Scheme.{u}) [IsAffine T''] (_ : IsField Γ(T'', ⊤)) (h : T'' ⟶ T) (t : T''),
        chiPoint σ hσ π ((sigmaG G).map h.op x) = χ (h t) := by
  obtain ⟨g, y⟩ := x
  letI : T.Over Sk := ⟨g⟩
  haveI : Scheme.Modules.IsInvertible (X := pullback (C ↘ Sk) (T ↘ Sk))
      (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1) :=
    inferInstanceAs (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1).IsInvertible
  obtain ⟨χ, hχ, H⟩ := exists_isLocallyConstant_chiCurve (T := T) π
    (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1)
  exact ⟨χ, hχ, fun T'' _ hF h t ↦ (chiPoint_map σ hσ π h g y).trans (H T'' hF h t)⟩

/-- **`Pic^d` is open in `Pic_{C/k,σ}`** (Stacks, Lemma 44.6.7, Tag 0BA0, via Tag 0B9T), tested
on affine schemes. -/
theorem picDeg_open (d : ℤ) (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)) :
    ∃ U : T.Opens, ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
      picDeg σ hσ π d T' ((sigmaG G).map h.op x) ↔ Set.range h ⊆ U := by
  obtain ⟨χ, hχ, H⟩ := exists_isLocallyConstant_chiPoint σ hσ π x
  refine ⟨⟨χ ⁻¹' {d + 1 - genusNat k C}, hχ.isOpen_fiber _⟩, fun T' _ h ↦ ⟨fun hd ↦ ?_,
    fun hr T'' _ hF h' ↦ ?_⟩⟩
  · rintro _ ⟨t, rfl⟩
    have h1 := hd _ (isField_residueField t) (T'.fromSpecResidueField t)
    rw [map_map_sigmaG] at h1
    obtain ⟨s⟩ := nonempty_of_isField (isField_residueField t)
    rw [H _ (isField_residueField t) _ s, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply] at h1
    exact h1
  · rw [map_map_sigmaG]
    obtain ⟨s⟩ := nonempty_of_isField hF
    rw [H T'' hF _ s, Scheme.Hom.comp_apply]
    exact hr ⟨h' s, rfl⟩

omit [IsFinite π] in
/-- **`Pic^d` is a Zariski-local predicate.** -/
theorem isLocalPredicate_picDeg (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    (d : ℤ) : IsLocalPredicate (sheafG G hG) (picDeg σ hσ π d) := by
  refine ⟨fun h x hx T'' _ hF h' ↦ ?_, fun x hx T'' _ hF h ↦ ?_⟩
  · change chiPoint σ hσ π ((sigmaG G).map h'.op ((sigmaG G).map h.op x)) = _
    rw [map_map_sigmaG]
    exact hx T'' hF (h' ≫ h)
  · obtain ⟨s⟩ := nonempty_of_isField hF
    haveI := subsingleton_of_isField hF
    obtain ⟨U, hsU, hU⟩ := hx (h s)
    have hrange : Set.range h ⊆ Set.range U.ι := by
      rintro _ ⟨s', rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim s' s]
      exact hsU
    let l := IsOpenImmersion.lift U.ι h hrange
    have hl : l ≫ U.ι = h := IsOpenImmersion.lift_fac _ _ _
    have h1 := hU T'' hF l
    change chiPoint σ hσ π ((sigmaG G).map l.op ((sigmaG G).map U.ι.op x)) = _ at h1
    rwa [map_map_sigmaG, hl] at h1

/-- Over a field, a point of `Pic_{C/k,σ}` lies in `Pic^d` for `d = χ − 1 + g`. -/
lemma picDeg_of_isField {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤))
    (x : (sigmaG G).obj (op T)) :
    picDeg σ hσ π (chiPoint σ hσ π x - 1 + genusNat k C) T x := by
  intro T' _ hF' h
  obtain ⟨χ, -, H⟩ := exists_isLocallyConstant_chiPoint σ hσ π x
  obtain ⟨s⟩ := nonempty_of_isField hF'
  obtain ⟨t⟩ := nonempty_of_isField hF
  haveI := subsingleton_of_isField hF
  have h1 := H T' hF' h s
  have h2 := H T hF (𝟙 T) t
  rw [op_id, Functor.map_id_apply] at h2
  change chiPoint σ hσ π x = χ t at h2
  rw [h1, Subsingleton.elim (h s) t, ← h2]
  ring

/-- **The degree decomposition** `Pic_{C/k,σ} = ∐_d Pic^d_{C/k,σ}` (Stacks, Lemma 44.6.7,
Tag 0BA0, first step): for every scheme `T` and `x ∈ Pic_{C/k,σ}(T)` there are pairwise disjoint
opens `U_d ⊆ T` (`d ∈ ℤ`) covering `T` such that the pullback of `x` along `h : T' ⟶ T` lies in
`Pic^d` iff `h` factors through `U_d`. -/
theorem exists_degree_decomposition (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) :
    ∃ U : ℤ → T.Opens, (∀ (d : ℤ) (T' : Scheme.{u}) (h : T' ⟶ T),
        picDeg σ hσ π d T' ((sigmaG G).map h.op x) ↔ Set.range h ⊆ U d) ∧
      Pairwise (fun d e ↦ Disjoint (U d) (U e)) ∧ ⨆ d, U d = ⊤ := by
  have hU := fun d : ℤ ↦ exists_opens_of_isAffine (F := sheafG G hG)
    (isLocalPredicate_picDeg σ hσ π hG d) (picDeg_open σ hσ π d) x
  choose U hU using hU
  -- membership of a point is tested on its residue field
  have hmem : ∀ (d : ℤ) (t : T), t ∈ U d ↔
      picDeg σ hσ π d _ ((sigmaG G).map (T.fromSpecResidueField t).op x) := fun d t ↦ by
    have := hU d _ (T.fromSpecResidueField t)
    rw [Scheme.range_fromSpecResidueField, Set.singleton_subset_iff] at this
    exact this.symm
  refine ⟨U, hU, fun d e hde ↦ ?_, ?_⟩
  · change Disjoint (U d) (U e)
    rw [disjoint_iff, eq_bot_iff]
    intro t ⟨htd, hte⟩
    change t ∈ U d at htd
    change t ∈ U e at hte
    rw [hmem] at htd hte
    have hF := isField_residueField t
    have h1 := htd _ hF (𝟙 _)
    have h2 := hte _ hF (𝟙 _)
    exact hde (by omega)
  · rw [eq_top_iff]
    intro t _
    have hF := isField_residueField t
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨_, (hmem _ t).mpr
      (picDeg_of_isField σ hσ π hF _)⟩

end Degree

end CurvesJacobian
