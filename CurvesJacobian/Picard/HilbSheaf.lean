/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbSch
import CurvesJacobian.Picard.IdealSheafGlue
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# The Hilbert functor is a Zariski sheaf

We show that `hilbSch f d : Scheme.{u}ᵒᵖ ⥤ Type u` (the functor
`T ↦ Σ (g : T ⟶ S), Hilb^d_{X/S}(T, g)`) is a sheaf for the big Zariski topology
(the Zariski part of Stacks, Lemma 44.2.1, Tag 0B95): `isSheaf_hilbSch`, packaged as
`hilbSheaf f d : Sheaf Scheme.zariskiTopology (Type u)`.

Given an open cover `U i ⟶ T` and compatible points `(g i, Z i)`, the structure morphisms
`g i` glue to `g : T ⟶ S` (as for the subcanonicity of the Zariski topology), the ideal
sheaves of the `Z i ⊆ X_{U i}` glue to an ideal sheaf on `X_T` along the open cover
`X_{U i} ⟶ X_T` (`Scheme.IdealSheafData.glue`), and finiteness, flatness, local finite
presentation and the rank are checked locally on `T`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

variable {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}

/-- A property local at the target holds for `q` if it holds for the left sides of pullback
squares over the members of an open cover. -/
lemma of_isPullback_openCover {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {Y Z : Scheme.{u}} (q : Y ⟶ Z) (𝓤 : Z.OpenCover) {W : 𝓤.I₀ → Scheme.{u}}
    (top : ∀ i, W i ⟶ Y) (left : ∀ i, W i ⟶ 𝓤.X i)
    (sq : ∀ i, IsPullback (top i) (left i) q (𝓤.f i)) (H : ∀ i, P (left i)) : P q :=
  IsZariskiLocalAtTarget.of_openCover 𝓤 fun i ↦ by
    have := H i
    rw [← (sq i).isoPullback_hom_snd] at this
    exact (P.cancel_left_of_respectsIso _ _).mp this

lemma hilbSch_map_mk {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ S)
    (P : HilbPoint f d (Over.mk g)) :
    (hilbSch f d).map a.op ⟨g, P⟩ = ⟨a ≫ g, P.pullback (Over.homMk a rfl)⟩ := rfl

lemma hilbSch_mk_eq {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (h : g₁ = g₂)
    {P₁ : HilbPoint f d (Over.mk g₁)} {P₂ : HilbPoint f d (Over.mk g₂)} (hP : P₁.cast h = P₂) :
    (⟨g₁, P₁⟩ : (hilbSch f d).obj (op T)) = ⟨g₂, P₂⟩ :=
  Sigma.ext h ((HilbPoint.heq_iff h).mpr hP)

lemma cast_eq_of_hilbSch_mk_eq {T : Scheme.{u}} {g₁ g₂ : T ⟶ S}
    {P₁ : HilbPoint f d (Over.mk g₁)} {P₂ : HilbPoint f d (Over.mk g₂)}
    (e : (⟨g₁, P₁⟩ : (hilbSch f d).obj (op T)) = ⟨g₂, P₂⟩) (h : g₁ = g₂) : P₁.cast h = P₂ := by
  subst h
  rw [HilbPoint.cast_rfl]
  exact eq_of_heq (Sigma.mk.inj_iff.mp e).2

section Cover

variable (f)

/-- The map `X ×_{S, g'} T' ⟶ X ×_{S, g} T` induced by `a : T' ⟶ T` with `a ≫ g = g'`. -/
def bcMap {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g') :
    pullback f g' ⟶ pullback f g :=
  HilbPoint.baseChangeMap f (Over.homMk a w : Over.mk g' ⟶ Over.mk g)

variable {T T' : Scheme.{u}} (a : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (w : a ≫ g = g')

@[reassoc (attr := simp)]
lemma bcMap_fst : bcMap f a g g' w ≫ pullback.fst f g = pullback.fst f g' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma bcMap_snd : bcMap f a g g' w ≫ pullback.snd f g = pullback.snd f g' ≫ a :=
  pullback.lift_snd _ _ _

lemma isPullback_bcMap :
    IsPullback (bcMap f a g g' w) (pullback.snd f g') (pullback.snd f g) a :=
  HilbPoint.isPullback_baseChangeMap f _

instance [IsOpenImmersion a] : IsOpenImmersion (bcMap f a g g' w) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bcMap f a g g' w).flip ‹_›

/-- For `J` an ideal sheaf on `X_T` and `a : T' ⟶ T`, the closed subscheme cut out by the
pullback of `J` to `X_{T'}` is the base change along `a` of the closed subscheme cut out
by `J`. -/
lemma isPullback_comap_bcMap (J : (pullback f g).IdealSheafData) :
    IsPullback ((J.comapIso (bcMap f a g g' w)).hom ≫ pullback.snd _ _)
      ((J.comap (bcMap f a g g' w)).subschemeι ≫ pullback.snd f g')
      (J.subschemeι ≫ pullback.snd f g) a := by
  have sq : IsPullback (pullback.snd (bcMap f a g g' w) J.subschemeι)
      (pullback.fst (bcMap f a g g' w) J.subschemeι ≫ pullback.snd f g')
      (J.subschemeι ≫ pullback.snd f g) a :=
    (IsPullback.of_hasPullback (bcMap f a g g' w) J.subschemeι).flip.paste_vert
      (isPullback_bcMap f a g g' w)
  have sq₀ : IsPullback (J.comapIso (bcMap f a g g' w)).hom
      ((J.comap (bcMap f a g g' w)).subschemeι ≫ pullback.snd f g')
      (pullback.fst (bcMap f a g g' w) J.subschemeι ≫ pullback.snd f g') (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]⟩
  have := sq₀.paste_horiz sq
  rwa [Category.id_comp] at this

lemma pullback_ideal_eq_comap_bcMap (P : HilbPoint f d (Over.mk g)) :
    (P.pullback (Over.homMk a w : Over.mk g' ⟶ Over.mk g)).ideal =
      P.ideal.comap (bcMap f a g g' w) :=
  rfl

/-- The base changes `X_{U i} ⟶ X_T` of an open cover `U i ⟶ T` are jointly surjective. -/
lemma exists_mem_range_bcMap (𝓤 : T.OpenCover) (y : ↥(pullback f g)) :
    ∃ i, y ∈ Set.range (bcMap f (𝓤.f i) g _ rfl) := by
  refine ⟨𝓤.idx (pullback.snd f g y), ?_⟩
  obtain ⟨z, hz⟩ : y ∈ Set.range (pullback.snd (𝓤.f (𝓤.idx (pullback.snd f g y)))
      (pullback.snd f g)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    exact 𝓤.covers _
  refine ⟨(isPullback_bcMap f _ g _ rfl).flip.isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]
  exact hz

/-- Points of `Hilb` over `Tᵢ ⟶ T` and `Tⱼ ⟶ T` which agree on all `Z` over both have ideal
sheaves agreeing on the overlap `X_{Tᵢ} ×_{X_T} X_{Tⱼ}`. -/
lemma comap_fst_eq_comap_snd {Tᵢ Tⱼ : Scheme.{u}} (uᵢ : Tᵢ ⟶ T) (uⱼ : Tⱼ ⟶ T)
    (Qᵢ : HilbPoint f d (Over.mk (uᵢ ≫ g))) (Qⱼ : HilbPoint f d (Over.mk (uⱼ ≫ g)))
    (hQ : ∀ {Z : Scheme.{u}} (aᵢ : Z ⟶ Tᵢ) (aⱼ : Z ⟶ Tⱼ), aᵢ ≫ uᵢ = aⱼ ≫ uⱼ →
      ∀ w : aᵢ ≫ uᵢ ≫ g = aⱼ ≫ uⱼ ≫ g,
        Qᵢ.pullback (Over.homMk aᵢ w : Over.mk (aⱼ ≫ uⱼ ≫ g) ⟶ Over.mk (uᵢ ≫ g)) =
          Qⱼ.pullback (Over.homMk aⱼ rfl)) :
    Qᵢ.ideal.comap (pullback.fst (bcMap f uᵢ g _ rfl) (bcMap f uⱼ g _ rfl)) =
      Qⱼ.ideal.comap (pullback.snd (bcMap f uᵢ g _ rfl) (bcMap f uⱼ g _ rfl)) := by
  let aᵢ : pullback (bcMap f uᵢ g _ rfl) (bcMap f uⱼ g _ rfl) ⟶ Tᵢ :=
    pullback.fst _ _ ≫ pullback.snd f (uᵢ ≫ g)
  let aⱼ : pullback (bcMap f uᵢ g _ rfl) (bcMap f uⱼ g _ rfl) ⟶ Tⱼ :=
    pullback.snd _ _ ≫ pullback.snd f (uⱼ ≫ g)
  have ha : aᵢ ≫ uᵢ = aⱼ ≫ uⱼ := by
    simp only [aᵢ, aⱼ, Category.assoc]
    rw [← bcMap_snd f uᵢ g _ rfl, ← bcMap_snd f uⱼ g _ rfl, pullback.condition_assoc]
  have w : aᵢ ≫ uᵢ ≫ g = aⱼ ≫ uⱼ ≫ g := by
    rw [← Category.assoc, ha, Category.assoc]
  have hc : Qᵢ.ideal.comap (bcMap f aᵢ (uᵢ ≫ g) _ w) =
      Qⱼ.ideal.comap (bcMap f aⱼ (uⱼ ≫ g) _ rfl) :=
    congrArg HilbPoint.ideal (hQ aᵢ aⱼ ha w)
  let m : pullback (bcMap f uᵢ g _ rfl) (bcMap f uⱼ g _ rfl) ⟶
      pullback f (aⱼ ≫ uⱼ ≫ g) :=
    pullback.lift (pullback.snd _ _ ≫ pullback.fst f (uⱼ ≫ g)) (𝟙 _) (by
      simp only [aⱼ, Category.assoc, Category.id_comp, pullback.condition])
  have hmᵢ : m ≫ bcMap f aᵢ (uᵢ ≫ g) _ w = pullback.fst _ _ := by
    apply pullback.hom_ext
    · simp only [m, Category.assoc, bcMap_fst, pullback.lift_fst]
      rw [← bcMap_fst f uᵢ g _ rfl, ← bcMap_fst f uⱼ g _ rfl, pullback.condition_assoc]
    · simp only [m, aᵢ, Category.assoc, bcMap_snd, pullback.lift_snd_assoc, Category.id_comp]
  have hmⱼ : m ≫ bcMap f aⱼ (uⱼ ≫ g) _ rfl = pullback.snd _ _ := by
    apply pullback.hom_ext
    · simp only [m, Category.assoc, bcMap_fst, pullback.lift_fst]
    · simp only [m, aⱼ, Category.assoc, bcMap_snd, pullback.lift_snd_assoc, Category.id_comp]
  rw [← hmᵢ, ← hmⱼ]
  exact (Scheme.IdealSheafData.comap_comp _ _ _).trans
    ((congrArg (fun K ↦ K.comap m) hc).trans (Scheme.IdealSheafData.comap_comp _ _ _).symm)

end Cover

section Glue

variable {T : Scheme.{u}} (𝓤 : T.OpenCover) (g : T ⟶ S)
  (Q : ∀ i, HilbPoint f d (Over.mk (𝓤.f i ≫ g)))
  (hI : ∀ i j, (Q i).ideal.comap (pullback.fst (bcMap f (𝓤.f i) g _ rfl)
    (bcMap f (𝓤.f j) g _ rfl)) =
      (Q j).ideal.comap (pullback.snd (bcMap f (𝓤.f i) g _ rfl) (bcMap f (𝓤.f j) g _ rfl)))

/-- The ideal sheaf on `X_T` glued from the ideal sheaves of compatible points `Q i` of `Hilb`
over the members `U i` of an open cover of `T`. -/
def glueIdealHilb : (pullback f g).IdealSheafData :=
  Scheme.IdealSheafData.glue (fun i ↦ bcMap f (𝓤.f i) g _ rfl) (fun i ↦ (Q i).ideal)
    (exists_mem_range_bcMap f g 𝓤) hI

lemma comap_glueIdealHilb (i : 𝓤.I₀) :
    (glueIdealHilb 𝓤 g Q hI).comap (bcMap f (𝓤.f i) g _ rfl) = (Q i).ideal :=
  Scheme.IdealSheafData.comap_glue (fun i ↦ bcMap f (𝓤.f i) g _ rfl) (fun i ↦ (Q i).ideal)
    (exists_mem_range_bcMap f g 𝓤) hI i

lemma isPullback_glueIdealHilb (i : 𝓤.I₀) :
    IsPullback (((glueIdealHilb 𝓤 g Q hI).comapIso (bcMap f (𝓤.f i) g _ rfl)).hom ≫
        pullback.snd _ _)
      (((glueIdealHilb 𝓤 g Q hI).comap (bcMap f (𝓤.f i) g _ rfl)).subschemeι ≫
        pullback.snd f (𝓤.f i ≫ g))
      ((glueIdealHilb 𝓤 g Q hI).subschemeι ≫ pullback.snd f g) (𝓤.f i) :=
  isPullback_comap_bcMap f (𝓤.f i) g _ rfl (glueIdealHilb 𝓤 g Q hI)

lemma isFinite_glueIdealHilb :
    IsFinite ((glueIdealHilb 𝓤 g Q hI).subschemeι ≫ pullback.snd f g) :=
  of_isPullback_openCover _ 𝓤 _ _ (isPullback_glueIdealHilb 𝓤 g Q hI) fun i ↦ by
    rw [comap_glueIdealHilb]
    exact (Q i).isFinite

lemma flat_glueIdealHilb :
    Flat ((glueIdealHilb 𝓤 g Q hI).subschemeι ≫ pullback.snd f g) :=
  of_isPullback_openCover _ 𝓤 _ _ (isPullback_glueIdealHilb 𝓤 g Q hI) fun i ↦ by
    rw [comap_glueIdealHilb]
    exact (Q i).flat

lemma locallyOfFinitePresentation_glueIdealHilb :
    LocallyOfFinitePresentation ((glueIdealHilb 𝓤 g Q hI).subschemeι ≫ pullback.snd f g) :=
  of_isPullback_openCover _ 𝓤 _ _ (isPullback_glueIdealHilb 𝓤 g Q hI) fun i ↦ by
    rw [comap_glueIdealHilb]
    exact (Q i).locallyOfFinitePresentation

/-- The point of `Hilb` over `T` glued from compatible points `Q i` over an open cover. -/
def glueHilbPoint : HilbPoint f d (Over.mk g) where
  ideal := glueIdealHilb 𝓤 g Q hI
  isFinite := isFinite_glueIdealHilb 𝓤 g Q hI
  flat := flat_glueIdealHilb 𝓤 g Q hI
  locallyOfFinitePresentation := locallyOfFinitePresentation_glueIdealHilb 𝓤 g Q hI
  finrank_eq t := by
    haveI := isFinite_glueIdealHilb 𝓤 g Q hI
    haveI := flat_glueIdealHilb 𝓤 g Q hI
    change ((glueIdealHilb 𝓤 g Q hI).subschemeι ≫ pullback.snd f g).finrank t = d
    obtain ⟨s, hs⟩ := 𝓤.covers t
    rw [← hs, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_glueIdealHilb 𝓤 g Q hI _) s,
      comap_glueIdealHilb]
    exact (Q _).finrank_eq s

lemma glueHilbPoint_pullback (i : 𝓤.I₀) :
    (glueHilbPoint 𝓤 g Q hI).pullback
      (Over.homMk (𝓤.f i) rfl : Over.mk (𝓤.f i ≫ g) ⟶ Over.mk g) = Q i :=
  HilbPoint.ext (comap_glueIdealHilb 𝓤 g Q hI i)

end Glue

variable (f d)

/-- The sheaf condition for `hilbSch f d` with respect to an open cover. -/
lemma isSheafFor_hilbSch_ofArrows {T : Scheme.{u}} (𝓤 : T.OpenCover) :
    Presieve.IsSheafFor (hilbSch f d) (Presieve.ofArrows 𝓤.X 𝓤.f) := by
  intro x hx
  -- glue the structure morphisms
  let g₀ : ∀ i, 𝓤.X i ⟶ S := fun i ↦ (x (𝓤.f i) (.mk i)).1
  have hg₀ : ∀ i j, pullback.fst (𝓤.f i) (𝓤.f j) ≫ g₀ i = pullback.snd _ _ ≫ g₀ j :=
    fun i j ↦ congrArg Sigma.fst (hx (pullback.fst (𝓤.f i) (𝓤.f j)) (pullback.snd _ _)
      (.mk i) (.mk j) pullback.condition)
  let g : T ⟶ S := 𝓤.glueMorphisms g₀ hg₀
  have hg : ∀ i, 𝓤.f i ≫ g = g₀ i := 𝓤.ι_glueMorphisms g₀ hg₀
  let Q : ∀ i, HilbPoint f d (Over.mk (𝓤.f i ≫ g)) := fun i ↦
    (x (𝓤.f i) (.mk i)).2.cast (hg i).symm
  have hQ : ∀ i, x (𝓤.f i) (.mk i) = ⟨𝓤.f i ≫ g, Q i⟩ := fun i ↦
    hilbSch_mk_eq (hg i).symm rfl
  have hI : ∀ i j, (Q i).ideal.comap (pullback.fst (bcMap f (𝓤.f i) g _ rfl)
      (bcMap f (𝓤.f j) g _ rfl)) =
        (Q j).ideal.comap (pullback.snd (bcMap f (𝓤.f i) g _ rfl) (bcMap f (𝓤.f j) g _ rfl)) :=
    fun i j ↦ comap_fst_eq_comap_snd f g _ _ (Q i) (Q j) fun aᵢ aⱼ ha w ↦ by
      have hc := hx aᵢ aⱼ (.mk i) (.mk j) ha
      rw [hQ i, hQ j, hilbSch_map_mk, hilbSch_map_mk] at hc
      rw [← cast_eq_of_hilbSch_mk_eq hc w, HilbPoint.cast, HilbPoint.pullback_pullback]
      ext
      exact Category.id_comp _
  refine ⟨⟨g, glueHilbPoint 𝓤 g Q hI⟩, ?_, ?_⟩
  · rintro _ _ ⟨i⟩
    rw [hQ i, hilbSch_map_mk]
    exact hilbSch_mk_eq rfl (by rw [HilbPoint.cast_rfl]; exact glueHilbPoint_pullback 𝓤 g Q hI i)
  · rintro ⟨g', P'⟩ ht
    have e : ∀ i, (⟨𝓤.f i ≫ g', P'.pullback (Over.homMk (𝓤.f i) rfl)⟩ :
        (hilbSch f d).obj (op (𝓤.X i))) = ⟨𝓤.f i ≫ g, Q i⟩ := fun i ↦ by
      rw [← hilbSch_map_mk, ht _ (.mk i), hQ i]
    obtain rfl : g' = g := 𝓤.hom_ext _ _ fun i ↦ congrArg Sigma.fst (e i)
    refine hilbSch_mk_eq rfl ?_
    rw [HilbPoint.cast_rfl]
    refine HilbPoint.ext (Scheme.IdealSheafData.ext_of_comap_eq _
      (exists_mem_range_bcMap f g 𝓤) fun i ↦ ?_)
    change P'.ideal.comap (bcMap f (𝓤.f i) g _ rfl) =
      (glueIdealHilb 𝓤 g Q hI).comap (bcMap f (𝓤.f i) g _ rfl)
    rw [comap_glueIdealHilb]
    have := cast_eq_of_hilbSch_mk_eq (e i) rfl
    rw [HilbPoint.cast_rfl] at this
    exact congrArg HilbPoint.ideal this

/-- The Hilbert functor `Hilb^d_{X/S}` is a sheaf for the big Zariski topology (the Zariski part
of Stacks, Lemma 44.2.1, Tag 0B95). -/
theorem isSheaf_hilbSch : Presieve.IsSheaf Scheme.zariskiTopology (hilbSch f d) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro T R hR
  obtain ⟨(𝓤 : Scheme.OpenCover T), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hR
  exact isSheafFor_hilbSch_ofArrows f d 𝓤

/-- The Hilbert functor `Hilb^d_{X/S}` as a sheaf for the big Zariski topology. -/
def hilbSheaf : Sheaf Scheme.zariskiTopology.{u} (Type u) where
  obj := hilbSch f d
  property := (isSheaf_iff_isSheaf_of_type _ _).mpr (isSheaf_hilbSch f d)

@[simp]
lemma hilbSheaf_obj : (hilbSheaf f d).obj = hilbSch f d := rfl

end CurvesJacobian
