/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Gluing ideal sheaves along open immersions

Generic lemmas, candidates for upstreaming to Mathlib.

Let `φ i : V i ⟶ Y` be a (possibly infinite) family of open immersions whose ranges cover `Y`.
We show that ideal sheaves on `Y` are determined by their pullbacks along the `φ i`
(`IdealSheafData.ext_of_comap_eq`), and that a family of ideal sheaves `I i` on the `V i`
which agree on the overlaps `V i ×_Y V j` glues to an ideal sheaf on `Y`
(`IdealSheafData.glue`, `IdealSheafData.comap_glue`, `IdealSheafData.exists_comap_eq`).
No quasi-compactness or quasi-separatedness assumption is needed.

We also record an element-wise locality statement for ideal sheaves:
`IdealSheafData.mem_ideal_of_forall_exists_affine`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

section Locality

variable {X : Scheme.{u}}

/-- A section `a` over an affine open `U` restricts into `I` on the basic open `D(r)` iff
`r ^ n * a ∈ I(U)` for some `n`. -/
lemma map_mem_ideal_basicOpen_iff (I : X.IdealSheafData) (U : X.affineOpens) (r a : Γ(X, U)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom a ∈ I.ideal (X.affineBasicOpen r) ↔
      ∃ n : ℕ, r ^ n * a ∈ I.ideal U := by
  have := U.2.isLocalization_basicOpen r
  rw [← I.map_ideal_basicOpen U r]
  change algebraMap Γ(X, U) Γ(X, X.basicOpen r) a ∈
    (I.ideal U).map (algebraMap Γ(X, U) Γ(X, X.basicOpen r)) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, h⟩
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨_, ⟨n, rfl⟩, h⟩

/-- Membership in an ideal sheaf can be checked on basic opens `D(r)` for `r` in a set
spanning the unit ideal. -/
lemma mem_ideal_of_span_eq_top (I : X.IdealSheafData) (U : X.affineOpens) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) (a : Γ(X, U))
    (H : ∀ r ∈ s, (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom a ∈
      I.ideal (X.affineBasicOpen r)) :
    a ∈ I.ideal U :=
  Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs a fun r ↦
    (I.map_mem_ideal_basicOpen_iff U r a).mp (H r r.2)

/-- Element-wise locality of ideal sheaves: a section over an affine open `U` lies in `I(U)`
if every point of `U` has an affine open neighbourhood in `U` on which the restriction of the
section lies in `I`. -/
lemma mem_ideal_of_forall_exists_affine (I : X.IdealSheafData) (U : X.affineOpens)
    (a : Γ(X, U))
    (H : ∀ x ∈ U.1, ∃ (W : X.affineOpens) (h : W ≤ U), x ∈ W.1 ∧
      (X.presheaf.map (homOfLE h).op).hom a ∈ I.ideal W) :
    a ∈ I.ideal U := by
  let s : Set Γ(X, U) := {r | ∃ (W : X.affineOpens) (h : W ≤ U), X.basicOpen r ≤ W.1 ∧
    (X.presheaf.map (homOfLE h).op).hom a ∈ I.ideal W}
  refine I.mem_ideal_of_span_eq_top U s ?_ a ?_
  · rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨W, hWU, hxW, hW⟩ := H x hx
    obtain ⟨r, hrW, hxr⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨x, hxW⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨r, W, hWU, hrW, hW⟩, hxr⟩
  · rintro r ⟨W, hWU, hrW, hW⟩
    have := I.ideal_le_comap_ideal (U := X.affineBasicOpen r) (V := W) hrW hW
    rw [Ideal.mem_comap, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
      at this
    exact this

end Locality

section Glue

variable {Y : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}} (φ : ∀ i, V i ⟶ Y)
  [∀ i, IsOpenImmersion (φ i)]

private lemma inv_hom_apply' {A B : CommRingCat.{u}} (e : A ≅ B) (x : A) :
    e.inv.hom (e.hom.hom x) = x := by
  change (e.hom ≫ e.inv).hom x = x
  simp

private lemma appLE_res_apply {X Z : Scheme.{u}} (g : X ⟶ Z) {U : Z.Opens} {W W' : X.Opens}
    (e : W ≤ g ⁻¹ᵁ U) (i : W' ≤ W) (a : Γ(Z, U)) :
    (X.presheaf.map (homOfLE i).op).hom ((g.appLE U W e).hom a) =
      (g.appLE U W' (i.trans e)).hom a :=
  congr($(g.appLE_map e (homOfLE i).op).hom a)

private lemma res_appLE_apply {X Z : Scheme.{u}} (g : X ⟶ Z) {U U' : Z.Opens} {W : X.Opens}
    (e : W ≤ g ⁻¹ᵁ U) (i : U ≤ U') (a : Γ(Z, U')) :
    (g.appLE U W e).hom ((Z.presheaf.map (homOfLE i).op).hom a) =
      (g.appLE U' W (e.trans (g.preimage_mono i))).hom a :=
  congr($(g.map_appLE e (homOfLE i).op).hom a)

private lemma mem_of_eq' {R : CommRingCat.{u}} {J : Ideal R} {x y : R} (e : x = y) (h : y ∈ J) :
    x ∈ J :=
  e ▸ h

private lemma hom_inv_apply' {A B : CommRingCat.{u}} (e : A ≅ B) (x : B) :
    e.hom.hom (e.inv.hom x) = x := by
  change (e.inv ≫ e.hom).hom x = x
  simp

/-- Ideal sheaves are determined by their pullbacks along a jointly surjective family of
open immersions. -/
theorem ext_of_comap_eq (hφ : ∀ y, ∃ i, y ∈ Set.range (φ i)) {I J : Y.IdealSheafData}
    (h : ∀ i, I.comap (φ i) = J.comap (φ i)) : I = J := by
  refine ext_of_iSup_eq_top (ι := Σ i, (V i).affineOpens)
    (fun p ↦ ⟨φ p.1 ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion _⟩) ?_ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨i, x, rfl⟩ := hφ y
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (V i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨U, hU⟩⟩, ⟨x, hxU, rfl⟩⟩
  · rintro ⟨i, U⟩
    have := congrArg (fun K ↦ K.ideal U) (h i)
    simp only [ideal_comap_of_isOpenImmersion] at this
    exact Ideal.comap_injective_of_surjective _
      (fun y ↦ ⟨((φ i).appIso U).hom.hom y, inv_hom_apply' _ _⟩) this

variable (I : ∀ i, (V i).IdealSheafData)

/-- The ideals of the glued ideal sheaf: a section over an affine open `W` of `Y` belongs to it
iff its restriction to every affine open `U ⊆ φ i ⁻¹ᵁ W` lies in `I i`. -/
def glueIdeal (W : Y.affineOpens) : Ideal Γ(Y, W) :=
  ⨅ (i) (U : (V i).affineOpens) (h : U.1 ≤ φ i ⁻¹ᵁ W.1),
    ((I i).ideal U).comap ((φ i).appLE W U h).hom

omit [∀ i, IsOpenImmersion (φ i)] in
variable {φ I} in
lemma mem_glueIdeal {W : Y.affineOpens} {a : Γ(Y, W)} :
    a ∈ glueIdeal φ I W ↔
      ∀ i (U : (V i).affineOpens) (h : U.1 ≤ φ i ⁻¹ᵁ W.1),
        ((φ i).appLE W U h).hom a ∈ (I i).ideal U := by
  simp [glueIdeal, Submodule.mem_iInf]

/-- Compatibility on overlaps transports membership from one chart to another. -/
lemma appLE_mem_of_image_le
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j)))
    {W : Y.Opens} (s : Γ(Y, W)) {i j : ι} (Ui : (V i).affineOpens) (Uj : (V j).affineOpens)
    (hi : Ui.1 ≤ φ i ⁻¹ᵁ W) (hj : Uj.1 ≤ φ j ⁻¹ᵁ W) (hji : φ j ''ᵁ Uj.1 ≤ φ i ''ᵁ Ui.1)
    (hs : ((φ i).appLE W Ui hi).hom s ∈ (I i).ideal Ui) :
    ((φ j).appLE W Uj hj).hom s ∈ (I j).ideal Uj := by
  set p := pullback.fst (φ i) (φ j)
  set q := pullback.snd (φ i) (φ j)
  have hrange : Uj.1 ≤ q.opensRange := by
    rw [Scheme.Hom.opensRange_pullbackSnd]
    intro x hx
    obtain ⟨y, -, e⟩ := hji ⟨x, hx, rfl⟩
    exact ⟨y, e⟩
  let Q : (pullback (φ i) (φ j)).affineOpens :=
    ⟨q ⁻¹ᵁ Uj.1, Uj.2.preimage_of_isOpenImmersion _ hrange⟩
  have hqQ : q ''ᵁ Q.1 = Uj.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hrange]
  have hpQ : p ''ᵁ Q.1 ≤ Ui.1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hpt : φ i (p x) = φ j (q x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨z, hz, e⟩ := hji ⟨q x, hx, hpt.symm⟩
    have hz' : p x ∈ Ui.1 := (φ i).isOpenEmbedding.injective e ▸ hz
    exact hz'
  -- membership in the pullback of `I i` along `p`
  have h₁ : ((p ≫ φ i).appLE W Q.1 (fun x hx ↦ hi (hpQ ⟨x, hx, rfl⟩))).hom s ∈
      ((I i).comap p).ideal Q := by
    rw [ideal_comap_of_isOpenImmersion, Ideal.mem_comap, ← Scheme.Hom.appLE_comp_appLE
      (e₁ := hpQ.trans hi)
      (e₂ := (p.preimage_image_eq Q.1).ge), CommRingCat.hom_comp, RingHom.comp_apply,
      ← Scheme.Hom.appIso_hom', inv_hom_apply']
    have := (I i).ideal_le_comap_ideal (U := ⟨p ''ᵁ Q.1, Q.2.image_of_isOpenImmersion _⟩)
      (V := Ui) hpQ hs
    rwa [Ideal.mem_comap, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_map] at this
  rw [hI i j] at h₁
  have hcongr : ∀ {f g : pullback (φ i) (φ j) ⟶ Y} (_ : f = g) (e₁ e₂),
      f.appLE W Q.1 e₁ = g.appLE W Q.1 e₂ := by
    rintro _ _ rfl _ _
    rfl
  rw [hcongr pullback.condition _ (fun x hx ↦ hj (hqQ.le ⟨x, hx, rfl⟩)),
    ideal_comap_of_isOpenImmersion, Ideal.mem_comap, ← Scheme.Hom.appLE_comp_appLE
      (e₁ := hqQ.le.trans hj)
      (e₂ := (q.preimage_image_eq Q.1).ge), CommRingCat.hom_comp, RingHom.comp_apply,
      ← Scheme.Hom.appIso_hom', inv_hom_apply'] at h₁
  have := (I j).ideal_le_comap_ideal (U := Uj)
    (V := ⟨q ''ᵁ Q.1, Q.2.image_of_isOpenImmersion _⟩) hqQ.ge h₁
  rwa [Ideal.mem_comap, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    Scheme.Hom.appLE_map] at this


variable {φ I} in
/-- On an affine open `A` inside the image of an affine open `U` of `V i`, membership in
`glueIdeal` is membership in `I i` after pulling back along `φ i`. -/
lemma mem_glueIdeal_iff_of_le_image
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j)))
    {i : ι} (U : (V i).affineOpens) (A : Y.affineOpens) (h₁ : U.1 ≤ φ i ⁻¹ᵁ A.1)
    (h₂ : A.1 ≤ φ i ''ᵁ U.1) (a : Γ(Y, A)) :
    a ∈ glueIdeal φ I A ↔ ((φ i).appLE A U h₁).hom a ∈ (I i).ideal U := by
  refine ⟨fun ha ↦ mem_glueIdeal.mp ha i U h₁, fun ha ↦ mem_glueIdeal.mpr fun j U' h ↦ ?_⟩
  exact appLE_mem_of_image_le φ I hI a U U' h₁ h
    ((((φ j).image_mono h).trans ((φ j).image_preimage_le _)).trans h₂) ha

omit [∀ i, IsOpenImmersion (φ i)] in
variable {φ I} in
/-- Membership in `glueIdeal` is local for basic opens. -/
lemma mem_glueIdeal_of_span_eq_top {W : Y.affineOpens} (s : Set Γ(Y, W))
    (hs : Ideal.span s = ⊤) (a : Γ(Y, W))
    (H : ∀ r ∈ s, (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom a ∈
      glueIdeal φ I (Y.affineBasicOpen r)) :
    a ∈ glueIdeal φ I W := by
  refine mem_glueIdeal.mpr fun i U h ↦ ?_
  refine (I i).mem_ideal_of_span_eq_top U (((φ i).appLE W U h).hom '' s)
    (by rw [← Ideal.map_span, hs, Ideal.map_top]) _ ?_
  rintro _ ⟨r, hr, rfl⟩
  have hle : ((V i).affineBasicOpen (((φ i).appLE W U h).hom r)).1 ≤
      φ i ⁻¹ᵁ (Y.affineBasicOpen r).1 := by
    simp only [affineBasicOpen_coe]
    rw [Scheme.basicOpen_appLE]
    exact inf_le_right
  exact mem_of_eq' ((appLE_res_apply _ _ _ _).trans (res_appLE_apply _ _ _ _).symm)
    (mem_glueIdeal.mp (H r hr) i _ hle)

omit [∀ i, IsOpenImmersion (φ i)] in
lemma map_glueIdeal_le (W : Y.affineOpens) (f : Γ(Y, W)) :
    (glueIdeal φ I W).map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom ≤
      glueIdeal φ I (Y.affineBasicOpen f) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  refine mem_glueIdeal.mpr fun i U h ↦ ?_
  convert mem_glueIdeal.mp ha i U (h.trans ((φ i).preimage_mono (Y.basicOpen_le f))) using 2
  exact res_appLE_apply _ _ _ _

variable {φ I} in
lemma glueIdeal_basicOpen_le (hφ : ∀ y, ∃ i, y ∈ Set.range (φ i))
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j)))
    (W : Y.affineOpens) (f : Γ(Y, W)) :
    glueIdeal φ I (Y.affineBasicOpen f) ≤
      (glueIdeal φ I W).map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := by
  intro (s : Γ(Y, Y.basicOpen f)) hs
  have := W.2.isLocalization_basicOpen f
  obtain ⟨⟨t, _, ⟨n, rfl⟩⟩, ht⟩ := IsLocalization.surj (Submonoid.powers f) s
  have ht' : s * algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) (f ^ n) =
      algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) t := ht
  suffices ∃ m, f ^ m * t ∈ glueIdeal φ I W by
    obtain ⟨m, hm⟩ := this
    have hu : IsUnit (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) (f ^ (n + m))) :=
      IsLocalization.map_units _ (⟨_, n + m, rfl⟩ : Submonoid.powers f)
    have hs' : s = algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) (f ^ m * t) * ↑hu.unit⁻¹ := by
      rw [eq_comm, Units.mul_inv_eq_iff_eq_mul, IsUnit.unit_spec, pow_add, map_mul, map_mul]
      linear_combination (-algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) (f ^ m)) * ht'
    rw [hs']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hm)
  -- the sections `g` with `D(g)` inside the range of some `φ i`
  let S : Set Γ(Y, W) := {g | ∃ i, (Y.basicOpen g : Set Y) ⊆ Set.range (φ i)}
  have hS : Ideal.span S = ⊤ := by
    rw [← W.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := hφ x
    obtain ⟨g, hg, hxg⟩ := W.2.exists_basicOpen_le (V := (φ i).opensRange) ⟨x, hi⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨g, i, hg⟩, hxg⟩
  obtain ⟨T, hTS, hT⟩ := (Ideal.span_eq_top_iff_finite S).mp hS
  have hloc : ∀ g : T, ∃ m, (Y.presheaf.map (homOfLE (Y.basicOpen_le g.1)).op).hom
      (f ^ m * t) ∈ glueIdeal φ I (Y.affineBasicOpen g.1) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, hi⟩ := hTS hg
    let A := Y.affineBasicOpen g
    have hA : A.1 ≤ (φ i).opensRange := hi
    let U : (V i).affineOpens := ⟨φ i ⁻¹ᵁ A.1, A.2.preimage_of_isOpenImmersion _ hA⟩
    have hUW : U.1 ≤ φ i ⁻¹ᵁ W.1 := (φ i).preimage_mono (Y.basicOpen_le g)
    let f' := ((φ i).appLE W U hUW).hom f
    let t' := ((φ i).appLE W U hUW).hom t
    have hD : ((V i).affineBasicOpen f').1 ≤ φ i ⁻¹ᵁ (Y.affineBasicOpen f).1 := by
      simp only [affineBasicOpen_coe, f']
      rw [Scheme.basicOpen_appLE]
      exact inf_le_right
    have h1 := mem_glueIdeal.mp hs i _ hD
    have h3 : ((φ i).appLE _ _ hD).hom (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen f) t) ∈
        (I i).ideal ((V i).affineBasicOpen f') :=
      mem_of_eq' ((congrArg ((φ i).appLE _ _ hD).hom ht'.symm).trans (map_mul _ _ _))
        (Ideal.mul_mem_right _ _ h1)
    have h2 : ((V i).presheaf.map (homOfLE ((V i).basicOpen_le f')).op).hom t' ∈
        (I i).ideal ((V i).affineBasicOpen f') :=
      mem_of_eq' ((appLE_res_apply _ _ _ _).trans (res_appLE_apply _ _ _ _).symm) h3
    obtain ⟨m, hm⟩ := ((I i).map_mem_ideal_basicOpen_iff U f' t').mp h2
    refine ⟨m, (mem_glueIdeal_iff_of_le_image hI U A le_rfl ?_ _).mpr ?_⟩
    · rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact le_inf hA le_rfl
    · convert hm using 2
      exact (res_appLE_apply _ _ _ _).trans (by rw [map_mul, map_pow])
  choose m hm using hloc
  refine ⟨Finset.univ.sup m, mem_glueIdeal_of_span_eq_top (T : Set Γ(Y, W)) hT _ ?_⟩
  intro g hg
  have hle : m ⟨g, hg⟩ ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ _)
  rw [← pow_sub_mul_pow f hle, mul_assoc, map_mul]
  exact Ideal.mul_mem_left _ _ (hm ⟨g, hg⟩)

/-- The ideal sheaf on `Y` glued from compatible ideal sheaves `I i` on the members `V i` of a
jointly surjective family of open immersions. -/
noncomputable def glue (hφ : ∀ y, ∃ i, y ∈ Set.range (φ i))
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j))) : Y.IdealSheafData where
  ideal := glueIdeal φ I
  map_ideal_basicOpen W f :=
    (map_glueIdeal_le φ I W f).antisymm (glueIdeal_basicOpen_le hφ hI W f)

lemma ideal_glue (hφ : ∀ y, ∃ i, y ∈ Set.range (φ i))
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j))) :
    (glue φ I hφ hI).ideal = glueIdeal φ I := rfl

theorem comap_glue (hφ : ∀ y, ∃ i, y ∈ Set.range (φ i))
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j))) (i : ι) :
    (glue φ I hφ hI).comap (φ i) = I i := by
  ext U x
  rw [ideal_comap_of_isOpenImmersion, Ideal.mem_comap, ideal_glue,
    mem_glueIdeal_iff_of_le_image hI U _ ((φ i).preimage_image_eq U.1).ge le_rfl,
    ← Scheme.Hom.appIso_hom', hom_inv_apply']

/-- Compatible ideal sheaves on a jointly surjective family of open immersions glue. -/
theorem exists_comap_eq (hφ : ∀ y, ∃ i, y ∈ Set.range (φ i))
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j))) :
    ∃ J : Y.IdealSheafData, ∀ i, J.comap (φ i) = I i :=
  ⟨glue φ I hφ hI, comap_glue φ I hφ hI⟩

/-- Compatible ideal sheaves on a jointly surjective family of open immersions glue uniquely. -/
theorem existsUnique_comap_eq (hφ : ∀ y, ∃ i, y ∈ Set.range (φ i))
    (hI : ∀ i j, (I i).comap (pullback.fst (φ i) (φ j)) =
      (I j).comap (pullback.snd (φ i) (φ j))) :
    ∃! J : Y.IdealSheafData, ∀ i, J.comap (φ i) = I i :=
  ⟨glue φ I hφ hI, comap_glue φ I hφ hI, fun _ hJ ↦
    ext_of_comap_eq φ hφ fun i ↦ (hJ i).trans (comap_glue φ I hφ hI i).symm⟩

end Glue

end AlgebraicGeometry.Scheme.IdealSheafData
