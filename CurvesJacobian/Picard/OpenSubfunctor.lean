/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Open subfunctors cut out by local predicates, checked on affine schemes

This file is generic (it does not depend on anything specific to this project) and is a
candidate for upstreaming to Mathlib.

Let `F` be a `Type u`-valued sheaf on `Scheme.{u}` for the Zariski topology. We consider
predicates `p T : F(T) → Prop` which are stable under pullback and Zariski-local
(`IsLocalPredicate`). Such a predicate defines a subfunctor of `F`. We give criteria, which only
have to be checked on *affine* test schemes, for

* this subfunctor to be an open subfunctor (`exists_opens_of_isAffine`),
* this subfunctor to be represented by a scheme `Y` with universal element `ξ`
  (`injective_of_isAffine`, `iff_exists_of_isAffine`),
* in this case, `yonedaEquiv.symm ξ : yoneda.obj Y ⟶ F` is a relatively representable open
  immersion (`isOpenImmersion_presheaf`, the pullback along `x : yoneda.obj T ⟶ F` being given
  by an open `U ⊆ T`, see `isPullback_yoneda`),
* a family of such morphisms to be locally surjective (`isLocallySurjective_sigmaDesc`),

and we combine everything to a representability criterion `isRepresentable_of_isAffine`, which
is a convenient way to apply `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`
(Stacks, Tag 01JJ).
-/

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.OpenSubfunctor

variable {F : Sheaf Scheme.zariskiTopology.{u} (Type u)}

/-- Sections of a Zariski sheaf agreeing on an open cover are equal. -/
lemma ext_of_openCover {T : Scheme.{u}} (𝒰 : T.OpenCover) {x y : F.obj.obj (op T)}
    (h : ∀ i, F.obj.map (𝒰.f i).op x = F.obj.map (𝒰.f i).op y) : x = y := by
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _
    𝒰.mem_grothendieckTopology).isSeparatedFor.ext ?_
  rintro V g ⟨W, a, b, ⟨i⟩, rfl⟩
  simp only [op_comp, Functor.map_comp_apply, h i]

variable (F) in
/-- A predicate on the sections of `F` which is stable under pullback and Zariski-local. -/
structure IsLocalPredicate (p : ∀ T : Scheme.{u}, F.obj.obj (op T) → Prop) : Prop where
  map {T T' : Scheme.{u}} (h : T' ⟶ T) (x : F.obj.obj (op T)) : p T x →
    p T' (F.obj.map h.op x)
  of_forall {T : Scheme.{u}} (x : F.obj.obj (op T)) :
    (∀ t : T, ∃ U : T.Opens, t ∈ U ∧ p U (F.obj.map U.ι.op x)) → p T x

variable {p : ∀ T : Scheme.{u}, F.obj.obj (op T) → Prop}

/-- If the subfunctor of `F` cut out by a local predicate `p` is open when tested on affine
schemes, then it is open: for every `x : F(T)` there is an open `U ⊆ T` such that `p` holds
for the pullback of `x` along `h : T' ⟶ T` iff `h` factors through `U`. -/
theorem exists_opens_of_isAffine (hp : IsLocalPredicate F p)
    (H : ∀ (T : Scheme.{u}) [IsAffine T] (x : F.obj.obj (op T)), ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        p T' (F.obj.map h.op x) ↔ Set.range h ⊆ U)
    {T : Scheme.{u}} (x : F.obj.obj (op T)) :
    ∃ U : T.Opens, ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
      p T' (F.obj.map h.op x) ↔ Set.range h ⊆ U := by
  let S : Set T := {t | ∃ (V : Scheme.{u}) (f : V ⟶ T), IsOpenImmersion f ∧ t ∈ Set.range f ∧
    p V (F.obj.map f.op x)}
  have hS : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro t ⟨V, f, hf, ht, hpf⟩
    exact ⟨Set.range f, fun s hs ↦ ⟨V, f, hf, hs, hpf⟩, f.isOpenEmbedding.isOpen_range, ht⟩
  refine ⟨⟨S, hS⟩, fun T' h ↦ ⟨fun hph ↦ ?_, fun hh ↦ ?_⟩⟩
  · rintro _ ⟨t', rfl⟩
    obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := h t')
      (U := ⊤) trivial
    have : IsAffine W := hW
    obtain ⟨UW, hUW⟩ := H W (F.obj.map W.ι.op x)
    obtain ⟨V', hV', htV', hV'le⟩ := exists_isAffineOpen_mem_and_subset (x := t')
      (U := h ⁻¹ᵁ W) hsW
    have : IsAffine V' := hV'
    let h' : (V' : Scheme.{u}) ⟶ W := T'.homOfLE hV'le ≫ (h ∣_ W)
    have hh' : h' ≫ W.ι = V'.ι ≫ h := by simp [h']
    have hrange := (hUW V' h').1 (by
      rw [← Functor.map_comp_apply, ← op_comp, hh', op_comp,
        Functor.map_comp_apply]
      exact hp.map _ _ hph)
    obtain ⟨A, hA, hwA, hAle⟩ := exists_isAffineOpen_mem_and_subset (x := h' ⟨t', htV'⟩)
      (U := UW) (hrange ⟨_, rfl⟩)
    have : IsAffine A := hA
    refine ⟨A, A.ι ≫ W.ι, inferInstance, ⟨⟨_, hwA⟩, ?_⟩, ?_⟩
    · change W.ι (h' ⟨t', htV'⟩) = h t'
      rw [← Scheme.Hom.comp_apply, hh']
      rfl
    · rw [op_comp, Functor.map_comp_apply]
      exact (hUW A A.ι).2 (by rw [Scheme.Opens.range_ι]; exact hAle)
  · refine hp.of_forall _ fun t' ↦ ?_
    obtain ⟨V, f, hf, ⟨v, hv⟩, hpf⟩ := hh ⟨t', rfl⟩
    refine ⟨h ⁻¹ᵁ f.opensRange, ⟨v, hv⟩, ?_⟩
    have hle : Set.range ((h ⁻¹ᵁ f.opensRange).ι ≫ h) ⊆ Set.range f := by
      rintro _ ⟨s, rfl⟩
      exact s.2
    rw [← Functor.map_comp_apply, ← op_comp, ← IsOpenImmersion.lift_fac f _ hle,
      op_comp, Functor.map_comp_apply]
    exact hp.map _ _ hpf

section Representable

variable {Y : Scheme.{u}} (ξ : F.obj.obj (op Y))

/-- Injectivity of `a ↦ ξ|_a` on all schemes follows from injectivity on affine schemes. -/
theorem injective_of_isAffine
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y ↦ F.obj.map a.op ξ)
    (T : Scheme.{u}) : Function.Injective fun a : T ⟶ Y ↦ F.obj.map a.op ξ := by
  intro a b hab
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
  have : IsAffine U := hU
  refine ⟨U, htU, hinj U ?_⟩
  simp only [op_comp, Functor.map_comp_apply]
  exact congrArg _ hab

/-- If `ξ ∈ F(Y)` represents the subfunctor cut out by `p` on affine schemes, then it does so on
all schemes. (Injectivity is `injective_of_isAffine`.) -/
theorem iff_exists_of_isAffine (hp : IsLocalPredicate F p)
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y ↦ F.obj.map a.op ξ)
    (hrange : ∀ (T : Scheme.{u}) [IsAffine T] (x : F.obj.obj (op T)),
      p T x ↔ ∃ a : T ⟶ Y, F.obj.map a.op ξ = x)
    {T : Scheme.{u}} (x : F.obj.obj (op T)) :
    p T x ↔ ∃ a : T ⟶ Y, F.obj.map a.op ξ = x := by
  constructor
  · intro hx
    let 𝒰 := T.affineCover
    choose a ha using fun i ↦ (hrange (𝒰.X i) (F.obj.map (𝒰.f i).op x)).1 (hp.map _ _ hx)
    refine ⟨𝒰.glueMorphisms a fun i j ↦ injective_of_isAffine ξ hinj _ ?_, ?_⟩
    · change F.obj.map (pullback.fst _ _ ≫ a i).op ξ = F.obj.map (pullback.snd _ _ ≫ a j).op ξ
      rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ha, ha,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
        pullback.condition]
    · refine ext_of_openCover 𝒰 fun i ↦ ?_
      rw [← Functor.map_comp_apply, ← op_comp, Scheme.Cover.ι_glueMorphisms, ha]
  · rintro ⟨a, rfl⟩
    refine hp.of_forall _ fun t ↦ ?_
    obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
    have : IsAffine U := hU
    refine ⟨U, htU, (hrange U _).2 ⟨U.ι ≫ a, ?_⟩⟩
    rw [op_comp, Functor.map_comp_apply]

/-- The pullback of `yoneda.obj Y ⟶ F` (given by `ξ`) along `yoneda.obj T ⟶ F` (given by `x`)
is the open subscheme `U ⊆ T`, provided `U` is the locus where `x` comes from `ξ`. -/
theorem isPullback_yoneda
    (hinj : ∀ T : Scheme.{u}, Function.Injective fun a : T ⟶ Y ↦ F.obj.map a.op ξ)
    {T : Scheme.{u}} (x : F.obj.obj (op T)) (U : T.Opens)
    (hU : ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
      (∃ b : T' ⟶ Y, F.obj.map b.op ξ = F.obj.map h.op x) → Set.range h ⊆ U)
    (a : (U : Scheme.{u}) ⟶ Y) (ha : F.obj.map a.op ξ = F.obj.map U.ι.op x) :
    IsPullback (yoneda.map a) (yoneda.map U.ι) (yonedaEquiv.symm ξ) (yonedaEquiv.symm x) := by
  have w : yoneda.map a ≫ yonedaEquiv.symm ξ = yoneda.map U.ι ≫ yonedaEquiv.symm x := by
    rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, ha]
  refine IsPullback.of_forall_isPullback_app fun T' ↦ ?_
  refine (Types.isPullback_iff _ _ _ _).2 ⟨congrArg (fun φ ↦ NatTrans.app φ T') w,
    fun b₁ b₂ hb ↦ ?_, fun b c hbc ↦ ?_⟩
  · exact (cancel_mono U.ι).1 hb.2
  · change F.obj.map b.op ξ = F.obj.map c.op x at hbc
    have hc := hU _ c ⟨b, hbc⟩
    refine ⟨IsOpenImmersion.lift U.ι c (by rwa [Scheme.Opens.range_ι]), hinj _ ?_,
      IsOpenImmersion.lift_fac _ _ _⟩
    change F.obj.map (_ ≫ a).op ξ = F.obj.map b.op ξ
    rw [op_comp, Functor.map_comp_apply, ha, ← Functor.map_comp_apply, ← op_comp,
      IsOpenImmersion.lift_fac, hbc]

/-- If `ξ ∈ F(Y)` represents an open subfunctor of `F`, then `yoneda.obj Y ⟶ F` is a relatively
representable open immersion. -/
theorem isOpenImmersion_presheaf
    (hinj : ∀ T : Scheme.{u}, Function.Injective fun a : T ⟶ Y ↦ F.obj.map a.op ξ)
    (hU : ∀ (T : Scheme.{u}) (x : F.obj.obj (op T)), ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        (∃ b : T' ⟶ Y, F.obj.map b.op ξ = F.obj.map h.op x) ↔ Set.range h ⊆ U) :
    IsOpenImmersion.presheaf (yonedaEquiv.symm ξ) := by
  refine MorphismProperty.relative.of_exists fun T g ↦ ?_
  obtain ⟨x, rfl⟩ := yonedaEquiv.symm.surjective g
  obtain ⟨U, hU⟩ := hU T x
  obtain ⟨a, ha⟩ := (hU U U.ι).2 (by rw [Scheme.Opens.range_ι])
  exact ⟨U, yoneda.map a, U.ι,
    isPullback_yoneda ξ hinj x U (fun T' h ↦ (hU T' h).1) a ha, inferInstance⟩

end Representable

/-- A family of maps `yoneda.obj (Y i) ⟶ F` (given by `ξ i`) is locally surjective as soon as
every section of `F` locally comes from one of the `ξ i`. -/
theorem isLocallySurjective_sigmaDesc {ι : Type u} {Y : ι → Scheme.{u}}
    (ξ : ∀ i, F.obj.obj (op (Y i)))
    (H : ∀ (T : Scheme.{u}) (x : F.obj.obj (op T)) (t : T), ∃ (i : ι) (V : Scheme.{u})
      (f : V ⟶ T), IsOpenImmersion f ∧ t ∈ Set.range f ∧
        ∃ a : V ⟶ Y i, F.obj.map a.op (ξ i) = F.obj.map f.op x) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i ↦ yonedaEquiv.symm (ξ i)) := by
  let G : ι → (Scheme.{u}ᵒᵖ ⥤ Type u) := fun j ↦ yoneda.obj (Y j)
  constructor
  intro T x
  choose i V f hf ht a ha using H T x
  let 𝒰 : T.OpenCover := Cover.mkOfCovers T V f (fun t ↦ ⟨t, ht t⟩) hf
  refine Scheme.zariskiTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro W g ⟨t⟩
  refine ⟨(Sigma.ι G (i t)).app _ (a t), ?_⟩
  rw [← NatTrans.comp_app_apply, Sigma.ι_desc, yonedaEquiv_symm_app_apply]
  exact ha t

/-- **Representability criterion checked on affine schemes.**

Let `F` be a Zariski sheaf on schemes and `p i` (for `i : ι`) be local predicates on `F`. Assume
that on affine test schemes:
* `p i` cuts out an open subfunctor (`hopen`),
* this subfunctor is represented by `Y i` with universal element `ξ i` (`hinj`, `hrange`),
* these open subfunctors cover `F` (`hcov`).

Then `F` is representable. -/
theorem isRepresentable_of_isAffine {ι : Type u}
    {p : ι → ∀ T : Scheme.{u}, F.obj.obj (op T) → Prop} (hp : ∀ i, IsLocalPredicate F (p i))
    (hopen : ∀ (i : ι) (T : Scheme.{u}) [IsAffine T] (x : F.obj.obj (op T)), ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        p i T' (F.obj.map h.op x) ↔ Set.range h ⊆ U)
    {Y : ι → Scheme.{u}} (ξ : ∀ i, F.obj.obj (op (Y i)))
    (hinj : ∀ (i : ι) (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y i ↦ F.obj.map a.op (ξ i))
    (hrange : ∀ (i : ι) (T : Scheme.{u}) [IsAffine T] (x : F.obj.obj (op T)),
      p i T x ↔ ∃ a : T ⟶ Y i, F.obj.map a.op (ξ i) = x)
    (hcov : ∀ (T : Scheme.{u}) [IsAffine T] (x : F.obj.obj (op T)) (t : T), ∃ (i : ι)
      (U : T.Opens), (∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        p i T' (F.obj.map h.op x) ↔ Set.range h ⊆ U) ∧ t ∈ U) :
    F.obj.IsRepresentable := by
  have hinj' (i : ι) := injective_of_isAffine (ξ i) (hinj i)
  have hrange' (i : ι) {T : Scheme.{u}} (x : F.obj.obj (op T)) :=
    iff_exists_of_isAffine (ξ i) (hp i) (hinj i) (hrange i) x
  have hf (i : ι) : IsOpenImmersion.presheaf (yonedaEquiv.symm (ξ i)) := by
    refine isOpenImmersion_presheaf (ξ i) (hinj' i) fun T x ↦ ?_
    obtain ⟨U, hU⟩ := exists_opens_of_isAffine (hp i) (hopen i) x
    exact ⟨U, fun T' h ↦ (hrange' i _).symm.trans (hU T' h)⟩
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i ↦ yonedaEquiv.symm (ξ i)) := by
    refine isLocallySurjective_sigmaDesc ξ fun T x t ↦ ?_
    obtain ⟨W, hW, htW, -⟩ := exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
    have : IsAffine W := hW
    obtain ⟨i, U, hU, htU⟩ := hcov W (F.obj.map W.ι.op x) ⟨t, htW⟩
    obtain ⟨A, hA, htA, hAU⟩ := exists_isAffineOpen_mem_and_subset htU
    have : IsAffine A := hA
    obtain ⟨a, ha⟩ := (hrange' i _).1 ((hU A A.ι).2 (by rw [Scheme.Opens.range_ι]; exact hAU))
    refine ⟨i, A, A.ι ≫ W.ι, inferInstance, ⟨⟨_, htA⟩, rfl⟩, a, ?_⟩
    rw [ha, op_comp, Functor.map_comp_apply]
  exact LocalRepresentability.isRepresentable hf

end AlgebraicGeometry.Scheme.OpenSubfunctor
