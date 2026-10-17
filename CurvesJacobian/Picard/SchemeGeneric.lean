/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Generic lemmas on schemes

Generic lemmas, candidates for upstreaming to Mathlib. Nothing here is specific to this
project.

* `CategoryTheory.IsPullback.range_fst_eq_preimage`: in a pullback square of schemes, the
  range of the top map is the preimage of the range of the bottom map.
* `AlgebraicGeometry.isIso_pullbackSnd_of_range_subset`: the base change of an open immersion
  `m` along a morphism whose range lies in the range of `m` is an isomorphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.ker_comap_subschemeι_comp` and
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_ker_comp_of_mono`: restricting ideal sheaves
  to an open subscheme containing their support, and extending them back.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_comap_inv`,
  `AlgebraicGeometry.Scheme.Hom.ker_subschemeι_eq`: small API lemmas.
* `AlgebraicGeometry.isClosedImmersion_of_universallyClosed_comp`: a preimmersion which becomes
  universally closed after composing with a separated morphism is a closed immersion.
* `PrimeSpectrum.exists_basicOpen_of_finite` (prime avoidance) and
  `AlgebraicGeometry.exists_isAffineOpen_of_finite`: a finite set of points of an affine open
  `U` contained in an open `W` lies in an affine open contained in `U ∩ W`.
* `CategoryTheory.Functor.exists_univ_of_restrict_of_univ`,
  `CategoryTheory.Functor.exists_univ_of_restrict` and
  `CategoryTheory.Functor.isRepresentable_of_univ`: transporting representability along a
  natural bijection between a (subfunctor of a) representable functor and a subfunctor.
-/

open CategoryTheory Limits Opposite

universe u v w u₁

/-- Prime avoidance, topologically: a finite set `E` of points of `Spec R` contained in an open
`W` is contained in a basic open `D(r) ⊆ W`. -/
lemma PrimeSpectrum.exists_basicOpen_of_finite {R : Type*} [CommRing R]
    {E : Set (PrimeSpectrum R)} (hE : E.Finite) {W : Set (PrimeSpectrum R)} (hW : IsOpen W)
    (hEW : E ⊆ W) :
    ∃ r : R, E ⊆ PrimeSpectrum.basicOpen r ∧ (PrimeSpectrum.basicOpen r : Set _) ⊆ W := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, Set.empty_subset _, by simp⟩
  set I := PrimeSpectrum.vanishingIdeal Wᶜ
  have hI : ¬ ((I : Set R) ⊆ ⋃ p ∈ E, (p.asIdeal : Set R)) := by
    rw [Ideal.subset_union_prime_finite hE (f := fun p ↦ p.asIdeal) a a
      fun p _ _ _ ↦ p.isPrime]
    rintro ⟨p, hp, hle⟩
    have : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := (PrimeSpectrum.mem_zeroLocus p _).2 hle
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hW.isClosed_compl.closure_eq] at this
    exact this (hEW hp)
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.1 hI
  refine ⟨r, fun p hp ↦ (PrimeSpectrum.mem_basicOpen _ _).2 fun hrp ↦
    hr (Set.mem_biUnion hp hrp), fun q hq ↦ by_contra fun hqW ↦ ?_⟩
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hq
    ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hrI q hqW)

namespace AlgebraicGeometry

variable {P X Y Z : Scheme.{u}}

/-- In a pullback square of schemes, the range of the top map is the preimage of the range of
the bottom map. -/
lemma _root_.CategoryTheory.IsPullback.range_fst_eq_preimage {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨snd p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz]⟩

/-- The base change of an open immersion `m` along a morphism whose range lies in the range
of `m` is an isomorphism. -/
lemma isIso_pullbackSnd_of_range_subset (m : X ⟶ Y) [IsOpenImmersion m] (i : Z ⟶ Y)
    (hi : Set.range i ⊆ Set.range m) : IsIso (pullback.snd m i) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  rw [Scheme.Hom.opensRange_pullbackSnd, eq_top_iff]
  intro z _
  exact hi ⟨z, rfl⟩

/-- A preimmersion which becomes universally closed after composing with a separated morphism
is a closed immersion. -/
lemma isClosedImmersion_of_universallyClosed_comp (i : Z ⟶ X) (q : X ⟶ Y) [IsPreimmersion i]
    [IsSeparated q] [UniversallyClosed (i ≫ q)] : IsClosedImmersion i := by
  have : UniversallyClosed i := .of_comp_of_isSeparated i q
  exact .of_isPreimmersion i i.isClosedMap.isClosed_range

/-- For a closed immersion `i`, the closed subscheme cut out by the kernel of `i` is `i` up to
the isomorphism `i.toImage`. -/
lemma Scheme.Hom.ker_subschemeι_eq (i : Z ⟶ X) [IsClosedImmersion i] :
    i.ker.subschemeι = inv i.toImage ≫ i :=
  ((IsIso.inv_comp_eq _).mpr i.toImage_imageι.symm).symm

namespace Scheme.IdealSheafData

/-- Pulling back an ideal sheaf along an isomorphism and then along its inverse gives the
original ideal sheaf. -/
lemma comap_comap_inv (J : Y.IdealSheafData) (φ : X ⟶ Y) [IsIso φ] :
    (J.comap φ).comap (inv φ) = J := by
  rw [← comap_comp, IsIso.inv_hom_id, comap_id]

lemma comap_injective_of_isIso (φ : X ⟶ Y) [IsIso φ] :
    Function.Injective fun J : Y.IdealSheafData ↦ J.comap φ := fun J K h ↦ by
  rw [← comap_comap_inv J φ, ← comap_comap_inv K φ]
  exact congrArg (fun L : X.IdealSheafData ↦ L.comap (inv φ)) h

/-- The closed subscheme cut out by the pullback of `J` to `X` along `m`, mapped to `Y`. -/
lemma comap_subschemeι_comp (m : X ⟶ Y) (J : Y.IdealSheafData) :
    (J.comap m).subschemeι ≫ m =
      (J.comapIso m).hom ≫ pullback.snd m J.subschemeι ≫ J.subschemeι := by
  rw [← J.comapIso_hom_fst m, Category.assoc, pullback.condition]

/-- If the support of `J` lies in the range of the open immersion `m`, then `J` is the kernel
of the closed subscheme cut out by its pullback along `m`, mapped to `Y`. -/
lemma ker_comap_subschemeι_comp (m : X ⟶ Y) [IsOpenImmersion m] (J : Y.IdealSheafData)
    (hJ : Set.range J.subschemeι ⊆ Set.range m) :
    ((J.comap m).subschemeι ≫ m).ker = J := by
  have := isIso_pullbackSnd_of_range_subset m _ hJ
  rw [comap_subschemeι_comp, ← Category.assoc, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

/-- If `i ≫ m` is a closed immersion and `m` is a monomorphism, then the pullback of the kernel
of `i ≫ m` along `m` is the kernel of `i`. -/
lemma comap_ker_comp_of_mono (i : Z ⟶ X) (m : X ⟶ Y) [Mono m] [IsClosedImmersion (i ≫ m)] :
    (i ≫ m).ker.comap m = i.ker := by
  rw [← ker_fst_of_isClosedImmersion]
  have e : pullback.fst m (i ≫ m) = pullback.snd m (i ≫ m) ≫ i := by
    rw [← cancel_mono m, Category.assoc, pullback.condition]
  rw [e, Scheme.Hom.ker_comp_of_isIso]

end Scheme.IdealSheafData

/-- A finite set `E` of points of an affine open `U` which is contained in an open `W` lies in
an affine open (a basic open of `U`) contained in `U ∩ W`. -/
lemma exists_isAffineOpen_of_finite {U : X.Opens} (hU : IsAffineOpen U) (W : X.Opens)
    {E : Set X} (hE : E.Finite) (hEU : E ⊆ U) (hEW : E ⊆ W) :
    ∃ U' : X.Opens, IsAffineOpen U' ∧ E ⊆ U' ∧ U' ≤ U ∧ U' ≤ W := by
  obtain ⟨r, hr₁, hr₂⟩ := PrimeSpectrum.exists_basicOpen_of_finite (R := Γ(X, U))
    (E := hU.fromSpec ⁻¹' E) (hE.preimage hU.fromSpec.isOpenEmbedding.injective.injOn)
    (hU.fromSpec ⁻¹ᵁ W).isOpen (Set.preimage_mono hEW)
  refine ⟨X.basicOpen r, hU.basicOpen r, fun x hx ↦ ?_, X.basicOpen_le r, fun x hx ↦ ?_⟩
  · obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hEU hx
    have : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hr₁ hx
    exact this
  · obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact X.basicOpen_le r hx
    have : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r := hx
    rw [hU.fromSpec_preimage_basicOpen] at this
    exact hr₂ this

end AlgebraicGeometry

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v} C]

/-- Let `F, G : Cᵒᵖ ⥤ Type w`, `p` a pullback-stable predicate on the sections of `F`, and `Φ`
a natural bijection from the sections of `F` satisfying `p` to the sections of `G`. If the
sections of `G` satisfying `q` are represented by `η ∈ G(Y)`, then the sections `x` of `F` with
`p x` and `q (Φ x)` are represented by some `ξ ∈ F(Y)`. -/
theorem exists_univ_of_restrict_of_univ {F G : Cᵒᵖ ⥤ Type w}
    (p : ∀ T : C, F.obj (op T) → Prop)
    (hpmap : ∀ {T T' : C} (h : T' ⟶ T) (x : F.obj (op T)), p T x → p T' (F.map h.op x))
    (Φ : ∀ (T : C) (x : F.obj (op T)), p T x → G.obj (op T))
    (hnat : ∀ {T T' : C} (h : T' ⟶ T) (x : F.obj (op T)) (hx : p T x),
      Φ T' (F.map h.op x) (hpmap h x hx) = G.map h.op (Φ T x hx))
    (hinj : ∀ (T : C) (x y : F.obj (op T)) (hx : p T x) (hy : p T y), Φ T x hx = Φ T y hy →
      x = y)
    (hsurj : ∀ (T : C) (z : G.obj (op T)), ∃ (x : F.obj (op T)) (hx : p T x), Φ T x hx = z)
    (q : ∀ T : C, G.obj (op T) → Prop) {Y : C} (η : G.obj (op Y))
    (hηinj : ∀ T : C, Function.Injective fun a : T ⟶ Y ↦ G.map a.op η)
    (hq : ∀ (T : C) (z : G.obj (op T)), q T z ↔ ∃ a : T ⟶ Y, G.map a.op η = z) :
    ∃ ξ : F.obj (op Y), (∀ T : C, Function.Injective fun a : T ⟶ Y ↦ F.map a.op ξ) ∧
      ∀ (T : C) (x : F.obj (op T)),
        (∃ hx : p T x, q T (Φ T x hx)) ↔ ∃ a : T ⟶ Y, F.map a.op ξ = x := by
  obtain ⟨ξ, hξ, hΦξ⟩ := hsurj Y η
  have key : ∀ (T : C) (a : T ⟶ Y), Φ T (F.map a.op ξ) (hpmap a ξ hξ) = G.map a.op η := by
    intro T a
    rw [hnat a ξ hξ, hΦξ]
  have hc : ∀ (T : C) (x y : F.obj (op T)) (h : x = y) (hx : p T x) (hy : p T y),
      Φ T x hx = Φ T y hy := by
    rintro T x _ rfl _ _
    rfl
  refine ⟨ξ, fun T a b hab ↦ hηinj T ?_, fun T x ↦ ⟨?_, ?_⟩⟩
  · change G.map a.op η = G.map b.op η
    rw [← key, ← key]
    exact hc T _ _ hab _ _
  · rintro ⟨hx, hqx⟩
    obtain ⟨a, ha⟩ := (hq T _).1 hqx
    exact ⟨a, hinj _ _ _ (hpmap a ξ hξ) hx (by rw [key, ha])⟩
  · rintro ⟨a, rfl⟩
    exact ⟨hpmap a ξ hξ, by rw [key]; exact (hq T _).2 ⟨a, rfl⟩⟩

/-- Let `F, G : Cᵒᵖ ⥤ Type w` with `G` representable, `p` a pullback-stable predicate on the
sections of `F`, and `Φ` a natural bijection from the sections of `F` satisfying `p` to the
sections of `G`. Then there is `ξ ∈ F(Y)` such that `a ↦ F.map a ξ` is injective with image
the sections satisfying `p`. -/
theorem exists_univ_of_restrict {F G : Cᵒᵖ ⥤ Type w} [G.IsRepresentable]
    (p : ∀ T : C, F.obj (op T) → Prop)
    (hpmap : ∀ {T T' : C} (h : T' ⟶ T) (x : F.obj (op T)), p T x → p T' (F.map h.op x))
    (Φ : ∀ (T : C) (x : F.obj (op T)), p T x → G.obj (op T))
    (hnat : ∀ {T T' : C} (h : T' ⟶ T) (x : F.obj (op T)) (hx : p T x),
      Φ T' (F.map h.op x) (hpmap h x hx) = G.map h.op (Φ T x hx))
    (hinj : ∀ (T : C) (x y : F.obj (op T)) (hx : p T x) (hy : p T y), Φ T x hx = Φ T y hy →
      x = y)
    (hsurj : ∀ (T : C) (z : G.obj (op T)), ∃ (x : F.obj (op T)) (hx : p T x), Φ T x hx = z) :
    ∃ (Y : C) (ξ : F.obj (op Y)), (∀ T : C, Function.Injective fun a : T ⟶ Y ↦ F.map a.op ξ) ∧
      ∀ (T : C) (x : F.obj (op T)), p T x ↔ ∃ a : T ⟶ Y, F.map a.op ξ = x := by
  obtain ⟨Y, ⟨e⟩⟩ := ‹G.IsRepresentable›.has_representation
  obtain ⟨ξ, hξ, hΦξ⟩ := hsurj Y (e.homEquiv (𝟙 Y))
  have key : ∀ (T : C) (a : T ⟶ Y), Φ T (F.map a.op ξ) (hpmap a ξ hξ) = e.homEquiv a := by
    intro T a
    rw [hnat a ξ hξ, hΦξ, ← e.homEquiv_eq]
  have hc : ∀ (T : C) (x y : F.obj (op T)) (h : x = y) (hx : p T x) (hy : p T y),
      Φ T x hx = Φ T y hy := by
    rintro T x _ rfl _ _
    rfl
  refine ⟨Y, ξ, fun T a b hab ↦ e.homEquiv.injective ?_, fun T x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · rw [← key, ← key]
    exact hc T _ _ hab _ _
  · obtain ⟨a, ha⟩ := e.homEquiv.surjective (Φ T x hx)
    exact ⟨a, hinj _ _ _ (hpmap a ξ hξ) hx (by rw [key, ha])⟩
  · rintro ⟨a, rfl⟩
    exact hpmap a ξ hξ

/-- A functor `F` with a section `ξ ∈ F(Y)` such that `a ↦ F.map a ξ` is bijective on all
objects is representable. -/
theorem isRepresentable_of_univ {F : Cᵒᵖ ⥤ Type w} {Y : C} (ξ : F.obj (op Y))
    (hinj : ∀ T : C, Function.Injective fun a : T ⟶ Y ↦ F.map a.op ξ)
    (hsurj : ∀ (T : C) (x : F.obj (op T)), ∃ a : T ⟶ Y, F.map a.op ξ = x) :
    F.IsRepresentable :=
  RepresentableBy.isRepresentable
    { homEquiv := Equiv.ofBijective (fun a ↦ F.map a.op ξ) ⟨hinj _, fun x ↦ hsurj _ x⟩
      homEquiv_comp := fun a b ↦ by
        change F.map (a ≫ b).op ξ = F.map a.op (F.map b.op ξ)
        rw [op_comp, Functor.map_comp_apply] }

end CategoryTheory.Functor
