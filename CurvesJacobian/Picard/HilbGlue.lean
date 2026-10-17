/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbAffineRep
import CurvesJacobian.Picard.SchemeGeneric

/-!
# Open subfunctors of the Hilbert functor and representability (Stacks, Tag 0B9A)

Let `f : X ⟶ S` and `d : ℕ`. For an open immersion `j : X' ⟶ X` let `F_j ⊆ Hilb^d_{X/S}` be the
subfunctor of points `Z ⊆ X_T` with `Z ⊆ X'_T` (set-theoretically, `pOpen`). We show:

* `F_j` is an open subfunctor: for a point `x` over `T` it is cut out by the open complement
  `openLocus j x` of the image in `T` of the closed set `Z ∖ X'_T` under the closed map
  `Z → T` (`pOpen_map_iff_range`); the predicate is Zariski-local (`isLocalPredicate_pOpen`).
* Restricting ideal sheaves along `X'_T ⟶ X_T` identifies `F_j` with `Hilb^d_{X'/S}`
  (`restrict`, `restrict_injective`, `restrict_surjective`), provided closed subschemes of
  `X'_T` finite over `T` are closed in `X_T`; this holds if `f` is separated
  (`isClosedImmersion_comp_xMap`) or if `j` is an isomorphism. Hence `F_j` is represented by a
  scheme as soon as `Hilb^d_{X'/S}` is (`exists_univ_pOpen`).
* Base change along an open immersion `ε : S ⟶ S'`: the points of `Hilb^d_{X/S'}` lying over the
  range of `ε` are represented by `Hilb^d_{X/S}` (`exists_univ_pBase`).
* Isomorphism invariance: `isRepresentable_hilbSch_of_isIso` (in `X`) and
  `isRepresentable_hilbSch_comp_isIso` (in `S`). Hence `Hilb^d_{X/S}` is representable for any
  affine `X` over an affine `S` (`isRepresentable_hilbSch_of_isAffine`, Stacks, Lemma 44.2.5,
  Tag 0B99, for arbitrary affine schemes), by presenting `Γ(X)` as a quotient of a polynomial
  ring over `Γ(S)`.
* **Stacks, Proposition 44.2.6 (Tag 0B9A)** for separated `f`: `isRepresentable_hilbSch`. The
  hypothesis is that every finite set of points of a fibre `X_s` lies in an affine open of `X`.
  For affine opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`, the subfunctor `F_{U,V}` of points with
  `T → S` factoring through `V` and `Z ⊆ U_T` (`pGlue`) is open and represented by
  `Hilb^d_{U/V}`; these subfunctors cover `Hilb^d_{X/S}` since the fibres of a finite morphism
  `Z → T` are finite and a finite subset of an affine open `U₀` lying in an open `W` lies in a
  basic open of `U₀` contained in `W` (prime avoidance). Instead of reducing to affine `S` first
  (as Stacks does) we use the pairs `(U, V)` directly.

Separatedness of `f` is used (only) to see that a closed subscheme of `U_T` which is finite over
`T` is closed in `X_T` (Stacks handles non-separated `X` in a footnote). The hypothesis on finite
sets of points is stated for all finite subsets of a fibre; Stacks only requires it for at most
`d` points (which suffices since the fibres of `Z → T` have at most `d` points; this bound is
not formalised here).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

/-- The conditions on `Z ⟶ T` in the definition of `Hilb^d`: finite, flat, locally of finite
presentation and of constant rank `d`. -/
def IsHilbMor (d : ℕ) {Z T : Scheme.{u}} (q : Z ⟶ T) : Prop :=
  IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ ∀ t, q.finrank t = d

lemma isHilbMor_iff_of_isIso (d : ℕ) {Z' Z T : Scheme.{u}} (e : Z' ⟶ Z) [IsIso e]
    (q : Z ⟶ T) : IsHilbMor d (e ≫ q) ↔ IsHilbMor d q := by
  unfold IsHilbMor
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite),
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat),
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  refine forall_congr' fun t ↦ ?_
  rw [Scheme.Hom.finrank_comp_left_of_isIso]

/-- Pulling back an ideal sheaf along an open immersion `m` whose range contains its support
preserves the conditions `IsHilbMor`. -/
lemma isHilbMor_comap_iff (d : ℕ) {Y Y' T : Scheme.{u}} (J : Y.IdealSheafData) (m : Y' ⟶ Y)
    [IsOpenImmersion m] (hJ : Set.range J.subschemeι ⊆ Set.range m) (q : Y ⟶ T) (q' : Y' ⟶ T)
    (hq : m ≫ q = q') :
    IsHilbMor d ((J.comap m).subschemeι ≫ q') ↔ IsHilbMor d (J.subschemeι ≫ q) := by
  subst hq
  have := isIso_pullbackSnd_of_range_subset m _ hJ
  have e : (J.comap m).subschemeι ≫ m ≫ q =
      ((J.comapIso m).hom ≫ pullback.snd m J.subschemeι) ≫ J.subschemeι ≫ q := by
    rw [← Category.assoc, Scheme.IdealSheafData.comap_subschemeι_comp]
    simp only [Category.assoc]
  rw [e, isHilbMor_iff_of_isIso]

lemma range_eq_univ_of_isIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIso j] : Set.range j = Set.univ :=
  Set.range_eq_univ.mpr j.homeomorph.surjective

/-- The kernel of a closed immersion `i` satisfies `IsHilbMor` iff `i` does. -/
lemma isHilbMor_ker_iff (d : ℕ) {Z Y T : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (q : Y ⟶ T) : IsHilbMor d (i.ker.subschemeι ≫ q) ↔ IsHilbMor d (i ≫ q) := by
  rw [Scheme.Hom.ker_subschemeι_eq, Category.assoc, isHilbMor_iff_of_isIso]

variable {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}

namespace HilbPoint

variable {T : Scheme.{u}} {g : T ⟶ S}

/-- The ideal sheaf of a point over `Over.mk g`, as an ideal sheaf on `X ×_{S, g} T`. -/
def J (P : HilbPoint f d (Over.mk g)) : (Limits.pullback f g).IdealSheafData :=
  P.ideal

lemma isHilbMor_J (P : HilbPoint f d (Over.mk g)) :
    IsHilbMor d (P.J.subschemeι ≫ Limits.pullback.snd f g) :=
  ⟨P.isFinite, P.flat, P.locallyOfFinitePresentation, P.finrank_eq⟩

lemma ext_J {P Q : HilbPoint f d (Over.mk g)} (h : P.J = Q.J) : P = Q :=
  ext h

/-- A point of `Hilb` over `Over.mk g` from an ideal sheaf satisfying `IsHilbMor`. -/
def mk' (J : (Limits.pullback f g).IdealSheafData)
    (h : IsHilbMor d (J.subschemeι ≫ Limits.pullback.snd f g)) : HilbPoint f d (Over.mk g) where
  ideal := J
  isFinite := h.1
  flat := h.2.1
  locallyOfFinitePresentation := h.2.2.1
  finrank_eq := h.2.2.2

/-- Transport of a point of `Hilb` along an isomorphism `X ×_S T ≅ X' ×_{S'} T` over `T`. -/
def ofIso {X' S' : Scheme.{u}} {f' : X' ⟶ S'} {g' : T ⟶ S'}
    (φ : Limits.pullback f g ⟶ Limits.pullback f' g') [IsIso φ]
    (hφ : φ ≫ Limits.pullback.snd f' g' = Limits.pullback.snd f g)
    (P : HilbPoint f' d (Over.mk g')) : HilbPoint f d (Over.mk g) :=
  mk' (P.J.comap φ) ((isHilbMor_comap_iff d P.J φ
    (by rw [range_eq_univ_of_isIso φ]; exact Set.subset_univ _) _ _ hφ).2 P.isHilbMor_J)

lemma ofIso_J {X' S' : Scheme.{u}} {f' : X' ⟶ S'} {g' : T ⟶ S'}
    (φ : Limits.pullback f g ⟶ Limits.pullback f' g') [IsIso φ]
    (hφ : φ ≫ Limits.pullback.snd f' g' = Limits.pullback.snd f g)
    (P : HilbPoint f' d (Over.mk g')) : (ofIso φ hφ P).J = P.J.comap φ :=
  rfl

lemma pullback_J {T' : Scheme.{u}} (h : T' ⟶ T) (P : HilbPoint f d (Over.mk g)) :
    (P.pullback (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g)).J =
      P.J.comap (bcMap f h g _ rfl) :=
  rfl

lemma cast_J {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) (P : HilbPoint f d (Over.mk g₁)) :
    (P.cast h).J = P.J.comap (bcMap f (𝟙 T) g₁ g₂ (by rw [Category.id_comp, h])) :=
  rfl

end HilbPoint

section OpenImmersion

variable (f) {X' : Scheme.{u}} (j : X' ⟶ X)

/-- The map `X'_T ⟶ X_T` induced by `j : X' ⟶ X`. -/
def xMap {T : Scheme.{u}} (g : T ⟶ S) : pullback (j ≫ f) g ⟶ pullback f g :=
  pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

variable {T : Scheme.{u}} (g : T ⟶ S)

@[reassoc (attr := simp)]
lemma xMap_fst : xMap f j g ≫ pullback.fst f g = pullback.fst _ _ ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma xMap_snd : xMap f j g ≫ pullback.snd f g = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

lemma isPullback_xMap : IsPullback (pullback.fst (j ≫ f) g) (xMap f j g) j (pullback.fst f g) :=
  IsPullback.of_bot (by rw [xMap_snd]; exact IsPullback.of_hasPullback _ _)
    (xMap_fst f j g).symm (IsPullback.of_hasPullback f g)

lemma range_xMap : Set.range (xMap f j g) = pullback.fst f g ⁻¹' Set.range j :=
  (isPullback_xMap f j g).flip.range_fst_eq_preimage

instance [IsOpenImmersion j] : IsOpenImmersion (xMap f j g) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_xMap f j g) ‹_›

instance [IsIso j] : IsIso (xMap f j g) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (eq_top_iff.mpr fun z _ ↦ ?_)
  change z ∈ Set.range (xMap f j g)
  rw [range_xMap, range_eq_univ_of_isIso]
  trivial

/-- If `f` is separated, a closed subscheme of `X'_T` which is universally closed over `T` is
closed in `X_T`. -/
lemma isClosedImmersion_comp_xMap [IsSeparated f] [IsOpenImmersion j] {Z : Scheme.{u}}
    (i : Z ⟶ pullback (j ≫ f) g) [IsClosedImmersion i]
    [UniversallyClosed (i ≫ pullback.snd _ _)] : IsClosedImmersion (i ≫ xMap f j g) := by
  haveI : UniversallyClosed ((i ≫ xMap f j g) ≫ pullback.snd f g) := by
    rw [Category.assoc, xMap_snd]
    infer_instance
  exact isClosedImmersion_of_universallyClosed_comp _ (pullback.snd f g)

variable {f}

/-- The predicate cutting out `F_j ⊆ Hilb^d_{X/S}`: the closed subscheme `Z ⊆ X_T` lies in
`X'_T` (set-theoretically). -/
def pOpen (T : Scheme.{u}) (x : (hilbSch f d).obj (op T)) : Prop :=
  Set.range (x.2.J.subschemeι ≫ pullback.fst f x.1) ⊆ Set.range j

lemma pOpen_aux {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S)
    (J : (pullback f g).IdealSheafData) :
    Set.range ((J.comap (bcMap f h g _ rfl)).subschemeι ≫ pullback.fst f (h ≫ g)) ⊆
        Set.range j ↔
      ∀ z, (J.subschemeι ≫ pullback.snd f g) z ∈ Set.range h →
        (J.subschemeι ≫ pullback.fst f g) z ∈ Set.range j := by
  have e : (J.comap (bcMap f h g _ rfl)).subschemeι ≫ pullback.fst f (h ≫ g) =
      ((J.comapIso (bcMap f h g _ rfl)).hom ≫ pullback.snd _ _) ≫
        J.subschemeι ≫ pullback.fst f g := by
    rw [← bcMap_fst f h g _ rfl, ← Category.assoc, Scheme.IdealSheafData.comap_subschemeι_comp]
    simp only [Category.assoc]
  have hr := (isPullback_comap_bcMap f h g _ rfl J).range_fst_eq_preimage
  rw [e]
  constructor
  · intro H z hz
    have hz' : z ∈ Set.range ((J.comapIso (bcMap f h g _ rfl)).hom ≫ pullback.snd _ _) := by
      rw [hr]
      exact hz
    obtain ⟨z', rfl⟩ := hz'
    exact H ⟨z', (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro H _ ⟨z', rfl⟩
    rw [Scheme.Hom.comp_apply]
    refine H _ ?_
    change _ ∈ (J.subschemeι ≫ pullback.snd f g) ⁻¹' Set.range h
    rw [← hr]
    exact ⟨z', rfl⟩

/-- The pullback of `x` along `h : T' ⟶ T` lies in `F_j` iff all points of `Z` lying over the
range of `h` lie in `X'`. -/
lemma pOpen_map_iff {T T' : Scheme.{u}} (h : T' ⟶ T) (x : (hilbSch f d).obj (op T)) :
    pOpen j T' ((hilbSch f d).map h.op x) ↔
      ∀ z, (x.2.J.subschemeι ≫ pullback.snd f x.1) z ∈ Set.range h →
        (x.2.J.subschemeι ≫ pullback.fst f x.1) z ∈ Set.range j :=
  pOpen_aux j h x.1 x.2.J

lemma pOpen_iff {T : Scheme.{u}} (x : (hilbSch f d).obj (op T)) :
    pOpen j T x ↔ ∀ z, (x.2.J.subschemeι ≫ pullback.fst f x.1) z ∈ Set.range j :=
  Set.range_subset_iff

lemma isLocalPredicate_pOpen :
    Scheme.OpenSubfunctor.IsLocalPredicate (hilbSheaf f d) (pOpen j) where
  map h x hx := (pOpen_map_iff j h x).2 fun z _ ↦ (pOpen_iff j x).1 hx z
  of_forall x H := by
    refine (pOpen_iff j x).2 fun z ↦ ?_
    obtain ⟨U, htU, hU⟩ := H ((x.2.J.subschemeι ≫ pullback.snd f x.1) z)
    exact (pOpen_map_iff j U.ι x).1 hU z (by rw [Scheme.Opens.range_ι]; exact htU)

/-- The open subset of `T` over which `Z ⊆ X_T` lies in `X'_T`: the complement of the image of
the closed set `Z ∖ X'_T` under the closed map `Z → T` (Stacks, proof of Tag 0B9A). -/
def openLocus [IsOpenImmersion j] {T : Scheme.{u}} (x : (hilbSch f d).obj (op T)) : T.Opens :=
  ⟨((x.2.J.subschemeι ≫ pullback.snd f x.1) ''
      {z | (x.2.J.subschemeι ≫ pullback.fst f x.1) z ∉ Set.range j})ᶜ, by
    haveI : IsFinite (x.2.J.subschemeι ≫ pullback.snd f x.1) := x.2.isHilbMor_J.1
    refine (Scheme.Hom.isClosedMap _ _ ?_).isOpen_compl
    exact j.isOpenEmbedding.isOpen_range.isClosed_compl.preimage (Scheme.Hom.continuous _)⟩

lemma mem_openLocus [IsOpenImmersion j] {T : Scheme.{u}} (x : (hilbSch f d).obj (op T))
    (t : T) :
    t ∈ openLocus j x ↔ ∀ z, (x.2.J.subschemeι ≫ pullback.snd f x.1) z = t →
      (x.2.J.subschemeι ≫ pullback.fst f x.1) z ∈ Set.range j := by
  change t ∉ _ ↔ _
  constructor
  · intro H z hz
    by_contra hj
    exact H ⟨z, hj, hz⟩
  · rintro H ⟨z, hj, hz⟩
    exact hj (H z hz)

/-- `F_j` is an open subfunctor of `Hilb^d_{X/S}`: the pullback of `x` along `h` lies in `F_j`
iff `h` factors through `openLocus j x`. -/
lemma pOpen_map_iff_range [IsOpenImmersion j] {T T' : Scheme.{u}} (h : T' ⟶ T)
    (x : (hilbSch f d).obj (op T)) :
    pOpen j T' ((hilbSch f d).map h.op x) ↔ Set.range h ⊆ openLocus j x := by
  rw [pOpen_map_iff]
  constructor
  · rintro H _ ⟨t', rfl⟩
    exact (mem_openLocus j x _).2 fun z hz ↦ H z ⟨t', hz.symm⟩
  · rintro H z ⟨t', ht'⟩
    exact (mem_openLocus j x _).1 (H ⟨t', rfl⟩) z ht'.symm

variable [IsOpenImmersion j]

section Restrict

variable {T : Scheme.{u}} {g : T ⟶ S}

omit [IsOpenImmersion j] in
lemma range_subset_range_xMap (J : (pullback f g).IdealSheafData)
    (hJ : Set.range (J.subschemeι ≫ pullback.fst f g) ⊆ Set.range j) :
    Set.range J.subschemeι ⊆ Set.range (xMap f j g) := by
  rintro _ ⟨z, rfl⟩
  rw [range_xMap]
  exact hJ ⟨z, rfl⟩

/-- The restriction of a point `Z ⊆ X_T` of `Hilb^d_{X/S}` with `Z ⊆ X'_T` to a point of
`Hilb^d_{X'/S}`. -/
def restrictPoint (P : HilbPoint f d (Over.mk g))
    (hP : Set.range (P.J.subschemeι ≫ pullback.fst f g) ⊆ Set.range j) :
    HilbPoint (j ≫ f) d (Over.mk g) :=
  HilbPoint.mk' (P.J.comap (xMap f j g))
    ((isHilbMor_comap_iff d P.J (xMap f j g) (range_subset_range_xMap j P.J hP) _ _
      (xMap_snd f j g)).2 P.isHilbMor_J)

/-- The closed subscheme of `X_T` given by a point `Z ⊆ X'_T` of `Hilb^d_{X'/S}`, provided
`Z → X_T` is a closed immersion. -/
def extendPoint (P : HilbPoint (j ≫ f) d (Over.mk g))
    [IsClosedImmersion (P.J.subschemeι ≫ xMap f j g)] : HilbPoint f d (Over.mk g) :=
  HilbPoint.mk' (P.J.subschemeι ≫ xMap f j g).ker ((isHilbMor_ker_iff d _ _).2 (by
    rw [Category.assoc, xMap_snd]
    exact P.isHilbMor_J))

omit [IsOpenImmersion j] in
lemma range_extendPoint (P : HilbPoint (j ≫ f) d (Over.mk g))
    [IsClosedImmersion (P.J.subschemeι ≫ xMap f j g)] :
    Set.range ((extendPoint j P).J.subschemeι ≫ pullback.fst f g) ⊆ Set.range j := by
  have e : (extendPoint j P).J.subschemeι ≫ pullback.fst f g =
      (inv (P.J.subschemeι ≫ xMap f j g).toImage ≫ P.J.subschemeι ≫ pullback.fst _ _) ≫ j := by
    change (P.J.subschemeι ≫ xMap f j g).ker.subschemeι ≫ _ = _
    rw [Scheme.Hom.ker_subschemeι_eq]
    simp only [Category.assoc, xMap_fst]
  rintro _ ⟨z, rfl⟩
  rw [e]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

lemma restrictPoint_extendPoint (P : HilbPoint (j ≫ f) d (Over.mk g))
    [IsClosedImmersion (P.J.subschemeι ≫ xMap f j g)] :
    restrictPoint j (extendPoint j P) (range_extendPoint j P) = P := by
  refine HilbPoint.ext_J ?_
  change (P.J.subschemeι ≫ xMap f j g).ker.comap (xMap f j g) = P.J
  rw [Scheme.IdealSheafData.comap_ker_comp_of_mono, Scheme.IdealSheafData.ker_subschemeι]

lemma J_eq_ker_restrictPoint (P : HilbPoint f d (Over.mk g))
    (hP : Set.range (P.J.subschemeι ≫ pullback.fst f g) ⊆ Set.range j) :
    P.J = ((restrictPoint j P hP).J.subschemeι ≫ xMap f j g).ker :=
  (Scheme.IdealSheafData.ker_comap_subschemeι_comp _ _ (range_subset_range_xMap j P.J hP)).symm

end Restrict

/-- The restriction map `F_j ⟶ Hilb^d_{X'/S}`. -/
def restrict {T : Scheme.{u}} (x : (hilbSch f d).obj (op T)) (hx : pOpen j T x) :
    (hilbSch (j ≫ f) d).obj (op T) :=
  ⟨x.1, restrictPoint j x.2 hx⟩

lemma restrict_map {T T' : Scheme.{u}} (h : T' ⟶ T) (x : (hilbSch f d).obj (op T))
    (hx : pOpen j T x) :
    restrict j ((hilbSch f d).map h.op x) ((isLocalPredicate_pOpen j).map h x hx) =
      (hilbSch (j ≫ f) d).map h.op (restrict j x hx) := by
  obtain ⟨g, P⟩ := x
  refine Sigma.ext rfl (heq_of_eq (HilbPoint.ext_J ?_))
  change (P.J.comap (bcMap f h g _ rfl)).comap (xMap f j (h ≫ g)) =
    (P.J.comap (xMap f j g)).comap (bcMap (j ≫ f) h g _ rfl)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext <;> simp

lemma restrict_injective {T : Scheme.{u}} (x y : (hilbSch f d).obj (op T)) (hx : pOpen j T x)
    (hy : pOpen j T y) (e : restrict j x hx = restrict j y hy) : x = y := by
  obtain ⟨g, P⟩ := x
  obtain ⟨g', P'⟩ := y
  obtain ⟨rfl, e₂⟩ := Sigma.mk.inj_iff.mp e
  refine Sigma.ext rfl (heq_of_eq (HilbPoint.ext_J ?_))
  rw [J_eq_ker_restrictPoint j P hx, J_eq_ker_restrictPoint j P' hy, eq_of_heq e₂]

lemma restrict_surjective {T : Scheme.{u}}
    (hc : ∀ (g : T ⟶ S) (P : HilbPoint (j ≫ f) d (Over.mk g)),
      IsClosedImmersion (P.J.subschemeι ≫ xMap f j g))
    (z : (hilbSch (j ≫ f) d).obj (op T)) :
    ∃ (x : (hilbSch f d).obj (op T)) (hx : pOpen j T x), restrict j x hx = z := by
  obtain ⟨g, P⟩ := z
  have := hc g P
  exact ⟨⟨g, extendPoint j P⟩, range_extendPoint j P,
    Sigma.ext rfl (heq_of_eq (restrictPoint_extendPoint j P))⟩

/-- If `Hilb^d_{X'/S}` is representable and closed subschemes of `X'_T` finite over `T` are
closed in `X_T`, then `F_j ⊆ Hilb^d_{X/S}` is represented by a scheme `Y` with universal
point `ξ`. -/
theorem exists_univ_pOpen [(hilbSch (j ≫ f) d).IsRepresentable]
    (hc : ∀ {T : Scheme.{u}} (g : T ⟶ S) (P : HilbPoint (j ≫ f) d (Over.mk g)),
      IsClosedImmersion (P.J.subschemeι ≫ xMap f j g)) :
    ∃ (Y : Scheme.{u}) (ξ : (hilbSch f d).obj (op Y)),
      (∀ T : Scheme.{u}, Function.Injective fun a : T ⟶ Y ↦ (hilbSch f d).map a.op ξ) ∧
      ∀ (T : Scheme.{u}) (x : (hilbSch f d).obj (op T)),
        pOpen j T x ↔ ∃ a : T ⟶ Y, (hilbSch f d).map a.op ξ = x :=
  Functor.exists_univ_of_restrict (pOpen j) (fun h x hx ↦ (isLocalPredicate_pOpen j).map h x hx)
    (fun _ x hx ↦ restrict j x hx) (fun h x hx ↦ restrict_map j h x hx)
    (fun _ x y hx hy e ↦ restrict_injective j x y hx hy e)
    (fun _ z ↦ restrict_surjective j (fun g P ↦ hc g P) z)

/-- For separated `f`, a point of `Hilb^d_{X'/S}` is closed in `X_T`. -/
lemma isClosedImmersion_of_isSeparated [IsSeparated f] {T : Scheme.{u}} (g : T ⟶ S)
    (P : HilbPoint (j ≫ f) d (Over.mk g)) :
    IsClosedImmersion (P.J.subschemeι ≫ xMap f j g) := by
  haveI : IsFinite (P.J.subschemeι ≫ pullback.snd (j ≫ f) g) := P.isHilbMor_J.1
  exact isClosedImmersion_comp_xMap f j g _

end OpenImmersion

section IsoInvariance

/-- `Hilb^d` is invariant under isomorphisms `X' ≅ X` over `S`. -/
theorem isRepresentable_hilbSch_of_isIso {X' : Scheme.{u}} (j : X' ⟶ X) [IsIso j]
    [(hilbSch (j ≫ f) d).IsRepresentable] : (hilbSch f d).IsRepresentable := by
  obtain ⟨Y, ξ, hinj, hrange⟩ := exists_univ_pOpen (f := f) (d := d) j
    (fun _ _ ↦ inferInstance)
  refine Functor.isRepresentable_of_univ ξ hinj fun T x ↦ (hrange T x).1 ?_
  rw [pOpen, range_eq_univ_of_isIso j]
  exact Set.subset_univ _

variable {S' : Scheme.{u}} (ε : S ⟶ S')

variable (f) in
/-- `X ×_{S, g} T ⟶ X ×_{S', g'} T` for an isomorphism `ε : S ⟶ S'` and `g ≫ ε = g'`. -/
def baseIsoMap {T : Scheme.{u}} (g : T ⟶ S) (g' : T ⟶ S') (w : g ≫ ε = g') :
    pullback f g ⟶ pullback (f ≫ ε) g' :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [← w, pullback.condition_assoc])

variable {T : Scheme.{u}} (g : T ⟶ S) (g' : T ⟶ S') (w : g ≫ ε = g')

@[reassoc (attr := simp)]
lemma baseIsoMap_fst : baseIsoMap f ε g g' w ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseIsoMap_snd : baseIsoMap f ε g g' w ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

instance [Mono ε] : IsIso (baseIsoMap f ε g g' w) := by
  refine ⟨⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _) ?_, ?_, ?_⟩⟩
  · rw [← cancel_mono ε, Category.assoc, Category.assoc, pullback.condition, w]
  · apply pullback.hom_ext <;>
      simp only [baseIsoMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Category.id_comp]
  · apply pullback.hom_ext <;>
      simp only [baseIsoMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Category.id_comp]

/-- The predicate cutting out the points of `Hilb^d_{Y/S'}` lying over the range of
`ε : S ⟶ S'`. -/
abbrev pBase {Y : Scheme.{u}} {f' : Y ⟶ S'} (T : Scheme.{u}) (x : (hilbSch f' d).obj (op T)) :
    Prop :=
  Set.range x.1 ⊆ Set.range ε

lemma pBase_map {Y : Scheme.{u}} {f' : Y ⟶ S'} {T T' : Scheme.{u}} (h : T' ⟶ T)
    (x : (hilbSch f' d).obj (op T)) (hx : pBase ε T x) :
    pBase ε T' ((hilbSch f' d).map h.op x) := by
  rintro _ ⟨t', rfl⟩
  exact hx ⟨h t', (Scheme.Hom.comp_apply _ _ _).symm⟩

variable [IsOpenImmersion ε]

/-- For an open immersion `ε : S ⟶ S'`, the bijection between the points of `Hilb^d_{X/S'}`
(with `X` over `S'` via `f ≫ ε`) lying over the range of `ε` and the points of
`Hilb^d_{X/S}`. -/
def baseFun {T : Scheme.{u}} (x : (hilbSch (f ≫ ε) d).obj (op T)) (hx : pBase ε T x) :
    (hilbSch f d).obj (op T) :=
  ⟨IsOpenImmersion.lift ε x.1 hx, HilbPoint.ofIso (baseIsoMap f ε (IsOpenImmersion.lift ε x.1 hx)
    x.1 (IsOpenImmersion.lift_fac _ _ _)) (baseIsoMap_snd ..) x.2⟩

lemma baseFun_map_mk {T T' : Scheme.{u}} (h : T' ⟶ T) (g' : T ⟶ S')
    (P : HilbPoint (f ≫ ε) d (Over.mk g')) (hx : Set.range g' ⊆ Set.range ε)
    (hx' : Set.range (h ≫ g') ⊆ Set.range ε) :
    baseFun ε ⟨h ≫ g', P.pullback (Over.homMk h rfl)⟩ hx' =
      (hilbSch f d).map h.op (baseFun ε ⟨g', P⟩ hx) := by
  have e : IsOpenImmersion.lift ε (h ≫ g') hx' = h ≫ IsOpenImmersion.lift ε g' hx := by
    rw [← cancel_mono ε, IsOpenImmersion.lift_fac, Category.assoc, IsOpenImmersion.lift_fac]
  refine hilbSch_mk_eq e (HilbPoint.ext_J ?_)
  dsimp only [baseFun]
  refine Eq.trans ?_ (HilbPoint.pullback_J (g := IsOpenImmersion.lift ε g' hx) h _).symm
  rw [HilbPoint.cast_J, HilbPoint.ofIso_J, HilbPoint.pullback_J, HilbPoint.ofIso_J]
  simp only [← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext <;>
    simp only [baseIsoMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc, bcMap_fst, bcMap_snd, bcMap_snd_assoc, Category.id_comp]

lemma baseFun_map {T T' : Scheme.{u}} (h : T' ⟶ T) (x : (hilbSch (f ≫ ε) d).obj (op T))
    (hx : pBase ε T x) :
    baseFun ε ((hilbSch (f ≫ ε) d).map h.op x) (pBase_map ε h x hx) =
      (hilbSch f d).map h.op (baseFun ε x hx) := by
  obtain ⟨g', P⟩ := x
  exact baseFun_map_mk ε h g' P hx _

lemma baseFun_injective {T : Scheme.{u}} (x y : (hilbSch (f ≫ ε) d).obj (op T))
    (hx : pBase ε T x) (hy : pBase ε T y) (e : baseFun ε x hx = baseFun ε y hy) : x = y := by
  obtain ⟨g₁, P₁⟩ := x
  obtain ⟨g₂, P₂⟩ := y
  obtain ⟨e₁, e₂⟩ := Sigma.mk.inj_iff.mp e
  obtain rfl : g₁ = g₂ := by
    have := congrArg (· ≫ ε) e₁
    simpa only [IsOpenImmersion.lift_fac] using this
  refine Sigma.ext rfl (heq_of_eq (HilbPoint.ext_J ?_))
  exact Scheme.IdealSheafData.comap_injective_of_isIso
    (baseIsoMap f ε (IsOpenImmersion.lift ε g₁ hx) g₁ (IsOpenImmersion.lift_fac _ _ _))
    (congrArg HilbPoint.J (eq_of_heq e₂))

lemma baseFun_surjective {T : Scheme.{u}} (z : (hilbSch f d).obj (op T)) :
    ∃ (x : (hilbSch (f ≫ ε) d).obj (op T)) (hx : pBase ε T x), baseFun ε x hx = z := by
  obtain ⟨g, P⟩ := z
  have hx : Set.range (g ≫ ε) ⊆ Set.range ε := by
    rintro _ ⟨t, rfl⟩
    exact ⟨g t, (Scheme.Hom.comp_apply _ _ _).symm⟩
  refine ⟨⟨g ≫ ε, HilbPoint.ofIso (inv (baseIsoMap f ε g (g ≫ ε) rfl))
    (by rw [IsIso.inv_comp_eq, baseIsoMap_snd]) P⟩, hx, ?_⟩
  refine hilbSch_mk_eq ((cancel_mono ε).1 (IsOpenImmersion.lift_fac _ _ _)) (HilbPoint.ext_J ?_)
  dsimp only [baseFun]
  rw [HilbPoint.cast_J, HilbPoint.ofIso_J, HilbPoint.ofIso_J]
  simp only [← Scheme.IdealSheafData.comap_comp]
  convert P.J.comap_id using 2
  rw [← cancel_mono (baseIsoMap f ε g (g ≫ ε) rfl)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  apply pullback.hom_ext <;>
    simp only [baseIsoMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      bcMap_fst, bcMap_snd, Category.comp_id]

/-- For an open immersion `ε : S ⟶ S'`, the points of `Hilb^d_{X/S'}` lying over the range of
`ε` are represented by `Hilb^d_{X/S}` (if the latter is representable). -/
theorem exists_univ_pBase [(hilbSch f d).IsRepresentable] {f' : X ⟶ S'} (hf : f ≫ ε = f') :
    ∃ (Y : Scheme.{u}) (ξ : (hilbSch f' d).obj (op Y)),
      (∀ T : Scheme.{u}, Function.Injective fun a : T ⟶ Y ↦ (hilbSch f' d).map a.op ξ) ∧
      ∀ (T : Scheme.{u}) (x : (hilbSch f' d).obj (op T)),
        pBase ε T x ↔ ∃ a : T ⟶ Y, (hilbSch f' d).map a.op ξ = x := by
  subst hf
  exact Functor.exists_univ_of_restrict (pBase ε) (fun h x hx ↦ pBase_map ε h x hx)
    (fun _ x hx ↦ baseFun ε x hx) (fun h x hx ↦ baseFun_map ε h x hx)
    (fun _ x y hx hy e ↦ baseFun_injective ε x y hx hy e) (fun _ z ↦ baseFun_surjective ε z)

omit [IsOpenImmersion ε] in
/-- `Hilb^d` is invariant under isomorphisms of the base `S ≅ S'`. -/
theorem isRepresentable_hilbSch_comp_isIso [IsIso ε] [(hilbSch f d).IsRepresentable] :
    (hilbSch (f ≫ ε) d).IsRepresentable := by
  obtain ⟨Y, ξ, hinj, hrange⟩ := exists_univ_pBase (f := f) (d := d) ε rfl
  refine Functor.isRepresentable_of_univ ξ hinj fun T x ↦ (hrange T x).1 ?_
  rw [pBase, range_eq_univ_of_isIso ε]
  exact Set.subset_univ _

end IsoInvariance

section Affine

/-- `Hilb^d_{X/S}` is representable for any affine scheme `X` over an affine scheme `S`
(Stacks, Lemma 44.2.5, Tag 0B99): present `Γ(X)` as a quotient of a polynomial ring over `Γ(S)`
and use `HilbAffine.isRepresentable_hilbSch` together with isomorphism invariance. -/
theorem isRepresentable_hilbSch_of_isAffine (f : X ⟶ S) [IsAffine X] [IsAffine S] :
    (hilbSch f d).IsRepresentable := by
  let φ : Γ(S, ⊤) ⟶ Γ(X, ⊤) := f.appTop
  let ev : MvPolynomial Γ(X, ⊤) Γ(S, ⊤) →+* Γ(X, ⊤) := MvPolynomial.eval₂Hom φ.hom id
  have hev : Function.Surjective ev := fun a ↦ ⟨MvPolynomial.X a, MvPolynomial.eval₂Hom_X' ..⟩
  let K := RingHom.ker ev
  let e₀ : CommRingCat.of (MvPolynomial Γ(X, ⊤) Γ(S, ⊤) ⧸ K) ≅ Γ(X, ⊤) :=
    (RingHom.quotientKerEquivOfSurjective hev).toCommRingCatIso
  let j : Spec (CommRingCat.of (MvPolynomial Γ(X, ⊤) Γ(S, ⊤) ⧸ K)) ⟶ X :=
    Spec.map e₀.inv ≫ X.isoSpec.inv
  have hring : φ ≫ e₀.inv = CommRingCat.ofHom ((Ideal.Quotient.mk K).comp MvPolynomial.C) := by
    rw [Iso.comp_inv_eq]
    ext r
    change φ r = RingHom.quotientKerEquivOfSurjective hev (Ideal.Quotient.mk K (MvPolynomial.C r))
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    exact (MvPolynomial.eval₂Hom_C _ _ _).symm
  have key : j ≫ f = HilbAffine.presMap K ≫ S.isoSpec.inv := by
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp,
      hring]
  haveI := HilbAffine.isRepresentable_hilbSch (K := K) (d := d)
  haveI : (hilbSch (HilbAffine.presMap K ≫ S.isoSpec.inv) d).IsRepresentable :=
    isRepresentable_hilbSch_comp_isIso _
  haveI : (hilbSch (j ≫ f) d).IsRepresentable := by
    rw [key]
    infer_instance
  exact isRepresentable_hilbSch_of_isIso j

end Affine

section Glue

lemma range_comp_subset_iff {T T' Y : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ Y) (V : Y.Opens) :
    Set.range (h ≫ g) ⊆ V ↔ Set.range h ⊆ g ⁻¹ᵁ V := by
  constructor
  · rintro H _ ⟨t, rfl⟩
    have := H ⟨t, rfl⟩
    rwa [Scheme.Hom.comp_apply] at this
  · rintro H _ ⟨t, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact H ⟨t, rfl⟩

/-- The predicate cutting out `F_{U,V} ⊆ Hilb^d_{X/S}` for opens `U ⊆ X`, `V ⊆ S`: the
structure morphism `T → S` factors through `V` and `Z ⊆ U_T`. -/
def pGlue (U : X.Opens) (V : S.Opens) (T : Scheme.{u}) (x : (hilbSch f d).obj (op T)) : Prop :=
  pOpen U.ι T x ∧ Set.range x.1 ⊆ V

lemma isLocalPredicate_pGlue (U : X.Opens) (V : S.Opens) :
    Scheme.OpenSubfunctor.IsLocalPredicate (hilbSheaf f d) (pGlue U V) where
  map h x hx := ⟨(isLocalPredicate_pOpen U.ι).map h x hx.1, by
    rintro _ ⟨t', rfl⟩
    exact hx.2 ⟨h t', (Scheme.Hom.comp_apply _ _ _).symm⟩⟩
  of_forall x H := by
    refine ⟨(isLocalPredicate_pOpen U.ι).of_forall x fun t ↦ ?_, ?_⟩
    · obtain ⟨W, htW, hW, -⟩ := H t
      exact ⟨W, htW, hW⟩
    · rintro _ ⟨t, rfl⟩
      obtain ⟨W, htW, -, hW⟩ := H t
      exact (range_comp_subset_iff W.ι x.1 V).1 hW ⟨⟨t, htW⟩, rfl⟩

/-- `F_{U,V}` is an open subfunctor of `Hilb^d_{X/S}`. -/
lemma pGlue_map_iff_range (U : X.Opens) (V : S.Opens) {T T' : Scheme.{u}} (h : T' ⟶ T)
    (x : (hilbSch f d).obj (op T)) :
    pGlue U V T' ((hilbSch f d).map h.op x) ↔ Set.range h ⊆ openLocus U.ι x ⊓ x.1 ⁻¹ᵁ V := by
  refine Iff.trans (and_congr (pOpen_map_iff_range U.ι h x) (range_comp_subset_iff h x.1 V)) ?_
  exact ⟨fun H _ ht ↦ ⟨H.1 ht, H.2 ht⟩, fun H ↦ ⟨fun _ ht ↦ (H ht).1, fun _ ht ↦ (H ht).2⟩⟩

/-- **Stacks, Proposition 44.2.6 (Tag 0B9A)**, for a separated morphism. Let `f : X ⟶ S` be
separated, and assume that every finite set of points of a fibre `X_s` is contained in an
affine open of `X`. Then `Hilb^d_{X/S}` is representable. -/
theorem isRepresentable_hilbSch [IsSeparated f]
    (H : ∀ (s : S) (E : Set X), E.Finite → (∀ x ∈ E, f x = s) →
      ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U) :
    (hilbSch f d).IsRepresentable := by
  let ι := {UV : X.affineOpens × S.affineOpens // UV.1.1 ≤ f ⁻¹ᵁ UV.2.1}
  have hrep : ∀ i : ι, ∃ (Y : Scheme.{u}) (ξ : (hilbSch f d).obj (op Y)),
      (∀ T : Scheme.{u}, Function.Injective fun a : T ⟶ Y ↦ (hilbSch f d).map a.op ξ) ∧
      ∀ (T : Scheme.{u}) (x : (hilbSch f d).obj (op T)),
        pGlue i.1.1.1 i.1.2.1 T x ↔ ∃ a : T ⟶ Y, (hilbSch f d).map a.op ξ = x := by
    rintro ⟨⟨U, V⟩, hUV⟩
    haveI : IsAffine (U.1 : Scheme.{u}) := U.2
    haveI : IsAffine (V.1 : Scheme.{u}) := V.2
    haveI := isRepresentable_hilbSch_of_isAffine (d := d) (f.resLE V.1 U.1 hUV)
    obtain ⟨Y, η, hηinj, hη⟩ := exists_univ_pBase (f := f.resLE V.1 U.1 hUV) (d := d) V.1.ι
      (f' := U.1.ι ≫ f) (Scheme.Hom.resLE_comp_ι f hUV)
    obtain ⟨ξ, hinj, hiff⟩ := Functor.exists_univ_of_restrict_of_univ (pOpen U.1.ι)
      (fun h x hx ↦ (isLocalPredicate_pOpen U.1.ι).map h x hx)
      (fun _ x hx ↦ restrict U.1.ι x hx) (fun h x hx ↦ restrict_map U.1.ι h x hx)
      (fun _ x y hx hy e ↦ restrict_injective U.1.ι x y hx hy e)
      (fun _ z ↦ restrict_surjective U.1.ι
        (fun g P ↦ isClosedImmersion_of_isSeparated U.1.ι g P) z)
      (pBase V.1.ι) η hηinj hη
    refine ⟨Y, ξ, hinj, fun T x ↦ (Iff.trans ?_ (hiff T x))⟩
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, ?_⟩
      change Set.range x.1 ⊆ Set.range V.1.ι
      rwa [Scheme.Opens.range_ι]
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, ?_⟩
      change Set.range x.1 ⊆ Set.range V.1.ι at h₂
      rwa [Scheme.Opens.range_ι] at h₂
  choose Y ξ hinj hrange using hrep
  refine Scheme.OpenSubfunctor.isRepresentable_of_isAffine (F := hilbSheaf f d) (ι := ι)
    (p := fun i ↦ pGlue i.1.1.1 i.1.2.1) (fun i ↦ isLocalPredicate_pGlue _ _)
    (fun i T _ x ↦ ⟨openLocus i.1.1.1.ι x ⊓ x.1 ⁻¹ᵁ i.1.2.1,
      fun T' _ h ↦ pGlue_map_iff_range i.1.1.1 i.1.2.1 h x⟩) ξ
    (fun i T _ ↦ hinj i T) (fun i T _ x ↦ hrange i T x) fun T _ x t ↦ ?_
  haveI : IsFinite (x.2.J.subschemeι ≫ pullback.snd f x.1) := x.2.isHilbMor_J.1
  obtain ⟨V, hV, htV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x.1 t) (U := ⊤) trivial
  let E := (x.2.J.subschemeι ≫ pullback.fst f x.1) ''
    ((x.2.J.subschemeι ≫ pullback.snd f x.1) ⁻¹' {t})
  have hE : E.Finite := (Scheme.Hom.finite_preimage_singleton _ t).image _
  have hEs : ∀ y ∈ E, f y = x.1 t := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc,
      Scheme.Hom.comp_apply]
    exact congrArg x.1 hz
  obtain ⟨U₀, hU₀, hEU₀⟩ := H (x.1 t) E hE hEs
  obtain ⟨U, hU, hEU, -, hUV⟩ := exists_isAffineOpen_of_finite hU₀ (f ⁻¹ᵁ V) hE hEU₀
    fun y hy ↦ by
      change f y ∈ V
      rw [hEs y hy]
      exact htV
  refine ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, openLocus U.ι x ⊓ x.1 ⁻¹ᵁ V,
    fun T' _ h ↦ pGlue_map_iff_range U V h x, ⟨(mem_openLocus U.ι x t).2 fun z hz ↦ ?_, htV⟩⟩
  rw [Scheme.Opens.range_ι]
  exact hEU ⟨z, hz, rfl⟩

end Glue

end CurvesJacobian
