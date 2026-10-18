/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbCurve
import CurvesJacobian.Picard.HilbAffineRep
import CurvesJacobian.Picard.OpenSubfunctorIso

/-!
# `Hilb^d_{C/k}` is locally of finite type over `k`

Let `C` be a curve over a perfect field `k`. We show that the Hilbert scheme of points
`Hilb^d_{C/k}` (`hilbCurve k C d`) is locally of finite type, hence locally of finite
presentation, over `k` (`CurvesJacobian.locallyOfFiniteType_hilbCurveHom`; part of Stacks,
Proposition 44.3.6, Tag 0B9I, which says it is smooth and proper of dimension `d`).

Proof: every point of `Hilb^d_{C/k}` lies in an open subscheme representing the open subfunctor
`F_{j,W}` of points `Z ⊆ C_T` with `Z ⊆ U_T` for an affine open `U ⊆ C` and such that the
monomials `w` form a basis of `𝒪_Z` in a *finite* presentation `U ≅ Spec k[x_i]/K`
(`exists_curvePres`). By `HilbAffine.isRepresentable_hilbSch` this subfunctor is represented by
`Spec (univRingK K w)`, which is of finite type over `k` since there are finitely many
variables (`finiteType_univRingK`); and by `OpenSubfunctor.exists_iso_opens` the representing
scheme of an open subfunctor is an open subscheme of `Hilb^d_{C/k}`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

/-! ### Generic lemmas -/

section Generic

variable {C : Type*} [Category C]

/-- Variant of `Functor.exists_univ_of_restrict_of_univ` recording that the universal element
`ξ` maps to `η`. -/
theorem _root_.CategoryTheory.Functor.exists_univ_of_restrict_of_univ' {F G : Cᵒᵖ ⥤ Type u}
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
    ∃ (ξ : F.obj (op Y)) (hξ : p Y ξ), Φ Y ξ hξ = η ∧
      (∀ T : C, Function.Injective fun a : T ⟶ Y ↦ F.map a.op ξ) ∧
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
  refine ⟨ξ, hξ, hΦξ, fun T a b hab ↦ hηinj T ?_, fun T x ↦ ⟨?_, ?_⟩⟩
  · change G.map a.op η = G.map b.op η
    rw [← key, ← key]
    exact hc T _ _ hab _ _
  · rintro ⟨hx, hqx⟩
    obtain ⟨a, ha⟩ := (hq T _).1 hqx
    exact ⟨a, hinj _ _ _ (hpmap a ξ hξ) hx (by rw [key, ha])⟩
  · rintro ⟨a, rfl⟩
    exact ⟨hpmap a ξ hξ, by rw [key]; exact (hq T _).2 ⟨a, rfl⟩⟩

end Generic

section Transport

variable {X S : Scheme.{u}} {d : ℕ}

/-- Transport of points of `Hilb^d` along an equality of structure morphisms. -/
def hilbTr {f₁ f₂ : X ⟶ S} (e : f₁ = f₂) (T : Scheme.{u}) :
    (hilbSch f₁ d).obj (op T) → (hilbSch f₂ d).obj (op T) :=
  (eqToHom (congrArg (fun f ↦ hilbSch f d) e)).app (op T)

lemma hilbTr_fst {f₁ f₂ : X ⟶ S} (e : f₁ = f₂) {T : Scheme.{u}}
    (y : (hilbSch f₁ d).obj (op T)) : (hilbTr e T y).1 = y.1 := by
  subst e
  rfl

lemma hilbTr_map {f₁ f₂ : X ⟶ S} (e : f₁ = f₂) {T T' : Scheme.{u}} (h : T' ⟶ T)
    (y : (hilbSch f₁ d).obj (op T)) :
    hilbTr e T' ((hilbSch f₁ d).map h.op y) = (hilbSch f₂ d).map h.op (hilbTr e T y) := by
  subst e
  rfl

lemma hilbTr_injective {f₁ f₂ : X ⟶ S} (e : f₁ = f₂) (T : Scheme.{u}) :
    Function.Injective (hilbTr (d := d) e T) := by
  subst e
  exact fun _ _ h ↦ h

lemma hilbTr_surjective {f₁ f₂ : X ⟶ S} (e : f₁ = f₂) (T : Scheme.{u}) :
    Function.Surjective (hilbTr (d := d) e T) := by
  subst e
  exact fun y ↦ ⟨y, rfl⟩

end Transport

/-! ### The universal ring is of finite type -/

namespace HilbAffine

variable {R : Type u} [CommRing R] {I : Type u} [Finite I] {d : ℕ} (K : Ideal (MvPolynomial I R))
  (w : Fin d → I →₀ ℕ)

instance finiteType_univRingK : Algebra.FiniteType R (univRingK K w) := by
  haveI : Finite (UnivVar I d) := inferInstance
  haveI : Algebra.FiniteType R (CommRingR₀ I d R) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective
  exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective

end HilbAffine

/-! ### Finite presentations of affine opens of a curve -/

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  [PerfectField k] [Belyi.IsCurveOver k C]

local notation "Sk" => Spec (CommRingCat.of k)

omit [PerfectField k] in
variable (k) in
include k in
/-- Every affine open `U` of a curve is isomorphic over `k` to `Spec k[x_i]/K` with finitely many
variables, via an open immersion `j` with image `U`. -/
theorem exists_curvePres (U : C.Opens) (hU : IsAffineOpen U) :
    ∃ (I : Type u) (_ : Finite I) (K : Ideal (MvPolynomial I k))
      (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C), IsOpenImmersion j ∧
      Set.range j = U ∧ j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K := by
  let φ : Γ(Sk, ⊤) ⟶ Γ(C, U) := (C ↘ Sk).appLE ⊤ U le_top
  let ψ : k →+* Γ(C, U) := φ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hfp : φ.hom.FinitePresentation :=
    (C ↘ Sk).finitePresentation_appLE (isAffineOpen_top _) hU le_top
  have hψ : ψ.FiniteType :=
    (RingHom.FiniteType.of_finitePresentation hfp).comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  letI := ψ.toAlgebra
  have hft : Algebra.FiniteType k Γ(C, U) := hψ
  obtain ⟨s, hs⟩ := hft.out
  let ev : MvPolynomial s k →ₐ[k] Γ(C, U) := MvPolynomial.aeval fun i ↦ (i : Γ(C, U))
  have hev : Function.Surjective ev := by
    intro a
    have ha : a ∈ (⊤ : Subalgebra k Γ(C, U)) := trivial
    rw [← hs, Algebra.adjoin_eq_range] at ha
    obtain ⟨p, hp⟩ := ha
    exact ⟨MvPolynomial.rename (fun i : s ↦ (⟨i.1, by simp⟩ : (s : Set Γ(C, U)))) p, by
      rw [← hp]
      simp only [ev, MvPolynomial.aeval_rename]
      rfl⟩
  let K := RingHom.ker ev.toRingHom
  let e₀ : (MvPolynomial s k ⧸ K) ≃ₐ[k] Γ(C, U) := Ideal.quotientKerAlgEquivOfSurjective hev
  let eC : CommRingCat.of (MvPolynomial s k ⧸ K) ≅ Γ(C, U) := e₀.toRingEquiv.toCommRingCatIso
  let j : Spec (CommRingCat.of (MvPolynomial s k ⧸ K)) ⟶ C := Spec.map eC.inv ≫ hU.fromSpec
  refine ⟨s, inferInstance, K, j, inferInstance, ?_, ?_⟩
  · apply subset_antisymm
    · rintro _ ⟨y, rfl⟩
      rw [← IsAffineOpen.range_fromSpec hU]
      exact ⟨Spec.map eC.inv y, rfl⟩
    · intro y hy
      rw [← IsAffineOpen.range_fromSpec hU] at hy
      obtain ⟨y', rfl⟩ := hy
      obtain ⟨y'', rfl⟩ := (Spec.map eC.inv).surjective y'
      exact ⟨y'', rfl⟩
  · have h1 : hU.fromSpec ≫ (C ↘ Sk) = Spec.map φ ≫ (isAffineOpen_top Sk).fromSpec :=
      (IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_top _) hU le_top).symm
    have h2 : φ ≫ eC.inv = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
          CommRingCat.ofHom ((Ideal.Quotient.mk K).comp MvPolynomial.C) := by
      rw [← Iso.inv_comp_eq]
      ext a
      change e₀.symm (algebraMap k Γ(C, U) a) = Ideal.Quotient.mk K (MvPolynomial.C a)
      rw [AlgEquiv.commutes]
      rfl
    simp only [j, Category.assoc, h1]
    rw [← Spec.map_comp_assoc, h2, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp, Iso.inv_hom_id_assoc]

/-! ### The open subfunctors `F_{j,W}` -/

section Pieces

variable {C}


/-- The restriction of a point of `F_j ⊆ Hilb^d_{C/k}` to a point of `Hilb^d` of
`Spec k[x_i]/K`. -/
def resK (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) {T : Scheme.{u}} (x :
        (hilbSch (C ↘ Sk) d).obj (op T)) (hx : pOpen j T x) : (HilbAffine.HS (R := CommRingCat.of
            k) K d).obj (op T) :=
  hilbTr hj T (restrict j x hx)

omit [PerfectField k] [Belyi.IsCurveOver k C] in
lemma resK_fst (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) {T : Scheme.{u}} (x :
        (hilbSch (C ↘ Sk) d).obj (op T)) (hx : pOpen j T x) :
    (resK d j hj x hx).1 = x.1 :=
  hilbTr_fst hj _

omit [PerfectField k] [Belyi.IsCurveOver k C] in
lemma resK_map (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) {T T' : Scheme.{u}} (h : T'
        ⟶ T) (x : (hilbSch (C ↘ Sk) d).obj (op T)) (hx : pOpen j T x) :
    resK d j hj ((hilbSch (C ↘ Sk) d).map h.op x) ((isLocalPredicate_pOpen j).map h x hx) =
      (HilbAffine.HS (R := CommRingCat.of k) K d).map h.op (resK d j hj x hx) := by
  change hilbTr hj T' (restrict j ((hilbSch (C ↘ Sk) d).map h.op x) _) =
    (HilbAffine.HS (R := CommRingCat.of k) K d).map h.op (hilbTr hj T (restrict j x hx))
  rw [restrict_map, hilbTr_map]


/-- The predicate cutting out `F_{j,W} ⊆ Hilb^d_{C/k}`: `Z ⊆ j(Spec k[x]/K)_T`, and the
monomials `w` form a basis of `𝒪_Z`. -/
def qJ (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) (w : Fin d → I →₀ ℕ) (T :
        Scheme.{u}) (x : (hilbSch (C ↘ Sk) d).obj (op T)) : Prop :=
  ∃ hx : pOpen j T x, HilbAffine.pW (R := CommRingCat.of k) K d w T (resK d j hj x hx)

omit [PerfectField k] [Belyi.IsCurveOver k C] in
lemma qJ_map_iff (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) (w : Fin d → I →₀ ℕ) {T T' :
        Scheme.{u}} (h : T' ⟶ T) (x : (hilbSch (C ↘ Sk) d).obj (op T)) (hx : pOpen j T x) :
    qJ d j hj w T' ((hilbSch (C ↘ Sk) d).map h.op x) ↔ HilbAffine.pW (R := CommRingCat.of k) K d w
        T' ((HilbAffine.HS (R := CommRingCat.of k) K d).map h.op (resK d j hj x hx)) := by
  constructor
  · rintro ⟨_, hw⟩
    rwa [resK_map d j hj h x hx] at hw
  · intro hw
    exact ⟨(isLocalPredicate_pOpen j).map h x hx, by rw [resK_map d j hj h x hx]; exact hw⟩

omit [PerfectField k] [Belyi.IsCurveOver k C] in
lemma isLocalPredicate_qJ (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) (w : Fin d → I →₀ ℕ) :
    Scheme.OpenSubfunctor.IsLocalPredicate (hilbSheaf (C ↘ Sk) d) (qJ d j hj w) where
  map h x hx := by
    obtain ⟨hx, hw⟩ := hx
    exact (qJ_map_iff d j hj w h x hx).2 (HilbAffine.pW_map h hw)
  of_forall {T} x H := by
    have hx : pOpen j T x := (isLocalPredicate_pOpen j).of_forall x fun t ↦ by
      obtain ⟨U, htU, hU, -⟩ := H t
      exact ⟨U, htU, hU⟩
    refine ⟨hx, (HilbAffine.isLocalPredicate_pW (R := CommRingCat.of k) (K := K)).of_forall _ fun t
        ↦ ?_⟩
    obtain ⟨U, htU, hU⟩ := H t
    exact ⟨U, htU, (qJ_map_iff d j hj w U.ι x hx).1 hU⟩

omit [PerfectField k] [Belyi.IsCurveOver k C] in
lemma qJ_open (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) (w : Fin d → I →₀ ℕ) (T :
        Scheme.{u}) (x : (hilbSch (C ↘ Sk) d).obj (op T)) : ∃ U : T.Opens,
    ∀ (T' : Scheme.{u}) (h : T' ⟶ T), qJ d j hj w T' ((hilbSch (C ↘ Sk) d).map h.op x) ↔ Set.range
        h ⊆ U := by
  let O₁ := openLocus j x
  have hx₁ : pOpen j O₁ ((hilbSch (C ↘ Sk) d).map O₁.ι.op x) :=
    (pOpen_map_iff_range j O₁.ι x).2 (by rw [Scheme.Opens.range_ι])
  obtain ⟨O₂, hO₂⟩ := Scheme.OpenSubfunctor.exists_opens_of_isAffine
    (F := hilbSheaf (HilbAffine.presMap (R := CommRingCat.of k) K) d)
    (HilbAffine.isLocalPredicate_pW (R := CommRingCat.of k) (K := K)) (fun T _ y ↦ by
      obtain ⟨U, hU, -⟩ := HilbAffine.exists_opens (R := CommRingCat.of k) (K := K) w T y
      exact ⟨U, fun T' _ h ↦ hU T' h⟩) (resK d j hj _ hx₁)
  refine ⟨O₁.ι ''ᵁ O₂, fun T' h ↦ ?_⟩
  have key : ∀ h' : T' ⟶ O₁, h' ≫ O₁.ι = h →
      (qJ d j hj w T' ((hilbSch (C ↘ Sk) d).map h.op x) ↔ Set.range h ⊆ O₁.ι ''ᵁ O₂) := by
    rintro h' rfl
    rw [op_comp, Functor.map_comp_apply, qJ_map_iff d j hj w h' _ hx₁]
    change HilbAffine.pW (R := CommRingCat.of k) K d w T' ((hilbSch _ d).map h'.op (resK d j hj _
        hx₁)) ↔ _
    refine (hO₂ T' h').trans ?_
    constructor
    · rintro H _ ⟨t, rfl⟩
      exact ⟨h' t, H ⟨t, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro H _ ⟨t, rfl⟩
      obtain ⟨s, hs, hst⟩ := H ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply] at hst
      rwa [O₁.ι.isOpenEmbedding.injective hst] at hs
  have hlift : Set.range h ⊆ Set.range O₁.ι →
      (qJ d j hj w T' ((hilbSch (C ↘ Sk) d).map h.op x) ↔ Set.range h ⊆ O₁.ι ''ᵁ O₂) :=
    fun hr ↦ key _ (IsOpenImmersion.lift_fac O₁.ι h hr)
  constructor
  · intro hq
    exact (hlift (by rw [Scheme.Opens.range_ι]; exact (pOpen_map_iff_range j h x).1 hq.1)).1 hq
  · intro hr
    refine (hlift ?_).2 hr
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, -, hs⟩ := hr ⟨t, rfl⟩
    exact ⟨s, hs⟩

omit [PerfectField k] in
/-- `F_{j,W}` is represented by `Spec (univRingK K w)`, with structure morphism given by
`univHom`. -/
lemma exists_univ_qJ (d : ℕ) {I : Type u} {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) (w : Fin d → I →₀ ℕ) : ∃ η :
        (hilbSch (C ↘ Sk) d).obj (op (Spec (CommRingCat.of (HilbAffine.univRingK K w)))),
    η.1 = Spec.map (HilbAffine.univHom (R := CommRingCat.of k) K d w) ∧
      (∀ T : Scheme.{u}, Function.Injective fun a : T ⟶ _ ↦ (hilbSch (C ↘ Sk) d).map a.op η) ∧
      ∀ (T : Scheme.{u}) (x : (hilbSch (C ↘ Sk) d).obj (op T)),
        qJ d j hj w T x ↔ ∃ a : T ⟶ _, (hilbSch (C ↘ Sk) d).map a.op η = x := by
  have hηinj := Scheme.OpenSubfunctor.injective_of_isAffine
    (F := hilbSheaf (HilbAffine.presMap (R := CommRingCat.of k) K) d)
    (HilbAffine.univPoint (R := CommRingCat.of k) K d w) (fun T _ ↦
        HilbAffine.univPoint_injective_of_isAffine (R := CommRingCat.of k) (K := K) (w := w) T)
  have hq := fun (T : Scheme.{u}) (z : (HilbAffine.HS (R := CommRingCat.of k) K d).obj (op T)) ↦
    Scheme.OpenSubfunctor.iff_exists_of_isAffine
      (F := hilbSheaf (HilbAffine.presMap (R := CommRingCat.of k) K) d)
      (HilbAffine.univPoint (R := CommRingCat.of k) K d w) (HilbAffine.isLocalPredicate_pW (R :=
          CommRingCat.of k) (K := K))
      (fun T _ ↦ HilbAffine.univPoint_injective_of_isAffine (R := CommRingCat.of k) (K := K) (w :=
          w) T)
      (fun T _ x ↦ HilbAffine.pW_iff_exists_of_isAffine (R := CommRingCat.of k) (K := K) T x) z
  obtain ⟨ξ, hξ, hΦ, hinj, hiff⟩ := Functor.exists_univ_of_restrict_of_univ' (pOpen j)
    (fun h x hx ↦ (isLocalPredicate_pOpen j).map h x hx) (fun T x hx ↦ resK d j hj x hx)
    (fun h x hx ↦ resK_map d j hj h x hx)
    (fun T x y hx hy e ↦ restrict_injective j x y hx hy (hilbTr_injective hj T e))
    (fun T z ↦ by
      obtain ⟨z', rfl⟩ := hilbTr_surjective hj T z
      obtain ⟨x, hx, hxz⟩ := restrict_surjective j
        (fun g P ↦ isClosedImmersion_of_isSeparated j g P) z'
      exact ⟨x, hx, by rw [resK, hxz]⟩)
    (HilbAffine.pW (R := CommRingCat.of k) K d w) (HilbAffine.univPoint (R := CommRingCat.of k) K d
        w) hηinj (fun T z ↦ hq T z)
  refine ⟨ξ, ?_, hinj, fun T x ↦ hiff T x⟩
  rw [← resK_fst d j hj ξ hξ, hΦ]
  rfl

variable (k C) in
lemma hilbCurve_univ_bijective (d : ℕ) (T : Scheme.{u}) :
    Function.Bijective fun a : T ⟶ hilbCurve k C d ↦ (hilbSch (C ↘ Sk) d).map a.op (hilbCurveUniv k
        C d) := by
  have : (fun a : T ⟶ hilbCurve k C d ↦ (hilbSch (C ↘ Sk) d).map a.op (hilbCurveUniv k C d)) =
      hilbCurveHomEquiv k C d T := funext fun a ↦ (hilbCurveHomEquiv_apply k C d a).symm
  rw [this]
  exact (hilbCurveHomEquiv k C d T).bijective

/-- The open subscheme of `Hilb^d_{C/k}` representing `F_{j,W}` is of finite type over `k`. -/
theorem exists_opens_qJ (d : ℕ) {I : Type u} [Finite I] {K : Ideal (MvPolynomial I k)}
    (j : Spec (CommRingCat.of (MvPolynomial I k ⧸ K)) ⟶ C) [IsOpenImmersion j]
    (hj : j ≫ (C ↘ Sk) = HilbAffine.presMap (R := CommRingCat.of k) K) (w : Fin d → I →₀ ℕ) : ∃ O :
        (hilbCurve k C d).Opens,
    (∀ (T' : Scheme.{u}) (h : T' ⟶ hilbCurve k C d),
      qJ d j hj w T' ((hilbSch (C ↘ Sk) d).map h.op (hilbCurveUniv k C d)) ↔ Set.range h ⊆ O) ∧
      LocallyOfFiniteType (O.ι ≫ hilbCurveHom k C d) := by
  obtain ⟨η, hη1, hinj, hiff⟩ := exists_univ_qJ d j hj w
  obtain ⟨O, e, hO, he⟩ := Scheme.OpenSubfunctor.exists_iso_opens
    (F := hilbSheaf (C ↘ Sk) d) (isLocalPredicate_qJ d j hj w)
    (fun T _ x ↦ by
      obtain ⟨U, hU⟩ := qJ_open d j hj w T x
      exact ⟨U, fun T' _ h ↦ hU T' h⟩)
    (hilbCurveUniv k C d) (fun T ↦ (hilbCurve_univ_bijective k C d T).1)
    (fun T x ↦ (hilbCurve_univ_bijective k C d T).2 x) η (fun T _ ↦ hinj T)
    (fun T _ x ↦ hiff T x)
  refine ⟨O, hO, ?_⟩
  have h1 : O.ι ≫ hilbCurveHom k C d = e.hom ≫ Spec.map (HilbAffine.univHom (R := CommRingCat.of k)
      K d w) := by
    have := congrArg Sigma.fst he
    change e.hom ≫ η.1 = O.ι ≫ (hilbCurveUniv k C d).1 at this
    rw [hη1] at this
    exact this.symm
  haveI : LocallyOfFiniteType (Spec.map (HilbAffine.univHom (R := CommRingCat.of k) K d w)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr (HilbAffine.finiteType_univRingK K w)
  rw [h1]
  infer_instance

end Pieces

/-! ### `Hilb^d_{C/k}` is locally of finite type -/

variable (k) (d : ℕ)

/-- Every point of `Hilb^d_{C/k}` has an open neighbourhood which is of finite type over `k`. -/
theorem exists_opens_locallyOfFiniteType_hilbCurve (z : hilbCurve k C d) :
    ∃ O : (hilbCurve k C d).Opens, z ∈ O ∧ LocallyOfFiniteType (O.ι ≫ hilbCurveHom k C d) := by
  let T := Spec ((hilbCurve k C d).residueField z)
  let h := (hilbCurve k C d).fromSpecResidueField z
  let x := (hilbSch (C ↘ Sk) d).map h.op (hilbCurveUniv k C d)
  haveI : Subsingleton T := inferInstanceAs (Subsingleton (PrimeSpectrum _))
  -- the support of the divisor is finite, hence lies in an affine open
  haveI : IsFinite (x.2.J.subschemeι ≫ pullback.snd (C ↘ Sk) x.1) := x.2.isHilbMor_J.1
  let E := Set.range (x.2.J.subschemeι ≫ pullback.fst (C ↘ Sk) x.1)
  have hE : E.Finite := by
    obtain ⟨t⟩ : Nonempty T := inferInstance
    refine ((Scheme.Hom.finite_preimage_singleton
      (x.2.J.subschemeι ≫ pullback.snd (C ↘ Sk) x.1) t).image
        (x.2.J.subschemeι ≫ pullback.fst (C ↘ Sk) x.1)).subset ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨y, Subsingleton.elim _ _, rfl⟩
  obtain ⟨U, hU, hEU⟩ := IsCurveOver.exists_isAffineOpen_superset k C hE
  obtain ⟨I, _, K, j, _, hjU, hj⟩ := exists_curvePres k C U hU
  have hx : pOpen j T x := by
    change E ⊆ Set.range j
    rw [hjU]
    exact hEU
  -- a monomial basis at the point
  obtain ⟨t⟩ : Nonempty T := inferInstance
  let y := resK d j hj x hx
  obtain ⟨w, hw⟩ := HilbAffine.exists_not_obstr_le (HilbAffine.isHilbIdeal_idealOf
    ((HilbAffine.HS (R := CommRingCat.of k) K d).map T.isoSpec.inv.op y)) (T.isoSpec.hom t)
  obtain ⟨U', hU', hmem⟩ := HilbAffine.exists_opens (R := CommRingCat.of k) (K := K) w T y
  have hy : HilbAffine.pW (R := CommRingCat.of k) K d w T y := by
    have := (hU' T (𝟙 T)).2 (by
      rintro _ ⟨t', rfl⟩
      rw [Subsingleton.elim t' t]
      exact (hmem t).2 hw)
    rwa [op_id, Functor.map_id_apply] at this
  obtain ⟨O, hO, hlft⟩ := exists_opens_qJ d j hj w
  refine ⟨O, ?_, hlft⟩
  have hrange := (hO T h).1 ⟨hx, hy⟩
  have hz : z ∈ Set.range h := by
    rw [Scheme.range_fromSpecResidueField]
    rfl
  exact hrange hz

/-- **`Hilb^d_{C/k}` is locally of finite type over `k`** (part of Stacks, Proposition 44.3.6,
Tag 0B9I). -/
theorem locallyOfFiniteType_hilbCurveHom : LocallyOfFiniteType (hilbCurveHom k C d) := by
  choose O hzO hO using exists_opens_locallyOfFiniteType_hilbCurve k C d
  exact IsZariskiLocalAtSource.of_iSup_eq_top O
    (top_unique fun z _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzO z⟩) hO

/-- **`Hilb^d_{C/k}` is locally of finite presentation over `k`.** -/
theorem locallyOfFinitePresentation_hilbCurveHom :
    LocallyOfFinitePresentation (hilbCurveHom k C d) := by
  haveI := locallyOfFiniteType_hilbCurveHom k C d
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

end CurvesJacobian
