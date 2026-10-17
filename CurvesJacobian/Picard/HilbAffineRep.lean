/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.HilbAffineScheme
import CurvesJacobian.Picard.HilbAffineUniv
import CurvesJacobian.Picard.OpenSubfunctor
import CurvesJacobian.Picard.HilbSheaf

/-!
# Representability of `Hilb^d` of an affine scheme (Stacks, Lemma 44.2.5, Tag 0B99)

Let `R` be a ring, `K ⊆ R[x_i]` an ideal (any set of variables `I`), and `X = Spec R[x_i]/K`
(every affine `R`-scheme is of this form). For monomials `w : Fin d → (I →₀ ℕ)` let `F_W ⊆ Hilb^d`
be the subfunctor of points `Z ⊆ X_T` such that, over every affine `Spec B → T`, the images of the
`w l` form a basis of `𝒪_Z` (`pW`). We show:

* `F_W` is an open subfunctor: its pullback to an affine `Spec A` with point `x` is the open
  `D(obstr w J_x)` (`pW_map_iff_range`, from `hasMonomialBasis_map_iff`);
* the `F_W` cover `Hilb^d` (`iSup_obstr_eq_top`);
* `F_W` is represented by `Spec (univRingK K w)` (Stacks' structure-constants ring in matrix form,
  cut down by the closed condition `K A[x] ⊆ J` of Stacks, Lemma 44.2.3, Tag 0B97), with universal
  point `univPoint`;
* hence (`isRepresentable_hilbSch`) `Hilb^d_{X/S}` is representable, using that it is a Zariski
  sheaf (`hilbSheaf`) and Mathlib's gluing of representable open subfunctors (Stacks, Tag 01JJ).
-/

open CategoryTheory Limits AlgebraicGeometry Opposite MvPolynomial

universe u

noncomputable section

namespace CurvesJacobian.HilbAffine

variable {R : CommRingCat.{u}} {I : Type u} (K : Ideal (MvPolynomial I R)) (d : ℕ)

/-- The Hilbert functor of `Spec R[x]/K → Spec R`. -/
abbrev HS : Scheme.{u}ᵒᵖ ⥤ Type u := hilbSch (presMap K) d

section Algebra

lemma hasMonomialBasis_map_iff' {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B)
    {w : Fin d → I →₀ ℕ} {J : Ideal (MvPolynomial I A)} (hJ : IsHilbIdeal d J) :
    HasMonomialBasis w (J.map (MvPolynomial.map ψ)) ↔ (obstr w J).map ψ = ⊤ := by
  letI := ψ.toAlgebra
  exact hasMonomialBasis_map_iff B hJ

/-- The open `D(𝔞) ⊆ Spec A`. -/
def openOf {A : CommRingCat.{u}} (𝔞 : Ideal A) : (Spec A).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (𝔞 : Set A))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

lemma map_eq_top_iff_range_subset {A B : CommRingCat.{u}} (ψ : A ⟶ B) (𝔞 : Ideal A) :
    𝔞.map ψ.hom = ⊤ ↔ Set.range (Spec.map ψ) ⊆ openOf 𝔞 := by
  constructor
  · rintro h _ ⟨q, rfl⟩ hq
    apply q.2.ne_top
    rw [eq_top_iff, ← h, Ideal.map_le_iff_le_comap]
    exact hq
  · intro h
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    exact h ⟨⟨q, hq.isPrime⟩, rfl⟩ (Ideal.map_le_iff_le_comap.mp hle)

lemma matData_eq_of_kerIdeal_eq {A : Type u} [CommRing A] {w : Fin d → I →₀ ℕ}
    {M N : MatData A w} (h : kerIdeal M.X M.comm M.v = kerIdeal N.X N.comm N.v) : M = N := by
  have hM := (monomialBasisEquiv (w := w)).apply_symm_apply M
  have hN := (monomialBasisEquiv (w := w)).apply_symm_apply N
  have e : (monomialBasisEquiv (w := w)).symm M = (monomialBasisEquiv (w := w)).symm N :=
    Subtype.ext h
  rw [← hM, ← hN, e]

lemma matOfHom_comp {A A' : Type u} [CommRing A] [CommRing A'] (w : Fin d → I →₀ ℕ)
    (f : univRingK K w →+* A) (g : A →+* A') :
    matOfHom K w (g.comp f) = (matOfHom K w f).map g := by
  refine MatData.ext _ (funext fun i ↦ ?_) rfl
  change (genMatR₀ I d R i).map ((g.comp f).comp (Ideal.Quotient.mk _)) =
    ((genMatR₀ I d R i).map (f.comp (Ideal.Quotient.mk _))).map g
  rw [Matrix.map_map]
  rfl

end Algebra

section Pred

variable (w : Fin d → I →₀ ℕ)

/-- The subfunctor `F_W` of `Hilb^d` (Stacks, Tag 0B99), tested on affine schemes. -/
def pW (T : Scheme.{u}) (x : (HS K d).obj (op T)) : Prop :=
  ∀ (B : CommRingCat.{u}) (b : Spec B ⟶ T), HasMonomialBasis w (idealOf ((HS K d).map b.op x))

variable {K d w}

lemma pW_map {T T' : Scheme.{u}} (h : T' ⟶ T) {x : (HS K d).obj (op T)} (hx : pW K d w T x) :
    pW K d w T' ((HS K d).map h.op x) := fun B b ↦ by
  rw [← Functor.map_comp_apply, ← op_comp]
  exact hx B (b ≫ h)

/-- **`F_W` is open** (affine case of Stacks, Tag 0B99): the pullback of `F_W` along a point
`x` over `Spec A` is the open `D(obstr w J_x)`. -/
lemma pW_map_iff_range {A : CommRingCat.{u}} (x : (HS K d).obj (op (Spec A))) {T' : Scheme.{u}}
    (h : T' ⟶ Spec A) :
    pW K d w T' ((HS K d).map h.op x) ↔ Set.range h ⊆ openOf (obstr w (idealOf x)) := by
  have key : ∀ (B : CommRingCat.{u}) (b : Spec B ⟶ T'),
      HasMonomialBasis w (idealOf ((HS K d).map b.op ((HS K d).map h.op x))) ↔
        Set.range (b ≫ h) ⊆ openOf (obstr w (idealOf x)) := fun B b ↦ by
    rw [← Functor.map_comp_apply, ← op_comp, ← Spec.map_preimage (b ≫ h), idealOf_map,
      hasMonomialBasis_map_iff' d _ (isHilbIdeal_idealOf x), map_eq_top_iff_range_subset]
  constructor
  · rintro hx _ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := T'.affineCover.covers t
    have := (key _ _).mp (hx _ (T'.affineCover.f (T'.affineCover.idx t)))
    exact this ⟨s, by rw [Scheme.Hom.comp_apply]; exact congrArg _ hs⟩
  · intro hU B b
    rw [key]
    rintro _ ⟨s, rfl⟩
    exact hU ⟨b s, rfl⟩

lemma pW_iff {A : CommRingCat.{u}} (x : (HS K d).obj (op (Spec A))) :
    pW K d w (Spec A) x ↔ Set.range (𝟙 (Spec A)) ⊆ openOf (obstr w (idealOf x)) := by
  rw [← pW_map_iff_range, op_id, Functor.map_id_apply]

lemma isLocalPredicate_pW : Scheme.OpenSubfunctor.IsLocalPredicate (hilbSheaf (presMap K) d)
    (pW K d w) where
  map h x hx := pW_map h hx
  of_forall {T} x H' := fun B b ↦ by
    have hy : pW K d w (Spec B) ((HS K d).map b.op x) := by
      rw [pW_iff]
      rintro _ ⟨s, rfl⟩
      obtain ⟨U, hU, hpU⟩ := H' (b s)
      obtain ⟨W, hW, hsW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (Spec B).isBasis_affineOpens (show s ∈ b ⁻¹ᵁ U from hU)
      let c : Spec Γ(Spec B, W) ⟶ Spec B := (IsAffineOpen.isoSpec hW).inv ≫ Scheme.Opens.ι W
      have hc : Set.range (c ≫ b) ⊆ Set.range U.ι := by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have hy : c y ∈ Set.range (IsAffineOpen.fromSpec hW) := ⟨y, by simp [c]⟩
        rw [IsAffineOpen.range_fromSpec] at hy
        exact hWU hy
      let l := IsOpenImmersion.lift U.ι (c ≫ b) hc
      have hl : l ≫ U.ι = c ≫ b := IsOpenImmersion.lift_fac _ _ _
      have := pW_map l hpU
      change pW K d w _ ((HS K d).map l.op ((HS K d).map U.ι.op x)) at this
      rw [← Functor.map_comp_apply, ← op_comp, hl, op_comp,
        Functor.map_comp_apply, pW_map_iff_range] at this
      apply this
      have hs : s ∈ Set.range (IsAffineOpen.fromSpec hW) := by
        rw [IsAffineOpen.range_fromSpec]
        exact hsW
      obtain ⟨y, hy⟩ := hs
      exact ⟨y, by simpa [c] using hy⟩
    have := hy B (𝟙 _)
    rwa [op_id, Functor.map_id_apply] at this

end Pred

section Rep

variable (w : Fin d → I →₀ ℕ)

/-- The structure map `R → univRingK K w`. -/
def univHom : R ⟶ CommRingCat.of (univRingK K w) := CommRingCat.ofHom (algebraMap R _)

/-- The universal matrix data over `univRingK K w`. -/
abbrev univMat : MatData (univRingK K w) w := matOfHom K w (RingHom.id _)

lemma univMat_kCond : KCond K w (univHom K d w).hom (univMat K d w) := by
  have := kCond_matOfHom K w (RingHom.id (univRingK K w))
  rwa [RingHom.id_comp] at this

/-- The universal point of `F_W` over `Spec (univRingK K w)`. -/
def univPoint : (HS K d).obj (op (Spec (CommRingCat.of (univRingK K w)))) :=
  mk (univHom K d w) (kerIdeal (univMat K d w).X (univMat K d w).comm (univMat K d w).v)
    ((map_le_kerIdeal_iff K w _ _).mpr (univMat_kCond K d w))
    (isHilbIdeal_of_hasMonomialBasis
      (hasMonomialBasis_kerIdeal (univMat K d w).comm (univMat K d w).eval_eq))

variable {K d w}

lemma univPoint_map_fst {B : CommRingCat.{u}} (α : CommRingCat.of (univRingK K w) ⟶ B) :
    ((HS K d).map (Spec.map α).op (univPoint K d w)).1 = Spec.map (univHom K d w ≫ α) := by
  rw [Spec.map_comp]
  rfl

lemma idealOf_univPoint_map {B : CommRingCat.{u}} (α : CommRingCat.of (univRingK K w) ⟶ B) :
    idealOf ((HS K d).map (Spec.map α).op (univPoint K d w)) =
      kerIdeal (matOfHom K w α.hom).X (matOfHom K w α.hom).comm (matOfHom K w α.hom).v := by
  rw [idealOf_map, univPoint, idealOf_mk, kerIdeal_map]
  have key : ∀ N N' : MatData B w, N = N' → kerIdeal N.X N.comm N.v = kerIdeal N'.X N'.comm N'.v :=
    by rintro _ _ rfl; rfl
  exact key _ _ (by rw [← matOfHom_comp, RingHom.comp_id])

lemma hasMonomialBasis_univPoint_map {B : CommRingCat.{u}}
    (c : Spec B ⟶ Spec (CommRingCat.of (univRingK K w))) :
    HasMonomialBasis w (idealOf ((HS K d).map c.op (univPoint K d w))) := by
  rw [← Spec.map_preimage c, idealOf_univPoint_map]
  exact hasMonomialBasis_kerIdeal _ (MatData.eval_eq _)

lemma pW_univPoint_map {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of (univRingK K w))) :
    pW K d w T ((HS K d).map c.op (univPoint K d w)) := fun B b ↦ by
  rw [← Functor.map_comp_apply, ← op_comp]
  exact hasMonomialBasis_univPoint_map _

lemma univPoint_map_injective {B : CommRingCat.{u}} :
    Function.Injective fun c : Spec B ⟶ Spec (CommRingCat.of (univRingK K w)) ↦
      (HS K d).map c.op (univPoint K d w) := by
  intro a b hab
  rw [← Spec.map_preimage a, ← Spec.map_preimage b] at hab ⊢
  congr 1
  have h1 := congrArg Sigma.fst hab
  have h2 := congrArg idealOf hab
  simp only at h1 h2
  rw [univPoint_map_fst, univPoint_map_fst] at h1
  rw [idealOf_univPoint_map, idealOf_univPoint_map] at h2
  have hφ := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hM := matData_eq_of_kerIdeal_eq d h2
  have := (univRingKHomEquiv K w ((Spec.preimage b).hom.comp (algebraMap R _))).injective
    (a₁ := ⟨(Spec.preimage a).hom, hφ⟩) (a₂ := ⟨(Spec.preimage b).hom, rfl⟩) (Subtype.ext hM)
  exact CommRingCat.hom_ext (congrArg Subtype.val this)

lemma pW_iff_exists {B : CommRingCat.{u}} (x : (HS K d).obj (op (Spec B))) :
    pW K d w (Spec B) x ↔
      ∃ c : Spec B ⟶ Spec (CommRingCat.of (univRingK K w)),
        (HS K d).map c.op (univPoint K d w) = x := by
  constructor
  · intro hx
    have h := hx B (𝟙 _)
    rw [op_id, Functor.map_id_apply] at h
    set M := monomialBasisEquiv ⟨idealOf x, h⟩ with hM
    have hJ : kerIdeal M.X M.comm M.v = idealOf x :=
      congrArg Subtype.val ((monomialBasisEquiv (w := w)).symm_apply_apply ⟨idealOf x, h⟩)
    have hK : KCond K w (Spec.preimage x.1).hom M := by
      rw [← map_le_kerIdeal_iff, hJ]
      exact map_le_idealOf x
    set α := (univRingKHomEquiv K w (Spec.preimage x.1).hom).symm ⟨M, hK⟩ with hα
    have hαM : matOfHom K w α.1 = M :=
      congrArg Subtype.val ((univRingKHomEquiv K w _).apply_symm_apply ⟨M, hK⟩)
    refine ⟨Spec.map (CommRingCat.ofHom α.1), ext_of_idealOf ?_ ?_⟩
    · rw [univPoint_map_fst]
      refine (congrArg Spec.map ?_).trans (Spec.map_preimage x.1)
      exact CommRingCat.hom_ext α.2
    · rw [idealOf_univPoint_map]
      have key : ∀ N : MatData B w, N = M → kerIdeal N.X N.comm N.v = idealOf x := by
        rintro _ rfl
        exact hJ
      exact key _ hαM
  · rintro ⟨c, rfl⟩
    exact pW_univPoint_map c

end Rep

section Final

variable {K d} {w : Fin d → I →₀ ℕ}

lemma map_isoSpec {T T' : Scheme.{u}} [IsAffine T] (x : (HS K d).obj (op T)) (h : T' ⟶ T) :
    (HS K d).map (h ≫ T.isoSpec.hom).op ((HS K d).map T.isoSpec.inv.op x) =
      (HS K d).map h.op x := by
  rw [← Functor.map_comp_apply, ← op_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma exists_opens (w : Fin d → I →₀ ℕ) (T : Scheme.{u}) [IsAffine T] (x : (HS K d).obj (op T)) :
    ∃ U : T.Opens, (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
      pW K d w T' ((HS K d).map h.op x) ↔ Set.range h ⊆ U) ∧
      ∀ t, t ∈ U ↔ ¬ obstr w (idealOf ((HS K d).map T.isoSpec.inv.op x)) ≤
        (T.isoSpec.hom t).asIdeal := by
  refine ⟨T.isoSpec.hom ⁻¹ᵁ openOf (obstr w (idealOf ((HS K d).map T.isoSpec.inv.op x))),
    fun T' h ↦ ?_, fun t ↦ ?_⟩
  · rw [← map_isoSpec x h, pW_map_iff_range]
    constructor
    · rintro hU _ ⟨s, rfl⟩
      exact hU ⟨s, rfl⟩
    · rintro hU _ ⟨s, rfl⟩
      exact hU ⟨s, rfl⟩
  · change T.isoSpec.hom t ∉ PrimeSpectrum.zeroLocus _ ↔ _
    exact not_congr (PrimeSpectrum.mem_zeroLocus _ _)

lemma univPoint_injective_of_isAffine (T : Scheme.{u}) [IsAffine T] :
    Function.Injective fun a : T ⟶ Spec (CommRingCat.of (univRingK K w)) ↦
      (HS K d).map a.op (univPoint K d w) := by
  intro a b hab
  have h : (HS K d).map (T.isoSpec.inv ≫ a).op (univPoint K d w) =
      (HS K d).map (T.isoSpec.inv ≫ b).op (univPoint K d w) := by
    simp only [op_comp, Functor.map_comp_apply]
    exact congrArg _ hab
  exact (cancel_epi _).mp (univPoint_map_injective h)

lemma pW_iff_exists_of_isAffine (T : Scheme.{u}) [IsAffine T] (x : (HS K d).obj (op T)) :
    pW K d w T x ↔ ∃ a : T ⟶ Spec (CommRingCat.of (univRingK K w)),
      (HS K d).map a.op (univPoint K d w) = x := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (pW_iff_exists _).mp (pW_map T.isoSpec.inv hx)
    refine ⟨T.isoSpec.hom ≫ c, ?_⟩
    rw [op_comp, Functor.map_comp_apply, hc, ← Functor.map_comp_apply, ← op_comp,
      Iso.hom_inv_id, op_id, Functor.map_id_apply]
  · rintro ⟨c, rfl⟩
    exact pW_univPoint_map c

/-- **Representability of the Hilbert scheme of points of an affine scheme** (Stacks,
Lemma 44.2.5, Tag 0B99, with Lemma 44.2.3, Tag 0B97): for any ring `R`, any ideal `K` of a
polynomial ring `R[x_i]` (in any set of variables) and any `d`, the Hilbert functor
`Hilb^d_{X/S}` of `X = Spec R[x_i]/K → S = Spec R` is representable. -/
theorem isRepresentable_hilbSch : (hilbSch (presMap K) d).IsRepresentable := by
  have := Scheme.OpenSubfunctor.isRepresentable_of_isAffine (F := hilbSheaf (presMap K) d)
    (ι := Fin d → I →₀ ℕ) (p := fun w ↦ pW K d w) (fun _ ↦ isLocalPredicate_pW)
    (fun w T _ x ↦ by
      obtain ⟨U, hU, -⟩ := exists_opens w T x
      exact ⟨U, fun T' _ h ↦ hU T' h⟩)
    (Y := fun w ↦ Spec (CommRingCat.of (univRingK K w))) (fun w ↦ univPoint K d w)
    (fun _ T _ ↦ univPoint_injective_of_isAffine T)
    (fun _ T _ x ↦ pW_iff_exists_of_isAffine T x)
    (fun T _ x t ↦ by
      obtain ⟨w, hw⟩ := exists_not_obstr_le (isHilbIdeal_idealOf
        ((HS K d).map T.isoSpec.inv.op x)) (T.isoSpec.hom t)
      obtain ⟨U, hU, hmem⟩ := exists_opens w T x
      exact ⟨w, U, fun T' _ h ↦ hU T' h, (hmem t).mpr hw⟩)
  exact this

end Final

end CurvesJacobian.HilbAffine
