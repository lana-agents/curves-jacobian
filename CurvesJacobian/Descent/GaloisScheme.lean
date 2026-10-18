/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Descent.GaloisAffine
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import CurvesJacobian.Picard.OverSigmaRep
import CurvesJacobian.Picard.OverSigmaSheafSmall
import CurvesJacobian.Picard.OpenSubfunctor

/-!
# Galois descent of schemes covered by Galois-stable affine opens

Let `L / k` be a finite Galois extension with group `G` and `X` a scheme over `Spec L` with a
semilinear `G`-action (`GalAction`).

* `CurvesJacobian.GaloisDescent.exists_baseAct_apply_eq`: for an affine `k`-scheme `T`, the
  fibres of `T_L ⟶ T` are `G`-orbits.
* `CurvesJacobian.GaloisDescent.GalAction.restrict`: the action on a `G`-stable open `V ⊆ X`,
  and `eqMorRestrictEquiv`: equivariant morphisms to `V` are those to `X` landing in `V`.
* `CurvesJacobian.GaloisDescent.descFunctor`: the functor `T ↦ Hom^G_L(T_L, X)` on `(Sch/k)`,
  a Zariski sheaf (`isSheafOver_descFunctor`).
* **`CurvesJacobian.GaloisDescent.isRepresentable_descFunctor`**: if `X` is covered by `G`-stable
  affine opens `V`, the descended functor is representable (by gluing the affine descents
  `Spec Γ(V)^G` of `GaloisAffine`, using `Scheme.OpenSubfunctor.isRepresentable_of_isAffine`);
  `descScheme`, `descRepresentableBy`: the descended `k`-scheme `X₀` with
  `Hom_k(T, X₀) ≃ Hom^G_L(T_L, X)`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

instance : Flat (sL k L) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance [FiniteDimensional k L] : LocallyOfFinitePresentation (sL k L) := by
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.finitePresentation_algebraMap]
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

instance [FiniteDimensional k L] : UniversallyOpen (sL k L) := UniversallyOpen.of_flat _

instance : Surjective (sL k L) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

section BaseChange

variable {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
  {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T) (ht : h ≫ t = t')

/-- `T'_L` is the pullback of `T_L ⟶ T` along `h : T' ⟶ T`. -/
lemma isPullback_bcL :
    IsPullback (bcL (L := L) t h ht) (pullback.fst t' (sL k L)) (pullback.fst t (sL k L)) h := by
  subst ht
  refine IsPullback.of_right ?_ (bcL_fst (L := L) t h rfl)
    (IsPullback.of_hasPullback t (sL k L)).flip
  rw [bcL_snd]
  exact (IsPullback.of_hasPullback _ _).flip

/-- A point of `T_L` over the image of `h` lies in the image of `T'_L`. -/
lemma mem_range_bcL (z : ↥(pullback t (sL k L))) (u : T')
    (hu : h u = pullback.fst t (sL k L) z) :
    z ∈ Set.range (bcL (L := L) t h ht) := by
  have H := (isPullback_bcL (L := L) t h ht).flip
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback u z hu
  refine ⟨H.isoPullback.inv w, ?_⟩
  have e : H.isoPullback.inv ≫ bcL (L := L) t h ht =
      pullback.snd h (pullback.fst t (sL k L)) :=
    (Iso.inv_comp_eq _).mpr H.isoPullback_hom_snd.symm
  rw [← Scheme.Hom.comp_apply, e, hw]

lemma bcL_id : bcL (L := L) t (𝟙 T) (Category.id_comp t) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

lemma bcL_comp {T'' : Scheme.{u}} {t'' : T'' ⟶ Spec (CommRingCat.of k)} (h' : T'' ⟶ T')
    (ht' : h' ≫ t' = t'') :
    bcL (L := L) t (h' ≫ h) (by rw [Category.assoc, ht, ht']) =
      bcL (L := L) t' h' ht' ≫ bcL (L := L) t h ht := by
  apply pullback.hom_ext <;> simp

instance isOpenImmersion_bcL [IsOpenImmersion h] : IsOpenImmersion (bcL (L := L) t h ht) := by
  have H := (isPullback_bcL (L := L) t h ht).flip
  rw [← H.isoPullback_hom_snd]
  infer_instance

end BaseChange

namespace GalAction

variable {X : Scheme.{u}} {q : X ⟶ Spec (CommRingCat.of L)} (a : GalAction (k := k) X q)

/-- `V ⊆ X` is `G`-stable. -/
def IsStable (V : X.Opens) : Prop := ∀ g, a.act g ⁻¹ᵁ V = V

/-- The restriction of a semilinear action to a `G`-stable open `V`. -/
def restrict (V : X.Opens) (hV : a.IsStable V) : GalAction (k := k) V.toScheme (V.ι ≫ q) where
  act g := (a.act g).resLE V V (hV g).ge
  act_comp g := by
    rw [Scheme.Hom.resLE_comp_ι_assoc, a.act_comp, Category.assoc]
  act_one := by
    rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι, a.act_one, Category.comp_id, Category.id_comp]
  act_mul g h := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      Scheme.Hom.resLE_comp_ι, a.act_mul]

@[reassoc]
lemma restrict_act_ι (V : X.Opens) (hV : a.IsStable V) (g : Gal(L/k)) :
    (a.restrict V hV).act g ≫ V.ι = V.ι ≫ a.act g :=
  Scheme.Hom.resLE_comp_ι _ _

lemma mem_of_isStable {V : X.Opens} (hV : a.IsStable V) (g : Gal(L/k)) {x : X} (hx : x ∈ V) :
    a.act g x ∈ V := by
  rw [← hV g] at hx
  exact hx

end GalAction

lemma isoSpec_hom_apply_asIdeal {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (x : X) :
    (Y.isoSpec.hom (f x)).asIdeal = (X.isoSpec.hom x).asIdeal.comap f.appTop.hom := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply,
    Spec.map_apply]
  rfl

lemma eq_of_isoSpec_hom_asIdeal {X : Scheme.{u}} [IsAffine X] {x y : X}
    (h : (X.isoSpec.hom x).asIdeal = (X.isoSpec.hom y).asIdeal) : x = y := by
  have h' : X.isoSpec.hom x = X.isoSpec.hom y := PrimeSpectrum.ext h
  have := congrArg X.isoSpec.inv h'
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at this

section Saturation

variable [FiniteDimensional k L] [IsGalois k L]

/-- **The fibres of `T_L ⟶ T` are `Gal(L/k)`-orbits** (`T` affine). -/
theorem exists_baseAct_apply_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [IsAffine T]
    (w w' : ↥(pullback t (sL k L)))
    (h : pullback.fst t (sL k L) w = pullback.fst t (sL k L) w') :
    ∃ g : Gal(L/k), (baseAct t).act g w = w' := by
  let P : Ideal (SecU (pullback.snd t (sL k L))) :=
    ((pullback t (sL k L)).isoSpec.hom w).asIdeal
  let Q : Ideal (SecU (pullback.snd t (sL k L))) :=
    ((pullback t (sL k L)).isoSpec.hom w').asIdeal
  haveI : P.IsPrime := PrimeSpectrum.isPrime _
  haveI : Q.IsPrime := PrimeSpectrum.isPrime _
  have hPQ : P.comap (algebraMap (SecT t) (SecU (pullback.snd t (sL k L)))) =
      Q.comap (algebraMap (SecT t) (SecU (pullback.snd t (sL k L)))) := by
    have e1 := isoSpec_hom_apply_asIdeal (pullback.fst t (sL k L)) w
    have e2 := isoSpec_hom_apply_asIdeal (pullback.fst t (sL k L)) w'
    rw [h, e2] at e1
    exact e1.symm
  obtain ⟨g, hg⟩ := exists_comap_eq_of_comap_eq (R := SecT t)
    (B := SecU (pullback.snd t (sL k L))) (baseAct t).secAct_algebraMap
    (baseAct_secAct_algebraMap t) P Q hPQ
  refine ⟨g, eq_of_isoSpec_hom_asIdeal ?_⟩
  rw [isoSpec_hom_apply_asIdeal]
  exact hg.symm

end Saturation

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) {X : Scheme.{u}}
  {q : X ⟶ Spec (CommRingCat.of L)} (aX : GalAction (k := k) X q)

/-- **Equivariant morphisms to a stable open `V`** are those to `X` landing in `V`. -/
def eqMorRestrictEquiv (V : X.Opens) (hV : aX.IsStable V) :
    EqMor t (aX.restrict V hV) ≃ {f : EqMor t aX // Set.range f.1 ⊆ V} where
  toFun f := ⟨⟨f.1 ≫ V.ι, by rw [Category.assoc, f.2.1], fun g ↦ by
    rw [reassoc_of% f.2.2 g, GalAction.restrict_act_ι, Category.assoc]⟩, by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← Scheme.Opens.range_ι V]
      exact Set.image_subset_range _ _⟩
  invFun f := ⟨IsOpenImmersion.lift V.ι f.1.1 (by rw [Scheme.Opens.range_ι]; exact f.2), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact f.1.2.1, fun g ↦ by
      rw [← cancel_mono V.ι, Category.assoc, IsOpenImmersion.lift_fac, Category.assoc,
        GalAction.restrict_act_ι, IsOpenImmersion.lift_fac_assoc, f.1.2.2 g]⟩
  left_inv f := Subtype.ext (by
    rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac])
  right_inv f := Subtype.ext (Subtype.ext (IsOpenImmersion.lift_fac _ _ _))

lemma EqMor.pull_val {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') (f : EqMor t aX) : (EqMor.pull t aX h ht f).1 = bcL t h ht ≫ f.1 := rfl

lemma EqMor.pull_congr {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} {h₁ h₂ : T' ⟶ T}
    (e : h₁ = h₂) (ht₁ : h₁ ≫ t = t') (ht₂ : h₂ ≫ t = t') (f : EqMor t aX) :
    EqMor.pull t aX h₁ ht₁ f = EqMor.pull t aX h₂ ht₂ f := by
  subst e
  rfl

lemma EqMor.pull_id (f : EqMor t aX) : EqMor.pull t aX (𝟙 T) (Category.id_comp t) f = f :=
  Subtype.ext ((congrArg (· ≫ f.1) (bcL_id t)).trans (Category.id_comp _))

lemma EqMor.pull_pull {T' T'' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)}
    {t'' : T'' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T) (ht : h ≫ t = t') (h' : T'' ⟶ T')
    (ht' : h' ≫ t' = t'') (f : EqMor t aX) :
    EqMor.pull t' aX h' ht' (EqMor.pull t aX h ht f) =
      EqMor.pull t aX (h' ≫ h) (by rw [Category.assoc, ht, ht']) f :=
  Subtype.ext (by rw [EqMor.pull_val, EqMor.pull_val, EqMor.pull_val, bcL_comp t h ht h' ht',
    Category.assoc])

lemma eqMorRestrictEquiv_pull (V : X.Opens) (hV : aX.IsStable V) {T' : Scheme.{u}}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T) (ht : h ≫ t = t')
    (f : EqMor t (aX.restrict V hV)) :
    (eqMorRestrictEquiv t' aX V hV (EqMor.pull t _ h ht f)).1 =
      EqMor.pull t aX h ht (eqMorRestrictEquiv t aX V hV f).1 :=
  Subtype.ext (Category.assoc _ _ _)

/-- **The descended functor** on `(Sch/k)`: `T ↦` the `G`-equivariant `L`-morphisms `T_L ⟶ X`. -/
def descFunctor : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type u where
  obj T := EqMor T.unop.hom aX
  map {T _} a := TypeCat.ofHom fun f ↦ EqMor.pull T.unop.hom aX a.unop.left (Over.w a.unop) f
  map_id _ := ConcreteCategory.hom_ext _ _ fun f ↦ EqMor.pull_id _ aX f
  map_comp _ _ := ConcreteCategory.hom_ext _ _ fun f ↦ (EqMor.pull_pull _ aX _ _ _ _ f).symm

lemma descFunctor_map_homMk {T' : Scheme.{u}} (h : T' ⟶ T) (f : EqMor t aX) :
    (descFunctor aX).map (Over.homMk h rfl : Over.mk (h ≫ t) ⟶ Over.mk t).op f =
      EqMor.pull t aX h rfl f := rfl

/-- The predicate "`T_L ⟶ X` lands in `V`" on `overSigma (descFunctor aX)`. -/
def landsIn (V : X.Opens) (T : Scheme.{u}) (x : (overSigma (descFunctor aX)).obj (op T)) : Prop :=
  Set.range x.2.1 ⊆ (V : Set X)

lemma overSigma_descFunctor_map {T' : Scheme.{u}} (h : T' ⟶ T) (f : EqMor t aX) :
    (overSigma (descFunctor aX)).map h.op ⟨t, f⟩ = ⟨h ≫ t, EqMor.pull t aX h rfl f⟩ := rfl

section Sheaf

/-- The comparison `(U_a)_L ×_{T_L} (U_b)_L ⟶ (U_a ×_T U_b)_L`. -/
def pairL {T Ua Ub : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of k)) (ia : Ua ⟶ T) (ib : Ub ⟶ T) :
    pullback (bcL (L := L) g ia rfl) (bcL (L := L) g ib rfl) ⟶
      pullback (pullback.fst ia ib ≫ ia ≫ g) (sL k L) :=
  pullback.lift (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
      (pullback.snd _ _ ≫ pullback.fst _ _) (by
        have := pullback.condition (f := bcL (L := L) g ia rfl) (g := bcL (L := L) g ib rfl)
        have := congrArg (· ≫ pullback.fst g (sL k L)) this
        simp only [Category.assoc, bcL_fst] at this
        simpa only [Category.assoc] using this))
    (pullback.fst _ _ ≫ pullback.snd _ _) (by
      rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])

lemma pairL_fst {T Ua Ub : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of k)) (ia : Ua ⟶ T)
    (ib : Ub ⟶ T) :
    pairL g ia ib ≫ bcL (L := L) (ia ≫ g) (pullback.fst ia ib) rfl = pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcL_fst, pairL, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, bcL_snd, pairL, pullback.lift_snd]

lemma pairL_snd {T Ua Ub : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of k)) (ia : Ua ⟶ T)
    (ib : Ub ⟶ T) :
    pairL g ia ib ≫ bcL (L := L) (ib ≫ g) (pullback.snd ia ib)
      (by exact (pullback.condition_assoc g).symm) = pullback.snd _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcL_fst, pairL, pullback.lift_fst_assoc, pullback.lift_snd]
  · rw [Category.assoc, bcL_snd, pairL, pullback.lift_snd]
    have := congrArg (· ≫ pullback.snd g (sL k L))
      (pullback.condition (f := bcL (L := L) g ia rfl) (g := bcL (L := L) g ib rfl))
    simpa only [Category.assoc, bcL_snd] using this

/-- **The descended functor is a Zariski sheaf** (equivariant morphisms glue). -/
theorem isSheafOver_descFunctor : IsSheafOver.{u} (descFunctor aX) := by
  intro T g 𝓤 y hy
  let 𝓥 : (pullback g (sL k L)).OpenCover := Scheme.Cover.mkOfCovers 𝓤.I₀
    (fun a ↦ pullback (𝓤.f a ≫ g) (sL k L)) (fun a ↦ bcL g (𝓤.f a) rfl) (fun z ↦ by
      obtain ⟨a, u, hu⟩ := 𝓤.exists_eq (pullback.fst g (sL k L) z)
      obtain ⟨w, hw⟩ := mem_range_bcL g (𝓤.f a) rfl z u hu
      exact ⟨a, w, hw⟩)
  have hcompat : ∀ a b, pullback.fst (𝓥.f a) (𝓥.f b) ≫ (y a).1 =
      pullback.snd (𝓥.f a) (𝓥.f b) ≫ (y b).1 := by
    intro a b
    have h := congrArg Subtype.val (hy a b)
    change bcL (𝓤.f a ≫ g) (pullback.fst (𝓤.f a) (𝓤.f b)) rfl ≫ (y a).1 =
      bcL (𝓤.f b ≫ g) (pullback.snd (𝓤.f a) (𝓤.f b))
        (by exact (pullback.condition_assoc g).symm) ≫ (y b).1 at h
    change pullback.fst (bcL g (𝓤.f a) rfl) (bcL g (𝓤.f b) rfl) ≫ (y a).1 =
      pullback.snd (bcL g (𝓤.f a) rfl) (bcL g (𝓤.f b) rfl) ≫ (y b).1
    rw [← pairL_fst g (𝓤.f a) (𝓤.f b), ← pairL_snd g (𝓤.f a) (𝓤.f b), Category.assoc,
      Category.assoc, h]
  let z₀ := 𝓥.glueMorphisms (fun a ↦ (y a).1) hcompat
  have hz₀ (a : 𝓤.I₀) : bcL g (𝓤.f a) rfl ≫ z₀ = (y a).1 :=
    𝓥.ι_glueMorphisms (fun a ↦ (y a).1) hcompat a
  refine ⟨⟨z₀, 𝓥.hom_ext _ _ fun a ↦ ?_, fun γ ↦ 𝓥.hom_ext _ _ fun a ↦ ?_⟩,
    fun a ↦ Subtype.ext (hz₀ a), fun z hz ↦ Subtype.ext (𝓥.hom_ext _ _ fun a ↦ ?_)⟩
  · change bcL g (𝓤.f a) rfl ≫ z₀ ≫ q = bcL g (𝓤.f a) rfl ≫ pullback.snd g (sL k L)
    rw [reassoc_of% hz₀ a, bcL_snd]
    exact (y a).2.1
  · change bcL g (𝓤.f a) rfl ≫ (baseAct g).act γ ≫ z₀ = bcL g (𝓤.f a) rfl ≫ z₀ ≫ aX.act γ
    rw [← baseAct_bcL_assoc, hz₀ a, reassoc_of% hz₀ a]
    exact (y a).2.2 γ
  · change bcL g (𝓤.f a) rfl ≫ z.1 = bcL g (𝓤.f a) rfl ≫ z₀
    rw [hz₀ a]
    exact congrArg Subtype.val (hz a)

end Sheaf

section Piece

variable [FiniteDimensional k L] [IsGalois k L] (V : X.Opens) (hVa : IsAffineOpen V)
  (hV : aX.IsStable V)

/-- The universal element over the descent `Spec Γ(V)^G` of a stable affine open `V`. -/
def pieceξ : (overSigma (descFunctor aX)).obj (op (descAff (aX.restrict V hV))) :=
  ⟨descAffHom (aX.restrict V hV), (eqMorRestrictEquiv _ aX V hV
    (haveI : IsAffine V.toScheme := hVa; univEqMor (aX.restrict V hV))).1⟩

include hVa in
lemma piece_injective [IsAffine T] :
    Function.Injective fun a : T ⟶ descAff (aX.restrict V hV) ↦
      (overSigma (descFunctor aX)).map a.op (pieceξ aX V hVa hV) := by
  haveI : IsAffine V.toScheme := hVa
  intro a b hab
  have h1 : a ≫ descAffHom _ = b ≫ descAffHom _ := congrArg Sigma.fst hab
  have h2 := (overSigma_mk_eq_iff (descFunctor aX) h1 _ _).mp hab
  change EqMor.pull _ aX (𝟙 T) _ (EqMor.pull _ aX a rfl (eqMorRestrictEquiv _ aX V hV
    (univEqMor (aX.restrict V hV))).1) = EqMor.pull _ aX b rfl (eqMorRestrictEquiv _ aX V hV
    (univEqMor (aX.restrict V hV))).1 at h2
  rw [EqMor.pull_pull, ← eqMorRestrictEquiv_pull, ← eqMorRestrictEquiv_pull] at h2
  have h3 := congrArg (affineDescentEquiv (b ≫ descAffHom _) (aX.restrict V hV))
    ((eqMorRestrictEquiv _ aX V hV).injective (Subtype.ext h2))
  rw [affineDescentEquiv_pull, affineDescentEquiv_pull] at h3
  exact (Category.id_comp a).symm.trans (congrArg Subtype.val h3)

lemma range_subset_of_comp {Y Z : Scheme.{u}} (f : Y ⟶ Z) (V : X.Opens) (g : Z ⟶ V.toScheme) :
    Set.range (f ≫ g ≫ V.ι) ⊆ (V : Set X) := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (g (f y)).2

include hVa in
lemma piece_range_aux [IsAffine T] (f : EqMor t aX) (hf : Set.range f.1 ⊆ (V : Set X)) :
    ∃ a : T ⟶ descAff (aX.restrict V hV),
      (overSigma (descFunctor aX)).map a.op (pieceξ aX V hVa hV) = ⟨t, f⟩ := by
  haveI : IsAffine V.toScheme := hVa
  let f' := (eqMorRestrictEquiv t aX V hV).symm ⟨f, hf⟩
  have hf' := eq_pull_univEqMor t (aX.restrict V hV) f'
  refine ⟨(affineDescentEquiv t (aX.restrict V hV) f').1, ?_⟩
  refine (overSigma_mk_eq_iff (descFunctor aX)
    (affineDescentEquiv t (aX.restrict V hV) f').2 _ _).mpr ?_
  change EqMor.pull _ aX (𝟙 T) _ (EqMor.pull _ aX _ rfl (eqMorRestrictEquiv _ aX V hV
    (univEqMor (aX.restrict V hV))).1) = f
  rw [EqMor.pull_pull, EqMor.pull_congr _ aX (Category.id_comp _) _
    (affineDescentEquiv t (aX.restrict V hV) f').2, ← eqMorRestrictEquiv_pull, ← hf',
    Equiv.apply_symm_apply]

include hVa in
lemma piece_range [IsAffine T] (x : (overSigma (descFunctor aX)).obj (op T)) :
    landsIn aX V T x ↔ ∃ a : T ⟶ descAff (aX.restrict V hV),
      (overSigma (descFunctor aX)).map a.op (pieceξ aX V hVa hV) = x := by
  constructor
  · exact piece_range_aux x.1 aX V hVa hV x.2
  · rintro ⟨a, rfl⟩
    exact range_subset_of_comp _ V _

end Piece

section Open

/-- The open of `T` over which `f : T_L ⟶ X` lands in `V`: the image of `f⁻¹(V)` in `T`. -/
def openOf [FiniteDimensional k L] (f : EqMor t aX) (V : X.Opens) : T.Opens :=
  ⟨pullback.fst t (sL k L) '' (f.1 ⁻¹' (V : Set X)),
    (pullback.fst t (sL k L)).isOpenMap _ (V.2.preimage f.1.continuous)⟩

variable [FiniteDimensional k L] [IsGalois k L]

/-- **The locus where an equivariant morphism lands in a stable open is open**: for `T` affine
and any `h : T' ⟶ T`, `h^* f` lands in `V` iff `h` factors through `openOf f V`. -/
lemma landsIn_map_iff [IsAffine T] (f : EqMor t aX) {V : X.Opens} (hV : aX.IsStable V)
    {T' : Scheme.{u}} (h : T' ⟶ T) :
    landsIn aX V T' ((overSigma (descFunctor aX)).map h.op ⟨t, f⟩) ↔
      Set.range h ⊆ (openOf t aX f V : Set T) := by
  change Set.range (bcL t h rfl ≫ f.1) ⊆ (V : Set X) ↔ _
  constructor
  · rintro H _ ⟨τ, rfl⟩
    obtain ⟨z', rfl⟩ := (pullback.fst (h ≫ t) (sL k L)).surjective τ
    refine ⟨bcL t h rfl z', H ⟨z', rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, bcL_fst, Scheme.Hom.comp_apply]
  · rintro H _ ⟨z', rfl⟩
    obtain ⟨w, hw, hw'⟩ := H ⟨pullback.fst (h ≫ t) (sL k L) z', rfl⟩
    rw [← Scheme.Hom.comp_apply, ← bcL_fst t h rfl, Scheme.Hom.comp_apply] at hw'
    obtain ⟨g, hg⟩ := exists_baseAct_apply_eq t w _ hw'
    rw [Scheme.Hom.comp_apply, ← hg, ← Scheme.Hom.comp_apply, f.2.2 g, Scheme.Hom.comp_apply]
    exact aX.mem_of_isStable hV g hw

end Open

section Rep

/-- The descended functor as a Zariski sheaf on all schemes. -/
def descSheaf : Sheaf Scheme.zariskiTopology.{u} (Type u) where
  obj := overSigma (descFunctor aX)
  property := (isSheaf_iff_isSheaf_of_type _ _).mpr
    (isSheaf_overSigma_of_small (isSheafOver_descFunctor aX))

lemma isLocalPredicate_landsIn (V : X.Opens) :
    Scheme.OpenSubfunctor.IsLocalPredicate (descSheaf aX) (landsIn aX V) := by
  refine ⟨fun {T T'} h x hx ↦ ?_, fun {T} x H ↦ ?_⟩
  · rintro _ ⟨z, rfl⟩
    change (bcL x.1 h rfl ≫ x.2.1) z ∈ (V : Set X)
    rw [Scheme.Hom.comp_apply]
    exact hx ⟨_, rfl⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨U, hτ, hU⟩ := H (pullback.fst x.1 (sL k L) z)
    obtain ⟨w, rfl⟩ := mem_range_bcL x.1 U.ι rfl z ⟨_, hτ⟩ rfl
    have := hU ⟨w, rfl⟩
    change (bcL x.1 U.ι rfl ≫ x.2.1) w ∈ (V : Set X) at this
    rwa [Scheme.Hom.comp_apply] at this

variable [FiniteDimensional k L] [IsGalois k L]

/-- **Galois descent of schemes**: if `X` (over `Spec L`, with a semilinear `Gal(L/k)`-action)
is covered by `G`-stable affine opens, the descended functor `T ↦ Hom^G_L(T_L, X)` on schemes
over `k` is representable. -/
theorem isRepresentable_descFunctor
    (hcov : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ aX.IsStable V ∧ x ∈ V) :
    (overSigma (descFunctor aX)).IsRepresentable := by
  let ι := {V : X.Opens // IsAffineOpen V ∧ aX.IsStable V}
  refine Scheme.OpenSubfunctor.isRepresentable_of_isAffine (F := descSheaf aX) (ι := ι)
    (p := fun i ↦ landsIn aX i.1) (fun i ↦ isLocalPredicate_landsIn aX i.1)
    (fun i T _ x ↦ ⟨openOf x.1 aX x.2 i.1, fun T' _ h ↦ landsIn_map_iff x.1 aX x.2 i.2.2 h⟩)
    (Y := fun i ↦ descAff (aX.restrict i.1 i.2.2)) (fun i ↦ pieceξ aX i.1 i.2.1 i.2.2)
    (fun i T _ ↦ piece_injective aX i.1 i.2.1 i.2.2)
    (fun i T _ x ↦ piece_range aX i.1 i.2.1 i.2.2 x)
    (fun T _ x τ ↦ ?_)
  obtain ⟨z, rfl⟩ := (pullback.fst x.1 (sL k L)).surjective τ
  obtain ⟨V, hVa, hVs, hz⟩ := hcov (x.2.1 z)
  exact ⟨⟨V, hVa, hVs⟩, openOf x.1 aX x.2 V,
    fun T' _ h ↦ landsIn_map_iff x.1 aX x.2 hVs h, ⟨z, hz, rfl⟩⟩

/-- **The Galois descent of `X`**: the `k`-scheme representing `T ↦ Hom^G_L(T_L, X)`. -/
def descScheme (hcov : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ aX.IsStable V ∧ x ∈ V) :
    Over (Spec (CommRingCat.of k)) :=
  haveI := isRepresentable_descFunctor aX hcov
  OverSigmaRep.over (overSigma (descFunctor aX)).representableBy

/-- `descScheme` represents the descended functor: `Hom_k(T, X₀) ≃ Hom^G_L(T_L, X)`. -/
def descRepresentableBy
    (hcov : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ aX.IsStable V ∧ x ∈ V) :
    (descFunctor aX).RepresentableBy (descScheme aX hcov) :=
  haveI := isRepresentable_descFunctor aX hcov
  OverSigmaRep.representableBy (overSigma (descFunctor aX)).representableBy

end Rep

end CurvesJacobian.GaloisDescent
