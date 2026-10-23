/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.KummerFaithful
import ContinuousKummerTheory.Kummer.Faithful

/-!
# The multiplicative group `𝔾_m` and "Kummer-faithful ⟹ torally Kummer-faithful"

Mochizuki, *Topics in Absolute Anabelian Geometry III* ([AbsTopIII]), Definition 1.5
(`T3` l.1807–1836) defines Kummer-faithful and torally Kummer-faithful fields, and Remark 1.5.3(ii)
(`T3` l.1888–1889) observes that "Kummer-faithful ⟹ torally Kummer-faithful" follows from the
definitions. Here we prove this for `CurvesJacobian.IsKummerFaithful` (semi-abelian varieties as
group schemes) and the `𝔾_m`-form `KummerTheory.IsTorallyKummerFaithful` of
`ContinuousKummerTheory`.

Mathlib has no `𝔾_m`, so we construct it.

* `CurvesJacobian.GmScheme K`: `𝔾_{m,K} = Spec K[T, T⁻¹]` as a scheme over `Spec K`.
* `CurvesJacobian.GmScheme.representableBy`: `𝔾_{m,K}` represents `X ↦ Γ(X, 𝒪_X)ˣ` on `(Sch/K)`
  (`Hom_K(X, Spec K[T, T⁻¹]) ≃ {φ : K[T, T⁻¹] → Γ(X, 𝒪_X) over K} ≃ Γ(X, 𝒪_X)ˣ`); hence
  `𝔾_{m,K}` is a commutative group scheme (`GrpObj.ofRepresentableBy`) and
  `CurvesJacobian.GmScheme.homMulEquiv : Hom_K(T, 𝔾_{m,K}) ≃* Γ(T, 𝒪_T)ˣ`.
* `CurvesJacobian.GmScheme.isTorus`: `𝔾_{m,K}` is a torus (`r = 1`).
* `CurvesJacobian.GmScheme.isSemiAbelianVariety`: `𝔾_{m,K}` is a semi-abelian variety
  (`0 → 𝔾_m → 𝔾_m → Spec K → 0`; `CurvesJacobian.isAbelianVariety_tensorUnit`).
* **`CurvesJacobian.IsKummerFaithful.isTorallyKummerFaithful`**: [AbsTopIII] Remark 1.5.3(ii),
  via the injective group homomorphism `Kˣ → 𝔾_m(K)`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
  MonObj LaurentPolynomial

universe u

noncomputable section

namespace CurvesJacobian

namespace GmScheme

section Laurent

variable {K B : Type u} [Field K] [CommRing B]

/-- The ring homomorphism `K[T, T⁻¹] → B` extending `s` and sending `T` to the unit `v`. -/
def laurentLift (s : K →+* B) (v : Bˣ) : K[T;T⁻¹] →+* B :=
  AddMonoidAlgebra.liftNCRingHom s ((Units.coeHom B).comp (zpowersHom Bˣ v))
    fun _ _ ↦ Commute.all _ _

lemma laurentLift_single (s : K →+* B) (v : Bˣ) (n : ℤ) (a : K) :
    laurentLift s v (AddMonoidAlgebra.single n a) = s a * ((v ^ n : Bˣ) : B) :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

/-- **The universal property of `K[T, T⁻¹]`**: ring homomorphisms `K[T, T⁻¹] → B` extending a
given `s : K → B` correspond to units of `B` (`φ ↦ φ(T)`). -/
def laurentHomEquiv (s : K →+* B) :
    {φ : K[T;T⁻¹] →+* B // φ.comp (algebraMap K K[T;T⁻¹]) = s} ≃ Bˣ where
  toFun φ := Units.mkOfMulEqOne (φ.1 (T 1)) (φ.1 (T (-1))) (by
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one])
  invFun v := ⟨laurentLift s v, by
    ext a
    exact (laurentLift_single s v 0 a).trans (by simp)⟩
  left_inv φ := by
    refine Subtype.ext (AddMonoidAlgebra.ringHom_ext (fun a ↦ ?_) fun n ↦ ?_)
    · rw [laurentLift_single, zpow_zero, Units.val_one, _root_.mul_one]
      exact (RingHom.congr_fun φ.2 a).symm
    · rw [laurentLift_single, map_one, _root_.one_mul]
      change ((Units.coeHom B).comp (zpowersHom Bˣ _)) (Multiplicative.ofAdd n) =
        (φ.1.toMonoidHom.comp (AddMonoidAlgebra.of K ℤ)) (Multiplicative.ofAdd n)
      exact DFunLike.congr_fun (MonoidHom.ext_mint (by simp)) _
  right_inv v := by
    ext
    change laurentLift s v (AddMonoidAlgebra.single 1 1) = v
    rw [laurentLift_single, map_one, _root_.one_mul, zpow_one]

@[simp]
lemma coe_laurentHomEquiv (s : K →+* B) (φ) : (laurentHomEquiv s φ : B) = φ.1 (T 1) := rfl

end Laurent

section SpecHom

/-- Morphisms to an affine scheme: `Hom(X, Spec R) ≃ Hom(R, Γ(X, 𝒪_X))`. -/
def specHomEquiv (X : Scheme.{u}) (R : CommRingCat.{u}) : (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) where
  toFun f := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  invFun φ := X.toSpecΓ ≫ Spec.map φ
  left_inv f := by
    simp only [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  right_inv φ := by
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

lemma specHomEquiv_comp {X Y : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec R) :
    specHomEquiv X R (g ≫ f) = specHomEquiv Y R f ≫ g.appTop := by
  simp [specHomEquiv]

lemma specHomEquiv_comp_specMap {X : Scheme.{u}} {R A : CommRingCat.{u}} (f : X ⟶ Spec A)
    (ψ : R ⟶ A) : specHomEquiv X R (f ≫ Spec.map ψ) = ψ ≫ specHomEquiv X A f := by
  simp only [specHomEquiv, Equiv.coe_fn_mk, Scheme.Hom.comp_appTop,
    Scheme.ΓSpecIso_inv_naturality_assoc]

end SpecHom

end GmScheme

variable (K : Type u) [Field K]

/-- **The multiplicative group** `𝔾_{m,K} = Spec K[T, T⁻¹]` over a field `K`. -/
def GmScheme : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])))

namespace GmScheme

variable {K}

/-- The structure map `K → Γ(X, 𝒪_X)` of a `K`-scheme `X`. -/
def structHom (X : Over (Spec (CommRingCat.of K))) : K →+* Γ(X.left, ⊤) :=
  (specHomEquiv X.left _ X.hom).hom

/-- `Hom_K(X, 𝔾_{m,K}) ≃ {φ : K[T, T⁻¹] → Γ(X, 𝒪_X) over K}`. -/
def homEquivRingHom (X : Over (Spec (CommRingCat.of K))) :
    (X ⟶ GmScheme K) ≃
      {φ : K[T;T⁻¹] →+* Γ(X.left, ⊤) // φ.comp (algebraMap K K[T;T⁻¹]) = structHom X} where
  toFun f := ⟨(specHomEquiv _ _ f.left).hom, by
    have := specHomEquiv_comp_specMap f.left (CommRingCat.ofHom (algebraMap K K[T;T⁻¹]))
    exact congrArg CommRingCat.Hom.hom (this.symm.trans (congrArg (specHomEquiv _ _) (Over.w f)))⟩
  invFun φ := Over.homMk ((specHomEquiv _ _).symm (CommRingCat.ofHom φ.1)) (by
    apply (specHomEquiv _ _).injective
    change specHomEquiv _ _ (_ ≫ Spec.map _) = _
    rw [specHomEquiv_comp_specMap, Equiv.apply_symm_apply]
    ext1
    exact φ.2)
  left_inv f := by
    ext1
    simp
  right_inv φ := by
    ext1
    simp

/-- **`𝔾_{m,K}` represents the units**: `Hom_K(X, 𝔾_{m,K}) ≃ Γ(X, 𝒪_X)ˣ`. -/
def homEquivUnits (X : Over (Spec (CommRingCat.of K))) : (X ⟶ GmScheme K) ≃ (Γ(X.left, ⊤))ˣ :=
  (homEquivRingHom X).trans (laurentHomEquiv (structHom X))

lemma coe_homEquivUnits {X : Over (Spec (CommRingCat.of K))} (f : X ⟶ GmScheme K) :
    (homEquivUnits X f : Γ(X.left, ⊤)) = (specHomEquiv _ _ f.left).hom (T 1) := rfl

variable (K) in
/-- The presheaf of groups `X ↦ Γ(X, 𝒪_X)ˣ` on `(Sch/K)`. -/
@[simps]
def unitsFunctor : (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ CommGrpCat.{u} where
  obj X := CommGrpCat.of (Γ(X.unop.left, ⊤))ˣ
  map f := CommGrpCat.ofHom (Units.map f.unop.left.appTop.hom.toMonoidHom)
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

variable (K) in
/-- **`𝔾_{m,K}` represents `X ↦ Γ(X, 𝒪_X)ˣ`.** -/
def representableBy : (unitsFunctor K ⋙ forget CommGrpCat).RepresentableBy (GmScheme K) where
  homEquiv {X} := homEquivUnits X
  homEquiv_comp {X X'} f g := by
    apply Units.ext
    change (homEquivUnits X (f ≫ g) : Γ(X.left, ⊤)) =
      f.left.appTop.hom (homEquivUnits X' g : Γ(X'.left, ⊤))
    exact congrArg (fun φ ↦ φ.hom (T 1)) (specHomEquiv_comp f.left g.left)

/-- **`𝔾_{m,K}` is a group scheme.** -/
instance : GrpObj (GmScheme K) :=
  GrpObj.ofRepresentableBy _ (unitsFunctor K ⋙ forget₂ CommGrpCat GrpCat) (representableBy K)

/-- **`𝔾_{m,K}` is commutative.** -/
instance : IsCommMonObj (GmScheme K) :=
  IsCommMonObj.ofRepresentableBy _ (unitsFunctor K ⋙ forget₂ CommGrpCat CommMonCat)
    (representableBy K)

/-- **`Hom_K(X, 𝔾_{m,K}) ≃* Γ(X, 𝒪_X)ˣ` as groups.** -/
def homMulEquiv (X : Over (Spec (CommRingCat.of K))) : (X ⟶ GmScheme K) ≃* (Γ(X.left, ⊤))ˣ where
  toEquiv := homEquivUnits X
  map_mul' := ((yonedaGrpObjIsoOfRepresentableBy (GmScheme K)
    (unitsFunctor K ⋙ forget₂ CommGrpCat GrpCat) (representableBy K)).hom.app (op X)).hom.map_mul

lemma homMulEquiv_comp {X X' : Over (Spec (CommRingCat.of K))} (f : X ⟶ X') (g : X' ⟶ GmScheme K) :
    homMulEquiv X (f ≫ g) = Units.map f.left.appTop.hom.toMonoidHom (homMulEquiv X' g) :=
  (representableBy K).homEquiv_comp f g

/-- **`𝔾_{m,K}` is a torus** (of dimension `1`). -/
theorem isTorus : IsTorus (GmScheme K) :=
  ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, inferInstance, 1,
    fun _ ↦ (homMulEquiv _).trans (MulEquiv.funUnique (Fin 1) _).symm,
    fun _ _ _ x ↦ funext fun _ ↦ homMulEquiv_comp _ x⟩

end GmScheme

/-- An isomorphism of schemes is geometrically connected. -/
lemma geometricallyConnected_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyConnected f :=
  ⟨fun _ _ _ _ _ snd h ↦ by
    haveI := h.isIso_snd_of_isIso
    exact (Scheme.homeoOfIso (asIso snd)).connectedSpace_iff.mpr inferInstance⟩

/-- **The trivial group scheme `Spec K` is an abelian variety** (of dimension `0`). -/
theorem isAbelianVariety_tensorUnit :
    IsAbelianVariety (𝟙_ (Over (Spec (CommRingCat.of K)))) where
  isProper := inferInstanceAs (IsProper (𝟙 _))
  smooth := inferInstanceAs (Smooth (𝟙 _))
  geometricallyConnected := geometricallyConnected_of_isIso (𝟙 _)

namespace GmScheme

variable {K}

/-- **`𝔾_{m,K}` is a semi-abelian variety** (`0 → 𝔾_m → 𝔾_m → Spec K → 0`). -/
theorem isSemiAbelianVariety : IsSemiAbelianVariety (GmScheme K) where
  isCommMonObj := inferInstance
  nonempty_extension := ⟨{
    T := GmScheme K
    B := 𝟙_ _
    i := 𝟙 (GmScheme K)
    p := toUnit (GmScheme K)
    isTorus := isTorus
    isAbelianVariety := isAbelianVariety_tensorUnit K
    isPullback := by
      rw [show η[𝟙_ (Over (Spec (CommRingCat.of K)))] = 𝟙 _ from toUnit_unique _ _]
      exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
    flat := by
      change Flat (Spec.map _)
      rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
        RingHom.flat_algebraMap_iff]
      infer_instance
    surjective := by
      change Surjective (Spec.map _)
      exact ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
    locallyOfFinitePresentation := by
      change LocallyOfFinitePresentation (Spec.map _)
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation),
        CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
      exact Algebra.FinitePresentation.of_finiteType.mp inferInstance }⟩

end GmScheme

/-- **Kummer-faithful ⟹ torally Kummer-faithful** ([AbsTopIII] Remark 1.5.3(ii)): applied to the
semi-abelian variety `𝔾_m` over a finite extension `L` of `k`, Kummer-faithfulness of `k` says
that `⋂_{N ≥ 1} (Lˣ)^N = {1}`, via the injective group homomorphism
`Lˣ → Γ(Spec L, 𝒪)ˣ ≃ 𝔾_m(L)`. -/
theorem IsKummerFaithful.isTorallyKummerFaithful {k : Type u} [Field k]
    (hk : IsKummerFaithful k) : KummerTheory.IsTorallyKummerFaithful k := by
  intro L _ _ _ x hx
  let φ : Lˣ →* (𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ GmScheme L) :=
    (GmScheme.homMulEquiv _).symm.toMonoidHom.comp (Units.map (GmScheme.structHom _).toMonoidHom)
  haveI : Nontrivial Γ((𝟙_ (Over (Spec (CommRingCat.of L)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  have hinj : Function.Injective (GmScheme.structHom (𝟙_ (Over (Spec (CommRingCat.of L))))) :=
    RingHom.injective _
  have hφ : Function.Injective φ :=
    (GmScheme.homMulEquiv _).symm.injective.comp (Units.map_injective hinj)
  apply hφ
  rw [map_one]
  exact hk L (GmScheme L) GmScheme.isSemiAbelianVariety (φ x) fun N hN ↦ by
    obtain ⟨y, hy⟩ := hx N hN
    exact ⟨φ y, by rw [← map_pow, hy]⟩

end CurvesJacobian
