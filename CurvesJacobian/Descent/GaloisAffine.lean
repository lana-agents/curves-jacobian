/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Descent.GaloisHom
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Galois descent of affine schemes

Let `L / k` be a finite Galois extension with group `G`. A *semilinear `G`-action* on a scheme
`X` over `Spec L` (`CurvesJacobian.GaloisDescent.GalAction`) is an action of `G` on `X` by
automorphisms `act g` lying over `Spec(g) : Spec L ⟶ Spec L`.

For a scheme `T` over `k`, `T_L = T ×_k L` carries the action `id × Spec(g)` (`baseAct`). Let `U`
be an affine scheme over `Spec L` with a semilinear action and `A = Γ(U)`, with the induced
semilinear action on `A` (`GalAction.ringAct`).

* **`CurvesJacobian.GaloisDescent.affineDescentEquiv`**: for an affine `k`-scheme `T`, the
  `G`-equivariant `L`-morphisms `T_L ⟶ U` (`EqMor`) correspond to the `k`-morphisms
  `T ⟶ Spec A^G` (`descAff`); i.e. `Spec A^G` is the Galois descent of `U`.
* `CurvesJacobian.GaloisDescent.affineDescentEquiv_pull`, `eq_pull_univEqMor`: the
  correspondence is induced by the universal equivariant morphism `(Spec A^G)_L ⟶ U`
  (`univEqMor`; pull it back along `T ⟶ Spec A^G`), which is an isomorphism
  (`isIso_univEqMor`, Speiser).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "SL" => Spec (CommRingCat.of L)

variable (k L) in
/-- `Spec L ⟶ Spec k`. -/
abbrev sL : SL ⟶ Sk := Spec.map (CommRingCat.ofHom (algebraMap k L))

/-- `Spec(g) : Spec L ⟶ Spec L` for `g ∈ Gal(L/k)`. -/
abbrev specGal (g : Gal(L/k)) : SL ⟶ SL := Spec.map (CommRingCat.ofHom (g : L →+* L))

@[reassoc (attr := simp)]
lemma specGal_comp_sL (g : Gal(L/k)) : specGal g ≫ sL k L = sL k L := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact g.commutes r

lemma specGal_mul (g h : Gal(L/k)) : specGal g ≫ specGal h = specGal (g * h) := by
  rw [← Spec.map_comp]
  rfl

lemma specGal_one : specGal (1 : Gal(L/k)) = 𝟙 SL := by
  rw [← Spec.map_id]
  rfl

/-- A **semilinear action** of `Gal(L/k)` on a scheme `X` over `Spec L`: automorphisms `act g`
of `X` lying over `Spec(g)`, with `act 1 = 𝟙` and `act g ≫ act h = act (g * h)`. -/
structure GalAction (X : Scheme.{u}) (q : X ⟶ Spec (CommRingCat.of L)) where
  /-- The automorphism attached to `g`. -/
  act : Gal(L/k) → (X ⟶ X)
  act_comp (g : Gal(L/k)) : act g ≫ q = q ≫ specGal g
  act_one : act 1 = 𝟙 X
  act_mul (g h : Gal(L/k)) : act g ≫ act h = act (g * h)

attribute [reassoc] GalAction.act_comp GalAction.act_mul

namespace GalAction

variable {X : Scheme.{u}} {q : X ⟶ Spec (CommRingCat.of L)} (a : GalAction (k := k) X q)

lemma act_inv_act (g : Gal(L/k)) : a.act g⁻¹ ≫ a.act g = 𝟙 X := by
  rw [a.act_mul, inv_mul_cancel, a.act_one]

lemma act_act_inv (g : Gal(L/k)) : a.act g ≫ a.act g⁻¹ = 𝟙 X := by
  rw [a.act_mul, mul_inv_cancel, a.act_one]

/-- The `L`-algebra structure on `Γ(X)` given by `q`. -/
abbrev algL : Algebra L Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ q.appTop).hom.toAlgebra

/-- The induced action on global sections: `ρ g = (act g)^*`. -/
def ringAct : Gal(L/k) →* RingAut Γ(X, ⊤) where
  toFun g := RingEquiv.ofRingHom (a.act g).appTop.hom (a.act g⁻¹).appTop.hom
    (by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, act_act_inv, Scheme.Hom.id_appTop]
      rfl)
    (by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, act_inv_act, Scheme.Hom.id_appTop]
      rfl)
  map_one' := by
    apply RingEquiv.ext
    intro x
    change (a.act 1).appTop.hom x = x
    rw [a.act_one, Scheme.Hom.id_appTop]
    rfl
  map_mul' g h := by
    apply RingEquiv.ext
    intro x
    change (a.act (g * h)).appTop.hom x = (a.act g).appTop.hom ((a.act h).appTop.hom x)
    rw [← a.act_mul, Scheme.Hom.comp_appTop]
    rfl

lemma ringAct_apply (g : Gal(L/k)) (x : Γ(X, ⊤)) : a.ringAct g x = (a.act g).appTop.hom x := rfl

lemma ringAct_algebraMap (g : Gal(L/k)) (l : L) :
    letI := algL (q := q)
    a.ringAct g (algebraMap L Γ(X, ⊤) l) = algebraMap L Γ(X, ⊤) (g l) := by
  letI := algL (q := q)
  change ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ q.appTop ≫ (a.act g).appTop).hom l =
    ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ q.appTop).hom (g l)
  rw [← Scheme.Hom.comp_appTop, a.act_comp, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end GalAction

section Base

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

/-- The action `id × Spec(g)` on `T_L = T ×_k L`. -/
def baseAct : GalAction (k := k) (pullback t (sL k L)) (pullback.snd t (sL k L)) where
  act g := pullback.lift (pullback.fst t (sL k L)) (pullback.snd t (sL k L) ≫ specGal g)
    (by rw [pullback.condition, Category.assoc, specGal_comp_sL])
  act_comp g := pullback.lift_snd _ _ _
  act_one := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, specGal_one, Category.comp_id, Category.id_comp]
  act_mul g h := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.assoc, specGal_mul]

@[reassoc (attr := simp)]
lemma baseAct_fst (g : Gal(L/k)) :
    (baseAct t).act g ≫ pullback.fst t (sL k L) = pullback.fst t (sL k L) :=
  pullback.lift_fst _ _ _

/-- `Γ(T)` as a `k`-algebra. -/
abbrev algT : Algebra k Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom.toAlgebra

/-- `Γ(T_L)` as a `Γ(T)`-algebra. -/
abbrev algTL : Algebra Γ(T, ⊤) Γ(pullback t (sL k L), ⊤) :=
  (pullback.fst t (sL k L)).appTop.hom.toAlgebra

end Base

section Sections

/-- `Γ(X)` for `q : X ⟶ Spec L`, as an `L`-algebra (and a `k`-algebra through `L`). -/
def SecU {X : Scheme.{u}} (_q : X ⟶ Spec (CommRingCat.of L)) : Type u := Γ(X, ⊤)

variable {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of L))

instance : CommRing (SecU q) := inferInstanceAs (CommRing Γ(X, ⊤))

instance : Algebra L (SecU q) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ q.appTop).hom.toAlgebra

instance : Algebra k (SecU q) := ((algebraMap L (SecU q)).comp (algebraMap k L)).toAlgebra

instance : IsScalarTower k L (SecU q) := .of_algebraMap_eq fun _ ↦ rfl

lemma algebraMap_secU (l : L) :
    algebraMap L (SecU q) l = ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ q.appTop).hom l := rfl

/-- The induced action on `SecU q`. -/
abbrev GalAction.secAct {q : X ⟶ Spec (CommRingCat.of L)} (a : GalAction (k := k) X q) :
    Gal(L/k) →* RingAut (SecU q) := a.ringAct

lemma GalAction.secAct_algebraMap {q : X ⟶ Spec (CommRingCat.of L)} (a : GalAction (k := k) X q)
    (g : Gal(L/k)) (l : L) :
    a.secAct g (algebraMap L (SecU q) l) = algebraMap L (SecU q) (g l) :=
  a.ringAct_algebraMap g l

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

/-- `Γ(T)` for `t : T ⟶ Spec k`, as a `k`-algebra. -/
def SecT {T : Scheme.{u}} (_t : T ⟶ Spec (CommRingCat.of k)) : Type u := Γ(T, ⊤)

instance : CommRing (SecT t) := inferInstanceAs (CommRing Γ(T, ⊤))

instance : Algebra k (SecT t) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom.toAlgebra

lemma algebraMap_secT (c : k) :
    algebraMap k (SecT t) c = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom c := rfl

instance : Algebra (SecT t) (SecU (pullback.snd t (sL k L))) :=
  (pullback.fst t (sL k L)).appTop.hom.toAlgebra

lemma algebraMap_secT_secU (r : SecT t) :
    algebraMap (SecT t) (SecU (pullback.snd t (sL k L))) r =
      (pullback.fst t (sL k L)).appTop.hom r := rfl

/-- `ΓSpecIso` intertwines `Spec.map f` and `f`. -/
lemma ΓSpecIso_inv_appTop_apply {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) =
      (Scheme.ΓSpecIso S).inv.hom (f r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

instance : IsScalarTower k (SecT t) (SecU (pullback.snd t (sL k L))) := by
  refine .of_algebraMap_eq fun c ↦ ?_
  rw [algebraMap_secT_secU, algebraMap_secT, IsScalarTower.algebraMap_apply k L,
    algebraMap_secU]
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop ≫
    (pullback.fst t (sL k L)).appTop).hom c
  rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

instance [IsAffine T] : Algebra.IsPushout k L (SecT t) (SecU (pullback.snd t (sL k L))) := by
  rw [← CommRingCat.isPushout_iff_isPushout]
  have h := (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback t (sL k L))).flip
  refine h.of_iso' (Scheme.ΓSpecIso (CommRingCat.of k)).symm
    (Scheme.ΓSpecIso (CommRingCat.of L)).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Scheme.ΓSpecIso_inv_naturality _).symm
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- `T_L ⟶ T` fixes `Γ(T)`. -/
lemma baseAct_secAct_algebraMap (g : Gal(L/k)) (r : SecT t) :
    (baseAct t).secAct g (algebraMap (SecT t) (SecU (pullback.snd t (sL k L))) r) =
      algebraMap (SecT t) (SecU (pullback.snd t (sL k L))) r := by
  change ((pullback.fst t (sL k L)).appTop ≫ ((baseAct t).act g).appTop).hom r = _
  rw [← Scheme.Hom.comp_appTop, baseAct_fst]
  rfl

end Sections

section Affine

/-- A morphism to an affine scheme with prescribed map on global sections. -/
def homOfΓ (X : Scheme.{u}) {Y : Scheme.{u}} [IsAffine Y] (φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) : X ⟶ Y :=
  X.toSpecΓ ≫ Spec.map φ ≫ Y.isoSpec.inv

lemma homOfΓ_appTop (X : Scheme.{u}) {Y : Scheme.{u}} [IsAffine Y] (φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) :
    (homOfΓ X φ).appTop = φ := by
  have h : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
    rw [← Iso.comp_hom_eq_id]
    have := congrArg Scheme.Hom.appTop Y.isoSpec.hom_inv_id
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_appTop] at this
    exact this
  rw [homOfΓ, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, h, Scheme.toSpecΓ_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- The `G`-equivariant `L`-morphisms `T_L ⟶ U`. -/
def EqMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) {U : Scheme.{u}}
    {qU : U ⟶ Spec (CommRingCat.of L)} (aU : GalAction (k := k) U qU) : Type u :=
  {f : pullback t (sL k L) ⟶ U // f ≫ qU = pullback.snd t (sL k L) ∧
    ∀ g, (baseAct t).act g ≫ f = f ≫ aU.act g}

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) {U : Scheme.{u}}
  {qU : U ⟶ Spec (CommRingCat.of L)} (aU : GalAction (k := k) U qU)

/-- The `L`-algebra map `Γ(U) ⟶ Γ(T_L)` of an `L`-morphism `T_L ⟶ U`. -/
def appTopAlgHom (f : pullback t (sL k L) ⟶ U) (hf : f ≫ qU = pullback.snd t (sL k L)) :
    SecU qU →ₐ[L] SecU (pullback.snd t (sL k L)) where
  toRingHom := f.appTop.hom
  commutes' l := by
    change ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ qU.appTop ≫ f.appTop).hom l =
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (pullback.snd t (sL k L)).appTop).hom l
    rw [← Scheme.Hom.comp_appTop, hf]

/-- **Equivariant morphisms are equivariant maps on global sections** (`U` affine). -/
def eqMorEquivHom [IsAffine U] :
    EqMor t aU ≃ EquivariantHom (SecU (pullback.snd t (sL k L))) (baseAct t).secAct aU.secAct where
  toFun f := ⟨appTopAlgHom t f.1 f.2.1, fun g a ↦ by
    change (f.1 ≫ aU.act g).appTop.hom a = ((baseAct t).act g ≫ f.1).appTop.hom a
    rw [f.2.2 g]⟩
  invFun φ := ⟨homOfΓ _ (CommRingCat.ofHom φ.1.toRingHom), by
      refine ext_of_isAffine ?_
      rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of L)).inv, Scheme.Hom.comp_appTop,
        homOfΓ_appTop]
      ext l
      exact φ.1.commutes l, fun g ↦ by
      refine ext_of_isAffine ?_
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, homOfΓ_appTop]
      ext a
      exact (φ.2 g a).symm⟩
  left_inv f := Subtype.ext (ext_of_isAffine (homOfΓ_appTop _ _))
  right_inv φ := by
    apply Subtype.ext
    ext a
    change (homOfΓ _ (CommRingCat.ofHom φ.1.toRingHom)).appTop.hom a = φ.1 a
    rw [homOfΓ_appTop]
    rfl

/-- The base change `T'_L ⟶ T_L` of `h : T' ⟶ T` over `k`. -/
def bcL {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T) (ht : h ≫ t = t') :
    pullback t' (sL k L) ⟶ pullback t (sL k L) :=
  pullback.lift (pullback.fst t' (sL k L) ≫ h) (pullback.snd t' (sL k L))
    (by rw [Category.assoc, ht, pullback.condition])

@[reassoc (attr := simp)]
lemma bcL_fst {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') : bcL t h ht ≫ pullback.fst t (sL k L) = pullback.fst t' (sL k L) ≫ h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma bcL_snd {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') : bcL t h ht ≫ pullback.snd t (sL k L) = pullback.snd t' (sL k L) :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma baseAct_bcL {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') (g : Gal(L/k)) :
    (baseAct t').act g ≫ bcL t h ht = bcL t h ht ≫ (baseAct t).act g := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcL_fst]
    change pullback.lift _ _ _ ≫ pullback.fst t' (sL k L) ≫ h =
      bcL t h ht ≫ pullback.lift _ _ _ ≫ pullback.fst t (sL k L)
    rw [pullback.lift_fst_assoc, pullback.lift_fst, bcL_fst]
  · rw [Category.assoc, Category.assoc, bcL_snd]
    change pullback.lift _ _ _ ≫ pullback.snd t' (sL k L) =
      bcL t h ht ≫ pullback.lift _ _ _ ≫ pullback.snd t (sL k L)
    rw [pullback.lift_snd, pullback.lift_snd, bcL_snd_assoc]

/-- The pullback of an equivariant morphism along `h : T' ⟶ T`. -/
def EqMor.pull {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') (f : EqMor t aU) : EqMor t' aU :=
  ⟨bcL t h ht ≫ f.1, by rw [Category.assoc, f.2.1, bcL_snd], fun g ↦ by
    rw [baseAct_bcL_assoc, f.2.2 g, Category.assoc]⟩

variable [FiniteDimensional k L] [IsGalois k L]

/-- The invariants `Γ(U)^G`. -/
abbrev invAlg : Subalgebra k (SecU qU) := fixedAlg aU.secAct aU.secAct_algebraMap

/-- **The Galois descent `Spec Γ(U)^G` of the affine scheme `U`.** -/
abbrev descAff : Scheme.{u} := Spec (CommRingCat.of (invAlg aU))

/-- The structure morphism `Spec Γ(U)^G ⟶ Spec k`. -/
abbrev descAffHom : descAff aU ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (invAlg aU)))

/-- `k`-algebra maps `Γ(U)^G ⟶ Γ(T)` are `k`-morphisms `T ⟶ Spec Γ(U)^G`. -/
def specHomEquiv :
    (invAlg aU →ₐ[k] SecT t) ≃ {a : T ⟶ descAff aU // a ≫ descAffHom aU = t} where
  toFun χ := ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (χ : invAlg aU →+* SecT t)), by
    rw [Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (algebraMap k (invAlg aU)) ≫
        CommRingCat.ofHom (χ : invAlg aU →+* SecT t) =
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop := by
      ext c
      exact χ.commutes c
    erw [this]
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]⟩
  invFun a :=
    { toRingHom := ((Scheme.ΓSpecIso (CommRingCat.of (invAlg aU))).inv ≫ a.1.appTop).hom
      commutes' c := by
        change ((CommRingCat.ofHom (algebraMap k (invAlg aU)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (invAlg aU))).inv) ≫ a.1.appTop).hom c =
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom c
        rw [Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop, a.2] }
  left_inv χ := by
    ext β
    change ((Scheme.ΓSpecIso _).inv ≫
      (Spec.map (CommRingCat.ofHom (χ : invAlg aU →+* SecT t))).appTop ≫
        T.toSpecΓ.appTop).hom β = χ β
    rw [Scheme.toSpecΓ_appTop]
    erw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl
  right_inv a := by
    apply Subtype.ext
    change T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso _).inv ≫ a.1.appTop) = a.1
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]

omit [FiniteDimensional k L] [IsGalois k L] in
lemma specHomEquiv_symm_apply (a : {a : T ⟶ descAff aU // a ≫ descAffHom aU = t})
    (β : invAlg aU) :
    (specHomEquiv t aU).symm a β =
      a.1.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (invAlg aU))).inv.hom β) := rfl

variable [IsAffine T] [IsAffine U]

/-- **Galois descent of affine schemes**: for an affine `k`-scheme `T`, `G`-equivariant
`L`-morphisms `T_L ⟶ U` are `k`-morphisms `T ⟶ Spec Γ(U)^G`. -/
def affineDescentEquiv :
    EqMor t aU ≃ {a : T ⟶ descAff aU // a ≫ descAffHom aU = t} :=
  (eqMorEquivHom t aU).trans ((equivariantHomEquiv (baseAct t).secAct_algebraMap
    (baseAct_secAct_algebraMap t) aU.secAct_algebraMap).trans (specHomEquiv t aU))

lemma affineDescentEquiv_apply (f : EqMor t aU) :
    affineDescentEquiv t aU f = specHomEquiv t aU (restrictInv (baseAct t).secAct_algebraMap
      (baseAct_secAct_algebraMap t) aU.secAct_algebraMap ((eqMorEquivHom t aU) f)) := rfl

/-- `f ∈ EqMor` on invariants, in terms of its descent `T ⟶ Spec Γ(U)^G`. -/
lemma appTop_eqMor_apply (f : EqMor t aU) (β : invAlg aU) :
    f.1.appTop.hom β.1 = (pullback.fst t (sL k L)).appTop.hom
      ((affineDescentEquiv t aU f).1.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (invAlg aU))).inv.hom β)) := by
  rw [← specHomEquiv_symm_apply, affineDescentEquiv_apply, Equiv.symm_apply_apply]
  exact (algebraMap_restrictInv (R := SecT t) (B := SecU (pullback.snd t (sL k L)))
    (baseAct t).secAct_algebraMap (baseAct_secAct_algebraMap t) aU.secAct_algebraMap
    ((eqMorEquivHom t aU) f) β).symm

/-- **The universal equivariant morphism** `(Spec Γ(U)^G)_L ⟶ U`. -/
def univEqMor : EqMor (descAffHom aU) aU :=
  (affineDescentEquiv (descAffHom aU) aU).symm ⟨𝟙 _, Category.id_comp _⟩

/-- **Naturality**: the descent of the pullback of the universal morphism along
`a : T ⟶ Spec Γ(U)^G` is `a`. -/
lemma affineDescentEquiv_pull (a : T ⟶ descAff aU) (ha : a ≫ descAffHom aU = t) :
    affineDescentEquiv t aU (EqMor.pull (descAffHom aU) aU a ha (univEqMor aU)) = ⟨a, ha⟩ := by
  rw [affineDescentEquiv_apply, Equiv.apply_eq_iff_eq_symm_apply]
  ext β
  apply algebraMap_pushout_injective k L (SecT t) (SecU (pullback.snd t (sL k L)))
  rw [algebraMap_restrictInv, specHomEquiv_symm_apply, algebraMap_secT_secU]
  change ((univEqMor aU).1.appTop ≫ (bcL (descAffHom aU) a ha).appTop).hom β.1 = _
  rw [CommRingCat.comp_apply, appTop_eqMor_apply, univEqMor, Equiv.apply_symm_apply]
  change ((Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop (𝟙 (descAff aU)) ≫
    (pullback.fst (descAffHom aU) (sL k L)).appTop ≫ (bcL (descAffHom aU) a ha).appTop).hom β =
    ((Scheme.ΓSpecIso _).inv ≫ a.appTop ≫ (pullback.fst t (sL k L)).appTop).hom β
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    Category.comp_id, bcL_fst]

/-- Every equivariant morphism is the pullback of the universal one along its descent. -/
lemma eq_pull_univEqMor (f : EqMor t aU) :
    f = EqMor.pull (descAffHom aU) aU (affineDescentEquiv t aU f).1
      (affineDescentEquiv t aU f).2 (univEqMor aU) :=
  (affineDescentEquiv t aU).injective (by rw [affineDescentEquiv_pull])

/-- **The universal equivariant morphism `(Spec Γ(U)^G)_L ⟶ U` is an isomorphism**
(`U` affine): Speiser's lemma `L ⊗_k Γ(U)^G ≅ Γ(U)`. -/
theorem isIso_univEqMor : IsIso (univEqMor aU).1 := by
  rw [← MorphismProperty.isomorphisms.iff, (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine _), MorphismProperty.isomorphisms.iff, isIso_SpecMap_iff]
  let χ := (specHomEquiv (descAffHom aU) aU).symm ⟨𝟙 _, Category.id_comp _⟩
  have hχ : Function.Bijective χ := by
    have : ∀ β, χ β = (Scheme.ΓSpecIso (CommRingCat.of (invAlg aU))).inv.hom β := fun β ↦ by
      rw [specHomEquiv_symm_apply, Scheme.Hom.id_appTop]
      rfl
    rw [show (χ : invAlg aU → SecT (descAffHom aU)) = _ from funext this]
    exact (ConcreteCategory.bijective_of_isIso _)
  have e : (univEqMor aU).1.appTop.hom = (extendInv (SecU (pullback.snd (descAffHom aU) (sL k L)))
      aU.secAct_algebraMap χ).toRingHom := by
    change (homOfΓ _ _).appTop.hom = _
    rw [homOfΓ_appTop]
    rfl
  rw [e]
  exact bijective_extendInv (R := SecT (descAffHom aU))
    (B := SecU (pullback.snd (descAffHom aU) (sL k L))) aU.secAct_algebraMap χ hχ

end Affine

end CurvesJacobian.GaloisDescent
