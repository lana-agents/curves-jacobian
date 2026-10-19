/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Descent.GaloisSplit
import CurvesJacobian.Descent.GaloisTwist
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Galois descent of representing objects: invariant points and group structures

Let `L / k` be a finite Galois extension, `P` a presheaf on `(Sch/k)` and `X` an `L`-scheme
representing the restriction of `P` to `(Sch/L)`, with the semilinear action of `Gal(L/k)` by
Yoneda twists (`twistGalAction`). For a `k`-scheme `T` with `T_L = T ×_k L`:

* `CurvesJacobian.GaloisDescent.eqMor_iff`: an `L`-morphism `f : T_L ⟶ X` is `Gal(L/k)`-equivariant
  iff its class `R(f) ∈ P(T_L)` is invariant under the action `id × Spec(g)` on `T_L`;
* **`eqMorEquivInv`**: `EqMor T aX ≃ P(T_L)^{Gal(L/k)}`, natural in `T` (`eqMorEquivInv_pull`).

For a presheaf of abelian groups `P` the invariants form a presheaf of abelian groups
(`invFunctor`), represented by the descended scheme (`descRepresentableByInv`), which is thus a
commutative group scheme over `k` (instances `GrpObj`, `IsCommMonObj` on `descScheme`).
Pullback to `T_L` is a natural map `ν : P ⟶ P((-)_L)^G` (`invNu`), bijective on `L`-schemes
(`bijective_invNu`, from the splitting `T ×_k L = ∐_G T`, `splitEquiv`).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.GaloisDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

section Inv

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

/-- `T_L = T ×_k L` as a `k`-scheme. -/
abbrev overTL : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.snd t (sL k L) ≫ sL k L)

lemma baseActOver_w (g : Gal(L/k)) :
    (baseAct t).act g ≫ pullback.snd t (sL k L) ≫ sL k L = pullback.snd t (sL k L) ≫ sL k L := by
  rw [← Category.assoc, GalAction.act_comp, Category.assoc, specGal_comp_sL]

/-- The action `id × Spec(g)` on `T_L` as a morphism of `k`-schemes. -/
def baseActOver (g : Gal(L/k)) : overTL (L := L) t ⟶ overTL (L := L) t :=
  Over.homMk ((baseAct t).act g) (baseActOver_w t g)

lemma bcLOver_w {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') :
    bcL (L := L) t h ht ≫ pullback.snd t (sL k L) ≫ sL k L = pullback.snd t' (sL k L) ≫ sL k L := by
  rw [← Category.assoc, bcL_snd]

/-- The base change `T'_L ⟶ T_L` as a morphism of `k`-schemes. -/
def bcLOver {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') : overTL (L := L) t' ⟶ overTL (L := L) t :=
  Over.homMk (bcL t h ht) (bcLOver_w t h ht)

variable (P : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type u)

lemma map_map_eq_map {A B D : Over (Spec (CommRingCat.of k))} (f₁ : A ⟶ B) (f₂ : B ⟶ D)
    (f : A ⟶ D) (h : f₁.left ≫ f₂.left = f.left) (y : P.obj (op D)) :
    P.map f₁.op (P.map f₂.op y) = P.map f.op y := by
  rw [← Functor.map_comp_apply, ← op_comp, show f₁ ≫ f₂ = f from Over.OverMorphism.ext h]

/-- The `Gal(L/k)`-invariant points `P(T_L)^G`. -/
def InvPt : Type u :=
  {y : P.obj (op (overTL (L := L) t)) // ∀ g : Gal(L/k), P.map (baseActOver t g).op y = y}

/-- The pullback of invariant points along `h : T' ⟶ T`. -/
def InvPt.pull {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') (y : InvPt (L := L) t P) : InvPt (L := L) t' P :=
  ⟨P.map (bcLOver t h ht).op y.1, fun g ↦ by
    rw [← Functor.map_comp_apply, ← op_comp]
    have : baseActOver t' g ≫ bcLOver t h ht = bcLOver t h ht ≫ baseActOver t g :=
      Over.OverMorphism.ext (baseAct_bcL t h ht g)
    rw [this, op_comp, Functor.map_comp_apply, y.2 g]⟩

variable {X : Over (Spec (CommRingCat.of L))} (R : ((Over.map (sL k L)).op ⋙ P).RepresentableBy X)

/-- The class of an `L`-morphism `T_L ⟶ X`. -/
def classOf (f : pullback t (sL k L) ⟶ X.left) (hf : f ≫ X.hom = pullback.snd t (sL k L)) :
    P.obj (op (overTL (L := L) t)) :=
  R.homEquiv (Over.homMk f hf : Over.mk (pullback.snd t (sL k L)) ⟶ X)

lemma classOf_comp {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of L))
    (m : T' ⟶ pullback t (sL k L)) (hm : m ≫ pullback.snd t (sL k L) = s)
    (f : pullback t (sL k L) ⟶ X.left) (hf : f ≫ X.hom = pullback.snd t (sL k L))
    (hmf : (m ≫ f) ≫ X.hom = s) (hms : m ≫ pullback.snd t (sL k L) ≫ sL k L = s ≫ sL k L) :
    R.homEquiv (Over.homMk (m ≫ f) hmf : Over.mk s ⟶ X) =
      P.map (Over.homMk m hms : Over.mk (s ≫ sL k L) ⟶ overTL (L := L) t).op
        (classOf t P R f hf) := by
  have e : (Over.homMk (m ≫ f) hmf : Over.mk s ⟶ X) =
      (Over.homMk m hm : Over.mk s ⟶ Over.mk (pullback.snd t (sL k L))) ≫ Over.homMk f hf :=
    Over.OverMorphism.ext rfl
  rw [e, R.homEquiv_comp]
  rfl

/-- **Equivariance is invariance of the class.** -/
theorem eqMor_iff (f : pullback t (sL k L) ⟶ X.left) (hf : f ≫ X.hom = pullback.snd t (sL k L))
    (g : Gal(L/k)) :
    (baseAct t).act g ≫ f = f ≫ (twistGalAction P R).act g ↔
      P.map (baseActOver t g).op (classOf t P R f hf) = classOf t P R f hf := by
  -- both sides of the equivariance lie over `snd ≫ Spec g`
  have h1 : ((baseAct t).act g ≫ f) ≫ X.hom = pullback.snd t (sL k L) ≫ specGal g := by
    rw [Category.assoc, hf, GalAction.act_comp]
  have h2 : (f ≫ (twistGalAction P R).act g) ≫ X.hom =
      pullback.snd t (sL k L) ≫ specGal g := by
    rw [Category.assoc, GalAction.act_comp, ← Category.assoc, hf]
  have E1 : R.homEquiv (Over.homMk _ h1 : Over.mk (pullback.snd t (sL k L) ≫ specGal g) ⟶ X) =
      P.map (twistIso (sL k L) (specGal_comp_sL g)
        (Over.mk (pullback.snd t (sL k L)))).hom.op
        (P.map (baseActOver t g).op (classOf t P R f hf)) := by
    have hms : (baseAct t).act g ≫ pullback.snd t (sL k L) ≫ sL k L =
        (pullback.snd t (sL k L) ≫ specGal g) ≫ sL k L := by
      rw [← Category.assoc, GalAction.act_comp]
    refine (classOf_comp t P R _ ((baseAct t).act g) (GalAction.act_comp _ _) f hf h1 hms).trans ?_
    exact (map_map_eq_map P (twistIso (sL k L) (specGal_comp_sL g)
      (Over.mk (pullback.snd t (sL k L)))).hom (baseActOver t g)
      (Over.homMk ((baseAct t).act g) hms) (Category.id_comp _) _).symm
  have E2 : R.homEquiv (Over.homMk _ h2 : Over.mk (pullback.snd t (sL k L) ≫ specGal g) ⟶ X) =
      P.map (twistIso (sL k L) (specGal_comp_sL g)
        (Over.mk (pullback.snd t (sL k L)))).hom.op (classOf t P R f hf) := by
    have e : (Over.homMk _ h2 : Over.mk (pullback.snd t (sL k L) ≫ specGal g) ⟶ X) =
        twistPt (sL k L) P R (specGal_comp_sL g) (Over.homMk f hf :
          Over.mk (pullback.snd t (sL k L)) ⟶ X) :=
      Over.OverMorphism.ext rfl
    exact (congrArg R.homEquiv e).trans (homEquiv_twistPt (sL k L) P R (specGal_comp_sL g)
      (T := Over.mk (pullback.snd t (sL k L))) (Over.homMk f hf))
  have hinj : Function.Injective (P.map (twistIso (sL k L) (specGal_comp_sL g)
      (Over.mk (pullback.snd t (sL k L)))).hom.op) := by
    intro a b hab
    have := congrArg (P.map (twistIso (sL k L) (specGal_comp_sL g)
      (Over.mk (pullback.snd t (sL k L)))).inv.op) hab
    simpa only [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
      Functor.map_id_apply] using this
  constructor
  · intro H
    have : (Over.homMk _ h1 : Over.mk (pullback.snd t (sL k L) ≫ specGal g) ⟶ X) =
        Over.homMk _ h2 := Over.OverMorphism.ext H
    have := congrArg R.homEquiv this
    rw [E1, E2] at this
    exact hinj this
  · intro H
    have : R.homEquiv (Over.homMk _ h1 : Over.mk (pullback.snd t (sL k L) ≫ specGal g) ⟶ X) =
        R.homEquiv (Over.homMk _ h2) := by
      rw [E1, E2, H]
    exact congrArg CommaMorphism.left (R.homEquiv.injective this)

/-- The `L`-morphism `T_L ⟶ X` of a class. -/
def invHom (y : P.obj (op (overTL (L := L) t))) : Over.mk (pullback.snd t (sL k L)) ⟶ X :=
  (R.homEquiv (X := Over.mk (pullback.snd t (sL k L)))).symm y

lemma classOf_invHom (y : P.obj (op (overTL (L := L) t))) :
    classOf t P R (invHom t P R y).left (Over.w (invHom t P R y)) = y :=
  (congrArg R.homEquiv (Over.OverMorphism.ext rfl)).trans (R.homEquiv.apply_symm_apply _)

/-- **Equivariant morphisms are invariant points**: `EqMor T aX ≃ P(T_L)^G`. -/
def eqMorEquivInv : EqMor t (twistGalAction P R) ≃ InvPt (L := L) t P where
  toFun f := ⟨classOf t P R f.1 f.2.1, fun g ↦ (eqMor_iff t P R f.1 f.2.1 g).1 (f.2.2 g)⟩
  invFun y := ⟨(invHom t P R y.1).left, Over.w (invHom t P R y.1), fun g ↦ by
    refine (eqMor_iff t P R _ (Over.w (invHom t P R y.1)) g).2 ?_
    rw [classOf_invHom]
    exact y.2 g⟩
  left_inv f := by
    apply Subtype.ext
    change (R.homEquiv.symm (R.homEquiv (Over.homMk f.1 f.2.1 :
      Over.mk (pullback.snd t (sL k L)) ⟶ X))).left = f.1
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv y := Subtype.ext (classOf_invHom t P R y.1)

lemma eqMorEquivInv_pull {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T)
    (ht : h ≫ t = t') (f : EqMor t (twistGalAction P R)) :
    eqMorEquivInv t' P R (EqMor.pull t _ h ht f) = (eqMorEquivInv t P R f).pull t P h ht := by
  apply Subtype.ext
  exact classOf_comp t P R _ (bcL t h ht) (bcL_snd t h ht) f.1 f.2.1 _ (bcLOver_w t h ht)

end Inv

section Split

variable [FiniteDimensional k L] [IsGalois k L] {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of L))
  (P : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type u) {X : Over (Spec (CommRingCat.of L))}
  (R : ((Over.map (sL k L)).op ⋙ P).RepresentableBy X)

omit [FiniteDimensional k L] [IsGalois k L] in
lemma deltaOver_w : diagL k s ≫ pullback.snd (s ≫ sL k L) (sL k L) ≫ sL k L = s ≫ sL k L := by
  rw [← Category.assoc, diagL_snd]

/-- The diagonal `T ⟶ T ×_k L` of an `L`-scheme `T`, as a morphism of `k`-schemes. -/
def deltaOver : Over.mk (s ≫ sL k L) ⟶ overTL (L := L) (s ≫ sL k L) :=
  Over.homMk (diagL k s) (deltaOver_w s)

/-- Restriction of invariant classes along the diagonal: `P(T_L)^G ⟶ P(T)`. -/
def thetaRes (y : InvPt (L := L) (s ≫ sL k L) P) : P.obj (op (Over.mk (s ≫ sL k L))) :=
  P.map (deltaOver s).op y.1

/-- `L`-morphisms `T ⟶ X` as morphisms in `Over (Spec L)`. -/
def overHomEquiv : {φ : T ⟶ X.left // φ ≫ X.hom = s} ≃ (Over.mk s ⟶ X) where
  toFun φ := Over.homMk φ.1 φ.2
  invFun a := ⟨a.left, Over.w a⟩
  left_inv _ := rfl
  right_inv _ := Over.OverMorphism.ext rfl

/-- **Restriction along the diagonal is bijective on invariants** (`T ×_k L = ∐_G T`). -/
def thetaEquiv : InvPt (L := L) (s ≫ sL k L) P ≃ P.obj (op (Over.mk (s ≫ sL k L))) :=
  (eqMorEquivInv (s ≫ sL k L) P R).symm.trans ((splitEquiv s (twistGalAction P R)).trans
    ((overHomEquiv s).trans R.homEquiv))

lemma thetaEquiv_apply (y : InvPt (L := L) (s ≫ sL k L) P) :
    thetaEquiv s P R y = thetaRes s P y := by
  obtain ⟨f, rfl⟩ := (eqMorEquivInv (s ≫ sL k L) P R).surjective y
  rw [thetaEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact classOf_comp _ P R s (diagL k s) (diagL_snd s) f.1 f.2.1
    (by rw [Category.assoc, f.2.1, diagL_snd]) (deltaOver_w s)

include R in
lemma bijective_thetaRes : Function.Bijective (thetaRes (L := L) s P) := by
  have : thetaRes (L := L) s P = thetaEquiv s P R := funext fun y ↦ (thetaEquiv_apply s P R y).symm
  rw [this]
  exact (thetaEquiv s P R).bijective

end Split

section Group

variable (Pab : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The subgroup `P(T_L)^G` of `Gal(L/k)`-invariant classes. -/
def invSubgroup {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    AddSubgroup (Pab.obj (op (overTL (L := L) t))) where
  carrier := {y | ∀ g : Gal(L/k), (Pab.map (baseActOver t g).op).hom y = y}
  zero_mem' _ := map_zero _
  add_mem' {a b} ha hb g := by
    rw [map_add, ha g, hb g]
  neg_mem' {a} ha g := by
    rw [map_neg, ha g]

lemma pull_mem_invSubgroup {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    {t' : T' ⟶ Spec (CommRingCat.of k)} (h : T' ⟶ T) (ht : h ≫ t = t')
    {y : Pab.obj (op (overTL (L := L) t))} (hy : y ∈ invSubgroup Pab t) :
    (Pab.map (bcLOver t h ht).op).hom y ∈ invSubgroup Pab t' :=
  (InvPt.pull t (Pab ⋙ forget AddCommGrpCat) h ht ⟨y, hy⟩).2

/-- **The presheaf of invariants** `T ↦ P(T_L)^{Gal(L/k)}` on `(Sch/k)`. -/
def invFunctor : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (invSubgroup (L := L) Pab T.unop.hom)
  map {T T'} a := AddCommGrpCat.ofHom
    (((Pab.map (bcLOver T.unop.hom a.unop.left (Over.w a.unop)).op).hom.comp
      (invSubgroup (L := L) Pab T.unop.hom).subtype).codRestrict _
        fun y ↦ pull_mem_invSubgroup Pab _ _ _ y.2)
  map_id T := by
    ext y
    change (Pab.map (bcLOver T.unop.hom (𝟙 _) _).op).hom y.1 = y.1
    rw [show bcLOver (L := L) T.unop.hom (𝟙 _) (Category.id_comp _) = 𝟙 _ from
      Over.OverMorphism.ext (bcL_id _), op_id, Pab.map_id]
    rfl
  map_comp {T T' T''} a b := by
    ext y
    change (Pab.map (bcLOver T.unop.hom (b.unop.left ≫ a.unop.left) _).op).hom y.1 =
      (Pab.map (bcLOver T'.unop.hom b.unop.left (Over.w b.unop)).op).hom
        ((Pab.map (bcLOver T.unop.hom a.unop.left (Over.w a.unop)).op).hom y.1)
    rw [show bcLOver (L := L) T.unop.hom (b.unop.left ≫ a.unop.left)
        (by rw [Category.assoc, Over.w a.unop, Over.w b.unop]) =
        bcLOver T'.unop.hom b.unop.left (Over.w b.unop) ≫
          bcLOver T.unop.hom a.unop.left (Over.w a.unop) from
      Over.OverMorphism.ext (bcL_comp _ _ (Over.w a.unop) _ (Over.w b.unop)), op_comp,
      Pab.map_comp]
    rfl

/-- Invariant points as elements of the invariant subgroup. -/
def invPtEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    InvPt (L := L) t (Pab ⋙ forget AddCommGrpCat) ≃ invSubgroup (L := L) Pab t where
  toFun y := ⟨y.1, y.2⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [FiniteDimensional k L] [IsGalois k L] {X : Over (Spec (CommRingCat.of L))}
  (R : ((Over.map (sL k L)).op ⋙ Pab ⋙ forget AddCommGrpCat).RepresentableBy X)
  (hcov : ∀ x : X.left, ∃ V : X.left.Opens, IsAffineOpen V ∧
    (twistGalAction (Pab ⋙ forget AddCommGrpCat) R).IsStable V ∧ x ∈ V)

/-- **The descended scheme represents the invariants**:
`Hom_k(T, X₀) ≃ P(T_L)^{Gal(L/k)}`. -/
def descRepresentableByInv : (invFunctor (L := L) Pab ⋙ forget AddCommGrpCat).RepresentableBy
    (descScheme (twistGalAction (Pab ⋙ forget AddCommGrpCat) R) hcov) where
  homEquiv {T} := (descRepresentableBy _ hcov).homEquiv.trans
    ((eqMorEquivInv T.hom (Pab ⋙ forget AddCommGrpCat) R).trans (invPtEquiv Pab T.hom))
  homEquiv_comp {T T'} f g := by
    apply Subtype.ext
    change (eqMorEquivInv T.hom (Pab ⋙ forget AddCommGrpCat) R
      ((descRepresentableBy _ hcov).homEquiv (f ≫ g))).1 =
      (Pab.map (bcLOver T'.hom f.left (Over.w f)).op).hom (eqMorEquivInv T'.hom
        (Pab ⋙ forget AddCommGrpCat) R ((descRepresentableBy _ hcov).homEquiv g)).1
    rw [(descRepresentableBy _ hcov).homEquiv_comp f g]
    exact congrArg Subtype.val (eqMorEquivInv_pull T'.hom (Pab ⋙ forget AddCommGrpCat) R
      f.left (Over.w f) _)

/-- The multiplicative version of `descRepresentableByInv`. -/
def descRepresentableByInvMul :
    ((invFunctor (L := L) Pab ⋙ AddCommGrpCat.toCommGrp) ⋙ forget CommGrpCat).RepresentableBy
      (descScheme (twistGalAction (Pab ⋙ forget AddCommGrpCat) R) hcov) where
  homEquiv := (descRepresentableByInv Pab R hcov).homEquiv
  homEquiv_comp f g := (descRepresentableByInv Pab R hcov).homEquiv_comp f g

/-- **The descended scheme is a group scheme over `k`.** -/
instance : GrpObj (descScheme (twistGalAction (Pab ⋙ forget AddCommGrpCat) R) hcov) :=
  GrpObj.ofRepresentableBy _ ((invFunctor (L := L) Pab ⋙ AddCommGrpCat.toCommGrp) ⋙
    forget₂ CommGrpCat GrpCat) (descRepresentableByInvMul Pab R hcov)

/-- **The descended group scheme is commutative.** -/
instance : IsCommMonObj (descScheme (twistGalAction (Pab ⋙ forget AddCommGrpCat) R) hcov) :=
  IsCommMonObj.ofRepresentableBy _ ((invFunctor (L := L) Pab ⋙ AddCommGrpCat.toCommGrp) ⋙
    forget₂ CommGrpCat CommMonCat) (descRepresentableByInvMul Pab R hcov)

end Group

section Nu

variable (Pab : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u})

lemma mapAb_map_eq {A B D : Over (Spec (CommRingCat.of k))} (f₁ : A ⟶ B) (f₂ : B ⟶ D)
    (f : A ⟶ D) (h : f₁.left ≫ f₂.left = f.left) (y : Pab.obj (op D)) :
    (Pab.map f₁.op).hom ((Pab.map f₂.op).hom y) = (Pab.map f.op).hom y := by
  rw [← ConcreteCategory.comp_apply, ← Pab.map_comp, ← op_comp,
    show f₁ ≫ f₂ = f from Over.OverMorphism.ext h]

lemma fstOver_w {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    pullback.fst t (sL k L) ≫ t = pullback.snd t (sL k L) ≫ sL k L :=
  pullback.condition

/-- The projection `T_L ⟶ T` as a morphism of `k`-schemes. -/
def fstOver {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    overTL (L := L) t ⟶ Over.mk t :=
  Over.homMk (pullback.fst t (sL k L)) (fstOver_w t)

lemma fst_mem_invSubgroup {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : Pab.obj (op (Over.mk t))) :
    (Pab.map (fstOver (L := L) t).op).hom x ∈ invSubgroup (L := L) Pab t := fun g ↦ by
  rw [← ConcreteCategory.comp_apply, ← Pab.map_comp, ← op_comp,
    show baseActOver (L := L) t g ≫ fstOver t = fstOver t from
      Over.OverMorphism.ext (baseAct_fst t g)]

/-- **The pullback to `T_L` as an invariant class**: `ν : P ⟶ P((-)_L)^G`. -/
def invNu : Pab ⟶ invFunctor (L := L) Pab where
  app T := AddCommGrpCat.ofHom ((Pab.map (fstOver (L := L) T.unop.hom).op).hom.codRestrict _
    (fst_mem_invSubgroup Pab T.unop.hom))
  naturality {T T'} a := by
    ext x
    apply Subtype.ext
    change (Pab.map (fstOver (L := L) T'.unop.hom).op).hom ((Pab.map a.unop.op).hom x) =
      (Pab.map (bcLOver (L := L) T.unop.hom a.unop.left (Over.w a.unop)).op).hom
        ((Pab.map (fstOver (L := L) T.unop.hom).op).hom x)
    exact (mapAb_map_eq Pab (fstOver (L := L) T'.unop.hom) a.unop
      (fstOver (L := L) T'.unop.hom ≫ a.unop) rfl x).trans
      (mapAb_map_eq Pab _ _ _ (bcL_fst T.unop.hom a.unop.left (Over.w a.unop)) x).symm

lemma invNu_app_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : Pab.obj (op (Over.mk t))) :
    ((invNu (L := L) Pab).app (op (Over.mk t)) x).1 = (Pab.map (fstOver (L := L) t).op).hom x :=
  rfl

variable [FiniteDimensional k L] [IsGalois k L] {X : Over (Spec (CommRingCat.of L))}
  (R : ((Over.map (sL k L)).op ⋙ Pab ⋙ forget AddCommGrpCat).RepresentableBy X)

include R in
/-- **`ν` is bijective on `L`-schemes.** -/
theorem bijective_invNu {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of L)) :
    Function.Bijective ((invNu (L := L) Pab).app (op (Over.mk (s ≫ sL k L)))) := by
  have hb := bijective_thetaRes s (Pab ⋙ forget AddCommGrpCat) R
  have hleft : ∀ x, thetaRes s (Pab ⋙ forget AddCommGrpCat)
      ⟨((invNu (L := L) Pab).app (op (Over.mk (s ≫ sL k L))) x).1,
        ((invNu (L := L) Pab).app (op (Over.mk (s ≫ sL k L))) x).2⟩ = x := by
    intro x
    change (Pab.map (deltaOver s).op).hom ((Pab.map (fstOver _).op).hom x) = x
    rw [← ConcreteCategory.comp_apply, ← Pab.map_comp, ← op_comp,
      show deltaOver (L := L) s ≫ fstOver (s ≫ sL k L) = 𝟙 _ from
        Over.OverMorphism.ext (diagL_fst s), op_id, Pab.map_id]
    rfl
  refine ⟨fun x x' h ↦ ?_, fun y ↦ ?_⟩
  · rw [← hleft x, ← hleft x']
    congr 2
    · exact congrArg Subtype.val h
  · refine ⟨thetaRes s (Pab ⋙ forget AddCommGrpCat) ⟨y.1, y.2⟩, Subtype.ext ?_⟩
    have := hb.1 (hleft (thetaRes s (Pab ⋙ forget AddCommGrpCat) ⟨y.1, y.2⟩))
    exact congrArg Subtype.val this

end Nu

end CurvesJacobian.GaloisDescent
