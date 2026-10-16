/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Tensor

/-!
# Line bundles on schemes

* `AlgebraicGeometry.Scheme.PresheafOfModules.IsBasisOn P U e`: the section `e ∈ P(U)` of a
  presheaf of modules is a basis of `P` over every `V ≤ U` (`r ↦ r • e|_V` is bijective).
* `AlgebraicGeometry.Scheme.Modules.IsInvertible L`: `L` is locally free of rank one, i.e. every
  point has a neighbourhood `U` with a section `s ∈ Γ(L, U)` which is a basis on `U`.
* `isBasisOn_of_isLocallyBijective`: a locally bijective morphism of presheaves of modules into a
  sheaf maps a basis on `U` to a basis on `U`. This is the main tool to produce local bases of
  sheafifications (tensor products, duals).
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace CurvesJacobian

section Gluing

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type u}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
  [HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  {T : TopCat.{u}} (F : TopCat.Sheaf C T)

/-- Two sections of a sheaf agreeing near every point are equal. -/
lemma sheaf_eq_of_locally_eq {V : Opens T} (s t : ToType (F.1.obj (op V)))
    (h : ∀ x ∈ V, ∃ (W : Opens T) (hW : W ≤ V), x ∈ W ∧
      F.1.map (homOfLE hW).op s = F.1.map (homOfLE hW).op t) : s = t := by
  choose W hW hxW hst using h
  exact F.eq_of_locally_eq' V (U := fun x : V ↦ W x.1 x.2) (fun x ↦ homOfLE (hW x.1 x.2))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxW y hy⟩) s t (fun x ↦ hst x.1 x.2)

/-- Gluing of sections given on a neighbourhood of each point. -/
lemma sheaf_exists_glue {V : Opens T} (W : V → Opens T) (hW : ∀ x, W x ≤ V)
    (hx : ∀ x : V, x.1 ∈ W x) (sf : ∀ x, ToType (F.1.obj (op (W x))))
    (compat : ∀ x y, F.1.map (homOfLE (inf_le_left : W x ⊓ W y ≤ W x)).op (sf x) =
      F.1.map (homOfLE (inf_le_right : W x ⊓ W y ≤ W y)).op (sf y)) :
    ∃ s : ToType (F.1.obj (op V)), ∀ x, F.1.map (homOfLE (hW x)).op s = sf x := by
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W V (fun x ↦ homOfLE (hW x))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩) sf compat
  exact ⟨s, hs⟩

end Gluing

end CurvesJacobian

namespace AlgebraicGeometry.Scheme

open CurvesJacobian

variable {X : Scheme.{u}}

noncomputable instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

namespace PresheafOfModules

/-- Restriction of sections of a presheaf of modules along `V ≤ U`. -/
noncomputable abbrev res (P : X.PresheafOfModules) {U V : X.Opens} (h : V ≤ U) (m : P.obj (op U)) :
    P.obj (op V) :=
  P.map (homOfLE h).op m

lemma res_res (P : X.PresheafOfModules) {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V)
    (m : P.obj (op U)) : res P h' (res P h m) = res P (h'.trans h) m := by
  change (P.presheaf.map _ ≫ P.presheaf.map _) m = _
  rw [← Functor.map_comp]
  rfl

lemma res_eq (P : X.PresheafOfModules) {U V : X.Opens} (f : V ⟶ U) (m : P.obj (op U)) :
    P.map f.op m = res P f.le m := rfl

lemma res_smul (P : X.PresheafOfModules) {U V : X.Opens} (h : V ≤ U)
    (r : X.ringCatSheaf.obj.obj (op U)) (m : P.obj (op U)) :
    res P h (r • m) = X.ringCatSheaf.obj.map (homOfLE h).op r • res P h m :=
  P.map_smul _ r m

lemma res_add (P : X.PresheafOfModules) {U V : X.Opens} (h : V ≤ U) (m m' : P.obj (op U)) :
    res P h (m + m') = res P h m + res P h m' := map_add _ _ _

lemma res_zero (P : X.PresheafOfModules) {U V : X.Opens} (h : V ≤ U) :
    res P h (0 : P.obj (op U)) = 0 := map_zero _

lemma res_self (P : X.PresheafOfModules) {U : X.Opens} (m : P.obj (op U)) :
    res P (le_refl U) m = m := by
  change P.presheaf.map (𝟙 _) m = m
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma app_res {P Q : X.PresheafOfModules} (η : P ⟶ Q) {U V : X.Opens} (h : V ≤ U)
    (m : P.obj (op U)) : η.app (op V) (res P h m) = res Q h (η.app (op U) m) :=
  _root_.PresheafOfModules.naturality_apply η _ m

/-- `e ∈ P(U)` is a basis of `P` on `U`: for every `V ≤ U`, `r ↦ r • e|_V` is a bijection
`𝒪(V) ≃ P(V)`. -/
def IsBasisOn (P : X.PresheafOfModules) (U : X.Opens) (e : P.obj (op U)) : Prop :=
  ∀ ⦃V : X.Opens⦄ (h : V ≤ U),
    Function.Bijective (fun r : X.ringCatSheaf.obj.obj (op V) ↦ r • res P h e)

lemma IsBasisOn.restrict {P : X.PresheafOfModules} {U : X.Opens} {e : P.obj (op U)}
    (he : IsBasisOn P U e) {V : X.Opens} (h : V ≤ U) : IsBasisOn P V (res P h e) := by
  intro W hW
  simpa only [res_res] using he (hW.trans h)

lemma IsBasisOn.of_iso {P Q : X.PresheafOfModules} (φ : P ≅ Q) {U : X.Opens}
    {e : P.obj (op U)} (he : IsBasisOn P U e) : IsBasisOn Q U (φ.hom.app _ e) := by
  intro V h
  have : (fun r : X.ringCatSheaf.obj.obj (op V) ↦ r • res Q h (φ.hom.app _ e)) =
      φ.hom.app (op V) ∘ (fun r ↦ r • res P h e) := by
    ext r
    simp only [Function.comp_apply, map_smul, app_res]
  rw [this]
  refine Function.Bijective.comp ?_ (he h)
  exact ((CategoryTheory.forget _).mapIso ((evaluation _ _).obj (op V) |>.mapIso
    ((_root_.PresheafOfModules.toPresheaf _).mapIso φ))).toEquiv.bijective


section LocallyBijective

open _root_.PresheafOfModules

lemma ringCatSheaf_map_apply {U V : X.Opens} (h : V ≤ U) (r : X.ringCatSheaf.obj.obj (op U)) :
    X.ringCatSheaf.obj.map (homOfLE h).op r = X.sheaf.1.map (homOfLE h).op r := rfl

/-- Pointwise form of local injectivity. -/
lemma exists_res_eq_zero {P Q : X.PresheafOfModules} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) ((toPresheaf _).map η)]
    {V : X.Opens} (m : P.obj (op V)) (hm : η.app _ m = 0) :
    ∀ x ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧ res P hW m = 0 := by
  intro x hx
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    ((toPresheaf _).map η) (show ToType (((toPresheaf _).obj P).obj (op V)) from m) 0
    (by change η.app _ m = η.app _ 0; rw [hm, map_zero])
  obtain ⟨W, f, hf, hxW⟩ := hmem x hx
  refine ⟨W, f.le, hxW, ?_⟩
  have hf' : P.map f.op m = P.map f.op 0 := hf
  rw [map_zero] at hf'
  exact hf'

/-- Pointwise form of local surjectivity. -/
lemma exists_res_eq_app {P Q : X.PresheafOfModules} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) ((toPresheaf _).map η)]
    {V : X.Opens} (n : Q.obj (op V)) :
    ∀ x ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧
      ∃ p : P.obj (op W), η.app _ p = res Q hW n := by
  intro x hx
  obtain ⟨W, f, ⟨p, hp⟩, hxW⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((toPresheaf _).map η) (show ToType (((toPresheaf _).obj Q).obj (op V)) from n) x hx
  exact ⟨W, f.le, hxW, p, hp⟩

/-- A locally bijective morphism of presheaves of modules into a sheaf maps a basis on `U` to a
basis on `U`. -/
theorem isBasisOn_of_isLocallyBijective {P Q : X.PresheafOfModules} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) ((toPresheaf _).map η)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) ((toPresheaf _).map η)]
    (hQ : TopCat.Presheaf.IsSheaf ((toPresheaf _).obj Q))
    {U : X.Opens} {e : P.obj (op U)} (he : IsBasisOn P U e) :
    IsBasisOn Q U (η.app _ e) := by
  have inj : ∀ ⦃V⦄ (h : V ≤ U), Function.Injective
      (fun r : X.ringCatSheaf.obj.obj (op V) ↦ r • res Q h (η.app _ e)) := by
    intro V h r r' hrr'
    simp only at hrr'
    rw [← sub_eq_zero]
    have h0 : η.app _ ((r - r') • res P h e) = 0 := by
      rw [map_smul, app_res, sub_smul, hrr', sub_self]
    apply sheaf_eq_of_locally_eq X.sheaf
    intro x hx
    obtain ⟨W, hW, hxW, hW0⟩ := exists_res_eq_zero η _ h0 x hx
    refine ⟨W, hW, hxW, ?_⟩
    rw [res_smul, res_res] at hW0
    have h1 := (he (hW.trans h)).1 (a₁ := X.ringCatSheaf.obj.map (homOfLE hW).op (r - r'))
      (a₂ := 0) (by simp only; rw [hW0, zero_smul])
    exact h1.trans (map_zero _).symm
  intro V h
  refine ⟨inj h, fun n ↦ ?_⟩
  choose W hW hxW p hp using exists_res_eq_app η n
  have hcoef : ∀ x (hx : x ∈ V), ∃ r : X.ringCatSheaf.obj.obj (op (W x hx)),
      r • res Q ((hW x hx).trans h) (η.app _ e) = res Q (hW x hx) n := by
    intro x hx
    obtain ⟨r, hr⟩ := (he ((hW x hx).trans h)).2 (p x hx)
    refine ⟨r, ?_⟩
    rw [← hp, ← hr]
    simp only [map_smul, app_res]
  choose r hr using hcoef
  have key : ∀ (x : V) {Z : X.Opens} (hZ : Z ≤ W x.1 x.2),
      X.ringCatSheaf.obj.map (homOfLE hZ).op (r x.1 x.2) •
        res Q (hZ.trans ((hW x.1 x.2).trans h)) (η.app _ e) =
          res Q (hZ.trans (hW x.1 x.2)) n := by
    intro x Z hZ
    rw [← res_res Q ((hW x.1 x.2).trans h) hZ, ← res_smul, hr, res_res]
  obtain ⟨R, hR⟩ := sheaf_exists_glue X.sheaf (V := V) (fun x ↦ W x.1 x.2)
    (fun x ↦ hW x.1 x.2) (fun x ↦ hxW x.1 x.2) (fun x ↦ r x.1 x.2) (by
      intro x y
      apply inj ((inf_le_left : W x.1 x.2 ⊓ W y.1 y.2 ≤ _).trans ((hW x.1 x.2).trans h))
      refine (key x inf_le_left).trans ((key y inf_le_right).trans ?_).symm
      rfl)
  let R' : X.ringCatSheaf.obj.obj (op V) := R
  refine ⟨R', ?_⟩
  apply sheaf_eq_of_locally_eq ⟨(toPresheaf _).obj Q, hQ⟩
  intro x hx
  refine ⟨W x hx, hW x hx, hxW x hx, ?_⟩
  change res Q (hW x hx) (R' • res Q h (η.app _ e)) = res Q (hW x hx) n
  rw [res_smul, res_res]
  have := hR ⟨x, hx⟩
  rw [← ringCatSheaf_map_apply] at this
  rw [this, hr]

end LocallyBijective

end PresheafOfModules


section Algebra

/-- If `a` and `b` are bases of the rank-one free modules `A` and `B`, then `a ⊗ b` is a basis of
`A ⊗ B`. -/
lemma bijective_smul_tmul {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (a : A) (b : B)
    (ha : Function.Bijective (fun r : R ↦ r • a)) (hb : Function.Bijective (fun r : R ↦ r • b)) :
    Function.Bijective (fun r : R ↦ r • (a ⊗ₜ[R] b)) := by
  let ea : R ≃ₗ[R] A := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R A a) ha
  let eb : R ≃ₗ[R] B := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B b) hb
  have : (fun r : R ↦ r • (a ⊗ₜ[R] b)) =
      (TensorProduct.congr ea eb) ∘ (TensorProduct.lid R R).symm := by
    ext r
    simp [ea, eb, TensorProduct.smul_tmul']
  rw [this]
  exact (TensorProduct.congr ea eb).bijective.comp (TensorProduct.lid R R).symm.bijective

end Algebra

namespace PresheafOfModules

open _root_.PresheafOfModules

/-- Tensor product of bases. -/
lemma IsBasisOn.tensor {P Q : X.PresheafOfModules} {U : X.Opens} {a : P.obj (op U)}
    {b : Q.obj (op U)} (ha : IsBasisOn P U a) (hb : IsBasisOn Q U b) :
    IsBasisOn (P ⊗ Q) U (a ⊗ₜ b) := by
  intro V h
  exact bijective_smul_tmul (res P h a) (res Q h b) (ha h) (hb h)

/-- The unit section is a basis of the unit presheaf. -/
lemma isBasisOn_unit (U : X.Opens) :
    IsBasisOn (𝟙_ X.PresheafOfModules) U (1 : X.ringCatSheaf.obj.obj (op U)) := by
  intro V h
  have : (fun r : X.ringCatSheaf.obj.obj (op V) ↦
      r • res (𝟙_ X.PresheafOfModules) h (1 : X.ringCatSheaf.obj.obj (op U))) = id := by
    ext r
    change r * X.ringCatSheaf.obj.map _ 1 = r
    exact (congrArg (r * ·) (map_one _)).trans (mul_one r)
  rw [this]
  exact Function.bijective_id

/-- If `φ` is bijective on every open contained in some member of an open cover, then `φ` is
locally injective. -/
lemma isLocallyInjective_of_locally_bijective {P Q : X.PresheafOfModules} (φ : P ⟶ Q)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U, Function.Bijective (φ.app (op V))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) ((toPresheaf _).map φ) := by
  rw [isLocallyInjective_iff_of_additive]
  intro V m hm x hx
  obtain ⟨U, hxU, hU⟩ := H x
  refine ⟨V.unop ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩
  have h1 : φ.app (op (V.unop ⊓ U)) (P.map (homOfLE inf_le_left).op m) = 0 := by
    rw [naturality_apply]
    change Q.map _ (φ.app V m) = 0
    rw [show φ.app V m = 0 from hm, map_zero]
  have h2 : P.map (homOfLE (inf_le_left : V.unop ⊓ U ≤ V.unop)).op m = 0 :=
    (hU _ inf_le_right).1 (h1.trans (map_zero _).symm)
  exact h2.trans (map_zero _).symm

/-- If `φ` is bijective on every open contained in some member of an open cover, then `φ` is
locally surjective. -/
lemma isLocallySurjective_of_locally_bijective {P Q : X.PresheafOfModules} (φ : P ⟶ Q)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U, Function.Bijective (φ.app (op V))) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) ((toPresheaf _).map φ) where
  imageSieve_mem {V} n := by
    intro x hx
    obtain ⟨U, hxU, hU⟩ := H x
    obtain ⟨m, hm⟩ := (hU _ (inf_le_right : V ⊓ U ≤ U)).2 (Q.map (homOfLE inf_le_left).op n)
    exact ⟨V ⊓ U, homOfLE inf_le_left, ⟨m, hm⟩, ⟨hx, hxU⟩⟩

end PresheafOfModules

namespace Modules

open _root_.PresheafOfModules

/-- `s ∈ Γ(M, U)` is a basis of the sheaf of modules `M` on `U`, i.e. `r ↦ r • s|_V` is a
bijection `𝒪(V) ≃ M(V)` for every `V ≤ U`. -/
def IsBasisOn (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) : Prop :=
  PresheafOfModules.IsBasisOn ((toPresheafOfModules X).obj M) U s

/-- An invertible sheaf (line bundle): a sheaf of modules which is locally free of rank one,
i.e. every point has an open neighbourhood `U` and a section `s ∈ Γ(L, U)` which is a basis of
`L` on `U` (Stacks, Tag 0B8M: locally free of rank one is equivalent to invertible on a locally
ringed space). -/
class IsInvertible (L : X.Modules) : Prop where
  exists_basis : ∀ x : X, ∃ (U : X.Opens) (s : Γ(L, U)), x ∈ U ∧ L.IsBasisOn U s

lemma IsInvertible.of_iso {L M : X.Modules} (e : L ≅ M) [L.IsInvertible] : M.IsInvertible where
  exists_basis x := by
    obtain ⟨U, s, hxU, hs⟩ := IsInvertible.exists_basis (L := L) x
    exact ⟨U, e.hom.app U s, hxU,
      PresheafOfModules.IsBasisOn.of_iso ((toPresheafOfModules X).mapIso e) hs⟩

lemma isInvertible_iff_of_iso {L M : X.Modules} (e : L ≅ M) :
    L.IsInvertible ↔ M.IsInvertible :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩

section Sheafify

variable (P : X.PresheafOfModules)

/-- The unit `P ⟶ sheafify P`, as a morphism of presheaves of modules. -/
noncomputable abbrev toSheafify : P ⟶ (SheafOfModules.forget _ ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ((sheafify X).obj P) :=
  (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app P

instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map (toSheafify P)) := by
  change Presheaf.IsLocallyInjective _
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  infer_instance

instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map (toSheafify P)) := by
  change Presheaf.IsLocallySurjective _
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  infer_instance

/-- A basis of a presheaf of modules on `U` gives a basis of its sheafification on `U`. -/
lemma isBasisOn_sheafify {U : X.Opens} {e : P.obj (op U)}
    (he : PresheafOfModules.IsBasisOn P U e) :
    ((sheafify X).obj P).IsBasisOn U ((toSheafify P).app _ e) :=
  PresheafOfModules.isBasisOn_of_isLocallyBijective (toSheafify P)
    ((sheafify X).obj P).isSheaf he

end Sheafify

/-- The presheaf of modules underlying a sheaf of modules, in the form used by the
sheafification adjunction. -/
noncomputable abbrev toPre (L : X.Modules) : X.PresheafOfModules :=
  (SheafOfModules.forget _ ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj L

/-- A sheaf of modules is isomorphic to the sheafification of its underlying presheaf. -/
noncomputable def sheafifyToPreIso (L : X.Modules) : (sheafify X).obj (toPre L) ≅ L :=
  (asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).counit).app L

lemma IsBasisOn.toPre {L : X.Modules} {U : X.Opens} {s : Γ(L, U)} (h : L.IsBasisOn U s) :
    PresheafOfModules.IsBasisOn (toPre L) U s := h

/-- If a presheaf of modules has local bases around every point, its sheafification is
invertible. -/
lemma isInvertible_sheafify (P : X.PresheafOfModules)
    (H : ∀ x : X, ∃ (U : X.Opens) (e : P.obj (op U)), x ∈ U ∧
      PresheafOfModules.IsBasisOn P U e) :
    ((sheafify X).obj P).IsInvertible where
  exists_basis x := by
    obtain ⟨U, e, hxU, he⟩ := H x
    exact ⟨U, _, hxU, isBasisOn_sheafify P he⟩

instance : IsInvertible (X := X) (SheafOfModules.unit X.ringCatSheaf) where
  exists_basis _ := ⟨⊤, (1 : Γ(X, ⊤)), trivial, PresheafOfModules.isBasisOn_unit ⊤⟩

instance : (𝟙_ X.Modules).IsInvertible :=
  isInvertible_sheafify (𝟙_ X.PresheafOfModules)
    (fun _ ↦ ⟨⊤, (1 : X.ringCatSheaf.obj.obj (op ⊤)), trivial,
      PresheafOfModules.isBasisOn_unit ⊤⟩)

/-- The tensor product of two invertible sheaves is invertible. -/
instance isInvertible_tensor (L M : X.Modules) [L.IsInvertible] [M.IsInvertible] :
    (L ⊗ M).IsInvertible := by
  have : ((sheafify X).obj (toPre L ⊗ toPre M)).IsInvertible := by
    apply isInvertible_sheafify
    intro x
    obtain ⟨U, s, hxU, hs⟩ := IsInvertible.exists_basis (L := L) x
    obtain ⟨U', t, hxU', ht⟩ := IsInvertible.exists_basis (L := M) x
    exact ⟨U ⊓ U', _, ⟨hxU, hxU'⟩,
      (hs.toPre.restrict inf_le_left).tensor (ht.toPre.restrict inf_le_right)⟩
  exact .of_iso ((Functor.Monoidal.μIso (sheafify X) (toPre L) (toPre M)).symm ≪≫
    (sheafifyToPreIso L ⊗ᵢ sheafifyToPreIso M))

end Modules

end AlgebraicGeometry.Scheme
