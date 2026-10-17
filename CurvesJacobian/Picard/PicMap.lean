/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Small

/-!
# Functoriality of the Picard group

* `Modules.tmulSection a b ∈ Γ(A ⊗ B, V)`: the pure tensor of two sections; the pure tensor of
  two bases is a basis (`Modules.isBasisOn_tmulSection`).
* `Modules.pullbackTensorHom f L M : f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M`, the comparison morphism, adjoint
  to `l ⊗ m ↦ f^* l ⊗ f^* m`; it is an isomorphism for invertible `L`, `M`
  (`Modules.isIso_pullbackTensorHom`).
* `Pic.map f : Y.Pic →+ X.Pic`, `[L] ↦ [f^* L]`, with `Pic.map_id` and `Pic.map_comp`.
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

namespace Modules

open _root_.PresheafOfModules

/-- `sheafify (A(-) ⊗ B(-)) ≅ A ⊗ B`. -/
def sheafifyTensorIso (A B : X.Modules) : (sheafify X).obj (toPre A ⊗ toPre B) ≅ A ⊗ B :=
  (Functor.Monoidal.μIso (sheafify X) (toPre A) (toPre B)).symm ≪≫
    (sheafifyToPreIso A ⊗ᵢ sheafifyToPreIso B)

/-- The canonical morphism of presheaves `A(V) ⊗ B(V) ⟶ (A ⊗ B)(V)`. -/
def tensorPreToTensor (A B : X.Modules) : toPre A ⊗ toPre B ⟶ toPre (A ⊗ B) :=
  toSheafify _ ≫ (SheafOfModules.forget _ ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
      (sheafifyTensorIso A B).hom

/-- The pure tensor `a ⊗ b ∈ Γ(A ⊗ B, V)` of two sections. -/
def tmulSection {A B : X.Modules} {V : X.Opens} (a : Γ(A, V)) (b : Γ(B, V)) : Γ(A ⊗ B, V) :=
  (tensorPreToTensor A B).app (op V)
    (show ↑((toPre A ⊗ toPre B).obj (op V)) from
      (show (toPre A).obj (op V) from a) ⊗ₜ (show (toPre B).obj (op V) from b))

/-- The pure tensor of two bases is a basis. -/
lemma isBasisOn_tmulSection {A B : X.Modules} {V : X.Opens} {a : Γ(A, V)} {b : Γ(B, V)}
    (ha : A.IsBasisOn V a) (hb : B.IsBasisOn V b) : (A ⊗ B).IsBasisOn V (tmulSection a b) :=
  IsBasisOn.of_iso' (sheafifyTensorIso A B) (isBasisOn_sheafify _ (ha.toPre.tensor hb.toPre)) rfl


section TmulSection

variable {A B : X.Modules} {V : X.Opens}

lemma tmulSection_add_left (a a' : Γ(A, V)) (b : Γ(B, V)) :
    tmulSection (a + a') b = tmulSection a b + tmulSection a' b :=
  (congrArg (fun t ↦ (tensorPreToTensor A B).app (op V) t)
    (TensorProduct.add_tmul (R := X.ringCatSheaf.obj.obj (op V))
      (show (toPre A).obj (op V) from a) a' (show (toPre B).obj (op V) from b))).trans
    (map_add _ _ _)

lemma tmulSection_add_right (a : Γ(A, V)) (b b' : Γ(B, V)) :
    tmulSection a (b + b') = tmulSection a b + tmulSection a b' :=
  (congrArg (fun t ↦ (tensorPreToTensor A B).app (op V) t)
    (TensorProduct.tmul_add (R := X.ringCatSheaf.obj.obj (op V))
      (show (toPre A).obj (op V) from a) (show (toPre B).obj (op V) from b) b')).trans
    (map_add _ _ _)

lemma tmulSection_smul_left (c : X.ringCatSheaf.obj.obj (op V)) (a : Γ(A, V)) (b : Γ(B, V)) :
    tmulSection (show Γ(A, V) from c • (show (toPre A).obj (op V) from a)) b =
      show Γ(A ⊗ B, V) from c • (show (toPre (A ⊗ B)).obj (op V) from tmulSection a b) :=
  (congrArg (fun t ↦ (tensorPreToTensor A B).app (op V) t)
    (TensorProduct.smul_tmul' (R := X.ringCatSheaf.obj.obj (op V)) c
      (show (toPre A).obj (op V) from a) (show (toPre B).obj (op V) from b)).symm).trans
    (_root_.map_smul ((tensorPreToTensor A B).app (op V)).hom c _)

lemma tmulSection_smul_right (c : X.ringCatSheaf.obj.obj (op V)) (a : Γ(A, V)) (b : Γ(B, V)) :
    tmulSection a (show Γ(B, V) from c • (show (toPre B).obj (op V) from b)) =
      show Γ(A ⊗ B, V) from c • (show (toPre (A ⊗ B)).obj (op V) from tmulSection a b) :=
  (congrArg (fun t ↦ (tensorPreToTensor A B).app (op V) t)
    (TensorProduct.tmul_smul (R := X.ringCatSheaf.obj.obj (op V)) c
      (show (toPre A).obj (op V) from a) (show (toPre B).obj (op V) from b))).trans
    (_root_.map_smul ((tensorPreToTensor A B).app (op V)).hom c _)

lemma tmulSection_res {V' : X.Opens} (h : V' ≤ V) (a : Γ(A, V)) (b : Γ(B, V)) :
    (A ⊗ B).presheaf.map (homOfLE h).op (tmulSection a b) =
      tmulSection (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) := by
  unfold tmulSection
  exact (naturality_apply (tensorPreToTensor A B) (homOfLE h).op _).symm

end TmulSection

section Comparison

variable (f : X ⟶ Y)

lemma pullbackSection_add {M : Y.Modules} {U : Y.Opens} (m m' : Γ(M, U)) :
    pullbackSection f (m + m') = pullbackSection f m + pullbackSection f m' :=
  map_add _ _ _

lemma pullbackSection_smul {M : Y.Modules} {U : Y.Opens} (r : Y.ringCatSheaf.obj.obj (op U))
    (m : Γ(M, U)) :
    pullbackSection f (show Γ(M, U) from r • (show (toPre M).obj (op U) from m)) =
      show Γ((pullback f).obj M, f ⁻¹ᵁ U) from
        (show X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ U)) from f.app U r) •
          (show (toPre ((pullback f).obj M)).obj (op (f ⁻¹ᵁ U)) from pullbackSection f m) :=
  Hom.app_smul ((pullbackPushforwardAdjunction f).unit.app M) r m

lemma pullbackSection_res {M : Y.Modules} {U V : Y.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    pullbackSection f (M.presheaf.map (homOfLE h).op m) =
      ((pullback f).obj M).presheaf.map (homOfLE (f.preimage_mono h)).op
        (pullbackSection f m) :=
  naturality_apply ((toPresheafOfModules Y).map ((pullbackPushforwardAdjunction f).unit.app M))
    (homOfLE h).op m

variable (L M : Y.Modules)

/-- The morphism of presheaves `L(V) ⊗ M(V) ⟶ Γ(f^*L ⊗ f^*M, f⁻¹V)`, `l ⊗ m ↦ f^*l ⊗ f^*m`. -/
def pullbackTensorPre : toPre L ⊗ toPre M ⟶
    toPre ((pushforward f).obj ((pullback f).obj L ⊗ (pullback f).obj M)) where
  app V := ModuleCat.MonoidalCategory.tensorLift
    (R := (Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj V)
    (M₁ := (toPre L).obj V) (M₂ := (toPre M).obj V)
    (M₃ := (toPre ((pushforward f).obj ((pullback f).obj L ⊗ (pullback f).obj M))).obj V)
    (fun l m ↦ tmulSection (pullbackSection f (U := V.unop) l) (pullbackSection f (U := V.unop) m))
    (fun l l' m ↦ (congrArg (fun x ↦ tmulSection x _) (pullbackSection_add f l l')).trans
      (tmulSection_add_left _ _ _))
    (fun r l m ↦ (congrArg (fun x ↦ tmulSection x _) (pullbackSection_smul f r l)).trans
      (tmulSection_smul_left _ _ _))
    (fun l m m' ↦ (congrArg (fun x ↦ tmulSection _ x) (pullbackSection_add f m m')).trans
      (tmulSection_add_right _ _ _))
    (fun r l m ↦ (congrArg (fun x ↦ tmulSection _ x) (pullbackSection_smul f r m)).trans
      (tmulSection_smul_right _ _ _))
  naturality {V V'} g := ModuleCat.MonoidalCategory.tensor_ext (fun l m ↦ by
    change tmulSection (pullbackSection f (L.presheaf.map (homOfLE g.unop.le).op l))
        (pullbackSection f (M.presheaf.map (homOfLE g.unop.le).op m)) =
      ((pullback f).obj L ⊗ (pullback f).obj M).presheaf.map
        (homOfLE (f.preimage_mono g.unop.le)).op
          (tmulSection (pullbackSection f (U := V.unop) l) (pullbackSection f (U := V.unop) m))
    rw [pullbackSection_res, pullbackSection_res, tmulSection_res])

lemma pullbackTensorPre_app_tmul {V : Y.Opens} (l : Γ(L, V)) (m : Γ(M, V)) :
    (pullbackTensorPre f L M).app (op V)
      (show ↑((toPre L ⊗ toPre M).obj (op V)) from
        (show (toPre L).obj (op V) from l) ⊗ₜ (show (toPre M).obj (op V) from m)) =
      tmulSection (pullbackSection f l) (pullbackSection f m) := rfl

/-- The adjoint of `pullbackTensorPre`. -/
def pullbackTensorAdj :
    L ⊗ M ⟶ (pushforward f).obj ((pullback f).obj L ⊗ (pullback f).obj M) :=
  (sheafifyTensorIso L M).inv ≫
    ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
      (pullbackTensorPre f L M)

lemma pullbackTensorAdj_app_tmulSection {V : Y.Opens} (l : Γ(L, V)) (m : Γ(M, V)) :
    (pullbackTensorAdj f L M).app V (tmulSection l m) =
      tmulSection (pullbackSection f l) (pullbackSection f m) := by
  let x : ↑((toPre L ⊗ toPre M).obj (op V)) :=
    (show (toPre L).obj (op V) from l) ⊗ₜ (show (toPre M).obj (op V) from m)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)
  let ψ : (sheafify Y).obj (toPre L ⊗ toPre M) ⟶
      (pushforward f).obj ((pullback f).obj L ⊗ (pullback f).obj M) :=
    (adj.homEquiv _ _).symm (pullbackTensorPre f L M)
  have h : adj.unit.app (toPre L ⊗ toPre M) ≫ (SheafOfModules.forget _ ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map ψ =
        pullbackTensorPre f L M :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have h2 := congr_arg (fun φ ↦ φ.app (op V) x) h
  refine Eq.trans ?_ (h2.trans (pullbackTensorPre_app_tmul f L M l m))
  calc (pullbackTensorAdj f L M).app V (tmulSection l m) =
      ψ.app V ((sheafifyTensorIso L M).inv.app V ((sheafifyTensorIso L M).hom.app V
        ((toSheafify (toPre L ⊗ toPre M)).app (op V) x))) := rfl
    _ = ψ.app V ((toSheafify (toPre L ⊗ toPre M)).app (op V) x) :=
        congrArg _ (iso_inv_app_hom_app _ _ _)
    _ = _ := rfl

/-- The comparison morphism `f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M`. -/
def pullbackTensorHom :
    (pullback f).obj (L ⊗ M) ⟶ (pullback f).obj L ⊗ (pullback f).obj M :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm (pullbackTensorAdj f L M)

lemma pullbackTensorHom_app_pullbackSection {V : Y.Opens} (l : Γ(L, V)) (m : Γ(M, V)) :
    (pullbackTensorHom f L M).app (f ⁻¹ᵁ V) (pullbackSection f (tmulSection l m)) =
      tmulSection (pullbackSection f l) (pullbackSection f m) := by
  have h := ((pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply
    (pullbackTensorAdj f L M)
  rw [Adjunction.homEquiv_unit] at h
  rw [← pullbackTensorAdj_app_tmulSection, ← h]
  rfl

/-- For invertible sheaves, the comparison morphism is an isomorphism. -/
instance isIso_pullbackTensorHom [L.IsInvertible] [M.IsInvertible] :
    IsIso (pullbackTensorHom f L M) := by
  apply isIso_of_isBasisOn
  intro x
  obtain ⟨U, s, hxU, hs⟩ := IsInvertible.exists_basis (L := L) (f.base x)
  obtain ⟨U', t, hxU', ht⟩ := IsInvertible.exists_basis (L := M) (f.base x)
  have hs' := Scheme.PresheafOfModules.IsBasisOn.restrict hs (inf_le_left : U ⊓ U' ≤ U)
  have ht' := Scheme.PresheafOfModules.IsBasisOn.restrict ht (inf_le_right : U ⊓ U' ≤ U')
  refine ⟨f ⁻¹ᵁ (U ⊓ U'), _, ⟨hxU, hxU'⟩,
    isBasisOn_pullbackSection f _ (isBasisOn_tmulSection hs' ht'), ?_⟩
  rw [pullbackTensorHom_app_pullbackSection]
  exact isBasisOn_tmulSection (isBasisOn_pullbackSection f _ hs')
    (isBasisOn_pullbackSection f _ ht')

/-- `f^*(L ⊗ M) ≅ f^*L ⊗ f^*M` for invertible `L`, `M`. -/
def pullbackTensorIso [L.IsInvertible] [M.IsInvertible] :
    (pullback f).obj (L ⊗ M) ≅ (pullback f).obj L ⊗ (pullback f).obj M :=
  asIso (pullbackTensorHom f L M)

end Comparison

end Modules

namespace Pic

open Modules

/-- The pullback map on Picard groups, `[L] ↦ [f^* L]`. -/
def map (f : X ⟶ Y) : Y.Pic →+ X.Pic :=
  AddMonoidHom.mk' (fun x ↦ mk ((Modules.pullback f).obj (rep x))) (fun x y ↦ by
    obtain ⟨e⟩ : Nonempty (rep (x + y) ≅ rep x ⊗ rep y) := by
      rw [← mk_eq_mk_iff, mk_tensor, mk_rep, mk_rep, mk_rep]
    rw [← mk_tensor, mk_eq_mk_iff]
    exact ⟨(Modules.pullback f).mapIso e ≪≫ pullbackTensorIso f _ _⟩)

lemma map_mk (f : X ⟶ Y) (L : Y.Modules) [L.IsInvertible] :
    map f (mk L) = mk ((Modules.pullback f).obj L) :=
  mk_eq_of_iso ((Modules.pullback f).mapIso (rep_mk L).some)

@[simp]
lemma map_id : map (𝟙 X) = AddMonoidHom.id _ := by
  ext x
  induction x using Pic.ind with | h L =>
  rw [map_mk, AddMonoidHom.id_apply]
  exact mk_eq_of_iso ((pullbackId X).app L)

lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = (map f).comp (map g) := by
  ext x
  induction x using Pic.ind with | h L =>
  rw [AddMonoidHom.comp_apply, map_mk, map_mk, map_mk]
  exact mk_eq_of_iso ((pullbackComp f g).app L).symm

end Pic

end AlgebraicGeometry.Scheme

end
