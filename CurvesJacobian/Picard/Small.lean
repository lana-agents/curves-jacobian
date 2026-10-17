/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.Pullback

/-!
# Invertible sheaves are determined by transition functions

If two invertible sheaves `L`, `L'` have local bases `s x`, `s' x` on the same open cover
`(U x)_{x : X}` with the same transition functions (`s y = g x y • s x` and `s' y = g x y • s' x`
on `U x ⊓ U y`), then `L ≅ L'` (`Modules.nonempty_iso_of_transitions`). Since the transition data
live in a type of the universe of `X`, the isomorphism classes of invertible sheaves form a small
type (`small_picLarge`), and `X.Pic := Shrink X.PicLarge : Type u`.
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

open CurvesJacobian

variable {X : Scheme.{u}}

namespace PresheafOfModules

open _root_.PresheafOfModules

lemma res_smul' (P : X.PresheafOfModules) {U V : X.Opens} (h : V ≤ U)
    (r : X.ringCatSheaf.obj.obj (op U)) (m : P.obj (op U)) :
    res P h (r • m) = rres h r • res P h m :=
  res_smul P h r m

lemma coord_res {P : X.PresheafOfModules} {U : X.Opens} {e : P.obj (op U)}
    (he : IsBasisOn P U e) {V W : X.Opens} (hV : V ≤ U) (hW : W ≤ V) (a : P.obj (op V)) :
    coord he (hW.trans hV) (res P hW a) = rres hW (coord he hV a) := by
  apply coord_eq
  rw [← res_res P hV hW, ← res_smul', coord_smul]

/-- Local bases of `P` and `Q` on the same open cover with the same transition functions. -/
structure SameTransitions (P Q : X.PresheafOfModules) where
  /-- the open cover -/
  U : X → X.Opens
  mem : ∀ x, x ∈ U x
  /-- the local bases of `P` -/
  s : ∀ x, P.obj (op (U x))
  /-- the local bases of `Q` -/
  s' : ∀ x, Q.obj (op (U x))
  hs : ∀ x, IsBasisOn P (U x) (s x)
  /-- the transition functions -/
  g : ∀ x y, X.ringCatSheaf.obj.obj (op (U x ⊓ U y))
  hg : ∀ x y, res P inf_le_right (s y) = g x y • res P inf_le_left (s x)
  hg' : ∀ x y, res Q inf_le_right (s' y) = g x y • res Q inf_le_left (s' x)

namespace SameTransitions

variable {P Q : X.PresheafOfModules} (D : SameTransitions P Q)

/-- The local candidate for the glued morphism on `V ⊓ U x`. -/
def localMap {V : X.Opens} (m : P.obj (op V)) (x : X) : Q.obj (op (V ⊓ D.U x)) :=
  coord (D.hs x) inf_le_right (res P inf_le_left m) • res Q inf_le_right (D.s' x)

lemma localMap_compat {V : X.Opens} (m : P.obj (op V)) (x y : X) :
    res Q (inf_le_left : (V ⊓ D.U x) ⊓ (V ⊓ D.U y) ≤ V ⊓ D.U x) (D.localMap m x) =
      res Q (inf_le_right : (V ⊓ D.U x) ⊓ (V ⊓ D.U y) ≤ V ⊓ D.U y) (D.localMap m y) := by
  set Z := (V ⊓ D.U x) ⊓ (V ⊓ D.U y)
  have hZx : Z ≤ D.U x := inf_le_left.trans inf_le_right
  have hZy : Z ≤ D.U y := inf_le_right.trans inf_le_right
  have hZxy : Z ≤ D.U x ⊓ D.U y := le_inf hZx hZy
  have hZV : Z ≤ V := inf_le_left.trans inf_le_left
  have hcx : rres (inf_le_left : Z ≤ V ⊓ D.U x)
      (coord (D.hs x) inf_le_right (res P inf_le_left m)) =
        coord (D.hs x) hZx (res P hZV m) := by
    rw [← coord_res (D.hs x) inf_le_right inf_le_left, res_res]
  have hcy : rres (inf_le_right : Z ≤ V ⊓ D.U y)
      (coord (D.hs y) inf_le_right (res P inf_le_left m)) =
        coord (D.hs y) hZy (res P hZV m) := by
    rw [← coord_res (D.hs y) inf_le_right inf_le_right, res_res]
  have hsy : res P hZy (D.s y) = rres hZxy (D.g x y) • res P hZx (D.s x) := by
    rw [← res_res P inf_le_right hZxy, D.hg, res_smul', res_res]
  have hs'y : res Q hZy (D.s' y) = rres hZxy (D.g x y) • res Q hZx (D.s' x) := by
    rw [← res_res Q inf_le_right hZxy, D.hg', res_smul', res_res]
  have key : coord (D.hs x) hZx (res P hZV m) =
      coord (D.hs y) hZy (res P hZV m) * rres hZxy (D.g x y) := by
    apply coord_eq
    rw [mul_smul, ← hsy, coord_smul]
  unfold localMap
  rw [res_smul', res_smul', res_res, res_res, hcx, hcy, hs'y, smul_smul, key]

variable (hQ : TopCat.Presheaf.IsSheaf ((toPresheaf _).obj Q))

include hQ in
lemma exists_glue {V : X.Opens} (m : P.obj (op V)) :
    ∃ n : Q.obj (op V), ∀ x : V, res Q (inf_le_left : V ⊓ D.U x.1 ≤ V) n = D.localMap m x.1 := by
  obtain ⟨n, hn⟩ := sheaf_exists_glue ⟨(toPresheaf _).obj Q, hQ⟩ (V := V)
    (fun x ↦ V ⊓ D.U x.1) (fun _ ↦ inf_le_left) (fun x ↦ ⟨x.2, D.mem x.1⟩)
    (fun x ↦ D.localMap m x.1) (fun x y ↦ D.localMap_compat m x.1 y.1)
  exact ⟨n, hn⟩

include hQ in
lemma eq_of_res_eq {V : X.Opens} {n n' : Q.obj (op V)}
    (h : ∀ x : V, res Q (inf_le_left : V ⊓ D.U x.1 ≤ V) n =
      res Q (inf_le_left : V ⊓ D.U x.1 ≤ V) n') : n = n' :=
  sheaf_eq_of_locally_eq ⟨(toPresheaf _).obj Q, hQ⟩ n n' (fun x hx ↦
    ⟨V ⊓ D.U x, inf_le_left, ⟨hx, D.mem x⟩, h ⟨x, hx⟩⟩)

/-- The glued morphism, on sections. -/
def glueFun {V : X.Opens} (m : P.obj (op V)) : Q.obj (op V) :=
  (D.exists_glue hQ m).choose

lemma glueFun_spec {V : X.Opens} (m : P.obj (op V)) (x : V) :
    res Q (inf_le_left : V ⊓ D.U x.1 ≤ V) (D.glueFun hQ m) = D.localMap m x.1 :=
  (D.exists_glue hQ m).choose_spec x

lemma glueFun_eq {V : X.Opens} (m : P.obj (op V)) (n : Q.obj (op V))
    (h : ∀ x : V, res Q (inf_le_left : V ⊓ D.U x.1 ≤ V) n = D.localMap m x.1) :
    D.glueFun hQ m = n :=
  D.eq_of_res_eq hQ (fun x ↦ (D.glueFun_spec hQ m x).trans (h x).symm)

lemma localMap_add {V : X.Opens} (m m' : P.obj (op V)) (x : X) :
    D.localMap (m + m') x = D.localMap m x + D.localMap m' x := by
  unfold localMap
  rw [res_add, ← add_smul]
  congr 1
  apply coord_eq
  rw [add_smul, coord_smul, coord_smul]

lemma localMap_smul {V : X.Opens} (r : X.ringCatSheaf.obj.obj (op V)) (m : P.obj (op V))
    (x : X) : D.localMap (r • m) x = rres (inf_le_left : V ⊓ D.U x ≤ V) r • D.localMap m x := by
  unfold localMap
  rw [res_smul', smul_smul]
  congr 1
  apply coord_eq
  rw [mul_smul, coord_smul]

lemma localMap_res {V V' : X.Opens} (h : V' ≤ V) (m : P.obj (op V)) (x : X) :
    D.localMap (res P h m) x =
      res Q (inf_le_inf_right _ h : V' ⊓ D.U x ≤ V ⊓ D.U x) (D.localMap m x) := by
  unfold localMap
  rw [res_smul', res_res, res_res]
  congr 1
  have := coord_res (D.hs x) (inf_le_right : V ⊓ D.U x ≤ D.U x)
    (inf_le_inf_right (D.U x) h : V' ⊓ D.U x ≤ V ⊓ D.U x) (res P inf_le_left m)
  rw [res_res] at this
  exact this

/-- The glued morphism of presheaves of modules. -/
def glueHom : P ⟶ Q :=
  homMk
    { app V := AddCommGrpCat.ofHom (AddMonoidHom.mk' (D.glueFun hQ (V := V.unop))
        (fun m m' ↦ D.glueFun_eq hQ _ _ (fun x ↦ by
          rw [res_add, glueFun_spec, glueFun_spec, localMap_add])))
      naturality {V V'} f := by
        ext m
        change D.glueFun hQ (res P f.unop.le m) = res Q f.unop.le (D.glueFun hQ m)
        apply glueFun_eq
        intro x
        rw [res_res, localMap_res D f.unop.le, ← D.glueFun_spec hQ m ⟨x.1, f.unop.le x.2⟩,
          res_res] }
    (fun V r m ↦ D.glueFun_eq hQ _ _ (fun x ↦ (res_smul' Q _ r _).trans (by
      change rres _ r • res Q _ (D.glueFun hQ (V := V.unop) m) = _
      rw [glueFun_spec, localMap_smul])))

lemma glueHom_app_basis (x : X) : (D.glueHom hQ).app (op (D.U x)) (D.s x) = D.s' x := by
  refine D.glueFun_eq hQ _ _ (fun z ↦ ?_)
  have h : D.U x ⊓ D.U z.1 ≤ D.U z.1 ⊓ D.U x := le_of_eq (inf_comm _ _)
  have e1 : res P (inf_le_left : D.U x ⊓ D.U z.1 ≤ D.U x) (D.s x) =
      rres h (D.g z.1 x) • res P (inf_le_right : D.U x ⊓ D.U z.1 ≤ D.U z.1) (D.s z.1) := by
    rw [← res_res P (inf_le_right : D.U z.1 ⊓ D.U x ≤ D.U x) h, D.hg, res_smul', res_res]
  have e2 : res Q (inf_le_left : D.U x ⊓ D.U z.1 ≤ D.U x) (D.s' x) =
      rres h (D.g z.1 x) • res Q (inf_le_right : D.U x ⊓ D.U z.1 ≤ D.U z.1) (D.s' z.1) := by
    rw [← res_res Q (inf_le_right : D.U z.1 ⊓ D.U x ≤ D.U x) h, D.hg', res_smul', res_res]
  unfold localMap
  rw [coord_eq (D.hs z.1) inf_le_right _ _ e1.symm, e2]

end SameTransitions

end PresheafOfModules

namespace Modules

/-- Two sheaves with local bases on the same open cover and the same transition functions are
isomorphic. -/
lemma nonempty_iso_of_transitions {L L' : X.Modules} (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (s : ∀ x, Γ(L, U x)) (s' : ∀ x, Γ(L', U x))
    (hs : ∀ x, L.IsBasisOn (U x) (s x)) (hs' : ∀ x, L'.IsBasisOn (U x) (s' x))
    (g : ∀ x y, X.ringCatSheaf.obj.obj (op (U x ⊓ U y)))
    (hg : ∀ x y, Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L) inf_le_right (s y) =
      g x y • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L) inf_le_left (s x))
    (hg' : ∀ x y, Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L') inf_le_right
      (s' y) = g x y •
        Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L') inf_le_left (s' x)) :
    Nonempty (L ≅ L') := by
  let D : Scheme.PresheafOfModules.SameTransitions ((toPresheafOfModules X).obj L)
      ((toPresheafOfModules X).obj L') := ⟨U, hU, s, s', hs, g, hg, hg'⟩
  let φ : L ⟶ L' := (fullyFaithfulToPresheafOfModules (X := X)).preimage (D.glueHom L'.isSheaf)
  have : IsIso φ := isIso_of_isBasisOn φ (fun x ↦ ⟨U x, s x, hU x, hs x, by
    change L'.IsBasisOn (U x) ((D.glueHom L'.isSheaf).app (op (U x)) (s x))
    rw [D.glueHom_app_basis L'.isSheaf x]
    exact hs' x⟩)
  exact ⟨asIso φ⟩

variable (X) in
/-- Transition data of an invertible sheaf: an open neighbourhood of every point and transition
functions on the pairwise intersections. -/
structure TransitionData : Type u where
  /-- the open neighbourhoods -/
  U : X → X.Opens
  /-- the transition functions -/
  g : ∀ x y, X.ringCatSheaf.obj.obj (op (U x ⊓ U y))

/-- `L` has local bases realising the transition data `T`. -/
def AdmitsTransitions (L : X.Modules) (T : TransitionData X) : Prop :=
  (∀ x, x ∈ T.U x) ∧ ∃ s : ∀ x, Γ(L, T.U x), (∀ x, L.IsBasisOn (T.U x) (s x)) ∧
    ∀ x y, Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L) inf_le_right (s y) =
      T.g x y • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L) inf_le_left (s x)

lemma exists_admitsTransitions (L : X.Modules) [L.IsInvertible] :
    ∃ T, AdmitsTransitions L T := by
  choose U s hU hs using fun x : X ↦ IsInvertible.exists_basis (L := L) x
  exact ⟨⟨U, fun x y ↦ Scheme.PresheafOfModules.coord (hs x) inf_le_left
      (Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L) inf_le_right (s y))⟩,
    hU, s, hs, fun x y ↦ (Scheme.PresheafOfModules.coord_smul (hs x) inf_le_left _).symm⟩

lemma nonempty_iso_of_admitsTransitions {L L' : X.Modules} {T : TransitionData X}
    (hL : AdmitsTransitions L T) (hL' : AdmitsTransitions L' T) : Nonempty (L ≅ L') := by
  obtain ⟨hU, s, hs, hg⟩ := hL
  obtain ⟨-, s', hs', hg'⟩ := hL'
  exact nonempty_iso_of_transitions T.U hU s s' hs hs' T.g hg hg'

end Modules

open Modules

instance small_picLarge : Small.{u} X.PicLarge := by
  refine small_of_injective (f := fun c : X.PicLarge ↦ {T | AdmitsTransitions (PicLarge.rep c) T})
    (fun c c' h ↦ ?_)
  obtain ⟨T, hT⟩ := exists_admitsTransitions (PicLarge.rep c)
  have hT' : AdmitsTransitions (PicLarge.rep c') T := by
    have : T ∈ {T | AdmitsTransitions (PicLarge.rep c) T} := hT
    simp only at h
    rwa [h] at this
  obtain ⟨e⟩ := nonempty_iso_of_admitsTransitions hT hT'
  rw [← PicLarge.mk_rep c, ← PicLarge.mk_rep c']
  exact PicLarge.mk_eq_of_iso e

variable (X) in
/-- The Picard group of a scheme (Stacks, Tag 01CX): the group of isomorphism classes of
invertible sheaves, with `[L] + [M] = [L ⊗ M]`. -/
def Pic : Type u := Shrink.{u} X.PicLarge

instance : AddCommGroup X.Pic := (equivShrink X.PicLarge).symm.addCommGroup

namespace Pic

/-- The additive equivalence between `X.Pic` and `X.PicLarge`. -/
def equivLarge : X.Pic ≃+ X.PicLarge where
  __ := (equivShrink X.PicLarge).symm
  map_add' _ _ := by
    change (equivShrink X.PicLarge).symm ((equivShrink X.PicLarge)
      ((equivShrink X.PicLarge).symm _ + (equivShrink X.PicLarge).symm _)) = _
    rw [Equiv.symm_apply_apply]
    rfl

/-- The class of an invertible sheaf in the Picard group. -/
def mk (L : X.Modules) [L.IsInvertible] : X.Pic := equivLarge.symm (PicLarge.mk L)

lemma equivLarge_mk (L : X.Modules) [L.IsInvertible] : equivLarge (mk L) = PicLarge.mk L :=
  equivLarge.apply_symm_apply _

lemma mk_eq_mk_iff {L M : X.Modules} [L.IsInvertible] [M.IsInvertible] :
    mk L = mk M ↔ Nonempty (L ≅ M) := by
  rw [← PicLarge.mk_eq_mk_iff, ← equivLarge_mk, ← equivLarge_mk, equivLarge.apply_eq_iff_eq]

lemma mk_eq_of_iso {L M : X.Modules} [L.IsInvertible] [M.IsInvertible] (e : L ≅ M) :
    mk L = mk M :=
  mk_eq_mk_iff.mpr ⟨e⟩

lemma mk_tensor (L M : X.Modules) [L.IsInvertible] [M.IsInvertible] :
    mk (L ⊗ M) = mk L + mk M := by
  apply equivLarge.injective
  rw [map_add, equivLarge_mk, equivLarge_mk, equivLarge_mk, PicLarge.mk_tensor]

lemma mk_unit : mk (𝟙_ X.Modules) = 0 := by
  apply equivLarge.injective
  rw [map_zero, equivLarge_mk, PicLarge.mk_unit]

lemma mk_eq_zero_iff (L : X.Modules) [L.IsInvertible] :
    mk L = 0 ↔ Nonempty (L ≅ 𝟙_ X.Modules) := by
  rw [← mk_unit, mk_eq_mk_iff]

lemma mk_dual (L : X.Modules) [L.IsInvertible] : mk (dual L) = -mk L := by
  apply equivLarge.injective
  rw [map_neg, equivLarge_mk, equivLarge_mk, PicLarge.mk_dual]

/-- A representative of a class in the Picard group. -/
def rep (x : X.Pic) : X.Modules := PicLarge.rep (equivLarge x)

instance (x : X.Pic) : (rep x).IsInvertible := inferInstanceAs (PicLarge.rep _).IsInvertible

lemma mk_rep (x : X.Pic) : mk (rep x) = x := by
  apply equivLarge.injective
  rw [equivLarge_mk]
  exact PicLarge.mk_rep _

lemma rep_mk (L : X.Modules) [L.IsInvertible] : Nonempty (rep (mk L) ≅ L) :=
  mk_eq_mk_iff.mp (mk_rep (mk L))

lemma mk_surjective (x : X.Pic) : ∃ (L : X.Modules) (_ : L.IsInvertible), mk L = x :=
  ⟨rep x, inferInstance, mk_rep x⟩

/-- Induction principle for the Picard group. -/
@[elab_as_elim]
lemma ind {p : X.Pic → Prop} (h : ∀ (L : X.Modules) [L.IsInvertible], p (mk L)) (x : X.Pic) :
    p x := by
  rw [← mk_rep x]
  exact h _

end Pic

end AlgebraicGeometry.Scheme

end
