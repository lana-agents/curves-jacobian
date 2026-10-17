/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.OverSigma
import CurvesJacobian.Picard.OpenSubfunctor
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Representability by translates of an open subfunctor (Stacks, Lemma 44.5.1, Tag 0B9Q)

This file is generic. Let `S` be a scheme and `G : (Sch/S)ᵒᵖ ⥤ Ab` a functor of abelian groups,
viewed as a functor on all schemes via `overSigma` (`T ↦ Σ (g : T ⟶ S), G(T, g)`). A global
section `c ∈ G(S)` acts on every `G(T)` by translation `x ↦ c|_T + x` (`translate`), compatibly
with pullbacks (`map_translate`).

**Stacks, Lemma 44.5.1 (Tag 0B9Q)** (`isRepresentable_of_translate`): assume that `G` is a
sheaf for the Zariski topology, that `F ⊆ G` is a subfunctor (given by a Zariski-local predicate
`p`) which is representable and open, and that for every field `K` and every `x ∈ G(Spec K)`
there is `c ∈ G(S)` with `c + x ∈ F(Spec K)`. Then `G` is representable. As in Stacks, the
proof covers `G` by the translates `F_c = {x | c + x ∈ F}`, `c ∈ G(S)`, each isomorphic to `F`
by translation, and applies the gluing criterion of Schemes, Lemma 26.15.4 (Tag 01JJ, here
`AlgebraicGeometry.Scheme.OpenSubfunctor.isRepresentable_of_isAffine`, built on Mathlib's
`LocalRepresentability`). The covering condition at a point `t ∈ T` is checked at the field
point `Spec κ(t) ⟶ T`, whose image is `{t}`.

Stacks states the lemma over `S = Spec k`; the argument works for every base `S` (with the
group `G(S)` of global sections acting).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace CurvesJacobian

variable {S : Scheme.{u}} (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- `G` as a functor on all schemes: `T ↦ Σ (g : T ⟶ S), G(T, g)`. -/
abbrev sigmaG : Scheme.{u}ᵒᵖ ⥤ Type u := overSigma (G ⋙ forget AddCommGrpCat)

lemma sigmaG_map_mk {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S)
    (y : G.obj (op (Over.mk g))) :
    (sigmaG G).map h.op ⟨g, y⟩ =
      ⟨h ≫ g, (G.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g).op).hom y⟩ :=
  rfl

/-- An element of `(G ⋙ forget).obj X` as an element of the group `G.obj X`. -/
def asG {X : (Over S)ᵒᵖ} (y : (G ⋙ forget AddCommGrpCat).obj X) : G.obj X := y

/-- The morphism `(T, g) ⟶ (S, 𝟙)` in `Over S`. -/
def toTop {T : Scheme.{u}} (g : T ⟶ S) : Over.mk g ⟶ Over.mk (𝟙 S) :=
  Over.homMk g (Category.comp_id g)

/-- The restriction `c|_T ∈ G(T, g)` of a global section `c ∈ G(S)`. -/
def restr (c : G.obj (op (Over.mk (𝟙 S)))) {T : Scheme.{u}} (g : T ⟶ S) :
    G.obj (op (Over.mk g)) :=
  (G.map (toTop g).op).hom c

lemma restr_add (c c' : G.obj (op (Over.mk (𝟙 S)))) {T : Scheme.{u}} (g : T ⟶ S) :
    restr G (c + c') g = restr G c g + restr G c' g :=
  map_add _ _ _

lemma restr_zero {T : Scheme.{u}} (g : T ⟶ S) : restr G 0 g = 0 :=
  map_zero _

lemma map_restr (c : G.obj (op (Over.mk (𝟙 S)))) {T T' : Scheme.{u}} (h : T' ⟶ T)
    (g : T ⟶ S) :
    (G.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g).op).hom (restr G c g) =
      restr G c (h ≫ g) := by
  have : toTop (h ≫ g) = (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g) ≫ toTop g := rfl
  rw [restr, restr, this, op_comp, G.map_comp]
  rfl

/-- Translation by a global section: `x ↦ c|_T + x`. -/
def translate (c : G.obj (op (Over.mk (𝟙 S)))) {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) :
    (sigmaG G).obj (op T) :=
  ⟨x.1, restr G c x.1 + asG G x.2⟩

lemma map_translate (c : G.obj (op (Over.mk (𝟙 S)))) {T T' : Scheme.{u}} (h : T' ⟶ T)
    (x : (sigmaG G).obj (op T)) :
    (sigmaG G).map h.op (translate G c x) = translate G c ((sigmaG G).map h.op x) := by
  obtain ⟨g, y⟩ := x
  refine Sigma.ext rfl (heq_of_eq ?_)
  change (G.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g).op).hom
      (restr G c g + asG G y) = restr G c (h ≫ g) +
    (G.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g).op).hom (asG G y)
  rw [map_add, map_restr]

lemma translate_translate (c c' : G.obj (op (Over.mk (𝟙 S)))) {T : Scheme.{u}}
    (x : (sigmaG G).obj (op T)) :
    translate G c (translate G c' x) = translate G (c + c') x := by
  obtain ⟨g, y⟩ := x
  change (⟨g, restr G c g + (restr G c' g + asG G y)⟩ :
    (sigmaG G).obj (op T)) = ⟨g, restr G (c + c') g + asG G y⟩
  rw [restr_add, add_assoc]

lemma translate_zero {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) : translate G 0 x = x := by
  obtain ⟨g, y⟩ := x
  change (⟨g, restr G 0 g + asG G y⟩ : (sigmaG G).obj (op T)) = ⟨g, y⟩
  rw [restr_zero, zero_add]
  rfl

lemma translate_neg_translate (c : G.obj (op (Over.mk (𝟙 S)))) {T : Scheme.{u}}
    (x : (sigmaG G).obj (op T)) : translate G (-c) (translate G c x) = x := by
  rw [translate_translate, neg_add_cancel, translate_zero]

lemma translate_translate_neg (c : G.obj (op (Over.mk (𝟙 S)))) {T : Scheme.{u}}
    (x : (sigmaG G).obj (op T)) : translate G c (translate G (-c) x) = x := by
  rw [translate_translate, add_neg_cancel, translate_zero]

lemma translate_injective (c : G.obj (op (Over.mk (𝟙 S)))) (T : Scheme.{u}) :
    Function.Injective (translate G c (T := T)) :=
  Function.LeftInverse.injective (translate_neg_translate G c)

lemma translate_neg_eq_iff (c : G.obj (op (Over.mk (𝟙 S)))) {T : Scheme.{u}}
    (x y : (sigmaG G).obj (op T)) : translate G (-c) y = x ↔ y = translate G c x := by
  constructor
  · rintro rfl
    rw [translate_translate_neg]
  · rintro rfl
    rw [translate_neg_translate]

/-- `G` as a Zariski sheaf, given the sheaf property. -/
def sheafG (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G)) :
    Sheaf Scheme.zariskiTopology.{u} (Type u) where
  obj := sigmaG G
  property := (isSheaf_iff_isSheaf_of_type _ _).mpr hG

open Scheme.OpenSubfunctor in
/-- **Stacks, Lemma 44.5.1 (Tag 0B9Q).** Let `G : (Sch/S)ᵒᵖ ⥤ Ab` be a Zariski sheaf and let
`F ⊆ G` be the subfunctor cut out by a Zariski-local predicate `p`. Assume that, tested on affine
schemes, `F ⊆ G` is open (`hopen`) and `F` is represented by `Y` with universal element `ξ`
(`hinj`, `hrange`), and that for every field `K` every `x ∈ G(Spec K)` has a translate by a
global section `c ∈ G(S)` lying in `F` (`hfield`). Then `G` is representable. -/
theorem isRepresentable_of_translate
    (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
    {p : ∀ T : Scheme.{u}, (sigmaG G).obj (op T) → Prop}
    (hp : IsLocalPredicate (sheafG G hG) p)
    (hopen : ∀ (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)), ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        p T' ((sigmaG G).map h.op x) ↔ Set.range h ⊆ U)
    {Y : Scheme.{u}} (ξ : (sigmaG G).obj (op Y))
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y ↦ (sigmaG G).map a.op ξ)
    (hrange : ∀ (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)),
      p T x ↔ ∃ a : T ⟶ Y, (sigmaG G).map a.op ξ = x)
    (hfield : ∀ (K : CommRingCat.{u}), IsField K → ∀ x : (sigmaG G).obj (op (Spec K)),
      ∃ c : G.obj (op (Over.mk (𝟙 S))), p _ (translate G c x)) :
    (sigmaG G).IsRepresentable := by
  have hopen' (c : G.obj (op (Over.mk (𝟙 S)))) (T : Scheme.{u}) [IsAffine T]
      (x : (sigmaG G).obj (op T)) : ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        p T' (translate G c ((sigmaG G).map h.op x)) ↔ Set.range h ⊆ U := by
    obtain ⟨U, hU⟩ := hopen T (translate G c x)
    exact ⟨U, fun T' _ h ↦ by rw [← map_translate]; exact hU T' h⟩
  refine isRepresentable_of_isAffine (F := sheafG G hG) (ι := G.obj (op (Over.mk (𝟙 S))))
    (p := fun c T x ↦ p T (translate G c x)) (fun c ↦ ⟨fun h x hx ↦ ?_, fun x hx ↦ ?_⟩)
    (hopen') (Y := fun _ ↦ Y) (fun c ↦ translate G (-c) ξ) (fun c T _ ↦ ?_)
    (fun c T _ x ↦ ?_) (fun T _ x t ↦ ?_)
  · change p _ (translate G c ((sigmaG G).map h.op x))
    rw [← map_translate]
    exact hp.map h _ hx
  · refine hp.of_forall _ fun t ↦ ?_
    obtain ⟨U, htU, hU⟩ := hx t
    refine ⟨U, htU, ?_⟩
    change p _ ((sigmaG G).map U.ι.op (translate G c x))
    rw [map_translate]
    exact hU
  · intro a b hab
    refine hinj T ?_
    change (sigmaG G).map a.op (translate G (-c) ξ) = (sigmaG G).map b.op (translate G (-c) ξ)
      at hab
    rw [map_translate, map_translate] at hab
    exact translate_injective G (-c) T hab
  · change p T (translate G c x) ↔ ∃ a : T ⟶ Y, (sigmaG G).map a.op (translate G (-c) ξ) = x
    rw [hrange]
    simp only [map_translate, translate_neg_eq_iff]
  · let K := T.residueField t
    have hK : IsField K := Field.toIsField _
    obtain ⟨c, hc⟩ := hfield K hK ((sigmaG G).map (T.fromSpecResidueField t).op x)
    obtain ⟨U, hU⟩ := hopen' c T x
    refine ⟨c, U, hU, ?_⟩
    have := (hU (Spec K) (T.fromSpecResidueField t)).1 hc
    rw [Scheme.range_fromSpecResidueField] at this
    exact this rfl

end CurvesJacobian
