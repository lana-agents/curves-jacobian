/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TranslateRep

/-!
# Representability by translates for a functor identified with a restriction

This file is generic. Let `p : S' ⟶ S`, `G : (Sch/S)ᵒᵖ ⥤ Ab` and `G' : (Sch/S')ᵒᵖ ⥤ Ab`, together
with isomorphisms `Φ_t : G'(T, t) ≅ G(T, t ≫ p)`, natural in `T` (`G'` is the restriction of `G`
to `(Sch/S')`, e.g. `Pic_{C_L/L,σ}` and `Pic_{C/k,σ}` restricted to `(Sch/L)`). On all schemes
this gives `Ψ : G' ⟶ G`, `(t, y) ↦ (t ≫ p, Φ_t y)` (`restrictPt`, natural: `restrictPt_map`).

**`CurvesJacobian.isRepresentable_of_translate_restrict`**: if `F ⊆ G` is a representable open
subfunctor (cut out by a local predicate `P`, the inputs of `isRepresentable_of_translate`), `G'`
is a Zariski sheaf and every point of `G'` over a field has a translate by a global section of
`G'` (over `S'`) whose image under `Ψ` lies in `F`, then `G'` is representable. The proof applies
`isRepresentable_of_translate` (Stacks, Lemma 44.5.1, Tag 0B9Q) to `G'` and the subfunctor
`Ψ⁻¹ F`, which is open and represented by `Y ×_S S'`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Scheme.OpenSubfunctor

variable {S S' : Scheme.{u}} (p : S' ⟶ S) (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (G' : (Over S')ᵒᵖ ⥤ AddCommGrpCat.{u})
  (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ S'), G'.obj (op (Over.mk t)) ≃+ G.obj (op (Over.mk (t ≫ p))))

lemma heq_mapG {T : Scheme.{u}} {g₁ g₂ : T ⟶ S} (e : g₁ = g₂) {V : Over S} (a : T ⟶ V.left)
    (w₁ : a ≫ V.hom = g₁) (w₂ : a ≫ V.hom = g₂) (x : G.obj (op V)) :
    HEq ((G.map (Over.homMk a w₁ : Over.mk g₁ ⟶ V).op).hom x)
      ((G.map (Over.homMk a w₂ : Over.mk g₂ ⟶ V).op).hom x) := by
  subst e
  rfl

include p in
lemma comp_restrict_eq {T T' : Scheme.{u}} {a : T' ⟶ T} {t : T ⟶ S'} {t' : T' ⟶ S'}
    (w : a ≫ t = t') : a ≫ t ≫ p = t' ≫ p := by
  rw [← w, Category.assoc]

/-- Naturality of `Φ`. -/
def RestrictNatural : Prop :=
  ∀ {T T' : Scheme.{u}} (a : T' ⟶ T) (t : T ⟶ S') (t' : T' ⟶ S') (w : a ≫ t = t')
    (y : G'.obj (op (Over.mk t))),
    Φ t' ((G'.map (Over.homMk a w : Over.mk t' ⟶ Over.mk t).op).hom y) =
      (G.map (Over.homMk a (comp_restrict_eq p w) :
        Over.mk (t' ≫ p) ⟶ Over.mk (t ≫ p)).op).hom (Φ t y)

/-- `Ψ : G' ⟶ G` on points: `(t, y) ↦ (t ≫ p, Φ_t y)`. -/
def restrictPt {T : Scheme.{u}} (x : (sigmaG G').obj (op T)) : (sigmaG G).obj (op T) :=
  ⟨x.1 ≫ p, Φ x.1 x.2⟩

variable {p G G' Φ}

lemma restrictPt_map (hΦ : RestrictNatural p G G' Φ) {T T' : Scheme.{u}} (h : T' ⟶ T)
    (x : (sigmaG G').obj (op T)) :
    restrictPt p G G' Φ ((sigmaG G').map h.op x) = (sigmaG G).map h.op (restrictPt p G G' Φ x) := by
  obtain ⟨t, y⟩ := x
  change (⟨(h ≫ t) ≫ p, Φ (h ≫ t) ((G'.map (Over.homMk h rfl :
    Over.mk (h ≫ t) ⟶ Over.mk t).op).hom y)⟩ : (sigmaG G).obj (op T')) =
      ⟨h ≫ t ≫ p, (G.map (Over.homMk h rfl : Over.mk (h ≫ t ≫ p) ⟶ Over.mk (t ≫ p)).op).hom
        (Φ t y)⟩
  rw [hΦ h t (h ≫ t) rfl y]
  exact Sigma.ext (Category.assoc _ _ _) (heq_mapG G (Category.assoc _ _ _) h _ rfl (Φ t y))

lemma restrictPt_injective {T : Scheme.{u}} {x y : (sigmaG G').obj (op T)} (h1 : x.1 = y.1)
    (h2 : restrictPt p G G' Φ x = restrictPt p G G' Φ y) : x = y := by
  obtain ⟨t, a⟩ := x
  obtain ⟨t', b⟩ := y
  change t = t' at h1
  subst h1
  have h3 := eq_of_heq (Sigma.mk.inj_iff.mp h2).2
  exact Sigma.ext rfl (heq_of_eq ((Φ t).injective h3))

variable (hΦ : RestrictNatural p G G' Φ)
  (hG : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G))
  {P : ∀ T : Scheme.{u}, (sigmaG G).obj (op T) → Prop}

include hΦ in
lemma isLocalPredicate_restrict (hG' : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G'))
    (hP : IsLocalPredicate (sheafG G hG) P) :
    IsLocalPredicate (sheafG G' hG') (fun T x ↦ P T (restrictPt p G G' Φ x)) where
  map h x hx := by
    change P _ (restrictPt p G G' Φ ((sigmaG G').map h.op x))
    rw [restrictPt_map hΦ]
    exact hP.map h _ hx
  of_forall x hx := by
    refine hP.of_forall _ fun t ↦ ?_
    obtain ⟨U, htU, hU⟩ := hx t
    refine ⟨U, htU, ?_⟩
    change P _ (restrictPt p G G' Φ ((sigmaG G').map U.ι.op x)) at hU
    rw [restrictPt_map hΦ] at hU
    exact hU

include hΦ in
/-- **Representability of `G'` by translates** (Stacks, Lemma 44.5.1, Tag 0B9Q, applied to the
open subfunctor `Ψ⁻¹ F ⊆ G'`, represented by `Y ×_S S'`). -/
theorem isRepresentable_of_translate_restrict
    (hP : IsLocalPredicate (sheafG G hG) P)
    (hopen : ∀ (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)), ∃ U : T.Opens,
      ∀ (T' : Scheme.{u}) [IsAffine T'] (h : T' ⟶ T),
        P T' ((sigmaG G).map h.op x) ↔ Set.range h ⊆ U)
    {Y : Scheme.{u}} (ξ : (sigmaG G).obj (op Y))
    (hinj : ∀ (T : Scheme.{u}) [IsAffine T],
      Function.Injective fun a : T ⟶ Y ↦ (sigmaG G).map a.op ξ)
    (hrange : ∀ (T : Scheme.{u}) [IsAffine T] (x : (sigmaG G).obj (op T)),
      P T x ↔ ∃ a : T ⟶ Y, (sigmaG G).map a.op ξ = x)
    (hG' : Presieve.IsSheaf Scheme.zariskiTopology (sigmaG G'))
    (hfield : ∀ (K : CommRingCat.{u}), IsField K → ∀ x : (sigmaG G').obj (op (Spec K)),
      ∃ c : G'.obj (op (Over.mk (𝟙 S'))), P _ (restrictPt p G G' Φ (translate G' c x))) :
    (sigmaG G').IsRepresentable := by
  let Y' := pullback ξ.1 p
  let ξ' : (sigmaG G').obj (op Y') := ⟨pullback.snd ξ.1 p, (Φ _).symm
    ((G.map (Over.homMk (pullback.fst ξ.1 p) pullback.condition :
      Over.mk (pullback.snd ξ.1 p ≫ p) ⟶ Over.mk ξ.1).op).hom ξ.2)⟩
  have hξ' : restrictPt p G G' Φ ξ' = (sigmaG G).map (pullback.fst ξ.1 p).op ξ := by
    change (⟨pullback.snd ξ.1 p ≫ p, Φ _ ((Φ _).symm _)⟩ : (sigmaG G).obj (op Y')) = _
    rw [AddEquiv.apply_symm_apply]
    exact Sigma.ext pullback.condition.symm (heq_mapG G pullback.condition.symm _ _ rfl ξ.2)
  have hmap : ∀ {T : Scheme.{u}} (a : T ⟶ Y'),
      restrictPt p G G' Φ ((sigmaG G').map a.op ξ') =
        (sigmaG G).map (a ≫ pullback.fst ξ.1 p).op ξ := by
    intro T a
    rw [restrictPt_map hΦ, hξ', op_comp, Functor.map_comp_apply]
  refine isRepresentable_of_translate G' hG' (isLocalPredicate_restrict hΦ hG hG' hP)
    (fun T _ x ↦ ?_) ξ' (fun T _ ↦ ?_) (fun T _ x ↦ ?_) hfield
  · obtain ⟨U, hU⟩ := hopen T (restrictPt p G G' Φ x)
    refine ⟨U, fun T' _ h ↦ ?_⟩
    change P T' (restrictPt p G G' Φ ((sigmaG G').map h.op x)) ↔ _
    rw [restrictPt_map hΦ]
    exact hU T' h
  · intro a b hab
    have h1 : a ≫ pullback.snd ξ.1 p = b ≫ pullback.snd ξ.1 p := congrArg Sigma.fst hab
    have h2 := congrArg (restrictPt p G G' Φ) hab
    simp only [hmap] at h2
    have h3 := hinj T h2
    exact pullback.hom_ext h3 h1
  · change P T (restrictPt p G G' Φ x) ↔ _
    rw [hrange]
    constructor
    · rintro ⟨w, hw⟩
      have hw1 : w ≫ ξ.1 = x.1 ≫ p := congrArg Sigma.fst hw
      refine ⟨pullback.lift w x.1 hw1, restrictPt_injective (p := p) (G := G) (Φ := Φ)
        (pullback.lift_snd _ _ _) ?_⟩
      rw [hmap, pullback.lift_fst]
      exact hw
    · rintro ⟨a, rfl⟩
      exact ⟨_, (hmap a).symm⟩

end CurvesJacobian
