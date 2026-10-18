/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.LocIso

/-!
# Section-wise isomorphisms and evaluations along open immersions

This file is generic. We transport the notions of `CurvesJacobian.Picard.LocIso` along open
immersions: isomorphisms of restrictions along an open immersion `q` are the same as
section-wise isomorphisms on the range of `q` (`LocIso.ofRestrictIso`,
`LocIso.nonempty_restrictIso`), and an evaluation along a section `s'` of `L` on `Y'` gives one
of `j_* L` on the range of an open immersion `j : Y' ⟶ Y` (`Rig.pushforward`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme Scheme.Modules

variable {Y T : Scheme.{u}} {s : T ⟶ Y}

section OpenImmersion

variable {Y' T' : Scheme.{u}}

lemma image_preimage_eq_of_le (q : Y' ⟶ Y) [IsOpenImmersion q] {W : Y.Opens}
    (hW : W ≤ q.opensRange) : q ''ᵁ (q ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.2 hW

/-- A morphism of restrictions along an open immersion is linear over `Γ(Y, q ''ᵁ U)`. -/
lemma restrict_app_smul (q : Y' ⟶ Y) [IsOpenImmersion q] {M N : Y.Modules}
    (f : M.restrict q ⟶ N.restrict q) (U : Y'.Opens) (r : Γ(Y, q ''ᵁ U))
    (x : Γ(M, q ''ᵁ U)) :
    f.app U (r • x) = r • (show Γ(N, q ''ᵁ U) from f.app U x) := by
  have h1 : r = (q.appIso U).inv ((q.appIso U).hom r) := by simp
  rw [h1]
  exact Scheme.Modules.Hom.app_smul f ((q.appIso U).hom r) x

/-- An isomorphism of restrictions along an open immersion `q` gives a section-wise isomorphism
on the range of `q`. -/
def LocIso.ofRestrictIso (q : Y' ⟶ Y) [IsOpenImmersion q] {M N : Y.Modules}
    (e : M.restrict q ≅ N.restrict q) : LocIso M N q.opensRange where
  φ W hW :=
    (N.presheaf.map (homOfLE (image_preimage_eq_of_le q hW).ge).op).hom.comp
      ((e.hom.app (q ⁻¹ᵁ W)).hom.comp
        (M.presheaf.map (homOfLE (image_preimage_eq_of_le q hW).le).op).hom)
  φ_smul W hW c m := by
    change rs N _ (e.hom.app _ (rs M _ (c • m))) = c • rs N _ (e.hom.app _ (rs M _ m))
    rw [rs_smul, restrict_app_smul, rs_smul, rr_rr, rr_self]
  φ_rs W W' hW h m := by
    change rs N _ (e.hom.app _ (rs M _ (rs M h m))) = rs N h (rs N _ (e.hom.app _ (rs M _ m)))
    have hU : q ⁻¹ᵁ W' ≤ q ⁻¹ᵁ W := q.preimage_mono h
    have hnat := app_rs e.hom hU (rs M (image_preimage_eq_of_le q hW).le m)
    change e.hom.app _ (rs M (q.image_mono hU) _) = rs N (q.image_mono hU) _ at hnat
    rw [rs_rs, rs_rs, ← rs_rs M (image_preimage_eq_of_le q hW).le (q.image_mono hU), hnat,
      rs_rs]
  bij W hW := by
    change Function.Bijective (fun m ↦ rs N (image_preimage_eq_of_le q hW).ge
      (e.hom.app (q ⁻¹ᵁ W) (rs M (image_preimage_eq_of_le q hW).le m)))
    exact (rs_bijective_of_eq N (image_preimage_eq_of_le q hW).symm).comp
      ((ConcreteCategory.bijective_of_isIso (e.hom.app (q ⁻¹ᵁ W))).comp
        (rs_bijective_of_eq M (image_preimage_eq_of_le q hW)))

/-- A section-wise isomorphism on the range of an open immersion `q` gives an isomorphism of
restrictions along `q`. -/
theorem LocIso.nonempty_restrictIso (q : Y' ⟶ Y) [IsOpenImmersion q] {M N : Y.Modules}
    (Φ : LocIso M N q.opensRange) : Nonempty (M.restrict q ≅ N.restrict q) := by
  let F : M.restrict q ⟶ N.restrict q :=
    (SheafOfModules.fullyFaithfulForget _).preimage
      (_root_.PresheafOfModules.homMk
        { app U := AddCommGrpCat.ofHom (Φ.φ (q ''ᵁ U.unop) (q.image_le_opensRange U.unop))
          naturality U U' f := by
            ext m
            exact Φ.φ_rs _ _ (q.image_le_opensRange U.unop) (q.image_mono f.unop.le) m }
        (fun U r m ↦ Φ.φ_smul _ _ ((q.appIso U.unop).inv r) m))
  have hF : ∀ U : Y'.Opens, Function.Bijective (F.app U) := fun U ↦
    Φ.bij (q ''ᵁ U) (q.image_le_opensRange U)
  have : IsIso F := Scheme.Modules.isIso_of_forall_bijective F fun x ↦
    ⟨⊤, trivial, fun V _ ↦ hF V⟩
  exact ⟨asIso F⟩

/-- `(j_* L)|_{p ≫ j} ≅ L|_p` for open immersions `p`, `j`. -/
def pushforwardRestrictCompIso {Y'' : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    (p : Y'' ⟶ Y') [IsOpenImmersion p] (L : Y'.Modules) :
    ((pushforward j).obj L).restrict (p ≫ j) ≅ L.restrict p :=
  (restrictFunctorComp p j).app _ ≪≫ (restrictFunctor p).mapIso
    ((restrictFunctorAdjCounitIso j).app L)

/-- A basis of `L` on `j⁻¹ U` is a basis of `j_* L` on `U ⊆ j(Y')`. -/
lemma isBasisOn_pushforward (j : Y' ⟶ Y) [IsOpenImmersion j] {L : Y'.Modules} {U : Y.Opens}
    (hU : U ≤ j.opensRange) {b : Γ(L, j ⁻¹ᵁ U)} (hb : L.IsBasisOn (j ⁻¹ᵁ U) b) :
    ((pushforward j).obj L).IsBasisOn U b := by
  intro V h
  haveI := j.isIso_app V (h.trans hU)
  exact (hb (j.preimage_mono h)).comp (ConcreteCategory.bijective_of_isIso (j.app V))

/-- A basis of `j_* L` on `U ⊆ j(Y')` is a basis of `L` on `j⁻¹ U`. -/
lemma isBasisOn_of_pushforward (j : Y' ⟶ Y) [IsOpenImmersion j] {L : Y'.Modules}
    {U : Y.Opens} (hU : U ≤ j.opensRange) {b : Γ(L, j ⁻¹ᵁ U)}
    (hb : ((pushforward j).obj L).IsBasisOn U b) : L.IsBasisOn (j ⁻¹ᵁ U) b := by
  intro V h
  have hV : j ''ᵁ V ≤ U := (j.image_mono h).trans (j.image_preimage_le U)
  haveI := j.isIso_app (j ''ᵁ V) (hV.trans hU)
  have h1 := hb hV
  have h2 : Function.Bijective (fun r : Γ(Y', j ⁻¹ᵁ (j ''ᵁ V)) ↦
      r • Scheme.PresheafOfModules.res ((toPresheafOfModules Y').obj L)
        (j.preimage_mono hV) b) :=
    (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso
      (j.app (j ''ᵁ V)))).1 h1
  exact (Scheme.PresheafOfModules.bijective_res_congr (j.preimage_image_eq V) _ _ _).1 h2

lemma isInvOn_pushforward (j : Y' ⟶ Y) [IsOpenImmersion j] (L : Y'.Modules) [L.IsInvertible] :
    IsInvOn ((pushforward j).obj L) j.opensRange := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨U', b, hx, hb⟩ := IsInvertible.exists_basis (L := L) x
  refine ⟨j ''ᵁ U', rs L (j.preimage_image_eq U').le b, j.image_le_opensRange U', ⟨x, hx, rfl⟩,
    isBasisOn_pushforward j (j.image_le_opensRange U') ?_⟩
  exact Scheme.PresheafOfModules.IsBasisOn.restrict hb _

lemma preimage_eq_of_comm (j : Y' ⟶ Y) (t : T' ⟶ T) (s' : T' ⟶ Y') (w : s' ≫ j = t ≫ s)
    (W : Y.Opens) : t ⁻¹ᵁ s ⁻¹ᵁ W = s' ⁻¹ᵁ j ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]

lemma preimage_le_of_le {j : Y' ⟶ Y} [IsOpenImmersion j] {t : T' ⟶ T} [IsOpenImmersion t]
    (hst : s ⁻¹ᵁ j.opensRange ≤ t.opensRange) {W : Y.Opens} (hW : W ≤ j.opensRange) :
    s ⁻¹ᵁ W ≤ t.opensRange :=
  (s.preimage_mono hW).trans hst

/-- The inverse of `t^♯ : Γ(T, U) ⟶ Γ(T', t⁻¹ U)` for `U` in the range of the open immersion
`t`. -/
def pushInv (t : T' ⟶ T) [IsOpenImmersion t] {U : T.Opens} (hU : U ≤ t.opensRange) :
    Γ(T', t ⁻¹ᵁ U) ≃+* Γ(T, U) :=
  haveI := t.isIso_app U hU
  (asIso (t.app U)).commRingCatIsoToRingEquiv.symm

lemma pushInv_app (t : T' ⟶ T) [IsOpenImmersion t] {U : T.Opens} (hU : U ≤ t.opensRange)
    (c : Γ(T, U)) : pushInv t hU (t.app U c) = c :=
  (pushInv t hU).apply_symm_apply c

lemma app_pushInv (t : T' ⟶ T) [IsOpenImmersion t] {U : T.Opens} (hU : U ≤ t.opensRange)
    (x : Γ(T', t ⁻¹ᵁ U)) : t.app U (pushInv t hU x) = x :=
  (pushInv t hU).symm_apply_apply x

lemma pushInv_rr (t : T' ⟶ T) [IsOpenImmersion t] {U U' : T.Opens} (hU : U ≤ t.opensRange)
    (h : U' ≤ U) (x : Γ(T', t ⁻¹ᵁ U)) :
    pushInv t (h.trans hU) (rr (t.preimage_mono h) x) = rr h (pushInv t hU x) := by
  apply (pushInv t (h.trans hU)).symm.injective
  change t.app U' (pushInv t _ _) = t.app U' (rr h (pushInv t hU x))
  rw [app_pushInv]
  change _ = (T.presheaf.map (homOfLE h).op ≫ t.app U') _
  rw [t.naturality]
  change _ = rr _ (t.app U (pushInv t hU x))
  rw [app_pushInv]

lemma map_endo_eq_id {X : Scheme.{u}} {U : X.Opens} (f : op U ⟶ op U) :
    X.presheaf.map f = 𝟙 _ := by
  have : f = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, CategoryTheory.Functor.map_id]

lemma rr_app_comm (j : Y' ⟶ Y) (t : T' ⟶ T) (s' : T' ⟶ Y') (w : s' ≫ j = t ≫ s)
    (W : Y.Opens) (c : Γ(Y, W)) :
    rr (preimage_eq_of_comm j t s' w W).le (s'.app (j ⁻¹ᵁ W) (j.app W c)) =
      t.app (s ⁻¹ᵁ W) (s.app W c) := by
  change ((s' ≫ j).app W ≫ T'.presheaf.map
    (homOfLE (preimage_eq_of_comm j t s' w W).le).op) c = ((t ≫ s).app W) c
  rw [Scheme.Hom.congr_app w W, Category.assoc, ← Functor.map_comp]
  erw [map_endo_eq_id]
  rfl

/-- Transport of an evaluation along a section through open immersions: if `s' : T' ⟶ Y'`,
`j : Y' ⟶ Y`, `t : T' ⟶ T` with `s' ≫ j = t ≫ s` and `s⁻¹(j(Y')) ⊆ t(T')`, an evaluation of
`L` along `s'` gives one of `j_* L` along `s` on the range of `j`. -/
def Rig.pushforward (j : Y' ⟶ Y) [IsOpenImmersion j] (t : T' ⟶ T) [IsOpenImmersion t]
    (s' : T' ⟶ Y') (w : s' ≫ j = t ≫ s) (hst : s ⁻¹ᵁ j.opensRange ≤ t.opensRange)
    {L : Y'.Modules} (χ : Rig s' L ⊤) : Rig s ((pushforward j).obj L) j.opensRange where
  χ W hW := (pushInv t (preimage_le_of_le hst hW)).toRingHom.toAddMonoidHom.comp
    ((T'.presheaf.map (homOfLE (preimage_eq_of_comm j t s' w W).le).op).hom.toAddMonoidHom.comp
      (χ.χ (j ⁻¹ᵁ W) le_top))
  χ_smul W hW c m := by
    change pushInv t (preimage_le_of_le hst hW) (rr (preimage_eq_of_comm j t s' w W).le
        (χ.χ (j ⁻¹ᵁ W) le_top (j.app W c • (show Γ(L, j ⁻¹ᵁ W) from m)))) =
      s.app W c * pushInv t (preimage_le_of_le hst hW)
        (rr (preimage_eq_of_comm j t s' w W).le (χ.χ (j ⁻¹ᵁ W) le_top m))
    rw [χ.χ_smul, rr_mul, RingEquiv.map_mul, rr_app_comm j t s' w W c, pushInv_app]
  χ_rs W W' hW h m := by
    change pushInv t (preimage_le_of_le hst (h.trans hW)) (rr (preimage_eq_of_comm j t s' w W').le
        (χ.χ (j ⁻¹ᵁ W') le_top (rs L (j.preimage_mono h) m))) =
      rr (s.preimage_mono h) (pushInv t (preimage_le_of_le hst hW)
        (rr (preimage_eq_of_comm j t s' w W).le (χ.χ (j ⁻¹ᵁ W) le_top m)))
    rw [χ.χ_rs _ _ le_top (j.preimage_mono h), rr_rr, ← pushInv_rr, rr_rr]
  isUnit_χ W hW e he := by
    change IsUnit (pushInv t (preimage_le_of_le hst hW)
      (rr (preimage_eq_of_comm j t s' w W).le (χ.χ (j ⁻¹ᵁ W) le_top e)))
    exact ((χ.isUnit_χ _ le_top e (isBasisOn_of_pushforward j hW he)).map _).map _

end OpenImmersion

end CurvesJacobian.ModulesGlue
