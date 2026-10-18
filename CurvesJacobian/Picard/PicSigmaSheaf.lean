/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RigidGlue
import CurvesJacobian.Picard.LocIsoOpen
import CurvesJacobian.Picard.PicSigma
import CurvesJacobian.Picard.PicSpecEquiv
import CurvesJacobian.Picard.OverSigmaSheaf

/-!
# The Zariski sheaf property of `Pic_{X/S,σ}`

Let `f : X ⟶ S` have a section `σ`, and assume that for every `g : T ⟶ S` the map
`Γ(T, U) ⟶ Γ(X_T, f_T⁻¹ U)` is surjective for all opens `U ⊆ T` (for curves this is
`𝒪_T ≅ f_{T,*}𝒪_{X_T}`, Stacks, Lemma 44.6.1, Tag 0B9U). Then the rigidified Picard functor
`Pic_{X/S,σ}(T) = Ker(σ_T^* : Pic(X_T) ⟶ Pic(T))` (Stacks, Section 44.6, Tag 0B9R) satisfies
the sheaf condition for open covers (`isSheafOver_picSigma`).

Proof (as in Stacks, proof of Lemma 44.4.3, Tag 0B9N): an element of `Pic_{X/S,σ}(T_a)` is an
invertible sheaf `L_a` on `X_{T_a}` with a trivialisation of `σ_{T_a}^* L_a`; its pushforward to
`X_T` carries an evaluation along `σ_T` on the open `X_{T_a} ⊆ X_T` (`Rig.pushforward`).
Isomorphisms on overlaps can be chosen compatible with these evaluations, are then unique, and
so glue (`ModulesGlue.glueDataOfRigid`); uniqueness is `ModulesGlue.nonempty_iso_unit_of_rig`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open ModulesGlue Scheme Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

section Generic

variable {T T' : Scheme.{u}}

lemma opensRange_bcMap (a : T' ⟶ T) [IsOpenImmersion a] (g : T ⟶ S) (g' : T' ⟶ S)
    (w : a ≫ g = g') :
    (bcMap f a g g' w).opensRange = pullback.snd f g ⁻¹ᵁ a.opensRange := by
  have h := (isPullback_bcMap f a g g' w).flip
  have e := Scheme.Hom.opensRange_comp_of_isIso h.isoPullback.hom
    (pullback.snd a (pullback.snd f g))
  rw [Scheme.Hom.opensRange_pullbackSnd] at e
  simp only [h.isoPullback_hom_snd] at e
  exact e

lemma preimage_secT_preimage_snd (g : T ⟶ S) (U : T.Opens) :
    secT f σ hσ g ⁻¹ᵁ (pullback.snd f g ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, secT_snd, Scheme.Hom.id_preimage]

lemma isSaturated_preimage_snd (g : T ⟶ S) (U : T.Opens) :
    pullback.snd f g ⁻¹ᵁ (secT f σ hσ g ⁻¹ᵁ (pullback.snd f g ⁻¹ᵁ U)) =
      pullback.snd f g ⁻¹ᵁ U := by
  rw [preimage_secT_preimage_snd]

/-- A class in the kernel of `s^*` has a trivialisation of the pullback of its representative. -/
lemma nonempty_trivialisation {Z W : Scheme.{u}} (s : W ⟶ Z) (x : Z.Pic)
    (hx : Pic.map s x = 0) :
    Nonempty ((Modules.pullback s).obj (Pic.rep x) ≅ SheafOfModules.unit W.ringCatSheaf) := by
  rw [← Pic.mk_rep x, Pic.map_mk, Pic.mk_eq_zero_iff] at hx
  exact ⟨hx.some ≪≫ (structureSheafIsoUnit W).symm⟩

lemma pic_map_eq_zero_of_nonempty {Z W : Scheme.{u}} (s : W ⟶ Z) (L : Z.Modules) [L.IsInvertible]
    (h : Nonempty ((Modules.pullback s).obj L ≅ SheafOfModules.unit W.ringCatSheaf)) :
    Pic.map s (Pic.mk L) = 0 := by
  rw [Pic.map_mk, Pic.mk_eq_zero_iff]
  exact ⟨h.some ≪≫ structureSheafIsoUnit W⟩

end Generic

section Cover

variable {T : Scheme.{u}} (g : T ⟶ S) (𝓤 : Scheme.OpenCover.{u} T)

/-- The open immersion `X_{T_a} ⟶ X_T`. -/
abbrev jMap (a : 𝓤.I₀) : pullback f (𝓤.f a ≫ g) ⟶ pullback f g := bcMap f (𝓤.f a) g _ rfl

/-- The open `X_{T_a} ⊆ X_T`. -/
def coverV (a : 𝓤.I₀) : (pullback f g).Opens := pullback.snd f g ⁻¹ᵁ (𝓤.f a).opensRange

lemma opensRange_jMap (a : 𝓤.I₀) : (jMap f g 𝓤 a).opensRange = coverV f g 𝓤 a :=
  opensRange_bcMap f _ g _ rfl

lemma coverV_covers (y : ↥(pullback f g)) : ∃ a, y ∈ coverV f g 𝓤 a :=
  ⟨𝓤.idx (pullback.snd f g y), 𝓤.covers _⟩

lemma isSaturated_coverV (a : 𝓤.I₀) :
    pullback.snd f g ⁻¹ᵁ (secT f σ hσ g ⁻¹ᵁ coverV f g 𝓤 a) = coverV f g 𝓤 a :=
  isSaturated_preimage_snd f σ hσ g _

lemma preimage_secT_coverV_le (a : 𝓤.I₀) :
    secT f σ hσ g ⁻¹ᵁ (jMap f g 𝓤 a).opensRange ≤ (𝓤.f a).opensRange := by
  rw [opensRange_jMap, coverV, preimage_secT_preimage_snd]

variable (y : ∀ a, picSigmaGrp f σ hσ (𝓤.f a ≫ g))

/-- The sheaf on `X_T` attached to `y a`: the pushforward of a representative. -/
def coverM (a : 𝓤.I₀) : (pullback f g).Modules :=
  (pushforward (jMap f g 𝓤 a)).obj (Pic.rep (y a).1)

lemma isInvOn_coverM (a : 𝓤.I₀) : IsInvOn (coverM f σ hσ g 𝓤 y a) (coverV f g 𝓤 a) :=
  opensRange_jMap f g 𝓤 a ▸ isInvOn_pushforward _ _

/-- The evaluation along `σ_T` of `coverM` on `X_{T_a}`, from a trivialisation along
`σ_{T_a}`. -/
def coverRig (a : 𝓤.I₀) : Rig (secT f σ hσ g) (coverM f σ hσ g 𝓤 y a) (coverV f g 𝓤 a) :=
  opensRange_jMap f g 𝓤 a ▸ Rig.pushforward (jMap f g 𝓤 a) (𝓤.f a)
    (secT f σ hσ (𝓤.f a ≫ g)) (secT_bcMap f σ hσ _ _ _ _) (preimage_secT_coverV_le f σ hσ g 𝓤 a)
    (Rig.ofIso _ _ (nonempty_trivialisation _ _ (y a).2).some)

/-- The projection `X_{T_a} ×_{X_T} X_{T_b} = X_{T_a ×_T T_b} ⟶ X_{T_a}`. -/
abbrev pMapL (a b : 𝓤.I₀) :
    pullback f (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a ≫ g) ⟶ pullback f (𝓤.f a ≫ g) :=
  bcMap f (pullback.fst (𝓤.f a) (𝓤.f b)) (𝓤.f a ≫ g) _ rfl

/-- The projection `X_{T_a ×_T T_b} ⟶ X_{T_b}`. -/
abbrev pMapR (a b : 𝓤.I₀) :
    pullback f (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a ≫ g) ⟶ pullback f (𝓤.f b ≫ g) :=
  bcMap f (pullback.snd (𝓤.f a) (𝓤.f b)) (𝓤.f b ≫ g) _ (pullback.condition_assoc g).symm

lemma pMapL_jMap (a b : 𝓤.I₀) :
    pMapL f g 𝓤 a b ≫ jMap f g 𝓤 a = pMapR f g 𝓤 a b ≫ jMap f g 𝓤 b := by
  apply pullback.hom_ext
  · simp
  · simp [pullback.condition]

lemma le_opensRange_pMapL_jMap (a b : 𝓤.I₀) :
    coverV f g 𝓤 a ⊓ coverV f g 𝓤 b ≤ (pMapL f g 𝓤 a b ≫ jMap f g 𝓤 a).opensRange := by
  have : pMapL f g 𝓤 a b ≫ jMap f g 𝓤 a =
      bcMap f (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a) g _ (Category.assoc _ _ _) := by
    apply pullback.hom_ext <;> simp
  intro x hx
  change x ∈ Set.range (pMapL f g 𝓤 a b ≫ jMap f g 𝓤 a)
  rw [this]
  refine (opensRange_bcMap f (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a) g _
    (Category.assoc _ _ _)).ge ?_
  change pullback.snd f g x ∈ Set.range (pullback.fst (𝓤.f a) (𝓤.f b) ≫ 𝓤.f a)
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  exact hx

/-- The section-wise isomorphisms on overlaps given by the compatibility of the `y a`. -/
def coverΦ (hy : ∀ a b, Scheme.Pic.map (pMapL f g 𝓤 a b) (y a).1 =
      Scheme.Pic.map (pMapR f g 𝓤 a b) (y b).1) (a b : 𝓤.I₀) :
    LocIso (coverM f σ hσ g 𝓤 y a) (coverM f σ hσ g 𝓤 y b)
      (coverV f g 𝓤 a ⊓ coverV f g 𝓤 b) :=
  let e₀ : (Modules.pullback (pMapL f g 𝓤 a b)).obj (Pic.rep (y a).1) ≅
      (Modules.pullback (pMapR f g 𝓤 a b)).obj (Pic.rep (y b).1) := by
    refine (Pic.mk_eq_mk_iff.mp ?_).some
    rw [← Pic.map_mk, ← Pic.map_mk, Pic.mk_rep, Pic.mk_rep, hy]
  let e : (coverM f σ hσ g 𝓤 y a).restrict (pMapL f g 𝓤 a b ≫ jMap f g 𝓤 a) ≅
      (coverM f σ hσ g 𝓤 y b).restrict (pMapL f g 𝓤 a b ≫ jMap f g 𝓤 a) :=
    pushforwardRestrictCompIso _ _ _ ≪≫
      (restrictFunctorIsoPullback _).app _ ≪≫ e₀ ≪≫ ((restrictFunctorIsoPullback _).app _).symm ≪≫
      (pushforwardRestrictCompIso _ _ _).symm ≪≫
      (restrictFunctorCongr (pMapL_jMap f g 𝓤 a b).symm).app _
  (LocIso.ofRestrictIso _ e).restrict (le_opensRange_pMapL_jMap f g 𝓤 a b)

end Cover

section Main

variable (hΓ : ∀ (T : Scheme.{u}) (g : T ⟶ S) (U : T.Opens),
  Function.Surjective ((pullback.snd f g).app U))

include hΓ

/-- **Gluing** in `Pic_{X/S,σ}`: compatible elements over an open cover glue. -/
theorem exists_glue_picSigma {T : Scheme.{u}} (g : T ⟶ S) (𝓤 : Scheme.OpenCover.{u} T)
    (y : ∀ a, picSigmaGrp f σ hσ (𝓤.f a ≫ g))
    (hy : ∀ a b, Scheme.Pic.map (pMapL f g 𝓤 a b) (y a).1 =
      Scheme.Pic.map (pMapR f g 𝓤 a b) (y b).1) :
    ∃ x : picSigmaGrp f σ hσ g, ∀ a, Scheme.Pic.map (jMap f g 𝓤 a) x.1 = (y a).1 := by
  let D := glueDataOfRigid (secT_snd f σ hσ g) (hΓ T g) (isSaturated_coverV f σ hσ g 𝓤)
    (isInvOn_coverM f σ hσ g 𝓤 y) (coverRig f σ hσ g 𝓤 y) (coverΦ f σ hσ g 𝓤 y hy)
  haveI : D.glued.IsInvertible :=
    D.isInvertible_glued (coverV_covers f g 𝓤) (isInvOn_coverM f σ hσ g 𝓤 y)
  refine ⟨⟨Scheme.Pic.mk D.glued, ?_⟩, fun a ↦ ?_⟩
  · rw [mem_picSigmaGrp]
    exact pic_map_eq_zero_of_nonempty _ _ (Rig.nonempty_iso _ _
      (D.rig (coverV_covers f g 𝓤) (isInvOn_coverM f σ hσ g 𝓤 y) (coverRig f σ hσ g 𝓤 y)
        (glueDataOfRigid_isRigid _ _ _ _ _ _)))
  · obtain ⟨e⟩ := LocIso.nonempty_restrictIso (jMap f g 𝓤 a)
      ((D.locIso a).restrict (opensRange_jMap f g 𝓤 a).le)
    rw [Scheme.Pic.map_mk, ← Scheme.Pic.mk_rep (y a).1]
    exact Scheme.Pic.mk_eq_of_iso (((restrictFunctorIsoPullback _).app _).symm ≪≫ e ≪≫
      (restrictFunctorAdjCounitIso _).app _)

/-- **Uniqueness** in `Pic_{X/S,σ}`: an element restricting to `0` on an open cover is `0`. -/
theorem eq_zero_of_forall_map_jMap {T : Scheme.{u}} (g : T ⟶ S) (𝓤 : Scheme.OpenCover.{u} T)
    (x : picSigmaGrp f σ hσ g) (hx : ∀ a, Scheme.Pic.map (jMap f g 𝓤 a) x.1 = 0) : x = 0 := by
  obtain ⟨ρ⟩ := nonempty_trivialisation _ _ x.2
  have Φ : ∀ a, LocIso (SheafOfModules.unit _) (Scheme.Pic.rep x.1) (coverV f g 𝓤 a) :=
    fun a ↦ (LocIso.ofRestrictIso (jMap f g 𝓤 a) (restrictUnitIso _ ≪≫
      (nonempty_trivialisation (jMap f g 𝓤 a) x.1 (hx a)).some.symm ≪≫
        ((restrictFunctorIsoPullback _).app _).symm)).restrict (opensRange_jMap f g 𝓤 a).ge
  obtain ⟨e⟩ := nonempty_iso_unit_of_rig (secT_snd f σ hσ g) (hΓ T g)
    (isSaturated_coverV f σ hσ g 𝓤) (coverV_covers f g 𝓤) _ (Rig.ofIso _ _ ρ) Φ
  refine Subtype.ext ?_
  rw [AddSubgroup.coe_zero, ← Scheme.Pic.mk_rep x.1, Scheme.Pic.mk_eq_zero_iff]
  exact ⟨e ≪≫ structureSheafIsoUnit _⟩

/-- **`Pic_{X/S,σ}` satisfies the sheaf condition for open covers** (Stacks, Section 44.6,
Tag 0B9R; proof of Lemma 44.4.3, Tag 0B9N), if `Γ(T, U) ⟶ Γ(X_T, f_T⁻¹ U)` is surjective for all
`T ⟶ S` and opens `U ⊆ T`. -/
theorem isSheafOver_picSigma : IsSheafOver.{u} (picSigma f σ hσ ⋙ forget AddCommGrpCat) := by
  intro T g 𝓤 y hy
  obtain ⟨x, hx⟩ := exists_glue_picSigma f σ hσ hΓ g 𝓤 (fun a ↦ y a)
    fun a b ↦ congrArg Subtype.val (hy a b)
  refine ⟨x, fun a ↦ Subtype.ext (hx a), fun z hz ↦ ?_⟩
  let z' : picSigmaGrp f σ hσ g := z
  have hz' : ∀ a, Scheme.Pic.map (jMap f g 𝓤 a) z'.1 = (y a).1 :=
    fun a ↦ congrArg Subtype.val (hz a)
  refine sub_eq_zero.1 (eq_zero_of_forall_map_jMap f σ hσ hΓ g 𝓤 (z' - x) fun a ↦ ?_)
  rw [AddSubgroup.coe_sub, map_sub, sub_eq_zero]
  exact (hz' a).trans (hx a).symm

end Main

end CurvesJacobian
