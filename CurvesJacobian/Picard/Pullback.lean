/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicGroup
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pullback of line bundles

For a morphism of schemes `f : X ⟶ Y` we show that `f^*` preserves invertible sheaves and is
compatible with tensor products of invertible sheaves, which gives the functoriality
`Pic.map f : Y.Pic →+ X.Pic`.

The main technical statement is `Modules.isBasisOn_pullbackSection`: if `s ∈ Γ(L, U)` is a basis
of `L` on `U`, then its image `f^* s ∈ Γ(f^*L, f⁻¹U)` under the unit of the adjunction
`f^* ⊣ f_*` is a basis of `f^*L` on `f⁻¹U`.
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

instance (f : X ⟶ Y) : (Opens.map f.base).Final where
  out d := isConnected_of_isTerminal _
    (IsTerminal.ofUniqueHom (fun _ ↦ StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _))
      (fun _ _ ↦ StructuredArrow.ext _ _ (Subsingleton.elim _ _)) :
      IsTerminal (StructuredArrow.mk (Y := ⊤)
        (homOfLE (fun _ _ ↦ Set.mem_univ _ : d ≤ (Opens.map f.base).obj ⊤))))

namespace Modules

open _root_.PresheafOfModules

/-- A morphism of sheaves of modules which is bijective on all opens contained in the members
of an open cover is an isomorphism. -/
lemma isIso_of_forall_bijective {A B : X.Modules} (φ : A ⟶ B)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U, Function.Bijective (φ.app V)) : IsIso φ := by
  have h1 := Scheme.PresheafOfModules.isLocallyInjective_of_locally_bijective
    ((toPresheafOfModules X).map φ) H
  have h2 := Scheme.PresheafOfModules.isLocallySurjective_of_locally_bijective
    ((toPresheafOfModules X).map φ) H
  let φ' : (⟨A.presheaf, A.isSheaf⟩ : Sheaf (Opens.grothendieckTopology X) Ab.{u}) ⟶
      ⟨B.presheaf, B.isSheaf⟩ := Sheaf.homEquiv.symm φ.mapPresheaf
  have : IsIso φ' := (Sheaf.isLocallyBijective_iff_isIso φ').mp ⟨h1, h2⟩
  have : IsIso φ'.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map φ'))
  rw [Hom.isIso_iff_isIso_app]
  intro U
  exact inferInstanceAs (IsIso (φ'.hom.app (op U)))

/-- A morphism of sheaves of modules mapping, near every point, a basis to a basis is an
isomorphism. -/
lemma isIso_of_isBasisOn {A B : X.Modules} (φ : A ⟶ B)
    (H : ∀ x : X, ∃ (U : X.Opens) (a : Γ(A, U)), x ∈ U ∧ A.IsBasisOn U a ∧
      B.IsBasisOn U (φ.app U a)) : IsIso φ := by
  apply isIso_of_forall_bijective
  intro x
  obtain ⟨U, a, hxU, ha, hb⟩ := H x
  refine ⟨U, hxU, fun V hV ↦ ?_⟩
  have : (((toPresheafOfModules X).map φ).app (op V) : _ → _) ∘
      (fun r : X.ringCatSheaf.obj.obj (op V) ↦
        r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj A) hV a) =
      (fun r : X.ringCatSheaf.obj.obj (op V) ↦
        r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj B) hV (φ.app U a)) := by
    funext r
    exact (_root_.map_smul (((toPresheafOfModules X).map φ).app (op V)).hom r _).trans
      (congrArg (r • ·) (Scheme.PresheafOfModules.app_res ((toPresheafOfModules X).map φ) hV a))
  have hb' := hb hV
  rw [← this] at hb'
  exact (Function.Bijective.of_comp_iff _ (ha hV)).mp hb'


lemma IsBasisOn.of_iso {A B : X.Modules} (e : A ≅ B) {U : X.Opens} {a : Γ(A, U)}
    (h : A.IsBasisOn U a) : B.IsBasisOn U (e.hom.app U a) :=
  Scheme.PresheafOfModules.IsBasisOn.of_iso ((toPresheafOfModules X).mapIso e) h

lemma IsBasisOn.of_iso' {A B : X.Modules} (e : A ≅ B) {U : X.Opens} {a : Γ(A, U)}
    (h : A.IsBasisOn U a) {b : Γ(B, U)} (hb : e.hom.app U a = b) : B.IsBasisOn U b :=
  hb ▸ h.of_iso e

lemma iso_inv_app_hom_app {A B : X.Modules} (e : A ≅ B) (U : X.Opens) (a : Γ(A, U)) :
    e.inv.app U (e.hom.app U a) = a := by
  calc e.inv.app U (e.hom.app U a) = (e.hom ≫ e.inv).app U a := rfl
    _ = (𝟙 A : A ⟶ A).app U a := by rw [e.hom_inv_id]
    _ = a := rfl

lemma iso_hom_app_inv_app {A B : X.Modules} (e : A ≅ B) (U : X.Opens) (b : Γ(B, U)) :
    e.hom.app U (e.inv.app U b) = b :=
  iso_inv_app_hom_app e.symm U b

/-- The structure sheaf as an object of `X.Modules`. -/
abbrev structureSheaf (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The morphism `𝒪_X ⟶ L` given by a global section. -/
def homOfSection {L : X.Modules} (s : Γ(L, ⊤)) : structureSheaf X ⟶ L :=
  (SheafOfModules.unitHomEquiv L).symm
    ⟨fun V ↦ L.presheaf.map (homOfLE le_top).op s, fun {V V'} g ↦ by
      change (L.presheaf.map _ ≫ L.presheaf.map _) s = _
      rw [← CategoryTheory.Functor.map_comp]
      rfl⟩

lemma homOfSection_app {L : X.Modules} (s : Γ(L, ⊤)) (V : X.Opens)
    (r : X.ringCatSheaf.obj.obj (op V)) :
    (homOfSection s).app V r = r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj L)
      (le_top : V ≤ ⊤) s := rfl

lemma isIso_homOfSection {L : X.Modules} {s : Γ(L, ⊤)} (hs : L.IsBasisOn ⊤ s) :
    IsIso (homOfSection s) :=
  isIso_of_forall_bijective _ (fun _ ↦ ⟨⊤, trivial, fun _ hV ↦ hs hV⟩)

variable (f : X ⟶ Y)

/-- The image `f^* m ∈ Γ(f^* M, f⁻¹ U)` of a section `m ∈ Γ(M, U)` under the unit of the
adjunction `f^* ⊣ f_*`. -/
def pullbackSection {M : Y.Modules} {U : Y.Opens} (m : Γ(M, U)) :
    Γ((pullback f).obj M, f ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction f).unit.app M).app U m

lemma pullbackSection_naturality {M N : Y.Modules} (φ : M ⟶ N) {U : Y.Opens} (m : Γ(M, U)) :
    ((pullback f).map φ).app (f ⁻¹ᵁ U) (pullbackSection f m) = pullbackSection f (φ.app U m) := by
  have := congr_arg (fun ψ : M ⟶ (pushforward f).obj ((pullback f).obj N) ↦ ψ.app U m)
    ((pullbackPushforwardAdjunction f).unit.naturality φ)
  exact this.symm

/-- The canonical isomorphism `f^* 𝒪_Y ≅ 𝒪_X`. -/
def pullbackStructureSheafHom : (pullback f).obj (structureSheaf Y) ⟶ structureSheaf X :=
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

instance : IsIso (pullbackStructureSheafHom f) :=
  inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom))

lemma pullbackObjUnitToUnit_pullbackSection_one :
    (pullbackStructureSheafHom f).app (f ⁻¹ᵁ ⊤)
      (pullbackSection f (M := structureSheaf Y) (U := ⊤) (1 : Y.ringCatSheaf.obj.obj (op ⊤))) =
        (1 : X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ ⊤))) := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  have := congr_arg (fun ψ : structureSheaf Y ⟶ (pushforward f).obj (structureSheaf X) ↦
    ψ.app ⊤ (1 : Y.ringCatSheaf.obj.obj (op ⊤))) h
  refine this.trans ?_
  exact map_one (f.c.app (op ⊤)).hom

/-- The pullback of a global basis is a basis. -/
lemma isBasisOn_pullbackSection_top {L : Y.Modules} {s : Γ(L, ⊤)} (hs : L.IsBasisOn ⊤ s) :
    ((pullback f).obj L).IsBasisOn (f ⁻¹ᵁ ⊤) (pullbackSection f s) := by
  let ρ := pullbackStructureSheafHom f
  have h1 : (structureSheaf X).IsBasisOn (f ⁻¹ᵁ ⊤) (1 : X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ ⊤))) :=
    Scheme.PresheafOfModules.isBasisOn_unit _
  have h2 := IsBasisOn.of_iso' (asIso ρ).symm h1 (b := pullbackSection f (M := structureSheaf Y)
    (U := ⊤) (1 : Y.ringCatSheaf.obj.obj (op ⊤))) (by
      rw [← pullbackObjUnitToUnit_pullbackSection_one f]
      exact iso_inv_app_hom_app (asIso ρ) _ _)
  have := isIso_homOfSection hs
  refine IsBasisOn.of_iso' (asIso ((pullback f).map (homOfSection s))) h2 ?_
  rw [asIso_hom, pullbackSection_naturality, homOfSection_app]
  congr 1
  change (1 : Y.ringCatSheaf.obj.obj (op ⊤)) • Scheme.PresheafOfModules.res
    ((toPresheafOfModules Y).obj L) (le_top : (⊤ : Y.Opens) ≤ ⊤) s = s
  rw [one_smul]
  exact Scheme.PresheafOfModules.res_self _ _


section Restrict

lemma _root_.AlgebraicGeometry.Scheme.PresheafOfModules.bijective_res_congr
    {P : X.PresheafOfModules} {U A B : X.Opens} (hAB : A = B) (hA : A ≤ U) (hB : B ≤ U)
    (t : P.obj (op U)) :
    Function.Bijective (fun r : X.ringCatSheaf.obj.obj (op A) ↦
        r • Scheme.PresheafOfModules.res P hA t) ↔
      Function.Bijective (fun r : X.ringCatSheaf.obj.obj (op B) ↦
        r • Scheme.PresheafOfModules.res P hB t) := by
  subst hAB
  rfl

variable {W : X.Opens} {N : X.Modules}

/-- A basis of `N` on `W.ι ''ᵁ V` is a basis of the restriction `N|_W` on `V`. -/
lemma IsBasisOn.restrict_of {V : W.toScheme.Opens} {t : Γ(N, W.ι ''ᵁ V)}
    (h : N.IsBasisOn (W.ι ''ᵁ V) t) : (N.restrict W.ι).IsBasisOn V t := by
  intro V' hV'
  have hV'' : W.ι ''ᵁ V' ≤ W.ι ''ᵁ V := Hom.image_mono _ hV'
  have : (fun r : W.toScheme.ringCatSheaf.obj.obj (op V') ↦
      r • Scheme.PresheafOfModules.res ((toPresheafOfModules _).obj (N.restrict W.ι)) hV' t) =
      (fun r ↦ r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj N) hV'' t) ∘
        (W.ι.appIso V').inv := rfl
  rw [this]
  exact (h hV'').comp (ConcreteCategory.bijective_of_isIso (W.ι.appIso V').inv)

/-- A basis of the restriction `N|_W` on `V` is a basis of `N` on `W.ι ''ᵁ V`. -/
lemma IsBasisOn.of_restrict {V : W.toScheme.Opens} {t : Γ(N, W.ι ''ᵁ V)}
    (h : (N.restrict W.ι).IsBasisOn V t) : N.IsBasisOn (W.ι ''ᵁ V) t := by
  intro V'' hV''
  have hV' : W.ι ⁻¹ᵁ V'' ≤ V := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hV'' hx
    rw [← W.ι.isOpenEmbedding.injective hyx]
    exact hy
  have heq : W.ι ''ᵁ W.ι ⁻¹ᵁ V'' = V'' := by
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι]
    exact inf_eq_right.mpr (hV''.trans (Hom.image_le_opensRange _ _ |>.trans
      (by rw [Opens.opensRange_ι])))
  have hb := h hV'
  have : (fun r : W.toScheme.ringCatSheaf.obj.obj (op (W.ι ⁻¹ᵁ V'')) ↦
      r • Scheme.PresheafOfModules.res ((toPresheafOfModules _).obj (N.restrict W.ι)) hV' t) =
      (fun r ↦ r • Scheme.PresheafOfModules.res ((toPresheafOfModules X).obj N)
        (heq.le.trans hV'') t) ∘ (W.ι.appIso _).inv := rfl
  rw [this] at hb
  have hb' := (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (W.ι.appIso (W.ι ⁻¹ᵁ V'')).inv)).mp hb
  exact (Scheme.PresheafOfModules.bijective_res_congr heq _ _ t).mp hb'

end Restrict

lemma isBasisOn_pullbackSection_of_eq_top {L : Y.Modules} {A : Y.Opens} (hA : A = ⊤)
    {s : Γ(L, A)} (hs : L.IsBasisOn A s) :
    ((pullback f).obj L).IsBasisOn (f ⁻¹ᵁ A) (pullbackSection f s) := by
  subst hA
  exact isBasisOn_pullbackSection_top f hs

lemma isBasisOn_of_eq {N : X.Modules} {A B : X.Opens} (hAB : A = B) {x : Γ(N, B)}
    (h : N.IsBasisOn A (N.presheaf.map (homOfLE hAB.le).op x)) : N.IsBasisOn B x := by
  subst hAB
  have := Scheme.PresheafOfModules.res_self ((toPresheafOfModules X).obj N) x
  exact this ▸ h


section BaseChange

variable (f : X ⟶ Y) (U : Y.Opens)

/-- `j_* ∘ (f|_U)_* ≅ f_* ∘ j'_*` for the open immersions `j : U → Y`, `j' : f⁻¹U → X`. -/
def pushforwardRestrictIso :
    pushforward (f ∣_ U) ⋙ pushforward U.ι ≅ pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f :=
  pushforwardComp (f ∣_ U) U.ι ≪≫ pushforwardCongr (morphismRestrict_ι f U) ≪≫
    (pushforwardComp (f ⁻¹ᵁ U).ι f).symm

/-- Pullback commutes with restriction to open subschemes. -/
def pullbackRestrictIso :
    pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι ≅ restrictFunctor U.ι ⋙ pullback (f ∣_ U) :=
  ((pullbackPushforwardAdjunction f).comp (restrictAdjunction (f ⁻¹ᵁ U).ι)).leftAdjointUniq
    (((restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (f ∣_ U))).ofNatIsoRight
      (pushforwardRestrictIso f U))

lemma preimage_ι_preimage_eq :
    (f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ U = (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U := by
  rw [← Hom.comp_preimage, ← Hom.comp_preimage, morphismRestrict_ι]

/-- The isomorphism `(f^* M)|_{f⁻¹U} ≅ (f|_U)^*(M|_U)` maps the restriction of `f^* s` to
`(f|_U)^*(s|_U)`. -/
lemma pullbackRestrictIso_hom_app_app (M : Y.Modules) (s : Γ(M, U)) :
    ((pullbackRestrictIso f U).hom.app M).app ((f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ U)
      (((pullback f).obj M).presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ U))).op (pullbackSection f s)) =
    ((pullback (f ∣_ U)).obj (M.restrict U.ι)).presheaf.map
      (homOfLE (preimage_ι_preimage_eq f U).le).op
      (pullbackSection (f ∣_ U) (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s)) := by
  have := congr_arg (fun φ ↦ φ.app U s) (Adjunction.unit_leftAdjointUniq_hom_app
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction (f ⁻¹ᵁ U).ι))
    (((restrictAdjunction U.ι).comp (pullbackPushforwardAdjunction (f ∣_ U))).ofNatIsoRight
      (pushforwardRestrictIso f U)) M)
  exact this

/-- The pullback of a basis of `L` on `U` is a basis of `f^*L` on `f⁻¹U`. -/
theorem isBasisOn_pullbackSection {L : Y.Modules} {s : Γ(L, U)} (hs : L.IsBasisOn U s) :
    ((pullback f).obj L).IsBasisOn (f ⁻¹ᵁ U) (pullbackSection f s) := by
  have h1 : (L.restrict U.ι).IsBasisOn (U.ι ⁻¹ᵁ U)
      (L.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s) :=
    IsBasisOn.restrict_of (Scheme.PresheafOfModules.IsBasisOn.restrict hs _)
  have h2 := isBasisOn_pullbackSection_of_eq_top (f ∣_ U) (Opens.ι_preimage_self U) h1
  have h3 := Scheme.PresheafOfModules.IsBasisOn.restrict h2 (preimage_ι_preimage_eq f U).le
  have h4 := IsBasisOn.of_iso' ((pullbackRestrictIso f U).app L).symm h3
    (b := ((pullback f).obj L).presheaf.map
      (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ U))).op (pullbackSection f s))
      ((congrArg (((pullbackRestrictIso f U).app L).inv.app _)
        (pullbackRestrictIso_hom_app_app f U L s)).symm.trans
          (iso_inv_app_hom_app ((pullbackRestrictIso f U).app L) _ _))
  have h5 := IsBasisOn.of_restrict h4
  have heq : (f ⁻¹ᵁ U).ι ''ᵁ (f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ U = f ⁻¹ᵁ U := by
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_idem]
  exact isBasisOn_of_eq heq h5

end BaseChange

/-- The pullback of an invertible sheaf is invertible. -/
instance isInvertible_pullback (f : X ⟶ Y) (L : Y.Modules) [L.IsInvertible] :
    ((pullback f).obj L).IsInvertible where
  exists_basis x := by
    obtain ⟨U, s, hxU, hs⟩ := IsInvertible.exists_basis (L := L) (f.base x)
    exact ⟨f ⁻¹ᵁ U, _, hxU, isBasisOn_pullbackSection f U hs⟩


end Modules

end AlgebraicGeometry.Scheme

end
