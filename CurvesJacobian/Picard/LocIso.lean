/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.RigidIso

/-!
# Section-wise isomorphisms and rigidifications of sheaves of modules on opens

This file is generic. It provides the section-wise language in which rigidified invertible
sheaves are glued (the Zariski sheaf property of `Pic_{X/S,σ}`, Stacks, Section 44.6,
Tag 0B9R, compare the proof of Lemma 44.4.3, Tag 0B9N).

Let `Y` be a scheme and `V` an open of `Y`.
* `LocIso M N V`: `𝒪`-linear bijections `Γ(M, W) ≃ Γ(N, W)` for all opens `W ≤ V`, compatible with
  restrictions (an isomorphism `M|_V ≅ N|_V`, written section-wise).
* `IsInvOn M V`: `M` has a local basis near every point of `V`.
* For `s : T ⟶ Y`, `Rig s M V`: an "evaluation along `s`", i.e. additive maps
  `χ : Γ(M, W) ⟶ Γ(T, s⁻¹W)` for `W ≤ V`, semilinear over `s^♯`, compatible with restriction,
  and sending local bases to units. For `V = ⊤` and `M` invertible, these are the same as
  trivialisations `s^*M ≅ 𝒪_T` (`Rig.ofIso`, `Rig.nonempty_iso`).
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian.ModulesGlue

open Scheme Scheme.Modules

variable {Y T : Scheme.{u}}

/-- `M` has a local basis near every point of `V`. -/
def IsInvOn (M : Y.Modules) (V : Y.Opens) : Prop :=
  ∀ y : Y, y ∈ V → ∃ (U : Y.Opens) (b : Γ(M, U)), U ≤ V ∧ y ∈ U ∧ M.IsBasisOn U b

/-- A section-wise isomorphism `M|_V ≅ N|_V`. -/
structure LocIso (M N : Y.Modules) (V : Y.Opens) where
  /-- the maps on sections -/
  φ : ∀ W : Y.Opens, W ≤ V → Γ(M, W) →+ Γ(N, W)
  φ_smul : ∀ (W : Y.Opens) (hW : W ≤ V) (c : Γ(Y, W)) (m : Γ(M, W)),
    φ W hW (c • m) = c • φ W hW m
  φ_rs : ∀ (W W' : Y.Opens) (hW : W ≤ V) (h : W' ≤ W) (m : Γ(M, W)),
    φ W' (h.trans hW) (rs M h m) = rs N h (φ W hW m)
  bij : ∀ (W : Y.Opens) (hW : W ≤ V), Function.Bijective (φ W hW)

/-- Evaluation along `s : T ⟶ Y` of sections of `M` over opens contained in `V`: a
section-wise form of a trivialisation of `s^* M` over `s⁻¹ V`. -/
structure Rig (s : T ⟶ Y) (M : Y.Modules) (V : Y.Opens) where
  /-- the evaluation maps -/
  χ : ∀ W : Y.Opens, W ≤ V → Γ(M, W) →+ Γ(T, s ⁻¹ᵁ W)
  χ_smul : ∀ (W : Y.Opens) (hW : W ≤ V) (c : Γ(Y, W)) (m : Γ(M, W)),
    χ W hW (c • m) = s.app W c * χ W hW m
  χ_rs : ∀ (W W' : Y.Opens) (hW : W ≤ V) (h : W' ≤ W) (m : Γ(M, W)),
    χ W' (h.trans hW) (rs M h m) = rr (s.preimage_mono h) (χ W hW m)
  isUnit_χ : ∀ (W : Y.Opens) (hW : W ≤ V) (e : Γ(M, W)), M.IsBasisOn W e →
    IsUnit (χ W hW e)

variable {s : T ⟶ Y}

/-- `Φ` is compatible with the evaluations `χM`, `χN` along `s`. -/
def LocIso.IsRigid {M N : Y.Modules} {V VM VN : Y.Opens} (Φ : LocIso M N V)
    (χM : Rig s M VM) (χN : Rig s N VN) (hM : V ≤ VM) (hN : V ≤ VN) : Prop :=
  ∀ (W : Y.Opens) (hW : W ≤ V) (m : Γ(M, W)),
    χN.χ W (hW.trans hN) (Φ.φ W hW m) = χM.χ W (hW.trans hM) m

section Basic

variable {M N P : Y.Modules} {V V' : Y.Opens}

/-- The identity. -/
def LocIso.refl (M : Y.Modules) (V : Y.Opens) : LocIso M M V where
  φ _ _ := AddMonoidHom.id _
  φ_smul _ _ _ _ := rfl
  φ_rs _ _ _ _ _ := rfl
  bij _ _ := Function.bijective_id

/-- Composition. -/
def LocIso.trans (Φ : LocIso M N V) (Ψ : LocIso N P V) : LocIso M P V where
  φ W hW := (Ψ.φ W hW).comp (Φ.φ W hW)
  φ_smul W hW c m := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Φ.φ_smul, Ψ.φ_smul]
  φ_rs W W' hW h m := by
    change Ψ.φ W' (h.trans hW) (Φ.φ W' (h.trans hW) (rs M h m)) = _
    rw [Φ.φ_rs, Ψ.φ_rs]
    rfl
  bij W hW := (Ψ.bij W hW).comp (Φ.bij W hW)

/-- The inverse. -/
def LocIso.symm (Φ : LocIso M N V) : LocIso N M V where
  φ W hW := (AddEquiv.ofBijective (Φ.φ W hW) (Φ.bij W hW)).symm.toAddMonoidHom
  φ_smul W hW c n := by
    apply (Φ.bij W hW).1
    have h1 := (AddEquiv.ofBijective (Φ.φ W hW) (Φ.bij W hW)).apply_symm_apply
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Φ.φ_smul]
    erw [h1, h1]
  φ_rs W W' hW h n := by
    apply (Φ.bij W' (h.trans hW)).1
    have h1 := (AddEquiv.ofBijective (Φ.φ W hW) (Φ.bij W hW)).apply_symm_apply
    have h2 := (AddEquiv.ofBijective (Φ.φ W' (h.trans hW)) (Φ.bij W' _)).apply_symm_apply
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [Φ.φ_rs W W' hW h]
    exact (h2 _).trans (congrArg _ (h1 n).symm)
  bij W hW := (AddEquiv.ofBijective (Φ.φ W hW) (Φ.bij W hW)).symm.bijective

/-- Restriction to a smaller open. -/
def LocIso.restrict (Φ : LocIso M N V) (h : V' ≤ V) : LocIso M N V' where
  φ W hW := Φ.φ W (hW.trans h)
  φ_smul W hW := Φ.φ_smul W (hW.trans h)
  φ_rs W W' hW h' := Φ.φ_rs W W' (hW.trans h) h'
  bij W hW := Φ.bij W (hW.trans h)

lemma LocIso.refl_φ (W : Y.Opens) (hW : W ≤ V) (m : Γ(M, W)) :
    (LocIso.refl M V).φ W hW m = m := rfl

lemma LocIso.trans_φ (Φ : LocIso M N V) (Ψ : LocIso N P V) (W : Y.Opens) (hW : W ≤ V)
    (m : Γ(M, W)) : (Φ.trans Ψ).φ W hW m = Ψ.φ W hW (Φ.φ W hW m) := rfl

lemma LocIso.symm_φ_φ (Φ : LocIso M N V) (W : Y.Opens) (hW : W ≤ V) (m : Γ(M, W)) :
    Φ.symm.φ W hW (Φ.φ W hW m) = m :=
  (AddEquiv.ofBijective (Φ.φ W hW) (Φ.bij W hW)).symm_apply_apply m

lemma LocIso.φ_symm_φ (Φ : LocIso M N V) (W : Y.Opens) (hW : W ≤ V) (n : Γ(N, W)) :
    Φ.φ W hW (Φ.symm.φ W hW n) = n :=
  (AddEquiv.ofBijective (Φ.φ W hW) (Φ.bij W hW)).apply_symm_apply n

lemma LocIso.restrict_φ (Φ : LocIso M N V) (h : V' ≤ V) (W : Y.Opens) (hW : W ≤ V')
    (m : Γ(M, W)) : (Φ.restrict h).φ W hW m = Φ.φ W (hW.trans h) m := rfl

lemma LocIso.isBasisOn_φ (Φ : LocIso M N V) {W : Y.Opens} (hW : W ≤ V) {e : Γ(M, W)}
    (he : M.IsBasisOn W e) : N.IsBasisOn W (Φ.φ W hW e) := by
  intro V' h
  have key : Function.Bijective
      (Φ.φ V' (h.trans hW) ∘ fun r : Γ(Y, V') ↦ r • rs M h e) :=
    (Φ.bij V' (h.trans hW)).comp (he h)
  have hfun : (Φ.φ V' (h.trans hW) ∘ fun r : Γ(Y, V') ↦ r • rs M h e) =
      fun r : Γ(Y, V') ↦ r • rs N h (Φ.φ W hW e) := by
    funext r
    exact (Φ.φ_smul V' (h.trans hW) r (rs M h e)).trans
      (congrArg (r • ·) (Φ.φ_rs W V' hW h e))
  rw [hfun] at key
  exact key

lemma LocIso.isInvOn (Φ : LocIso M N V) (hM : IsInvOn M V) : IsInvOn N V := by
  intro y hy
  obtain ⟨U, b, hUV, hyU, hb⟩ := hM y hy
  exact ⟨U, Φ.φ U hUV b, hUV, hyU, Φ.isBasisOn_φ hUV hb⟩

lemma isInvOn_of_isInvertible (M : Y.Modules) [M.IsInvertible] (V : Y.Opens) :
    IsInvOn M V := by
  intro y hy
  obtain ⟨U, b, hyU, hb⟩ := Scheme.Modules.IsInvertible.exists_basis (L := M) y
  exact ⟨U ⊓ V, rs M inf_le_left b, inf_le_right, ⟨hyU, hy⟩, isBasisOn_rs hb inf_le_left⟩

lemma IsInvOn.mono {M : Y.Modules} (hM : IsInvOn M V) (h : V' ≤ V) : IsInvOn M V' := by
  intro y hy
  obtain ⟨U, b, hUV, hyU, hb⟩ := hM y (h hy)
  exact ⟨U ⊓ V', rs M inf_le_left b, inf_le_right, ⟨hyU, hy⟩, isBasisOn_rs hb inf_le_left⟩

/-- A section of the structure sheaf which is a basis is a unit. -/
lemma isUnit_of_isBasisOn_unit {X : Scheme.{u}} {U : X.Opens}
    {b : Γ(SheafOfModules.unit X.ringCatSheaf, U)}
    (hb : Scheme.Modules.IsBasisOn (SheafOfModules.unit X.ringCatSheaf) U b) :
    IsUnit (show Γ(X, U) from b) := by
  obtain ⟨r, hr⟩ := exists_smul_eq_of_isBasisOn hb
    (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from (1 : Γ(X, U)))
  have hre : r * (show Γ(X, U) from b) = 1 := hr
  exact IsUnit.of_mul_eq_one_right r hre

/-- Scaling a basis by a unit gives a basis. -/
lemma isBasisOn_smul_of_isUnit {L : Y.Modules} {U : Y.Opens} {e : Γ(L, U)}
    (he : L.IsBasisOn U e) {c : Γ(Y, U)} (hc : IsUnit c) : L.IsBasisOn U (c • e) := by
  intro V h
  have hc' : IsUnit (rr h c) := hc.map (Y.presheaf.map (homOfLE h).op).hom
  have key : Function.Bijective
      ((fun r : Γ(Y, V) ↦ r • rs L h e) ∘ fun r ↦ r * rr h c) :=
    (bijective_smul_of_isBasisOn (isBasisOn_rs he h)).comp (Units.mulRight hc'.unit).bijective
  have hfun : ((fun r : Γ(Y, V) ↦ r • rs L h e) ∘ fun r ↦ r * rr h c) =
      fun r ↦ r • rs L h (c • e) := by
    funext r
    simp only [Function.comp_apply, rs_smul, smul_smul]
  rw [hfun] at key
  exact key

/-- The evaluation of `𝒪_Y` along `s`: `c ↦ s^♯ c`. -/
def Rig.unit (s : T ⟶ Y) (V : Y.Opens) : Rig s (SheafOfModules.unit Y.ringCatSheaf) V where
  χ W _ := (s.app W).hom.toAddMonoidHom
  χ_smul W _ c m := map_mul (s.app W).hom c m
  χ_rs _ _ _ h m := app_rr s h m
  isUnit_χ W _ _ he := (isUnit_of_isBasisOn_unit he).map (s.app W).hom

lemma Rig.unit_χ (V W : Y.Opens) (hW : W ≤ V) (c : Γ(Y, W)) :
    (Rig.unit s V).χ W hW c = s.app W c := rfl

/-- Restriction of an evaluation to a smaller open. -/
def Rig.restrict {M : Y.Modules} (χ : Rig s M V) (h : V' ≤ V) : Rig s M V' where
  χ W hW := χ.χ W (hW.trans h)
  χ_smul W hW := χ.χ_smul W (hW.trans h)
  χ_rs W W' hW h' := χ.χ_rs W W' (hW.trans h) h'
  isUnit_χ W hW := χ.isUnit_χ W (hW.trans h)

lemma Rig.restrict_χ {M : Y.Modules} (χ : Rig s M V) (h : V' ≤ V) (W : Y.Opens) (hW : W ≤ V')
    (m : Γ(M, W)) : (χ.restrict h).χ W hW m = χ.χ W (hW.trans h) m := rfl

lemma LocIso.isRigid_refl {M : Y.Modules} {VM : Y.Opens} (χ : Rig s M VM) (h : V ≤ VM) :
    (LocIso.refl M V).IsRigid χ χ h h := fun _ _ _ ↦ rfl

lemma LocIso.IsRigid.trans {VM VN VP : Y.Opens} {χM : Rig s M VM} {χN : Rig s N VN}
    {χP : Rig s P VP} {hM : V ≤ VM} {hN : V ≤ VN} {hP : V ≤ VP} {Φ : LocIso M N V}
    {Ψ : LocIso N P V} (hΦ : Φ.IsRigid χM χN hM hN) (hΨ : Ψ.IsRigid χN χP hN hP) :
    (Φ.trans Ψ).IsRigid χM χP hM hP := fun W hW m ↦
  (hΨ W hW (Φ.φ W hW m)).trans (hΦ W hW m)

lemma LocIso.IsRigid.restrict {VM VN : Y.Opens} {χM : Rig s M VM} {χN : Rig s N VN}
    {hM : V ≤ VM} {hN : V ≤ VN} {Φ : LocIso M N V} (hΦ : Φ.IsRigid χM χN hM hN)
    (h : V' ≤ V) : (Φ.restrict h).IsRigid χM χN (h.trans hM) (h.trans hN) :=
  fun W hW m ↦ hΦ W (hW.trans h) m

end Basic

section Trivialisation

/-- A trivialisation `s^* M ≅ 𝒪_T` gives an evaluation along `s` on all of `Y`. -/
def Rig.ofIso (s : T ⟶ Y) (M : Y.Modules)
    (ρ : (Modules.pullback s).obj M ≅ SheafOfModules.unit T.ringCatSheaf) : Rig s M ⊤ where
  χ W _ := AddMonoidHom.mk' (fun m ↦ (show Γ(T, s ⁻¹ᵁ W) from
      ρ.hom.app (s ⁻¹ᵁ W) (pullbackSection s m))) (fun m m' ↦ by
    change ρ.hom.app _ (pullbackSection s (m + m')) =
      ρ.hom.app _ (pullbackSection s m) + ρ.hom.app _ (pullbackSection s m')
    rw [pullbackSection_add, map_add])
  χ_smul W _ c m :=
    (congrArg (ρ.hom.app _) (pullbackSection_smul s c m)).trans (Hom.app_smul ρ.hom _ _)
  χ_rs W W' _ h m :=
    (congrArg (ρ.hom.app _) (pullbackSection_res s h m)).trans (app_rs ρ.hom _ _)
  isUnit_χ W _ _ he :=
    isUnit_of_isBasisOn_unit (IsBasisOn.of_iso ρ (isBasisOn_pullbackSection s W he))

lemma Rig.ofIso_χ (s : T ⟶ Y) (M : Y.Modules)
    (ρ : (Modules.pullback s).obj M ≅ SheafOfModules.unit T.ringCatSheaf) (W : Y.Opens)
    (hW : W ≤ ⊤) (m : Γ(M, W)) :
    (Rig.ofIso s M ρ).χ W hW m = ρ.hom.app (s ⁻¹ᵁ W) (pullbackSection s m) := rfl

/-- The morphism `M ⟶ s_* 𝒪_T` given by an evaluation along `s`. -/
def Rig.toPushforward {M : Y.Modules} (χ : Rig s M ⊤) :
    M ⟶ (pushforward s).obj (SheafOfModules.unit T.ringCatSheaf) :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (_root_.PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (χ.χ U.unop le_top)
        naturality U U' f := by
          ext m
          exact χ.χ_rs U.unop U'.unop le_top f.unop.le m }
      (fun U r m ↦ χ.χ_smul U.unop le_top r m))

lemma Rig.toPushforward_app {M : Y.Modules} (χ : Rig s M ⊤) (W : Y.Opens) (m : Γ(M, W)) :
    χ.toPushforward.app W m = χ.χ W le_top m :=
  rfl

/-- An evaluation along `s` on all of `Y` of an invertible sheaf gives a trivialisation of
`s^* M`. -/
theorem Rig.nonempty_iso (s : T ⟶ Y) (M : Y.Modules) [M.IsInvertible] (χ : Rig s M ⊤) :
    Nonempty ((Modules.pullback s).obj M ≅ SheafOfModules.unit T.ringCatSheaf) := by
  let adj := pullbackPushforwardAdjunction s
  let φ := (adj.homEquiv _ _).symm χ.toPushforward
  have key : ∀ (W : Y.Opens) (m : Γ(M, W)),
      φ.app (s ⁻¹ᵁ W) (pullbackSection s m) = χ.χ W le_top m := by
    intro W m
    have h : χ.toPushforward = adj.unit.app M ≫ (pushforward s).map φ :=
      ((adj.homEquiv _ _).apply_symm_apply _).symm.trans (adj.homEquiv_unit (f := φ))
    exact (congrArg (fun g ↦ g.app W m) h).symm
  have : IsIso φ := by
    refine isIso_of_isBasisOn φ fun t ↦ ?_
    obtain ⟨U, e, htU, he⟩ := Scheme.Modules.IsInvertible.exists_basis (L := M) (s.base t)
    refine ⟨s ⁻¹ᵁ U, pullbackSection s e, htU, isBasisOn_pullbackSection s U he, ?_⟩
    rw [key]
    have h1 : Scheme.Modules.IsBasisOn (SheafOfModules.unit T.ringCatSheaf) (s ⁻¹ᵁ U)
        (show Γ(SheafOfModules.unit T.ringCatSheaf, s ⁻¹ᵁ U) from (1 : Γ(T, s ⁻¹ᵁ U))) :=
      Scheme.PresheafOfModules.isBasisOn_unit (X := T) (s ⁻¹ᵁ U)
    have hb := isBasisOn_smul_of_isUnit h1 (χ.isUnit_χ U le_top e he)
    have h2 : (χ.χ U le_top e • (1 : Γ(T, s ⁻¹ᵁ U)) : Γ(T, s ⁻¹ᵁ U)) = χ.χ U le_top e :=
      mul_one _
    have h3 := congrArg (fun x : Γ(T, s ⁻¹ᵁ U) ↦ Scheme.Modules.IsBasisOn
      (SheafOfModules.unit T.ringCatSheaf) (s ⁻¹ᵁ U)
      (show Γ(SheafOfModules.unit T.ringCatSheaf, s ⁻¹ᵁ U) from x)) h2
    exact h3.mp hb
  exact ⟨asIso φ⟩

end Trivialisation

end CurvesJacobian.ModulesGlue
