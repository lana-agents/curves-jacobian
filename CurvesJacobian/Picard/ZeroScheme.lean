/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ContentIdeal
import CurvesJacobian.Picard.EndInvertible
import CurvesJacobian.Picard.QcohLocal
import CurvesJacobian.Picard.RelEffCartierPullback

/-!
# The zero scheme of a section of an invertible sheaf

Let `L` be an invertible sheaf on a scheme `X` and `s ∈ Γ(X, L)`. The zero scheme `Z(s)` of `s`
is the closed subscheme cut out by the ideal sheaf which on an affine open `U` where `L` has a
generator `e` and `s = f • e` is `(f)`. We define it as
`Scheme.Modules.zeroIdeal L s : X.IdealSheafData`, whose ideal on an arbitrary affine open `U`
is the content ideal `{μ (s|_U) | μ ∈ Hom(Γ(L, U), Γ(X, U))}` (`CurvesJacobian.contentIdeal`);
it is compatible with restriction to basic opens since `Γ(L, U)` is finitely presented and
`Γ(L, D(f)) = Γ(L, U)_f`.

* `Scheme.Modules.zeroIdeal_ideal_of_isBasisOn`: if `e` is a basis of `L` on `U` and
  `s|_U = t • e`, then `Z(s) ∩ U = V(t)`.
* `Scheme.Modules.zeroIdeal_iso`, `Scheme.Modules.zeroIdeal_smul`.
* `RelEffCartier.zeroIdeal_canonicalSection`: the zero scheme of the canonical section of
  `𝒪_X(D)` is `D` (used in Stacks, Lemma 44.6.4, Tag 0B9X).
* `Scheme.Modules.zeroIdealSheafIsoDual`: if `s` is a nonzerodivisor on every affine open, the
  ideal sheaf of `Z(s)` is `L^∨` (via `φ ↦ φ(s)`); hence a relative effective Cartier divisor
  with ideal `Z(s)` has class `[L]` (`RelEffCartier.picClass_eq_of_ideal_eq_zeroIdeal`).
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

open Scheme CurvesJacobian

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The content ideal of a section commutes with restriction to a basic open of an affine
open. -/
lemma map_contentIdeal_basicOpen (L : X.Modules) [L.IsInvertible] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (m : Γ(L, U)) :
    (contentIdeal m).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      contentIdeal (R := Γ(X, X.basicOpen f))
        (L.presheaf.map (homOfLE (X.basicOpen_le f)).op m) := by
  haveI := isQuasicoherent_of_isInvertible L
  haveI := hU.isLocalization_basicOpen f
  haveI := L.isLocalizedModule_resBasicOpen hU f
  haveI := (finitePresentation_and_flat_sections L hU).1
  exact (contentIdeal_isLocalizedModule (Submonoid.powers f) (L.resBasicOpen f) m).symm

/-- The zero scheme of a section of an invertible sheaf: on an affine open `U` its ideal is the
content ideal of `s|_U` in the `Γ(X, U)`-module `Γ(L, U)`. -/
def zeroIdeal (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤)) : X.IdealSheafData where
  ideal U := contentIdeal (R := Γ(X, U.1)) (L.presheaf.map (homOfLE le_top).op s)
  map_ideal_basicOpen U f := by
    rw [map_contentIdeal_basicOpen L U.2 f]
    exact congrArg _ (ModulesGlue.rs_rs L le_top (X.basicOpen_le f) s)

variable (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))

lemma zeroIdeal_ideal (U : X.affineOpens) :
    (zeroIdeal L s).ideal U =
      contentIdeal (R := Γ(X, U.1)) (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) :=
  rfl

/-- If `e` is a basis of `L` on the affine open `U` and `s|_U = t • e`, then the ideal of the
zero scheme of `s` on `U` is `(t)`. -/
lemma zeroIdeal_ideal_of_isBasisOn {U : X.affineOpens} {e : Γ(L, U.1)} (he : L.IsBasisOn U.1 e)
    {t : Γ(X, U.1)} (hs : L.presheaf.map (homOfLE le_top).op s = t • e) :
    (zeroIdeal L s).ideal U = Ideal.span {t} := by
  rw [zeroIdeal_ideal, hs]
  exact contentIdeal_smul_of_bijective (ModulesGlue.bijective_smul_of_isBasisOn he) t

/-- An isomorphism of sheaves of modules induces linear isomorphisms on sections. -/
def appLinearEquiv {L L' : X.Modules} (e : L ≅ L') (U : X.Opens) :
    Γ(L, U) ≃ₗ[Γ(X, U)] Γ(L', U) where
  toFun := e.hom.app U
  invFun := e.inv.app U
  map_add' := map_add _
  map_smul' := Hom.app_smul e.hom
  left_inv := iso_inv_app_hom_app e U
  right_inv := iso_hom_app_inv_app e U

lemma zeroIdeal_iso {L' : X.Modules} [L'.IsInvertible] (e : L ≅ L') :
    zeroIdeal L' (e.hom.app ⊤ s) = zeroIdeal L s := by
  refine IdealSheafData.ext (funext fun U ↦ ?_)
  rw [zeroIdeal_ideal, zeroIdeal_ideal]
  have h : L'.presheaf.map (homOfLE le_top).op (e.hom.app ⊤ s) =
      appLinearEquiv e U.1 (L.presheaf.map (homOfLE le_top).op s) :=
    (ModulesGlue.app_rs e.hom le_top s).symm
  rw [h, contentIdeal_map_equiv]

lemma zeroIdeal_smul (a : Γ(X, ⊤)) (U : X.affineOpens) :
    (zeroIdeal L (a • s)).ideal U =
      Ideal.span {X.presheaf.map (homOfLE le_top).op a} * (zeroIdeal L s).ideal U := by
  rw [zeroIdeal_ideal, zeroIdeal_ideal, ← contentIdeal_smul]
  exact congrArg _ (ModulesGlue.rs_smul L le_top a s)

end Scheme.Modules

namespace RelEffCartier

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : RelEffCartier f)

/-- On an affine open where `D` is cut out by a nonzerodivisor `g`, the ideal of the zero scheme
of the canonical section of `𝒪_X(D)` is `(g)`. -/
lemma zeroIdeal_canonicalSection_ideal {U : X.affineOpens} {g : Γ(X, U.1)}
    (hI : D.ideal.ideal U = Ideal.span {g}) (hg : IsSMulRegular Γ(X, U.1) g) :
    (Modules.zeroIdeal D.lineBundle D.canonicalSection).ideal U = Ideal.span {g} := by
  let P := Modules.toPre D.idealSheaf
  let a : D.ideal.idealSub.obj (op U.1) :=
    ⟨g, (D.ideal.mem_idealSub_iff_of_isAffine U g).mpr (hI ▸ Ideal.mem_span_singleton_self g)⟩
  let ε : Γ(D.idealSheaf, U.1) := (Modules.toSheafify D.ideal.idealPre).app (op U.1) a
  have hε : Scheme.PresheafOfModules.IsBasisOn P U.1 ε :=
    (IdealSheafData.isBasisOn_idealSheaf hI hg).toPre
  have he := Modules.isBasisOn_sheafify (Scheme.PresheafOfModules.dualPre P)
    (Scheme.PresheafOfModules.isBasisOn_dualBasis hε)
  refine Modules.zeroIdeal_ideal_of_isBasisOn D.lineBundle D.canonicalSection he ?_
  obtain ⟨φ, hcs, hφ⟩ : ∃ φ : Scheme.PresheafOfModules.DualSec P ⊤,
      D.canonicalSection =
        (Modules.toSheafify (Scheme.PresheafOfModules.dualPre P)).app (op ⊤) φ ∧
      ∀ V h b, φ.toFun V h b = D.idealSheafToStructureSheaf.app V b :=
    ⟨_, rfl, fun _ _ _ ↦ rfl⟩
  have hε1 : D.idealSheafToStructureSheaf.app U.1 ε = g :=
    IdealSheafData.idealSheafι_app D.ideal a
  have key : Scheme.PresheafOfModules.res (Scheme.PresheafOfModules.dualPre P)
      (le_top : U.1 ≤ ⊤) φ =
        (show X.ringCatSheaf.obj.obj (op U.1) from g) •
          (show (Scheme.PresheafOfModules.dualPre P).obj (op U.1) from
            Scheme.PresheafOfModules.dualBasis hε) := by
    refine Scheme.PresheafOfModules.DualSec.ext ?_
    funext V h b
    rw [Scheme.PresheafOfModules.dualPre_res_toFun, hφ]
    change _ = Scheme.PresheafOfModules.rres h g * Scheme.PresheafOfModules.coord hε h b
    conv_lhs => rw [← Scheme.PresheafOfModules.coord_smul hε h b]
    change D.idealSheafToStructureSheaf.app V
      ((Scheme.PresheafOfModules.coord hε h b : Γ(X, V)) •
        Scheme.PresheafOfModules.res ((Modules.toPresheafOfModules X).obj D.idealSheaf) h ε) = _
    refine (Modules.Hom.app_smul D.idealSheafToStructureSheaf
      (Scheme.PresheafOfModules.coord hε h b : Γ(X, V))
      (Scheme.PresheafOfModules.res ((Modules.toPresheafOfModules X).obj D.idealSheaf) h ε)).trans
        ?_
    rw [IdealSheafData.hom_app_res (M := D.idealSheaf) D.idealSheafToStructureSheaf h ε, hε1]
    exact mul_comm (Scheme.PresheafOfModules.coord hε h b : Γ(X, V))
      (X.presheaf.map (homOfLE h).op g)
  have h1 := Scheme.PresheafOfModules.app_res
    (Modules.toSheafify (Scheme.PresheafOfModules.dualPre P)) (le_top : U.1 ≤ ⊤)
    (show (Scheme.PresheafOfModules.dualPre P).obj (op ⊤) from φ)
  have h2 : (Modules.toSheafify (Scheme.PresheafOfModules.dualPre P)).app (op U.1)
      (Scheme.PresheafOfModules.res (Scheme.PresheafOfModules.dualPre P) (le_top : U.1 ≤ ⊤) φ) =
        g • (Modules.toSheafify (Scheme.PresheafOfModules.dualPre P)).app (op U.1)
          (Scheme.PresheafOfModules.dualBasis hε) := by
    rw [key]
    exact map_smul _ _ _
  rw [hcs]
  exact h1.symm.trans h2

/-- The zero scheme of the canonical section of `𝒪_X(D)` is `D`. -/
theorem zeroIdeal_canonicalSection :
    Modules.zeroIdeal D.lineBundle D.canonicalSection = D.ideal := by
  choose U g hxU hI hg using D.locally_principal
  refine IdealSheafData.ext_of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x ↦ ?_
  rw [hI x]
  exact D.zeroIdeal_canonicalSection_ideal (hI x) (hg x)

end RelEffCartier

namespace Scheme.Modules

variable {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))

open Scheme.PresheafOfModules in
/-- A dual section `φ` over `V`, as a linear form on `Γ(L, V)`. -/
def dualSecForm {U V : X.Opens} (φ : DualSec (toPre L) U) (h : V ≤ U) :
    Module.Dual Γ(X, V) Γ(L, V) where
  toFun := φ.toFun V h
  map_add' := φ.map_add' V h
  map_smul' := φ.map_smul' V h

open Scheme.PresheafOfModules in
lemma dualSec_apply_mem_zeroIdeal {U : X.Opens} (φ : DualSec (toPre L) U) (V : X.affineOpens)
    (h : V.1 ≤ U) :
    X.presheaf.map (homOfLE h).op (φ.toFun U le_rfl (L.presheaf.map (homOfLE le_top).op s)) ∈
      (zeroIdeal L s).ideal V := by
  have := φ.natural' U V.1 le_rfl h (L.presheaf.map (homOfLE le_top).op s)
  change _ = X.presheaf.map (homOfLE h).op _ at this
  rw [← this, zeroIdeal_ideal]
  refine ⟨dualSecForm L φ (h.trans le_rfl), ?_⟩
  change φ.toFun V.1 _ (L.presheaf.map (homOfLE le_top).op s) =
    φ.toFun V.1 _ (L.presheaf.map (homOfLE h).op (L.presheaf.map (homOfLE le_top).op s))
  exact congrArg _ (ModulesGlue.rs_rs L le_top h s).symm

open Scheme.PresheafOfModules in
/-- Evaluation at `s`, `L^∨ ⟶ I_{Z(s)}`, `φ ↦ φ(s)`, on presheaves. -/
def dualEval : dualPre (toPre L) ⟶ (zeroIdeal L s).idealPre where
  app U := ModuleCat.ofHom
    { toFun := fun φ ↦ ⟨(φ : DualSec (toPre L) U.unop).toFun U.unop le_rfl
          (L.presheaf.map (homOfLE le_top).op s),
        fun V h ↦ dualSec_apply_mem_zeroIdeal L s φ V h⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r φ ↦ Subtype.ext (by
        change rres le_rfl r * _ = r * _
        rw [rres_self]) }
  naturality {U U'} g := by
    ext φ
    refine Subtype.ext ?_
    change (φ : DualSec (toPre L) U.unop).toFun U'.unop (le_rfl.trans g.unop.le)
        (L.presheaf.map (homOfLE le_top).op s) =
      X.presheaf.map g (φ.toFun U.unop le_rfl (L.presheaf.map (homOfLE le_top).op s))
    have hn := φ.natural' U.unop U'.unop le_rfl g.unop.le (L.presheaf.map (homOfLE le_top).op s)
    refine Eq.trans ?_ hn
    exact congrArg _ (ModulesGlue.rs_rs L le_top g.unop.le s).symm

lemma dualEval_app_coe {U : X.Opens}
    (φ : (Scheme.PresheafOfModules.dualPre (toPre L)).obj (op U)) :
    (show (zeroIdeal L s).idealSub.obj (op U) from (dualEval L s).app (op U) φ).1 =
      (φ : Scheme.PresheafOfModules.DualSec (toPre L) U).toFun U le_rfl
        (L.presheaf.map (homOfLE le_top).op s) :=
  rfl

/-- If `s` is a nonzerodivisor on every affine open, the evaluation `L^∨ ⟶ I_{Z(s)}` at `s`
is an isomorphism after sheafification. -/
lemma isIso_sheafify_dualEval
    (hs : ∀ U : X.affineOpens, Function.Injective fun r : Γ(X, U.1) ↦
      r • L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) :
    IsIso ((sheafify X).map (dualEval L s)) := by
  apply isIso_of_isBasisOn
  intro x
  obtain ⟨W, e, hxW, he⟩ := IsInvertible.exists_basis (L := L) x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  let U' : X.affineOpens := ⟨U, hU⟩
  have he' : L.IsBasisOn U (ModulesGlue.rs L hUW e) := ModulesGlue.isBasisOn_rs he hUW
  set e' := ModulesGlue.rs L hUW e
  obtain ⟨t, ht⟩ := ModulesGlue.exists_smul_eq_of_isBasisOn he'
    (L.presheaf.map (homOfLE le_top).op s)
  have hI : (zeroIdeal L s).ideal U' = Ideal.span {t} :=
    zeroIdeal_ideal_of_isBasisOn L s (U := U') he' ht.symm
  have htreg : IsSMulRegular Γ(X, U) t := by
    intro r₁ r₂ h
    apply hs U'
    change r₁ • L.presheaf.map (homOfLE le_top).op s = r₂ • L.presheaf.map (homOfLE le_top).op s
    rw [← ht, smul_smul, smul_smul, mul_comm r₁, mul_comm r₂]
    exact congrArg (· • e') h
  have hb := isBasisOn_sheafify _ (Scheme.PresheafOfModules.isBasisOn_dualBasis he'.toPre)
  refine ⟨U, _, hxU, hb, ?_⟩
  have hev : (dualEval L s).app (op U) (Scheme.PresheafOfModules.dualBasis he'.toPre) =
      ⟨t, ((zeroIdeal L s).mem_idealSub_iff_of_isAffine U' t).mpr
        (hI ▸ Ideal.mem_span_singleton_self t)⟩ := by
    refine Subtype.ext ?_
    rw [dualEval_app_coe]
    exact Scheme.PresheafOfModules.coord_eq he'.toPre le_rfl _ _ (by
      rw [Scheme.PresheafOfModules.res_self]
      exact ht)
  have hnat := congr_arg (fun η ↦ η.app (op U) (Scheme.PresheafOfModules.dualBasis he'.toPre))
    ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (dualEval L s))
  have hB := IdealSheafData.isBasisOn_idealSheaf (I := zeroIdeal L s) hI htreg
  have h3 : ((sheafify X).map (dualEval L s)).app U
      ((toSheafify (Scheme.PresheafOfModules.dualPre (toPre L))).app (op U)
        (Scheme.PresheafOfModules.dualBasis he'.toPre)) =
      (toSheafify (zeroIdeal L s).idealPre).app (op U)
        ⟨t, ((zeroIdeal L s).mem_idealSub_iff_of_isAffine U' t).mpr
          (hI ▸ Ideal.mem_span_singleton_self t)⟩ := by
    refine hnat.symm.trans ?_
    change (toSheafify _).app (op U) ((dualEval L s).app (op U) _) = _
    rw [hev]
  rw [h3]
  exact hB

/-- If `s` is a nonzerodivisor on every affine open, the ideal sheaf of the zero scheme of `s`
is isomorphic to `L^∨`. -/
def zeroIdealSheafIsoDual
    (hs : ∀ U : X.affineOpens, Function.Injective fun r : Γ(X, U.1) ↦
      r • L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) :
    (zeroIdeal L s).idealSheaf ≅ dual L :=
  haveI := isIso_sheafify_dualEval L s hs
  (asIso ((sheafify X).map (dualEval L s))).symm

end Scheme.Modules

/-- A relative effective Cartier divisor which is the zero scheme of a section `s` of an
invertible sheaf `L` (with `s` a nonzerodivisor on affine opens) has class `[L]`. -/
theorem RelEffCartier.picClass_eq_of_ideal_eq_zeroIdeal {X S : Scheme.{u}} {f : X ⟶ S}
    (D : RelEffCartier f) (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (hs : ∀ U : X.affineOpens, Function.Injective fun r : Γ(X, U.1) ↦
      r • L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s)
    (hD : D.ideal = Modules.zeroIdeal L s) : D.picClass = Pic.mk L := by
  have h : D.idealSheaf = (Modules.zeroIdeal L s).idealSheaf := by
    rw [RelEffCartier.idealSheaf, hD]
  rw [RelEffCartier.picClass_eq_neg,
    Pic.mk_eq_of_iso (eqToIso h ≪≫ Modules.zeroIdealSheafIsoDual L s hs), Pic.mk_dual, neg_neg]

end AlgebraicGeometry

end
