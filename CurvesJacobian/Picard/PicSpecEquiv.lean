/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicSpec
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# `Pic (Spec A) ≃ Pic A`

* `Scheme.Modules.isQuasicoherent_of_isInvertible`: an invertible sheaf is quasi-coherent
  (it is locally isomorphic to `𝒪`).
* `picSpecEquiv : (Spec A).Pic ≃+ Additive (CommRing.Pic A)`: `[M] ↦ [M^~]` is an isomorphism;
  surjectivity uses `L ≅ (Γ L)^~` for the quasi-coherent sheaf `L` and `(M ⊗ N)^~ ≅ M^~ ⊗ N^~`.
* `Pic` of the spectrum of a local ring (e.g. a field) is trivial.
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry

open Scheme Scheme.Modules CurvesJacobian

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- A section `s ∈ Γ(L, U)` as a global section of `L.over U`. -/
def overSection (L : X.Modules) {U : X.Opens} (s : Γ(L, U)) : (L.over U).sections :=
  ⟨fun V ↦ L.val.map V.unop.hom.op s, fun {V _} g ↦
    Scheme.PresheafOfModules.res_res ((toPresheafOfModules X).obj L) V.unop.hom.le
      g.unop.left.le s⟩

lemma isIso_unitHomEquiv_symm_overSection {L : X.Modules} {U : X.Opens} {s : Γ(L, U)}
    (hs : L.IsBasisOn U s) : IsIso ((L.over U).unitHomEquiv.symm (overSection L s)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hs V.unop.hom.le

lemma isIso_freeHomEquiv_symm_overSection {L : X.Modules} {U : X.Opens} {s : Γ(L, U)}
    (hs : L.IsBasisOn U s) :
    IsIso ((L.over U).freeHomEquiv.symm (fun _ : PUnit ↦ overSection L s)) := by
  have h1 : SheafOfModules.ιFree PUnit.unit ≫
      (L.over U).freeHomEquiv.symm (fun _ : PUnit ↦ overSection L s) =
        (L.over U).unitHomEquiv.symm (overSection L s) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  haveI : IsIso (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) PUnit.unit) := by
    change IsIso (Sigma.ι (fun _ : PUnit ↦ SheafOfModules.unit _) default)
    rw [← coproductUniqueIso_inv]
    infer_instance
  haveI := isIso_unitHomEquiv_symm_overSection hs
  rw [← h1] at this
  exact IsIso.of_isIso_comp_left (SheafOfModules.ιFree PUnit.unit) _

set_option maxHeartbeats 1600000 in -- elaborating the local generators data is slow

/-- An invertible sheaf is locally free. -/
lemma isLocallyFree_of_isInvertible (L : X.Modules) [L.IsInvertible] :
    SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) L := by
  choose U s hU hs using fun x : X ↦ IsInvertible.exists_basis (L := L) x
  have hcov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact top_le_iff.mp (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)
  let q : SheafOfModules.LocalGeneratorsData (R := X.ringCatSheaf) L :=
    { I := X
      X := U
      coversTop := hcov
      generators x :=
        { I := PUnit
          s := fun _ ↦ overSection L (s x)
          epi := by haveI := isIso_freeHomEquiv_symm_overSection (hs x); infer_instance } }
  haveI : q.IsLocallyFreeData := by
    constructor
    intro x
    exact isIso_freeHomEquiv_symm_overSection (hs x)
  exact q.isLocallyFree

/-- An invertible sheaf is quasi-coherent. -/
instance isQuasicoherent_of_isInvertible (L : X.Modules) [L.IsInvertible] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) L :=
  haveI := isLocallyFree_of_isInvertible L
  inferInstance

end Scheme.Modules


namespace Scheme.Modules

/-- The structure sheaf is the unit for the tensor product. -/
def structureSheafIsoUnit (X : Scheme.{u}) : structureSheaf X ≅ 𝟙_ X.Modules :=
  haveI := isIso_homOfSection (L := 𝟙_ X.Modules)
    (s := (toSheafify (𝟙_ X.PresheafOfModules)).app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤)))
    (isBasisOn_sheafify (𝟙_ X.PresheafOfModules) (Scheme.PresheafOfModules.isBasisOn_unit ⊤))
  asIso (homOfSection (L := 𝟙_ X.Modules)
    ((toSheafify (𝟙_ X.PresheafOfModules)).app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤))))

end Scheme.Modules

variable {A : CommRingCat.{u}}

/-- `[M] ↦ [M^~]`. -/
def picTilde : Additive (CommRing.Pic A) →+ (Spec A).Pic :=
  AddMonoidHom.mk'
    (fun x ↦ Pic.mk (tilde (ModuleCat.of A ((Additive.toMul x : CommRing.Pic A) : Type u))))
    (fun x y ↦ by
      rw [← Pic.mk_tensor, Pic.mk_eq_mk_iff, toMul_add, CommRing.Pic.mul_eq_tensor]
      set P : CommRing.Pic A := Additive.toMul x
      set Q : CommRing.Pic A := Additive.toMul y
      exact ⟨(tilde.functor A).mapIso (CommRing.Pic.mk.linearEquiv A (P ⊗[A] Q)).toModuleIso ≪≫
        tildeTensorIso (ModuleCat.of A P) (ModuleCat.of A Q)⟩)

lemma picTilde_injective : Function.Injective (picTilde (A := A)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  change Pic.mk (tilde (ModuleCat.of A ((Additive.toMul x : CommRing.Pic A) : Type u))) = 0 at hx
  rw [Pic.mk_eq_zero_iff] at hx
  obtain ⟨e⟩ := hx
  let e' : tilde (ModuleCat.of A ((Additive.toMul x : CommRing.Pic A) : Type u)) ≅
      tilde (ModuleCat.of A A) :=
    e ≪≫ (structureSheafIsoUnit _).symm ≪≫ (tildeSelf (R := A)).symm
  have e'' := (tilde.fullyFaithfulFunctor (R := A)).preimageIso e'
  apply Additive.toMul.injective
  rw [toMul_zero, ← CommRing.Pic.mk_eq_self (M := Additive.toMul x), CommRing.Pic.mk_eq_one_iff]
  exact ⟨e''.toLinearEquiv⟩

lemma picTilde_surjective : Function.Surjective (picTilde (A := A)) := by
  intro x
  induction x using Pic.ind with | h L =>
  let M := (moduleSpecΓFunctor (R := A)).obj L
  let N := (moduleSpecΓFunctor (R := A)).obj (dual L)
  haveI : SheafOfModules.IsQuasicoherent (R := (Spec A).ringCatSheaf) L :=
    isQuasicoherent_of_isInvertible L
  haveI : SheafOfModules.IsQuasicoherent (R := (Spec A).ringCatSheaf) (dual L) :=
    isQuasicoherent_of_isInvertible (dual L)
  let eL : tilde M ≅ L :=
    @asIso _ _ _ _ L.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent L)
  let eN : tilde N ≅ dual L :=
    @asIso _ _ _ _ (dual L).fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _)
  let e : tilde (ModuleCat.of A (M ⊗[A] N)) ≅ tilde (ModuleCat.of A A) :=
    tildeTensorIso M N ≪≫ (eL ⊗ᵢ eN) ≪≫ tensorDualIso L ≪≫ (structureSheafIsoUnit _).symm ≪≫
      (tildeSelf (R := A)).symm
  let e' : M ⊗[A] N ≃ₗ[A] A := ((tilde.fullyFaithfulFunctor (R := A)).preimageIso e).toLinearEquiv
  haveI : Module.Invertible A M := Module.Invertible.left e'
  refine ⟨Additive.ofMul (CommRing.Pic.mk A M), ?_⟩
  change Pic.mk (tilde (ModuleCat.of A (CommRing.Pic.mk A M))) = Pic.mk L
  exact Pic.mk_eq_of_iso
    ((tilde.functor A).mapIso (CommRing.Pic.mk.linearEquiv A M).toModuleIso ≪≫ eL)

/-- `Pic (Spec A) ≃ Pic A`: the invertible sheaves on `Spec A` are the `M^~` for invertible
`A`-modules `M`. -/
def picSpecEquiv : (Spec A).Pic ≃+ Additive (CommRing.Pic A) :=
  (AddEquiv.ofBijective picTilde ⟨picTilde_injective, picTilde_surjective⟩).symm

instance [IsLocalRing A] : Subsingleton (Spec A).Pic :=
  picSpecEquiv.toEquiv.subsingleton

end AlgebraicGeometry

end
