/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicMap
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.PicardGroup

/-!
# The Picard group of an affine scheme

For a commutative ring `R` and an `R`-module `M`, the sheaf `M^~` on `Spec R` is the
sheafification of the presheaf `V ↦ 𝒪(V) ⊗_R M` (`tildeSheafifyIso`): the canonical map
`𝒪(D(f)) ⊗_R M → M_f = M^~(D(f))` is bijective on basic opens. Consequently `(-)^~` is
compatible with tensor products, the sheaf `M^~` of an invertible module is invertible, and
`(Spec R).Pic ≃+ Additive (CommRing.Pic R)` (`picSpecEquiv`).
-/

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry

open Scheme Scheme.Modules CurvesJacobian

variable {A : CommRingCat.{u}}

section LocalBasis

variable {X : Scheme.{u}}

open _root_.PresheafOfModules in
/-- If `φ` is bijective on a basis of the topology, it is locally injective and surjective. -/
lemma Scheme.PresheafOfModules.isLocallyBijective_of_basis {P Q : X.PresheafOfModules}
    (φ : P ⟶ Q) (B : Set X.Opens)
    (hB : ∀ (V : X.Opens) (x : X), x ∈ V → ∃ W ∈ B, x ∈ W ∧ W ≤ V)
    (H : ∀ W ∈ B, Function.Bijective (φ.app (op W))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
        ((_root_.PresheafOfModules.toPresheaf _).map φ) ∧
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        ((_root_.PresheafOfModules.toPresheaf _).map φ) := by
  constructor
  · rw [isLocallyInjective_iff_of_additive]
    intro V m hm x hx
    obtain ⟨W, hWB, hxW, hWV⟩ := hB V.unop x hx
    refine ⟨W, homOfLE hWV, ?_, hxW⟩
    have h1 : φ.app (op W) (P.map (homOfLE hWV).op m) = 0 := by
      rw [naturality_apply]
      change Q.map _ (φ.app V m) = 0
      rw [show φ.app V m = 0 from hm, map_zero]
    exact ((H W hWB).1 (h1.trans (map_zero _).symm)).trans (map_zero _).symm
  · refine ⟨fun {V} n x hx ↦ ?_⟩
    obtain ⟨W, hWB, hxW, hWV⟩ := hB V x hx
    obtain ⟨m, hm⟩ := (H W hWB).2 (Q.map (homOfLE hWV).op n)
    exact ⟨W, homOfLE hWV, ⟨m, hm⟩, hxW⟩

end LocalBasis

section Algebra

/-- If `m/1` is a basis of `M_r` and `r` is invertible in the `R`-algebra `B`, then
`b ↦ b ⊗ m` is a bijection `B ≃ B ⊗_R M`. -/
lemma bijective_tmul_of_localization {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (r : R) (m : M)
    (hm : Function.Bijective (fun a : Localization.Away r ↦
      a • LocalizedModule.mkLinearMap (Submonoid.powers r) M m))
    {B : Type*} [CommRing B] [Algebra R B] (hr : IsUnit (algebraMap R B r)) :
    Function.Bijective (fun b : B ↦ b ⊗ₜ[R] m) := by
  letI : Algebra (Localization.Away r) B := (IsLocalization.Away.lift r hr).toAlgebra
  haveI : IsScalarTower R (Localization.Away r) B := IsScalarTower.of_algebraMap_eq
    (fun a ↦ (IsLocalization.Away.lift_eq r hr a).symm)
  let e1 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away r) B B M
  let e2 := (LocalizedModule.isBaseChange (Submonoid.powers r) M).equiv
  let e3 := (LinearEquiv.ofBijective (LinearMap.toSpanSingleton (Localization.Away r) _
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M m)) (by exact hm)).symm
  let e : B ⊗[R] M ≃ₗ[B] B := e1.symm ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (e2 ≪≫ₗ e3)) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid (Localization.Away r) B B
  have h2 : e2 (1 ⊗ₜ m) = LocalizedModule.mkLinearMap (Submonoid.powers r) M m := by
    simp [e2, IsBaseChange.equiv_tmul]
  have h3 : e3 (LocalizedModule.mkLinearMap (Submonoid.powers r) M m) = 1 := by
    apply (LinearEquiv.ofBijective (LinearMap.toSpanSingleton (Localization.Away r) _
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M m)) (by exact hm)).injective
    simp [e3]
  have he : ∀ b : B, e (b ⊗ₜ[R] m) = b := by
    intro b
    simp only [e, LinearEquiv.trans_apply, e1,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
    rw [h2, h3, TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]
  have : (fun b : B ↦ b ⊗ₜ[R] m) = e.symm := by
    funext b
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply]
  rw [this]
  exact e.symm.bijective

/-- An invertible module becomes free with a basis of the form `m/1` after localizing at the
members of a finite family generating the unit ideal. -/
lemma exists_localization_basis {R : Type u} [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Invertible R M] :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧ ∀ r ∈ s, ∃ m : M,
      Function.Bijective (fun a : Localization.Away r ↦
        a • LocalizedModule.mkLinearMap (Submonoid.powers r) M m) := by
  obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization R M
  refine ⟨s, hs, fun r hr ↦ ?_⟩
  haveI := hfree r hr
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := Localization.Away r)
    (M := LocalizedModule (Submonoid.powers r) M)).mp inferInstance
  obtain ⟨⟨m, t⟩, hmk⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M) (e.symm 1)
  refine ⟨m, ?_⟩
  have hb : Function.Bijective (fun a : Localization.Away r ↦ a • e.symm 1) := by
    have : (fun a : Localization.Away r ↦ a • e.symm 1) = e.symm := by
      funext a
      rw [← _root_.map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact e.symm.bijective
  have hunit : IsUnit (algebraMap R (Localization.Away r) (t : R)) :=
    IsLocalization.map_units _ t
  have hmk' : LocalizedModule.mkLinearMap (Submonoid.powers r) M m =
      algebraMap R (Localization.Away r) (t : R) • e.symm 1 := by
    simp only [Function.uncurry_apply_pair] at hmk
    rw [← hmk, algebraMap_smul]
    exact (IsLocalizedModule.mk'_cancel' _ m t).symm
  have hmul : (fun a : Localization.Away r ↦ a * algebraMap R (Localization.Away r) (t : R)) =
      ⇑(Units.mulRight hunit.unit) := by
    funext a
    simp
  have : (fun a : Localization.Away r ↦
      a • LocalizedModule.mkLinearMap (Submonoid.powers r) M m) =
      (fun a ↦ a • e.symm 1) ∘
        (fun a ↦ a * algebraMap R (Localization.Away r) (t : R)) := by
    funext a
    simp only [Function.comp_apply, hmk', smul_smul]
  rw [this, hmul]
  exact hb.comp (Units.mulRight hunit.unit).bijective

end Algebra

lemma spec_map_map {U V W : (Spec A).Opens} (h : V ≤ U) (h' : W ≤ V) (c : Γ(Spec A, U)) :
    (Spec A).presheaf.map (homOfLE h').op ((Spec A).presheaf.map (homOfLE h).op c) =
      (Spec A).presheaf.map (homOfLE (h'.trans h)).op c := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma spec_map_self {U : (Spec A).Opens} (c : Γ(Spec A, U)) :
    (Spec A).presheaf.map (homOfLE (le_refl U)).op c = c := by
  change (Spec A).presheaf.map (𝟙 _) c = c
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Restriction of functions on `Spec A` as an `A`-algebra map. -/
def specRes {V V' : (Spec A).Opens} (h : V' ≤ V) : Γ(Spec A, V) →ₐ[A] Γ(Spec A, V') where
  toRingHom := ((Spec A).presheaf.map (homOfLE h).op).hom
  commutes' a := by
    simp only [IsAffineOpen.algebraMap_Spec_obj, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    exact spec_map_map _ _ _

lemma specRes_apply {V V' : (Spec A).Opens} (h : V' ≤ V) (c : Γ(Spec A, V)) :
    specRes h c = (Spec A).presheaf.map (homOfLE h).op c := rfl

variable (M : ModuleCat.{u} A)

/-- The abelian presheaf `V ↦ 𝒪(V) ⊗_A M` on `Spec R`. -/
def tensorPresheaf : (Spec A).Opensᵒᵖ ⥤ Ab.{u} where
  obj V := AddCommGrpCat.of (Γ(Spec A, V.unop) ⊗[A] M)
  map f := AddCommGrpCat.ofHom
    (TensorProduct.map (specRes f.unop.le).toLinearMap (LinearMap.id (M := M))).toAddMonoidHom
  map_id V := by
    ext x
    change TensorProduct.map _ _ x = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq]
      rw [specRes_apply]
      congr 1
    | add x y hx hy => rw [map_add, hx, hy]
  map_comp f g := by
    ext x
    change TensorProduct.map _ _ x = TensorProduct.map _ _ (TensorProduct.map _ _ x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq]
      rw [specRes_apply, specRes_apply, specRes_apply]
      congr 1
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

instance (V : (Spec A).Opensᵒᵖ) :
    Module ((Spec A).ringCatSheaf.obj.obj V) ((tensorPresheaf M).obj V) :=
  inferInstanceAs (Module Γ(Spec A, V.unop) (Γ(Spec A, V.unop) ⊗[A] M))

/-- The presheaf of modules `V ↦ 𝒪(V) ⊗_A M` on `Spec R`. -/
def tensorPre : (Spec A).PresheafOfModules :=
  _root_.PresheafOfModules.ofPresheaf (tensorPresheaf M) (fun V V' f r x ↦ by
    change TensorProduct.map (specRes f.unop.le).toLinearMap LinearMap.id
        ((show Γ(Spec A, V.unop) from r) • (show Γ(Spec A, V.unop) ⊗[A] M from x)) =
      (specRes f.unop.le (show Γ(Spec A, V.unop) from r)) •
        TensorProduct.map (specRes f.unop.le).toLinearMap LinearMap.id
          (show Γ(Spec A, V.unop) ⊗[A] M from x)
    generalize (show Γ(Spec A, V.unop) ⊗[A] M from x) = y
    generalize (show Γ(Spec A, V.unop) from r) = c
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c' m =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.smul_tmul']
      congr 1
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add])


/-- The bilinear map `(c, m) ↦ c • m` with values in `M^~(V)`. -/
def tildeBil (V : (Spec A).Opens) :
    Γ(Spec A, V) →ₗ[A] M →ₗ[A] Γ(tilde M, V) :=
  LinearMap.mk₂ A (fun c m ↦ c • (show Γ(tilde M, V) from (tilde.toOpen M V).hom m))
    (fun c c' m ↦ add_smul _ _ _)
    (fun a c m ↦ smul_assoc a c _)
    (fun c m m' ↦ by simp only [map_add]; exact smul_add _ _ _)
    (fun a c m ↦ by
      change c • (show Γ(tilde M, V) from (tilde.toOpen M V).hom (a • m)) =
        a • (c • (show Γ(tilde M, V) from (tilde.toOpen M V).hom m))
      rw [show (show Γ(tilde M, V) from (tilde.toOpen M V).hom (a • m)) =
        a • (show Γ(tilde M, V) from (tilde.toOpen M V).hom m) from map_smul _ a m]
      exact smul_comm c a _)

/-- The canonical map of abelian presheaves `𝒪(V) ⊗_A M ⟶ M^~(V)`. -/
def toTildeAb : tensorPresheaf M ⟶ (toPre (tilde M)).presheaf where
  app V := AddCommGrpCat.ofHom (TensorProduct.lift (tildeBil M V.unop)).toAddMonoidHom
  naturality {V V'} f := by
    ext x
    change TensorProduct.lift (tildeBil M V'.unop) (TensorProduct.map _ _ x) =
      (tilde M).presheaf.map f (TensorProduct.lift (tildeBil M V.unop) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq,
        TensorProduct.lift.tmul, tildeBil, LinearMap.mk₂_apply]
      refine Eq.trans ?_ (Modules.map_smul (tilde M) f.unop c _).symm
      congr 1
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add (TensorProduct.lift (tildeBil M V.unop)) x y]
      exact (map_add (ConcreteCategory.hom ((tilde M).presheaf.map f)) _ _).symm

/-- The canonical morphism of presheaves of modules `𝒪 ⊗_A M ⟶ M^~`. -/
def toTilde : tensorPre M ⟶ toPre (tilde M) :=
  _root_.PresheafOfModules.homMk (toTildeAb M) (fun V r x ↦ by
    change TensorProduct.lift (tildeBil M V.unop)
        ((show Γ(Spec A, V.unop) from r) •
          (show Γ(Spec A, V.unop) ⊗[A] M from x)) =
      (show Γ(Spec A, V.unop) from r) •
        TensorProduct.lift (tildeBil M V.unop) (show Γ(Spec A, V.unop) ⊗[A] M from x)
    generalize (show Γ(Spec A, V.unop) ⊗[A] M from x) = y
    generalize (show Γ(Spec A, V.unop) from r) = c
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c' m =>
      rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      simp only [tildeBil, LinearMap.mk₂_apply]
      exact smul_assoc c c' _
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add])

lemma bijective_toTilde_basicOpen (g : A) :
    Function.Bijective ((toTilde M).app (op (PrimeSpectrum.basicOpen g))) := by
  let W : (Spec A).Opens := PrimeSpectrum.basicOpen g
  let f' : M →ₗ[A] Γ(tilde M, W) :=
    { toFun := fun m ↦ (tilde.toOpen M W).hom m
      map_add' := map_add _
      map_smul' := map_smul _ }
  haveI : IsLocalizedModule (Submonoid.powers g) f' :=
    inferInstanceAs (IsLocalizedModule (Submonoid.powers g) (tilde.toOpen M W).hom)
  have h : IsBaseChange Γ(Spec A, W) f' :=
    IsLocalizedModule.isBaseChange (Submonoid.powers g) _ f'
  have : ((toTilde M).app (op W) : _ → _) = h.equiv := by
    funext x
    change TensorProduct.lift (tildeBil M W) x = h.equiv x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [TensorProduct.lift.tmul, IsBaseChange.equiv_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [this]
  exact h.equiv.bijective

lemma sheafificationW_toTilde : sheafificationW (Spec A) (toTilde M) := by
  change (Opens.grothendieckTopology _).W ((_root_.PresheafOfModules.toPresheaf _).map _)
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  refine Scheme.PresheafOfModules.isLocallyBijective_of_basis (toTilde M)
    (Set.range (fun g : A ↦ (PrimeSpectrum.basicOpen g : (Spec A).Opens)))
    (fun V x hx ↦ ?_) (fun W ⟨g, hg⟩ ↦ hg ▸ bijective_toTilde_basicOpen M g)
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx V.isOpen
  exact ⟨PrimeSpectrum.basicOpen g, ⟨g, rfl⟩, hxg, hgV⟩

instance : IsIso ((sheafify (Spec A)).map (toTilde M)) :=
  Localization.inverts (sheafificationFunctor _) (sheafificationW _) _ (sheafificationW_toTilde M)

/-- `M^~` is the sheafification of `V ↦ 𝒪(V) ⊗_A M`. -/
def tildeSheafifyIso : (sheafify (Spec A)).obj (tensorPre M) ≅ tilde M :=
  asIso ((sheafify (Spec A)).map (toTilde M)) ≪≫ sheafifyToPreIso (tilde M)


section Monoidal

variable (N : ModuleCat.{u} A)

lemma tensorPreTensor_naturality_aux {V V' : (Spec A).Opensᵒᵖ} (f : V ⟶ V')
    (y : (Γ(Spec A, V.unop) ⊗[A] M) ⊗[Γ(Spec A, V.unop)] (Γ(Spec A, V.unop) ⊗[A] N)) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange A Γ(Spec A, V'.unop) M N).symm
        ((tensorPre M ⊗ tensorPre N).map f y) =
      TensorProduct.map (specRes f.unop.le).toLinearMap LinearMap.id
        ((TensorProduct.AlgebraTensorModule.distribBaseChange A Γ(Spec A, V.unop) M N).symm y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  | add x y hx hy =>
    rw [map_add, map_add, ← hx, ← hy]
    exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)
  | tmul a b =>
    change (TensorProduct.AlgebraTensorModule.distribBaseChange A Γ(Spec A, V'.unop) M N).symm
        ((TensorProduct.map (specRes f.unop.le).toLinearMap LinearMap.id a) ⊗ₜ
          (TensorProduct.map (specRes f.unop.le).toLinearMap LinearMap.id b)) = _
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a a' ha ha' => rw [TensorProduct.add_tmul, map_add, TensorProduct.add_tmul, map_add,
        ha, ha', map_add, map_add]
    | tmul c m =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add b b' hb hb' =>
        rw [TensorProduct.tmul_add, map_add, TensorProduct.tmul_add, map_add, hb, hb',
          map_add, map_add]
      | tmul c' n =>
        simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq,
          TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, map_mul]

/-- `(𝒪 ⊗ M) ⊗_𝒪 (𝒪 ⊗ N) ⟶ 𝒪 ⊗ (M ⊗ N)` on abelian presheaves. -/
def tensorPreTensorAb : (tensorPre M ⊗ tensorPre N).presheaf ⟶
    (tensorPre (ModuleCat.of A (M ⊗[A] N))).presheaf where
  app V := AddCommGrpCat.ofHom
    (TensorProduct.AlgebraTensorModule.distribBaseChange A Γ(Spec A, V.unop) M
      N).symm.toLinearMap.toAddMonoidHom
  naturality {V V'} f := by
    ext x
    exact tensorPreTensor_naturality_aux M N f x

/-- `(𝒪 ⊗ M) ⊗_𝒪 (𝒪 ⊗ N) ⟶ 𝒪 ⊗ (M ⊗ N)` as presheaves of modules. -/
def tensorPreTensorHom : tensorPre M ⊗ tensorPre N ⟶ tensorPre (ModuleCat.of A (M ⊗[A] N)) :=
  _root_.PresheafOfModules.homMk (tensorPreTensorAb M N) (fun V r x ↦ by
    change (TensorProduct.AlgebraTensorModule.distribBaseChange A Γ(Spec A, V.unop) M N).symm
        ((show Γ(Spec A, V.unop) from r) • (show (Γ(Spec A, V.unop) ⊗[A] M) ⊗[Γ(Spec A, V.unop)]
          (Γ(Spec A, V.unop) ⊗[A] N) from x)) = _
    rw [_root_.map_smul]
    rfl)

lemma bijective_tensorPreTensorHom (V : (Spec A).Opens) :
    Function.Bijective ((tensorPreTensorHom M N).app (op V)) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange A Γ(Spec A, V) M N).symm.bijective

instance : IsIso ((sheafify (Spec A)).map (tensorPreTensorHom M N)) := by
  refine Localization.inverts (sheafificationFunctor _) (sheafificationW _) _ ?_
  change (Opens.grothendieckTopology _).W ((_root_.PresheafOfModules.toPresheaf _).map _)
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  exact Scheme.PresheafOfModules.isLocallyBijective_of_basis _ Set.univ
    (fun V x hx ↦ ⟨V, trivial, hx, le_rfl⟩) (fun W _ ↦ bijective_tensorPreTensorHom M N W)

/-- `(M ⊗ N)^~ ≅ M^~ ⊗ N^~`. -/
def tildeTensorIso : tilde (ModuleCat.of A (M ⊗[A] N)) ≅ tilde M ⊗ tilde N :=
  (tildeSheafifyIso _).symm ≪≫ (asIso ((sheafify (Spec A)).map (tensorPreTensorHom M N))).symm ≪≫
    (Functor.Monoidal.μIso (sheafify (Spec A)) _ _).symm ≪≫
      (tildeSheafifyIso M ⊗ᵢ tildeSheafifyIso N)

end Monoidal

section Invertible

lemma isUnit_algebraMap_of_le_basicOpen {V : (Spec A).Opens} {r : A}
    (h : V ≤ PrimeSpectrum.basicOpen r) : IsUnit (algebraMap A Γ(Spec A, V) r) := by
  have := (IsLocalization.Away.algebraMap_isUnit (S := Γ(Spec A, PrimeSpectrum.basicOpen r)) r).map
    (specRes h)
  rwa [AlgHom.commutes] at this

lemma isBasisOn_tensorPre {r : A} {m : M}
    (hm : Function.Bijective (fun a : Localization.Away r ↦
      a • LocalizedModule.mkLinearMap (Submonoid.powers r) M m)) :
    Scheme.PresheafOfModules.IsBasisOn (tensorPre M) (PrimeSpectrum.basicOpen r)
      ((1 : Γ(Spec A, PrimeSpectrum.basicOpen r)) ⊗ₜ[A] m) := by
  intro V h
  have hb := bijective_tmul_of_localization r m hm (isUnit_algebraMap_of_le_basicOpen h)
  have key : ∀ c : Γ(Spec A, V), (show (Spec A).ringCatSheaf.obj.obj (op V) from c) •
      Scheme.PresheafOfModules.res (tensorPre M) h
        ((1 : Γ(Spec A, PrimeSpectrum.basicOpen r)) ⊗ₜ[A] m) = c ⊗ₜ[A] m := by
    intro c
    change c • TensorProduct.map (specRes h).toLinearMap LinearMap.id
      ((1 : Γ(Spec A, PrimeSpectrum.basicOpen r)) ⊗ₜ[A] m) = _
    rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
    rfl
  refine ⟨fun c c' hcc' ↦ hb.1 ?_, fun y ↦ ?_⟩
  · exact (key c).symm.trans (hcc'.trans (key c'))
  · obtain ⟨c, hc⟩ := hb.2 y
    exact ⟨c, (key c).trans hc⟩

instance (M : ModuleCat.{u} A) [Module.Invertible A M] : (tilde M).IsInvertible := by
  obtain ⟨s, hs, hm⟩ := exists_localization_basis (R := A) M
  have : ((sheafify (Spec A)).obj (tensorPre M)).IsInvertible := by
    apply isInvertible_sheafify
    intro x
    obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x ∈ (PrimeSpectrum.basicOpen r : (Spec A).Opens) := by
      by_contra! H
      have : Ideal.span (s : Set A) ≤ x.asIdeal :=
        Ideal.span_le.mpr (fun r hr ↦ not_not.mp (fun h ↦ H r hr
          ((PrimeSpectrum.mem_basicOpen _ _).mpr h)))
      rw [hs] at this
      exact x.isPrime.ne_top (top_le_iff.mp this)
    obtain ⟨m, hm⟩ := hm r hr
    exact ⟨_, _, hxr, isBasisOn_tensorPre M hm⟩
  exact .of_iso (tildeSheafifyIso M)

end Invertible

end AlgebraicGeometry

end
