/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.BaseExtensionPi
import CurvesJacobian.Cusp.FieldExtIso
import CurvesJacobian.LocAn.HypCurveBcExt
import CurvesJacobian.LocAn.ExistsAssembly

/-!
# Base change of an isomorphism `Π_{U₁} ≃ Π_{U₂}` over `G_K` to `G_L` (MR7 S1, [LocAn] Cor. 15.5)

The proof of [LocAn] Cor. 15.5 (`The Local Pro-p Anabelian Geometry of Curves.txt`
l.4338–4370) descends the existence half of the rel-isom-DGC from a finite extension `L` of `ℚ_p`
to a number field `K ⊆ L`: an isomorphism `φ : Π_{U₁} ≃ Π_{U₂}` over `G_K` is base-changed to
`φ_L = φ ×_{G_K} G_L : Π_{U₁,L} ≃ Π_{U₂,L}` over `G_L` ("By base-changing to `L`"), the theorem
over `L` gives an `L`-isomorphism inducing `φ_L`, and Galois descent gives a `K`-isomorphism.

This file does the first step in the language of `Belyi.Anabelian.RelIsomDGC.Exists`, and states
the descent step as the remaining debt `DescentIso`:

* geometric points: for `Ω ⊆ Ω'` algebraic closures of `K ⊆ L` and a geometric point `ξ` of `U`
  over `Ω`, the point `bcExtPt L Ω' ξ` of `U_L` over `Ω'` (`Spec Ω' → Spec Ω → U` and
  `Spec Ω' → Spec L`);
* comparison `U_L ≅ Spec (L ⊗[K] R)` for an affine model `U ≅ Spec R` (`bcExtSpecIso`; for a
  curve with a cusp `R = Γ(X̄, U)` via `IsAffineOpen.isoSpec`);
* `Π_{U_L} = Π_U ×_{G_K} G_L` at these points (`isFibrePres_bcExt`), from PI1TOP's I3
  (`CurvesJacobian.Cusp.existsUnique_baseExtension_hypCurve`) transported along these isomorphisms
  and `Ω ⊆ Ω'` (`fieldExtEquiv`);
* lifting isomorphisms to fibre products of profinite groups (`IsFibrePres.liftEquiv`), hence
  `φ_L` (`bcExtPhi`), which lies over `G_L` (`isOverGk_bcExtPhi`) and over `φ`
  (`bcExtPiU_bcExtPhi`).

## Main results

* **`CurvesJacobian.LocAn.isFibrePres_bcExt`**, **`CurvesJacobian.LocAn.bcExtPhi`**,
  `CurvesJacobian.LocAn.isOverGk_bcExtPhi`;
* `CurvesJacobian.LocAn.DescentIso`: the debt S1(iii) (Galois descent of isomorphisms: finiteness of
  `Isom(U₁,K̄, U₂,K̄)`, invariance under `K̄ ⊆ L̄`, descent with `innerRigid`);
* `CurvesJacobian.LocAn.DescentNFProper`: the debt S1 for pairs containing a proper curve (needs the
  fibre product for proper curves, PI1TOP open item (2));
* **`CurvesJacobian.LocAn.descentNF_of_descentIso`**: `DescentIso` and `DescentNFProper` give the
  S8 debt `DescentNF p` of `LocAn/ExistsAssembly.lean`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace CurvesJacobian.LocAn

/-! ### Lifting an isomorphism to fibre products -/

section FibreLift

variable {P₁ P₂ A₁ A₂ B G : Type*} [Group P₁] [Group P₂] [Group A₁] [Group A₂] [Group B]
  [TopologicalSpace P₁] [TopologicalSpace P₂] [TopologicalSpace A₁] [TopologicalSpace A₂]
  [TopologicalSpace B]

/-- A pair `(a, b) : P → A × B` of continuous homomorphisms **presents `P` as the fibre product**
`A ×_G B` along `q : A → G`, `r : B → G`: `q ∘ a = r ∘ b`, and every `(a₀, b₀)` with
`q a₀ = r b₀` is `(a γ, b γ)` for a unique `γ`. -/
def IsFibrePres (a : P₁ →ₜ* A₁) (b : P₁ →ₜ* B) (q : A₁ → G) (r : B → G) : Prop :=
  (∀ γ, q (a γ) = r (b γ)) ∧ ∀ a₀ b₀, q a₀ = r b₀ → ∃! γ, a γ = a₀ ∧ b γ = b₀

variable {a₁ : P₁ →ₜ* A₁} {b₁ : P₁ →ₜ* B} {a₂ : P₂ →ₜ* A₂} {b₂ : P₂ →ₜ* B}
  {q₁ : A₁ → G} {q₂ : A₂ → G} {r : B → G}

namespace IsFibrePres

lemma ext (h : IsFibrePres a₁ b₁ q₁ r) {γ γ' : P₁} (ha : a₁ γ = a₁ γ') (hb : b₁ γ = b₁ γ') :
    γ = γ' :=
  (h.2 _ _ (h.1 γ')).unique ⟨ha, hb⟩ ⟨rfl, rfl⟩

/-- The map `P₁ → P₂` lifting `(a, b) ↦ (φ a, b)` (fibre products over `G`). -/
def liftFun (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ →* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) (γ : P₁) : P₂ :=
  (h₂.2 (φ (a₁ γ)) (b₁ γ) (by rw [hφ, h₁.1])).exists.choose

lemma liftFun_spec (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ →* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) (γ : P₁) :
    a₂ (liftFun h₂ h₁ φ hφ γ) = φ (a₁ γ) ∧ b₂ (liftFun h₂ h₁ φ hφ γ) = b₁ γ :=
  (h₂.2 (φ (a₁ γ)) (b₁ γ) (by rw [hφ, h₁.1])).exists.choose_spec

variable [CompactSpace P₁] [CompactSpace P₂] [T2Space A₁] [T2Space A₂] [T2Space B]

/-- `γ ↦ (a γ, b γ)` is a closed embedding (`P` compact, `A × B` Hausdorff). -/
lemma isEmbedding (h : IsFibrePres a₁ b₁ q₁ r) :
    Topology.IsEmbedding fun γ ↦ (a₁ γ, b₁ γ) :=
  (Continuous.isClosedEmbedding ((map_continuous a₁).prodMk (map_continuous b₁))
    fun _ _ hγ ↦ h.ext (congrArg Prod.fst hγ) (congrArg Prod.snd hγ)).isEmbedding

/-- The lift as a continuous homomorphism. -/
def lift (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ →ₜ* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) : P₁ →ₜ* P₂ where
  toFun := liftFun h₂ h₁ φ.toMonoidHom hφ
  map_one' := h₂.ext (by rw [(liftFun_spec h₂ h₁ _ hφ 1).1]; simp)
    (by rw [(liftFun_spec h₂ h₁ _ hφ 1).2]; simp)
  map_mul' x y := h₂.ext
    (by rw [(liftFun_spec h₂ h₁ _ hφ (x * y)).1, map_mul a₂, (liftFun_spec h₂ h₁ _ hφ x).1,
      (liftFun_spec h₂ h₁ _ hφ y).1, map_mul a₁, map_mul])
    (by rw [(liftFun_spec h₂ h₁ _ hφ (x * y)).2, map_mul b₂, (liftFun_spec h₂ h₁ _ hφ x).2,
      (liftFun_spec h₂ h₁ _ hφ y).2, map_mul b₁])
  continuous_toFun := by
    rw [h₂.isEmbedding.continuous_iff]
    have : ((fun γ ↦ (a₂ γ, b₂ γ)) ∘ liftFun h₂ h₁ φ.toMonoidHom hφ) =
        fun γ ↦ (φ (a₁ γ), b₁ γ) :=
      funext fun γ ↦ Prod.ext (liftFun_spec h₂ h₁ _ hφ γ).1 (liftFun_spec h₂ h₁ _ hφ γ).2
    rw [this]
    exact ((map_continuous φ).comp (map_continuous a₁)).prodMk (map_continuous b₁)

omit [CompactSpace P₁] [T2Space A₁] in
lemma a_lift (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ →ₜ* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) (γ : P₁) : a₂ (lift h₂ h₁ φ hφ γ) = φ (a₁ γ) :=
  (liftFun_spec h₂ h₁ φ.toMonoidHom hφ γ).1

omit [CompactSpace P₁] [T2Space A₁] in
lemma b_lift (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ →ₜ* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) (γ : P₁) : b₂ (lift h₂ h₁ φ hφ γ) = b₁ γ :=
  (liftFun_spec h₂ h₁ φ.toMonoidHom hφ γ).2

/-- **An isomorphism `A₁ ≃ A₂` over `G` lifts to `A₁ ×_G B ≃ A₂ ×_G B`**: the unique
`φ_B : P₁ ≃ₜ* P₂` with `a₂ ∘ φ_B = φ ∘ a₁` and `b₂ ∘ φ_B = b₁`. -/
def liftEquiv (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ ≃ₜ* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) : P₁ ≃ₜ* P₂ :=
  have hφ' : ∀ x, q₁ (φ.symm x) = q₂ x := fun x ↦ by rw [← hφ, φ.apply_symm_apply]
  let f := lift h₂ h₁ (φ : A₁ →ₜ* A₂) hφ
  let g := lift h₁ h₂ (φ.symm : A₂ →ₜ* A₁) hφ'
  { toFun := f
    invFun := g
    left_inv := fun γ ↦ h₁.ext (by
        rw [a_lift h₁ h₂ _ hφ', a_lift h₂ h₁ _ hφ]
        exact φ.symm_apply_apply _)
      (by rw [b_lift h₁ h₂ _ hφ', b_lift h₂ h₁ _ hφ])
    right_inv := fun γ ↦ h₂.ext (by
        rw [a_lift h₂ h₁ _ hφ, a_lift h₁ h₂ _ hφ']
        exact φ.apply_symm_apply _)
      (by rw [b_lift h₂ h₁ _ hφ, b_lift h₁ h₂ _ hφ'])
    map_mul' := map_mul f
    continuous_toFun := map_continuous f
    continuous_invFun := map_continuous g }

lemma a_liftEquiv (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ ≃ₜ* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) (γ : P₁) : a₂ (liftEquiv h₂ h₁ φ hφ γ) = φ (a₁ γ) :=
  a_lift h₂ h₁ _ hφ γ

lemma b_liftEquiv (h₂ : IsFibrePres a₂ b₂ q₂ r) (h₁ : IsFibrePres a₁ b₁ q₁ r) (φ : A₁ ≃ₜ* A₂)
    (hφ : ∀ x, q₂ (φ x) = q₁ x) (γ : P₁) : b₂ (liftEquiv h₂ h₁ φ hφ γ) = b₁ γ :=
  b_lift h₂ h₁ _ hφ γ

end IsFibrePres

end FibreLift

/-! ### Transport lemmas for `π₁ᵉᵗ` -/

section Transport

open FiniteEtale

variable {X Y : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']

/-- Naturality of `fieldExtEquiv` along `f`, at an arbitrary target point `x = y ≫ f`. -/
lemma fundamentalGroupMap_fieldExtEquiv' (ι : Ω →+* Ω') [ConnectedSpace X] [ConnectedSpace Y]
    (f : Y ⟶ X) {y : Spec (.of Ω) ⟶ Y} {x : Spec (.of Ω) ⟶ X} (h : y ≫ f = x)
    (h' : (specHom ι ≫ y) ≫ f = specHom ι ≫ x) (γ : π₁ᵉᵗ(y)) :
    fundamentalGroupMap f h' (fieldExtEquiv ι y γ) =
      fieldExtEquiv ι x (fundamentalGroupMap f h γ) := by
  subst h
  exact fundamentalGroupMap_fieldExtEquiv ι f y h' γ

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
/-- An equation between images in `π₁ᵉᵗ(w)` transports along `w = z`. -/
lemma fundamentalGroupMap_eq_transport {Y₁ Y₂ : Scheme.{u}} {w z : Spec (.of Ω) ⟶ X}
    (hwz : w = z) {y₁ : Spec (.of Ω) ⟶ Y₁} {y₂ : Spec (.of Ω) ⟶ Y₂} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    (h₁ : y₁ ≫ f₁ = w) (h₂ : y₂ ≫ f₂ = w) (h₁' : y₁ ≫ f₁ = z) (h₂' : y₂ ≫ f₂ = z)
    (α : π₁ᵉᵗ(y₁)) (β : π₁ᵉᵗ(y₂)) (h : fundamentalGroupMap f₁ h₁ α = fundamentalGroupMap f₂ h₂ β) :
    fundamentalGroupMap f₁ h₁' α = fundamentalGroupMap f₂ h₂' β := by
  subst hwz
  exact h

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
/-- Functoriality, applied to an element. -/
lemma fundamentalGroupMap_comp_apply {W : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ W)
    {gp : Spec (.of Ω) ⟶ Y} {η : Spec (.of Ω) ⟶ X} {ζ : Spec (.of Ω) ⟶ W} (h₁ : gp ≫ f = η)
    (h₂ : η ≫ g = ζ) (h : gp ≫ f ≫ g = ζ) (γ : π₁ᵉᵗ(gp)) :
    fundamentalGroupMap g h₂ (fundamentalGroupMap f h₁ γ) = fundamentalGroupMap (f ≫ g) h γ := by
  rw [fundamentalGroupMap_comp f g h₁ h₂ h]
  rfl

end Transport

/-! ### The base-changed curve: projection, comparison with `Spec (L ⊗ R)`, points -/

section BaseExt

open Belyi Belyi.Anabelian HypCurve FiniteEtale CurvesJacobian.Cusp

variable {K : Type u} [Field K] [CharZero K] (L : Type u) [Field L] [Algebra K L]

/-- The projection `U_L ⟶ U` of the base change `U_L = Spec L ×_{Spec K} U`. -/
def bcExtPr (C : HypCurve K) : (C.bcExt L).U.toScheme ⟶ C.U.toScheme :=
  (bcExtOpenIso L C).hom ≫ pullback.snd _ _

lemma bcExtPr_toSpec (C : HypCurve K) :
    bcExtPr L C ≫ C.toSpec = (C.bcExt L).toSpec ≫ specAlgebraMap K L := by
  rw [bcExtPr, Category.assoc, ← pullback.condition, ← Category.assoc, bcExtOpenIso_hom_fst]

section Model

variable {R : Type u} [CommRing R] [Algebra K R] {C : HypCurve K}
  (eU : C.U.toScheme ≅ Spec (.of R)) (heU : eU.hom ≫ strSpecR K R = C.toSpec)

/-- **`U_L ≅ Spec (L ⊗[K] R)`** for an affine model `U ≅ Spec R` over `K`. -/
def bcExtSpecIso : (C.bcExt L).U.toScheme ≅ Spec (.of (L ⊗[K] R)) :=
  bcExtOpenIso L C ≪≫
    @asIso _ _ _ _ (pullback.map (specAlgebraMap K L) C.toSpec (specExt K L) (strSpecR K R)
      (𝟙 _) eU.hom (𝟙 _) (by rw [Category.id_comp, Category.comp_id]; rfl)
      (by rw [Category.comp_id, heU])) (by infer_instance) ≪≫
    pullbackSpecIso K L R

lemma bcExtSpecIso_strSpec : (bcExtSpecIso L eU heU).hom ≫ strSpec K L R = (C.bcExt L).toSpec := by
  simp only [bcExtSpecIso, Iso.trans_hom, asIso_hom, Category.assoc, strSpec,
    pullbackSpecIso_hom_fst', pullback.lift_fst, Category.comp_id, bcExtOpenIso_hom_fst]

lemma bcExtSpecIso_baseChangeSpec :
    (bcExtSpecIso L eU heU).hom ≫ baseChangeSpec K L R = bcExtPr L C ≫ eU.hom := by
  have h : (pullbackSpecIso K L R).hom ≫ baseChangeSpec K L R = pullback.snd _ _ :=
    pullbackSpecIso_hom_snd K L R
  simp only [bcExtSpecIso, Iso.trans_hom, asIso_hom, Category.assoc, bcExtPr, h,
    pullback.lift_snd]

end Model

variable {L} {Ω Ω' : Type u} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra L Ω'] [Algebra Ω Ω']
  [iKΩ' : Algebra K Ω'] [tΩ : IsScalarTower K Ω Ω'] [tL : IsScalarTower K L Ω']

include iKΩ' tΩ tL

variable (K L Ω Ω') in
omit [CharZero K] in
lemma specMap_tower :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω')) ≫ specAlgebraMap K L =
      specHom (algebraMap Ω Ω') ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [specAlgebraMap, specHom, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

variable (L Ω') in
/-- **The geometric point of `U_L` over a geometric point `ξ` of `U`**: `(Spec Ω' → Spec L,
Spec Ω' → Spec Ω → U)` into `U_L = Spec L ×_{Spec K} U`. -/
def bcExtPt {C : HypCurve K} (gp : GeomPt Ω C) : GeomPt Ω' (C.bcExt L) :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap L Ω')))
      (specHom (algebraMap Ω Ω') ≫ gp.x)
      (by rw [specMap_tower K L Ω Ω', Category.assoc, gp.over]) ≫ (bcExtOpenIso L C).inv, by
    rw [Category.assoc, ← bcExtOpenIso_hom_fst L C, Iso.inv_hom_id_assoc, pullback.lift_fst]⟩

variable (L Ω') in
lemma bcExtPt_pr {C : HypCurve K} (gp : GeomPt Ω C) :
    (bcExtPt L Ω' gp).x ≫ bcExtPr L C = specHom (algebraMap Ω Ω') ≫ gp.x := by
  simp only [bcExtPt, bcExtPr, Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

end BaseExt

/-! ### `Π_{U_L} = Π_U ×_{G_K} G_L` at the points `bcExtPt` -/

section Fibre

open Belyi Belyi.Anabelian HypCurve FiniteEtale CurvesJacobian.Cusp

variable {K : Type u} [Field K] [CharZero K] (L : Type u) [Field L] [Algebra K L]
  {Ω Ω' : Type u} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra L Ω'] [Algebra Ω Ω']
  [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'] [IsSepClosed Ω] [IsSepClosed Ω']

instance connectedSpace_U (C : HypCurve K) : ConnectedSpace C.U.toScheme := by
  haveI := IsCurveOver.isIntegral K C.Xbar
  haveI : Nonempty C.U := C.nonempty.to_subtype
  infer_instance

/-- **`Π_{U_L} → Π_U`** at the points `bcExtPt ξ ↦ ξ` (projection, then `Ω' ↦ Ω`). -/
def bcExtPiU (C : HypCurve K) (gp : GeomPt Ω C) :
    π₁ᵉᵗ((bcExtPt L Ω' gp).x) →ₜ* π₁ᵉᵗ(gp.x) :=
  ((fieldExtEquiv (algebraMap Ω Ω') gp.x).symm : _ →ₜ* _).comp
    (fundamentalGroupMap (bcExtPr L C) (bcExtPt_pr L Ω' gp))

lemma bcExtPiU_apply (C : HypCurve K) (gp : GeomPt Ω C) (γ) :
    bcExtPiU L C gp γ = (fieldExtEquiv (algebraMap Ω Ω') gp.x).symm
      (fundamentalGroupMap (bcExtPr L C) (bcExtPt_pr L Ω' gp) γ) := rfl

/-- **`Π_{U_L} → G_L`** (`π₁ᵉᵗ(Spec L)` at `Spec Ω'`). -/
def bcExtPiG (C : HypCurve K) (gp : GeomPt Ω C) :
    π₁ᵉᵗ((bcExtPt L Ω' gp).x) →ₜ*
      π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap L Ω'))) :=
  fundamentalGroupMap (C.bcExt L).toSpec (bcExtPt L Ω' gp).over

variable (Ω Ω') in
/-- **`G_L → G_K`** (`π₁ᵉᵗ(Spec L)` at `Spec Ω'` to `π₁ᵉᵗ(Spec K)` at `Spec Ω`). -/
def resGL (b : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap L Ω')))) :
    π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  (fieldExtEquiv (algebraMap Ω Ω') (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).symm
    (fundamentalGroupMap (specAlgebraMap K L) (specMap_tower K L Ω Ω') b)

omit [CharZero K] [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'] in
lemma fieldExt_toSpec (C : HypCurve K) (gp : GeomPt Ω C)
    (a : π₁ᵉᵗ(gp.x)) :
    fundamentalGroupMap C.toSpec (by rw [Category.assoc, gp.over])
      (fieldExtEquiv (algebraMap Ω Ω') gp.x a) =
    fieldExtEquiv (algebraMap Ω Ω') (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (fundamentalGroupMap C.toSpec gp.over a) :=
  fundamentalGroupMap_fieldExtEquiv' _ C.toSpec gp.over _ a

section Pres

variable {R : Type u} [CommRing R] [Algebra K R] (C : HypCurve K)
  (eU : C.U.toScheme ≅ Spec (.of R)) (heU : eU.hom ≫ strSpecR K R = C.toSpec) (gp : GeomPt Ω C)

/-- The point `Spec Ω' ⟶ Spec (L ⊗[K] R)` of I3. -/
abbrev specPt : Spec (.of Ω') ⟶ Spec (.of (L ⊗[K] R)) :=
  (bcExtPt L Ω' gp).x ≫ (bcExtSpecIso L eU heU).hom

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specPt_strSpec : specPt (Ω' := Ω') L C eU heU gp ≫ strSpec K L R =
    Spec.map (CommRingCat.ofHom (algebraMap L Ω')) := by
  rw [Category.assoc, bcExtSpecIso_strSpec, (bcExtPt L Ω' gp).over]

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specPt_baseChangeSpec :
    (specHom (algebraMap Ω Ω') ≫ gp.x) ≫ eU.hom =
      specPt (Ω' := Ω') L C eU heU gp ≫ baseChangeSpec K L R := by
  symm
  rw [specPt, Category.assoc, bcExtSpecIso_baseChangeSpec, ← Category.assoc, bcExtPt_pr L Ω' gp]

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specPt_hb : Spec.map (CommRingCat.ofHom (algebraMap L Ω')) ≫ specExt K L =
    (specPt (Ω' := Ω') L C eU heU gp ≫ baseChangeSpec K L R) ≫ strSpecR K R := by
  rw [← specPt_baseChangeSpec, Category.assoc, heU, Category.assoc, gp.over]
  exact specMap_tower K L Ω Ω'

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specPt_a (γ : π₁ᵉᵗ((bcExtPt L Ω' gp).x)) :
    fundamentalGroupMap (baseChangeSpec K L R) rfl
      (fundamentalGroupMap (bcExtSpecIso L eU heU).hom rfl γ) =
    fundamentalGroupMap eU.hom (specPt_baseChangeSpec (Ω' := Ω') L C eU heU gp)
      (fundamentalGroupMap (bcExtPr L C) (bcExtPt_pr L Ω' gp) γ) := by
  rw [fundamentalGroupMap_comp_apply _ _ _ _ (by rw [← Category.assoc]),
    fundamentalGroupMap_comp_apply _ _ _ _
      (by rw [← Category.assoc, bcExtPt_pr L Ω' gp,
        specPt_baseChangeSpec (Ω' := Ω') L C eU heU gp])]
  exact DFunLike.congr_fun
    (fundamentalGroupMap_congr (Ω := Ω') (bcExtSpecIso_baseChangeSpec L eU heU) _ _) γ

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
lemma specPt_b (γ : π₁ᵉᵗ((bcExtPt L Ω' gp).x)) :
    fundamentalGroupMap (strSpec K L R) (specPt_strSpec (Ω' := Ω') L C eU heU gp)
      (fundamentalGroupMap (bcExtSpecIso L eU heU).hom rfl γ) =
    bcExtPiG L C gp γ := by
  rw [fundamentalGroupMap_comp_apply _ _ _ _
    (by rw [← Category.assoc, specPt_strSpec (Ω' := Ω') L C eU heU gp])]
  exact DFunLike.congr_fun
    (fundamentalGroupMap_congr (Ω := Ω') (bcExtSpecIso_strSpec L eU heU) _ _) γ

include eU heU in
/-- **Fibre-product presentation of `Π_{U_L}` from I3 for a model `U ≅ Spec R`**: if the
fibre-product property of PI1TOP's I3 holds for `Spec (L ⊗[K] R) → Spec R` (hypothesis `hI3`, the
form of `existsUnique_baseExtension_hypCurve`), then at the points `bcExtPt ξ` over `ξ` the pair
`(Π_{U_L} → Π_U, Π_{U_L} → G_L)` presents `Π_{U_L}` as `Π_U ×_{G_K} G_L`. -/
theorem isFibrePres_bcExt_of
    (hI3 : ∀ (pt : Spec (.of Ω') ⟶ Spec (.of (L ⊗[K] R)))
      (hpt : pt ≫ strSpec K L R = Spec.map (CommRingCat.ofHom (algebraMap L Ω')))
      (hb : Spec.map (CommRingCat.ofHom (algebraMap L Ω')) ≫ specExt K L =
        (pt ≫ baseChangeSpec K L R) ≫ strSpecR K R)
      (a : π₁ᵉᵗ(pt ≫ baseChangeSpec K L R))
      (b : π₁ᵉᵗ(Spec.map (CommRingCat.ofHom (algebraMap L Ω')))),
      fundamentalGroupMap (strSpecR K R) rfl a = fundamentalGroupMap (specExt K L) hb b →
      ∃! γ : π₁ᵉᵗ(pt), fundamentalGroupMap (baseChangeSpec K L R) rfl γ = a ∧
        fundamentalGroupMap (strSpec K L R) hpt γ = b) :
    IsFibrePres (bcExtPiU L C gp) (bcExtPiG L C gp) (fundamentalGroupMap C.toSpec gp.over)
      (resGL L Ω Ω') := by
  have hcomm : ∀ γ, fundamentalGroupMap C.toSpec gp.over (bcExtPiU L C gp γ) =
      resGL L Ω Ω' (bcExtPiG L C gp γ) := fun γ ↦ by
    apply (fieldExtEquiv (algebraMap Ω Ω')
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).injective
    rw [← fieldExt_toSpec, resGL, ContinuousMulEquiv.apply_symm_apply, bcExtPiU_apply,
      ContinuousMulEquiv.apply_symm_apply, bcExtPiG, fundamentalGroupMap_comp_apply _ _ _ _
      (by rw [← Category.assoc, bcExtPt_pr L Ω' gp, Category.assoc, gp.over]),
      fundamentalGroupMap_comp_apply _ _ _ _ (by rw [← Category.assoc, (bcExtPt L Ω' gp).over,
        specMap_tower K L Ω Ω'])]
    exact DFunLike.congr_fun (fundamentalGroupMap_congr (Ω := Ω') (bcExtPr_toSpec L C) _ _) γ
  refine ⟨hcomm, fun a₀ b₀ hab ↦ ?_⟩
  have h₁ := specPt_baseChangeSpec (Ω' := Ω') L C eU heU gp
  have hb := specPt_hb (Ω' := Ω') L C eU heU gp
  have hab' : fundamentalGroupMap (strSpecR K R) rfl
      (fundamentalGroupMap eU.hom h₁ (fieldExtEquiv (algebraMap Ω Ω') gp.x a₀)) =
      fundamentalGroupMap (specExt K L) hb b₀ := by
    rw [fundamentalGroupMap_comp_apply _ _ _ _ (by rw [← Category.assoc, h₁])]
    rw [fundamentalGroupMap_congr heU _ (by rw [← heU, ← Category.assoc, h₁])]
    have hw : specHom (algebraMap Ω Ω') ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
        (specPt (Ω' := Ω') L C eU heU gp ≫ baseChangeSpec K L R) ≫ strSpecR K R := by
      rw [← hb]
      exact (specMap_tower K L Ω Ω').symm
    refine fundamentalGroupMap_eq_transport hw _ _ (by rw [Category.assoc, gp.over])
      (specMap_tower K L Ω Ω') _ _ _ _ ?_
    rw [fieldExt_toSpec, hab, resGL, ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨γ', ⟨hγa, hγb⟩, huniq⟩ := hI3 (specPt (Ω' := Ω') L C eU heU gp)
    (specPt_strSpec (Ω' := Ω') L C eU heU gp) hb
    _ b₀ hab'
  have hbij := fundamentalGroupMap_bijective_of_isIso (bcExtSpecIso L eU heU).hom
    (rfl : (bcExtPt L Ω' gp).x ≫ _ = specPt (Ω' := Ω') L C eU heU gp)
  have hinj := (fundamentalGroupMap_bijective_of_isIso eU.hom h₁).1
  have key : ∀ γ, (fundamentalGroupMap (baseChangeSpec K L R) rfl
      (fundamentalGroupMap (bcExtSpecIso L eU heU).hom rfl γ) =
        fundamentalGroupMap eU.hom h₁ (fieldExtEquiv (algebraMap Ω Ω') gp.x a₀) ∧
      fundamentalGroupMap (strSpec K L R) (specPt_strSpec (Ω' := Ω') L C eU heU gp)
        (fundamentalGroupMap (bcExtSpecIso L eU heU).hom rfl γ) = b₀) ↔
      (bcExtPiU L C gp γ = a₀ ∧ bcExtPiG L C gp γ = b₀) := fun γ ↦ by
    rw [specPt_a, specPt_b, bcExtPiU_apply]
    refine and_congr_left' ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [hinj h, ContinuousMulEquiv.symm_apply_apply]
    · rw [← h, ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨γ, rfl⟩ := hbij.2 γ'
  exact ⟨γ, (key γ).1 ⟨hγa, hγb⟩, fun γ₂ h₂ ↦ hbij.1 (huniq _ ((key γ₂).2 h₂))⟩

end Pres

end Fibre

/-! ### The base-changed isomorphism `φ_L` and the remaining descent debt -/

section Iso

open Belyi Belyi.Anabelian HypCurve FiniteEtale CurvesJacobian.Cusp

attribute [local instance] isAlgClosure_of_isAlgebraic

variable {K : Type u} [Field K] [NumberField K] (L : Type u) [Field L] [Algebra K L]
  {Ω Ω' : Type u} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra L Ω'] [Algebra Ω Ω']
  [Algebra K Ω'] [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'] [IsAlgClosed Ω] [IsAlgClosed Ω']
  [Algebra.IsAlgebraic K Ω] [Algebra.IsAlgebraic L Ω']

lemma isoSpec_strSpecR (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty) :
    (isAffineOpen_U C hc).isoSpec.hom ≫ strSpecR K Γ(C.Xbar, C.U) = C.toSpec := by
  exact ((Iso.inv_comp_eq _).1 (isoSpec_inv_ι_structure K (isAffineOpen_U C hc))).symm

/-- **[LocAn] Cor. 15.5, base change of `Π`** (PI1TOP's I3 at the points `bcExtPt`): for an
affine hyperbolic curve `U` over a number field `K` and any extension `L ⊇ K`,
`Π_{U_L} = Π_U ×_{G_K} G_L` via `(bcExtPiU, bcExtPiG)`. -/
theorem isFibrePres_bcExt (C : HypCurve K) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (gp : GeomPt Ω C) :
    IsFibrePres (bcExtPiU (Ω' := Ω') L C gp) (bcExtPiG L C gp)
      (fundamentalGroupMap C.toSpec gp.over) (resGL L Ω Ω') :=
  isFibrePres_bcExt_of L C (isAffineOpen_U C hc).isoSpec (isoSpec_strSpecR C hc) gp
    (existsUnique_baseExtension_hypCurve C hc L Ω Ω')

omit [NumberField K] [Algebra L Ω'] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω']
  [IsScalarTower K L Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic L Ω'] in
/-- An isomorphism over `G_K` commutes with the projections `π₁ᵉᵗ(U_i) → π₁ᵉᵗ(Spec K)`. -/
lemma fundamentalGroupMap_toSpec_of_isOverGk [CharZero K] {C₁ C₂ : HypCurve K}
    {gp₁ : GeomPt Ω C₁} {gp₂ : GeomPt Ω C₂} {φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x)}
    (hφ : IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x))) (a : π₁ᵉᵗ(gp₁.x)) :
    fundamentalGroupMap C₂.toSpec gp₂.over (φ a) = fundamentalGroupMap C₁.toSpec gp₁.over a := by
  have h := DFunLike.congr_fun hφ a
  exact (mulEquivAutFiber K Ω).symm.injective h

/-- **The base change `φ_L : Π_{U₁,L} ≃ Π_{U₂,L}` over `G_L`** of an isomorphism
`φ : Π_{U₁} ≃ Π_{U₂}` over `G_K` ([LocAn] Cor. 15.5, proof, l.4344–4350: `φ ×_{G_K} G_L` on
`Π_{U_i,L} = Π_{U_i} ×_{G_K} G_L`). -/
def bcExtPhi {C₁ C₂ : HypCurve K} (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
    (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty) {gp₁ : GeomPt Ω C₁} {gp₂ : GeomPt Ω C₂}
    (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x))
    (hφ : IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x))) :
    π₁ᵉᵗ((bcExtPt L Ω' gp₁).x) ≃ₜ* π₁ᵉᵗ((bcExtPt L Ω' gp₂).x) :=
  IsFibrePres.liftEquiv (isFibrePres_bcExt L C₂ hc₂ gp₂) (isFibrePres_bcExt L C₁ hc₁ gp₁) φ
    (fundamentalGroupMap_toSpec_of_isOverGk hφ)

/-- `φ_L` lies over `φ`: `Π_{U₂,L} → Π_{U₂}` sends `φ_L γ` to `φ` of the image of `γ`. -/
lemma bcExtPiU_bcExtPhi {C₁ C₂ : HypCurve K} (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
    (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty) {gp₁ : GeomPt Ω C₁} {gp₂ : GeomPt Ω C₂}
    (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x))
    (hφ : IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x))) (γ) :
    bcExtPiU L C₂ gp₂ (bcExtPhi (Ω' := Ω') L hc₁ hc₂ φ hφ γ) = φ (bcExtPiU L C₁ gp₁ γ) :=
  IsFibrePres.a_liftEquiv _ _ _ _ γ

/-- **`φ_L` lies over `G_L`.** -/
theorem isOverGk_bcExtPhi [CharZero L] {C₁ C₂ : HypCurve K} (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
    (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty) {gp₁ : GeomPt Ω C₁} {gp₂ : GeomPt Ω C₂}
    (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x))
    (hφ : IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x))) :
    IsOverGk (bcExtPt L Ω' gp₁) (bcExtPt L Ω' gp₂)
      (bcExtPhi (Ω' := Ω') L hc₁ hc₂ φ hφ :
        π₁ᵉᵗ((bcExtPt L Ω' gp₁).x) →ₜ* π₁ᵉᵗ((bcExtPt L Ω' gp₂).x)) := by
  refine MonoidHom.ext fun γ ↦ ?_
  change (mulEquivAutFiber L Ω').symm
      (bcExtPiG L C₂ gp₂ (bcExtPhi (Ω' := Ω') L hc₁ hc₂ φ hφ γ)) =
    (mulEquivAutFiber L Ω').symm (bcExtPiG L C₁ gp₁ γ)
  exact congrArg _ (IsFibrePres.b_liftEquiv _ _ _ _ γ)

end Iso

/-! ### The descent debt and the refinement of `DescentNF` -/

section Debt

open Belyi Belyi.Anabelian HypCurve FiniteEtale CurvesJacobian.Cusp

/-- **Debt S1(iii), Galois descent of isomorphisms** (recorded in `MR7-plan.md`; [LocAn]
Cor. 15.5, l.4350–4370): for affine hyperbolic curves `U₁, U₂` over a number field `K`, an
extension `L ⊇ K`, algebraic closures `Ω ⊆ Ω'` of `K ⊆ L` and an isomorphism `φ : Π_{U₁} ≃ Π_{U₂}`
over `G_K`: if the base change `φ_L` (`bcExtPhi`) is induced by an `L`-isomorphism
`U₁,L ≅ U₂,L`, then `φ` is induced by a `K`-isomorphism `U₁ ≅ U₂`. The proof needs the finiteness
of `Isom(U₁,K̄, U₂,K̄)`, its invariance under `K̄ ⊆ L̄`, and Galois descent with the uniqueness
over number fields (`innerRigid`). -/
def DescentIso : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [Algebra K L]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Ω' : Type u) [Field Ω'] [Algebra L Ω'] [IsAlgClosure L Ω'] [Algebra Ω Ω'] [Algebra K Ω']
    [IsScalarTower K Ω Ω'] [IsScalarTower K L Ω'],
    haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
    haveI := IsAlgClosure.isAlgClosed (R := L) (K := Ω')
    haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    ∀ (C₁ C₂ : HypCurve K) (hc₁ : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty)
      (hc₂ : (C₂.U : Set C₂.Xbar)ᶜ.Nonempty) (gp₁ : GeomPt Ω C₁) (gp₂ : GeomPt Ω C₂)
      (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x))
      (hφ : IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x))),
      (∃ f : KIso (C₁.bcExt L) (C₂.bcExt L),
        InducedBy (bcExtPt L Ω' gp₁) (bcExtPt L Ω' gp₂) f (bcExtPhi L hc₁ hc₂ φ hφ)) →
      ∃ f : KIso C₁ C₂, InducedBy gp₁ gp₂ f φ

/-- **Debt S1, curves without cusps** (recorded in `MR7-plan.md`): the statement of
`DescentNF p` for pairs of curves of which at least one is proper. This needs the fibre product
`Π_{X_L} = Π_X ×_{G_K} G_L` for proper `X` (PI1TOP open item (2): filling of the cusps plus
`HomotopyExactQcqs`) in addition to `DescentIso`'s inputs. -/
def DescentNFProper (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [Algebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra K L],
    @RelIsomDGC.Exists L _ (charZero_of_padic p L) →
    ∀ (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω],
    haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
    ∀ (C₁ C₂ : HypCurve K),
      ¬ ((C₁.U : Set C₁.Xbar)ᶜ.Nonempty ∧ (C₂.U : Set C₂.Xbar)ᶜ.Nonempty) →
      ∀ (gp₁ : GeomPt Ω C₁) (gp₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(gp₁.x) ≃ₜ* π₁ᵉᵗ(gp₂.x)),
      IsOverGk gp₁ gp₂ (φ : π₁ᵉᵗ(gp₁.x) →ₜ* π₁ᵉᵗ(gp₂.x)) → ∃ f : KIso C₁ C₂, InducedBy gp₁ gp₂ f φ

/-- **Refinement of the debt `DescentNF`**: for affine curves, the descent from a finite
extension `L` of `ℚ_p` to the number field `K` follows from the base change of `Π`
(`bcExtPhi`, PI1TOP's I3, proved) and the Galois-descent debt `DescentIso`; the proper case is
`DescentNFProper`. -/
theorem descentNF_of_descentIso (p : ℕ) [Fact p.Prime] (hD : DescentIso.{u})
    (hP : DescentNFProper.{u} p) : DescentNF.{u} p := by
  intro K _ _ L _ _ _ _ hL Ω _ _ _ C₁ C₂ gp₁ gp₂ φ hφ
  by_cases hc : (C₁.U : Set C₁.Xbar)ᶜ.Nonempty ∧ (C₂.U : Set C₂.Xbar)ᶜ.Nonempty
  swap
  · exact hP K L hL Ω C₁ C₂ hc gp₁ gp₂ φ hφ
  haveI := IsAlgClosure.isAlgClosed (R := K) (K := Ω)
  haveI : CharZero L := charZero_of_padic p L
  let ι : Ω →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra Ω (AlgebraicClosure L) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω (AlgebraicClosure L) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  obtain ⟨fL, hfL⟩ := hL (AlgebraicClosure L) (C₁.bcExt L) (C₂.bcExt L)
    (bcExtPt L (AlgebraicClosure L) gp₁) (bcExtPt L (AlgebraicClosure L) gp₂)
    (bcExtPhi L hc.1 hc.2 φ hφ) (isOverGk_bcExtPhi L hc.1 hc.2 φ hφ)
  exact hD K L Ω (AlgebraicClosure L) C₁ C₂ hc.1 hc.2 gp₁ gp₂ φ hφ ⟨fL, hfL⟩

end Debt

end CurvesJacobian.LocAn
