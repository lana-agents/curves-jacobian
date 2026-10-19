/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CuspTerminal

/-!
# Connected covers with a prescribed open image (not necessarily normal)

Galois correspondence for `π₁ᵉᵗ` (Stacks 0BN4) for an arbitrary open subgroup: for an open
subgroup `O` of `π₁ᵉᵗ(U, η')` there are a connected finite étale `p : Y ⟶ U` and a geometric point
`ζ` of `Y` over `η'` such that the image of `π₁ᵉᵗ(Y, ζ) → π₁ᵉᵗ(U, η')` is `O`
(`CurvesJacobian.Cusp.exists_isFiniteEtale_range_eq_of_open`). For normal `O` every point over
`η'` works (`CurvesJacobian.Cusp.exists_isFiniteEtale_range_eq`); in general the point matters
(the images at the other points are the conjugates of `O`).
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory

universe u

noncomputable section

namespace CurvesJacobian.Cusp

variable {U : Scheme.{u}} [ConnectedSpace U] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η' : Spec (.of Ω) ⟶ U)

/-- **Connected covers with prescribed open image**: for an open subgroup `O` of
`π₁ᵉᵗ(U, η')` there is a connected finite étale `p : Y ⟶ U` and a point `ζ` of `Y` over `η'` such
that the image of `π₁ᵉᵗ(Y, ζ) → π₁ᵉᵗ(U, η')` is `O`. -/
theorem exists_isFiniteEtale_range_eq_of_open (O : OpenSubgroup π₁ᵉᵗ(η')) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ U) (_ : IsFiniteEtale p) (ζ : Spec (.of Ω) ⟶ Y)
      (h : ζ ≫ p = η'), ConnectedSpace Y ∧
        (fundamentalGroupMap p h).toMonoidHom.range = (O : Subgroup π₁ᵉᵗ(η')) := by
  let F' : FiniteEtale U ⥤ FintypeCat.{u + 1} := fiber η' ⋙ FintypeCat.uSwitch.{u, u + 1}
  letI : FiberFunctor F' := FiberFunctor.comp_right _
  let f : π₁ᵉᵗ(η') ≃ₜ* Aut F' :=
    autEquivAutWhiskerRight (fiber η') FintypeCat.uSwitchEquivalence.{u, u + 1}.fullyFaithfulFunctor
  let O₁ : Subgroup (Aut F') := (O : Subgroup π₁ᵉᵗ(η')).map f.toMulEquiv.toMonoidHom
  have hO₁ : IsOpen (O₁ : Set (Aut F')) := by
    rw [Subgroup.coe_map]
    exact f.toHomeomorph.isOpenMap _ O.isOpen
  obtain ⟨A, ⟨e⟩⟩ := exists_lift_of_quotient_openSubgroup (F := F') ⟨O₁, hO₁⟩
  let x : (fiber η').obj A :=
    FintypeCat.uSwitchEquiv.{u, u + 1} _ (e.inv.hom (QuotientGroup.mk 1))
  obtain ⟨B, i, y, hy, hB, hi⟩ := fiber_in_connected_component (fiber η') A x
  have hinj : Function.Injective ((fiber η').map i) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 inferInstance
  have hpB : IsFiniteEtale B.hom := B.2
  let ζ : Spec (.of Ω) ⟶ B.left := (fiberObjEquivHom η' B y).left
  have hζ : ζ ≫ B.hom = η' := w_left _
  refine ⟨B.left, B.hom, hpB, ζ, hζ, (isConnected_iff_connectedSpace B).1 hB, ?_⟩
  rw [@range_fundamentalGroupMap_of_isFiniteEtale' U B.left B.hom hpB Ω _ _ ζ η' hζ]
  have hz : coverPt B.hom ζ hζ = y := by
    change (fiberObjEquivHom η' B).symm (Over.homMk ζ hζ) = y
    rw [Equiv.symm_apply_eq]
    exact (Over.OverMorphism.ext rfl : Over.homMk ζ hζ = fiberObjEquivHom η' B y)
  ext γ
  rw [MulAction.mem_stabilizer_iff]
  let z : (fiber η').obj B := coverPt B.hom ζ hζ
  change γ • z = z ↔ _
  have hz' : z = y := hz
  rw [hz', ← hinj.eq_iff]
  have hnat : (fiber η').map i (γ • y) = γ • (fiber η').map i y :=
    (NatTrans.naturality_apply γ.hom i y).symm
  rw [hnat, hy]
  let e' : (fiber η').obj A ≃ F'.obj A :=
    (FintypeCat.uSwitchEquiv.{u, u + 1} ((fiber η').obj A)).symm
  have key : ∀ w : (fiber η').obj A, γ • w = w ↔ f γ • e' w = e' w := by
    intro w
    rw [← e'.symm.injective.eq_iff, Equiv.symm_apply_apply]
    change _ ↔ FintypeCat.uSwitchEquiv.{u, u + 1} _
      (FintypeCat.uSwitch.map (γ.hom.app A) ((FintypeCat.uSwitchEquiv.{u, u + 1} _).symm w)) = _
    rw [← FintypeCat.uSwitchEquiv_naturality, Equiv.apply_symm_apply]
    rfl
  rw [key]
  have hinjE : Function.Injective e.hom.hom := fun a b hab ↦ by
    have h1 := FintypeCat.hom_inv_id_apply ((Action.forget _ _).mapIso e) a
    have h2 := FintypeCat.hom_inv_id_apply ((Action.forget _ _).mapIso e) b
    rw [← h1, ← h2]
    exact congrArg _ hab
  have hw : e' x = e.inv.hom (QuotientGroup.mk 1) := Equiv.symm_apply_apply _ _
  have hw' : e.hom.hom (e' x) = (QuotientGroup.mk 1 : Aut F' ⧸ O₁) := by
    rw [hw]
    exact FintypeCat.inv_hom_id_apply ((Action.forget _ _).mapIso e) _
  have hcomm : e.hom.hom (f γ • e' x) = f γ • e.hom.hom (e' x) :=
    ConcreteCategory.congr_hom (e.hom.comm (f γ)) (e' x)
  refine (hinjE.eq_iff (a := f γ • e' x) (b := e' x)).symm.trans ?_
  rw [hcomm, hw']
  change (f γ • ((1 : Aut F') : Aut F' ⧸ O₁) = ((1 : Aut F') : Aut F' ⧸ O₁)) ↔ _
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, mul_one, inv_mem_iff,
    ← Subgroup.mem_map_iff_mem (f := f.toMulEquiv.toMonoidHom) f.injective
      (K := (O : Subgroup π₁ᵉᵗ(η')))]
  rfl

end CurvesJacobian.Cusp
