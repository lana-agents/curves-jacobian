/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Galois.GaloisObjects
import CurvesJacobian.Cusp.CoverOpen

/-!
# A connected object with normal stabiliser is Galois

For a Galois category `C` with fibre functor `F`, a connected object `A` and a point
`a : F.obj A` whose stabiliser in `Aut F` is normal, `A` is Galois
(`CurvesJacobian.Cusp.isGalois_of_stabilizer_normal₂`). This is the converse of Mathlib's
`PreGaloisCategory.stabilizer_normal_of_isGalois`.

Proof: for `b = γ • a`, normality makes `g • a ↦ (g * γ) • a` a well-defined `Aut F`-equivariant
bijection of `F.obj A`; since `functorToAction F` is fully faithful it lifts to an automorphism
of `A` sending `a` to `b`, so `Aut A` acts transitively (`isGalois_iff_pretransitive`).

Specialisation: for a connected finite étale cover `f : V ⟶ U` of a connected scheme, if the
image of `π₁ᵉᵗ(V) → π₁ᵉᵗ(U)` is normal, then `coverObj f` is Galois
(`CurvesJacobian.Cusp.isGalois_coverObj_of_normal_range`).
-/

open CategoryTheory PreGaloisCategory

universe u

namespace CurvesJacobian.Cusp

section Abstract

variable {C : Type*} [Category* C] [GaloisCategory C] (F : C ⥤ FintypeCat.{u})
  [FiberFunctor F] {A : C} (a : F.obj A)

omit [GaloisCategory C] [FiberFunctor F] in
/-- With normal stabiliser, `g • a = g' • a` implies `(g * γ) • a = (g' * γ) • a`. -/
lemma mul_smul_eq_of_stabilizer_normal₂ (hN : (MulAction.stabilizer (Aut F) a).Normal)
    (γ : Aut F) {g g' : Aut F} (h : g • a = g' • a) : (g * γ) • a = (g' * γ) • a := by
  have hm : g⁻¹ * g' ∈ MulAction.stabilizer (Aut F) a := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul]
  have hc : γ⁻¹ * (g⁻¹ * g') * γ ∈ MulAction.stabilizer (Aut F) a := by
    have := hN.conj_mem _ hm γ⁻¹
    rwa [inv_inv] at this
  have e : g' * γ = (g * γ) * (γ⁻¹ * (g⁻¹ * g') * γ) := by group
  rw [e, mul_smul (g * γ) _ a, MulAction.mem_stabilizer_iff.mp hc]

/-- The equivariant bijection `g • a ↦ (g * γ) • a` of `F.obj A` (for a normal stabiliser). -/
noncomputable def rightTransl₂ [IsConnected A] (γ : Aut F) : F.obj A → F.obj A :=
  fun y ↦ (Classical.choose (MulAction.exists_smul_eq (Aut F) a y) * γ) • a

lemma rightTransl₂_smul [IsConnected A] (hN : (MulAction.stabilizer (Aut F) a).Normal)
    (γ g : Aut F) : rightTransl₂ F a γ (g • a) = (g * γ) • a :=
  mul_smul_eq_of_stabilizer_normal₂ F a hN γ
    (Classical.choose_spec (MulAction.exists_smul_eq (Aut F) a (g • a)))

/-- The equivalence version of `rightTransl₂`. -/
noncomputable def rightTranslEquiv₂ [IsConnected A]
    (hN : (MulAction.stabilizer (Aut F) a).Normal) (γ : Aut F) : F.obj A ≃ F.obj A where
  toFun := rightTransl₂ F a γ
  invFun := rightTransl₂ F a γ⁻¹
  left_inv y := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Aut F) a y
    rw [rightTransl₂_smul F a hN, rightTransl₂_smul F a hN, mul_inv_cancel_right]
  right_inv y := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Aut F) a y
    rw [rightTransl₂_smul F a hN, rightTransl₂_smul F a hN, inv_mul_cancel_right]

lemma rightTransl₂_equivariant [IsConnected A] (hN : (MulAction.stabilizer (Aut F) a).Normal)
    (γ σ : Aut F) (y : F.obj A) : rightTransl₂ F a γ (σ • y) = σ • rightTransl₂ F a γ y := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Aut F) a y
  rw [← mul_smul, rightTransl₂_smul F a hN, rightTransl₂_smul F a hN, mul_assoc, mul_smul]

/-- `rightTranslEquiv₂` as an automorphism of the finite `Aut F`-set `F.obj A`. -/
noncomputable def rightTranslActionIso₂ [IsConnected A]
    (hN : (MulAction.stabilizer (Aut F) a).Normal) (γ : Aut F) :
    (functorToAction F).obj A ≅ (functorToAction F).obj A :=
  Action.mkIso (FintypeCat.equivEquivIso (rightTranslEquiv₂ F a hN γ)) (fun σ ↦ by
    ext y
    exact rightTransl₂_equivariant F a hN γ σ y)

/-- The automorphism of `A` lifting `rightTransl₂`. -/
noncomputable def rightTranslAut₂ [IsConnected A]
    (hN : (MulAction.stabilizer (Aut F) a).Normal) (γ : Aut F) : A ≅ A :=
  (Functor.FullyFaithful.ofFullyFaithful (functorToAction F)).preimageIso
    (rightTranslActionIso₂ F a hN γ)

lemma map_rightTranslAut₂_hom [IsConnected A] (hN : (MulAction.stabilizer (Aut F) a).Normal)
    (γ : Aut F) : F.map (rightTranslAut₂ F a hN γ).hom a = γ • a := by
  have h1 : (functorToAction F).map (rightTranslAut₂ F a hN γ).hom =
      (rightTranslActionIso₂ F a hN γ).hom :=
    Functor.FullyFaithful.map_preimage (Functor.FullyFaithful.ofFullyFaithful (functorToAction F))
      (rightTranslActionIso₂ F a hN γ).hom
  have h2 : F.map (rightTranslAut₂ F a hN γ).hom a = rightTransl₂ F a γ a :=
    ConcreteCategory.congr_hom (congrArg Action.Hom.hom h1) a
  have h3 : rightTransl₂ F a γ ((1 : Aut F) • a) = ((1 : Aut F) * γ) • a :=
    rightTransl₂_smul F a hN γ 1
  rw [one_smul, one_mul] at h3
  exact h2.trans h3

/-- **A connected object with a normal stabiliser is Galois** (converse of
`PreGaloisCategory.stabilizer_normal_of_isGalois`). -/
theorem isGalois_of_stabilizer_normal₂ (A : C) [IsConnected A] (a : F.obj A)
    (hN : (MulAction.stabilizer (Aut F) a).Normal) : IsGalois A := by
  have hb : ∀ b : F.obj A, ∃ φ : Aut A, φ • a = b := by
    intro b
    obtain ⟨γ, rfl⟩ := MulAction.exists_smul_eq (Aut F) a b
    exact ⟨rightTranslAut₂ F a hN γ, map_rightTranslAut₂_hom F a hN γ⟩
  rw [isGalois_iff_pretransitive F]
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := hb x
  obtain ⟨ψ, rfl⟩ := hb y
  exact ⟨ψ * φ⁻¹, by rw [mul_smul, inv_smul_smul]⟩

end Abstract

section Schemes

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

/-- **A connected finite étale cover with normal image of `π₁ᵉᵗ` is Galois.** For
`f : V ⟶ U` finite étale between connected schemes and a geometric point `η` of `V` over `η'`,
if the image of `π₁ᵉᵗ(V, η) → π₁ᵉᵗ(U, η')` is normal, then `coverObj f` is a Galois object. -/
theorem isGalois_coverObj_of_normal_range {U V : Scheme.{u}} [ConnectedSpace U] {f : V ⟶ U}
    [IsFiniteEtale f] [ConnectedSpace V] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ V) {η' : Spec (.of Ω) ⟶ U} (h : η ≫ f = η')
    (hN : (fundamentalGroupMap f h).toMonoidHom.range.Normal) : IsGalois (coverObj f) := by
  haveI : IsConnected (coverObj f) :=
    (FiniteEtale.isConnected_iff_connectedSpace (coverObj f)).mpr ‹ConnectedSpace V›
  rw [range_fundamentalGroupMap_of_isFiniteEtale' f η h] at hN
  exact isGalois_of_stabilizer_normal₂ (fiber η') (coverObj f) (coverPt f η h) hN

end Schemes

end CurvesJacobian.Cusp
