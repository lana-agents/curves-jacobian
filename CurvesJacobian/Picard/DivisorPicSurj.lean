/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.DivisorPic
import CurvesJacobian.Picard.PicDegreeAdd
import CurvesJacobian.Picard.RelEffCartierDegree

/-!
# Surjectivity of the bridge from divisor classes to line bundles

Let `Y` be a curve over a perfect field `κ` (integral). Every locally principal ideal sheaf on
`Y` has a divisor (`CurvesJacobian.exists_hasDiv_of_isLocPrincipal`): the orders of local
generators, which vanish outside the finitely many points where one fixed local generator
vanishes. For the base change `C_κ` of a curve `C/k` to an algebraically closed field `κ`, every
relative effective Cartier divisor is `effDiv C κ E` for an effective `E`, and since every class
in `Pic(C_κ)` is a difference of such (`exists_eq_picClass_sub`) we get (JAC-1b):

* **`CurvesJacobian.divPic_surjective`**, **`picDivPic_surjective`**: `Pic(K(C_κ)) ≃ Pic(C_κ)`;
* `CurvesJacobian.picDivPt_surjective`;
* **`CurvesJacobian.jacBridge_surjective`** and the isomorphism
  **`CurvesJacobian.jacBridgeEquiv : Pic⁰(K(C_κ)) ≃+ J(κ)`**.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Belyi Opposite
open WeilCurves.FunctionField

universe u

noncomputable section

namespace CurvesJacobian

open Scheme

section Generic

variable {κ : Type u} [Field κ] [PerfectField κ] {Y : Scheme.{u}} [Y.Over (Spec (.of κ))]
  [IsCurveOver κ Y] [IsIntegral Y]

/-- Two generators of a locally principal ideal sheaf on affine opens containing the point of
`P` have the same order at `P` (and the second is nonzero if the first is). -/
lemma ordAt_eq_of_ideal_eq_span {I : Y.IdealSheafData} {W W' : Y.affineOpens}
    {g : Γ(Y, W.1)} {g' : Γ(Y, W'.1)} (hI : I.ideal W = Ideal.span {g})
    (hI' : I.ideal W' = Ideal.span {g'}) (hg0 : g ≠ 0) (P : Place κ Y.functionField)
    (hP : pointOfPlace κ Y P ∈ W.1) (hP' : pointOfPlace κ Y P ∈ W'.1) :
    g' ≠ 0 ∧ ordAt P hP' g' = ordAt P hP g := by
  obtain ⟨V, hPV, hVle⟩ := exists_affineOpens_mem_le (O := W.1 ⊓ W'.1) ⟨hP, hP'⟩
  have hVW : V.1 ≤ W.1 := hVle.trans inf_le_left
  have hVW' : V.1 ≤ W'.1 := hVle.trans inf_le_right
  haveI : Nonempty V.1 := ⟨⟨_, hPV⟩⟩
  have h1 : Ideal.span {(Y.presheaf.map (homOfLE hVW').op g' : Γ(Y, V.1))} =
      Ideal.span {(Y.presheaf.map (homOfLE hVW).op g : Γ(Y, V.1))} :=
    (ideal_eq_span_res hVW' hI').symm.trans (ideal_eq_span_res hVW hI)
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h1
  have hgV : Y.presheaf.map (homOfLE hVW).op g ≠ 0 := by
    rw [← algebraMap_germ_ne_zero_iff hPV, Y.presheaf.germ_res_apply]
    exact (algebraMap_germ_ne_zero_iff hP g).2 hg0
  refine ⟨fun h ↦ hgV ?_, ?_⟩
  · rw [← hu, h, map_zero, zero_mul]
  · rw [← ordAt_res P hVW' hPV, ← ordAt_unit_mul P hPV u, hu, ordAt_res]

/-- **Every locally principal ideal sheaf on a curve has an effective divisor**: the order at
`P` of a local generator near the point of `P`. -/
theorem exists_hasDiv_of_isLocPrincipal {I : Y.IdealSheafData} (hI : I.IsLocPrincipal) :
    ∃ E : Divisor κ Y.functionField, 0 ≤ E ∧ I.HasDiv E := by
  choose W g hxW hgI hg using hI
  have hg0 : ∀ x, g x ≠ 0 := fun x ↦
    haveI : Nonempty (W x).1 := ⟨⟨x, hxW x⟩⟩
    ne_zero_of_isSMulRegular (hg x)
  let e : Place κ Y.functionField → ℤ := fun P ↦ ordAt P (hxW (pointOfPlace κ Y P)) (g _)
  set x₀ : Y := genericPoint Y
  haveI : Nonempty (W x₀).1 := ⟨⟨x₀, hxW x₀⟩⟩
  have hη : x₀ ∈ Y.basicOpen (g x₀) := by
    rw [Scheme.mem_basicOpen _ _ _ (genericPoint_mem_of_nonempty (W x₀).1)]
    change IsUnit (Y.germToFunctionField (W x₀).1 (g x₀))
    exact isUnit_iff_ne_zero.2
      ((map_ne_zero_iff _ (Y.germToFunctionField_injective (W x₀).1)).2 (hg0 x₀))
  haveI : Nonempty (Y.basicOpen (g x₀)) := ⟨⟨_, hη⟩⟩
  have hfin : (Function.support e).Finite := by
    refine ((finite_compl_of_nonempty κ Y (Y.basicOpen (g x₀))).preimage
      (pointOfPlace_injective κ Y).injOn).subset fun P hP hPO ↦ hP ?_
    have hPW : pointOfPlace κ Y P ∈ (W x₀).1 := Y.basicOpen_le _ hPO
    change ordAt P (hxW (pointOfPlace κ Y P)) (g _) = 0
    rw [(ordAt_eq_of_ideal_eq_span (hgI x₀) (hgI _) (hg0 x₀) P hPW _).2,
      ordAt_eq_zero_iff_isUnit P hPW (hg0 x₀)]
    exact (Scheme.mem_basicOpen _ _ _ hPW).1 hPO
  refine ⟨Finsupp.ofSupportFinite e hfin, fun P ↦ ordAt_nonneg P _ _,
    IdealSheafData.HasDiv.of_forall_exists fun P ↦
      ⟨W _, g _, hxW _, hgI _, hg0 _, rfl⟩⟩

end Generic

section BaseChange

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
  [IsCurveOver k C] (κ : Type u) [Field κ] [IsAlgClosed κ] [Algebra k κ]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "Cκ" => pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) κ)

variable {C κ} in
/-- **Every relative effective Cartier divisor on `C_κ` is `∑ E(P) x_P`** for an effective
divisor `E` (the divisor of its ideal sheaf). -/
theorem exists_eq_effDiv
    (D : RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) κ))) :
    ∃ E : Divisor κ (Cκ).functionField, 0 ≤ E ∧ D.ideal.HasDiv E ∧ D = effDiv C κ E := by
  obtain ⟨E, hE, hD⟩ := exists_hasDiv_of_isLocPrincipal (κ := κ) D.locally_principal
  exact ⟨E, hE, hD, RelEffCartier.ext_ideal (IdealSheafData.HasDiv.eq hD
    (hasDiv_effDiv C κ hE) D.locally_principal (effDiv C κ E).locally_principal)⟩

variable {C κ} in
/-- The class of a relative effective Cartier divisor on `C_κ` is in the image of `divPic`. -/
theorem exists_picClass_eq_divPic
    (D : RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) κ))) :
    ∃ E : Divisor κ (Cκ).functionField, 0 ≤ E ∧ D.ideal.HasDiv E ∧
      D.picClass = divPic C κ E := by
  obtain ⟨E, hE, hD, rfl⟩ := exists_eq_effDiv D
  exact ⟨E, hE, hD, picClass_effDiv C κ hE⟩

/-- **`Div(K(C_κ)) → Pic(C_κ)` is surjective.** -/
theorem divPic_surjective : Function.Surjective (divPic (k := k) C κ) := by
  letI : (Spec (CommRingCat.of κ)).Over Sk := ⟨specAlgebraMap (k₀ := k) κ⟩
  intro z
  obtain ⟨D, E, rfl⟩ := exists_eq_picClass_sub (curveToP1 k C) (T := Spec (.of κ))
    (isField_ΓSpec' κ) z
  obtain ⟨F, -, -, hF⟩ := exists_picClass_eq_divPic D
  obtain ⟨G, -, -, hG⟩ := exists_picClass_eq_divPic E
  exact ⟨F - G, by rw [map_sub, ← hF, ← hG]; rfl⟩

/-- **`Pic(K(C_κ)) → Pic(C_κ)` is surjective** (hence bijective, `picDivPic_injective`). -/
theorem picDivPic_surjective : Function.Surjective (picDivPic (k := k) C κ) := fun z ↦
  let ⟨E, hE⟩ := divPic_surjective C κ z
  ⟨QuotientAddGroup.mk E, hE⟩

/-- `Pic(K(C_κ)) ≃+ Pic(C_κ)`. -/
def picDivPicEquiv : Pic κ (Cκ).functionField ≃+ (Cκ).Pic :=
  AddEquiv.ofBijective (picDivPic C κ) ⟨picDivPic_injective C κ, picDivPic_surjective C κ⟩

variable (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- `Pic(K(C_κ)) → Pic_{C/k,σ}(κ)` is surjective. -/
theorem picDivPt_surjective : Function.Surjective (picDivPt C κ σ hσ) := fun z ↦
  let ⟨x, hx⟩ := picDivPic_surjective C κ z.1
  ⟨x, Subtype.ext hx⟩

/-- **The bridge `Pic⁰(K(C_κ)) → J(κ)` is surjective.** -/
theorem jacBridge_surjective : Function.Surjective (jacBridge C κ σ hσ) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx⟩ := picDivPt_surjective C κ σ hσ z
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hdeg : Pic.deg κ (Cκ).functionField (QuotientAddGroup.mk E) = 0 := by
    have h := (mem_jacPoints_iff_degPic C κ σ hσ z).1 hz
    rw [← hx, coe_picDivPt, picDivPic_mk, degPic_divPic] at h
    exact h
  exact ⟨⟨_, hdeg⟩, Subtype.ext hx⟩

/-- **`Pic⁰(K(C_κ)) ≃+ J(κ)`**: degree-zero divisor classes of the function field are the
`κ`-points of the Jacobian. -/
def jacBridgeEquiv : (Pic.deg κ (Cκ).functionField).ker ≃+ jacPoints C σ hσ κ :=
  AddEquiv.ofBijective (jacBridge C κ σ hσ)
    ⟨jacBridge_injective C κ σ hσ, jacBridge_surjective C κ σ hσ⟩

@[simp]
lemma jacBridgeEquiv_apply (x : (Pic.deg κ (Cκ).functionField).ker) :
    jacBridgeEquiv C κ σ hσ x = jacBridge C κ σ hσ x :=
  rfl

end BaseChange

end CurvesJacobian
