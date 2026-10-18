/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.TwistCech
import CurvesJacobian.Picard.RationalPointAlgebra
import CurvesJacobian.Picard.ChartFibre
import CurvesJacobian.Picard.RelEffCartierSection

/-!
# Rational points of a curve avoiding a section (input to Stacks, Lemma 44.6.5, Tag 0B9Y)

Let `C` be a curve over an algebraically closed field `k`, `W ⊆ C` a nonempty affine open,
`K` a field over `k` and `X_K = C ×_k K`. For a `k`-point `x : Spec k → C` (a section of
`C → Spec k`), `σ_x = secT x : T → X_K` is its base change.

* `CurvesJacobian.pointOf`: the `k`-point of `C` in `W` defined by a ring map
  `Γ(C, W) → k`; `CurvesJacobian.appLE_pointOf`: its pullback on `Γ(C, W)` is that map.
* `CurvesJacobian.exists_point_appLE_ne_zero` (**density of `C(k)`**): every nonzero function
  `a` on `W_K = W ×_k K` is nonzero at `σ_x` for some `k`-point `x ∈ W` (Nullstellensatz for
  `Γ(C, W)` and a `k`-basis of `K`).
* `CurvesJacobian.ker_secT_eq_comap`: the ideal of `σ_x(T) ⊂ X_K` is the pullback of the
  ideal of `x(Spec k) ⊂ C ×_k k` (the square `σ_x`, `x` is cartesian), so the divisors of `σ_x`
  and `x` have compatible line bundles (`CurvesJacobian.map_picClass_ofSection`).
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite Function TensorProduct

universe u

noncomputable section

namespace CurvesJacobian

open Belyi Cech

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]

local notation "Sk" => Spec (CommRingCat.of k)

section Point

variable {W : C.Opens} (hW : IsAffineOpen W) (x : Γ(C, W) ⟶ CommRingCat.of k)

/-- The point of `C` in `W` defined by a ring map `Γ(C, W) → k`. -/
def pointOf : Sk ⟶ C := Spec.map x ≫ hW.fromSpec

omit [C.Over Sk] in
lemma le_preimage_pointOf : ⊤ ≤ pointOf C hW x ⁻¹ᵁ W := by
  rw [pointOf, Scheme.Hom.comp_preimage, hW.fromSpec_preimage_self]
  exact le_rfl

omit [C.Over Sk] in
lemma appLE_pointOf :
    (pointOf C hW x).appLE W ⊤ (le_preimage_pointOf C hW x) = x ≫ (Scheme.ΓSpecIso _).inv := by
  suffices H : ∀ (f : Sk ⟶ C) (_ : f = Spec.map x ≫ hW.fromSpec) (hf : ⊤ ≤ f ⁻¹ᵁ W),
      f.appLE W ⊤ hf = x ≫ (Scheme.ΓSpecIso _).inv from H _ rfl _
  rintro f rfl hf
  rw [Scheme.Hom.comp_appLE, hW.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE,
    Scheme.ΓSpecIso_inv_naturality]
  congr 1

end Point

section Density

/-- `Γ(Spec k)` is algebraically closed if `k` is. -/
lemma isAlgClosed_ΓSpec [IsAlgClosed k] :
    letI : Field Γ(Sk, ⊤) := isField_ΓSpec.toField
    IsAlgClosed Γ(Sk, ⊤) :=
  letI : Field Γ(Sk, ⊤) := isField_ΓSpec.toField
  IsAlgClosed.of_ringEquiv k _ (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv

variable [PerfectField k] [IsCurveOver k C]


variable {T : Scheme.{u}} [IsAffine T] [T.Over (Spec (CommRingCat.of k))]

omit [PerfectField k] [IsCurveOver k C] in
/-- The base change of a `k`-point to `X_K`, evaluated on functions pulled back from `C ×_k K`:
for `t = λ ⊗ r ∈ Γ(K) ⊗ Γ(C, W)`, `σ_x^♯ (λ r) = λ x(r)`. -/
lemma appLE_secT_sectionsBaseChange (W : C.Opens) (hW : IsAffineOpen W)
    (x₀ : Γ(C, W) →ₐ[Γ(Sk, ⊤)] Γ(Sk, ⊤)) (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk)
    (hxW : ⊤ ≤ xC ⁻¹ᵁ W) (hxa : xC.appLE W ⊤ hxW = CommRingCat.ofHom x₀.toRingHom)
    (h : ⊤ ≤ secT (C ↘ Sk) xC hx (T ↘ Sk) ⁻¹ᵁ (pullback.fst (C ↘ Sk) (T ↘ Sk) ⁻¹ᵁ W))
    (hF : IsField Γ(T, ⊤)) :
    letI : Field Γ(Sk, ⊤) := isField_ΓSpec.toField
    letI : Field Γ(T, ⊤) := hF.toField
    ∀ t : Γ(T, ⊤) ⊗[Γ(Sk, ⊤)] Γ(C, W),
      (secT (C ↘ Sk) xC hx (T ↘ Sk)).appLE (pullback.fst (C ↘ Sk) (T ↘ Sk) ⁻¹ᵁ W) ⊤ h
        (sectionsBaseChangeAlgEquiv (T₀ := T) W hW _ rfl t) = evalTensor x₀ t := by
  letI : Field Γ(Sk, ⊤) := isField_ΓSpec.toField
  letI : Field Γ(T, ⊤) := hF.toField
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | tmul l r =>
    rw [sectionsBaseChangeAlgEquiv_tmul, map_mul, evalTensor_tmul, Algebra.smul_def, mul_comm]
    congr 1
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
        appLE_eq_of_eq (secT_fst _ _ _ _), ← Scheme.Hom.appLE_comp_appLE (V := ⊤) (e₁ := hxW)
          (e₂ := le_top), CommRingCat.comp_apply, hxa]
      rfl
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
        appLE_eq_of_eq (secT_snd _ _ _ _)]
      simp [Scheme.Hom.appLE]

variable [IsAlgClosed k]

omit [PerfectField k] in
/-- **Density of rational points** (proof of Stacks, Lemma 44.6.5, Tag 0B9Y): a nonzero
function on `W_K` is nonzero at the base change of some `k`-point of `W`. -/
theorem exists_point_appLE_ne_zero (hF : IsField Γ(T, ⊤)) (W : C.Opens)
    (hW : IsAffineOpen W) [Nonempty W]
    (a : (pullback (C ↘ Sk) (T ↘ Sk)).presheaf.obj (op (pullback.fst (C ↘ Sk) (T ↘ Sk) ⁻¹ᵁ W)))
    (ha : a ≠ 0) :
    ∃ (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk) (_ : ⊤ ≤ xC ⁻¹ᵁ W)
      (h : ⊤ ≤ secT (C ↘ Sk) xC hx (T ↘ Sk) ⁻¹ᵁ (pullback.fst (C ↘ Sk) (T ↘ Sk) ⁻¹ᵁ W)),
      (secT (C ↘ Sk) xC hx (T ↘ Sk)).appLE (pullback.fst (C ↘ Sk) (T ↘ Sk) ⁻¹ᵁ W) ⊤ h a ≠ 0 := by
  letI : Field Γ(Sk, ⊤) := isField_ΓSpec.toField
  letI : Field Γ(T, ⊤) := hF.toField
  haveI := isAlgClosed_ΓSpec (k := k)
  haveI : IsIntegral C := IsCurveOver.isIntegral k C
  haveI : Algebra.FiniteType Γ(Sk, ⊤) Γ(C, W) := by
    have := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (C ↘ Sk) inferInstance
      ⟨⊤, isAffineOpen_top Sk⟩ ⟨W, hW⟩ (by simp)
    exact this
  let ψ := sectionsBaseChangeAlgEquiv (T₀ := T) W hW
    (pullback.fst (C ↘ Sk) (T ↘ Sk) ⁻¹ᵁ W) rfl
  have ht : ψ.symm a ≠ 0 := by
    intro h0; apply ha
    rw [← ψ.apply_symm_apply a, h0, map_zero]
  obtain ⟨x₀, hx₀⟩ := exists_algHom_evalTensor_ne_zero (k := Γ(Sk, ⊤)) ht
  let x : Γ(C, W) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom x₀.toRingHom ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom
  let xC := pointOf C hW x
  have hxW := le_preimage_pointOf C hW x
  have hxa : xC.appLE W ⊤ hxW = CommRingCat.ofHom x₀.toRingHom := by
    rw [appLE_pointOf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hx : xC ≫ (C ↘ Sk) = 𝟙 Sk := by
    refine ext_of_isAffine ?_
    have e1 : (xC ≫ (C ↘ Sk)).appLE ⊤ ⊤ (by simp) = 𝟙 _ := by
      rw [← Scheme.Hom.appLE_comp_appLE (V := W) (e₁ := by simp) (e₂ := hxW), hxa]
      ext a
      exact x₀.commutes a
    rw [Scheme.Hom.id_appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact e1
  have h : ⊤ ≤ secT (C ↘ Sk) xC hx (T ↘ Sk) ⁻¹ᵁ (pullback.fst (C ↘ Sk) (T ↘ Sk) ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, secT_fst, Scheme.Hom.comp_preimage]
    exact le_top.trans ((T ↘ Sk).preimage_mono hxW)
  refine ⟨xC, hx, hxW, h, ?_⟩
  have key := appLE_secT_sectionsBaseChange C W hW x₀ xC hx hxW hxa h hF (ψ.symm a)
  rw [AlgEquiv.apply_symm_apply] at key
  rw [key]
  exact hx₀

end Density

section Kernel

variable [PerfectField k] [IsCurveOver k C]

omit [PerfectField k] in
/-- The image of the base change of a `k`-point is the preimage of the image of the point:
`ker σ_{x,T} = φ⁻¹ ker σ_x` for `φ : C ×_k T → C ×_k k`. -/
theorem ker_secT_eq_comap (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk) {T : Scheme.{u}}
    (g : T ⟶ Sk) :
    (secT (C ↘ Sk) xC hx g).ker = (secT (C ↘ Sk) xC hx (𝟙 Sk)).ker.comap
      (bcMap (C ↘ Sk) g (𝟙 Sk) g (Category.comp_id g)) := by
  haveI := isClosedImmersion_of_section C (𝟙 Sk) (secT (C ↘ Sk) xC hx (𝟙 Sk))
    (secT_snd _ _ _ _)
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hbig : IsPullback g (secT (C ↘ Sk) xC hx g ≫ pullback.snd (C ↘ Sk) g)
      (secT (C ↘ Sk) xC hx (𝟙 Sk) ≫ pullback.snd (C ↘ Sk) (𝟙 Sk)) g := by
    rw [secT_snd, secT_snd]
    exact IsPullback.id_vert g
  have H := (IsPullback.of_bot hbig (secT_bcMap (C ↘ Sk) xC hx g (𝟙 Sk) g
    (Category.comp_id g)).symm (isPullback_bcMap (C ↘ Sk) g (𝟙 Sk) g
      (Category.comp_id g))).flip
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- The line bundles of the divisors of `x` and of its base change `σ_{x,T}` correspond under
pullback. -/
theorem map_picClass_ofSection (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk) {T : Scheme.{u}}
    (g : T ⟶ Sk) :
    Scheme.Pic.map (bcMap (C ↘ Sk) g (𝟙 Sk) g (Category.comp_id g))
        (RelEffCartier.ofSection C (𝟙 Sk) (secT (C ↘ Sk) xC hx (𝟙 Sk))
          (secT_snd _ _ _ _)).picClass =
      (RelEffCartier.ofSection C g (secT (C ↘ Sk) xC hx g) (secT_snd _ _ _ _)).picClass :=
  RelEffCartier.map_picClass_of_ideal_eq
    (RelEffCartier.ofSection C (𝟙 Sk) (secT (C ↘ Sk) xC hx (𝟙 Sk)) (secT_snd _ _ _ _))
    (RelEffCartier.ofSection C g (secT (C ↘ Sk) xC hx g) (secT_snd _ _ _ _))
    (bcMap (C ↘ Sk) g (𝟙 Sk) g (Category.comp_id g)) (by
      rw [RelEffCartier.ofSection_ideal, RelEffCartier.ofSection_ideal, ker_secT_eq_comap])

end Kernel

end CurvesJacobian
