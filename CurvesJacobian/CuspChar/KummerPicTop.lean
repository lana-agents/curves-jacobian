/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.CuspChar.KummerCusp
import CurvesJacobian.Kummer.WeilPairingGalois
import CurvesJacobian.Kummer.WeilGenericPoint
import CurvesJacobian.Kummer.PicDivisible

/-!
# The characters of `π₁ᵉᵗ(U)` unramified at the cusps are `J[n]`

Setting of `CurvesJacobian/CuspChar/KummerCusp.lean`. The characters of `π₁ᵉᵗ(U)` with zero
residues at all cusps form the kernel `A` of the residue map; Kummer theory identifies it with
the `n`-torsion of the divisor class group:

* `CurvesJacobian.CuspChar.picChar : Pic(F)[n] →+ Hom_cont(π₁ᵉᵗ(U), ℤ/n)`, `[E] ↦` the Kummer
  character of `f` with `div f = n E`; it is injective (`picChar_injective`) with image the kernel
  of the residue map (`range_picChar`), giving `CurvesJacobian.CuspChar.picEquivKer`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi Pi1.Orbifold
  KummerTheory Curve AffOrbicurve WeilCurves.FunctionField

universe u

noncomputable section

set_option linter.unusedSectionVars false

namespace CurvesJacobian.CuspChar

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (D : GaloisData k t)
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [IsAlgClosed k] [CharZero k]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] [IsCurveOver k X]
  (eL : X.functionField ≃+* D.L)
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)
  (hH : D.H ≤ D.HL) {τ : X.functionField} (hτ : ((eL τ : D.L) : Ω) = t)
  {U : X.Opens} [Nonempty U] (n : ℕ) [NeZero n] (hU : (U : Set X)ᶜ.Finite)

attribute [local instance] isFunctionField_F

section PicChar

include hH in
/-- Kummer classes (`div f ∈ n · Div`) are unramified over `U`. -/
lemma kummerClasses_le_kumU : kummerClasses k (F D) n ≤ kumU D X eL U n := by
  intro v hv
  rw [mem_kumU, unramU_iff D X eL hH U n]
  intro P _
  exact (mem_nsmulDivisors_div_iff D n _).1 hv P

/-- The Kummer map on Kummer classes. -/
def jHom : kummerClasses k (F D) n →+
    charSpace n (⊤ : OpenSubgroup (PiU D X eL U)) :=
  (kumMap D X eL hk hH hτ n hU).comp
    (AddSubgroup.inclusion (kummerClasses_le_kumU D X eL hH n))

lemma jHom_apply (f : kummerClasses k (F D) n) :
    jHom D X eL hk hH hτ n hU f =
      kumMap D X eL hk hH hτ n hU ⟨f.1, kummerClasses_le_kumU D X eL hH n f.2⟩ :=
  rfl

/-- `n`-th powers. -/
lemma toMul_mem_pow_range {x : Additive (F D)ˣ}
    (hx : x ∈ (nsmulAddMonoidHom (α := Additive (F D)ˣ) n).range) :
    Additive.toMul x ∈ (powMonoidHom n : (F D)ˣ →* (F D)ˣ).range := by
  obtain ⟨w, rfl⟩ := hx
  exact ⟨Additive.toMul w, by simp⟩

lemma kummerTrivial_le_ker_jHom :
    (kummerTrivial k (F D) n).comap (kummerClasses k (F D) n).subtype ≤
      (jHom D X eL hk hH hτ n hU).ker := by
  intro f hf
  rw [AddMonoidHom.mem_ker, jHom_apply, kumMap_eq_zero_iff]
  obtain ⟨c, hc, w, hw, hcw⟩ := AddSubgroup.mem_sup.1 (hf : f.1 ∈ kummerTrivial k (F D) n)
  have hc' := mem_nsmul_range_of_div_eq_zero D n (Nat.pos_of_ne_zero (NeZero.ne n)) c hc
  have : f.1 ∈ (nsmulAddMonoidHom (α := Additive (F D)ˣ) n).range := by
    have h := AddSubgroup.add_mem _ hc' hw
    rwa [hcw, AddSubgroup.coe_subtype] at h
  exact toMul_mem_pow_range D n this

/-- **The Kummer characters of the `n`-torsion divisor classes.** -/
def picChar : picTorsion k (F D) n →+
    charSpace n (⊤ : OpenSubgroup (PiU D X eL U)) :=
  (QuotientAddGroup.lift _ (jHom D X eL hk hH hτ n hU)
    (kummerTrivial_le_ker_jHom D X eL hk hH hτ n hU)).comp
    (picTorsionEquiv (Nat.pos_of_ne_zero (NeZero.ne n))).symm.toAddMonoidHom

lemma picChar_kummerToPic (f : kummerClasses k (F D) n) :
    picChar D X eL hk hH hτ n hU (kummerToPic (Nat.pos_of_ne_zero (NeZero.ne n)) f) =
      jHom D X eL hk hH hτ n hU f := by
  have h : (picTorsionEquiv (Nat.pos_of_ne_zero (NeZero.ne n))).symm
      (kummerToPic (Nat.pos_of_ne_zero (NeZero.ne n)) f) = QuotientAddGroup.mk f :=
    (picTorsionEquiv _).symm_apply_eq.2 rfl
  simp only [picChar, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h,
    QuotientAddGroup.lift_mk]

theorem picChar_injective : Function.Injective (picChar D X eL hk hH hτ n hU) := by
  rw [injective_iff_map_eq_zero]
  refine (kummerToPic_surjective (Nat.pos_of_ne_zero (NeZero.ne n))).forall.2 fun f hx ↦ ?_
  simp only [picChar_kummerToPic, jHom_apply, kumMap_eq_zero_iff] at hx
  obtain ⟨w, hw⟩ := hx
  have hmem : f ∈ (kummerToPic (Nat.pos_of_ne_zero (NeZero.ne n))).ker := by
    rw [ker_kummerToPic]
    refine AddSubgroup.mem_sup_right ⟨Additive.ofMul w, ?_⟩
    apply Additive.toMul.injective
    simpa using hw
  exact hmem

theorem range_picChar :
    (picChar D X eL hk hH hτ n hU).range =
      (LinearMap.ker (resMap D X eL hH n (U := U))).toAddSubgroup := by
  ext e0
  constructor
  · rintro ⟨x, rfl⟩
    revert x
    refine (kummerToPic_surjective (Nat.pos_of_ne_zero (NeZero.ne n))).forall.2 fun f ↦ ?_
    simp only [picChar_kummerToPic, jHom_apply]
    change resMap D X eL hH n _ = 0
    funext c
    simp only [resMap_kumMap, Pi.zero_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2
      ((mem_nsmulDivisors_div_iff D n _).1 f.2 c.1)
  · revert e0
    refine (kumMap_surjective D X eL hk hH hτ n hU).forall.2 fun v he0 ↦ ?_
    have hres : ∀ c : CuspPl D X eL hH U, (n : ℤ) ∣ c.1.ord ((Additive.toMul v.1 : (F D)ˣ) :
        F D) := fun c ↦ by
      have := congrFun (he0 : resMap D X eL hH n (kumMap D X eL hk hH hτ n hU v) = 0) c
      simp only [resMap_kumMap, Pi.zero_apply] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 this
    have hall : ∀ P : Place k (F D), (n : ℤ) ∣ P.ord ((Additive.toMul v.1 : (F D)ˣ) : F D) := by
      intro P
      by_cases hP : IsCentredP D X eL hH U P
      · exact (unramU_iff D X eL hH U n _).1 ((mem_kumU D X eL U n).1 v.2) P hP
      · exact hres ⟨P, hP⟩
    have hv : v.1 ∈ kummerClasses k (F D) n := (mem_nsmulDivisors_div_iff D n _).2 hall
    refine ⟨kummerToPic (Nat.pos_of_ne_zero (NeZero.ne n)) ⟨v.1, hv⟩, ?_⟩
    simp only [picChar_kummerToPic, jHom_apply]

/-- `picChar` with values in the kernel of the residue map. -/
def picToKer : picTorsion k (F D) n →+ LinearMap.ker (resMap D X eL hH n (U := U)) where
  toFun x := ⟨picChar D X eL hk hH hτ n hU x,
    (SetLike.ext_iff.1 (range_picChar D X eL hk hH hτ n hU) _).1 ⟨x, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- **`Pic(F)[n]` is the group of characters of `π₁ᵉᵗ(U)` with zero residues.** -/
def picEquivKer : picTorsion k (F D) n ≃+ LinearMap.ker (resMap D X eL hH n (U := U)) :=
  AddEquiv.ofBijective (picToKer D X eL hk hH hτ n hU)
    ⟨fun x y h ↦ picChar_injective D X eL hk hH hτ n hU (congrArg Subtype.val h), fun a ↦ by
      have : (a : charSpace n _) ∈ (picChar D X eL hk hH hτ n hU).range :=
        (SetLike.ext_iff.1 (range_picChar D X eL hk hH hτ n hU) _).2 a.2
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩⟩

lemma coe_picEquivKer (x : picTorsion k (F D) n) :
    ((picEquivKer D X eL hk hH hτ n hU x :
      LinearMap.ker (resMap D X eL hH n (U := U))) :
        charSpace n (⊤ : OpenSubgroup (PiU D X eL U))) =
      picChar D X eL hk hH hτ n hU x :=
  rfl

end PicChar

end CurvesJacobian.CuspChar
