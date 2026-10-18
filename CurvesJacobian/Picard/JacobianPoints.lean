/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicDescentInj
import Belyi.Curve.BaseChange

/-!
# `J(Ω)` as the `Ω`-points of the Jacobian of `C_Ω`

Let `C` be a curve over a perfect field `k` with a rational point `σ`, and `Ω ⊇ k` a perfect
field. Write `C_Ω = C ×_k Ω` (a curve over `Ω`, belyi's `isCurveOver_pullback`) and
`σ_Ω` for the base change of `σ`.

* `CurvesJacobian.picPtEquivExt`: `Pic_{C/k,σ}(Ω) ≃ Pic_{C_Ω/Ω,σ_Ω}(Ω)` (via
  `C_Ω ×_Ω Ω ≅ C_Ω`).
* `CurvesJacobian.degPic_map_baseChange`: the degree does not depend on the chosen finite
  morphisms to `ℙ¹` (over a field every class is `[D] − [E]`, of degree `deg D − deg E`).
* **`CurvesJacobian.jacPointsEquivExt`**: `J(Ω) = Pic⁰_{C/k,σ}(Ω) ≃ Pic⁰_{C_Ω/Ω,σ_Ω}(Ω)`.
* **`CurvesJacobian.jacobianPointsEquiv`**: for `Ω` separably closed, the `Ω`-points of the
  abelian variety `Jacobian C_Ω σ_Ω` are `J(Ω)`; together with `jacPointsEquivInv` this gives
  `J(K) ≅ (Jacobian C_Ω)(Ω)^{Gal(Ω/K)}` for `Ω / K` Galois.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

section Degree

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)
  [IsFinite π] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]

local notation "Sk" => Spec (CommRingCat.of k)

/-- Over a field, `Pic⁰` is the kernel of `degPic`. -/
lemma picDeg_zero_iff_degPic (hF : IsField Γ(T, ⊤))
    (x : picSigmaGrp (C ↘ Sk) σ hσ (T ↘ Sk)) :
    picDeg σ hσ π 0 T ⟨T ↘ Sk, x⟩ ↔ degPic π (x : (pullback (C ↘ Sk) (T ↘ Sk)).Pic) = 0 := by
  constructor
  · intro h
    have h1 := h T hF (𝟙 T)
    rw [op_id, Functor.map_id_apply] at h1
    change chiCurve π (T ↘ Sk) (Scheme.Pic.rep (x : (pullback (C ↘ Sk) (T ↘ Sk)).Pic)) =
      0 + 1 - genusNat k C at h1
    unfold degPic
    omega
  · intro h
    have h1 := picDeg_of_isField σ hσ π hF ⟨T ↘ Sk, x⟩
    have e : chiPoint σ hσ π ⟨T ↘ Sk, x⟩ - 1 + genusNat k C = 0 := h
    rwa [e] at h1

/-- The degree of `[D] − [E]` is `deg D − deg E`. -/
lemma degPic_sub_picClass (hF : IsField Γ(T, ⊤))
    (D E : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk))) (t : T) :
    degPic π (D.picClass - E.picClass) = D.degree t - E.degree t := by
  have h := map_sub (degPicHom π hF) D.picClass E.picClass
  change degPic π _ = degPic π _ - degPic π _ at h
  rw [h, degPic_picClass π hF D t, degPic_picClass π hF E t]

end Degree

section Ext

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "CΩ" => pullback (C ↘ Spec (CommRingCat.of k)) (specAlgebraMap (k₀ := k) Ω)

/-- The base change `σ_Ω : Spec Ω ⟶ C_Ω` of the rational point. -/
abbrev sigmaExt : SΩ ⟶ CΩ := secT (C ↘ Sk) σ hσ (specAlgebraMap (k₀ := k) Ω)

omit [PerfectField k] [IsCurveOver k C] in
lemma sigmaExt_comp : sigmaExt C σ hσ Ω ≫ (CΩ ↘ SΩ) = 𝟙 SΩ := secT_snd _ _ _ _

/-- The isomorphism `C_Ω ×_Ω Ω ≅ C_Ω`. -/
abbrev extIso : pullback (CΩ ↘ SΩ) (𝟙 SΩ) ⟶ CΩ := pullback.fst _ _

omit [PerfectField k] [IsCurveOver k C] in
lemma secT_extIso :
    secT (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) (𝟙 SΩ) ≫ extIso C Ω =
      sigmaExt C σ hσ Ω := by
  rw [secT_fst, Category.id_comp]

/-- **`Pic_{C/k,σ}(Ω) ≃ Pic_{C_Ω/Ω,σ_Ω}(Ω)`.** -/
def picPtEquivExt : picPt C σ hσ Ω ≃+
    picSigmaGrp (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) (𝟙 SΩ) where
  toFun x := ⟨Scheme.Pic.map (extIso C Ω) x.1, by
    rw [mem_picSigmaGrp, ← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, secT_extIso]
    exact x.2⟩
  invFun y := ⟨Scheme.Pic.map (inv (extIso C Ω)) y.1, by
    rw [mem_picSigmaGrp, ← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp]
    have e : secT (C ↘ Sk) σ hσ (specAlgebraMap (k₀ := k) Ω) ≫ inv (extIso C Ω) =
        secT (CΩ ↘ SΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) (𝟙 SΩ) := by
      rw [IsIso.comp_inv_eq, secT_extIso]
    rw [e]
    exact y.2⟩
  left_inv x := Subtype.ext (by
    change Scheme.Pic.map (inv (extIso C Ω)) (Scheme.Pic.map (extIso C Ω) x.1) = x.1
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, IsIso.inv_hom_id, Scheme.Pic.map_id,
      AddMonoidHom.id_apply])
  right_inv y := Subtype.ext (by
    change Scheme.Pic.map (extIso C Ω) (Scheme.Pic.map (inv (extIso C Ω)) y.1) = y.1
    rw [← AddMonoidHom.comp_apply, ← Scheme.Pic.map_comp, IsIso.hom_inv_id, Scheme.Pic.map_id,
      AddMonoidHom.id_apply])
  map_add' x y := Subtype.ext (map_add (Scheme.Pic.map (extIso C Ω)) x.1 y.1)

omit [PerfectField k] [IsCurveOver k C] in
@[simp]
lemma coe_picPtEquivExt (x : picPt C σ hσ Ω) :
    (picPtEquivExt C σ hσ Ω x : (pullback (CΩ ↘ SΩ) (𝟙 SΩ)).Pic) =
      Scheme.Pic.map (extIso C Ω) x.1 := rfl

variable [PerfectField Ω]

/-- **The degree is independent of the model**: `deg (z|_{C_Ω ×_Ω Ω}) = deg z`. -/
lemma degPic_map_extIso (z : (CΩ).Pic) :
    letI : (SΩ).Over Sk := ⟨specAlgebraMap (k₀ := k) Ω⟩
    letI : (SΩ).Over SΩ := ⟨𝟙 SΩ⟩
    degPic (curveToP1 Ω CΩ) (T := SΩ) (Scheme.Pic.map (extIso C Ω) z) =
      degPic (curveToP1 k C) (T := SΩ) z := by
  letI : (SΩ).Over Sk := ⟨specAlgebraMap (k₀ := k) Ω⟩
  letI : (SΩ).Over SΩ := ⟨𝟙 SΩ⟩
  have hF := isField_ΓSpec' Ω
  obtain ⟨t⟩ := nonempty_of_isField hF
  obtain ⟨D, E, rfl⟩ : ∃ D E : RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) Ω)),
      z = D.picClass - E.picClass := exists_eq_picClass_sub (curveToP1 k C) hF z
  haveI := D.isFinite C (specAlgebraMap (k₀ := k) Ω)
  haveI := E.isFinite C (specAlgebraMap (k₀ := k) Ω)
  have hD := RelEffCartier.map_picClass_baseChange D (𝟙 SΩ)
  have hE := RelEffCartier.map_picClass_baseChange E (𝟙 SΩ)
  have h1 : Scheme.Pic.map (extIso C Ω) (D.picClass - E.picClass) =
      (D.baseChange (𝟙 SΩ)).picClass - (E.baseChange (𝟙 SΩ)).picClass := by
    rw [map_sub]
    exact congrArg₂ (· - ·) hD hE
  rw [h1]
  have h2 : ((D.baseChange (𝟙 SΩ)).degree t : ℤ) - (E.baseChange (𝟙 SΩ)).degree t =
      D.degree t - E.degree t := by
    rw [RelEffCartier.degree_baseChange, RelEffCartier.degree_baseChange]
    rfl
  exact (degPic_sub_picClass (curveToP1 Ω CΩ) hF _ _ t).trans
    (h2.trans (degPic_sub_picClass (curveToP1 k C) hF D E t).symm)

/-- `J(Ω)` corresponds to `Pic⁰_{C_Ω/Ω,σ_Ω}(Ω)` under `picPtEquivExt`. -/
lemma mem_jacPoints_iff (x : picPt C σ hσ Ω) :
    x ∈ jacPoints C σ hσ Ω ↔ picPtEquivExt C σ hσ Ω x ∈
      picZeroGrp (curveToP1 Ω CΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) (𝟙 SΩ) := by
  letI : (SΩ).Over Sk := ⟨specAlgebraMap (k₀ := k) Ω⟩
  letI : (SΩ).Over SΩ := ⟨𝟙 SΩ⟩
  have hF := isField_ΓSpec' Ω
  have h1 := picDeg_zero_iff_degPic (curveToP1 k C) σ hσ hF x
  have h2 := picDeg_zero_iff_degPic (curveToP1 Ω CΩ) (sigmaExt C σ hσ Ω)
    (sigmaExt_comp C σ hσ Ω) hF (picPtEquivExt C σ hσ Ω x)
  rw [mem_picZeroGrp, mem_picZeroGrp]
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [coe_picPtEquivExt, degPic_map_extIso]

/-- **`J(Ω) = Pic⁰_{C/k,σ}(Ω) ≃ Pic⁰_{C_Ω/Ω,σ_Ω}(Ω)`.** -/
def jacPointsEquivExt : jacPoints C σ hσ Ω ≃+
    picZeroGrp (curveToP1 Ω CΩ) (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω) (𝟙 SΩ) where
  toFun x := ⟨picPtEquivExt C σ hσ Ω x.1, (mem_jacPoints_iff C σ hσ Ω x.1).mp x.2⟩
  invFun y := ⟨(picPtEquivExt C σ hσ Ω).symm y.1, (mem_jacPoints_iff C σ hσ Ω _).mpr (by
    rw [AddEquiv.apply_symm_apply]
    exact y.2)⟩
  left_inv x := Subtype.ext ((picPtEquivExt C σ hσ Ω).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((picPtEquivExt C σ hσ Ω).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add (picPtEquivExt C σ hσ Ω) x.1 y.1)

variable [IsSepClosed Ω]

/-- **The `Ω`-points of the Jacobian of `C_Ω`** (an abelian variety over `Ω`, `Jacobian`) are
`J(Ω) = Pic⁰_{C/k,σ}(Ω)`. -/
def jacobianPointsEquiv :
    (Over.mk (𝟙 SΩ) ⟶ Jacobian CΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)) ≃
      jacPoints C σ hσ Ω :=
  ((jacobianRepresentableBy CΩ (sigmaExt C σ hσ Ω) (sigmaExt_comp C σ hσ Ω)).homEquiv).trans
    (jacPointsEquivExt C σ hσ Ω).toEquiv.symm

end Ext

end CurvesJacobian
