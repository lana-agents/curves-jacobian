/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicDegree
import CurvesJacobian.Picard.EulerCharTwist
import CurvesJacobian.Picard.PicFField

/-!
# Translating `Pic^d` by the class of a rational point (Stacks, Lemma 44.6.7, Tag 0BA0)

For a `k`-point `x` of `C` lying in both charts, twisting by `𝒪(x)` raises the Euler
characteristic by one (`Cech.chi_twist`). Hence translation by the class `[𝒪(x)]` in
`Pic_{C/k,σ}(k)` maps `Pic^d` onto `Pic^{d+1}`: this is the translation argument of the proof of
Stacks, Lemma 44.6.7 (Tag 0BA0), which reduces properness of all `Pic^d` to `d ≥ g` and
identifies all `Pic^d` with `Pic^0`.

* `CurvesJacobian.chiCurve_add_ofSection`: `χ(M(x_T)) = χ(M) + 1` on `C ×_k T`, `Γ(T)` a field;
* `CurvesJacobian.pointClass`: the class of `𝒪(x)` in `Pic_{C/k,σ}(k)`;
* `CurvesJacobian.chiPoint_translate`, **`CurvesJacobian.picDeg_translate_iff`**:
  `translate [𝒪(x)] x ∈ Pic^{d+1} ↔ x ∈ Pic^d`;
* `CurvesJacobian.exists_point_chart_inf`: such points exist when `k` is algebraically closed.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MonoidalCategory

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)

section Twist

variable [PerfectField k] [IsCurveOver k C]

/-- **Twisting by a rational point raises `χ` by one** (`deg 𝒪(x) = 1`): for `T` affine over
`k` with `Γ(T)` a field and a `k`-point `x` of `C` in both charts, `χ(M ⊗ 𝒪(x_T)) = χ(M) + 1`
for every invertible `M` on `C ×_k T`. -/
theorem chiCurve_add_ofSection {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]
    (hF : IsField Γ(T, ⊤)) (M : (pullback (C ↘ Sk) (T ↘ Sk)).Modules) [M.IsInvertible]
    (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk)
    (hxW : ⊤ ≤ xC ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1))) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (Scheme.Pic.mk M +
      (RelEffCartier.ofSection C (T ↘ Sk) (secT (C ↘ Sk) xC hx (T ↘ Sk))
        (secT_snd _ _ _ _)).picClass)) = chiCurve π (T ↘ Sk) M + 1 := by
  letI := hF.toField
  set σx := secT (C ↘ Sk) xC hx (T ↘ Sk)
  haveI := isClosedImmersion_of_section C (T ↘ Sk) σx (secT_snd _ _ _ _)
  set D := RelEffCartier.ofSection C (T ↘ Sk) σx (secT_snd _ _ _ _)
  set P := Scheme.Pic.rep (Scheme.Pic.mk M + D.picClass)
  have e : P ≅ M ⊗ D.lineBundle := by
    refine (Scheme.Pic.mk_eq_mk_iff.mp ?_).some
    rw [Scheme.Pic.mk_tensor, Scheme.Pic.mk_rep]
    rfl
  have hU := isAffineOpen_chart (T₀ := T) π 0
  have hV := isAffineOpen_chart (T₀ := T) π 1
  have hUV := isAffineOpen_chart_inf (T₀ := T) π
  have hσ : ⊤ ≤ σx ⁻¹ᵁ ((pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 0 ⊓
      (pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k 1) := by
    intro t _
    have h1 := hxW (show (T ↘ Sk) t ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial)
    have h3 : (σx ≫ pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) t ∈
        ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1 := by
      rw [secT_fst_assoc]
      exact h1
    exact h3
  haveI := (finite_cechModH0_H1 (T₀ := T) π M).1
  haveI := (finite_cechModH0_H1 (T₀ := T) π M).2
  haveI := (finite_cechModH0_H1 (T₀ := T) π P).1
  haveI := (finite_cechModH0_H1 (T₀ := T) π P).2
  have key := chi_twist σx (secT_snd _ _ _ _) hF hU hV hUV hσ D
    (RelEffCartier.ofSection_ideal _ _ _ _) M P e
  rw [chiCurve, chiCurve]
  exact key

end Twist

section Translate

variable [PerfectField k] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- The class of `𝒪(x)` in `Pic_{C/k,σ}(k)` for a `k`-point `x` of `C`. -/
def pointClass (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk) :
    (picSigma (C ↘ Sk) σ hσ).obj (op (Over.mk (𝟙 Sk))) :=
  have hmem : (RelEffCartier.ofSection C (𝟙 Sk) (secT (C ↘ Sk) xC hx (𝟙 Sk))
      (secT_snd _ _ _ _)).picClass ∈ picSigmaGrp (C ↘ Sk) σ hσ (𝟙 Sk) := by
    rw [mem_picSigmaGrp]
    exact Subsingleton.elim _ _
  ⟨_, hmem⟩

/-- Translation by `[𝒪(x)]` raises the Euler characteristic of a field valued point by one. -/
theorem chiPoint_translate (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk)
    (hxW : ⊤ ≤ xC ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)))
    {T : Scheme.{u}} [IsAffine T] (hF : IsField Γ(T, ⊤)) (x : (sigmaG G).obj (op T)) :
    chiPoint σ hσ π (translate G (pointClass C σ hσ xC hx) x) = chiPoint σ hσ π x + 1 := by
  obtain ⟨g, y⟩ := x
  letI : T.Over Sk := ⟨g⟩
  haveI : Scheme.Modules.IsInvertible (X := pullback (C ↘ Sk) (T ↘ Sk))
      (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1) :=
    inferInstanceAs (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1).IsInvertible
  have key := chiCurve_add_ofSection C π hF
    (Scheme.Pic.rep (y : picSigmaGrp (C ↘ Sk) σ hσ g).1) xC hx hxW
  rw [Scheme.Pic.mk_rep, ← map_picClass_ofSection C xC hx (T ↘ Sk), add_comm] at key
  exact key

/-- **Translation by `[𝒪(x)]` maps `Pic^d` onto `Pic^{d+1}`** (proof of Stacks, Lemma 44.6.7,
Tag 0BA0). -/
theorem picDeg_translate_iff (xC : Sk ⟶ C) (hx : xC ≫ (C ↘ Sk) = 𝟙 Sk)
    (hxW : ⊤ ≤ xC ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)))
    (d : ℤ) {T : Scheme.{u}} (x : (sigmaG G).obj (op T)) :
    picDeg σ hσ π (d + 1) T (translate G (pointClass C σ hσ xC hx) x) ↔
      picDeg σ hσ π d T x := by
  refine forall_congr' fun T' ↦ forall_congr' fun _ ↦ forall_congr' fun hF ↦
    forall_congr' fun h ↦ ?_
  rw [map_translate, chiPoint_translate C π σ hσ xC hx hxW hF]
  constructor <;> intro H <;> linarith

omit [PerfectField k] in
/-- Over an algebraically closed field, `C` has a `k`-point in both charts. -/
theorem exists_point_chart_inf [IsAlgClosed k] :
    ∃ (xC : Sk ⟶ C) (_ : xC ≫ (C ↘ Sk) = 𝟙 Sk),
      ⊤ ≤ xC ⁻¹ᵁ (π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)) := by
  let WC : C.Opens := π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)
  have hWC : IsAffineOpen WC := (ProjectiveLine.isAffineOpen_U_inf k).preimage π
  haveI : Nonempty WC := nonempty_chart_inf π
  obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty WC)
  let j : C ⟶ pullback (C ↘ Sk) (Sk ↘ Sk) :=
    pullback.lift (𝟙 C) (C ↘ Sk) (by simp)
  haveI : Nonempty (pullback.fst (C ↘ Sk) (Sk ↘ Sk) ⁻¹ᵁ WC) := by
    refine ⟨⟨j w, ?_⟩⟩
    change (j ≫ pullback.fst (C ↘ Sk) (Sk ↘ Sk)) w ∈ WC
    rw [pullback.lift_fst]
    exact hw
  obtain ⟨xC, hx, hxW, -⟩ := exists_point_appLE_ne_zero C (T := Sk) isField_ΓSpec WC hWC 1
    (one_ne_zero (α := Γ(pullback (C ↘ Sk) (Sk ↘ Sk), pullback.fst (C ↘ Sk) (Sk ↘ Sk) ⁻¹ᵁ WC)))
  exact ⟨xC, hx, hxW⟩

end Translate

end CurvesJacobian
