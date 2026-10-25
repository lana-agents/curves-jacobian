/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ThetaFamily
import CurvesJacobian.Picard.ChartH1

/-!
# A point of `J_L` over `Ω` at which the theta family has `H¹ = 0`

Let `C` be a curve over a perfect field `k` with a rational point `σ`, `Ω ⊇ k` an algebraic
closure and `J_L` the Jacobian over `L = jacFieldD C σ hσ Ω`, with theta family
`Θ = P ⊗ 𝒪((g − 1)(σ × J_L))`.

* `CurvesJacobian.exists_chartH0_chartH1_subsingleton_ext` (and variants): on `C_K`, `K` a field
  over `Ω`, there is an invertible sheaf `N` with chart Čech `H⁰ = H¹ = 0`: take a line bundle
  with `H¹ = 0` and `h⁰ = 1` (Stacks, Lemma 44.6.5, Tag 0B9Y, `goodK_one_ext`) and remove one more
  `Ω`-point in the overlap of the charts at which the generating section does not vanish
  (`goodK_removePoint_ext`);
* **`CurvesJacobian.exists_good_point`**: there is `t₀ : Spec Ω ⟶ J_L` with `H¹(Θ_{t₀}) = 0`.
  The class `ξ = [N] − (g − 1)[σ_Ω]` of such an `N` on `C_Ω` has `χ = 1 − g`, hence lies in
  `Pic⁰_{C/k,σ}(Ω)`, so it is the pullback of the universal class along a point `t₀` of `J_L`;
  then `Θ_{t₀} ≅ N`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

section NonSpecial

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]

local notation "Sk" => Spec (CommRingCat.of k)

variable (C) [PerfectField k] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]
  (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "sΩ" => specAlgebraMap (k₀ := k) Ω

include σ hσ

/-- **A class on `C_K` with vanishing chart Čech cohomology** (`K` a field over `Ω`): some
`z ∈ Pic(C_K)` has `H⁰ = 0` and `H¹ = 0` for the chart covering. -/
theorem exists_pic_chartH0_chartH1_subsingleton_ext (K : CommRingCat.{u})
    [(Spec K).Over Sk] (hF : IsField Γ(Spec K, ⊤)) (j : Spec K ⟶ SΩ)
    (hj : j ≫ sΩ = (Spec K ↘ Sk)) :
    ∃ z : (pullback (C ↘ Sk) (Spec K ↘ Sk)).Pic,
      Subsingleton (chartH0 π (Spec K ↘ Sk) (Scheme.Pic.rep z)) ∧
        Subsingleton (chartH1 π (Spec K ↘ Sk) (Scheme.Pic.rep z)) := by
  obtain ⟨c₁, d, h₁⟩ := goodK_twist C π K hF (Scheme.Pic.rep 0)
  rw [Scheme.Pic.mk_rep] at h₁
  obtain ⟨c₂, -, h₂⟩ := goodK_one_ext C π σ hσ Ω K hF j hj d _ h₁
  obtain ⟨c₃, -, h₃⟩ := goodK_removePoint_ext C π σ hσ Ω K hF j hj _ (d := 0) h₂
  have key : ∀ (M : (pullback (C ↘ Sk) (Spec K ↘ Sk)).Modules) [M.IsInvertible],
      GoodK C π K M 0 → Subsingleton (chartH0 π (Spec K ↘ Sk) M) := by
    intro M _ hM
    letI := hF.toField
    haveI := (finite_H0_H1_K C π K hF M).1
    exact Module.finrank_zero_iff.mp hM.2
  exact ⟨_, key _ h₃, h₃.1⟩

/-- **An invertible sheaf on `C_K` with vanishing chart Čech cohomology** (`K` a field over
`Ω`). -/
theorem exists_chartH0_chartH1_subsingleton_ext (K : CommRingCat.{u})
    [(Spec K).Over Sk] (hF : IsField Γ(Spec K, ⊤)) (j : Spec K ⟶ SΩ)
    (hj : j ≫ sΩ = (Spec K ↘ Sk)) :
    ∃ N : (pullback (C ↘ Sk) (Spec K ↘ Sk)).Modules, N.IsInvertible ∧
      Subsingleton (chartH0 π (Spec K ↘ Sk) N) ∧ Subsingleton (chartH1 π (Spec K ↘ Sk) N) := by
  obtain ⟨z, h0, h1⟩ := exists_pic_chartH0_chartH1_subsingleton_ext C π σ hσ Ω K hF j hj
  exact ⟨_, inferInstance, h0, h1⟩

/-- **A class on `C_Ω` with vanishing chart Čech cohomology.** -/
theorem exists_pic_chartH0_chartH1_subsingleton :
    ∃ z : (pullback (C ↘ Sk) sΩ).Pic,
      Subsingleton (chartH0 π sΩ (Scheme.Pic.rep z)) ∧
        Subsingleton (chartH1 π sΩ (Scheme.Pic.rep z)) := by
  letI : (Spec (CommRingCat.of Ω)).Over Sk := ⟨sΩ⟩
  exact exists_pic_chartH0_chartH1_subsingleton_ext C π σ hσ Ω (CommRingCat.of Ω)
    (isField_ΓSpec' Ω) (𝟙 _) (Category.id_comp _)

/-- **An invertible sheaf on `C_Ω` with vanishing chart Čech cohomology** (`H⁰ = H¹ = 0` for the
chart covering). -/
theorem exists_chartH0_chartH1_subsingleton :
    ∃ N : (pullback (C ↘ Sk) sΩ).Modules, N.IsInvertible ∧
      Subsingleton (chartH0 π sΩ N) ∧ Subsingleton (chartH1 π sΩ N) := by
  obtain ⟨z, h0, h1⟩ := exists_pic_chartH0_chartH1_subsingleton C π σ hσ Ω
  exact ⟨_, inferInstance, h0, h1⟩


end NonSpecial

/-- Divisors of sections given by equal points agree. -/
lemma picClass_ofSection_ptSec_eq {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] {S₁ : Scheme.{u}}
    (g₁ : S₁ ⟶ Spec (CommRingCat.of k)) {x x' : S₁ ⟶ C} (e : x = x')
    (hx : x ≫ (C ↘ Spec (CommRingCat.of k)) = g₁) (hx' : x' ≫ (C ↘ Spec (CommRingCat.of k)) = g₁) :
    (RelEffCartier.ofSection C g₁ (ptSec C g₁ x hx) (ptSec_snd _ _ _ _)).picClass =
      (RelEffCartier.ofSection C g₁ (ptSec C g₁ x' hx') (ptSec_snd _ _ _ _)).picClass := by
  subst e
  rfl

section Curve

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "SΩ" => Spec (CommRingCat.of Ω)
local notation "LD" => jacFieldD C σ hσ Ω
local notation "pL" => Belyi.specAlgebraMap (k₀ := k) LD
local notation "RJ" => jacDRepresentableBy C σ hσ Ω

/-- **A point of `J_L` over `Ω` at which the theta family has vanishing chart `H¹`.** -/
theorem exists_good_point :
    ∃ t₀ : SΩ ⟶ (jacDk C σ hσ Ω).left,
      Subsingleton (chartH1 (curveToP1 k C) (t₀ ≫ (jacDk C σ hσ Ω).hom)
        ((Scheme.Modules.pullback (bcMap (C ↘ Sk) t₀ (jacDk C σ hσ Ω).hom _ rfl)).obj
          (thetaFamily C σ hσ Ω))) := by
  set π := curveToP1 k C
  let sL : SΩ ⟶ Spec (CommRingCat.of LD) := specAlgebraMap (k₀ := LD) Ω
  let gΩ : SΩ ⟶ Sk := sL ≫ pL
  have hgΩ : 𝟙 _ ≫ specAlgebraMap (k₀ := k) Ω = gΩ := by
    rw [Category.id_comp]
    exact (specAlgebraMap_comp (k₀ := k) (K := Ω) LD).symm
  letI : (Spec (CommRingCat.of Ω)).Over Sk := ⟨gΩ⟩
  have hF : IsField Γ(SΩ, ⊤) := isField_ΓSpec' Ω
  obtain ⟨z, h0, h1⟩ : ∃ z : (pullback (C ↘ Sk) gΩ).Pic,
      Subsingleton (chartH0 π gΩ (Scheme.Pic.rep z)) ∧
        Subsingleton (chartH1 π gΩ (Scheme.Pic.rep z)) :=
    exists_pic_chartH0_chartH1_subsingleton_ext C π σ hσ Ω (CommRingCat.of Ω) hF (𝟙 _) hgΩ
  -- the divisor `σ_Ω` and the class `ξ = [N] − (g − 1) [σ_Ω]`
  let D := RelEffCartier.ofSection C gΩ (secT (C ↘ Sk) σ hσ gΩ) (secT_snd _ σ hσ _)
  let ξ : (pullback (C ↘ Sk) gΩ).Pic := z + (-((genusNat k C : ℤ) - 1)) • D.picClass
  have hξσ : ξ ∈ picSigmaGrp (C ↘ Sk) σ hσ gΩ := by
    rw [mem_picSigmaGrp]
    exact Subsingleton.elim _ _
  have hz : chiCurve π gΩ (Scheme.Pic.rep z) = 0 := by
    have e0 : Module.finrank Γ(SΩ, ⊤) (chartH0 π gΩ (Scheme.Pic.rep z)) = 0 :=
      Module.finrank_zero_of_subsingleton
    have e1 : Module.finrank Γ(SΩ, ⊤) (chartH1 π gΩ (Scheme.Pic.rep z)) = 0 :=
      Module.finrank_zero_of_subsingleton
    change (Module.finrank Γ(SΩ, ⊤) (chartH0 π gΩ (Scheme.Pic.rep z)) : ℤ) -
      Module.finrank Γ(SΩ, ⊤) (chartH1 π gΩ (Scheme.Pic.rep z)) = 0
    rw [e0, e1]
    rfl
  have hχ : chiCurve π gΩ (Scheme.Pic.rep ξ) = 1 - genusNat k C := by
    have := chiCurve_add_zsmul_divisor π (T := SΩ) hF z D (RelEffCartier.degree_ofSection _ _ _ _)
      (-((genusNat k C : ℤ) - 1))
    change chiCurve π gΩ (Scheme.Pic.rep (z + _)) =
      chiCurve π gΩ (Scheme.Pic.rep z) + _ at this
    refine this.trans ?_
    rw [hz]
    ring
  let y : (sigmaG (picSigma (C ↘ Sk) σ hσ)).obj (op SΩ) := ⟨gΩ, ⟨ξ, hξσ⟩⟩
  have hdeg : picDeg σ hσ π 0 SΩ y := by
    have := picDeg_of_isField σ hσ π hF y
    have hc : chiPoint σ hσ π y - 1 + genusNat k C = 0 := by
      change chiCurve π gΩ (Scheme.Pic.rep ξ) - 1 + _ = 0
      rw [hχ]
      ring
    rwa [hc] at this
  -- the point `t₀` of `J_L` classifying `ξ`
  let x : ((Over.map pL).op ⋙ picZero C σ hσ π ⋙ forget AddCommGrpCat).obj
      (op (Over.mk sL)) := ⟨⟨ξ, hξσ⟩, hdeg⟩
  obtain ⟨t, ht⟩ : ∃ t, (RJ).homEquiv t = x := ⟨_, Equiv.apply_symm_apply _ _⟩
  let t₀ : SΩ ⟶ (jacDk C σ hσ Ω).left := t.left
  refine ⟨t₀, ?_⟩
  have w : t₀ ≫ (jacDk C σ hσ Ω).hom = gΩ := Over.w ((Over.map pL).map t)
  have hPξ : Scheme.Pic.map (bcMap (C ↘ Sk) t₀ (jacDk C σ hσ Ω).hom gΩ w)
      (Scheme.Pic.mk (poincare C σ hσ Ω).L) = ξ := by
    have hP : Scheme.Pic.mk (poincare C σ hσ Ω).L = (univClass C σ hσ Ω).1 :=
      congrArg Subtype.val (poincare_cls C σ hσ Ω)
    have h2 := congrArg Subtype.val (homEquiv_eq_pull C σ hσ Ω t)
    rw [ht] at h2
    rw [hP]
    exact h2.symm
  have hx : ((jacDk C σ hσ Ω).hom ≫ σ) ≫ (C ↘ Sk) = (jacDk C σ hσ Ω).hom := by
    rw [Category.assoc, hσ, Category.comp_id]
  have hD : Scheme.Pic.map (bcMap (C ↘ Sk) t₀ (jacDk C σ hσ Ω).hom gΩ w)
      (sigmaDivJ C σ hσ Ω).picClass = D.picClass :=
    (map_picClass_ptSec C (jacDk C σ hσ Ω).hom ((jacDk C σ hσ Ω).hom ≫ σ) hx t₀ gΩ
      w).trans (picClass_ofSection_ptSec_eq C gΩ
        (by rw [← Category.assoc]; exact congrArg (· ≫ σ) w) _
        (by rw [Category.assoc, hσ, Category.comp_id]))
  have hθ : Scheme.Pic.map (bcMap (C ↘ Sk) t₀ (jacDk C σ hσ Ω).hom gΩ w)
      (thetaClass C σ hσ Ω) = z := by
    rw [thetaClass, map_add, map_zsmul, hPξ, hD]
    change z + _ + _ = z
    rw [neg_smul, neg_add_cancel_right]
  -- transport along `Θ_{t₀} ≅ N`
  suffices H : ∀ (g' : SΩ ⟶ Sk) (hg' : t₀ ≫ (jacDk C σ hσ Ω).hom = g'),
      Subsingleton (chartH1 π g' ((Scheme.Modules.pullback
        (bcMap (C ↘ Sk) t₀ (jacDk C σ hσ Ω).hom g' hg')).obj (thetaFamily C σ hσ Ω))) from
    H _ rfl
  intro g' hg'
  obtain rfl : g' = gΩ := hg'.symm.trans w
  have hmk : Scheme.Pic.mk ((Scheme.Modules.pullback
      (bcMap (C ↘ Sk) t₀ (jacDk C σ hσ Ω).hom gΩ hg')).obj (thetaFamily C σ hσ Ω)) =
        Scheme.Pic.mk (Scheme.Pic.rep z) := by
    rw [← Scheme.Pic.map_mk, mk_thetaFamily, Scheme.Pic.mk_rep]
    exact hθ
  obtain ⟨e⟩ := Scheme.Pic.mk_eq_mk_iff.mp hmk
  have hf := sectionsIso_res (S := SΩ) e
    (inf_le_left : chartOf π gΩ 0 ⊓ chartOf π gΩ 1 ≤ chartOf π gΩ 0)
  have hg := sectionsIso_res (S := SΩ) e
    (inf_le_right : chartOf π gΩ 0 ⊓ chartOf π gΩ 1 ≤ chartOf π gΩ 1)
  exact (TwoCech.equivH1 _ _ _ hf hg).toEquiv.subsingleton_congr.mpr h1

end Curve

end CurvesJacobian
