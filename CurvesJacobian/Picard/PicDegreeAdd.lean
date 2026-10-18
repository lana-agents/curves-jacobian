/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.ZeroSchemeDivisor
import CurvesJacobian.Picard.PicDegreeDivisor
import CurvesJacobian.Picard.PicFField

/-!
# Every line bundle over a field is a difference of effective divisors; `Pic⁰` is a subgroup

Let `C` be a curve over a perfect field `k` with a finite `π : C → ℙ¹_k`, and `T` an affine
`k`-scheme with `Γ(T)` a field. This file proves:

* `CurvesJacobian.fibreNonzero_of_isField`: a global section `s₀ ≠ 0` of an invertible sheaf on
  `X_T = C ×_k T` does not vanish in any fibre on any chart (its restriction to the overlap of
  the charts is nonzero because the chart rings are domains, and `K` is faithfully flat over the
  field `Γ(T)`). Hence its zero scheme is a relative effective Cartier divisor `D` with
  `𝒪(D) ≅ L` (`exists_relEffCartier_of_ne_zero`), without the `F`-condition of Stacks,
  Lemma 44.6.4 (Tag 0B9X).
* **`CurvesJacobian.exists_eq_picClass_sub`**: every class `z ∈ Pic(X_T)` is `[𝒪(D)] − [𝒪(E)]`
  with `D`, `E` effective: `E` is the zero scheme of `x₀ⁿ ∈ Γ(𝒪(n · ∞))` and `D` that of a
  nonzero section of `L ⊗ 𝒪(n · ∞)`, which exists for `n ≫ 0` by Serre vanishing on the chart
  complex (`Cech.exists_twist_H1_eq_zero`, proof of Stacks, Lemma 44.6.5, Tag 0B9Y).
* **`CurvesJacobian.chiCurve_add_of_isField`**: the degree `χ − (1 − g)` is additive on
  `Pic(X_T)`, and **`picDeg_add`**, **`picDeg_neg`**: `Pic^d + Pic^e ⊆ Pic^{d+e}`,
  `−Pic^d ⊆ Pic^{−d}`; with `picDeg_zero_zero`, `Pic⁰ ⊆ Pic_{C/k,σ}` is a subgroup functor
  (Stacks, Lemma 44.6.7, Tag 0BA0).
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite TensorProduct
open AlgebraicGeometry.Scheme.Modules MonoidalCategory

universe u

noncomputable section

namespace CurvesJacobian

section Curve

open Cech Belyi ModulesGlue

variable {k : Type u} [Field k] [PerfectField k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (π : C ⟶ ProjectiveLine.scheme k)
  [IsFinite π] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))] [IsAffine T]

local notation "Sk" => Spec (CommRingCat.of k)
local notation "XT" => pullback (C ↘ Sk) (T ↘ Sk)
local notation "𝒰" => chartOf π (T ↘ Sk)

/-- Over a field, the chart rings of `C ×_k T` are domains. -/
lemma isDomain_chart_of_isField (hF : IsField Γ(T, ⊤)) (i : Fin 2) :
    IsDomain Γ(XT, 𝒰 i) := by
  letI := hF.toField
  haveI := isDomain_tensor_chart (T₀ := T) π i Γ(T, ⊤)
  exact (Algebra.TensorProduct.lid Γ(T, ⊤) Γ(XT, 𝒰 i)).symm.toRingEquiv.injective.isDomain _

/-- Over a field, a nonzero global section of an invertible sheaf on `C ×_k T` has nonzero
restriction to the overlap of the charts. -/
lemma res_inf_ne_zero_of_isField (hF : IsField Γ(T, ⊤)) (L : (XT).Modules) [L.IsInvertible]
    (s₀ : Γ(L, ⊤)) (h : s₀ ≠ 0) : rs L (le_top : (𝒰 0) ⊓ (𝒰 1) ≤ ⊤) s₀ ≠ 0 := by
  letI := hF.toField
  intro h0
  have hi : ∀ i : Fin 2, rs L (le_top : 𝒰 i ≤ ⊤) s₀ = 0 := fun i ↦ by
    have h1 := one_tmul_res_eq_zero_of_inf π L s₀ Γ(T, ⊤) i (by rw [h0, TensorProduct.tmul_zero])
    rwa [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h1
  apply h
  apply (globalSectionsEquivH0 T L (chartOf_sup π (T ↘ Sk))).injective
  rw [map_zero]
  exact Subtype.ext (Prod.ext (hi 0) (hi 1))

/-- **Over a field, a nonzero section is nonzero in every fibre on every chart.** -/
theorem fibreNonzero_of_isField (hF : IsField Γ(T, ⊤)) (L : (XT).Modules) [L.IsInvertible]
    (s₀ : Γ(L, ⊤)) (h : s₀ ≠ 0) : FibreNonzero π L s₀ := by
  intro K _ _ i h0
  letI := hF.toField
  apply res_inf_ne_zero_of_isField π hF L s₀ h
  have h1 := congrArg ((resModLin T L (chart_inf_le (T := T) π i)).lTensor K) h0
  rw [LinearMap.lTensor_tmul, map_zero] at h1
  have hres : resModLin T L (chart_inf_le (T := T) π i) (rs L (le_top : 𝒰 i ≤ ⊤) s₀) =
      rs L (le_top : (𝒰 0) ⊓ (𝒰 1) ≤ ⊤) s₀ := rs_rs L _ _ s₀
  rw [hres] at h1
  rwa [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h1

include π in
/-- **The zero scheme of a nonzero section over a field** is a relative effective Cartier
divisor `D` on `C ×_k T` with `𝒪(D) ≅ L`. -/
theorem exists_relEffCartier_of_ne_zero (hF : IsField Γ(T, ⊤)) (L : (XT).Modules)
    [L.IsInvertible] (s₀ : Γ(L, ⊤)) (h : s₀ ≠ 0) :
    ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)), D.picClass = Scheme.Pic.mk L :=
  ⟨zeroSchemeDivisor π L s₀ (fibreNonzero_of_isField π hF L s₀ h),
    picClass_zeroSchemeDivisor π L s₀ _⟩

/-- Over a field, an invertible sheaf has a nonzero section on the chart `U_0`. -/
lemma exists_ne_zero_sections_chart (hF : IsField Γ(T, ⊤)) (M : (XT).Modules)
    [M.IsInvertible] : ∃ u : Γ(M, 𝒰 0), u ≠ 0 := by
  haveI := isDomain_chart_of_isField π hF 0
  haveI := invertible_sections M (isAffineOpen_chart (T₀ := T) π 0)
  by_contra h
  push Not at h
  haveI : Subsingleton Γ(M, 𝒰 0) := ⟨fun a b ↦ (h a).trans (h b).symm⟩
  have e := Module.Invertible.linearEquiv Γ(XT, 𝒰 0) Γ(M, 𝒰 0)
  haveI : Subsingleton (Module.Dual Γ(XT, 𝒰 0) Γ(M, 𝒰 0) ⊗[Γ(XT, 𝒰 0)] Γ(M, 𝒰 0)) :=
    inferInstance
  exact not_subsingleton Γ(XT, 𝒰 0) e.symm.toEquiv.subsingleton

include π in
/-- **Every line bundle over a field is a difference of effective divisors**: for `M`
invertible on `C ×_k T`, `Γ(T)` a field, `[M] = [𝒪(D)] − [𝒪(E)]` with `D`, `E` relative
effective Cartier divisors (`E = n · π⁻¹(∞)`, `D` the zero scheme of a section of `M(n · ∞)`). -/
theorem exists_mk_eq_picClass_sub (hF : IsField Γ(T, ⊤)) (M : (XT).Modules) [M.IsInvertible] :
    ∃ D E : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)),
      Scheme.Pic.mk M = D.picClass - E.picClass := by
  letI := hF.toField
  let p₁ : XT ⟶ ProjectiveLine.scheme k := pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π
  have hρ : 𝟙 (XT) ≫ p₁ = pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π := Category.id_comp _
  have hU : IsAffineOpen (𝒰 0) := isAffineOpen_chart (T₀ := T) π 0
  have hV : IsAffineOpen (𝒰 1) := isAffineOpen_chart (T₀ := T) π 1
  have hUV := isAffineOpen_chart_inf (T₀ := T) π
  haveI := (finite_cechModH0_H1 (T₀ := T) π M).2
  obtain ⟨u, hu⟩ := exists_ne_zero_sections_chart π hF M
  let N : ℕ → (XT).Modules := fun n ↦ (Scheme.Modules.pullback (𝟙 (XT))).obj (twistInf p₁ n)
  have hdata := fun n ↦ twistInf_pullback_data p₁ (𝟙 (XT))
    (pullback.fst (C ↘ Sk) (T ↘ Sk) ≫ π) hρ n
  obtain ⟨n, -, x, hx, hx0⟩ := exists_twist_H1_eq_zero (S := T) hU hV hUV
    (basicOpen_chartσ _) M hu N (fun n ↦ pullbackSection (𝟙 (XT)) (twistInfSection p₁ n))
    (fun n ↦ (hdata n).1) (fun n ↦ (hdata n).2)
  -- `D`: the zero scheme of a nonzero section of `M(n · ∞)`
  let eH := globalSectionsEquivH0 T (M ⊗ N n) (chartOf_sup π (T ↘ Sk))
  have hs : eH.symm ⟨x, hx⟩ ≠ 0 := by
    intro h0
    apply hx0
    have := congrArg eH h0
    rw [LinearEquiv.apply_symm_apply, map_zero] at this
    exact congrArg Subtype.val this
  obtain ⟨D, hD⟩ := exists_relEffCartier_of_ne_zero π hF (M ⊗ N n) _ hs
  -- `E`: the zero scheme of `x₀ⁿ`
  have ht : pullbackSection (𝟙 (XT)) (twistInfSection p₁ n) ≠ 0 := by
    intro h0
    haveI := isDomain_chart_of_isField π hF 0
    have hb := (hdata n).1
    have h1 : hb.equiv 1 = 0 := by
      change (1 : Γ(XT, 𝒰 0)) • ((N n).presheaf.map (homOfLE (le_top : 𝒰 0 ≤ ⊤)).op
        (pullbackSection (𝟙 (XT)) (twistInfSection p₁ n))) = 0
      rw [one_smul, h0]
      exact map_zero _
    exact one_ne_zero (hb.equiv.map_eq_zero_iff.mp h1)
  obtain ⟨E, hE⟩ := exists_relEffCartier_of_ne_zero π hF (N n) _ ht
  refine ⟨D, E, ?_⟩
  rw [hD, hE, Scheme.Pic.mk_tensor]
  abel

include π in
/-- **Every class in `Pic(C ×_k T)`, `Γ(T)` a field, is `[𝒪(D)] − [𝒪(E)]`** with `D`, `E`
effective. -/
theorem exists_eq_picClass_sub (hF : IsField Γ(T, ⊤)) (z : (XT).Pic) :
    ∃ D E : RelEffCartier (pullback.snd (C ↘ Sk) (T ↘ Sk)), z = D.picClass - E.picClass := by
  obtain ⟨D, E, h⟩ := exists_mk_eq_picClass_sub π hF (Scheme.Pic.rep z)
  exact ⟨D, E, by rw [← h, Scheme.Pic.mk_rep]⟩

/-- **Additivity of the degree over fields** (Stacks, Lemma 44.6.7, Tag 0BA0): with
`deg = χ − (1 − g)`, `deg (z + z') = deg z + deg z'` on `Pic(C ×_k T)`, `Γ(T)` a field. -/
theorem chiCurve_add_of_isField (hF : IsField Γ(T, ⊤)) (z z' : (XT).Pic) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (z + z')) =
      chiCurve π (T ↘ Sk) (Scheme.Pic.rep z) + chiCurve π (T ↘ Sk) (Scheme.Pic.rep z') -
        (1 - genusNat k C) := by
  obtain ⟨D, E, rfl⟩ := exists_eq_picClass_sub π hF z
  exact chiCurve_add_of_divisors π hF D E z'

/-- `χ(𝒪) = 1 − g`, for the representative of `0 ∈ Pic(C ×_k T)`. -/
lemma chiCurve_rep_zero (hF : IsField Γ(T, ⊤)) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (0 : (XT).Pic)) = 1 - genusNat k C := by
  have e : Scheme.Pic.rep (0 : (XT).Pic) ≅ structureSheaf (XT) :=
    ((Scheme.Pic.mk_eq_zero_iff _).mp (Scheme.Pic.mk_rep _)).some ≪≫
      (structureSheafIsoUnit _).symm
  rw [chiCurve_congr π _ e, chiCurve_structureSheaf π hF]

/-- `deg (−z) = − deg z` over fields. -/
theorem chiCurve_neg_of_isField (hF : IsField Γ(T, ⊤)) (z : (XT).Pic) :
    chiCurve π (T ↘ Sk) (Scheme.Pic.rep (-z)) =
      2 * (1 - genusNat k C) - chiCurve π (T ↘ Sk) (Scheme.Pic.rep z) := by
  have h := chiCurve_add_of_isField π hF z (-z)
  rw [add_neg_cancel, chiCurve_rep_zero π hF] at h
  linarith

end Curve

section Degree

open Cech Belyi

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k) [PerfectField k] [IsCurveOver k C] [IsFinite π]
  (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "Sk" => Spec (CommRingCat.of k)
local notation "G" => picSigma (C ↘ Sk) σ hσ

omit [PerfectField k] [IsCurveOver k C] [IsFinite π] in
lemma chiPoint_map_eq {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ Sk)
    (y : picSigmaGrp (C ↘ Sk) σ hσ g) :
    chiPoint σ hσ π ((sigmaG G).map h.op ⟨g, y⟩) =
      chiCurve π (h ≫ g) (Scheme.Pic.rep
        (Scheme.Pic.map (bcMap (C ↘ Sk) h g (h ≫ g) rfl) (y : (pullback (C ↘ Sk) g).Pic))) :=
  rfl

/-- Additivity of `χ − (1 − g)` on `Pic(C ×_k T')`, `Γ(T')` a field. -/
lemma chiCurve_map_add {T' : Scheme.{u}} [IsAffine T'] (hF : IsField Γ(T', ⊤)) (g' : T' ⟶ Sk)
    (a b : (pullback (C ↘ Sk) g').Pic) :
    chiCurve π g' (Scheme.Pic.rep (a + b)) =
      chiCurve π g' (Scheme.Pic.rep a) + chiCurve π g' (Scheme.Pic.rep b) -
        (1 - genusNat k C) := by
  letI : T'.Over Sk := ⟨g'⟩
  exact chiCurve_add_of_isField π hF a b

lemma chiCurve_map_neg {T' : Scheme.{u}} [IsAffine T'] (hF : IsField Γ(T', ⊤)) (g' : T' ⟶ Sk)
    (a : (pullback (C ↘ Sk) g').Pic) :
    chiCurve π g' (Scheme.Pic.rep (-a)) =
      2 * (1 - genusNat k C) - chiCurve π g' (Scheme.Pic.rep a) := by
  letI : T'.Over Sk := ⟨g'⟩
  exact chiCurve_neg_of_isField π hF a

/-- **`Pic^d + Pic^e ⊆ Pic^{d+e}`** (Stacks, Lemma 44.6.7, Tag 0BA0). -/
theorem picDeg_add {T : Scheme.{u}} (g : T ⟶ Sk) (y y' : picSigmaGrp (C ↘ Sk) σ hσ g)
    {d e : ℤ} (hy : picDeg σ hσ π d T ⟨g, y⟩) (hy' : picDeg σ hσ π e T ⟨g, y'⟩) :
    picDeg σ hσ π (d + e) T ⟨g, y + y'⟩ := by
  intro T' _ hF h
  have h1 := hy T' hF h
  have h2 := hy' T' hF h
  rw [chiPoint_map_eq] at h1 h2 ⊢
  rw [AddSubgroup.coe_add, map_add, chiCurve_map_add π hF, h1, h2]
  ring

/-- **`−Pic^d ⊆ Pic^{−d}`** (Stacks, Lemma 44.6.7, Tag 0BA0). -/
theorem picDeg_neg {T : Scheme.{u}} (g : T ⟶ Sk) (y : picSigmaGrp (C ↘ Sk) σ hσ g) {d : ℤ}
    (hy : picDeg σ hσ π d T ⟨g, y⟩) : picDeg σ hσ π (-d) T ⟨g, -y⟩ := by
  intro T' _ hF h
  have h1 := hy T' hF h
  rw [chiPoint_map_eq] at h1 ⊢
  rw [AddSubgroup.coe_neg, map_neg, chiCurve_map_neg π hF, h1]
  ring

/-- **`Pic⁰_{C/k,σ}(T)` is a subgroup** of `Pic_{C/k,σ}(T)` (Stacks, Lemma 44.6.7, Tag 0BA0). -/
def picZeroGrp {T : Scheme.{u}} (g : T ⟶ Sk) : AddSubgroup (picSigmaGrp (C ↘ Sk) σ hσ g) where
  carrier := {y | picDeg σ hσ π 0 T ⟨g, y⟩}
  zero_mem' := picDeg_zero_zero π σ hσ g
  add_mem' {a b} ha hb := by
    have := picDeg_add π σ hσ g a b ha hb
    rwa [add_zero] at this
  neg_mem' {a} ha := by
    have := picDeg_neg π σ hσ g a ha
    rwa [neg_zero] at this

lemma mem_picZeroGrp {T : Scheme.{u}} (g : T ⟶ Sk) (y : picSigmaGrp (C ↘ Sk) σ hσ g) :
    y ∈ picZeroGrp π σ hσ g ↔ picDeg σ hσ π 0 T ⟨g, y⟩ := Iff.rfl

end Degree

end CurvesJacobian
