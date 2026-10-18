/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicFFieldPoint
import CurvesJacobian.Picard.TwistInfinity
import CurvesJacobian.Picard.ChartTwist
import CurvesJacobian.Picard.PicFRep
import CurvesJacobian.Picard.PicSigmaSheafCurve

/-!
# Translates of `F` cover `Pic_{C/k,σ}` over fields (Stacks, Lemma 44.6.5, Tag 0B9Y)

Let `C` be a curve over an algebraically closed field `k` with a finite `π : C → ℙ¹_k`, and
`K` a field over `k`. For every invertible sheaf `L` on `X_K = C ×_k K` there is an invertible
sheaf `L₀` on `C` (here: on `C ×_k k`) such that `L ⊗ L₀_K` satisfies the `F`-condition: its
chart Čech complex has `H¹ = 0` and `h⁰ = 1` (`CurvesJacobian.exists_fCond_translate`).
Consequently every point of `Pic_{C/k,σ}` over a field has a translate in `F`
(`CurvesJacobian.exists_picF_translate`, the hypothesis `hfield` of
`isRepresentable_of_translate`), and

* **`CurvesJacobian.isRepresentable_picSigmaSch`**: for `k` separably closed (and perfect, as
  everywhere in this development, hence algebraically closed), the rigidified Picard functor
  `Pic_{C/k,σ}` is representable (Stacks, Lemma 44.6.5 + Lemma 44.5.1, Tags 0B9Y, 0B9Q; this is
  the separably closed case of Stacks, Proposition 44.6.6, Tag 0B9Z, for the rigidified
  functor).

## Proof (as in Stacks, Lemma 44.6.5)

1. *Twisting by `𝒪(n · ∞)`* (`goodK_twist`): with `N_n` the twist of `𝒪` on the charts by
   `τⁿ` (`Scheme.Modules.twoSetTwist`), `H¹(L ⊗ N_n) = 0` and `H⁰(L ⊗ N_n) ≠ 0` for `n ≫ 0`
   (`Cech.exists_twist_H1_eq_zero`).
2. *Removing `k`-points* (`goodK_removePoint`): if `H¹(L) = 0` and `h⁰(L) = d + 1`, choose a
   nonzero `h ∈ H⁰(L)` and (density of `C(k)`, `exists_point_appLE_ne_zero`) a `k`-point `x` in
   the overlap of the charts at which `h` does not vanish; then `L(-x_K)` has `H¹ = 0` and
   `h⁰ = d` (`Cech.removePoint`), and `𝒪(x_K)` is pulled back from `C ×_k k`
   (`map_picClass_ofSection`). Iterate until `h⁰ = 1`.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite Function
open AlgebraicGeometry.Scheme.Modules MonoidalCategory TensorProduct

universe u

noncomputable section

namespace CurvesJacobian

open Belyi Cech

variable {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
  (π : C ⟶ ProjectiveLine.scheme k) [IsFinite π]

local notation "Sk" => Spec (CommRingCat.of k)

section Field

variable (K : CommRingCat.{u}) [(Spec K).Over (Spec (CommRingCat.of k))]

local notation "XK" => pullback (C ↘ Sk) (Spec K ↘ Sk)

/-- The chart `π⁻¹ D₊(xᵢ)` of `X_K`. -/
abbrev chartK (i : Fin 2) : (XK).Opens :=
  (pullback.fst (C ↘ Sk) (Spec K ↘ Sk) ≫ π) ⁻¹ᵁ ProjectiveLine.U k i

/-- The pullback `X_K → X_k = C ×_k k`. -/
abbrev bcK : XK ⟶ pullback (C ↘ Sk) (𝟙 Sk) :=
  bcMap (C ↘ Sk) (Spec K ↘ Sk) (𝟙 Sk) (Spec K ↘ Sk) (Category.comp_id _)

/-- `H¹ = 0` and `h⁰ = d` for the chart Čech complex of `M` on `X_K`. -/
def GoodK (M : (XK).Modules) (d : ℕ) : Prop :=
  Subsingleton (cechModH1 (Spec K) M (chartK C π K 0) (chartK C π K 1)) ∧
    Module.finrank Γ(Spec K, ⊤) (cechModH0 (Spec K) M (chartK C π K 0) (chartK C π K 1)) = d

omit [IsFinite π] in
lemma goodK_congr {M M' : (XK).Modules} (e : M ≅ M') (d : ℕ) :
    GoodK C π K M d ↔ GoodK C π K M' d := by
  have hf := sectionsIso_res (S := Spec K) e
    (inf_le_left : chartK C π K 0 ⊓ chartK C π K 1 ≤ chartK C π K 0)
  have hg := sectionsIso_res (S := Spec K) e
    (inf_le_right : chartK C π K 0 ⊓ chartK C π K 1 ≤ chartK C π K 1)
  exact and_congr (TwoCech.equivH1 _ _ _ hf hg).toEquiv.subsingleton_congr
    (by rw [(TwoCech.equivH0 _ _ _ hf hg).finrank_eq])

omit [IsFinite π] in
lemma fCond_of_goodK (hF : IsField Γ(Spec K, ⊤)) {M : (XK).Modules} (h : GoodK C π K M 1) :
    FCond π (Spec K ↘ Sk) M := by
  letI := hF.toField
  refine ⟨h.1, ?_⟩
  haveI : FiniteDimensional Γ(Spec K, ⊤)
      (cechModH0 (Spec K) M (chartK C π K 0) (chartK C π K 1)) :=
    Module.finite_of_finrank_eq_succ h.2
  let e := LinearEquiv.ofFinrankEq (cechModH0 (Spec K) M (chartK C π K 0) (chartK C π K 1))
    Γ(Spec K, ⊤) (by rw [h.2, Module.finrank_self])
  exact Module.Invertible.congr e.symm

variable [PerfectField k] [IsCurveOver k C]

lemma finite_H0_H1_K (hF : IsField Γ(Spec K, ⊤)) (M : (XK).Modules) [M.IsInvertible] :
    Module.Finite Γ(Spec K, ⊤) (cechModH0 (Spec K) M (chartK C π K 0) (chartK C π K 1)) ∧
      Module.Finite Γ(Spec K, ⊤) (cechModH1 (Spec K) M (chartK C π K 0) (chartK C π K 1)) := by
  letI := hF.toField
  exact finite_cechModH0_H1 (T₀ := Spec K) π M

lemma isDomain_chartK (hF : IsField Γ(Spec K, ⊤)) (i : Fin 2) : IsDomain Γ(XK, chartK C π K i) := by
  letI := hF.toField
  haveI := isDomain_tensor_chart (T₀ := Spec K) π i Γ(Spec K, ⊤)
  exact (Algebra.TensorProduct.lid Γ(Spec K, ⊤)
    Γ(XK, chartK C π K i)).symm.toRingEquiv.injective.isDomain
    _

lemma nontrivial_chartK_inf (hF : IsField Γ(Spec K, ⊤)) :
    Nontrivial Γ(XK, chartK C π K 0 ⊓ chartK C π K 1) := by
  letI := hF.toField
  have h := nontrivial_tensor_chart_inf (T₀ := Spec K) π Γ(Spec K, ⊤)
  exact @Function.Injective.nontrivial _ _ h _ (Algebra.TensorProduct.lid Γ(Spec K, ⊤)
    Γ(XK, chartK C π K 0 ⊓ chartK C π K 1)).toRingEquiv.injective

/-- Restriction from a chart to the overlap is injective (sections of an invertible sheaf over
the domain `Γ(U_i)`, localized at the chart coordinate). -/
lemma injective_res_chartK (hF : IsField Γ(Spec K, ⊤)) (M : (XK).Modules) [M.IsInvertible]
    (i : Fin 2) (hle : chartK C π K 0 ⊓ chartK C π K 1 ≤ chartK C π K i) :
    Injective (M.presheaf.map (homOfLE hle).op) := by
  haveI := isDomain_chartK C π K hF i
  haveI := nontrivial_chartK_inf C π K hF
  haveI := isQuasicoherent_of_isInvertible M
  haveI := projective_sections M (isAffineOpen_chart (T₀ := Spec K) π i)
  -- the chart coordinate
  obtain ⟨f, hf⟩ : ∃ f : Γ(XK, chartK C π K i),
      (XK).basicOpen f = chartK C π K 0 ⊓ chartK C π K 1 := by
    fin_cases i
    · exact ⟨_, basicOpen_chartτ _⟩
    · exact ⟨_, basicOpen_chartσ _⟩
  have hf0 : f ≠ 0 := by
    intro h0
    have hu := isUnit_res_basicOpen (X := XK) (U := chartK C π K i) f
    haveI : Nontrivial Γ(XK, (XK).basicOpen f) := by rw [hf]; infer_instance
    have hz : (XK).presheaf.map (homOfLE ((XK).basicOpen_le f)).op f = 0 := by
      rw [h0, map_zero]
    exact not_isUnit_zero (hz ▸ hu)
  haveI := M.isLocalizedModule_resBasicOpen (isAffineOpen_chart (T₀ := Spec K) π i) f
  rw [injective_iff_map_eq_zero]
  intro m hm
  have hm' : M.resBasicOpen f m = 0 := by
    rw [resBasicOpen_apply]
    have : M.presheaf.map (homOfLE ((XK).basicOpen_le f)).op m =
        M.presheaf.map (homOfLE hf.le).op (M.presheaf.map (homOfLE hle).op m) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    rw [this, hm, map_zero]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
    (M.resBasicOpen f)).mp hm'
  have hfn : f ^ n ≠ 0 := pow_ne_zero n hf0
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(M, chartK C π K i))
    (mem_nonZeroDivisors_of_ne_zero hfn) (hn.trans (smul_zero _).symm)

variable [IsAlgClosed k]

/-- **Removing a `k`-point** (Stacks, Lemma 44.6.5, Tag 0B9Y). -/
theorem goodK_removePoint (hF : IsField Γ(Spec K, ⊤)) (M : (XK).Modules) [M.IsInvertible]
    {d : ℕ} (hM : GoodK C π K M (d + 1)) :
    ∃ c : (pullback (C ↘ Sk) (𝟙 Sk)).Pic,
      GoodK C π K (Scheme.Pic.rep (Scheme.Pic.mk M + Scheme.Pic.map (bcK C K) c)) d := by
  letI := hF.toField
  set U' := chartK C π K 0
  set V' := chartK C π K 1
  have hU : IsAffineOpen U' := isAffineOpen_chart (T₀ := Spec K) π 0
  have hV : IsAffineOpen V' := isAffineOpen_chart (T₀ := Spec K) π 1
  have hUV : IsAffineOpen (U' ⊓ V') := isAffineOpen_chart_inf (T₀ := Spec K) π
  haveI := (finite_H0_H1_K C π K hF M).1
  obtain ⟨h, hh⟩ : ∃ h : cechModH0 (Spec K) M U' V', h ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hM.2]; omega)
  have hW : M.presheaf.map (homOfLE (inf_le_left : U' ⊓ V' ≤ U')).op h.1.1 ≠ 0 := by
    intro h0
    have h2 : M.presheaf.map (homOfLE (inf_le_right : U' ⊓ V' ≤ V')).op h.1.2 = 0 :=
      (TwoCech.mem_H0.mp h.2).symm.trans h0
    apply hh
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact injective_res_chartK C π K hF M 0 inf_le_left (h0.trans (map_zero _).symm)
    · exact injective_res_chartK C π K hF M 1 inf_le_right (h2.trans (map_zero _).symm)
  haveI := projective_sections M hUV
  obtain ⟨μ, hμ⟩ : ∃ μ : Module.Dual Γ(XK, U' ⊓ V') Γ(M, U' ⊓ V'),
      μ (M.presheaf.map (homOfLE (inf_le_left : U' ⊓ V' ≤ U')).op h.1.1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hW ((Module.forall_dual_apply_eq_zero_iff _ _).mp hcon)
  -- a `k`-point in the overlap of the charts at which `h` does not vanish
  let WC : C.Opens := π ⁻¹ᵁ (ProjectiveLine.U k 0 ⊓ ProjectiveLine.U k 1)
  have hWC : IsAffineOpen WC := (ProjectiveLine.isAffineOpen_U_inf k).preimage π
  haveI : Nonempty WC := nonempty_chart_inf π
  obtain ⟨xC, hx, -, hσ, hne⟩ := exists_point_appLE_ne_zero C hF WC hWC _ hμ
  set σx := secT (C ↘ Sk) xC hx (Spec K ↘ Sk)
  haveI := isClosedImmersion_of_section C (Spec K ↘ Sk) σx (secT_snd _ _ _ _)
  let D := RelEffCartier.ofSection C (Spec K ↘ Sk) σx (secT_snd _ _ _ _)
  let D₁ := RelEffCartier.ofSection C (𝟙 Sk) (secT (C ↘ Sk) xC hx (𝟙 Sk)) (secT_snd _ _ _ _)
  refine ⟨-D₁.picClass, ?_⟩
  rw [map_neg, map_picClass_ofSection C xC hx (Spec K ↘ Sk)]
  set M' := Scheme.Pic.rep (Scheme.Pic.mk M + -D.picClass)
  have e : M ≅ M' ⊗ D.lineBundle := by
    refine (Scheme.Pic.mk_eq_mk_iff.mp ?_).some
    rw [Scheme.Pic.mk_tensor, Scheme.Pic.mk_rep]
    change Scheme.Pic.mk M = Scheme.Pic.mk M + -D.picClass + D.picClass
    abel
  have hh0 : M.presheaf.map (homOfLE (inf_le_left : U' ⊓ V' ≤ U')).op h.1.1 ∉
      RingHom.ker (σx.appLE (U' ⊓ V') ⊤ hσ).hom •
        (⊤ : Submodule Γ(XK, U' ⊓ V') Γ(M, U' ⊓ V')) := by
    intro hmem
    apply hne
    have : μ (M.presheaf.map (homOfLE (inf_le_left : U' ⊓ V' ≤ U')).op h.1.1) ∈
        RingHom.ker (σx.appLE (U' ⊓ V') ⊤ hσ).hom := by
      refine Submodule.smul_induction_on (p := fun y ↦ μ y ∈
        RingHom.ker (σx.appLE (U' ⊓ V') ⊤ hσ).hom) hmem ?_ ?_
      · intro r hr y _
        rw [LinearMap.map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro y z hy hz
        rw [map_add]
        exact add_mem hy hz
    exact this
  obtain ⟨h1, h0⟩ := removePoint σx (secT_snd _ _ _ _) hF hU hV hUV hσ D
    (RelEffCartier.ofSection_ideal _ _ _ _) M' M e hM.1 h.2 hh0
  refine ⟨h1, ?_⟩
  have h0' : Module.finrank Γ(Spec K, ⊤) (cechModH0 (Spec K) M' (chartK C π K 0)
      (chartK C π K 1)) + 1 = d + 1 := by
    rw [← hM.2]
    exact h0
  change Module.finrank Γ(Spec K, ⊤) (cechModH0 (Spec K) M' (chartK C π K 0)
      (chartK C π K 1)) = d
  omega

/-- Iterating `goodK_removePoint`: from `h⁰ = d + 1` down to `h⁰ = 1`. -/
theorem goodK_one (hF : IsField Γ(Spec K, ⊤)) :
    ∀ (d : ℕ) (z : (XK).Pic), GoodK C π K (Scheme.Pic.rep z) (d + 1) →
      ∃ c : (pullback (C ↘ Sk) (𝟙 Sk)).Pic,
        GoodK C π K (Scheme.Pic.rep (z + Scheme.Pic.map (bcK C K) c)) 1 := by
  intro d
  induction d with
  | zero => exact fun z hz ↦ ⟨0, by rwa [map_zero, add_zero]⟩
  | succ d ih =>
    intro z hz
    obtain ⟨c, hc⟩ := goodK_removePoint C π K hF (Scheme.Pic.rep z) hz
    rw [Scheme.Pic.mk_rep] at hc
    obtain ⟨c', hc'⟩ := ih _ hc
    exact ⟨c + c', by rwa [map_add, ← add_assoc]⟩

end Field

section TwistInf

variable {Y Y₁ : Scheme.{u}} (p₁ : Y₁ ⟶ ProjectiveLine.scheme k)

/-- The chart coordinate `τ` restricted to the overlap of the charts. -/
abbrev tauW : Γ(Y₁, p₁ ⁻¹ᵁ ProjectiveLine.U k 0 ⊓ p₁ ⁻¹ᵁ ProjectiveLine.U k 1) :=
  Y₁.presheaf.map (homOfLE inf_le_left).op (chartτ p₁)

lemma isUnit_tauW : IsUnit (tauW p₁) := by
  refine IsUnit.of_mul_eq_one (Y₁.presheaf.map (homOfLE inf_le_right).op (chartσ p₁)) ?_
  exact chartτ_mul_chartσ p₁

lemma sup_chart_eq_top : p₁ ⁻¹ᵁ ProjectiveLine.U k 0 ⊔ p₁ ⁻¹ᵁ ProjectiveLine.U k 1 = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, ProjectiveLine.U_sup, Scheme.Hom.preimage_top]

/-- `𝒪(n · ∞) = p₁^* 𝒪_{ℙ¹}(n)`, glued from the charts with transition function `τⁿ`. -/
abbrev twistInf (n : ℕ) : Y₁.Modules :=
  twoSetTwist (SheafOfModules.unit Y₁.ringCatSheaf) (p₁ ⁻¹ᵁ ProjectiveLine.U k 0)
    (p₁ ⁻¹ᵁ ProjectiveLine.U k 1) (tauW p₁ ^ n)

instance (n : ℕ) : (twistInf p₁ n).IsInvertible :=
  isInvertible_twist (sup_chart_eq_top p₁) ((isUnit_tauW p₁).pow n)

/-- The section `x₀ⁿ = (1, σⁿ)` of `𝒪(n · ∞)`. -/
def twistInfSection (n : ℕ) : Γ(twistInf p₁ n, ⊤) :=
  twistSection 1 (chartσ p₁ ^ n) (by
    rw [map_one, map_pow, ← mul_pow, chartτ_mul_chartσ, one_pow])

variable (φ : Y ⟶ Y₁) (ρ : Y ⟶ ProjectiveLine.scheme k) (hρ : φ ≫ p₁ = ρ)

include hρ in
/-- The pulled-back section of `𝒪(n · ∞)` is a basis on `ρ⁻¹ D₊(x₀)` and `σⁿ` times a basis
on `ρ⁻¹ D₊(x₁)`. -/
theorem twistInf_pullback_data (n : ℕ) :
    ((Scheme.Modules.pullback φ).obj (twistInf p₁ n)).IsBasisOn (ρ ⁻¹ᵁ ProjectiveLine.U k 0)
        (((Scheme.Modules.pullback φ).obj (twistInf p₁ n)).presheaf.map (homOfLE le_top).op
          (pullbackSection φ (twistInfSection p₁ n))) ∧
      ∃ b : Γ((Scheme.Modules.pullback φ).obj (twistInf p₁ n), ρ ⁻¹ᵁ ProjectiveLine.U k 1),
        ((Scheme.Modules.pullback φ).obj (twistInf p₁ n)).IsBasisOn
          (ρ ⁻¹ᵁ ProjectiveLine.U k 1) b ∧
        ((Scheme.Modules.pullback φ).obj (twistInf p₁ n)).presheaf.map (homOfLE le_top).op
          (pullbackSection φ (twistInfSection p₁ n)) = chartσ ρ ^ n • b := by
  subst hρ
  have hu : IsUnit (tauW p₁ ^ n) := (isUnit_tauW p₁).pow n
  constructor
  · have h1 := isBasisOn_pullbackSection φ _ (isBasisOn_twistBasisLeft (V := p₁ ⁻¹ᵁ
      ProjectiveLine.U k 1) hu)
    have e : (twistInf p₁ n).presheaf.map (homOfLE (le_top : p₁ ⁻¹ᵁ ProjectiveLine.U k 0 ≤ ⊤)).op
        (twistInfSection p₁ n) = twistBasisLeft hu := by
      rw [twistInfSection, twistSection_res_left hu, one_smul]
    rw [← e, pullbackSection_res] at h1
    exact h1
  · refine ⟨pullbackSection φ (twistBasisRight (U := p₁ ⁻¹ᵁ ProjectiveLine.U k 0)
      (t := tauW p₁ ^ n)), isBasisOn_pullbackSection φ _ isBasisOn_twistBasisRight, ?_⟩
    calc _ = pullbackSection φ ((twistInf p₁ n).presheaf.map
          (homOfLE (le_top : p₁ ⁻¹ᵁ ProjectiveLine.U k 1 ≤ ⊤)).op (twistInfSection p₁ n)) :=
        (pullbackSection_res φ le_top _).symm
      _ = _ := by
        rw [twistInfSection, twistSection_res_right, pullbackSection_smul', map_pow]
        rfl

end TwistInf

section Field

variable (K : CommRingCat.{u}) [(Spec K).Over (Spec (CommRingCat.of k))]

local notation "XK" => pullback (C ↘ Sk) (Spec K ↘ Sk)

variable [PerfectField k] [IsCurveOver k C]

lemma nontrivial_sections_chartK (hF : IsField Γ(Spec K, ⊤)) (M : (XK).Modules)
    [M.IsInvertible] : ∃ u : Γ(M, chartK C π K 0), u ≠ 0 := by
  haveI := isDomain_chartK C π K hF 0
  haveI := invertible_sections M (isAffineOpen_chart (T₀ := Spec K) π 0)
  by_contra h
  push Not at h
  haveI : Subsingleton Γ(M, chartK C π K 0) := ⟨fun a b ↦ (h a).trans (h b).symm⟩
  have e := Module.Invertible.linearEquiv Γ(XK, chartK C π K 0) Γ(M, chartK C π K 0)
  haveI : Subsingleton (Module.Dual Γ(XK, chartK C π K 0) Γ(M, chartK C π K 0) ⊗[Γ(XK,
    chartK C π K 0)] Γ(M, chartK C π K 0)) := inferInstance
  exact not_subsingleton Γ(XK, chartK C π K 0) e.symm.toEquiv.subsingleton

/-- **Twisting by `𝒪(n · ∞)`** (Stacks, Lemma 44.6.5, Tag 0B9Y, first step): some twist of `M`
by a line bundle pulled back from `C ×_k k` has `H¹ = 0` and `h⁰ ≥ 1`. -/
theorem goodK_twist (hF : IsField Γ(Spec K, ⊤)) (M : (XK).Modules) [M.IsInvertible] :
    ∃ (c : (pullback (C ↘ Sk) (𝟙 Sk)).Pic) (d : ℕ),
      GoodK C π K (Scheme.Pic.rep (Scheme.Pic.mk M + Scheme.Pic.map (bcK C K) c)) (d + 1) := by
  letI := hF.toField
  let p₁ := pullback.fst (C ↘ Sk) (𝟙 Sk) ≫ π
  have hρ : bcK C K ≫ p₁ = pullback.fst (C ↘ Sk) (Spec K ↘ Sk) ≫ π := by
    rw [← Category.assoc, bcMap_fst]
  have hU : IsAffineOpen (chartK C π K 0) := isAffineOpen_chart (T₀ := Spec K) π 0
  have hV : IsAffineOpen (chartK C π K 1) := isAffineOpen_chart (T₀ := Spec K) π 1
  have hUV := isAffineOpen_chart_inf (T₀ := Spec K) π
  haveI := (finite_H0_H1_K C π K hF M).2
  obtain ⟨u, hu⟩ := nontrivial_sections_chartK C π K hF M
  let N : ℕ → (XK).Modules := fun n ↦ (Scheme.Modules.pullback (bcK C K)).obj (twistInf p₁ n)
  have hdata := fun n ↦ twistInf_pullback_data p₁ (bcK C K)
    (pullback.fst (C ↘ Sk) (Spec K ↘ Sk) ≫ π) hρ n
  obtain ⟨n, h1, x, hx, hx0⟩ := exists_twist_H1_eq_zero (S := Spec K) hU hV hUV
    (basicOpen_chartσ _) M hu N (fun n ↦ pullbackSection (bcK C K) (twistInfSection p₁ n))
    (fun n ↦ (hdata n).1) (fun n ↦ (hdata n).2)
  have e : Scheme.Pic.rep (Scheme.Pic.mk M + Scheme.Pic.map (bcK C K)
      (Scheme.Pic.mk (twistInf p₁ n))) ≅ M ⊗ N n := by
    refine (Scheme.Pic.mk_eq_mk_iff.mp ?_).some
    rw [Scheme.Pic.mk_rep, Scheme.Pic.mk_tensor, Scheme.Pic.map_mk]
  haveI := (finite_H0_H1_K C π K hF (M ⊗ N n)).1
  have hpos : 0 < Module.finrank Γ(Spec K, ⊤)
      (cechModH0 (Spec K) (M ⊗ N n) (chartK C π K 0) (chartK C π K 1)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨x, hx⟩, fun h ↦ hx0 (congrArg Subtype.val h)⟩
  refine ⟨Scheme.Pic.mk (twistInf p₁ n), Module.finrank Γ(Spec K, ⊤)
    (cechModH0 (Spec K) (M ⊗ N n) (chartK C π K 0) (chartK C π K 1)) - 1, ?_⟩
  rw [goodK_congr C π K e]
  exact ⟨h1, by omega⟩

variable [IsAlgClosed k]

/-- **Stacks, Lemma 44.6.5 (Tag 0B9Y)**, for line bundles: for every invertible sheaf on
`X_K` there is a line bundle on `C ×_k k` whose pullback twists it into the `F`-condition. -/
theorem exists_fCond_translate (hF : IsField Γ(Spec K, ⊤)) (z : (XK).Pic) :
    ∃ c : (pullback (C ↘ Sk) (𝟙 Sk)).Pic,
      FCond π (Spec K ↘ Sk) (Scheme.Pic.rep (Scheme.Pic.map (bcK C K) c + z)) := by
  obtain ⟨c₁, d, h₁⟩ := goodK_twist C π K hF (Scheme.Pic.rep z)
  rw [Scheme.Pic.mk_rep] at h₁
  obtain ⟨c₂, h₂⟩ := goodK_one C π K hF d _ h₁
  refine ⟨c₁ + c₂, fCond_of_goodK C π K hF ?_⟩
  rw [map_add, show ∀ a b c : (XK).Pic, a + b + c = c + a + b from fun a b c ↦ by abel]
  exact h₂

end Field

section Rep

variable [PerfectField k] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

local notation "G" => picSigma (C ↘ Sk) σ hσ

/-- On an affine scheme, the `F`-condition for `x` itself implies `x ∈ F`. -/
lemma picF_of_fPoint {T : Scheme.{u}} [IsAffine T] (x : (sigmaG G).obj (op T))
    (hx : fPoint σ hσ π x) : picF σ hσ π T x := by
  obtain ⟨U, hU⟩ := exists_opens_fPoint σ hσ π x
  have htop : Set.range (𝟙 T) ⊆ U :=
    (hU T (𝟙 T)).mp (by rwa [op_id, Functor.map_id_apply])
  intro T' _ h
  exact (hU T' h).mpr fun _ ⟨t, ht⟩ ↦ ht ▸ htop ⟨h t, rfl⟩

variable [IsAlgClosed k]

/-- **Every point of `Pic_{C/k,σ}` over a field has a translate in `F`** (Stacks,
Lemma 44.6.5, Tag 0B9Y): the hypothesis `hfield` of `isRepresentable_of_translate`. -/
theorem exists_picF_translate (K : CommRingCat.{u}) (hK : IsField K)
    (x : (sigmaG G).obj (op (Spec K))) :
    ∃ c : (picSigma (C ↘ Sk) σ hσ).obj (op (Over.mk (𝟙 Sk))), picF σ hσ π _ (translate G c x) := by
  obtain ⟨g, y⟩ := x
  have hF : IsField Γ(Spec K, ⊤) :=
    MulEquiv.isField hK (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv
  letI : (Spec K).Over Sk := ⟨g⟩
  obtain ⟨c, hc⟩ := exists_fCond_translate C π K hF (y : picSigmaGrp (C ↘ Sk) σ hσ g).1
  have hmem : c ∈ picSigmaGrp (C ↘ Sk) σ hσ (𝟙 Sk) := by
    rw [mem_picSigmaGrp]
    exact Subsingleton.elim _ _
  refine ⟨⟨c, hmem⟩, picF_of_fPoint C π σ hσ _ ?_⟩
  exact hc

end Rep

section Representable

variable [PerfectField k] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))

/-- **Representability of the Picard functor** (Stacks, Lemmas 44.6.5 and 44.5.1, Tags 0B9Y,
0B9Q; the case of a separably closed ground field of Stacks, Proposition 44.6.6, Tag 0B9Z): for
a curve `C` over a separably closed (perfect, hence algebraically closed) field `k` with a
rational point `σ`, the rigidified Picard functor `Pic_{C/k,σ}` is representable by a scheme. -/
theorem isRepresentable_picSigmaSch [IsSepClosed k] :
    (picSigmaSch (C ↘ Sk) σ hσ).IsRepresentable := by
  haveI : IsAlgClosed k := IsSepClosed.isAlgClosed_of_perfectField k
  obtain ⟨π₀, hπ⟩ := IsCurveOver.exists_finite_to_P1 k C
  let π : C ⟶ ProjectiveLine.scheme k := π₀
  haveI : IsFinite π := hπ
  have hG := isSheaf_picSigmaSch_curve k C σ hσ
  exact isRepresentable_of_translate (picSigma (C ↘ Sk) σ hσ) hG
    (isLocalPredicate_picF σ hσ π hG) (picF_open σ hσ π) (xiW C σ hσ π hG)
    (injective_xiW C σ hσ π hG) (picF_iff_exists_xiW C σ hσ π hG)
    (exists_picF_translate C π σ hσ)

end Representable

end CurvesJacobian
