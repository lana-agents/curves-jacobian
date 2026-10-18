/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Picard.PicDescent
import CurvesJacobian.Picard.H0BaseChange

/-!
# `Pic_{C/k,σ}(K) ⟶ Pic_{C/k,σ}(Ω)` is injective

Let `C` be a curve over a perfect field `k` with a rational point `σ`, and `K ⊆ Ω` fields
containing `k`.

* `CurvesJacobian.isEff_of_isEff_map`: a class `z ∈ Pic(C_K)` whose image in `Pic(C_Ω)` is
  effective is effective (if `Γ(C_K, z) = 0` then `Γ(C_Ω, z_Ω) = 0`, flat base change of the
  Čech `H⁰`, `subsingleton_chartH0_bcMap'`).
* **`CurvesJacobian.picRes_injective`**: the restriction `Pic_{C/k,σ}(K) ⟶ Pic_{C/k,σ}(Ω)` is
  injective. If `x ↦ 0`, let `D` be the unique effective divisor in `n·[σ_Ω]`
  (`exists_unique_effective`); both `n·[σ_K]` and `x + n·[σ_K]` are effective, with divisors
  `D₁`, `D₂` whose base changes are `D`; as `K`-points of `Hilb^e_{C/k}` they agree after
  `Spec Ω ⟶ Spec K`, hence `D₁ = D₂` (`eq_of_specMapAlg_comp_eq`) and `x = 0`.
* **`CurvesJacobian.jacPointsEquivInv`**: for `Ω / K` Galois, `J(K) ≅ J(Ω)^{Gal(Ω/K)}`, as
  groups (`J = Pic⁰_{C/k,σ}`).
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

noncomputable section

namespace CurvesJacobian

open Cech Belyi

variable {k : Type u} [Field k] [PerfectField k] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k))] [IsCurveOver k C] (σ : Spec (CommRingCat.of k) ⟶ C)
  (hσ : σ ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
  (K Ω : Type u) [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω]

local notation "Sk" => Spec (CommRingCat.of k)

/-- The base change `C_Ω ⟶ C_K`. -/
abbrev bcExt : pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) Ω) ⟶
    pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) K) :=
  bcMap (C ↘ Sk) (specMapAlg K Ω) _ _ (specMapAlg_comp_specAlgebraMap K Ω)

/-- **Effectivity descends along field extensions.** -/
theorem isEff_of_isEff_map {z : (pullback (C ↘ Sk) (specAlgebraMap (k₀ := k) K)).Pic}
    (hz : ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) Ω)),
      D.picClass = Scheme.Pic.map (bcExt C K Ω) z) :
    ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) K)),
      D.picClass = z := by
  letI : (Spec (CommRingCat.of K)).Over Sk := ⟨specAlgebraMap (k₀ := k) K⟩
  set π := curveToP1 k C
  have hFK := isField_ΓSpec' K
  by_contra hne
  have hsub : Subsingleton Γ(Scheme.Pic.rep z, ⊤) := subsingleton_of_not_isEff π hFK hne
  have hsubH : Subsingleton (chartH0 π (specAlgebraMap (k₀ := k) K) (Scheme.Pic.rep z)) :=
    (globalSectionsEquivH0 _ (Scheme.Pic.rep z) (chartOf_sup π _)).toEquiv.symm.subsingleton
  have hΩ := subsingleton_chartH0_bcMap' π hFK (specMapAlg K Ω) (specAlgebraMap (k₀ := k) Ω)
    (specMapAlg_comp_specAlgebraMap K Ω) (Scheme.Pic.rep z) hsubH
  obtain ⟨D, hD⟩ := hz
  letI : (Spec (CommRingCat.of Ω)).Over Sk := ⟨specAlgebraMap (k₀ := k) Ω⟩
  have hFΩ := isField_ΓSpec' Ω
  have he : Scheme.Pic.mk D.lineBundle = Scheme.Pic.mk
      ((Scheme.Modules.pullback (bcExt C K Ω)).obj (Scheme.Pic.rep z)) := by
    rw [← Scheme.Pic.map_mk, Scheme.Pic.mk_rep]
    exact hD
  obtain ⟨e⟩ := Scheme.Pic.mk_eq_mk_iff.mp he
  have hne' : sectionsIso (S := Spec (CommRingCat.of Ω)) e ⊤ D.canonicalSection ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff]
    exact canonicalSection_ne_zero hFΩ D
  apply hne'
  apply (globalSectionsEquivH0 (Spec (CommRingCat.of Ω)) _
    (chartOf_sup π (specAlgebraMap (k₀ := k) Ω))).injective
  exact @Subsingleton.elim _ hΩ _ _

omit [IsScalarTower k K Ω] in
/-- A divisor on `C_K` and its base change to `C_Ω`, as points of `Hilb^e_{C/k}`. -/
lemma exists_hilb_baseChange [IsScalarTower k K Ω] {e : ℕ}
    (D' : RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) K)))
    (hD' : ∀ t, D'.degree t = e) :
    ∃ (D'' : RelEffCartier (pullback.snd (C ↘ Sk) (specAlgebraMap (k₀ := k) Ω)))
      (hD'' : ∀ t, D''.degree t = e),
      D''.picClass = Scheme.Pic.map (bcExt C K Ω) D'.picClass ∧
      hilbCurveEquiv k C e _ (specMapAlg K Ω ≫ (hilbCurveEquiv k C e _).symm
        ⟨specAlgebraMap (k₀ := k) K, D', hD'⟩) = ⟨specAlgebraMap (k₀ := k) Ω, D'', hD''⟩ := by
  set a := (hilbCurveEquiv k C e _).symm ⟨specAlgebraMap (k₀ := k) K, D', hD'⟩
  have ha : hilbCurveEquiv k C e _ a = ⟨specAlgebraMap (k₀ := k) K, D', hD'⟩ :=
    Equiv.apply_symm_apply _ _
  obtain ⟨y, hy⟩ : ∃ y, hilbCurveEquiv k C e _ (specMapAlg K Ω ≫ a) = y := ⟨_, rfl⟩
  obtain ⟨g', D'', hD''⟩ := y
  have w : specMapAlg K Ω ≫ specAlgebraMap (k₀ := k) K = g' := by
    have h1 := hilbCurveEquiv_comp_fst k C (specMapAlg K Ω) a
    rw [hy, ha] at h1
    exact h1.symm
  have hideal := hilbCurveEquiv_comp_ideal' k C (specMapAlg K Ω) a _ ha _ hy w
  have hg' : g' = specAlgebraMap (k₀ := k) Ω := w.symm.trans (specMapAlg_comp_specAlgebraMap K Ω)
  subst hg'
  exact ⟨D'', hD'', (RelEffCartier.map_picClass_of_ideal_eq D' D'' _ hideal).symm, hy⟩

/-- **The restriction `Pic_{C/k,σ}(K) ⟶ Pic_{C/k,σ}(Ω)` is injective.** -/
theorem picRes_injective : Function.Injective (picRes C σ hσ K Ω) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  letI : (Spec (CommRingCat.of Ω)).Over Sk := ⟨specAlgebraMap (k₀ := k) Ω⟩
  set gΩ := specAlgebraMap (k₀ := k) Ω
  set gK := specAlgebraMap (k₀ := k) K
  have hF := isField_ΓSpec' Ω
  have hs : Scheme.Pic.map (bcExt C K Ω) (sigmaDiv σ hσ gK).picClass =
      (sigmaDiv σ hσ gΩ).picClass := map_picClass_sigmaDiv σ hσ _ _ _ _
  have hx' : Scheme.Pic.map (bcExt C K Ω) (x : (pullback (C ↘ Sk) gK).Pic) = 0 :=
    congrArg Subtype.val hx
  obtain ⟨n, D, hD, huniq⟩ : ∃ n : ℤ, ∃ D : RelEffCartier (pullback.snd (C ↘ Sk) gΩ),
      D.picClass = (0 : (pullback (C ↘ Sk) gΩ).Pic) + n • (sigmaDiv σ hσ gΩ).picClass ∧
      ∀ D' : RelEffCartier (pullback.snd (C ↘ Sk) gΩ), D'.picClass = D.picClass → D' = D :=
    exists_unique_effective (curveToP1 k C) σ hσ hF 0
  obtain ⟨D₁, hD₁⟩ := isEff_of_isEff_map C K Ω (z := n • (sigmaDiv σ hσ gK).picClass)
    ⟨D, by rw [hD, map_zsmul, hs, zero_add]⟩
  obtain ⟨D₂, hD₂⟩ := isEff_of_isEff_map C K Ω
    (z := (x : (pullback (C ↘ Sk) gK).Pic) + n • (sigmaDiv σ hσ gK).picClass)
    ⟨D, by rw [hD, map_add, map_zsmul, hs, hx']⟩
  haveI := subsingleton_of_isField (isField_ΓSpec' K)
  obtain ⟨t⟩ := nonempty_of_isField (isField_ΓSpec' K)
  have hdeg₁ : ∀ s, D₁.degree s = D₁.degree t := fun s ↦ by rw [Subsingleton.elim s t]
  have hdeg₂ : ∀ s, D₂.degree s = D₂.degree t := fun s ↦ by rw [Subsingleton.elim s t]
  obtain ⟨E₁, hE₁, hpic₁, hpt₁⟩ := exists_hilb_baseChange C K Ω D₁ hdeg₁
  obtain ⟨E₂, hE₂, hpic₂, hpt₂⟩ := exists_hilb_baseChange C K Ω D₂ hdeg₂
  have h₁ : E₁ = D := huniq E₁ (by rw [hpic₁, hD₁, map_zsmul, hs, hD, zero_add])
  have h₂ : E₂ = D := huniq E₂ (by rw [hpic₂, hD₂, map_add, map_zsmul, hs, hx', hD])
  obtain ⟨tΩ⟩ := nonempty_of_isField hF
  have hee : D₁.degree t = D₂.degree t := by
    rw [← hE₁ tΩ, ← hE₂ tΩ, h₁, h₂]
  have key : ∀ (e : ℕ) (hd₁ : ∀ s, D₁.degree s = e) (hd₂ : ∀ s, D₂.degree s = e),
      hilbCurveEquiv k C e _ (specMapAlg K Ω ≫ (hilbCurveEquiv k C e _).symm ⟨gK, D₁, hd₁⟩) =
        hilbCurveEquiv k C e _ (specMapAlg K Ω ≫ (hilbCurveEquiv k C e _).symm ⟨gK, D₂, hd₂⟩) →
      D₁ = D₂ := by
    intro e hd₁ hd₂ h
    have h' := eq_of_specMapAlg_comp_eq (Ω := Ω) ((hilbCurveEquiv k C e _).injective h)
    have h'' := (hilbCurveEquiv k C e _).symm.injective h'
    simp only [Sigma.mk.injEq, heq_eq_eq, Subtype.mk.injEq, true_and] at h''
    exact h''
  have hD12 : D₁ = D₂ := key _ hdeg₁ (fun s ↦ (hdeg₂ s).trans hee.symm) (by
    rw [hpt₁]
    have := exists_hilb_baseChange C K Ω D₂ (fun s ↦ (hdeg₂ s).trans hee.symm)
    obtain ⟨E₂', hE₂', hpic₂', hpt₂'⟩ := this
    rw [hpt₂']
    have : E₂' = E₁ :=
      (huniq E₂' (by rw [hpic₂', hD₂, map_add, map_zsmul, hs, hx', hD])).trans h₁.symm
    subst this
    rfl)
  apply Subtype.ext
  have h12 := congrArg RelEffCartier.picClass hD12
  rw [hD₁, hD₂] at h12
  rw [AddSubgroup.coe_zero]
  have := congrArg (· - n • (sigmaDiv σ hσ gK).picClass) h12
  simpa using this.symm


variable [IsGalois K Ω]

/-- **`Pic_{C/k,σ}(K) ≅ Pic_{C/k,σ}(Ω)^{Gal(Ω/K)}`** for a Galois extension `Ω / K`. -/
def picPtEquivInv : picPt C σ hσ K ≃+ picInv C σ hσ K Ω :=
  AddEquiv.ofBijective ((picRes C σ hσ K Ω).codRestrict _ (picRes_mem_picInv C σ hσ K Ω))
    ⟨fun x y h ↦ picRes_injective C σ hσ K Ω (congrArg Subtype.val h), fun c ↦ by
      obtain ⟨x, hx⟩ := exists_picRes_eq C σ hσ K Ω c.1 c.2
      exact ⟨x, Subtype.ext hx⟩⟩

/-- **The `K`-points of the Jacobian are the Galois invariant `Ω`-points**:
`J(K) ≅ J(Ω)^{Gal(Ω/K)}` for a Galois extension `Ω / K` of fields containing `k`
(`J(K) = Pic⁰_{C/k,σ}(K)`). -/
def jacPointsEquivInv : jacPoints C σ hσ K ≃+ (jacPoints C σ hσ Ω ⊓ picInv C σ hσ K Ω :
    AddSubgroup (picPt C σ hσ Ω)) :=
  AddEquiv.ofBijective (((picRes C σ hσ K Ω).comp (jacPoints C σ hσ K).subtype).codRestrict _
    fun x ↦ AddSubgroup.mem_inf.mpr
      ⟨picRes_mem_jacPoints C σ hσ K Ω x.2, picRes_mem_picInv C σ hσ K Ω x⟩)
    ⟨fun x y h ↦ Subtype.ext (picRes_injective C σ hσ K Ω (congrArg Subtype.val h)), fun c ↦ by
      obtain ⟨x, hx₀, hx⟩ := exists_jacPoints_picRes_eq C σ hσ K Ω c.1
        (AddSubgroup.mem_inf.mp c.2).1 (AddSubgroup.mem_inf.mp c.2).2
      exact ⟨⟨x, hx₀⟩, Subtype.ext hx⟩⟩

@[simp]
lemma coe_jacPointsEquivInv (x : jacPoints C σ hσ K) :
    ((jacPointsEquivInv C σ hσ K Ω x : picPt C σ hσ Ω)) = picRes C σ hσ K Ω x := rfl

end CurvesJacobian
