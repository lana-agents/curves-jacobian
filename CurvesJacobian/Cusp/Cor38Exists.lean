/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.CandidateLiftX1
import CurvesJacobian.Cusp.CandidateLiftX2
import CurvesJacobian.Cusp.BelyiGaloisCover
import CurvesJacobian.Cusp.BelyiChainCusp
import CurvesJacobian.Cusp.ExtensionIso

/-!
# [AbsTopII] Corollary 3.8, existence (MR8, round 28, step (N3))

`Topics in Absolute Anabelian Geometry II.txt` l.4794–4842 (Corollary 3.8): for an isomorphism
`φ : Π₁ ≅ Π₂` and a nonempty open `U_{X₁} ⊆ X₁` there are a nonempty open `U_{X₂} ⊆ X₂` and an
isomorphism `φ_U : Π_{U_{X₁}} ≅ Π_{U_{X₂}}` compatible with `φ` relative to the natural
surjections `Π_{U_{Xᵢ}} ↠ Πᵢ` ("follows immediately from Corollary 3.7", l.4838–4839).

Here `Xᵢ = CXᵢ.U` are affine hyperbolic curves over number fields, `X₁` of strictly Belyi type
with a Galois cover `V → X₁` (`GaloisBelyiInput`, the lead decision for Cor 3.7 (b)), `φ` is an
isomorphism of the cuspidal extensions `arithmeticExt` (`CuspidalExt.Iso`), `Π_{U_X} ↠ Π_X` is
`cor38Fill` (for any choice of the change of base point `αᵢ`), and the only DGC input is the
explicit hypothesis `hDGC` (the rel-isom-DGC over all number fields).

**Main theorem** (`CurvesJacobian.Cusp.cor38_exists`).

Proof (the algorithmic route of Cor 3.7):
* `exists_belyiCandidate_galois`: Belyi data `D` over a field normal over `K₁` with
  `U = V ×_{X₁} U_{X₁}` a stage of its run of fillings and `V → X₁` Galois; the Belyi candidate
  `x₁ = (Π_U ↠ Π_V ↪ Π₁)` (`exists_belyiChain_cor38₂`).
* `cor38_side1`: `Π_U` is the preimage `H₁` of `Π_V` under `Π_{U_{X₁}} ↠ Π₁`, `Π_V ⊴ Π₁`,
  automorphisms of `Π_V` normalised by `Π₁` lift to `Π_U`, and (via a geometric model of `x₁`
  and the DGC) every automorphism of `H₁` over `Π₁` is inner from `ker(Π_{U_{X₁}} ↠ Π₁)`.
* `cor38_side2`: the transported candidate `x₂ = φ_*(x₁)` is geometric
  (`PiChain.IsBelyiType.exists_cover_fill`): `Π_U ≅ Π_Y`, `Π_V ≅ Π_{Y'}`, `q : Y' ⟶ X₂` finite
  étale, Galois (normal image) with deck transformations lifting to `Π_Y`; so `Y ⊆ Y'` descends to
  a nonempty open `U_{X₂} ⊆ X₂` (`exists_descent_of_lift`), and `Π_U` is the preimage `H₂` of
  `Π_V` under `Π_{U_{X₂}} ↠ Π₂` (Cor 3.7 (b)).
* `exists_continuousMulEquiv_of_models₂` (group theory): `H₁ ≅ Π_U ≅ H₂` extends to
  `Π_{U_{X₁}} ≅ Π_{U_{X₂}}` over `φ` (`exists_continuousMulEquiv_ext_of_unique`), after
  correcting by inner automorphisms.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale Belyi
  Belyi.Anabelian Pi1.Profinite PreGaloisCategory

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CurvesJacobian.Cusp

/-! ### Group theory -/

section GroupTheory

/-- Conjugation by `g` as a continuous automorphism of a topological group. -/
def conjContField₂ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G) :
    G ≃ₜ* G where
  toFun h := g * h * g⁻¹
  invFun h := g⁻¹ * h * g
  left_inv h := by simp [mul_assoc]
  right_inv h := by simp [mul_assoc]
  map_mul' a b := by simp [mul_assoc]
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

/-- **Extension of `H₁ ≅ Π_U ≅ H₂` over `Φ`** (group theory of [AbsTopII] Cor 3.8): for
surjections `fᵢ : Eᵢ ↠ Pᵢ`, `Φ : P₁ ≅ P₂`, `e₂ = Φ ∘ e₁` with `im e₁` normal, and
identifications `Jᵢ : P_U ≅ Hᵢ = fᵢ⁻¹(im eᵢ)` with `fᵢ ∘ Jᵢ = conj(cᵢ) ∘ eᵢ ∘ s`, if the `Hᵢ`
are open and centre-free and all automorphisms of `Hᵢ` over `Pᵢ` are inner from `ker fᵢ`, then
there is `φ : E₁ ≃ₜ* E₂` with `f₂ ∘ φ = Φ ∘ f₁`. -/
theorem exists_continuousMulEquiv_of_models₂ {E₁ E₂ P₁ P₂ PU PV : Type*} [Group E₁] [Group E₂]
    [TopologicalSpace E₁] [IsTopologicalGroup E₁] [TopologicalSpace E₂] [IsTopologicalGroup E₂]
    [Group P₁] [Group P₂] [Group PU] [TopologicalSpace PU] [Group PV]
    {f₁ : E₁ →* P₁} {f₂ : E₂ →* P₂} (hf₁ : Function.Surjective f₁)
    (hf₂ : Function.Surjective f₂) (Φ : P₁ ≃* P₂) (s : PU → PV) (e₁ : PV →* P₁)
    (e₂ : PV →* P₂) (he : ∀ v, e₂ v = Φ (e₁ v)) (hN₁ : e₁.range.Normal)
    (J₁ : PU ≃ₜ* e₁.range.comap f₁) (c₁ : P₁) (hJ₁ : ∀ u, f₁ (J₁ u) = c₁ * e₁ (s u) * c₁⁻¹)
    (J₂ : PU ≃ₜ* e₂.range.comap f₂) (c₂ : P₂) (hJ₂ : ∀ u, f₂ (J₂ u) = c₂ * e₂ (s u) * c₂⁻¹)
    (hH₁ : IsOpen ((e₁.range.comap f₁ : Subgroup E₁) : Set E₁))
    (hH₂ : IsOpen ((e₂.range.comap f₂ : Subgroup E₂) : Set E₂))
    (hZ₁ : Subgroup.center (e₁.range.comap f₁) = ⊥)
    (hZ₂ : Subgroup.center (e₂.range.comap f₂) = ⊥)
    (hU₁ : ∀ β : e₁.range.comap f₁ ≃ₜ* e₁.range.comap f₁, (∀ h, f₁ (β h) = f₁ h) →
      ∃ n : E₁, f₁ n = 1 ∧ ∀ h, (β h : E₁) = n * h * n⁻¹)
    (hU₂ : ∀ β : e₂.range.comap f₂ ≃ₜ* e₂.range.comap f₂, (∀ h, f₂ (β h) = f₂ h) →
      ∃ n : E₂, f₂ n = 1 ∧ ∀ h, (β h : E₂) = n * h * n⁻¹) :
    ∃ φ : E₁ ≃ₜ* E₂, ∀ x, f₂ (φ x) = Φ (f₁ x) := by
  have hr : e₂.range = e₁.range.map Φ.toMonoidHom := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨e₁ v, ⟨v, rfl⟩, (he v).symm⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, he v⟩
  haveI : e₁.range.Normal := hN₁
  haveI hN₂ : e₂.range.Normal := by
    rw [hr]
    exact Subgroup.Normal.map hN₁ _ Φ.surjective
  have hN : e₁.range.map (Φ.trans (MulAut.conj (c₂ * (Φ c₁)⁻¹))).toMonoidHom = e₂.range := by
    ext z
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      change MulAut.conj (c₂ * (Φ c₁)⁻¹) (Φ (e₁ v)) ∈ e₂.range
      rw [MulAut.conj_apply, ← he]
      exact hN₂.conj_mem _ ⟨v, rfl⟩ _
    · intro hz
      obtain ⟨v, hv⟩ := hN₂.conj_mem _ hz (c₂ * (Φ c₁)⁻¹)⁻¹
      refine ⟨e₁ v, ⟨v, rfl⟩, ?_⟩
      change MulAut.conj (c₂ * (Φ c₁)⁻¹) (Φ (e₁ v)) = z
      rw [MulAut.conj_apply, ← he]
      rw [show e₂ v = _ from hv]
      group
  have ha : ∀ h, f₂ ((J₁.symm.trans J₂) h) =
      (Φ.trans (MulAut.conj (c₂ * (Φ c₁)⁻¹))) (f₁ h) := fun h ↦ by
    have e1 : (h : E₁) = J₁ (J₁.symm h) := by rw [ContinuousMulEquiv.apply_symm_apply]
    change f₂ (J₂ (J₁.symm h)) = MulAut.conj (c₂ * (Φ c₁)⁻¹) (Φ (f₁ h))
    rw [hJ₂, e1, hJ₁, MulAut.conj_apply, map_mul, map_mul, map_inv, ← he]
    group
  obtain ⟨φ, hφ, -⟩ := exists_continuousMulEquiv_ext_of_unique
    (Φ := Φ.trans (MulAut.conj (c₂ * (Φ c₁)⁻¹))) (a := J₁.symm.trans J₂) hf₁ hf₂ hN hH₁ hH₂ ha
    hZ₁ hZ₂ hU₁ hU₂
  obtain ⟨n, hn⟩ := hf₂ (Φ c₁ * c₂⁻¹)
  refine ⟨φ.trans (conjContField₂ n), fun x ↦ ?_⟩
  change f₂ (n * φ x * n⁻¹) = Φ (f₁ x)
  rw [map_mul, map_mul, map_inv, hn, hφ]
  change Φ c₁ * c₂⁻¹ * MulAut.conj (c₂ * (Φ c₁)⁻¹) (Φ (f₁ x)) * (Φ c₁ * c₂⁻¹)⁻¹ = Φ (f₁ x)
  rw [MulAut.conj_apply]
  group

end GroupTheory

/-! ### The filling map `Π_{U_X} ↠ Π_X` -/

section Fill

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (CX : HypCurve K)
  (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U)
  (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- `Π_{U_X} ↠ Π_X` is surjective. -/
theorem cor38Fill_surjective₂ : Function.Surjective (cor38Fill Ω CX hcX UX hUX hne α₀) :=
  fun z ↦ by
    obtain ⟨w, hw⟩ := fillMap_surjective Ω (subCurve CX UX hUX hne)
      (compl_nonempty_of_le hUX hcX) hUX hcX
      (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
        α₀) z)
    exact ⟨w, (congrArg (autContinuousMulEquivOfIso _).symm hw).trans
      ((autContinuousMulEquivOfIso _).symm_apply_apply z)⟩

/-- `Π_{U_X} ↠ Π_X` is continuous. -/
theorem continuous_cor38Fill₂ : Continuous (cor38Fill Ω CX hcX UX hUX hne α₀) :=
  (autContinuousMulEquivOfIso (fiberIsoMap (baseChangeSpec K Ω Γ(CX.Xbar, CX.U)) rfl rfl
    α₀)).symm.continuous.comp
      (fillMap Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX).continuous

/-- The preimage under `Π_{U_X} ↠ Π_X` of an open subgroup is open. -/
theorem isOpen_comap_cor38Fill₂ {N : Subgroup (arithmeticExt Ω CX hcX).Pi}
    (hN : IsOpen (N : Set (arithmeticExt Ω CX hcX).Pi)) :
    IsOpen ((N.comap (cor38Fill Ω CX hcX UX hUX hne α₀) : Subgroup _) :
      Set (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi) :=
  hN.preimage (continuous_cor38Fill₂ Ω CX hcX UX hUX hne α₀)

/-- The preimage under `Π_{U_X} ↠ Π_X` of an open subgroup has trivial centre. -/
theorem center_comap_cor38Fill₂ {N : Subgroup (arithmeticExt Ω CX hcX).Pi}
    (hN : IsOpen (N : Set (arithmeticExt Ω CX hcX).Pi)) :
    Subgroup.center (N.comap (cor38Fill Ω CX hcX UX hUX hne α₀)) = ⊥ :=
  CuspidalExt.center_eq_bot_of_isOpen _ (isOpen_comap_cor38Fill₂ Ω CX hcX UX hUX hne α₀ hN)

end Fill

/-! ### Transfer of the Galois property along an equality of covers -/

lemma isGalois_coverObj_congr₂ {X Y : Scheme.{u}} [IsIntegral X] {f g : Y ⟶ X}
    [IsFiniteEtale f] [IsFiniteEtale g] (e : f = g) (H : IsGalois (coverObj f)) :
    IsGalois (coverObj g) := by
  subst e
  exact H

/-! ### Belyi data over a normal field with `V → X` Galois -/

section Glue

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω] {CX : HypCurve K} (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

set_option maxHeartbeats 1000000 in
-- matching the existential of `exists_belyiCandidate_normal` (Belyi data over `M'.1`) is slow
/-- **Belyi data with `V → X` Galois** ([AbsTopII] Cor 3.7 (a), (b)): for a strictly Belyi
input with Galois `V → X` and a nonempty open `U_X ⊆ X`, Belyi data `D` over a finite extension
`M'` (normal over `K`), `m ≤ r` with `U = UW_{r-m} = V ×_X U_X`, the identification of the
candidate with `π₁ᵉᵗ(U) ↠ π₁ᵉᵗ(V) → Π_X`, and `D.FV : V_{M'} ⟶ X` Galois. -/
theorem exists_belyiCandidate_galois (S : GaloisBelyiInput CX M) (UX : CX.Xbar.Opens)
    (hUX : UX ≤ CX.U) (hUXne : (UX : Set CX.Xbar).Nonempty) :
    ∃ (M' : IntermediateField.FinSub M Ω) (D : BelyiData (M := M'.1) CX) (m : ℕ) (hm : m ≤ D.r)
      (hVa : IsAffineOpen (D.UW (Fin.last D.r))),
      D.UW ⟨D.r - m, by omega⟩ =
        hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)) ∧
      (haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV)) ∧
      ∃ (eU : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiU ≃ₜ*
          π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW ⟨D.r - m, by omega⟩) ≫
            baseChangeSpec M'.1 Ω Γ(D.CW.Xbar, D.UW ⟨D.r - m, by omega⟩)))
        (eV : (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).PiV ≃ₜ*
          π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
            baseChangeSpec M'.1 Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r)))),
        (∀ x, eV ((PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).surj
            x) = D.stepHom Ω ⟨D.r - m, by omega⟩ (Fin.last D.r) (Fin.le_last _) (eU x)) ∧
          ∀ y, (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm).emb y =
            D.φ₄ Ω hcX (eV y) := by
  obtain ⟨M', D, m, hm, hVa, hU, -, hst, ⟨aV, hsq, hFV⟩, hrest⟩ :=
    exists_belyiCandidate_normal Ω hcX S.toStrictlyBelyiInput UX hUX hUXne
  refine ⟨M', D, m, hm, hVa, hU, ?_, hrest⟩
  haveI := isIntegral_specSections CX hcX
  haveI := isFiniteEtale_of_isPullback_sKU hsq
  exact isGalois_coverObj_congr₂ hFV.symm
    (isGalois_coverObj_comp_of_normal Ω CX hcX S.CV S.hcV S.FV S.hFV S.isGalois
      (fun σ x ↦ ⟨⟨σ (x : Ω), hst σ (x : Ω) x.2⟩, rfl⟩) D.CV D.hcV aV hsq)

end Glue

/-! ### The `X₁` side -/

section Side1

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω]
  (CX : HypCurve K) (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens)
  (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))
  (D : BelyiData (M := M) CX) (i : Fin (D.r + 1)) (hVa : IsAffineOpen (D.UW (Fin.last D.r)))
  (hU : D.UW i = hVa.fromSpec ''ᵁ (D.FV ⁻¹ᵁ ((isAffineOpen_U CX hcX).fromSpec ⁻¹ᵁ UX)))

attribute [local instance] isAlgClosure_of_isAlgebraic

include hVa hU in
/-- **[AbsTopII] Cor 3.8, the `X₁` side.** For Belyi data with `U = UW_i = V ×_X U_X`,
`V → X` Galois, a candidate `x` identified with `π₁ᵉᵗ(U) ↠ π₁ᵉᵗ(V) → Π_X`, and a geometric
model `Π_C ≅ x.PiU`, `Π_{C'} ≅ x.PiV` of `x.surj` as a filling `C ⊆ C'`: `im(x.emb)` is
normal, automorphisms of `x.PiV` normalised by `Π_X` lift to `x.PiU`, `x.PiU` is identified with
`H = (im x.emb).comap (Π_{U_X} ↠ Π_X)` up to conjugation, and every continuous automorphism of
`H` over `Π_X` is inner from `ker(Π_{U_X} ↠ Π_X)`. -/
theorem cor38_side1 (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hgal : haveI := isIntegral_specSections CX hcX; IsGalois (coverObj D.FV))
    (x : CuspCandidate (arithmeticExt Ω CX hcX))
    (eU : x.PiU ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW i) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW i)))
    (eV : x.PiV ≃ₜ* π₁ᵉᵗ(fillPoint Ω D.CW D.hcW (D.hleW (Fin.last D.r)) ≫
      baseChangeSpec M Ω Γ(D.CW.Xbar, D.UW (Fin.last D.r))))
    (hs : ∀ u, eV (x.surj u) = D.stepHom Ω i (Fin.last D.r) (Fin.le_last _) (eU u))
    (he : ∀ y, x.emb y = D.φ₄ Ω hcX (eV y))
    {M₁ : Type u} [Field M₁] [NumberField M₁] [Algebra M₁ Ω] [Algebra.IsAlgebraic M₁ Ω]
    (C : HypCurve M₁) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (ι : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M₁ Ω Γ(C.Xbar, C.U)) →ₜ* x.PiU)
    (hι : Function.Bijective ι) {U' : C.Xbar.Opens} (h : C.U ≤ U')
    (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
    (hyp : haveI := IsCurveOver.isIntegral M₁ C.Xbar
      2 < 2 * Anabelian.curveGenus M₁ C.Xbar + cuspDegree M₁ C.Xbar U')
    (ε : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M₁ Ω Γ(C.Xbar, U')) ≃ₜ*
      x.PiV)
    (hε : ∀ σ, x.surj (ι σ) = ε (fillPiHom Ω C hc h hc' hyp σ)) :
    x.emb.toMonoidHom.range.Normal ∧
      (∀ (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω CX hcX).Pi),
        (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
          ∃ ψ : x.PiU ≃ₜ* x.PiU, ∀ u, x.surj (ψ u) = B (x.surj u)) ∧
      ∃ (k : (arithmeticExt Ω CX hcX).Pi)
        (J : x.PiU ≃ₜ* x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀)),
        (∀ u, cor38Fill Ω CX hcX UX hUX hne α₀ (J u) = k * x.emb (x.surj u) * k⁻¹) ∧
        ∀ β : x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀) ≃ₜ*
            x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α₀),
          (∀ z, cor38Fill Ω CX hcX UX hUX hne α₀ (β z) = cor38Fill Ω CX hcX UX hUX hne α₀ z) →
          ∃ n : (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi,
            cor38Fill Ω CX hcX UX hUX hne α₀ n = 1 ∧
              ∀ z, (β z : (arithmeticExt Ω (subCurve CX UX hUX hne)
                (compl_nonempty_of_le hUX hcX)).Pi) = n * z * n⁻¹ := by
  have hN : x.emb.toMonoidHom.range.Normal := by
    rw [candidate_range_emb Ω CX hcX D x eV he]
    exact cor37b_normal Ω CX hcX D.CV D.hcV D.FV hgal
  refine ⟨hN, fun B g hB ↦ exists_candidate_lift Ω CX hcX UX hUX hne α₀ D i hVa hU hgal x eU eV
    hs he B g hB, ?_⟩
  obtain ⟨c, J, hJ⟩ := exists_candidate_comap_equiv Ω CX hcX UX hUX hne α₀ D i hVa hU hgal x eU
    eV hs he
  obtain ⟨ιe, hιe⟩ : ∃ ιe : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M₁ Ω Γ(C.Xbar, C.U)) ≃ₜ*
      x.PiU, ∀ y, ιe y = ι y := ⟨continuousMulEquivOfBijective ι hι, fun _ ↦ rfl⟩
  have hJ₀ : ∀ y, cor38Fill Ω CX hcX UX hUX hne α₀ ((ιe.trans J) y) =
      c * x.emb (ε (fillPiHom Ω C hc h hc' hyp y)) * c⁻¹ := fun y ↦ by
    change cor38Fill Ω CX hcX UX hUX hne α₀ (J (ιe y)) = _
    rw [hJ, hιe, hε]
  refine ⟨c, J, hJ, fun β hβ ↦ ?_⟩
  exact exists_conj_of_model_fill (hDGC M₁) (ιe.trans J)
    (x.emb.toMonoidHom.comp ε.toMulEquiv.toMonoidHom) (x.emb_injective.comp ε.injective) c hJ₀
    β hβ

end Side1

section Side1Exists

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω]
  {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
  [Algebra.IsAlgebraic M Ω]
  (CX : HypCurve K) (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty) (UX : CX.Xbar.Opens)
  (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty)
  (α₀ : fiber (basePoint Ω CX hcX) ≅
    fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **The `X₁` side of [AbsTopII] Cor 3.8, existence**: a Belyi-type chain of `Π_X` with a
terminal isomorphism and an infinite cusp image at `Π_V`, and `m ≤ r`, whose candidate
`Π_U ↠ Π_V ↪ Π_X` has normal `Π_V`, the lifting property, `Π_U ≅ H = (Π_V).comap(Π_{U_X} ↠ Π_X)`
up to conjugation, and automorphisms of `H` over `Π_X` inner from the kernel. -/
theorem exists_belyiChain_cor38₂
    (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (S : GaloisBelyiInput CX M) :
    ∃ (c : PiChain (arithmeticExt Ω CX hcX)) (l r : ℕ) (hc : c.IsBelyiType l r)
      (t : c.TerminalIso (PiChain.trivial _))
      (_ : (c.objN (l + r + 3) (by have := hc.len_eq; omega)).HasInfCusp) (m : ℕ) (hm : m ≤ r),
      (PiChain.belyiCandidate hc t m hm).emb.toMonoidHom.range.Normal ∧
      (∀ (B : (PiChain.belyiCandidate hc t m hm).PiV ≃ₜ* (PiChain.belyiCandidate hc t m hm).PiV)
        (g : (arithmeticExt Ω CX hcX).Pi),
        (∀ v, (PiChain.belyiCandidate hc t m hm).emb (B v) =
          g * (PiChain.belyiCandidate hc t m hm).emb v * g⁻¹) →
          ∃ ψ : (PiChain.belyiCandidate hc t m hm).PiU ≃ₜ* (PiChain.belyiCandidate hc t m hm).PiU,
            ∀ u, (PiChain.belyiCandidate hc t m hm).surj (ψ u) =
              B ((PiChain.belyiCandidate hc t m hm).surj u)) ∧
      ∃ (k : (arithmeticExt Ω CX hcX).Pi)
        (J : (PiChain.belyiCandidate hc t m hm).PiU ≃ₜ*
          (PiChain.belyiCandidate hc t m hm).emb.toMonoidHom.range.comap
            (cor38Fill Ω CX hcX UX hUX hne α₀)),
        (∀ u, cor38Fill Ω CX hcX UX hUX hne α₀ (J u) =
          k * (PiChain.belyiCandidate hc t m hm).emb
            ((PiChain.belyiCandidate hc t m hm).surj u) * k⁻¹) ∧
        ∀ β : (PiChain.belyiCandidate hc t m hm).emb.toMonoidHom.range.comap
              (cor38Fill Ω CX hcX UX hUX hne α₀) ≃ₜ*
            (PiChain.belyiCandidate hc t m hm).emb.toMonoidHom.range.comap
              (cor38Fill Ω CX hcX UX hUX hne α₀),
          (∀ z, cor38Fill Ω CX hcX UX hUX hne α₀ (β z) = cor38Fill Ω CX hcX UX hUX hne α₀ z) →
          ∃ n : (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi,
            cor38Fill Ω CX hcX UX hUX hne α₀ n = 1 ∧
              ∀ z, (β z : (arithmeticExt Ω (subCurve CX UX hUX hne)
                (compl_nonempty_of_le hUX hcX)).Pi) = n * z * n⁻¹ := by
  obtain ⟨M', D, m, hm, hVa, hU, hgal, eU, eV, hs, he⟩ :=
    exists_belyiCandidate_galois Ω hcX S UX hUX hne
  obtain ⟨D₁, hD₁, U', h, hc', hyp, ε, hε, -⟩ := (D.isBelyiType Ω hcX).exists_cover_fill
    (D.terminalIso Ω hcX) hDGC (D.hasInfCusp_V Ω hcX) m hm
  exact ⟨(D.path Ω hcX).toPiChain, D.l, D.r, D.isBelyiType Ω hcX, D.terminalIso Ω hcX,
    D.hasInfCusp_V Ω hcX, m, hm,
    cor38_side1 Ω CX hcX UX hUX hne α₀ D ⟨D.r - m, by omega⟩ hVa hU hDGC hgal
      (PiChain.belyiCandidate (D.isBelyiType Ω hcX) (D.terminalIso Ω hcX) m hm) eU eV hs he
      D₁.Y D₁.hY D₁.ι ⟨D₁.inj, hD₁⟩ h hc' hyp ε hε⟩

end Side1Exists

/-! ### The `X₂` side -/

section Side2

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] (CX : HypCurve K)
  (hcX : (CX.U : Set CX.Xbar)ᶜ.Nonempty)

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopII] Cor 3.8, the `X₂` side.** A candidate `x = (Π_U ↠ Π_V ↪ Π_X)` with normal
`Π_V` and the lifting property, which is geometric (`Π_C ≅ Π_U`, `Π_{C'} ≅ Π_V` for a filling
`C ⊆ C'`, `Π_V ↪ Π_X` induced by a finite étale `q : C' ⟶ X` over `Spec K`), determines a
nonempty open `U_X ⊆ X` (the descent of `C ⊆ C'`) such that `Π_U` is identified with
`H = (im x.emb).comap (Π_{U_X} ↠ Π_X)` up to conjugation, and every continuous automorphism of
`H` over `Π_X` is inner from `ker(Π_{U_X} ↠ Π_X)`. -/
theorem cor38_side2 (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (x : CuspCandidate (arithmeticExt Ω CX hcX)) (hN : x.emb.toMonoidHom.range.Normal)
    (hL : ∀ (B : x.PiV ≃ₜ* x.PiV) (g : (arithmeticExt Ω CX hcX).Pi),
      (∀ v, x.emb (B v) = g * x.emb v * g⁻¹) →
        ∃ ψ : x.PiU ≃ₜ* x.PiU, ∀ u, x.surj (ψ u) = B (x.surj u))
    {M : Type u} [Field M] [NumberField M] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω]
    [FiniteDimensional K M] [Algebra.IsAlgebraic M Ω]
    (C : HypCurve M) (hc : (C.U : Set C.Xbar)ᶜ.Nonempty)
    (ι : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) →ₜ* x.PiU)
    (hι : Function.Bijective ι) {U' : C.Xbar.Opens} (h : C.U ≤ U')
    (hc' : (U' : Set C.Xbar)ᶜ.Nonempty)
    (hyp : haveI := IsCurveOver.isIntegral M C.Xbar
      2 < 2 * Anabelian.curveGenus M C.Xbar + cuspDegree M C.Xbar U')
    (ε : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) ≃ₜ*
      x.PiV)
    (hε : ∀ σ, x.surj (ι σ) = ε (fillPiHom Ω C hc h hc' hyp σ))
    (q : Spec Γ(C.Xbar, U') ⟶ Spec Γ(CX.Xbar, CX.U)) [IsFiniteEtale q]
    (hq : IsConjInduced q (fun τ ↦ x.emb (ε τ) :
      π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) →
        π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U))))
    (hqK : q ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(CX.Xbar, CX.U))) =
      Spec.map (CommRingCat.ofHom (algebraMap M Γ(C.Xbar, U'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M))) :
    ∃ (UX : CX.Xbar.Opens) (hUX : UX ≤ CX.U) (hne : (UX : Set CX.Xbar).Nonempty),
      ∀ α : fiber (basePoint Ω CX hcX) ≅
          fiber (fillPoint Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) hUX),
      ∃ (k : (arithmeticExt Ω CX hcX).Pi)
        (J : x.PiU ≃ₜ* x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α)),
        (∀ u, cor38Fill Ω CX hcX UX hUX hne α (J u) = k * x.emb (x.surj u) * k⁻¹) ∧
        ∀ β : x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α) ≃ₜ*
            x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α),
          (∀ z, cor38Fill Ω CX hcX UX hUX hne α (β z) = cor38Fill Ω CX hcX UX hUX hne α z) →
          ∃ n : (arithmeticExt Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX)).Pi,
            cor38Fill Ω CX hcX UX hUX hne α n = 1 ∧
              ∀ z, (β z : (arithmeticExt Ω (subCurve CX UX hUX hne)
                (compl_nonempty_of_le hUX hcX)).Pi) = n * z * n⁻¹ := by
  haveI := isIntegral_specSections CX hcX
  haveI : IsIntegral (Spec (CommRingCat.of Γ(C.Xbar, U'))) :=
    isIntegral_specSections (fillCurve C h hyp) hc'
  have hgal : IsGalois (coverObj q) :=
    isGalois_of_isConjInduced_normal ε.toMulEquiv.toMonoidHom ε.surjective x.emb.toMonoidHom hN
      hq
  have hlift := hlift_of_lifts x.surj.toMonoidHom x.emb.toMonoidHom hL ι hι ε hε q hq
  obtain ⟨UX, hUX, hne, FU, hFU, hpb⟩ :=
    exists_descent_of_lift CX hcX C hc h hc' hyp (hDGC M) q hqK hgal hlift
  refine ⟨UX, hUX, hne, fun α ↦ ?_⟩
  obtain ⟨J', hJ'⟩ := exists_continuousMulEquiv_comap_cor38Fill Ω CX hcX UX hUX hne α C hc h hc'
    hyp q FU hgal hpb
  obtain ⟨c, hcc⟩ := exists_conj_cor38Fill_coverPiHom Ω CX hcX UX hUX hne α C hc h hc' hyp q FU
    hpb.w
  have hqi : IsConjInduced q
      (fun τ : π₁ᵉᵗ(basePoint Ω (fillCurve C h hyp) hc' ≫ baseChangeSpec M Ω Γ(C.Xbar, U')) ↦
        (coverPiHom Ω CX hcX (fillCurve C h hyp) hc' q τ :
          π₁ᵉᵗ(basePoint Ω CX hcX ≫ baseChangeSpec K Ω Γ(CX.Xbar, CX.U)))) :=
    ⟨coverFib Ω CX hcX (fillCurve C h hyp) hc' q, fun _ ↦ rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : (arithmeticExt Ω CX hcX).Pi, ∀ τ,
      coverPiHom Ω CX hcX (fillCurve C h hyp) hc' q τ = t * x.emb (ε τ) * t⁻¹ :=
    hqi.exists_conj_eq hq
  have hrange : cor37bPiV Ω CX hcX (fillCurve C h hyp) hc' q = x.emb.toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨τ, rfl⟩
      change coverPiHom Ω CX hcX (fillCurve C h hyp) hc' q τ ∈ x.emb.toMonoidHom.range
      rw [ht τ]
      exact hN.conj_mem _ ⟨ε τ, rfl⟩ t
    · intro hz
      obtain ⟨v, hv⟩ := hN.conj_mem _ hz t⁻¹
      refine ⟨ε.symm v, ?_⟩
      change coverPiHom Ω CX hcX (fillCurve C h hyp) hc' q (ε.symm v) = z
      rw [ht, ContinuousMulEquiv.apply_symm_apply]
      change t * x.emb.toMonoidHom v * t⁻¹ = z
      rw [hv]
      group
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) ≃ₜ*
      x.emb.toMonoidHom.range.comap (cor38Fill Ω CX hcX UX hUX hne α),
      ∀ y, (J₀ y : (arithmeticExt Ω (subCurve CX UX hUX hne)
        (compl_nonempty_of_le hUX hcX)).Pi) =
          coverPiHom Ω (subCurve CX UX hUX hne) (compl_nonempty_of_le hUX hcX) C hc FU y :=
    ⟨J'.trans (continuousSubgroupCongr (congrArg
      (Subgroup.comap (cor38Fill Ω CX hcX UX hUX hne α)) hrange)),
      fun y ↦ (coe_continuousSubgroupCongr₂ _ _).trans (hJ' y)⟩
  have hJ₀f : ∀ y, cor38Fill Ω CX hcX UX hUX hne α (J₀ y) =
      (c * t) * x.emb (ε (fillPiHom Ω C hc h hc' hyp y)) * (c * t)⁻¹ := fun y ↦ by
    rw [hJ₀ y, hcc y, ht]
    group
  obtain ⟨ιe, hιe⟩ : ∃ ιe : π₁ᵉᵗ(basePoint Ω C hc ≫ baseChangeSpec M Ω Γ(C.Xbar, C.U)) ≃ₜ*
      x.PiU, ∀ y, ιe y = ι y := ⟨continuousMulEquivOfBijective ι hι, fun _ ↦ rfl⟩
  refine ⟨c * t, ιe.symm.trans J₀, fun u ↦ ?_, fun β hβ ↦ ?_⟩
  · have e1 : ι (ιe.symm u) = u := (hιe _).symm.trans (ιe.apply_symm_apply u)
    change cor38Fill Ω CX hcX UX hUX hne α (J₀ (ιe.symm u)) = _
    rw [hJ₀f, ← hε, e1]
  · exact exists_conj_of_model_fill (hDGC M) J₀
      (x.emb.toMonoidHom.comp ε.toMulEquiv.toMonoidHom) (x.emb_injective.comp ε.injective)
      (c * t) hJ₀f β hβ

end Side2

/-! ### Combining the two sides -/

section Combine

variable {K₁ K₂ : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  (Ω₁ Ω₂ : Type u) [Field Ω₁] [Algebra K₁ Ω₁] [IsAlgClosed Ω₁] [Algebra.IsAlgebraic K₁ Ω₁]
  [CharZero Ω₁] [Field Ω₂] [Algebra K₂ Ω₂] [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂]
  [CharZero Ω₂] (CX₁ : HypCurve K₁) (hcX₁ : (CX₁.U : Set CX₁.Xbar)ᶜ.Nonempty)
  (CX₂ : HypCurve K₂) (hcX₂ : (CX₂.U : Set CX₂.Xbar)ᶜ.Nonempty)
  (Φ : (arithmeticExt Ω₁ CX₁ hcX₁).Iso (arithmeticExt Ω₂ CX₂ hcX₂))
  (UX₁ : CX₁.Xbar.Opens) (hUX₁ : UX₁ ≤ CX₁.U) (hne₁ : (UX₁ : Set CX₁.Xbar).Nonempty)
  (α₁ : fiber (basePoint Ω₁ CX₁ hcX₁) ≅
    fiber (fillPoint Ω₁ (subCurve CX₁ UX₁ hUX₁ hne₁) (compl_nonempty_of_le hUX₁ hcX₁) hUX₁))
  (UX₂ : CX₂.Xbar.Opens) (hUX₂ : UX₂ ≤ CX₂.U) (hne₂ : (UX₂ : Set CX₂.Xbar).Nonempty)
  (α₂ : fiber (basePoint Ω₂ CX₂ hcX₂) ≅
    fiber (fillPoint Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂) hUX₂))

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **Combining the two sides**: a candidate `x₁` of `Π₁` with normal `Π_V` and the data of
`cor38_side1` for `U_{X₁}`, together with the data of `cor38_side2` for the transported candidate
`φ_*(x₁)` and `U_{X₂}`, gives `φ_U : Π_{U_{X₁}} ≅ Π_{U_{X₂}}` compatible with `φ`. -/
theorem cor38_combine₂ (x : CuspCandidate (arithmeticExt Ω₁ CX₁ hcX₁))
    (hN : x.emb.toMonoidHom.range.Normal)
    (H₁ : ∃ (k : (arithmeticExt Ω₁ CX₁ hcX₁).Pi)
      (J : x.PiU ≃ₜ* x.emb.toMonoidHom.range.comap (cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁)),
      (∀ u, cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ (J u) = k * x.emb (x.surj u) * k⁻¹) ∧
      ∀ β : x.emb.toMonoidHom.range.comap (cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁) ≃ₜ*
          x.emb.toMonoidHom.range.comap (cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁),
        (∀ z, cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ (β z) =
          cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ z) →
        ∃ n : (arithmeticExt Ω₁ (subCurve CX₁ UX₁ hUX₁ hne₁)
            (compl_nonempty_of_le hUX₁ hcX₁)).Pi,
          cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ n = 1 ∧
            ∀ z, (β z : (arithmeticExt Ω₁ (subCurve CX₁ UX₁ hUX₁ hne₁)
              (compl_nonempty_of_le hUX₁ hcX₁)).Pi) = n * z * n⁻¹)
    (H₂ : ∃ (k : (arithmeticExt Ω₂ CX₂ hcX₂).Pi)
      (J : (x.transport Φ).PiU ≃ₜ* (x.transport Φ).emb.toMonoidHom.range.comap
        (cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂)),
      (∀ u, cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ (J u) =
        k * (x.transport Φ).emb ((x.transport Φ).surj u) * k⁻¹) ∧
      ∀ β : (x.transport Φ).emb.toMonoidHom.range.comap
            (cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂) ≃ₜ*
          (x.transport Φ).emb.toMonoidHom.range.comap (cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂),
        (∀ z, cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ (β z) =
          cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ z) →
        ∃ n : (arithmeticExt Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂)
            (compl_nonempty_of_le hUX₂ hcX₂)).Pi,
          cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ n = 1 ∧
            ∀ z, (β z : (arithmeticExt Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂)
              (compl_nonempty_of_le hUX₂ hcX₂)).Pi) = n * z * n⁻¹) :
    ∃ φU : (arithmeticExt Ω₁ (subCurve CX₁ UX₁ hUX₁ hne₁)
          (compl_nonempty_of_le hUX₁ hcX₁)).Pi ≃ₜ*
        (arithmeticExt Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂)).Pi,
      ∀ e, cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ (φU e) =
        Φ.pi (cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ e) := by
  obtain ⟨k₁, J₁, hJ₁, hU₁⟩ := H₁
  obtain ⟨k₂, J₂, hJ₂, hU₂⟩ := H₂
  have hO₁ : IsOpen ((x.emb.toMonoidHom.range : Subgroup _) :
      Set (arithmeticExt Ω₁ CX₁ hcX₁).Pi) := x.isOpen_range_emb
  have hO₂ : IsOpen (((x.transport Φ).emb.toMonoidHom.range : Subgroup _) :
      Set (arithmeticExt Ω₂ CX₂ hcX₂).Pi) := (x.transport Φ).isOpen_range_emb
  exact exists_continuousMulEquiv_of_models₂
    (cor38Fill_surjective₂ Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁)
    (cor38Fill_surjective₂ Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂) Φ.pi.toMulEquiv x.surj
    x.emb.toMonoidHom (x.transport Φ).emb.toMonoidHom (fun _ ↦ rfl) hN J₁ k₁ hJ₁ J₂ k₂ hJ₂
    (isOpen_comap_cor38Fill₂ Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ hO₁)
    (isOpen_comap_cor38Fill₂ Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ hO₂)
    (center_comap_cor38Fill₂ Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ hO₁)
    (center_comap_cor38Fill₂ Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ hO₂) hU₁ hU₂

end Combine

/-! ### [AbsTopII] Corollary 3.8, existence -/

attribute [local instance] isAlgClosure_of_isAlgebraic

/-- **[AbsTopII] Corollary 3.8, existence** (`Topics in Absolute Anabelian Geometry II.txt`
l.4794–4842): let `X₁`, `X₂` be affine hyperbolic curves over number fields, `X₁` of strictly
Belyi type with a Galois cover `V → X₁` (`S`), and `φ : Π₁ ≅ Π₂` an isomorphism of the
cuspidal extensions `Πᵢ ↠ G_{Kᵢ}`. Assuming the rel-isom-DGC over all number fields (`hDGC`),
for every nonempty open `U_{X₁} ⊆ X₁` there is a nonempty open `U_{X₂} ⊆ X₂` such that (for any
choice `α₂` of the base point change defining `Π_{U_{X₂}} ↠ Π₂`) some isomorphism
`φ_U : Π_{U_{X₁}} ≅ Π_{U_{X₂}}` is compatible with `φ` relative to `Π_{U_{Xᵢ}} ↠ Πᵢ`. -/
theorem cor38_exists (hDGC : ∀ (k : Type u) [Field k] [NumberField k], RelIsomDGC.Exists k)
    {K₁ K₂ : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (Ω₁ Ω₂ : Type u) [Field Ω₁] [Algebra K₁ Ω₁] [IsAlgClosed Ω₁] [Algebra.IsAlgebraic K₁ Ω₁]
    [CharZero Ω₁] [Field Ω₂] [Algebra K₂ Ω₂] [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂]
    [CharZero Ω₂] {M : Type u} [Field M] [NumberField M] [Algebra K₁ M] [Algebra M Ω₁]
    [IsScalarTower K₁ M Ω₁] [Algebra.IsAlgebraic M Ω₁]
    (CX₁ : HypCurve K₁) (hcX₁ : (CX₁.U : Set CX₁.Xbar)ᶜ.Nonempty) (S : GaloisBelyiInput CX₁ M)
    (CX₂ : HypCurve K₂) (hcX₂ : (CX₂.U : Set CX₂.Xbar)ᶜ.Nonempty)
    (Φ : (arithmeticExt Ω₁ CX₁ hcX₁).Iso (arithmeticExt Ω₂ CX₂ hcX₂))
    (UX₁ : CX₁.Xbar.Opens) (hUX₁ : UX₁ ≤ CX₁.U) (hne₁ : (UX₁ : Set CX₁.Xbar).Nonempty)
    (α₁ : fiber (basePoint Ω₁ CX₁ hcX₁) ≅
      fiber (fillPoint Ω₁ (subCurve CX₁ UX₁ hUX₁ hne₁) (compl_nonempty_of_le hUX₁ hcX₁) hUX₁)) :
    ∃ (UX₂ : CX₂.Xbar.Opens) (hUX₂ : UX₂ ≤ CX₂.U) (hne₂ : (UX₂ : Set CX₂.Xbar).Nonempty),
      ∀ α₂ : fiber (basePoint Ω₂ CX₂ hcX₂) ≅
          fiber (fillPoint Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂)
            hUX₂),
        ∃ φU : (arithmeticExt Ω₁ (subCurve CX₁ UX₁ hUX₁ hne₁)
              (compl_nonempty_of_le hUX₁ hcX₁)).Pi ≃ₜ*
            (arithmeticExt Ω₂ (subCurve CX₂ UX₂ hUX₂ hne₂) (compl_nonempty_of_le hUX₂ hcX₂)).Pi,
          ∀ e, cor38Fill Ω₂ CX₂ hcX₂ UX₂ hUX₂ hne₂ α₂ (φU e) =
            Φ.pi (cor38Fill Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ e) := by
  obtain ⟨c, l, r, hc, t, hV, m, hm, hN₁, hL₁, H₁⟩ :=
    exists_belyiChain_cor38₂ Ω₁ CX₁ hcX₁ UX₁ hUX₁ hne₁ α₁ hDGC S
  have hx := PiChain.belyiCandidate_transport Φ hc t m hm
  obtain ⟨D₂, hD₂, U', h, hc', hyp, ε, hε, q, hqfe, hq, hqK⟩ :=
    (hc.transport (Φ := Φ)).exists_cover_fill (t.transportTrivial (Φ := Φ)) hDGC
      (ChainObj.hasInfCusp_transport Φ hV) m hm
  have H₂ := cor38_side2 Ω₂ CX₂ hcX₂ hDGC
    (PiChain.belyiCandidate (hc.transport (Φ := Φ)) (t.transportTrivial (Φ := Φ)) m hm)
    (by rw [hx]; exact CuspCandidate.normal_range_emb_transport Φ _ hN₁)
    (by rw [hx]; exact fun B g hB ↦ lifts_of_mulEquiv _ _ Φ.pi.toMulEquiv hL₁ B g hB)
    D₂.Y D₂.hY D₂.ι ⟨D₂.inj, hD₂⟩ h hc' hyp ε hε q hq hqK
  rw [hx] at H₂
  obtain ⟨UX₂, hUX₂, hne₂, H₂⟩ := H₂
  exact ⟨UX₂, hUX₂, hne₂, fun α₂ ↦ cor38_combine₂ Ω₁ Ω₂ CX₁ hcX₁ CX₂ hcX₂ Φ UX₁ hUX₁ hne₁ α₁
    UX₂ hUX₂ hne₂ α₂ _ hN₁ H₁ (H₂ α₂)⟩

end CurvesJacobian.Cusp
